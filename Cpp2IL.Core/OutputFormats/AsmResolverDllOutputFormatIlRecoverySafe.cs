using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;

namespace Cpp2IL.Core.OutputFormats;

/// <summary>
/// dll_il_recovery, but "safe" plus diagnostic:
///
/// 1) SAFE: after IL generation, any method whose body still carries a placeholder
///    (a call to the injected Cpp2ILHelpers.NoteDecompilerIssue helper, i.e. an unresolved
///    operation that would otherwise silently produce a fake value such as
///    ldstr + Ldc_I4_0 + Conv_I) has its WHOLE body replaced by a stub.
///    => no silent fake values: every shipped body is either recovered or explicitly stubbed.
///
/// 2) DIAGNOSTIC: it also writes a per-method issue manifest (reason + assembly + method + detail)
///    and per-assembly counts, so the remaining IR gaps can be ranked and attacked by frequency
///    instead of by guesswork. This is the instrument that drives IR completion work.
/// </summary>
public class AsmResolverDllOutputFormatIlRecoverySafe : AsmResolverDllOutputFormatIlRecovery
{
    private const string NoteIssueMethodName = "NoteDecompilerIssue";

    public override string OutputFormatId => "dll_il_recovery_safe";
    public override string OutputFormatName => "DLL files with safe IL Recovery (methods with placeholders are stubbed)";

    // [0]=clean [1]=placeholder [2]=analysis exception [3]=skipped engine assembly
    private readonly ConcurrentDictionary<string, int[]> _perAssembly = new();
    private readonly ConcurrentBag<string> _issues = new(); // "reason\tassembly\tmethod\tdetail"
    private int _clean, _placeholder, _exception, _skipped;

    // ---- address diagnostics: is a "Unmanaged memory load: [ADDR]" address a real metadata-usage slot? ----
    private static readonly Regex BracketHex = new(@"\[([0-9A-Fa-f]+)\]", RegexOptions.Compiled);
    private readonly ConcurrentDictionary<long, int> _addrDelta = new(); // (addr - nearestSlot) -> count
    private long _addrHit, _addrMiss, _addrNoSlotSet;
    private ulong[]? _slotAddrs;
    private readonly object _slotLock = new();

    protected override void FillMethodBody(MethodDefinition methodDefinition, MethodAnalysisContext methodContext)
    {
        base.FillMethodBody(methodDefinition, methodContext);

        var assemblyName = methodContext.DeclaringType?.DeclaringAssembly?.Name ?? "?";
        var slot = _perAssembly.GetOrAdd(assemblyName, _ => new int[4]);

        if (methodDefinition.CilMethodBody is not { } body || body.Instructions.Count == 0)
        {
            Interlocked.Increment(ref slot[3]);
            Interlocked.Increment(ref _skipped);
            return;
        }

        // Engine/BCL assemblies are deliberately stubbed by the base class; don't count them as IR gaps.
        if (IsSkippedAssembly(methodDefinition))
        {
            Interlocked.Increment(ref slot[3]);
            Interlocked.Increment(ref _skipped);
            return;
        }

        var (reason, detail) = FindIssue(body);

        if (reason == null)
        {
            Interlocked.Increment(ref slot[0]);
            Interlocked.Increment(ref _clean);
            return;
        }

        Interlocked.Increment(ref slot[reason == "placeholder" ? 1 : 2]);
        _issues.Add($"{reason}\t{assemblyName}\t{methodContext.FullName}\t{Flatten(detail)}");

        if (reason == "placeholder")
        {
            // Safe mode: base counted this as a successful decompile; it is not - it would silently
            // carry fake values. Replace the whole body with a minimal implementation.
            SuccessfulMethodCount--;
            FillMethodBodyWithStub(methodDefinition);
            Interlocked.Increment(ref _placeholder);
            AnalyzePlaceholderAddress(methodContext, detail);
        }
        else
        {
            Interlocked.Increment(ref _exception);
        }
    }

    /// <summary>
    /// For a "Unmanaged memory load: [ADDR]" placeholder, checks whether ADDR really is a metadata-usage
    /// global slot address. If not, it records the delta to the nearest real slot address, so a systematic
    /// address miscomputation (e.g. an ADRP page added twice) shows up as a tight, page-aligned delta.
    /// </summary>
    private void AnalyzePlaceholderAddress(MethodAnalysisContext methodContext, string detail)
    {
        var match = BracketHex.Match(detail);
        if (!match.Success)
            return;
        if (!ulong.TryParse(match.Groups[1].Value, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out var address))
            return;

        var lib = methodContext.AppContext.LibCpp2IlContext;

        if (lib.GetAnyGlobalByAddress(address) != null)
        {
            Interlocked.Increment(ref _addrHit);
            return;
        }

        Interlocked.Increment(ref _addrMiss);

        var slots = GetSlotAddresses(lib);
        if (slots.Length == 0)
        {
            Interlocked.Increment(ref _addrNoSlotSet);
            return;
        }

        // binary search for the nearest slot address
        var idx = Array.BinarySearch(slots, address);
        if (idx < 0)
            idx = ~idx;

        var best = long.MaxValue;
        if (idx < slots.Length)
            best = Math.Min(best, Math.Abs((long)slots[idx] - (long)address));
        if (idx > 0)
            best = Math.Min(best, Math.Abs((long)slots[idx - 1] - (long)address));

        // keep the sign so an "address too large" artefact is distinguishable from "too small"
        var signedBest = idx < slots.Length && (idx == 0 || Math.Abs((long)slots[idx] - (long)address) <= Math.Abs((long)slots[idx - 1] - (long)address))
            ? (long)address - (long)slots[idx]
            : (long)address - (long)slots[idx - 1];

        _addrDelta.AddOrUpdate(signedBest, 1, (_, n) => n + 1);
    }

    /// <summary>All metadata-usage global slot addresses known from the metadata (pre-27 path).</summary>
    private ulong[] GetSlotAddresses(LibCpp2IlContext lib)
    {
        if (_slotAddrs != null)
            return _slotAddrs;

        lock (_slotLock)
        {
            if (_slotAddrs != null)
                return _slotAddrs;

            var set = new SortedSet<ulong>();
            try
            {
                var dic = lib.Metadata.metadataUsageDic;
                if (dic != null)
                {
                    foreach (var perType in dic.Values)
                    {
                        foreach (var index in perType.Keys)
                        {
                            try
                            {
                                set.Add(lib.Binary.GetRawMetadataUsage(index));
                            }
                            catch
                            {
                                // out-of-range usage index - ignore
                            }
                        }
                    }
                }
            }
            catch (Exception e)
            {
                Logger.WarnNewline($"[IlRecoverySafe] could not enumerate metadata-usage slots: {e.Message}", "IlRecoverySafe");
            }

            _slotAddrs = set.ToArray();
            return _slotAddrs;
        }
    }

    private static bool IsSkippedAssembly(MethodDefinition methodDefinition)
    {
        var moduleName = methodDefinition.DeclaringModule?.Name?.ToString() ?? "";
        return moduleName.StartsWith("UnityEngine.") || moduleName.StartsWith("Unity.") ||
               moduleName.StartsWith("System.") || moduleName == "System" ||
               moduleName.StartsWith("mscorlib");
    }

    /// <summary>
    /// Reads the diagnostic out of a generated body:
    ///  - "placeholder": the body contains a call to Cpp2ILHelpers.NoteDecompilerIssue, whose
    ///    preceding ldstr holds the reason (e.g. "Unmanaged memory load: [v1 @ X0+128]").
    ///  - "exception":   the base class replaced the body with ldstr detail; newobj Exception; throw.
    /// </summary>
    private static (string? Reason, string Detail) FindIssue(CilMethodBody body)
    {
        var ins = body.Instructions;

        for (var i = 0; i < ins.Count; i++)
        {
            if (ins[i].OpCode.Code != CilCode.Call || ins[i].Operand is not IMethodDescriptor md)
                continue;
            if (md.Name != NoteIssueMethodName)
                continue;

            var detail = i > 0 && ins[i - 1].OpCode.Code == CilCode.Ldstr && ins[i - 1].Operand is string s
                ? s
                : "";
            return ("placeholder", detail);
        }

        // Analysis-exception stub: ldstr <reason>; newobj System.Exception; throw
        if (ins.Count >= 3
            && ins[^1].OpCode.Code == CilCode.Throw
            && ins[^2].OpCode.Code == CilCode.Newobj)
        {
            var detail = ins
                .Where(x => x.OpCode.Code == CilCode.Ldstr && x.Operand is string)
                .Select(x => (string)x.Operand!)
                .FirstOrDefault() ?? "";
            return ("exception", detail);
        }

        return (null, "");
    }

    private static string Flatten(string s)
        => s.Replace('\t', ' ').Replace('\r', ' ').Replace('\n', ' ').Trim();

    public override List<AssemblyDefinition> BuildAssemblies(ApplicationAnalysisContext context)
    {
        var ret = base.BuildAssemblies(context);

        var stubPlaceholder = _placeholder;
        var issues = _issues.Count;
        Logger.InfoNewline(
            $"[IlRecoverySafe] game methods: clean={_clean}, placeholder={stubPlaceholder}, exception={_exception} " +
            $"(issues={issues}); engine/skipped={_skipped}; TotalCounted={TotalMethodCount}, Successful={SuccessfulMethodCount}",
            "IlRecoverySafe");

        var root = Environment.CurrentDirectory;
        try
        {
            var summary = Path.Combine(root, "dll_il_recovery_safe.summary.tsv");
            var lines = new List<string> { "assembly\tclean\tplaceholder\texception\tskipped" };
            lines.AddRange(_perAssembly
                .OrderByDescending(kv => kv.Value[1] + kv.Value[2])
                .ThenBy(kv => kv.Key, StringComparer.OrdinalIgnoreCase)
                .Select(kv => $"{kv.Key}\t{kv.Value[0]}\t{kv.Value[1]}\t{kv.Value[2]}\t{kv.Value[3]}"));
            File.WriteAllLines(summary, lines);

            var issuesPath = Path.Combine(root, "dll_il_recovery_safe.issues.tsv");
            File.WriteAllLines(issuesPath, new[] { "reason\tassembly\tmethod\tdetail" }
                .Concat(_issues.OrderBy(x => x, StringComparer.OrdinalIgnoreCase)));

            Logger.InfoNewline($"[IlRecoverySafe] summary: {summary}", "IlRecoverySafe");
            Logger.InfoNewline($"[IlRecoverySafe] issues : {issuesPath}", "IlRecoverySafe");

            ReportAddressDiagnostics(root);
        }
        catch (Exception e)
        {
            Logger.ErrorNewline($"[IlRecoverySafe] failed to write manifest: {e.Message}", "IlRecoverySafe");
        }

        return ret;
    }

    private void ReportAddressDiagnostics(string root)
    {
        var hit = Interlocked.Read(ref _addrHit);
        var miss = Interlocked.Read(ref _addrMiss);
        var noSet = Interlocked.Read(ref _addrNoSlotSet);
        Logger.InfoNewline(
            $"[IlRecoverySafe][addr] bracketed-address placeholders: hit={hit}, miss={miss}, noSlotSet={noSet} " +
            $"(slotAddresses={_slotAddrs?.Length ?? 0})",
            "IlRecoverySafe");

        var top = _addrDelta.OrderByDescending(kv => kv.Value).Take(20).ToList();
        if (top.Count == 0)
            return;

        var lines = new List<string> { "delta_to_nearest_slot\tcount\tpage_aligned" };
        foreach (var (delta, count) in top)
        {
            var aligned = delta != 0 && delta % 0x1000 == 0;
            lines.Add($"{(delta < 0 ? "-" : "+")}0x{Math.Abs(delta):X}\t{count}\t{aligned}");
            Logger.InfoNewline($"[IlRecoverySafe][addr] delta={(delta < 0 ? "-" : "+")}0x{Math.Abs(delta):X} " +
                               $"x{count} pageAligned={aligned}", "IlRecoverySafe");
        }

        try
        {
            var path = Path.Combine(root, "dll_il_recovery_safe.addrtest.tsv");
            File.WriteAllLines(path, lines);
            Logger.InfoNewline($"[IlRecoverySafe] addrtest: {path}", "IlRecoverySafe");
        }
        catch (Exception e)
        {
            Logger.ErrorNewline($"[IlRecoverySafe] failed to write addrtest: {e.Message}", "IlRecoverySafe");
        }
    }
}