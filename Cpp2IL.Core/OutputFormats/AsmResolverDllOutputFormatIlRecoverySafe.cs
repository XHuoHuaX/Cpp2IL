using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;

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
        }
        else
        {
            Interlocked.Increment(ref _exception);
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
        }
        catch (Exception e)
        {
            Logger.ErrorNewline($"[IlRecoverySafe] failed to write manifest: {e.Message}", "IlRecoverySafe");
        }

        return ret;
    }
}