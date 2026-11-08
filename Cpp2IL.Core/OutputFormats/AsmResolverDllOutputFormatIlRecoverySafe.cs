using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
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

    /// <summary>
    /// Accessibility is a compile-time notion; the native code these bodies were translated from has
    /// none. A method legitimately reads a private field of its own base type, or of a sibling type it
    /// reaches through a pointer, and C# then refuses to compile the - correct - translation (CS0122).
    /// Widening the fields of the assemblies we emit restores the access the native code had without
    /// changing any behaviour: visibility is not semantics.
    ///
    /// The *types* have to be widened with them, or a now-public field whose type is an internal or
    /// nested-private class becomes an inconsistent-accessibility error (CS0052) - the same trade in a
    /// different spelling.
    ///
    /// Members that are not fields are left alone, deliberately. Widening a *method* can break the rule
    /// that an override keeps its base's accessibility (CS0507); fields and types have no such rule.
    /// </summary>
    /// <summary>
    /// Whether the emitted assemblies declare each other as friend assemblies.
    ///
    /// IL2CPP does not care about C# visibility: the native code reads every field of every type, across
    /// assembly boundaries. Rebuilding that in C# needs some relaxation, and there are two ways to get it:
    /// make the members public, or keep them internal and let the sibling assemblies in through
    /// <c>InternalsVisibleTo</c>.
    ///
    /// Public is the one that costs: a public field may not name a type that is not publicly reachable, and
    /// the type cannot be widened either (measured, far worse). That is exactly the CS0052 cluster. Internal
    /// plus a friend declaration has no such constraint - see docs/EXPERIMENT-IVT-001.
    /// </summary>
    private static readonly bool UseFriendAssemblies = Environment.GetEnvironmentVariable("CPP2IL_IVT") == "1";

    /// <summary>
    /// Declares every emitted assembly as a friend of every other one, so `internal` members stay reachable
    /// from the sibling assemblies the native code crossed freely.
    /// </summary>
    private static int DeclareFriendAssemblies(List<AssemblyDefinition> assemblies)
    {
        var names = assemblies
            .Select(a => a.Name?.ToString())
            .Where(n => !string.IsNullOrEmpty(n))
            .Distinct()
            .ToList();

        var declared = 0;

        foreach (var assembly in assemblies)
        {
            var own = assembly.Name?.ToString();

            if (own == null || assembly.ManifestModule is not { } module)
                continue;

            var factory = module.CorLibTypeFactory;
            var attributeType = factory.CorLibScope.CreateTypeReference("System.Runtime.CompilerServices", "InternalsVisibleToAttribute");
            var constructor = attributeType.CreateMemberReference(".ctor",
                MethodSignature.CreateInstance(factory.Void, [factory.String]));

            foreach (var friend in names)
            {
                if (friend == own)
                    continue;

                var argument = new CustomAttributeArgument(factory.String, friend);
                assembly.CustomAttributes.Add(new CustomAttribute((ICustomAttributeType)constructor,
                    new CustomAttributeSignature(argument)));
                declared++;
            }
        }

        return declared;
    }

    protected override void OnAssembliesBuilt(List<AssemblyDefinition> assemblies)
    {
        var declaredFriends = UseFriendAssemblies ? DeclareFriendAssemblies(assemblies) : 0;

        var widenedFields = 0;
        var widenedTypes = 0;
        var renamedFields = 0;
        var widenedMethods = 0;

        foreach (var module in assemblies.Select(a => a.ManifestModule).OfType<ModuleDefinition>())
        {
            foreach (var type in module.GetAllTypes())
            {
                // IL2CPP metadata keeps the compiler-generated backing field of an event, and that field
                // carries the event's own name; emitting both declarations is CS0102. The C# decompiler
                // normally sidesteps this by renaming the field, but only while the field is private -
                // once widened it keeps its name and the collision survives. Rename it here instead, so
                // the field can stay accessible: the definition is renamed, so every reference to it
                // follows, and nothing about the value or layout changes.
                var takenByOtherKinds = new HashSet<string>();
                foreach (var method in type.Methods)
                    if (method.Name is { } methodName)
                        takenByOtherKinds.Add(methodName.ToString());
                foreach (var property in type.Properties)
                    if (property.Name is { } propertyName)
                        takenByOtherKinds.Add(propertyName.ToString());
                foreach (var ev in type.Events)
                    if (ev.Name is { } eventName)
                        takenByOtherKinds.Add(eventName.ToString());
                foreach (var nested in type.NestedTypes)
                    if (nested.Name is { } nestedName)
                        takenByOtherKinds.Add(nestedName.ToString());

                var fieldNames = new HashSet<string>(type.Fields.Select(f => f.Name.ToString()));

                foreach (var field in type.Fields)
                {
                    if (field.Name is not { } fieldName || !takenByOtherKinds.Contains(fieldName.ToString()))
                        continue;

                    var name = fieldName.ToString();
                    var candidate = "m_" + name;
                    for (var suffix = 2; takenByOtherKinds.Contains(candidate) || fieldNames.Contains(candidate); suffix++)
                        candidate = "m_" + name + "_" + suffix;

                    fieldNames.Remove(name);
                    field.Name = candidate;
                    fieldNames.Add(candidate);
                    renamedFields++;
                }

                // Types are deliberately NOT widened. Measured twice, both worse: widening every type
                // (B1 468 -> 5,641) let the emitted stubs publish the same names as the real BCL/engine
                // assemblies the consumer references, so references rebound to the stubs; widening only
                // nested types (B1 468 -> 561) traded CS0052 -12 for CS0122 +39, CS0426 +16, CS0030 +31.
                // The inconsistent-accessibility cases (CS0052, 140) stay, and are the cheaper trade.

                // Fields stay public even when friend assemblies are declared. `internal` compiles fine (the
                // friend declarations cover it) but the decompiler does not honour friend assemblies, so a
                // field reached from another emitted assembly becomes invisible to it and the source it writes
                // for that access is broken (measured: +45 CS0030, +31 CS0019, +28 CS0149, +14 CS0103).
                // Public costs the CS0052 cluster, which is the cheaper of the two trades - see
                // docs/EXPERIMENT-IVT-001.
                foreach (var field in type.Fields)
                {
                    if ((field.Attributes & FieldAttributes.FieldAccessMask) == FieldAttributes.Public)
                        continue;

                    field.Attributes = (field.Attributes & ~FieldAttributes.FieldAccessMask) | FieldAttributes.Public;
                    widenedFields++;
                }

                // Methods are widened too. A public method may not expose a less-accessible parameter (CS0051) or
                // return type (CS0050), so the types its signature mentions are widened with it - but only
                // when they are declared in this same module. A type from another module cannot be widened
                // here without publishing that assembly's stubs (measured, far worse), so in that case the
                // method keeps its original accessibility instead of trading one error for another.
                foreach (var method in type.Methods)
                {
                    if ((method.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public)
                        continue;

                    if (!MakeSignatureExpressible(method.Signature, module, ref widenedTypes))
                        continue;

                    method.Attributes = (method.Attributes & ~MethodAttributes.MemberAccessMask) | MethodAttributes.Public;
                    widenedMethods++;
                }
            }
        }

        Logger.InfoNewline($"[IlRecoverySafe] accessibility: {widenedFields} field(s), {widenedMethods} method(s) and {widenedTypes} type(s) widened to public; {renamedFields} field(s) renamed to avoid a member-name collision", "IlRecoverySafe");
    }

    /// <summary>
    /// Whether every type in this signature is namable at public visibility. Used to keep a widened member
    /// from tripping the inconsistent-accessibility rules (CS0050/CS0051/CS0052/CS0053).
    /// </summary>
    /// <summary>
    /// Makes every type named by this signature namable at public visibility, widening the ones this module
    /// declares. Returns false when a type would have to be widened in *another* module, because publishing
    /// another assembly's stubs as public is measured to be far worse than leaving the member as it is.
    /// </summary>
    private static bool MakeSignatureExpressible(MethodSignature? signature, ModuleDefinition module, ref int widenedTypes)
    {
        if (signature == null)
            return true;

        var localTypes = module.GetAllTypes().ToHashSet();

        foreach (var referenced in ReferencedTypeDefinitions(signature.ReturnType)
                     .Concat(signature.ParameterTypes.SelectMany(ReferencedTypeDefinitions))
                     .Distinct())
        {
            if (IsPubliclyReachable(referenced))
                continue;

            if (!localTypes.Contains(referenced))
                return false;

            // The declaring chain has to be public too, or the nested type stays just as unreachable.
            for (var current = referenced; current != null; current = current.DeclaringType as TypeDefinition)
            {
                var wanted = current.IsNested ? TypeAttributes.NestedPublic : TypeAttributes.Public;
                if ((current.Attributes & TypeAttributes.VisibilityMask) == wanted)
                    continue;

                current.Attributes = (current.Attributes & ~TypeAttributes.VisibilityMask) | wanted;
                widenedTypes++;
            }
        }

        return true;
    }

    private static bool IsPubliclyReachable(TypeDefinition definition)
    {
        for (var current = definition; current != null; current = current.DeclaringType as TypeDefinition)
        {
            var wanted = current.IsNested ? TypeAttributes.NestedPublic : TypeAttributes.Public;
            if ((current.Attributes & TypeAttributes.VisibilityMask) != wanted)
                return false;
        }

        return true;
    }

    /// <summary>Every type a signature mentions, including generic arguments and element types.</summary>
    private static IEnumerable<TypeDefinition> ReferencedTypeDefinitions(TypeSignature? signature)
    {
        switch (signature)
        {
            case null:
                yield break;
            case GenericInstanceTypeSignature generic:
                foreach (var definition in ReferencedTypeDefinitions(generic.GenericType.ToTypeSignature(false)))
                    yield return definition;
                foreach (var argument in generic.TypeArguments)
                    foreach (var definition in ReferencedTypeDefinitions(argument))
                        yield return definition;
                yield break;
            case SzArrayTypeSignature array:
                foreach (var definition in ReferencedTypeDefinitions(array.BaseType))
                    yield return definition;
                yield break;
            case ByReferenceTypeSignature byRef:
                foreach (var definition in ReferencedTypeDefinitions(byRef.BaseType))
                    yield return definition;
                yield break;
            case PointerTypeSignature pointer:
                foreach (var definition in ReferencedTypeDefinitions(pointer.BaseType))
                    yield return definition;
                yield break;
            case TypeDefOrRefSignature { Type: TypeDefinition definition }:
                yield return definition;
                yield break;
        }
    }

    // [0]=clean [1]=placeholder [2]=analysis exception [3]=skipped engine assembly
    private readonly ConcurrentDictionary<string, int[]> _perAssembly = new();
    private readonly ConcurrentBag<string> _issues = new(); // "reason\tassembly\tmethod\tdetail"
    private readonly ConcurrentBag<string> _issueCounts = new(); // "count\treason\tassembly\tmethod\tdetail"
    private int _clean, _placeholder, _exception, _skipped;

    // ---- address diagnostics: is a "Unmanaged memory load: [ADDR]" address a real metadata-usage slot? ----
    private static readonly Regex BracketHex = new(@"\[([0-9A-Fa-f]+)\]", RegexOptions.Compiled);
    private readonly ConcurrentDictionary<long, int> _addrDelta = new(); // (addr - nearestSlot) -> count
    private long _addrHit, _addrMiss, _addrNoSlotSet;
    private ulong[]? _slotAddrs;
    private readonly object _slotLock = new();

    // ---- "Method not found @ADDR" classification ----
    private static readonly Regex MethodNotFoundAt = new(@"Method not found @([0-9A-Fa-f]+)", RegexOptions.Compiled);
    private readonly ConcurrentDictionary<string, int> _mnfClass = new(); // class -> count
    private readonly ConcurrentDictionary<ulong, int> _mnfUnresolved = new(); // unresolved-address -> method count
    private readonly ConcurrentDictionary<ulong, string> _mnfInMba = new(); // addr -> "count\tsample signatures"
    private int _mnfInMethodsByAddress, _mnfInGenericImpl, _mnfInKeyFunctions, _mnfNearKnown, _mnfUnknown;
    private int _mnfThrowHelperName, _mnfThrowHelperRaiser; // unknown_native split
    private int _mnfOtherUnknown;

    // ---- untyped-base provenance: WHY does [ vN @ XREG+off ] have no type on its base? ----
    // Matches both "Unmanaged memory load: [v45 @ X0_v2+12F]" and the typed variant
    // "Unmanaged memory load: [v45 @ X0_v2 (Il2CppClass<...>)+128]" (group 3 = optional type).
    private static readonly Regex UntypedMemLoad = new(
        @"Unmanaged memory load: \[(\S+) @ ([^\s(]+)(?: \(([^)]*)\))?\+([0-9A-F]+)\]$", RegexOptions.Compiled);
    private readonly ConcurrentDictionary<string, int> _ubChain = new(); // provenance chain -> count
    private readonly ConcurrentDictionary<string, int> _ubConstAddr = new(); // terminal const addr -> count
    private readonly ConcurrentDictionary<string, int> _ubConstAddrKnown = new(); // of the above: known metadata global?
    private int _ubTotal, _ubConstTotal, _ubConstKnownTotal;

    // "Method ends with non empty stack" methods, with their native address, so the prologue/epilogue can
    // be read back from the binary and compared with what the lifter emitted.
    private static readonly Regex NonEmptyStack = new(@"ends with non empty stack", RegexOptions.Compiled);
    private readonly ConcurrentBag<string> _stackUnderflow = new();

    // Optional targeted ISIL dump for a name filter (env CPP2IL_DUMP_ISIL_FOR, ';'-separated substrings).
    // Used to obtain exact ground truth for a handful of failing methods without a full 450MB ISIL dump.
    private static readonly string[] IsilDumpFilter =
        (Environment.GetEnvironmentVariable("CPP2IL_DUMP_ISIL_FOR") ?? "")
        .Split(';', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
    private readonly ConcurrentBag<string> _isilDump = new();
    private int _isilDumped;

    // Same idea, but keyed on the method's first issue text (regex) so a whole failure family can be
    // sampled without knowing any method names:
    //   CPP2IL_DUMP_ISSUE_RE='Indirect call:.*\+2D0'
    private static readonly Regex? IsilDumpIssueFilter =
        (Environment.GetEnvironmentVariable("CPP2IL_DUMP_ISSUE_RE") ?? "") is { Length: > 0 } issuePattern
            ? new Regex(issuePattern, RegexOptions.Compiled)
            : null;

    // Debug-only: analyse a single method (substring of its full name) so a fix can be iterated on in
    // seconds instead of a ~25 minute full run. Every other method is emitted as a stub, unanalysed.
    private static readonly string? OnlyMethodFilter =
        (Environment.GetEnvironmentVariable("CPP2IL_ONLY_METHOD") ?? "") is { Length: > 0 } only ? only : null;

    protected override void FillMethodBody(MethodDefinition methodDefinition, MethodAnalysisContext methodContext)
    {
        // Fast path for single-method debugging: don't even analyse the rest.
        if (OnlyMethodFilter != null
            && !methodContext.FullName.Contains(OnlyMethodFilter, StringComparison.Ordinal))
        {
            FillMethodBodyWithStub(methodDefinition);
            return;
        }

        // The base releases ISIL/CFG at the end of its FillMethodBody. Because our diagnostics need
        // the CFG (to walk a placeholder's operand provenance), BuildAssemblies defers that release
        // and we drop it here in a finally - retention stays bounded to one method at a time.
        try
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

            var (reason, detail) = FindIssue(body, out var issueCount);

            if (reason == null)
            {
                Interlocked.Increment(ref slot[0]);
                Interlocked.Increment(ref _clean);

                // In single-method debug mode the whole point is to look at this method, so dump it
                // even when it came out clean - a clean body can still be wrong (e.g. a mistyped
                // operand that only shows up as a compile error after decompilation).
                if (OnlyMethodFilter != null)
                    MaybeDumpIsil(methodContext, "(clean method)");

                return;
            }

            Interlocked.Increment(ref slot[reason == "placeholder" ? 1 : 2]);
            _issues.Add($"{reason}\t{assemblyName}\t{methodContext.FullName}\t{Flatten(detail)}");

            // How far each body is from clean: a body needs ALL of its issues gone to count, so the
            // methods sitting at one issue are where the next gain actually is.
            _issueCounts.Add($"{issueCount}\t{reason}\t{assemblyName}\t{methodContext.FullName}\t{Flatten(detail)}");

            if (NonEmptyStack.IsMatch(detail))
                _stackUnderflow.Add($"{methodContext.FullName}\t0x{methodContext.UnderlyingPointer:X}\t{Flatten(detail)}");

            if (reason == "placeholder")
            {
                // Safe mode: base counted this as a successful decompile; it is not - it would silently
                // carry fake values. Replace the whole body with a minimal implementation.
                SuccessfulMethodCount--;
                FillMethodBodyWithStub(methodDefinition);
                Interlocked.Increment(ref _placeholder);
                AnalyzePlaceholderAddress(methodContext, detail);
                AnalyzeMethodNotFound(methodContext, detail);
                AnalyzeUntypedBase(methodContext, detail);
                MaybeDumpIsil(methodContext, detail);
            }
            else
            {
                Interlocked.Increment(ref _exception);
            }
        }
        finally
        {
            // Drop the ISIL/CFG that BuildAssemblies asked the base to defer.
            methodContext.ReleaseAnalysisDataNow();
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

    /// <summary>
    /// Classifies a "Method not found @ADDR" placeholder: is ADDR actually known somewhere?
    ///  - MethodsByAddress                           => anomaly: lookup should have succeeded
    ///  - Binary.ConcreteGenericImplementationsByAddress => generic method impl known but not registered
    ///  - a key function (runtime internal helper)   => not a managed method; KeyFunctionRecovery gap
    ///  - within 64 bytes of a MethodsByAddress key  => thunk/veneer offset guess
    ///  - otherwise                                  => genuinely unknown native target
    /// </summary>
    private void AnalyzeMethodNotFound(MethodAnalysisContext methodContext, string detail)
    {
        var match = MethodNotFoundAt.Match(detail);
        if (!match.Success)
            return;
        if (!ulong.TryParse(match.Groups[1].Value, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out var address))
            return;

        var app = methodContext.AppContext;
        var keyFuncs = app.GetOrCreateKeyFunctionAddresses();

        if (app.MethodsByAddress.ContainsKey(address))
        {
            Interlocked.Increment(ref _mnfInMethodsByAddress);
            _mnfClass.AddOrUpdate("in_MethodsByAddress_ANOMALY", 1, (_, n) => n + 1);
            if (app.MethodsByAddress.TryGetValue(address, out var list))
            {
                var sample = string.Join(" | ", list.Take(3).Select(m => m.FullNameWithSignature));
                _mnfInMba.AddOrUpdate(address, $"{list.Count}\t{sample}", (_, old) =>
                {
                    var c = int.Parse(old.Split('\t')[0]);
                    return $"{c + list.Count}\t{sample}";
                });
            }
            return;
        }

        if (app.Binary.ConcreteGenericImplementationsByAddress.ContainsKey(address))
        {
            Interlocked.Increment(ref _mnfInGenericImpl);
            _mnfClass.AddOrUpdate("in_ConcreteGenericImpl_but_not_registered", 1, (_, n) => n + 1);
            return;
        }

        if (keyFuncs.IsKeyFunctionAddress(address))
        {
            Interlocked.Increment(ref _mnfInKeyFunctions);
            _mnfClass.AddOrUpdate("key_function_runtime_helper", 1, (_, n) => n + 1);
            return;
        }

        var nearKnown = app.MethodsByAddress.Keys.Any(k => Math.Abs((long)k - (long)address) <= 64);
        if (nearKnown)
        {
            Interlocked.Increment(ref _mnfNearKnown);
            _mnfClass.AddOrUpdate("within_64B_of_known_method", 1, (_, n) => n + 1);
            return;
        }

        Interlocked.Increment(ref _mnfUnknown);
        _mnfClass.AddOrUpdate("unknown_native", 1, (_, n) => n + 1);
        _mnfUnresolved.AddOrUpdate(address, 1, (_, n) => n + 1);
        ClassifyUnknownNative(app, address);
    }

    /// <summary>Splits "unknown_native" into (a) throw-helper that names an exception type
    /// and (b) raiser that throws its argument, matching what ThrowHelperRecovery already
    /// resolves in MetadataResolver. If neither, keep the generic "unknown_native" label
    /// but record that it's a runtime helper (not a managed method) so the report can be
    /// filtered.</summary>
    private void ClassifyUnknownNative(ApplicationAnalysisContext app, ulong address)
    {
        if (ThrowHelperRecovery.GetThrownException(app, address) is not null)
        {
            Interlocked.Increment(ref _mnfThrowHelperName);
            _mnfClass.AddOrUpdate("unknown_throwhelper_named", 1, (_, n) => n + 1);
            return;
        }
        if (ThrowHelperRecovery.IsExceptionRaiser(app, address))
        {
            Interlocked.Increment(ref _mnfThrowHelperRaiser);
            _mnfClass.AddOrUpdate("unknown_throwhelper_raiser", 1, (_, n) => n + 1);
            return;
        }
        Interlocked.Increment(ref _mnfOtherUnknown);
        _mnfClass.AddOrUpdate("unknown_other_runtime_helper", 1, (_, n) => n + 1);
    }

    /// <summary>
    /// For a memory-load placeholder whose base local has NO type, walks the def chain of that base
    /// (up to 4 hops) and records a provenance signature, so the family can be split into actionable
    /// root causes: "loaded from a metadata global we DID resolve" vs "from a global we never
    /// resolved" vs "call result" vs "copy/phi", etc.
    /// </summary>
    private void AnalyzeUntypedBase(MethodAnalysisContext methodContext, string detail)
    {
        var match = UntypedMemLoad.Match(detail);
        if (!match.Success)
            return;

        // Group 3 present => the base carries a type: that is the other family (offset resolution).
        if (match.Groups[3].Success && match.Groups[3].Value.Length > 0)
            return;

        Interlocked.Increment(ref _ubTotal);

        var cfg = methodContext.ControlFlowGraph;
        if (cfg == null)
        {
            _ubChain.AddOrUpdate("no_cfg", 1, (_, n) => n + 1);
            return;
        }

        var chain = new List<string>();
        var current = match.Groups[1].Value;
        var visited = new HashSet<string>();

        for (var hop = 0; hop < 4 && visited.Add(current); hop++)
        {
            var def = FindDefinition(cfg.Instructions, current);
            if (def == null)
            {
                chain.Add("no_def(" + current + ")");
                break;
            }

            if (def.OpCode == Cpp2IL.Core.ISIL.OpCode.Call)
            {
                var target = def.Operands.Count > 0 ? def.Operands[0] : null;
                chain.Add("<-call(" + (target is MethodAnalysisContext tm ? tm.Name : target?.GetType().Name ?? "?") + ")");
                break;
            }

            if (def.OpCode == Cpp2IL.Core.ISIL.OpCode.Phi)
            {
                chain.Add("<-phi");
                break;
            }

            if (def.OpCode != Cpp2IL.Core.ISIL.OpCode.Move)
            {
                chain.Add("<-" + def.OpCode);
                break;
            }

            var src = def.Operands.Count > 1 ? def.Operands[1] : null;

            if (src is Cpp2IL.Core.ISIL.MemoryOperand mem)
            {
                if (mem.Base == null && mem.Index == null)
                {
                    var addr = (ulong)mem.Addend;
                    var known = methodContext.AppContext.LibCpp2IlContext.GetAnyGlobalByAddress(addr) != null;
                    chain.Add(known ? "<-metaglobal_KNOWN" : "<-const_addr_UNKNOWN");
                    Interlocked.Increment(ref _ubConstTotal);
                    _ubConstAddr.AddOrUpdate($"0x{addr:X}", 1, (_, n) => n + 1);
                    if (known)
                    {
                        Interlocked.Increment(ref _ubConstKnownTotal);
                        _ubConstAddrKnown.AddOrUpdate($"0x{addr:X}", 1, (_, n) => n + 1);
                    }

                    break;
                }

                if (mem.Base is Cpp2IL.Core.ISIL.LocalVariable baseLocal)
                {
                    chain.Add("<-load_of:" + baseLocal.Name);
                    current = baseLocal.Name;
                    continue;
                }

                chain.Add("<-memop_base_other");
                break;
            }

            if (src is Cpp2IL.Core.ISIL.LocalVariable copy)
            {
                chain.Add("<-copy_of:" + copy.Name);
                current = copy.Name;
                continue;
            }

            if (src is Cpp2IL.Core.ISIL.Immediate imm)
            {
                chain.Add($"<-imm_0x{imm.UnsignedValue:X}");
                break;
            }

            chain.Add("<-" + (src?.GetType().Name ?? "null"));
            break;
        }

        // Prefix the chain with the accessed offset so families like +0x12F can be told apart from
        // genuine managed field reads at the same offset.
        var addendKey = match.Groups[4].Success ? "+0x" + match.Groups[4].Value : "+?";
        _ubChain.AddOrUpdate($"{addendKey} {string.Join(" ", chain)}", 1, (_, n) => n + 1);
    }

    /// <summary>
    /// When CPP2IL_DUMP_ISIL_FOR matches the method name, writes the full ISIL (with operand types and
    /// the type of each operand's defining local) for that method, so a fix can be designed against
    /// exact ground truth. Bounded to a handful of methods by the filter.
    /// </summary>
    private void MaybeDumpIsil(MethodAnalysisContext methodContext, string detail)
    {
        var fullName = methodContext.FullName;

        // single-method debug mode implies "dump it"
        var byOnly = OnlyMethodFilter != null && fullName.Contains(OnlyMethodFilter, StringComparison.Ordinal);

        if (!byOnly && ((IsilDumpFilter.Length == 0 && IsilDumpIssueFilter == null) || _isilDumped >= 40))
            return;

        var byName = IsilDumpFilter.Length > 0
                     && IsilDumpFilter.Any(f => fullName.Contains(f, StringComparison.Ordinal));
        var byIssue = IsilDumpIssueFilter?.IsMatch(detail) == true;

        if (!byOnly && !byName && !byIssue)
            return;

        Interlocked.Increment(ref _isilDumped);

        var sb = new System.Text.StringBuilder();
        sb.AppendLine($"===== {methodContext.DeclaringType?.DeclaringAssembly?.Name} :: {fullName}");
        sb.AppendLine($"first issue: {detail}");
        sb.AppendLine($"native address: 0x{methodContext.UnderlyingPointer:X} (rva 0x{methodContext.Rva:X})");
        sb.AppendLine("globals/locals:");

        foreach (var l in methodContext.Locals.OrderBy(l => l.Name, StringComparer.Ordinal))
            sb.AppendLine($"    local {l.Name} @ {l.Register}  type={(l.Type?.FullName ?? "<null>")}" +
                          (l.IsThis ? " [this]" : "") + (l.IsReturn ? " [ret]" : "") + (l.IsMethodInfo ? " [mi]" : ""));

        if (methodContext.ControlFlowGraph is { } cfg)
        {
            sb.AppendLine("instructions:");
            for (var i = 0; i < cfg.Instructions.Count; i++)
                sb.AppendLine($"    {i,4}: {cfg.Instructions[i]}");
        }
        else
        {
            sb.AppendLine("instructions: <no CFG>");
        }

        if (Cpp2IL.Core.Analysis.StackAnalyzer.LastAnalysisTrace is { } trace)
        {
            sb.AppendLine(trace);
            Cpp2IL.Core.Analysis.StackAnalyzer.LastAnalysisTrace = null;
        }

        _isilDump.Add(sb.ToString());
    }

    /// <summary>The instruction that defines <paramref name="localName"/>, or null.</summary>
    private static Cpp2IL.Core.ISIL.Instruction? FindDefinition(
        IEnumerable<Cpp2IL.Core.ISIL.Instruction> instructions, string localName)
    {
        foreach (var ins in instructions)
        {
            if (ins.OpCode == Cpp2IL.Core.ISIL.OpCode.Call)
            {
                // a call's result is operand 1; operand 0 is the call target
                if (ins.Operands.Count > 1 && ins.Operands[1] is Cpp2IL.Core.ISIL.LocalVariable c && c.Name == localName)
                    return ins;
                continue;
            }

            if (ins.Operands.Count > 0 && ins.Operands[0] is Cpp2IL.Core.ISIL.LocalVariable d && d.Name == localName)
                return ins;
        }

        return null;
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
        => FindIssue(body, out _);

    /// <summary>
    /// Classifies a method body and also reports <paramref name="issueCount"/>: how many
    /// <c>NoteDecompilerIssue</c> calls the body carries.
    /// </summary>
    /// <remarks>
    /// The count matters because the headline metric is all-or-nothing per method: a body is only clean
    /// when it carries none. A change that eliminates one issue kind therefore only moves the metric
    /// when it happens to be the LAST issue in a method, so knowing the per-method count (and which
    /// kinds remain in the methods sitting at one) is what tells us where the next real gain is.
    /// </remarks>
    private static (string? Reason, string Detail) FindIssue(CilMethodBody body, out int issueCount)
    {
        var ins = body.Instructions;

        issueCount = 0;
        var firstDetail = "";
        var found = false;

        for (var i = 0; i < ins.Count; i++)
        {
            if (ins[i].OpCode.Code != CilCode.Call || ins[i].Operand is not IMethodDescriptor md)
                continue;
            if (md.Name != NoteIssueMethodName)
                continue;

            issueCount++;

            if (found)
                continue;

            found = true;
            firstDetail = i > 0 && ins[i - 1].OpCode.Code == CilCode.Ldstr && ins[i - 1].Operand is string s
                ? s
                : "";
        }

        if (found)
            return ("placeholder", firstDetail);

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
        // Defer the per-method ISIL/CFG release so FillMethodBody can walk operand provenance; each
        // method is released in FillMethodBody's finally, so peak retention is one method's CFG.
        MethodAnalysisContext.DeferAnalysisDataRelease = true;

        List<AssemblyDefinition> ret;
        try
        {
            ret = base.BuildAssemblies(context);
        }
        finally
        {
            MethodAnalysisContext.DeferAnalysisDataRelease = false;
        }

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

            var countsPath = Path.Combine(root, "dll_il_recovery_safe.issuecounts.tsv");
            File.WriteAllLines(countsPath, new[] { "issueCount\treason\tassembly\tmethod\tfirstDetail" }
                .Concat(_issueCounts.OrderBy(x => x, StringComparer.OrdinalIgnoreCase)));

            Logger.InfoNewline($"[IlRecoverySafe] summary: {summary}", "IlRecoverySafe");
            Logger.InfoNewline($"[IlRecoverySafe] issues : {issuesPath}", "IlRecoverySafe");
            Logger.InfoNewline($"[IlRecoverySafe] counts : {countsPath}", "IlRecoverySafe");

            if (_stackUnderflow.Count > 0)
            {
                var stackPath = Path.Combine(root, "dll_il_recovery_safe.stackunderflow.tsv");
                File.WriteAllLines(stackPath, new[] { "method\tnativeAddr\tdetail" }
                    .Concat(_stackUnderflow.OrderBy(x => x, StringComparer.OrdinalIgnoreCase)));
                Logger.InfoNewline($"[IlRecoverySafe] stackunderflow ({_stackUnderflow.Count}): {stackPath}", "IlRecoverySafe");
            }

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

        // Note: no early return when there is nothing to report here - the remaining diagnostics (and
        // the ISIL dump) live further down and used to be skipped whenever this one was empty.
        if (top.Count > 0)
        {
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

        ReportMethodNotFoundDiagnostics(root);
        ReportUntypedBaseDiagnostics(root);
        ReportGuardRemoverDiagnostics(root);
        ReportStaticFieldDiagnostics(root);

        if (_isilDump.Count > 0)
        {
            try
            {
                var path = Path.Combine(root, "dll_il_recovery_safe.isildump.txt");
                File.WriteAllText(path, string.Join("\n", _isilDump));
                Logger.InfoNewline($"[IlRecoverySafe] isildump ({_isilDump.Count} methods): {path}", "IlRecoverySafe");
            }
            catch (Exception e)
            {
                Logger.ErrorNewline($"[IlRecoverySafe] failed to write isildump: {e.Message}", "IlRecoverySafe");
            }
        }
    }

    private void ReportUntypedBaseDiagnostics(string root)
    {
        var total = Volatile.Read(ref _ubTotal);
        var constTotal = Volatile.Read(ref _ubConstTotal);
        var constKnown = Volatile.Read(ref _ubConstKnownTotal);
        Logger.InfoNewline(
            $"[IlRecoverySafe][ub] untyped-base memory loads: total={total}, terminal-const-addr={constTotal}, " +
            $"of which known-metadata-global={constKnown} ({KnownPct(constKnown, constTotal)})",
            "IlRecoverySafe");

        foreach (var (chain, count) in _ubChain.OrderByDescending(kv => kv.Value).Take(25))
            Logger.InfoNewline($"[IlRecoverySafe][ub]   x{count}\t{chain}", "IlRecoverySafe");

        try
        {
            var lines = new List<string> { "chain\tcount" };
            lines.AddRange(_ubChain.OrderByDescending(kv => kv.Value).Select(kv => $"{kv.Key}\t{kv.Value}"));
            lines.Add("--- terminal const addr (addr | count | known_metadata_global) ---");
            lines.AddRange(_ubConstAddr.OrderByDescending(kv => kv.Value).Take(40)
                .Select(kv => $"{kv.Key}\t{kv.Value}\t{(_ubConstAddrKnown.ContainsKey(kv.Key) ? 1 : 0)}"));
            var path = Path.Combine(root, "dll_il_recovery_safe.untypedbase.tsv");
            File.WriteAllLines(path, lines);
            Logger.InfoNewline($"[IlRecoverySafe] untypedbase: {path}", "IlRecoverySafe");
        }
        catch (Exception e)
        {
            Logger.ErrorNewline($"[IlRecoverySafe] failed to write untypedbase: {e.Message}", "IlRecoverySafe");
        }
    }

    private void ReportGuardRemoverDiagnostics(string root)
    {

        var diags = Cpp2IL.Core.Analysis.MetadataInitGuardRemover.Diagnostics;

        var sb = new System.Text.StringBuilder();
        sb.AppendLine("key\tcount");
        foreach (var (key, count) in diags.OrderByDescending(kv => kv.Value))
            sb.AppendLine($"{key}\t{count}");

        sb.AppendLine("--- guard shape samples (as seen by TryRemoveGuard) ---");
        foreach (var sample in Cpp2IL.Core.Analysis.MetadataInitGuardRemover.GuardShapeSamples.Take(16))
            sb.AppendLine(sample);

        sb.AppendLine("--- flag-test guards that failed to excise ---");
        foreach (var sample in Cpp2IL.Core.Analysis.MetadataInitGuardRemover.GuardFailureSamples.Take(12))
            sb.AppendLine(sample);

        foreach (var (key, count) in diags.OrderByDescending(kv => kv.Value).Take(30))
            Logger.InfoNewline($"[IlRecoverySafe][guard]   x{count}\t{key}", "IlRecoverySafe");

        try
        {
            var path = Path.Combine(root, "dll_il_recovery_safe.guarddiag.tsv");
            File.WriteAllText(path, sb.ToString());
            Logger.InfoNewline($"[IlRecoverySafe] guarddiag: {path}", "IlRecoverySafe");
        }
        catch (Exception e)
        {
            Logger.ErrorNewline($"[IlRecoverySafe] failed to write guarddiag: {e.Message}", "IlRecoverySafe");
        }
    }

    /// <summary>
    /// Writes the static-field propagation histogram (see LocalVariables.StaticFieldDiag).
    /// Motivation: an ISIL dump showed 82 accesses to [..+0xB8] (static_fields) and ZERO resolutions
    /// to a FieldReference across 40 sampled methods, i.e. static field reads never become ldsfld.
    /// These counters say which guard rejects them - evidence before changing behaviour.
    /// </summary>
    private void ReportStaticFieldDiagnostics(string root)
    {
        var diags = Cpp2IL.Core.Analysis.LocalVariables.StaticFieldDiag;
        if (diags.IsEmpty)
            return;

        var sb = new System.Text.StringBuilder();
        sb.AppendLine("key\tcount");
        foreach (var (key, count) in diags.OrderByDescending(kv => kv.Value))
            sb.AppendLine($"{key}\t{count}");

        foreach (var (key, count) in diags.OrderByDescending(kv => kv.Value).Take(12))
            Logger.InfoNewline($"[IlRecoverySafe][sf]   x{count}\t{key}", "IlRecoverySafe");

        try
        {
            var path = Path.Combine(root, "dll_il_recovery_safe.sfdiag.tsv");
            File.WriteAllText(path, sb.ToString());
            Logger.InfoNewline($"[IlRecoverySafe] sfdiag: {path}", "IlRecoverySafe");
        }
        catch (Exception e)
        {
            Logger.ErrorNewline($"[IlRecoverySafe] failed to write sfdiag: {e.Message}", "IlRecoverySafe");
        }
    }

    private static string KnownPct(int known, int total)
        => total == 0 ? "n/a" : $"{100.0 * known / total:F1}%";

    private void ReportMethodNotFoundDiagnostics(string root)
    {
        var mb = Volatile.Read(ref _mnfInMethodsByAddress);
        var gi = Volatile.Read(ref _mnfInGenericImpl);
        var kf = Volatile.Read(ref _mnfInKeyFunctions);
        var nk = Volatile.Read(ref _mnfNearKnown);
        var uk = Volatile.Read(ref _mnfUnknown);
        Logger.InfoNewline(
            $"[IlRecoverySafe][mnf] Method-not-found totals: inMethodsByAddress={mb}, " +
            $"genericKnownButNotRegistered={gi}, keyFunction={kf}, nearKnown={nk}, unknown={uk}",
            "IlRecoverySafe");

        foreach (var (cls, count) in _mnfClass.OrderByDescending(kv => kv.Value))
            Logger.InfoNewline($"[IlRecoverySafe][mnf]   {cls}: {count}", "IlRecoverySafe");

        try
        {
            var lines = new List<string> { "class\tcount" };
            lines.AddRange(_mnfClass.OrderByDescending(kv => kv.Value).Select(kv => $"{kv.Key}\t{kv.Value}"));
            var topUnresolved = _mnfUnresolved.OrderByDescending(kv => kv.Value).Take(40)
                .Select(kv => $"0x{kv.Key:X}\t{kv.Value}");
            lines.AddRange(topUnresolved);
            lines.Add("--- in MethodsByAddress (addr | totalCandidates | sample) ---");
            lines.AddRange(_mnfInMba.OrderByDescending(kv => int.Parse(kv.Value.Split('\t')[0])).Take(15)
                .Select(kv => $"0x{kv.Key:X}\t{kv.Value}"));
            var path = Path.Combine(root, "dll_il_recovery_safe.mnfclassify.tsv");
            File.WriteAllLines(path, lines);
            Logger.InfoNewline($"[IlRecoverySafe] mnfclassify: {path}", "IlRecoverySafe");
        }
        catch (Exception e)
        {
            Logger.ErrorNewline($"[IlRecoverySafe] failed to write mnfclassify: {e.Message}", "IlRecoverySafe");
        }
    }
}