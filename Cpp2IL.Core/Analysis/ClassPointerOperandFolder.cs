using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Replaces IL2CPP runtime class pointers with the managed types they denote, in every operand position
/// that is defined to name a type.
///
/// <para><b>Why this is exact, not a guess.</b> An IL2CPP class pointer (<c>Il2CppClass*</c>) is the
/// runtime metadata object <em>of one specific managed type</em>; <see cref="RuntimeClassTypeAnalysisContext"/>
/// records exactly which. So "the class pointer of T" and "the type T" are the same entity seen from two
/// levels, and substituting one for the other cannot invent a value (red line C5). Whenever any part of the
/// shape does not hold, the instruction is left untouched.</para>
///
/// <para><b>Two shapes occur in real output</b> (see docs/FINDING-014):
/// <list type="bullet">
/// <item>direct: <c>Move vX (Il2CppClass&lt;T&gt;), typeof(T)</c> â€?<c>use [vX]</c> â€?the pointer is
/// materialised into a local and read back. Requires the local to have exactly one definition;</item>
/// <item>inline: the operand is already a <see cref="RuntimeClassTypeAnalysisContext"/>, so it only needs
/// unwrapping.</item>
/// </list></para>
///
/// <para><b>Positions handled.</b> Only opcodes whose operand is defined to be a type name:</para>
/// <list type="table">
/// <item><term><c>Newobj</c></term><description>operand 1 â€?the type to allocate</description></item>
/// <item><term><c>NewArr</c></term><description>operand 1 â€?the array element type</description></item>
/// <item><term><c>Box</c></term><description>operand 1 â€?the type to box as</description></item>
/// <item><term><c>Throw</c></term><description>operand 0 â€?the exception type (no destination)</description></item>
/// <item><term><c>Call</c> to <c>System.Type.GetTypeFromHandle</c></term><description>operand 2 â€?the handle,
/// collapsed entirely into <c>typeof(T)</c> (a Move, not a call)</description></item>
/// </list>
///
/// <para><b>Why it matters for compilation.</b> Every one of those positions currently receives a pointer
/// with no managed counterpart, so the emitter's only recourse is <c>Ldc_I4_0</c> and the decompiled C#
/// comes out as <c>IntPtr p = (IntPtr)typeof(T);</c> (CS0030) or as a <c>newobj</c> that degrades to
/// <c>null</c>. Collapsing the pointer to the type restores what the C# source said, and the local behind it
/// becomes dead, so the existing unused-local pruner deletes it.</para>
/// </summary>
public static class ClassPointerOperandFolder
{
    // TEMPORARY probe - remove before committing.
    private static readonly bool ProbeEnabled = !string.IsNullOrEmpty(Environment.GetEnvironmentVariable("CPP2IL_TYPEFOLD_DEBUG"));

    private static void Probe(MethodAnalysisContext method, string message)
    {
        if (ProbeEnabled)
            Console.WriteLine($"[typefold] {method.DeclaringType?.FullName}::{method.Name} {message}");
    }

    public static bool Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg)
            return false;

        var definitions = CollectDefinitions(cfg);
        var changed = false;

        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.OpCode == OpCode.Call &&
                TryCollapseGetTypeFromHandle(method, instruction, definitions))
                changed = true;

            var typeOperandIndex = TypeOperandIndex(instruction);
            if (typeOperandIndex < 0 || typeOperandIndex >= instruction.Operands.Count)
                continue;

            if (ResolveToManagedType(instruction.Operands[typeOperandIndex], definitions) is not { } type)
                continue;

            Probe(method, $"{instruction.OpCode} type operand -> {type.FullName}");
            instruction.SetOperand(typeOperandIndex, type);
            changed = true;
        }

        return changed;
    }

    /// <summary>
    /// <c>Type.GetTypeFromHandle(handle)</c> where the handle is the class pointer of T is exactly
    /// <c>typeof(T)</c>, so the call collapses into a move.
    /// </summary>
    private static bool TryCollapseGetTypeFromHandle(MethodAnalysisContext method, Instruction instruction,
        Dictionary<LocalVariable, List<Instruction>> definitions)
    {
        // A call carries one operand per argument plus trailing register operands that the argument
        // trimmer only drops at the very end of the pipeline, so the count is not exact:
        // [target, result, arg0, ...extra].
        if (instruction.Operands.Count < 3 ||
            !IsGetTypeFromHandle(method, instruction.Operands[0]) ||
            instruction.Destination is not LocalVariable result ||
            ResolveToManagedType(instruction.Operands[2], definitions) is not { } type)
            return false;

        Probe(method, $"GetTypeFromHandle -> typeof({type.FullName})");
        instruction.OpCode = OpCode.Move;
        instruction.SetOperands([result, type]);
        return true;
    }

    /// <summary>
    /// The index of the operand that names a type, for the opcodes that have one, or -1.
    /// </summary>
    private static int TypeOperandIndex(Instruction instruction) => instruction.OpCode switch
    {
        OpCode.Newobj or OpCode.NewArr or OpCode.Box => 1,
        OpCode.Throw => 0,
        _ => -1,
    };

    /// <summary>
    /// The managed type denoted by <paramref name="operand"/>, or null when it does not denote one.
    /// Accepts the pointer inline, bare in a local, or deferred through a dereference of a local; in the
    /// local cases the definition must be unique, otherwise the value may come from another path.
    /// </summary>
    private static TypeAnalysisContext? ResolveToManagedType(IOperand operand,
        Dictionary<LocalVariable, List<Instruction>> definitions)
    {
        if (operand is TypeAnalysisContext direct)
            return RepresentedManagedType(direct);

        if (UnderlyingLocal(operand) is not { } local)
            return null;

        if (!definitions.TryGetValue(local, out var defs) || defs.Count != 1)
            return null;

        var definition = defs[0];
        if (definition.OpCode != OpCode.Move ||
            definition.Operands.Count != 2 ||
            definition.Operands[1] is not TypeAnalysisContext materialised)
            return null;

        return RepresentedManagedType(materialised);
    }

    /// <summary>
    /// The managed type that <paramref name="operand"/> denotes, or null when it does not denote one.
    /// A runtime class pointer records the type it describes; a plain type reference is already that
    /// type. The other synthetic types (rgctx tables, static storage) describe runtime infrastructure
    /// rather than a single managed type, so they must not be substituted.
    /// </summary>
    private static TypeAnalysisContext? RepresentedManagedType(TypeAnalysisContext operand) => operand switch
    {
        RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
        RgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext => null,
        _ => operand,
    };

    /// <summary>The local an operand reads, whether it arrives bare or as a plain dereference of one.</summary>
    private static LocalVariable? UnderlyingLocal(IOperand operand) => operand switch
    {
        LocalVariable local => local,
        MemoryOperand { Base: LocalVariable { } baseLocal, Index: null, Addend: 0 } => baseLocal,
        _ => null,
    };

    /// <summary>
    /// Every instruction that writes each local. After SSA removal a local may have one definition per
    /// predecessor, which is exactly why the caller requires <c>Count == 1</c> before substituting.
    /// </summary>
    private static Dictionary<LocalVariable, List<Instruction>> CollectDefinitions(ISILControlFlowGraph cfg)
    {
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();

        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.Destination is not LocalVariable local)
                continue;

            if (!definitions.TryGetValue(local, out var list))
                definitions[local] = list = [];

            list.Add(instruction);
        }

        return definitions;
    }

    private static bool IsGetTypeFromHandle(MethodAnalysisContext method, IOperand target)
    {
        if (target is MethodAnalysisContext resolved)
            return IsTheMethod(resolved);

        // Call targets are resolved to method contexts earlier in the pipeline, but tolerate an address
        // operand so the fold does not silently depend on that ordering.
        if (target is Immediate immediate && method.AppContext.MethodsByAddress.TryGetValue(immediate.UnsignedValue, out var candidates))
            return candidates.Any(IsTheMethod);

        return false;
    }

    private static bool IsTheMethod(MethodAnalysisContext candidate) =>
        candidate.Name == "GetTypeFromHandle" && candidate.DeclaringType?.FullName == "System.Type";
}