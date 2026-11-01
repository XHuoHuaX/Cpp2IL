using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Folds IL2CPP's type-materialisation idiom back to <c>typeof(T)</c>.
///
/// <para><b>Shape</b> (verified against real output, see docs/FINDING-014):</para>
/// <code>
///   Move vX (Il2CppClass&lt;T&gt;), typeof(T)      ; load the runtime class pointer for T
///   ...                                          ; any control flow, the two need not share a block
///   Call System.Type.GetTypeFromHandle, dest, [vX]
///   â‡?///   Move dest (System.Type), typeof(T)
/// </code>
///
/// <para><b>Why the fold is exact, not a guess.</b> <c>GetTypeFromHandle</c> is defined as "the
/// <see cref="System.Type"/> that this handle denotes", and the handle being fed in is the runtime
/// class pointer of the very type the preceding <c>Move</c> materialised. So the result IS
/// <c>typeof(T)</c> by construction - nothing is invented (red line C5). When any part of the shape
/// does not hold, the instruction is left untouched.</para>
///
/// <para><b>Why it has to happen at all.</b> <see cref="RuntimeClassTypeAnalysisContext"/> is a
/// synthetic, pointer-sized pseudo-type with no managed counterpart, so the emitter lowers the
/// <c>Move</c> to <c>Ldc_I4_0</c> and the decompiled C# comes out as the un-compilable pair
/// <c>IntPtr p = (IntPtr)typeof(T); Type t = Type.GetTypeFromHandle((RuntimeTypeHandle)(long)p);</c>
/// (CS0030 x2 per site). After the fold the local has no remaining use, so the existing unused-local
/// pruner deletes the bogus <c>Move</c> along with it.</para>
///
/// <para>The operand may arrive either bare or dereferenced (<c>[vX]</c>) depending on how the
/// calling convention modelled it, so both are accepted.</para>
/// </summary>
public static class TypeofFromHandleFolder
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
            // A call carries one operand per argument plus trailing register operands that the
            // argument trimmer only drops at the very end of the pipeline, so the count is not exact:
            // [target, result, arg0, ...extra].
            if (instruction.OpCode != OpCode.Call ||
                instruction.Operands.Count < 3 ||
                !IsGetTypeFromHandle(method, instruction.Operands[0]) ||
                instruction.Destination is not LocalVariable result ||
                UnderlyingLocal(instruction.Operands[2]) is not { } handleLocal)
                continue;

            // Soundness: the operand must have exactly one definition in the whole method, and that
            // definition must be the type materialisation. Anything else (a merge, a phi lowered to
            // several moves, an unrelated producer) is left alone.
            if (!definitions.TryGetValue(handleLocal, out var defs) || defs.Count != 1)
                continue;

            var definition = defs[0];
            if (definition.OpCode != OpCode.Move ||
                definition.Operands.Count != 2 ||
                definition.Operands[1] is not TypeAnalysisContext materialised ||
                RepresentedManagedType(materialised) is not { } type)
                continue;

            Probe(method, $"FOLD typeof({type.FullName})");
            instruction.OpCode = OpCode.Move;
            instruction.SetOperands([result, type]);
            changed = true;
        }

        return changed;
    }

    /// <summary>
    /// The managed type that <paramref name="operand"/> denotes, or null when it does not denote one.
    /// A runtime class pointer records the type it describes; a plain type reference is already that
    /// type. The other synthetic types (rgctx tables, static storage) describe runtime infrastructure
    /// rather than a single managed type, so they must not be folded.
    /// </summary>
    private static TypeAnalysisContext? RepresentedManagedType(TypeAnalysisContext operand) => operand switch
    {
        RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
        RgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext => null,
        _ => operand,
    };

    /// <summary>The local a call argument reads, whether it arrives bare or as a plain dereference of one.</summary>
    private static LocalVariable? UnderlyingLocal(IOperand operand) => operand switch
    {
        LocalVariable local => local,
        MemoryOperand { Base: LocalVariable { } baseLocal, Index: null, Addend: 0 } => baseLocal,
        _ => null,
    };

    /// <summary>
    /// Every instruction that writes each local. After SSA removal a local may have one definition per
    /// predecessor, which is exactly why the caller requires <c>Count == 1</c> before folding.
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