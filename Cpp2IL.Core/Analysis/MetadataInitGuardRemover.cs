using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes the IL2CPP runtime-metadata initialization guards the compiler emits near the top of
/// (almost) every method, plus il2cpp_runtime_class_init blocks.
/// </summary>
public static class MetadataInitGuardRemover
{
    /// <summary>
    /// Diagnostic counters, keyed by a short reason, incremented while scanning guards. Purely for
    /// offline analysis of why a guard was or was not excised. Off unless CPP2IL_GUARD_DIAG=1, so the
    /// hot path pays only a bool test; never affects behaviour.
    /// </summary>
    public static readonly ConcurrentDictionary<string, int> Diagnostics = new();

    private static readonly bool DiagEnabled =
        System.Environment.GetEnvironmentVariable("CPP2IL_GUARD_DIAG") == "1";

    /// <summary>Bounded sample of what a guard block actually looks like at removal time.</summary>
    public static readonly ConcurrentBag<string> GuardShapeSamples = new();

    /// <summary>Bounded sample of flag-test guards that could not be excised (block layout).</summary>
    public static readonly ConcurrentBag<string> GuardFailureSamples = new();

    internal static void Note(string key)
    {
        if (DiagEnabled)
            Diagnostics.AddOrUpdate(key, 1, (_, n) => n + 1);
    }
    private const string InitializeRuntimeMetadata = "il2cpp_codegen_initialize_runtime_metadata";
    private const string InitializeMethod = "il2cpp_codegen_initialize_method";
    private const string ClassInitExport = "il2cpp_runtime_class_init_export";
    private const string ClassInitActual = "il2cpp_runtime_class_init_actual";
    private const string ClassInitCodegen = "il2cpp_codegen_runtime_class_init";

    // Byte holding Il2CppClass's bitfield, of which bit 0 is initialized_and_no_error.
    // TODO this is almost certainly not correct on every version... but which?
    private const long InitialisedFlagOffset64 = 0x135;
    private const long InitialisedFlagOffset32 = 0xBD;

    // Verified per-target overrides for the same bitfield. A wrong entry is HARMLESS - the guard
    // simply does not match, which is exactly the pre-existing behaviour - so this table can only
    // ever enable an excision that is already correct, never cause a wrong one. Each entry MUST cite
    // the evidence it was verified against; unverified entries must not be added.
    //
    // (offset 0x12F, mask 2 = bit 1 "initialized"), 64-bit, metadata 24.x:
    //   verified on Unity 2019.4.21 / Android ARM64 / metadata 24.5
    //   raw ARM64:  LDRB W8, [X0 + 0x12F] ; TBZ W8, 0x1, <merge>
    //   ISIL:       And v46, [v44 + 0x12F], 2      (v44 = *(typeof(T)))
    //   evidence:   docs/FINDING-002-runtime-struct-layout-gap.md §5.0
    //   before this: 12,437 of 13,754 untyped-base placeholders came from this guard's dead residue
    private static readonly (long Offset, ulong Mask) InitialisedFlagTest24X64 = (0x12F, 2);

    // Offset of MethodInfo::rgctx_data
    private const long MethodRgctxOffset64 = 0x38;
    private const long MethodRgctxOffset32 = 0x1C;

    public static void Run(MethodAnalysisContext method)
    {
        var appContext = method.AppContext;

        // Preferred verified per-target (offset, mask) for the initialized bitfield; fall back to the
        // upstream defaults, which keeps behaviour unchanged wherever the override does not apply.
        var (offset, mask) = !appContext.Binary.is32Bit && appContext.MetadataVersion is >= 24f and < 27f
            ? InitialisedFlagTest24X64
            : (appContext.Binary.is32Bit ? InitialisedFlagOffset32 : InitialisedFlagOffset64, 1UL);

        Note($"metaver:{appContext.MetadataVersion}");
        Note($"is32:{appContext.Binary.is32Bit}");
        Note($"flagtest:off=0x{offset:X},mask=0x{mask:X}");

        Run(method.ControlFlowGraph!, offset, mask);
    }

    // Rewrite any metadata init calls we didn't remove into movs.
    public static void RewriteUnguardedInits(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands is not [StringLiteral { Value: InitializeRuntimeMetadata or InitializeMethod }, var result, var handle, ..])
                continue;

            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(result, handle);
        }
    }
    
    // Removes the lazy-init guards protecting a generic method's inlined RGCTX metadata lookups.
    public static void RunRgctx(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var rgctxOffset = method.AppContext.Binary.is32Bit ? MethodRgctxOffset32 : MethodRgctxOffset64;

        var removedAny = false;

        foreach (var guard in cfg.Blocks.ToList())
            removedAny |= TryRemoveRgctxGuard(cfg, guard, rgctxOffset);

        if (removedAny)
            DeadCodeEliminator.Run(cfg);
    }

    private static bool TryRemoveRgctxGuard(ISILControlFlowGraph cfg, Block guard, long rgctxOffset)
    {
        if (guard.BlockType != BlockType.TwoWay || guard.Successors.Count != 2
            || guard.Instructions.Count == 0 || guard.Instructions[^1].OpCode != OpCode.ConditionalJump)
            return false;

        var isRgctxGuard = guard.Instructions.Any(i =>
            i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
            && (IsRgctxLoad(i.Operands[1], rgctxOffset) && IsZero(i.Operands[2])
                || IsRgctxLoad(i.Operands[2], rgctxOffset) && IsZero(i.Operands[1])));

        if (!isRgctxGuard)
            return false;

        var first = guard.Successors[0];
        var second = guard.Successors[1];

        // treat region calls as init boilerplate, exactly as the class-init flag test does
        return TryExcise(cfg, guard, first, second, true)
            || TryExcise(cfg, guard, second, first, true);
    }

    private static bool IsRgctxLoad(IOperand operand, long rgctxOffset) =>
        operand is MemoryOperand { Index: null, Scale: 0, Base: LocalVariable { Type: RuntimeMethodInfoAnalysisContext } } memory
        && memory.Addend == rgctxOffset;

    private static bool IsZero(IOperand operand) => operand is Immediate { Value: 0 };

    public static void Run(ISILControlFlowGraph cfg, long initialisedFlagOffset, ulong initialisedFlagMask)
    {
        var removedAny = false;

        foreach (var guard in cfg.Blocks.ToList())
            removedAny |= TryRemoveGuard(cfg, guard, initialisedFlagOffset, initialisedFlagMask);

        removedAny |= RemoveBareClassInitCalls(cfg);

        if (removedAny)
            DeadCodeEliminator.Run(cfg);
    }

    // wasm keeps the initialized-flag check inside the class-init function, so callers make bare unguarded
    // calls with no region to excise (just drop the call)
    private static bool RemoveBareClassInitCalls(ISILControlFlowGraph cfg)
    {
        var removedAny = false;

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (!instruction.IsCall
                    || instruction.Operands[0] is not StringLiteral { Value: ClassInitExport or ClassInitActual or ClassInitCodegen })
                    continue;

                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
                removedAny = true;
            }
        }

        return removedAny;
    }

    private static bool TryRemoveGuard(ISILControlFlowGraph cfg, Block guard, long initialisedFlagOffset, ulong initialisedFlagMask)
    {
        if (guard.BlockType != BlockType.TwoWay || guard.Successors.Count != 2
            || guard.Instructions.Count == 0 || guard.Instructions[^1].OpCode != OpCode.ConditionalJump)
        {
            Note("guard:skip_not_shape");
            return false;
        }

        // Sample what this guard actually contains at removal time (bounded; used offline to match the
        // real flag-test shape, which is not the upstream single-instruction form on 24.x/ARM64).
        if (DiagEnabled && GuardShapeSamples.Count < 16
            && guard.Instructions.Any(i => i.OpCode is OpCode.Move or OpCode.And))
        {
            var desc = string.Join(" | ",
                guard.Instructions.Select(i => i.ToString()));
            GuardShapeSamples.Add(desc);
        }

        // see if we're checking Il2CppClass's initialized bitfield
        // that means this is runtime_init boilerplate and we can drop the block.
        // Two shapes occur: after LDRB+AND fusion a single "And tmp, [base+off], mask",
        // and before fusion a "Move tmp,[base+off]" followed by "And tmp,tmp,mask" (the 24.x/ARM64
        // codegen keeps them apart until the fusion pass that runs after this remover).
        var initialisedFlagTest = IsInlinedFlagTest(guard.Instructions, initialisedFlagOffset, initialisedFlagMask);
        Note("guard:flagtest=" + initialisedFlagTest);

        // Either successor could be the init entry; the other is then the merge.
        var first = guard.Successors[0];
        var second = guard.Successors[1];

        var excised = TryExcise(cfg, guard, first, second, initialisedFlagTest)
                      || TryExcise(cfg, guard, second, first, initialisedFlagTest);
        Note(excised ? "guard:excised" : "guard:excise_failed");
        if (!excised && initialisedFlagTest && DiagEnabled && GuardFailureSamples.Count < 12)
            RecordFailureSample(guard, first, second);

        return excised;
    }

    /// <summary>Captures the exact block layout of a flag-test guard that could not be excised.</summary>
    private static void RecordFailureSample(Block guard, Block first, Block second)
    {
        static string Describe(Block block)
        {
            var text = string.Join(" | ", block.Instructions.Select(i => i.ToString()));
            if (text.Length > 700)
                text = text[..700] + "…";

            return $"{block.BlockType}[succ={block.Successors.Count},pred={block.Predecessors.Count}] {text}";
        }

        GuardFailureSamples.Add(
            $"GUARD {Describe(guard)}\n  SUCC0 {Describe(first)}\n  SUCC1 {Describe(second)}");
    }

    private static bool IsInlinedFlagTest(IReadOnlyList<Instruction> instructions, long initialisedFlagOffset, ulong initialisedFlagMask)
    {
        // shape 1: And tmp, [base+off], mask   (LDRB + AND already fused by a later pass)
        foreach (var i in instructions)
        {
            if (i.OpCode != OpCode.And
                || i.Operands is not [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable } flag, { } mask])
                continue;

            Note($"guard:and_off=0x{flag.Addend & 0xFFFF:X},mask={(mask is Immediate imm1 ? $"0x{(ulong)imm1.Value:X}" : "nonimm")}");
            if (flag.Addend == initialisedFlagOffset && IsMask(mask, initialisedFlagMask))
                return true;
        }

        // shape 2: Move tmp,[base+off]; And result,tmp,mask   (pre-fusion, actual shape on 24.x/ARM64).
        // NOTE: the And writes a NEW local (SSA), only its source is the Move's target.
        for (var idx = 0; idx < instructions.Count; idx++)
        {
            var i = instructions[idx];
            if (i.OpCode != OpCode.Move
                || i.Operands is not [LocalVariable dst, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable } flag]
                || flag.Addend != initialisedFlagOffset)
                continue;

            for (var j = idx + 1; j < instructions.Count; j++)
            {
                var a = instructions[j];
                if (a.OpCode != OpCode.And
                    || a.Operands is not [_, LocalVariable src, { } aMask]
                    || src.Name != dst.Name)
                    continue;

                Note($"guard:and2:off=0x{flag.Addend & 0xFFFF:X},mask={(aMask is Immediate imm2 ? $"0x{(ulong)imm2.Value:X}" : "nonimm")},dst={dst.Name}");
                if (IsMask(aMask, initialisedFlagMask))
                    return true;
            }
        }

        return false;
    }

    private static bool IsMask(IOperand operand, ulong mask) => operand is Immediate imm && (ulong)imm.Value == mask;

    private static bool TryExcise(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge, bool initialisedFlagTest)
    {
        if (merge == cfg.EntryBlock || merge == cfg.ExitBlock)
            return false;

        if (!TryCollectRegion(cfg, guard, initEntry, merge, initialisedFlagTest, out var region))
            return false;

        Excise(cfg, guard, initEntry, merge, region);
        return true;
    }

    private static bool TryCollectRegion(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge,
        bool initialisedFlagTest, out HashSet<Block> region)
    {
        region = [];

        if (initEntry == merge || initEntry == guard)
        {
            Note("collect:fail_same");
            return false;
        }

        var sawMetadataInit = false;
        var sawClassInit = false;
        var sawFlagStore = false;
        var reconverges = false;

        var queue = new Queue<Block>();
        queue.Enqueue(initEntry);

        while (queue.Count > 0)
        {
            var block = queue.Dequeue();

            if (block == merge)
            {
                reconverges = true;
                continue;
            }

            // The region must not run into the method boundary or loop back through the guard.
            if (block == cfg.EntryBlock || block == cfg.ExitBlock || block == guard)
            {
                Note($"collect:fail_boundary:{(block == cfg.ExitBlock ? "exit" : block == cfg.EntryBlock ? "entry" : "guard")}");
                return false;
            }

            if (!region.Add(block))
                continue;

            var pureRuntimeTest = initialisedFlagTest && IsPureRuntimeTestBlock(block);

            if (!pureRuntimeTest && !ClassifyBlock(block, initialisedFlagTest, ref sawMetadataInit, ref sawClassInit, ref sawFlagStore, out var offending))
            {
                Note($"collect:fail_classify:{(offending == null ? "?" : offending.OpCode.ToString())}" +
                     (initialisedFlagTest ? ":flag" : ""));
                return false;
            }

            foreach (var successor in block.Successors)
                queue.Enqueue(successor);
        }

        // A region is acceptable only if either (a) a class-init / metadata-init was seen inside it, or
        // (b) the flag test itself already matched the *verified* Il2CppClass initialized-bitfield
        // (offset+mask are precise enough that this can ONLY be a class-init guard; on 24.x/ARM64 the
        // class-init call often lives outside the two successors, so the region is just an empty
        // trampoline and demanding sawClassInit would reject every real guard).
        if (!reconverges || (!initialisedFlagTest && !(sawClassInit || (sawMetadataInit && sawFlagStore))))
        {
            Note(!reconverges ? "collect:fail_no_reconverge" : "collect:fail_no_classinit");
            return false;
        }

        var collected = region;
        foreach (var block in collected)
        {
            if (block.Predecessors.Any(predecessor => predecessor != guard && !collected.Contains(predecessor)))
            {
                Note("collect:fail_outer_pred");
                return false;
            }

            if (block.Successors.Any(successor => successor != merge && !collected.Contains(successor)))
            {
                Note("collect:fail_outer_succ");
                return false;
            }
        }

        Note($"collect:ok:{collected.Count}");
        return true;
    }

    // A region block is acceptable only if every instruction is intra-region control flow, an init
    // call, the flag store, or otherwise side-effect-free (writes a local, not memory). A managed call
    // or any other store would have an effect we cannot silently drop, so it disqualifies the region.
    private static bool ClassifyBlock(Block block, bool initialisedFlagTest, ref bool sawMetadataInit, ref bool sawClassInit, ref bool sawFlagStore,
        out Instruction? offending)
    {
        offending = null;

        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Jump:
                    break;

                // Behind an initialized_and_no_error test the callee is the class initializer, even if we didn't resolve it.
                // If we didn't, that's fine, just skip.
                case OpCode.Call or OpCode.CallVoid when initialisedFlagTest:
                    sawClassInit = true;
                    break;

                case OpCode.Call or OpCode.CallVoid:
                    if (instruction.Operands is not [StringLiteral { Value: var name }, ..])
                    {
                        offending = instruction;
                        return false;
                    }

                    if (name is InitializeRuntimeMetadata or InitializeMethod)
                        sawMetadataInit = true;
                    else if (name is ClassInitExport or ClassInitActual or ClassInitCodegen)
                        sawClassInit = true;
                    else
                    {
                        offending = instruction;
                        return false;
                    }

                    break;

                case OpCode.Move when instruction.Operands is [MemoryOperand { IsConstant: true }, _]:
                    sawFlagStore = true;
                    break;

                default:
                    if (!IsSideEffectFree(instruction))
                    {
                        offending = instruction;
                        return false;
                    }

                    break;
            }
        }

        return true;
    }

    // A block that only reads memory into locals, compares, and branches - the shape of the extra
    // runtime-state test IL2CPP chains after the initialized bit (observed: klass->cctor_started at
    // +0xE0, branching to the same merge as the initialized test). Deleting such a block cannot drop
    // work: it has no call, no store, no phi and no return, so its only effect is a branch that the
    // surrounding checks already require to reconverge on the same merge.
    private static bool IsPureRuntimeTestBlock(Block block)
    {
        if (block.Instructions.Count == 0)
            return false;

        var sawBranch = false;

        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.ConditionalJump:
                    sawBranch = true;
                    break;
                case OpCode.Jump or OpCode.Nop:
                    break;
                default:
                    if (!IsSideEffectFree(instruction))
                        return false;

                    break;
            }
        }

        return sawBranch;
    }

    // True for instructions that only compute a value into a local (or do nothing). A store - any
    // instruction whose destination operand is a memory or field reference rather than a local - is
    // excluded, as is anything that transfers control or merges values (phi/return/indirect).
    private static bool IsSideEffectFree(Instruction instruction) =>
        instruction.OpCode switch
        {
            OpCode.Nop => true,
            OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Not or OpCode.Negate
                or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                => instruction.Operands is [LocalVariable, ..],
            _ => false,
        };

    internal static void Excise(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge, HashSet<Block> region)
    {
        // 1. Repair the merge's phis: drop the inputs from the region's back-edges.
        for (var i = merge.Predecessors.Count - 1; i >= 0; i--)
        {
            if (!region.Contains(merge.Predecessors[i]))
                continue;

            foreach (var phi in merge.Instructions)
                if (phi.OpCode == OpCode.Phi && 1 + i < phi.Operands.Count)
                    phi.RemoveOperandAt(1 + i);

            merge.Predecessors.RemoveAt(i);
        }

        // 2. Fold the guard so it goes straight to the merge.
        guard.Successors.Remove(initEntry);
        initEntry.Predecessors.Remove(guard);

        var terminator = guard.Instructions[^1];
        terminator.OpCode = OpCode.Jump;
        terminator.SetOperands(merge);
        guard.CalculateBlockType();

        // 3. Delete the region. 
        foreach (var block in region)
        {
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            foreach (var predecessor in block.Predecessors)
                predecessor.Successors.Remove(block);

            block.Successors.Clear();
            block.Predecessors.Clear();
            cfg.Blocks.Remove(block);
        }
    }
}
