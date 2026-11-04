using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public class StackAnalyzer
{
    [DebuggerDisplay("Size = {Size}")]
    private class StackState
    {
        public int Size;
        public StackState Copy() => new() { Size = this.Size };
    }

    private Dictionary<Block, StackState> _inComingState = [];
    private Dictionary<Block, StackState> _outGoingState = [];
    private Dictionary<Instruction, StackState> _instructionState = [];



    /// <summary>
    /// Max allowed count of blocks to visit (-1 for no limit).
    /// </summary>
    public static int MaxBlockVisitCount = 500000; //High enough to not be legitimately hit, but still give up if something loops infinitely.

    /// <summary>
    /// The deepest stack an emitted body can plausibly have. Exceeding it means the depth is being raised
    /// once per loop iteration, which is what bounds the monotone walk in <see cref="TraverseGraph"/>.
    /// </summary>
    private const int MaxStackDepth = 512;

    public static void Analyze(MethodAnalysisContext method)
    {
        var analyzer = new StackAnalyzer();

        LastAnalysisTrace = null; // never let a previous method's trace be attributed to this one

        var graph = method.ControlFlowGraph!;
        graph.RemoveUnreachableBlocks(); // Without this indirect jumps (in try catch i think) cause some weird stuff

        analyzer._method = method;
        analyzer._inComingState = new Dictionary<Block, StackState> { { graph.EntryBlock, new StackState() } };

        analyzer.TraverseGraph(graph.EntryBlock);

        // The exit block has no outgoing state if it was never reached (e.g. every path loops or
        // throws). That's fine - just skip the end-of-method stack balance check in that case.
        if (analyzer._outGoingState.TryGetValue(graph.ExitBlock, out var outDelta) && outDelta.Size != 0)
        {
            var outText = outDelta.Size < 0 ? "-" + (-outDelta.Size).ToString("X") : outDelta.Size.ToString("X");
            method.AddWarning($"Method ends with non empty stack ({outText}), the output could be wrong!");

            if (System.Environment.GetEnvironmentVariable("CPP2IL_STACK_DEBUG") == "1")
                LastAnalysisTrace = BuildTrace(graph, analyzer);
        }

        analyzer.ResolveFrameAliases(graph);
        analyzer.CorrectOffsets(graph);
        ReplaceStackWithRegisters(method);

        graph.RemoveNops();
        graph.RemoveEmptyBlocks();
    }

    // consider mov [reg], [stack pointer]
    // now we need to handle [reg] as if it were a stack pointer, forever.
    private void ResolveFrameAliases(ISILControlFlowGraph graph)
    {
        var aliases = new Dictionary<string, int>();

        foreach (var instruction in graph.EntryBlock.Successors.SelectMany(b => b.Instructions))
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [Register destination, Register { Name: "rsp" }] }
                && _instructionState.TryGetValue(instruction, out var atCopy))
                aliases[destination.Name] = atCopy.Size;
        }

        if (aliases.Count == 0)
            return;

        // Following a register that gets reassigned would need flow analysis, so stop trusting it entirely
        foreach (var instruction in graph.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [Register, Register { Name: "rsp" }] })
                continue;

            if (instruction.Destination is Register written)
                aliases.Remove(written.Name);
        }

        foreach (var instruction in graph.Instructions)
        {
            if (!_instructionState.TryGetValue(instruction, out var state))
                continue;

            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand { Index: null, Scale: 0, Base: Register frameBase } memory)
                    continue;

                if (!aliases.TryGetValue(frameBase.Name, out var frameOffset))
                    continue;

                instruction.SetOperand(i, new StackOffset((int)(frameOffset + memory.Addend - state.Size)));
            }
        }
    }

    private void CorrectOffsets(ISILControlFlowGraph graph)
    {
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is { OpCode: OpCode.ShiftStack })
                {
                    // Nop the shift stack instruction
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                    continue;
                }

                int? state = null;

                // Correct offset for stack operands.
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    var op = instruction.Operands[i];

                    var slot = op switch
                    {
                        StackOffset direct => direct,
                        AddressOf { Target: StackOffset addressed } => addressed,
                        _ => (StackOffset?)null
                    };

                    if (slot is { } offset)
                    {
                        // This can only be done before modifying any of the instruction operands,
                        // as doing so will make the dictionary lookup impossible.
                        state ??= _instructionState[instruction].Size;

                        var actual = new StackOffset(state.Value + offset.Offset);
                        instruction.SetOperand(i, op is AddressOf ? new AddressOf(actual) : actual);
                    }
                }
            }
        }
    }

    // Traverse the graph and calculate the stack state for each block and instruction
    private void TraverseGraph(Block initialBlock, int initialVisitedBlockCount = 0)
    {
        var blockLevelState = new Stack<(Block, int)>();
        blockLevelState.Push((initialBlock, initialVisitedBlockCount));

        while (blockLevelState.Count > 0)
        {
            var (block, visitedBlockCount) = blockLevelState.Pop();

            // Copy current state
            var incomingState = _inComingState[block];
            var currentState = incomingState.Copy();


            // Process instructions
            foreach (var instruction in block.Instructions)
            {
                _instructionState[instruction] = currentState;

                if (instruction.OpCode == OpCode.ShiftStack)
                {
                    var offset = (int)((Immediate)instruction.Operands[0]).Value;
                    currentState = currentState.Copy();
                    currentState.Size += offset;
                }
                else if (block.Instructions[^1] == instruction && block.BlockType == BlockType.TailCall)
                {
                    // Tail calls clear stack
                    currentState = currentState.Copy();
                    currentState.Size = 0;
                }
            }

            // Tail calls clear stack
            if (block.BlockType == BlockType.TailCall)
                currentState.Size = 0;

            // A block ending in `call <unresolved native target>; ret` is a noreturn call - in IL2CPP
            // that is the cold path of a null check, which calls a throw helper and therefore never
            // gives the frame back. Its (correctly) negative depth must not poison the method's final
            // balance check. Slot names inside the block were already computed above, so nothing but
            // the end-of-method comparison is affected.
            if (EndsInUnresolvedCallThenReturn(block))
                currentState.Size = 0;

            _outGoingState[block] = currentState;

            visitedBlockCount++;

            if (MaxBlockVisitCount != -1 && visitedBlockCount > MaxBlockVisitCount)
                throw new DecompilerException($"Stack state not settling! ({visitedBlockCount} blocks already visited)");

            // Deeper than any real frame. Because the walk is monotone, a method that raises the depth in a
            // loop would otherwise climb forever; this is the bound that makes it terminate. Flagged rather
            // than silent, because everything downstream from here is suspect.
            if (currentState.Size > MaxStackDepth)
            {
                _method?.AddWarning($"stack depth passed {MaxStackDepth} bytes; stopped propagating through this block");
                continue;
            }

            // Visit successors
            foreach (var successor in block.Successors)
            {
                // Already visited
                if (_inComingState.TryGetValue(successor, out var existingState))
                {
                    if (currentState.Size > existingState.Size)
                    {
                        // Monotone: only ever raise a block's incoming depth. Overwriting whenever the depth
                        // merely *differs* does not converge - a loop that pushes per iteration raises the
                        // depth forever, and a join whose predecessors disagree flips between two values.
                        // Raising only terminates, and is also the conservative answer for slot naming.
                        _inComingState[successor] = currentState.Copy();
                        blockLevelState.Push((successor, visitedBlockCount + 1));
                    }
                    else if (currentState.Size < existingState.Size)
                    {
                        _method?.AddWarning(
                            $"stack depth at a block would drop from {existingState.Size:X} to {currentState.Size:X}; kept the deeper one");
                    }
                }
                else
                {
                    // Set incoming delta and add to queue
                    _inComingState[successor] = currentState.Copy();
                    blockLevelState.Push((successor, visitedBlockCount + 1));
                }
            }
        }
    }

    /// <summary>
    /// Debug-only: a per-block dump of the simulated frame size, written when
    /// <c>CPP2IL_STACK_DEBUG=1</c> and the method ends unbalanced. Lets a single method be compared
    /// against the real prologue/epilogue instead of guessing which instruction lost its ShiftStack.
    /// </summary>
    public static string? LastAnalysisTrace;

    private MethodAnalysisContext? _method;

    /// <summary>
    /// True when the block's last real instruction is <c>Return</c> and the one before it calls a target
    /// that is not a known managed method. IL2CPP emits such blocks for the cold path of a null check
    /// (<c>cbz x0, &lt;cold&gt;</c> ... <c>ret</c> ... <c>cold: bl &lt;throw helper&gt;</c>) where the helper
    /// never returns, so the frame is never restored. Managed calls also carry their target as an
    /// immediate, hence the "not in MethodsByAddress" test.
    /// </summary>
    private bool EndsInUnresolvedCallThenReturn(Block block)
    {
        var instructions = block.Instructions;
        if (instructions.Count == 0)
            return false;

        // Shape 1: `call ...; ret` still inside one block.
        if (instructions[^1].OpCode == OpCode.Return)
        {
            for (var i = instructions.Count - 2; i >= 0; i--)
            {
                if (instructions[i].OpCode == OpCode.Nop)
                    continue;

                return IsUnresolvedCall(instructions[i]);
            }

            return false;
        }

        // Shape 2: the CFG splits a block after every call, so the call is the block terminator and the
        // Return is the sole instruction of its successor.
        return IsUnresolvedCall(instructions[^1])
               && block.Successors.Count == 1
               && block.Successors[0].Instructions is [var only]
               && only.OpCode == OpCode.Return;
    }

    /// <summary>
    /// A call whose target is not a known managed method. Managed calls also carry their target as an
    /// immediate, hence the lookup - an unresolved target means native/helper code whose return
    /// convention we cannot model.
    /// </summary>
    private bool IsUnresolvedCall(Instruction instruction)
    {
        if (instruction.OpCode is not (OpCode.Call or OpCode.CallVoid))
            return false;

        if (instruction.Operands.Count == 0 || instruction.Operands[0] is not Immediate target)
            return false;

        return _method != null && !_method.AppContext.MethodsByAddress.ContainsKey(target.UnsignedValue);
    }

    private static string BuildTrace(ISILControlFlowGraph graph, StackAnalyzer analyzer)
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("stack trace (in/out frame size per block):");

        foreach (var block in graph.Blocks)
        {
            var ins = block.Instructions;
            if (ins.Count == 0)
                continue;

            var first = ins[0];
            var last = ins[^1];
            var incoming = analyzer._inComingState.TryGetValue(block, out var i) ? i.Size : int.MinValue;
            var outgoing = analyzer._outGoingState.TryGetValue(block, out var o) ? o.Size : int.MinValue;

            sb.AppendLine($"    block #{block.ID} [{first.Index}..{last.Index}] in={incoming:X8} out={outgoing:X8} " +
                          $"type={block.BlockType} succ=[{string.Join(",", block.Successors.Select(s => s.ID))}] " +
                          $"preds=[{string.Join(",", block.Predecessors.Select(s => s.ID))}]");
            foreach (var instruction in ins)
                sb.AppendLine($"        {instruction.Index}: {instruction}");
        }

        return sb.ToString();
    }

    private static void ReplaceStackWithRegisters(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;

        // Replace stack offset operands
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is StackOffset offset)
                    instruction.SetOperand(i, new Register(null, NameForSlot(offset)));

                if (operand is AddressOf { Target: StackOffset addressed })
                    instruction.SetOperand(i, new AddressOf(new Register(null, NameForSlot(addressed))));
            }
        }

        // Replace params
        for (var i = 0; i < method.ParameterOperands.Count; i++)
        {
            var parameter = method.ParameterOperands[i];

            if (parameter is StackOffset offset)
                method.ParameterOperands[i] = new Register(null, NameForSlot(offset));
        }
    }

    private static string NameForSlot(StackOffset offset) => offset.Offset < 0 ? $"stack_-{-offset.Offset:X}" : $"stack_{offset.Offset:X}";
}
