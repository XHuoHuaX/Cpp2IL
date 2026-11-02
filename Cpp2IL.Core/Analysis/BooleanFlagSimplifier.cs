using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Fixes the compare-a-flag-against-zero pairs the we get for every conditional: <c>bool != 0</c>
/// is the bool itself, and <c>bool == 0</c> is its negation. Also removes the one-bit mask that
/// IL2CPP puts on a boolean to keep it canonical.
/// </summary>
public static class BooleanFlagSimplifier
{
    public static void Run(MethodAnalysisContext method)
    {
        var booleanType = method.AppContext.SystemTypes.SystemBooleanType;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (TryRemoveCanonicalBoolMask(instruction, booleanType))
                continue;

            if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual) || instruction.Operands.Count < 3)
                continue;

            if (!IsZeroConstant(instruction.Operands[2]))
                continue;

            if (instruction.Operands[1] is not LocalVariable { Type: { } type } || type != booleanType)
                continue;

            instruction.OpCode = instruction.OpCode == OpCode.CheckNotEqual ? OpCode.Move : OpCode.Not;
            instruction.SetOperands(instruction.Operands[0], instruction.Operands[1]);
        }
    }

    // A boolean is stored and passed as 0 or 1, so after boolean arithmetic IL2CPP normalises the
    // result with a one-bit mask (`and w0, w0, #1`). On a canonical boolean that mask is the
    // identity: drop it. Left in place it has no C# meaning at all (`bool & int`).
    private static bool TryRemoveCanonicalBoolMask(Instruction instruction, TypeAnalysisContext booleanType)
    {
        if (instruction.OpCode != OpCode.And || instruction.Operands.Count < 3)
            return false;

        if (instruction.Operands[0] is not LocalVariable destination)
            return false;

        for (var masked = 1; masked < instruction.Operands.Count; masked++)
        {
            if (instruction.Operands[masked] is not LocalVariable { Type: { } type } || type != booleanType)
                continue;

            for (var other = 1; other < instruction.Operands.Count; other++)
            {
                if (other == masked || instruction.Operands[other] is not Immediate { Value: 1 })
                    continue;

                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(destination, instruction.Operands[masked]);
                return true;
            }
        }

        return false;
    }

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
}