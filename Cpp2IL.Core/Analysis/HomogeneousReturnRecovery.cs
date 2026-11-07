using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Restores a method that returns a homogeneous float aggregate (`Color`, `Vector3`, ...).
///
/// ARM64 returns such a struct in one vector register per element, so IL2CPP emits it as a run of loads
/// into those registers and a bare `ret` - there is no single register holding the value. The lifter models
/// the loads faithfully (`V0 = [X0+20]`, `V1 = [X0+24]`, ...) but then appends `Return X0`, because a struct
/// is not a floating-point type and the convention names X0 for everything else. X0 still holds the
/// receiver, so the emission becomes `return (Color)this`, and the element loads die as dead code.
///
/// The aggregate those elements were read from is a *field* of the receiver, so the faithful reconstruction
/// is `return this.<field>;`. That is a byte-for-byte identical value, and the field is found by offset, not
/// guessed: only a field whose type is an aggregate of exactly N floats at exactly this offset qualifies, and
/// with no such field the method is left untouched (never a fabricated value).
///
/// Runs after <see cref="LocalVariables.CreateAll"/> - so the receiver is already a local - and before the
/// first dead-code pass, which is what would otherwise delete the element loads.
/// </summary>
public static class HomogeneousReturnRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        if (method.IsVoid || method.ReturnType is not { } returnType || method.ControlFlowGraph is not { } cfg)
            return;

        var elements = HomogeneousFloatAggregate.Count(returnType);

        if (elements == 0)
            return;

        // The receiver register, as the lifter recorded it. A struct return never comes through `this`.
        if (method.IsStatic || method.ParameterOperands.Count == 0 || method.ParameterOperands[0] is not Register thisRegister)
            return;

        var instructions = cfg.Instructions;

        var returnInstruction = instructions.LastOrDefault(i => i.OpCode == OpCode.Return && i.Operands.Count == 1);

        if (returnInstruction is null)
            return;

        var loads = LoadsOf(method, instructions, elements, thisRegister);

        if (loads is not { Count: > 0 })
            return;

        // Every element has to come from the same run of consecutive 4-byte slots, or it is not one aggregate.
        var baseLocal = loads[0].Base;
        var firstOffset = loads.Min(l => l.Offset);

        for (var i = 0; i < elements; i++)
            if (!loads.Any(l => l.Offset == firstOffset + 4 * i))
                return;

        var field = FindAggregateField(method, firstOffset, elements);

        if (field is null)
            return;

        returnInstruction.SetOperands(new FieldReference(field, baseLocal, firstOffset));
    }

    private static List<(LocalVariable Base, int Offset)>? LoadsOf(MethodAnalysisContext method, List<Instruction> instructions,
        int elements, Register thisRegister)
    {
        var found = new List<(LocalVariable, int)>();

        // Walk back from the end: the element loads are the last writes before the return.
        for (var i = instructions.Count - 1; i >= 0 && found.Count < elements; i--)
        {
            if (instructions[i] is not { OpCode: OpCode.Move, Operands.Count: 2 } move)
                continue;

            if (move.Operands[1] is not MemoryOperand { Index: null, Scale: 0, Base: LocalVariable baseLocal } memory)
                continue;

            if (baseLocal.Register.Number != thisRegister.Number)
                return null;

            found.Add((baseLocal, (int)memory.Addend));
        }

        return found.Count == elements ? found : null;
    }

    private static FieldAnalysisContext? FindAggregateField(MethodAnalysisContext method, int offset, int elements)
    {
        if (method.DeclaringType is not { } declaringType)
            return null;

        // Walk the base chain too: the load may read a field the type inherited.
        for (var type = declaringType; type != null; type = type.BaseType)
        {
            var matches = type.Fields
                .Where(f => !f.IsStatic && f.Offset == offset && HomogeneousFloatAggregate.Count(f.FieldType) == elements)
                .ToList();

            if (matches.Count == 1)
                return matches[0];

            if (matches.Count > 1)
                return null; // ambiguous: do not pick
        }

        return null;
    }
}
