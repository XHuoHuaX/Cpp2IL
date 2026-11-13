using System;
using System.Collections.Generic;
using System.Globalization;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A frame slot whose address is handed to someone else denotes a <b>memory location</b>, not an SSA value.
/// The callee reads and writes the whole object through that pointer, and no register version can see those
/// writes, so such slots must stay in memory form: not versioned, no phi, and their stores must survive dead
/// code elimination. This is the same boundary LLVM's mem2reg draws at address-taken allocas.
///
/// The mark carries a <b>range</b>, because the callee touches the whole object rather than the single word
/// the address pointed at: an HFA return is stored as four consecutive 4-byte slots and then read field by
/// field through the base address. Marking only the addressed slot leaves the siblings to be versioned and
/// deleted, which is exactly how <c>Book::get_Height</c> ended up returning <c>default(Rect)</c>
/// (see docs/FINDING-039-hfa-return-store-dropped.md).
///
/// Shared by SsaForm, DeadCodeEliminator and Simplifier so all three agree on the same set.
/// Enabled by <c>CPP2IL_ESCAPE_MEMORY=1</c> while it is being measured.
/// </summary>
public static class FrameSlotEscape
{
    /// <summary>
    /// How many bytes an addressed frame object is assumed to occupy. Rect, Vector2/3/4 and Color - the
    /// common Unity value types - are 16 bytes, and reading a smaller window would leave siblings unmarked.
    /// A conservative over-estimate only costs SSA promotion on neighbouring slots; an under-estimate loses
    /// stores, so rounding up is the safe direction.
    /// </summary>
    public const int DefaultObjectSize = 16;

    public static bool Enabled =>
        Environment.GetEnvironmentVariable("CPP2IL_ESCAPE_MEMORY") == "1";

    /// <summary>Frame slot names whose storage is reachable through a pointer taken anywhere in the method.</summary>
    public static HashSet<string> Collect(ISILControlFlowGraph cfg)
    {
        var resident = new HashSet<string>(StringComparer.Ordinal);
        if (!Enabled || cfg is null)
            return resident;

        var windows = new List<(int Start, int End)>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                foreach (var operand in instruction.Operands)
                {
                    var name = TargetName(operand);
                    if (name is not null && TryParseFrameOffset(name, out var offset))
                        windows.Add((offset, offset + DefaultObjectSize));
                }

        if (windows.Count == 0)
            return resident;

        // Second pass: every frame slot inside an addressed window belongs to the same object.
        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                foreach (var operand in instruction.Operands)
                {
                    var name = RegisterName(operand);
                    if (name is null || !TryParseFrameOffset(name, out var offset))
                        continue;

                    foreach (var (start, end) in windows)
                        if (offset >= start && offset < end)
                        {
                            resident.Add(name);
                            break;
                        }
                }

        return resident;
    }

    public static bool IsResident(HashSet<string> resident, LocalVariable local) =>
        resident.Count > 0 && local.Register is { Name: { } name } && resident.Contains(name);

    public static bool IsResident(HashSet<string> resident, Register register) =>
        resident.Count > 0 && register.Name is { } name && resident.Contains(name);

    private static string? TargetName(IOperand operand) => operand switch
    {
        AddressOf { Target: Register { Name: { } fromRegister } } => fromRegister,
        AddressOf { Target: LocalVariable { Register: { Name: { } fromLocal } } } => fromLocal,
        _ => null
    };

    private static string? RegisterName(IOperand operand) => operand switch
    {
        Register { Name: { } direct } => direct,
        LocalVariable { Register: { Name: { } viaLocal } } => viaLocal,
        _ => null
    };

    /// <summary>
    /// Parses the offset out of a frame slot name such as <c>stack_-20</c>.
    /// <para>
    /// Note the sign: <see cref="NumberStyles.HexNumber"/> does <b>not</b> accept a leading minus, so
    /// <c>int.TryParse("-20", NumberStyles.HexNumber, ...)</c> returns false. The first version of this
    /// analysis used exactly that call on the elimination side and therefore produced an empty set, which
    /// made every guard that consumed it a no-op - the stores kept being deleted and it looked as if the
    /// rule itself did not work.
    /// </para>
    /// </summary>
    public static bool TryParseFrameOffset(string name, out int offset)
    {
        offset = 0;
        if (name is null || !name.StartsWith("stack_", StringComparison.Ordinal))
            return false;

        var text = name.Substring("stack_".Length);
        var negative = text.StartsWith("-", StringComparison.Ordinal);
        if (negative)
            text = text.Substring(1);

        if (!int.TryParse(text, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out var magnitude))
            return false;

        offset = negative ? -magnitude : magnitude;
        return true;
    }
}