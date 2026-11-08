using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset, bool addressOf = false) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;

    /// <summary>
    /// Whether this reference is the field's *address* rather than its value.
    ///
    /// The native code takes the address of a value-type field so it can pass a byref `this` to an
    /// instance method of that value type. Reading the value instead loses the write: a setter would
    /// store into the temporary and the field would never change. Emitting ldflda keeps the reference
    /// pointing at the field, which is also what lets C# drop the cast entirely and write `t.field.x`.
    /// </summary>
    public bool AddressOf = addressOf;

    public override string ToString() => AddressOf
        ? $"&{Local.Name}.{Field.Name} ({Field.FieldType.FullName})"
        : $"{Local.Name}.{Field.Name} ({Field.FieldType.FullName})";
}
