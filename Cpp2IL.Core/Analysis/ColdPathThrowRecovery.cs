using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Turns a "return the exception object" tail back into <c>throw</c>.
///
/// <para><b>What IL2CPP emits.</b> A reference type's null check compiles to a branch and, on the cold
/// path, a call to a noreturn raise helper (<c>il2cpp_codegen_raise_null_reference_exception</c> and
/// friends). Because the helper never returns, IL2CPP puts the following block after the real <c>ret</c>
/// and lets it end the function. At ISIL that cold block looks like an ordinary tail:</para>
/// <code>
///   4: Newobj returnVal (System.NullReferenceException), typeof(System.NullReferenceException)
///   5: Return returnVal (System.NullReferenceException)
/// </code>
/// <para>which the emitter faithfully renders as <c>return (int)ex;</c> - a value that can never exist.</para>
///
/// <para><b>Why throwing is the faithful reconstruction (red line C5).</b> The native path cannot return:
/// it raises. So the only two candidate renderings are "throw" and "return something invented", and the
/// second one is exactly the silent fake value C5 forbids. <c>throw</c> also preserves the observable
/// behaviour: the caller sees the same exception either way. Nothing is guessed - the exception type and
/// instance come from the emitted instructions.</para>
///
/// <para><b>When it does not fire.</b> Only when the returned value's type cannot be assigned to the
/// method's declared return type <em>and</em> derives from <see cref="System.Exception"/>. A method that
/// legitimately returns an exception (return type <c>object</c>, <c>Exception</c>, a common base) is left
/// alone, because for it <c>return ex;</c> is ordinary, compilable C#.</para>
/// </summary>
public static class ColdPathThrowRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg)
            return false;

        // Name the method's declared return type; both operands are needed for the assignability test.
        var returnType = method.ReturnType;

        var changed = false;

        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.OpCode != OpCode.Return ||
                instruction.Operands.Count != 1 ||
                instruction.Operands[0] is not LocalVariable returned ||
                returned.Type is not { } returnedType)
                continue;

            // `return ex;` in a method that declares an exception-compatible return type is real code.
            if (returnedType.IsAssignableTo(returnType))
                continue;

            if (!DerivesFromException(returnedType))
                continue;

            instruction.OpCode = OpCode.Throw;
            changed = true;
        }

        return changed;
    }

    /// <summary>
    /// Walks the base type chain looking for <c>System.Exception</c>. Deep but finite: the depth cap keeps a
    /// malformed or cyclic stub hierarchy from hanging the whole run.
    /// </summary>
    private static bool DerivesFromException(TypeAnalysisContext type)
    {
        var current = type;

        for (var depth = 0; current != null && depth < 32; depth++)
        {
            if (current.Namespace == "System" && current.Name == "Exception")
                return true;

            current = current.BaseType;
        }

        return false;
    }
}