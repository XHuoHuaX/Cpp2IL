using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public abstract class BaseCallingConventionResolver
{
    public static bool IsFloatingPoint(TypeAnalysisContext type)
        => type == type.AppContext.SystemTypes.SystemSingleType || type == type.AppContext.SystemTypes.SystemDoubleType;

    protected static bool IsFloatingPoint(ParameterAnalysisContext par) => IsFloatingPoint(par.ParameterType);

    public abstract Register ReturnRegister(MethodAnalysisContext ctx);

    public abstract bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx);

    public abstract Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx);

    public abstract IOperand[] ResolveForManaged(MethodAnalysisContext ctx);

    protected abstract (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app);

    /// <summary>
    /// 公开转发，供"按位宽分流"的包装 resolver 读取另一个 resolver 的寄存器表。
    /// （protected 成员不能在别的实例上调用，而分流器需要拿 x64 那一份。）
    /// </summary>
    public (string[] Integer, string[] Float) RawRegistersFor(ApplicationAnalysisContext app) => RawRegisters(app);

    /// <summary>
    /// How many argument slots a parameter occupies and which register file each one takes.
    /// One slot per parameter for most ABIs, but a homogeneous float aggregate spans one SIMD
    /// register per element (see <see cref="HomogeneousFloatAggregate"/>). <paramref name="emit"/>
    /// marks the slot that carries the value itself; the extra slots of an aggregate are consumed
    /// without contributing an operand, because a call still has one argument there.
    /// </summary>
    protected virtual void AddParameterSlots(List<(bool IsFloat, bool Emit)> slots, TypeAnalysisContext? type, bool emit)
        => slots.Add((type != null && IsFloatingPoint(type), emit));

    // MSVC style: argument slot n is integer register n or float register n, not both
    protected virtual bool UsesShadowedArgumentSlots(ApplicationAnalysisContext app) => false;

    // false when the return buffer pointer lives outside the argument registers (e.g. arm64 uses x8)
    protected virtual bool HiddenBufferConsumesArgumentSlot => true;

    public IOperand[] ResolveForUnmanaged(ApplicationAnalysisContext app, ulong target)
    {
        // We don't know the callee's signature, so preserve every argument register.

        var (integerRegisters, floatRegisters) = RawRegisters(app);
        return integerRegisters.Concat(floatRegisters).Select(name => (IOperand)new Register(null, name)).ToArray();
    }

    public bool HasRawArgumentLayout(Instruction call, ApplicationAnalysisContext app)
    {
        var (integerRegisters, floatRegisters) = RawRegisters(app);
        var argBase = ArgBase(call);

        if (call.Operands.Count != argBase + integerRegisters.Length + floatRegisters.Length)
            return false;

        for (var i = 0; i < integerRegisters.Length; i++)
            if (RegisterName(call.Operands[argBase + i]) != integerRegisters[i])
                return false;

        for (var i = 0; i < floatRegisters.Length; i++)
            if (RegisterName(call.Operands[argBase + integerRegisters.Length + i]) != floatRegisters[i])
                return false;

        return true;
    }

    // TODO Fix handling of params on the stack here
    public void RemapRawArguments(Instruction call, MethodAnalysisContext resolved)
    {
        var app = resolved.AppContext;

        var (rawInteger, rawFloat) = RawRegisters(app);

        // 纯栈 ABI（x86 cdecl）：调用本身不携带任何参数操作数，参数在压栈时就写进内存了，
        // 所以"按寄存器名重映射"这条路永远走不通 —— HasRawArgumentLayout 会以数量不符为由返回 false，
        // 参数于是从未被附加。这里直接问 resolver 要栈槽操作数并挂上去。
        // 依据见 docs/FINDING-045（x86 实测 ABI）与 FINDING-046（这条链断在哪一环）。
        if (rawInteger.Length == 0 && rawFloat.Length == 0)
        {
            var stackArguments = ResolveForManaged(resolved);
            if (stackArguments.Length > 0)
                call.AddOperands(stackArguments);
            return;
        }

        if (!HasRawArgumentLayout(call, app))
            return;

        var (integerRegisters, floatRegisters) = RawRegisters(app);
        var argBase = ArgBase(call);

        var slots = new List<(bool IsFloat, bool Emit)>();
        if (ReturnsViaHiddenBuffer(resolved) && HiddenBufferConsumesArgumentSlot)
            slots.Add((false, false));
        if (!resolved.IsStatic)
            slots.Add((false, true));
        foreach (var parameter in resolved.Parameters)
            AddParameterSlots(slots, parameter.ParameterType, true);
        slots.Add((false, true)); // the MethodInfo argument

        var operands = new List<IOperand>(argBase + slots.Count);
        for (var i = 0; i < argBase; i++)
            operands.Add(call.Operands[i]);

        if (UsesShadowedArgumentSlots(app))
        {
            for (var slot = 0; slot < slots.Count && slot < integerRegisters.Length; slot++)
                if (slots[slot].Emit)
                    operands.Add(call.Operands[argBase + (slots[slot].IsFloat ? integerRegisters.Length + slot : slot)]);
        }
        else
        {
            // independent integer/float counters
            var (integer, floating) = (0, 0);

            foreach (var (isFloat, emit) in slots)
            {
                if (isFloat ? floating >= floatRegisters.Length : integer >= integerRegisters.Length)
                    break;

                var operand = call.Operands[argBase + (isFloat ? integerRegisters.Length + floating++ : integer++)];
                if (emit)
                    operands.Add(operand);
            }
        }

        call.SetOperands(operands);
    }

    protected static int ArgBase(Instruction call) => call.OpCode is OpCode.CallVoid ? 1 : 2;

    private static string? RegisterName(IOperand operand) => operand switch
    {
        Register register => register.Name,
        LocalVariable { Register.Name: var name } => name,
        _ => null
    };
}
