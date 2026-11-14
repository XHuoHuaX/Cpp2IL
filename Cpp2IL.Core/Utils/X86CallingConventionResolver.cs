using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

/// <summary>
/// 32-bit x86 IL2CPP 的调用约定 —— **实测得出，不是照搬文档**（依据见 docs/FINDING-045）。
///
/// 与 x64 的根本差别：**一切都走栈**。x86 上 IL2CPP 生成的是 cdecl 自由函数，
/// `__this` 就是第一个栈参数，而不是藏在 ECX 里。
///
/// 调用点（push 之后、call 之前）的布局：
///   [esp+0]=__this   [esp+4]=arg0   [esp+8]=arg1 ...
/// 被调方 push ebp 之后读 `[ebp+8]`=__this、`[ebp+0xc]`=arg0 —— 正好错开一个返回地址。
///
/// 结构体按值返回时，隐藏的目标指针**最后压栈**，于是占 `[esp+0]`，`this` 与参数整体后移一格。
/// 这与 x64 MSVC 把指针放进 rcx 是同一套槽序，只是槽的位置从寄存器换成了栈。
/// </summary>
public class X86CallingConventionResolver : BaseCallingConventionResolver
{
    private const int PtrSize = 4;

    // x86 没有 x87/SSE 的返回值建模（全仓无 st0 支持），所以这里如实返回 eax。
    // 浮点返回值走 ST0 这件事**尚未验证、也未被建模** —— 这是已知缺口，不是假设。
    public override Register ReturnRegister(MethodAnalysisContext ctx) => new(null, "eax");

    // 隐藏返回缓冲区在 x86 上是栈槽，不是寄存器。
    public override Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx) => null;

    public override bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx)
    {
        if (ctx.IsVoid)
            return false;

        var returnType = ctx.ReturnType;

        if (!returnType.IsValueType || IsFloatingPoint(returnType))
            return false;

        var size = TypeSizes.UnboxedSize(returnType, PtrSize);

        if (size == 0)
            return false; // 尺寸未知（泛型等）：按寄存器返回处理，不猜内存返回

        // MSVC x86：1/2/4 字节走 eax，8 字节走 edx:eax，其余一律由调用方提供缓冲区。
        return size is not (1 or 2 or 4 or 8);
    }

    // x86 不用寄存器传参 ⇒ 没有任何"原始参数寄存器"需要保护。
    // 空数组让基类的 ResolveForUnmanaged 不追加操作数（参数本来就在内存里），
    // 也让 HasRawArgumentLayout 对带参数的真实调用不成立，从而不会去 remap 寄存器名。
    protected override (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app) => ([], []);

    // 这是 ABI 事实，不是特性开关：x86 的参数一律在栈上。
    public override bool ArgumentsOnStack(ApplicationAnalysisContext app) => true;

    public override IOperand[] ResolveForManaged(MethodAnalysisContext ctx)
    {
        List<IOperand> args = new();
        var slot = 0;

        // 隐藏返回指针占 [esp+0]，但它不是"参数操作数"（下游把它读作 [this?, params..., MethodInfo]），
        // 所以只推进槽位，不产出操作数。
        if (ReturnsViaHiddenBuffer(ctx))
            slot++;

        void AddSlot()
        {
            args.Add(new StackOffset(slot * PtrSize));
            slot++;
        }

        if (!ctx.IsStatic)
            AddSlot(); // __this

        foreach (var _ in ctx.Parameters)
            AddSlot();

        AddSlot(); // MethodInfo 实参

        return args.ToArray();
    }
}
