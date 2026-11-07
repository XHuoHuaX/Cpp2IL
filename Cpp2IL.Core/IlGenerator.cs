using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core;

public static class IlGenerator
{
    private const string HelpersNamespace = "Cpp2ILInjected";
    private const string HelpersTypeName = "Cpp2ILHelpers";
    private const string NoteIssueMethodName = "NoteDecompilerIssue";

    /// <summary>
    /// False when <paramref name="type"/> is a generic parameter that the emitting method cannot name:
    /// IL2CPP shares generic method bodies, so a body recovered for a concrete method can still be
    /// written in terms of the shared definition's type or method parameters. Emitting those produces
    /// identifiers that do not resolve (CS0246 / CS7003), so callers substitute <c>object</c> instead.
    /// Ownership is compared by identity on purpose: matching on the index alone would silently bind the
    /// parameter to a different owner's parameter, which is a wrong value rather than a degrade.
    /// </summary>
    private static bool IsInScopeGenericParameter(MethodAnalysisContext context, TypeAnalysisContext type)
    {
        if (type is not GenericParameterTypeAnalysisContext parameter)
            return true;

        if (parameter.Type == LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR)
            return ReferenceEquals(parameter.Owner, context);

        for (var declaring = context.DeclaringType; declaring != null; declaring = declaring.DeclaringType)
            if (ReferenceEquals(parameter.Owner, declaring))
                return true;

        return false;
    }

    /// <summary>
    /// Replace a type that cannot be named at this site with <c>object</c>. Two cases: a generic
    /// parameter the method does not declare, and a generic instantiation that mentions one (a
    /// <c>List&lt;T&gt;</c> is just as unspeakable as a bare <c>T</c>). Used wherever a type signature
    /// reaches the output, not only local declarations - instruction operands carry types too.
    /// </summary>
    private static TypeAnalysisContext SanitizeType(MethodAnalysisContext context, TypeAnalysisContext type)
    {
        if (type is GenericParameterTypeAnalysisContext)
            return IsInScopeGenericParameter(context, type) ? type : context.AppContext.SystemTypes.SystemObjectType;

        if (type is GenericInstanceTypeAnalysisContext genericInstance)
            foreach (var argument in genericInstance.GenericArguments)
                if (!IsInScopeGenericParameter(context, argument))
                    return context.AppContext.SystemTypes.SystemObjectType;

        return type;
    }

    public static void InjectHelpersType(ApplicationAnalysisContext appContext)
    {
        var helpersType = appContext.InjectTypeIntoAllAssemblies(
            HelpersNamespace,
            HelpersTypeName,
            null,
            TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract | TypeAttributes.Sealed);

        helpersType.InjectMethodToAllAssemblies(
            NoteIssueMethodName,
            appContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static,
            [appContext.SystemTypes.SystemStringType]);
    }

    public static void GenerateIl(MethodAnalysisContext context, MethodDefinition definition)
    {
        var assembly = context.DeclaringType!.DeclaringAssembly;
        var module = definition.DeclaringModule!;
        var factory = module.CorLibTypeFactory;

        var noteIssueContext = assembly
            .GetTypeByFullName($"{HelpersNamespace}.{HelpersTypeName}")?.Methods.FirstOrDefault(m => m.Name == NoteIssueMethodName);

        var writeLine = noteIssueContext != null
            ? noteIssueContext.ToMethodDescriptor()
            : factory.CorLibScope
                .CreateTypeReference("System", "Console")
                .CreateMemberReference("WriteLine", MethodSignature.CreateStatic(factory.Void, [factory.String]));

        // Change branch targets to instructions
        foreach (var instruction in context.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.Operands.Count > 0 && instruction.Operands[0] is Block target)
            {
                if (target.Instructions.Count > 0)
                    instruction.SetOperand(0, target.Instructions[0]);
            }
        }

        var body = new CilMethodBody()
        {
            InitializeLocals = true, // Without this ILSpy does: CompilerServices.Unsafe.SkipInit(out object obj);
            ComputeMaxStackOnBuild = false // There's stack imbalance somewhere, but this works for now
        };

        definition.CilMethodBody = body;

        // Make sure context.Locals actually has all locals (idk why it doesn't sometimes)
        foreach (var operand in context.ControlFlowGraph.Instructions.SelectMany(i => i.Operands))
        {
            LocalVariable? local = null;

            if (operand is FieldReference field)
                local = field.Local;

            if (operand is LocalVariable local2)
                local = local2;

            if (operand is MemoryOperand memory && memory.Base is LocalVariable local3)
                local = local3;

            var elementOperand = operand is AddressOf { Target: ArrayAccess elementAddress } ? elementAddress : operand;

            if (elementOperand is ArrayAccess arrayAccess)
            {
                local = arrayAccess.Array;

                if (arrayAccess.Index is LocalVariable index && !context.Locals.Contains(index))
                    context.Locals.Add(index);
            }

            if (operand is ArrayLength arrayLength)
                local = arrayLength.Array;

            if (operand is AddressOf { Target: LocalVariable addressed })
                local = addressed;

            if (local != null && !context.Locals.Contains(local))
                context.Locals.Add(local);
        }

        // Map ISIL locals to IL
        Dictionary<LocalVariable, CilLocalVariable> locals = [];
        foreach (var local in context.Locals)
        {
            TypeSignature ilType;

            // Use object if type couldn't be determined, or if it's void, which no locals sig can hold
            // A local may also be typed by a generic parameter the emitting method does not declare:
            // IL2CPP shares generic bodies, so those leak into concrete methods and would emit an
            // identifier that does not resolve (CS0246). Degrade to object, which compiles and leaves
            // the control flow intact.
            if (local.Type != null && local.Type != context.AppContext.SystemTypes.SystemVoidType
                                    && IsInScopeGenericParameter(context, local.Type))
                ilType = SanitizeType(context, local.Type).ToTypeSignature();
            else
                ilType = module.CorLibTypeFactory.Object;

            var ilLocal = new CilLocalVariable(ilType);
            body.LocalVariables.Add(ilLocal);
            locals.Add(local, ilLocal);
        }

        /* foreach (var instruction in context.ControlFlowGraph!.Instructions)
        {
            body.Instructions.Add(CilOpCodes.Ldstr, instruction.ToString());
            body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!));
        }
        body.Instructions.Add(CilOpCodes.Ldstr, "-------------------------------------------------------------------------");
        body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!)); */

        // Generate IL
        Dictionary<Instruction, List<CilInstruction>> instructionMap = [];
        Dictionary<Block, CilInstruction> blockEntryMap = [];
        List<(CilInstruction BranchInstruction, Block TargetBlock)> pendingBlockBranchFixups = [];

        // Every allocation/constructor pairing is decided up front, and the constructor call is turned
        // into a Nop here rather than when the allocation is emitted. IL2CPP puts the allocation and the
        // call in different blocks, and the blocks are emitted in CFG order - so if the call's block
        // comes first, a lazy match would emit the constructor as an instance call (`x._002Ector(...)`,
        // which is not valid C#) and then the allocation's own `newobj`, constructing the object twice.
        var fusedConstructors = new Dictionary<Instruction, FusedConstructor>();
        foreach (var candidate in context.ControlFlowGraph!.Instructions)
        {
            if (candidate.OpCode != OpCode.Newobj)
                continue;

            if (FindConstructorCall(context, candidate) is not { Operands: [MethodAnalysisContext constructor, ..] } call)
                continue;

            var receiverIndex = ConstructorReceiverIndex(call);
            var arguments = call.Operands.Skip(receiverIndex + 1).ToArray();
            fusedConstructors[candidate] = new FusedConstructor(constructor, arguments);

            call.OpCode = OpCode.Nop;
            call.SetOperands();
        }

        foreach (var block in context.ControlFlowGraph!.Blocks)
        {
            if (block == context.ControlFlowGraph.EntryBlock || block == context.ControlFlowGraph.ExitBlock)
                continue;

            if (block.Instructions.Count == 0)
                continue;

            foreach (var instruction in block.Instructions)
            {
                var generated = GenerateInstructions(instruction, context, definition, locals, writeLine, fusedConstructors);
                instructionMap.Add(instruction, generated);

                if (!blockEntryMap.ContainsKey(block) && generated.Count > 0)
                    blockEntryMap[block] = generated[0];
            }

            var lastInstruction = block.Instructions.Last();
            
            if (lastInstruction.OpCode == OpCode.ConditionalJump)
            {
                var trueTarget = TryResolveJumpTargetBlock(lastInstruction, context.ControlFlowGraph);
                var falseSuccessor = block.Successors.FirstOrDefault(s => s != trueTarget && s != context.ControlFlowGraph.ExitBlock);
                if (falseSuccessor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, falseSuccessor));
            }

            else if (lastInstruction.OpCode != OpCode.Jump && lastInstruction.OpCode != OpCode.Return && lastInstruction.OpCode != OpCode.IndirectJump)
            {
                var successor = block.Successors.FirstOrDefault(s => s != context.ControlFlowGraph.ExitBlock);
                if (successor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, successor));
            }
        }
        // Set IL branch targets
        foreach (var kvp in instructionMap)
        {
            var instruction = kvp.Key;
            var il = kvp.Value;

            if (instruction.OpCode == OpCode.Jump || instruction.OpCode == OpCode.ConditionalJump)
            {
                var ilBranch = il.First(i => i.OpCode == CilOpCodes.Br || i.OpCode == CilOpCodes.Brtrue);

                if (instruction.Operands[0] is Block targetBlock)
                {
                    context.AddWarning($"Branch target block not in cfg: {instruction} ({targetBlock})");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                var target = (Instruction)instruction.Operands[0];

                // An ISIL instruction can legitimately expand to no CIL at all, in which case it has no
                // instruction to point a label at. Treat it exactly like a target that is missing from
                // the map instead of indexing into an empty list.
                if (!instructionMap.TryGetValue(target, out var targetIl) || targetIl.Count == 0)
                {
                    context.AddWarning($"Branch target has no emitted IL: {instruction} --- {target} ({target.OpCode})");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                ilBranch.Operand = new CilInstructionLabel(targetIl[0]);
            }
        }
        
        foreach (var (branchInstruction, targetBlock) in pendingBlockBranchFixups)
        {
            var target = ResolveBlockEntryInstruction(targetBlock, blockEntryMap);
            if (target == null)
            {
                context.AddWarning($"Unable to resolve branch target block: {targetBlock}");
                branchInstruction.OpCode = CilOpCodes.Nop;
                branchInstruction.Operand = null;
                continue;
            }

            branchInstruction.Operand = new CilInstructionLabel(target);
        }

        // Add analysis warnings
        var instructions = body.Instructions;
        foreach (var warning in context.AnalysisWarnings)
        {
            instructions.Add(CilOpCodes.Ldstr, Diagnostic("Warning: " + warning));
            instructions.Add(CilOpCodes.Call, writeLine);
        }
    }

    // Limit so we don't run into the 16mb limit (see AsmResolver issue #775)
    private static string Diagnostic(string message) 
        => message.Length <= 250 ? message : message[..250] + "…";
    
    private static Block? TryResolveJumpTargetBlock(Instruction jumpInstruction, ISILControlFlowGraph cfg)
    {
        if (jumpInstruction.Operands.Count == 0)
            return null;

        if (jumpInstruction.Operands[0] is Block targetBlock)
            return targetBlock;

        if (jumpInstruction.Operands[0] is Instruction targetInstruction)
            return cfg.FindBlockByInstruction(targetInstruction);

        return null;
    }

    private static CilInstruction? ResolveBlockEntryInstruction(Block block,
        Dictionary<Block, CilInstruction> blockEntryMap, HashSet<Block>? visited = null)
    {
        if (blockEntryMap.TryGetValue(block, out var target))
            return target;

        visited ??= [];
        if (!visited.Add(block))
            return null;

        foreach (var successor in block.Successors)
        {
            var resolved = ResolveBlockEntryInstruction(successor, blockEntryMap, visited);
            if (resolved != null)
                return resolved;
        }
        return null;
    }

    private static List<CilInstruction> GenerateInstructions(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        IReadOnlyDictionary<Instruction, FusedConstructor> fusedConstructors)
    {
        var body = method.CilMethodBody!;
        var instructions = body.Instructions;
        var currentCount = instructions.Count;
        var startIndex = instructions.Count;

        var module = method.DeclaringModule!;

        switch (instruction.OpCode)
        {
            case OpCode.Invalid:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Invalid instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.NotImplemented:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Not implemented instruction: {instruction.Operands[0]}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Interrupt:
            case OpCode.Nop:
                instructions.Add(CilOpCodes.Nop);
                break;

            case OpCode.Move:
                if (instruction.Operands[0] is FieldReference field) // stfld takes instance before value so LoadOperand StoreToOperand doesn't work
                {
                    if (!field.Field.IsStatic)
                        LoadLocal(field.Local, method, locals);

                    LoadOperand(instruction.Operands[1], method, locals, writeLine, field.Field.FieldType);
                    instructions.Add(field.Field.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld, field.Field.ToFieldDescriptor());
                    break;
                }

                // stelem needs array and index before the value, so like stfld it can't go through LoadOperand/StoreToOperand.
                // This also lets ILSpy handle it as a proper array initializer
                if (instruction.Operands[0] is ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } stored } } target)
                {
                    LoadLocal(target.Array, method, locals);
                    LoadOperand(target.Index, method, locals, writeLine);
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, stored);
                    instructions.Add(CilOpCodes.Stelem, SanitizeType(context, stored).ToTypeSignature().ToTypeDefOrRef());
                    break;
                }

                LoadOperand(instruction.Operands[1], method, locals, writeLine, DestinationType(instruction.Operands[0]));
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.NewArr:
                if (instruction.Operands is [_, SzArrayTypeAnalysisContext { ElementType: { } newArrayElement }, { } length])
                {
                    LoadOperand(length, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Newarr, SanitizeType(context, newArrayElement).ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Newobj:
                // Try and fuse our Newobj + the follow up constructor CallVoid into one IL newobj.
                // If we can't, just fall back to an Ldnull.
                //
                // A delegate is the other shape, and it needs different handling: IL2CPP allocates the
                // delegate type and carries the target method in a neighbouring `Move methodof(M)`. Both
                // halves are present, so the target is known - dropping it leaves `new D(this, (IntPtr)0)`,
                // a delegate that points nowhere (a fake value, red line C5) and not valid C# either
                // (CS0149). The structural signal is used rather than the delegate type's base chain,
                // because allocations routinely name the generic *definition* whose base is unresolved.
                if (instruction.Operands is [_, TypeAnalysisContext { } delegateType, ..]
                    && FindDelegateTarget(context, instruction) is { } delegateTargetMove
                    && delegateTargetMove.Operands[1] is RuntimeMethodInfoAnalysisContext delegateTarget
                    && FindDelegateCtor(delegateType) is { } delegateCtor
                    && IsEmittableDelegateTarget(context, delegateTarget.RepresentedMethod))
                {
                    // IL2CPP creates a delegate as "allocate the delegate type" plus a separate
                    // `Move <local>, methodof(M)` carrying the MethodInfo. Both halves are present, so the
                    // target method is known - dropping it would leave `new D(this, (IntPtr)0)`, a delegate
                    // that points nowhere (a fake value, red line C5) and not valid C# either (CS0149).
                    // Emit the real thing: ldarg.0/ldnull, ldftn M, newobj D::.ctor(object, native int).
                    var delegateTargetMethod = delegateTarget.RepresentedMethod;

                    // The MethodInfo load has been folded into the ldftn below; leaving it would emit a
                    // method-pointer local that can only be rendered as a fake `(IntPtr)0`.
                    delegateTargetMove.OpCode = OpCode.Nop;
                    delegateTargetMove.SetOperands();

                    if (delegateTargetMethod.IsStatic)
                        instructions.Add(CilOpCodes.Ldnull);
                    else
                        LoadOperand(context.Locals.First(l => l.IsThis), method, locals, writeLine);

                    instructions.Add(CilOpCodes.Ldftn, delegateTargetMethod.ToMethodDescriptor());
                    instructions.Add(CilOpCodes.Newobj, delegateCtor);

                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);

                    // The ctor call that IL2CPP emitted alongside the allocation is already a Nop: the
                    // pairing was resolved in the pre-pass, along with every other allocation. If the
                    // pre-pass found no pairing (the call may name the finished delegate rather than the
                    // allocated local), consume it here so it is not emitted as a second construction.
                    if (!fusedConstructors.ContainsKey(instruction) && FindConstructorCall(context, instruction) is { } consumedCtor)
                    {
                        consumedCtor.OpCode = OpCode.Nop;
                        consumedCtor.SetOperands();
                    }
                }
                else if (fusedConstructors.TryGetValue(instruction, out var fused))
                {
                    var constructor = fused.Constructor;
                    var constructorArgs = fused.Arguments.Take(constructor.Parameters.Count).ToList();
                    for (var i = 0; i < constructorArgs.Count; i++)
                        LoadOperand(constructorArgs[i], method, locals, writeLine, constructor.Parameters[i].ParameterType);

                    instructions.Add(CilOpCodes.Newobj, CtorDescriptor(constructor, AllocatedType(instruction)));
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                else if (instruction.Operands is [_, TypeAnalysisContext allocatedType] && allocatedType.Methods.FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 0 }) is { } parameterlessCtor)
                {
                    // Nothing to fuse with, so the allocation was self-contained. The type is still right, so construct it bare.
                    instructions.Add(CilOpCodes.Newobj, CtorDescriptor(parameterlessCtor, allocatedType));
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                else
                {
                    instructions.Add(CilOpCodes.Ldnull);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                break;

            case OpCode.Box:
                if (instruction.Operands is [_, TypeAnalysisContext boxedType, var boxedValue])
                {
                    // il2cpp_value_box takes the value by address, but IL boxes it by value
                    LoadOperand(boxedValue is AddressOf { Target: LocalVariable byRef } ? byRef : boxedValue, method, locals, writeLine, boxedType);
                    instructions.Add(CilOpCodes.Box, SanitizeType(context, boxedType).ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Throw:
                if (instruction.Operands is [TypeAnalysisContext exceptionType]
                    && exceptionType.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Count == 0) is { } exceptionCtor)
                    instructions.Add(CilOpCodes.Newobj, exceptionCtor.ToMethodDescriptor());
                else if (instruction.Operands is [LocalVariable or FieldReference])
                    LoadOperand(instruction.Operands[0], method, locals, writeLine); // an already-constructed exception
                else
                    instructions.Add(CilOpCodes.Ldnull);

                instructions.Add(CilOpCodes.Throw);
                break;

            case OpCode.Phi:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Phi opcodes should not exist at this point in decompilation ({instruction})"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Call:
            case OpCode.CallVoid:
                if (instruction.Operands[0] is not MethodAnalysisContext targetMethod)
                {
                    if (instruction.Operands[0] is Immediate targetAddress)
                        instructions.Add(CilOpCodes.Ldstr, $"Method not found @{targetAddress.UnsignedValue:X}");
                    else // Probably key function. Just the target, the full operand dump is huge and blows the 16MB #US heap limit
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown call target operand: {instruction.Operands[0]}"));

                    instructions.Add(CilOpCodes.Call, writeLine);
                    break;
                }

                var thisParamIndex = instruction.OpCode == OpCode.Call ? 2 : 1;

                // A parameterless constructor call on this very object, from inside its own constructor, is
                // the base/self initialiser. C# expresses that in the constructor initialiser (`: base()`)
                // and the compiler emits it implicitly when absent, so the *statement* form
                // `base._002Ector()` is not valid C# at all (CS1061) and must not be emitted.
                // Nothing is lost by leaving it out: the same call still happens implicitly, and the guard
                // (zero parameters, own `this`, enclosing method is a constructor) is what makes that exact.
                if (targetMethod is { Name: ".ctor", Parameters.Count: 0 }
                    && context.Name == ".ctor"
                    && instruction.Operands.Count > thisParamIndex
                    && instruction.Operands[thisParamIndex] is LocalVariable { IsThis: true })
                {
                    // Nothing is emitted for this instruction, but it still needs an anchor: any branch
                    // that targets it has to resolve to a real CIL instruction, and a block that starts
                    // here needs an entry point. A Nop costs nothing at runtime and is dropped later.
                    instructions.Add(CilOpCodes.Nop);
                    break;
                }

                var importedMethod = targetMethod.ToMethodDescriptor();

                // A call on a generic type instance has to reference that instance - see FINDING-010.
                // Emitting the definition yields `call List`1::Add(!0)`, which no C# compiler can express.
                if (!targetMethod.IsStatic
                    && instruction.Operands.Count > thisParamIndex
                    && DestinationType(instruction.Operands[thisParamIndex]) is GenericInstanceTypeAnalysisContext receiverInstance
                    && targetMethod.DeclaringType is { } callDeclaringType
                    && callDeclaringType.GenericParameters.Count > 0
                    && receiverInstance.GenericArguments.Count == callDeclaringType.GenericParameters.Count)
                    importedMethod = targetMethod.ToMethodDescriptorOnInstance(receiverInstance);

                if (!targetMethod.IsStatic) // Load 'this' param
                {
                    // IL2CPP compiles the whole program, so a method that never looks at its receiver is also
                    // called without one: the loading instruction is dropped and X0 still holds whatever the
                    // previous call returned. Taking that as the receiver yields a call on a value of the
                    // wrong type (CS0030) with a receiver the source never wrote. When the callee provably
                    // ignores `this` the choice is free, so emit the enclosing `this` - what the source said.
                    // See docs/FINDING-028.
                    if ((instruction.Operands.Count - 1) >= thisParamIndex
                        && EnclosingThis(context, targetMethod, instruction.Operands[thisParamIndex]) is { } enclosingThis)
                        LoadOperand(enclosingThis, method, locals, writeLine, targetMethod.DeclaringType);
                    else if ((instruction.Operands.Count - 1) >= thisParamIndex)
                        LoadOperand(instruction.Operands[thisParamIndex], method, locals, writeLine, targetMethod.DeclaringType);
                    else
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Non static method called without 'this' param ({instruction})"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        instructions.Add(CilOpCodes.Ldnull);
                    }
                }

                // Load normal params
                var callParamIndex = instruction.OpCode == OpCode.Call ? (targetMethod.IsStatic ? 2 : 3) : (targetMethod.IsStatic ? 1 : 2);
                // A call whose target was only identified after lifting still carries the operands the
                // unknown-callee convention gave it, which may be fewer than the method actually takes.
                // The stack still has to match the signature, so anything missing gets a placeholder.
                var availableArgs = instruction.Operands.Count - callParamIndex;
                for (var i = 0; i < targetMethod.Parameters.Count; i++)
                {
                    var parameterType = targetMethod.Parameters[i].ParameterType;

                    if (i < availableArgs)
                        LoadOperand(instruction.Operands[callParamIndex + i], method, locals, writeLine, parameterType);
                    else
                        PushDefaultOf(parameterType, instructions);
                }

                instructions.Add(CilOpCodes.Call, importedMethod);

                // the lifter's guess at whether the callee returns anything can disagree with the
                // signature we later resolved, so go by the signature and balance the stack
                if (!targetMethod.IsVoid)
                {
                    if (instruction.OpCode == OpCode.Call)
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine);
                    else
                        instructions.Add(CilOpCodes.Pop);
                }

                break;

            case OpCode.IndirectCall:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect call: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Return:
                if (!context.IsVoid)
                {
                    if (instruction.Operands.Count == 1)
                        LoadOperand(instruction.Operands[0], method, locals, writeLine, context.ReturnType);
                    else
                        instructions.Add(CilOpCodes.Ldnull); // ret still pops a value even if we lost track of it
                }
                instructions.Add(CilOpCodes.Ret);
                break;

            case OpCode.Jump:
                instructions.Add(CilOpCodes.Br, new CilInstructionLabel());
                break;

            case OpCode.ConditionalJump:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                instructions.Add(CilOpCodes.Brtrue, new CilInstructionLabel());
                break;

            case OpCode.IndirectJump:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect jump: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.ShiftStack:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Stack shift: {instruction} (stack analysis should have removed these)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.CheckEqual:
            case OpCode.CheckGreater:
            case OpCode.CheckLess:
            case OpCode.CheckNotEqual:
            case OpCode.CheckGreaterOrEqual:
            case OpCode.CheckLessOrEqual:

            case OpCode.Add:
            case OpCode.Subtract:
            case OpCode.Multiply:
            case OpCode.Divide:
            case OpCode.Modulo:

            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:

            case OpCode.And:
            case OpCode.Or:
            case OpCode.Xor:
                // klass pointer read => GetType
                if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    && TryEmitExactTypeComparison(context, instruction, method, locals, writeLine))
                    break;

                // Float arithmetic on a promoted integer operand needs an explicit conversion, so both
                // operands are coerced to the (float) result type. A no-op when they already match.
                var floatConversion = FloatArithmeticConversion(instruction);

                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                if (floatConversion is { } conv1)
                    instructions.Add(conv1);
                LoadOperand(instruction.Operands[2], method, locals, writeLine);
                if (floatConversion is { } conv2)
                    instructions.Add(conv2);

                switch (instruction.OpCode)
                {
                    case OpCode.CheckEqual: instructions.Add(CilOpCodes.Ceq); break;
                    case OpCode.CheckGreater: instructions.Add(CilOpCodes.Cgt); break;
                    case OpCode.CheckLess: instructions.Add(CilOpCodes.Clt); break;

                    // a != b  ==  (a == b) == 0
                    case OpCode.CheckNotEqual:
                        instructions.Add(CilOpCodes.Ceq);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a >= b  ==  !(a < b)
                    case OpCode.CheckGreaterOrEqual:
                        instructions.Add(CilOpCodes.Clt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a <= b  ==  !(a > b)
                    case OpCode.CheckLessOrEqual:
                        instructions.Add(CilOpCodes.Cgt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;

                    case OpCode.Add: instructions.Add(CilOpCodes.Add); break;
                    case OpCode.Subtract: instructions.Add(CilOpCodes.Sub); break;
                    case OpCode.Multiply: instructions.Add(CilOpCodes.Mul); break;
                    case OpCode.Divide: instructions.Add(CilOpCodes.Div); break;
                    case OpCode.Modulo: instructions.Add(CilOpCodes.Rem); break;

                    case OpCode.ShiftLeft: instructions.Add(CilOpCodes.Shl); break;
                    case OpCode.ShiftRight: instructions.Add(CilOpCodes.Shr); break;

                    case OpCode.And: instructions.Add(CilOpCodes.And); break;
                    case OpCode.Or: instructions.Add(CilOpCodes.Or); break;
                    case OpCode.Xor: instructions.Add(CilOpCodes.Xor); break;
                }

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Not:
            case OpCode.Negate:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);

                if (instruction.OpCode == OpCode.Negate)
                    instructions.Add(CilOpCodes.Neg);
                else if (IsBoolean(instruction.Operands[1], context))
                {
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Ceq);
                }
                else
                    instructions.Add(CilOpCodes.Not);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;
        }

        return instructions.ToList().GetRange(startIndex, instructions.Count - startIndex); // Return added IL
    }
    
    private static int ConstructorReceiverIndex(Instruction constructorCall) => constructorCall.OpCode == OpCode.CallVoid ? 1 : 2;

    /// <summary>
    /// Maps a BCL internal field that IL2CPP left behind (because the callee was inlined into its
    /// caller) onto the public property it backs, and emits the property read instead of the field read.
    ///
    /// Only fields that denote *exactly* the public value are listed, because a wrong value here would
    /// be silent - the red line this project does not cross. Deliberately absent:
    /// <c>Dictionary&lt;K,V&gt;._count</c> (Count is <c>_count - _freeCount</c>, not <c>_count</c>),
    /// <c>_items</c>/<c>_buckets</c> (no public equivalent), and the delegate internals
    /// <c>m_target</c>/<c>method_ptr</c> (they are written here, not read).
    /// </summary>
    private static bool TryEmitEquivalentProperty(FieldReference field, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, CilInstructionCollection instructions)
    {
        var declaring = field.Field.DeclaringType;
        var definition = (declaring as GenericInstanceTypeAnalysisContext)?.GenericType ?? declaring;

        var isIndexedContainer = definition.Namespace == "System.Collections.Generic"
            && definition.Name is "List`1" or "Queue`1" or "Stack`1";
        var isString = definition.Namespace == "System" && definition.Name == "String";

        string? propertyName = null;
        if (field.Field.Name == "_size" && isIndexedContainer)
            propertyName = "Count";
        else if (field.Field.Name is "m_stringLength" or "_stringLength" && isString)
            propertyName = "Length";

        if (propertyName == null)
            return false;

        // The getter is taken from the definition (an instance type exposes no property list of its
        // own) and re-parented onto the instance below, so the reference is a closed generic.
        var getter = definition.Properties.FirstOrDefault(p => p.Name == propertyName)?.Getter;
        if (getter == null)
            return false;

        var parent = declaring.ToTypeSignature().ToTypeDefOrRef();
        var member = parent.CreateMemberReference(getter.Name, getter.ToMethodDescriptor().Signature);

        LoadLocal(field.Local, method, locals);
        instructions.Add(CilOpCodes.Callvirt, member);
        return true;
    }

    /// <summary>
    /// One allocation's constructor call, resolved before any IL was emitted. <see cref="Arguments"/>
    /// is captured because the call itself becomes a Nop (and loses its operands) as soon as it is
    /// paired, while the allocation still needs those arguments to emit a real <c>newobj</c>.
    /// </summary>
    private sealed record FusedConstructor(MethodAnalysisContext Constructor, IOperand[] Arguments);

    /// <summary>
    /// Whether the delegate's target method can be named in emitted IL at all. Two shapes cannot, and
    /// fabricating something for them is worse than leaving the site degraded (red line C5):
    /// <list type="bullet">
    /// <item>a method declared on a <em>generic instance</em> - <c>ToMethodDescriptor</c> yields an
    /// unresolvable reference, which ILSpy renders as the pseudo-call <c>__ldftn(...)</c>;</item>
    /// <item>an <em>instance</em> method while the enclosing method has no <c>this</c> (a lambda lifted into
    /// a static context) - the receiver would have to be invented, and a null receiver produces code that
    /// does not compile (<c>CS0120</c>).</item>
    /// </list>
    /// </summary>
    private static bool IsEmittableDelegateTarget(MethodAnalysisContext context, MethodAnalysisContext target)
    {
        if (target.DeclaringType is GenericInstanceTypeAnalysisContext)
            return false;

        // A compiler-generated method (`<Method>b__0`, `<>9__32_0`) is the lambda body the C# compiler
        // synthesised for a source-level lambda. Naming it with ldftn makes ILSpy inline it as a lambda,
        // and it then emits that method's own attributes inside the expression, which does not parse and
        // takes the whole file's method bodies with it. Leaving the site degraded is strictly better.
        if (target.Name.Contains('<') || target.Name.Contains('>'))
            return false;

        if (target.IsStatic)
            return true;

        // An instance target must actually be reachable from this method's receiver; a lambda lifted into a
        // display class cannot call an instance method of the enclosing type.
        return context.Locals.FirstOrDefault(l => l.IsThis)?.Type is { } thisType
               && target.DeclaringType is { } declaringType
               && thisType.IsAssignableTo(declaringType);
    }

    /// <summary>The type a <c>Newobj</c> allocates, when the operand names one.</summary>
    private static TypeAnalysisContext? AllocatedType(Instruction newobj) =>
        newobj.Operands.Count > 1 ? newobj.Operands[1] as TypeAnalysisContext : null;

    /// <summary>
    /// The descriptor a constructor call must use for the given allocation. An instantiated generic type
    /// carries its constructors only on the definition, so the definition's constructor is projected onto
    /// the instance - the same machinery generic calls use (FINDING-010). Emitting the definition's own
    /// constructor renders as <c>new List&lt;T&gt;()</c> with an unbound <c>T</c>, which does not compile.
    /// </summary>
    private static IMethodDescriptor CtorDescriptor(MethodAnalysisContext constructor, TypeAnalysisContext? allocated) =>
        allocated is GenericInstanceTypeAnalysisContext instance
            ? constructor.ToMethodDescriptorOnInstance(instance)
            : constructor.ToMethodDescriptor();

    /// <summary>
    /// The enclosing method's own `this` when it is a valid receiver for <paramref name="callee"/>, i.e. only
    /// when the callee never reads the receiver it is given. Returns null otherwise, so callers fall back to
    /// the operand the lifter produced.
    /// </summary>
    private static LocalVariable? EnclosingThis(MethodAnalysisContext caller, MethodAnalysisContext callee, IOperand receiver)
    {
        if (caller.Locals.FirstOrDefault(l => l.IsThis) is not { } thisLocal || thisLocal.Type is not { } thisType)
            return null;

        // Already the enclosing instance: nothing to correct, and no need to look at the callee at all.
        if (ReferenceEquals(receiver, thisLocal))
            return null;

        // Only the shape IL2CPP leaves behind is worth the callee inspection: the receiver slot still holds
        // the previous call's return value, because no instruction ever loaded a real one. Anything else
        // (a field, a parameter, an argument) is a receiver the source really wrote.
        if (!IsCallResult(caller, receiver))
            return null;

        if (!CalleeIgnoresThis(callee))
            return null;

        return callee.DeclaringType is { } declaringType && thisType.IsAssignableTo(declaringType)
            ? thisLocal
            : null;
    }

    /// <summary>
    /// Cache keyed by the method's native address, never by its context object: a concrete generic's context is
    /// rebuilt on every lookup, so keying on it would miss every time and pin every instance (and its body) in
    /// memory for the rest of the run. The address is stable, shared by a generic and its instantiations, and
    /// costs one bool per method.
    /// </summary>
    private static readonly Dictionary<ulong, bool> CalleeIgnoresThisCache = [];

    /// <summary>
    /// Whether <paramref name="callee"/> provably never uses the `this` it is handed.
    /// Only X0's first access decides: a read before any write means the receiver is used; a write before any
    /// read means it is not; a branch reached first leaves it unknown and answers false.
    /// Unknown always answers false - nothing is rewritten on a guess (red line C5).
    /// </summary>
    private static bool CalleeIgnoresThis(MethodAnalysisContext callee)
    {
        var key = callee.UnderlyingPointer;

        if (key == 0)
            return false;

        lock (CalleeIgnoresThisCache)
            if (CalleeIgnoresThisCache.TryGetValue(key, out var cached))
                return cached;

        var result = ComputeCalleeIgnoresThis(callee);

        lock (CalleeIgnoresThisCache)
            CalleeIgnoresThisCache[key] = result;

        return result;
    }

    /// <summary>
    /// Whether <paramref name="operand"/> is a local whose only definition is a call's return value - i.e. the
    /// receiver slot was never loaded with anything the source wrote.
    /// </summary>
    private static bool IsCallResult(MethodAnalysisContext caller, IOperand operand)
    {
        if (operand is not LocalVariable local || caller.ControlFlowGraph is not { } cfg)
            return false;

        var definitions = 0;
        var definedByCall = false;

        foreach (var instruction in cfg.Instructions)
        {
            if (!ReferenceEquals(instruction.Destination, local))
                continue;

            if (++definitions > 1)
                return false;

            definedByCall = instruction.IsCall;
        }

        return definitions == 1 && definedByCall;
    }

    /// <summary>Whether an operand reads register X0, directly or as an addressing base.</summary>
    private static bool MentionsX0(IOperand operand) => operand switch
    {
        Register { Name: "X0" } => true,
        MemoryOperand { Base: Register { Name: "X0" } } => true,
        _ => false,
    };

    private static bool ComputeCalleeIgnoresThis(MethodAnalysisContext callee)
    {
        try
        {
            // Lift only - never Analyze here: analysis can register new concrete generic methods, and the
            // output format is enumerating the method collections while we run.
            var isil = callee.AppContext.InstructionSet.GetIsilFromMethod(callee);

            foreach (var instruction in isil)
            {
                var operands = instruction.Operands;
                var isMove = instruction.OpCode == OpCode.Move;

                // Any operand that mentions X0 - including as an addressing base - is a read of the
                // incoming `this`, except the destination slot of a move.
                for (var i = 0; i < operands.Count; i++)
                {
                    if (isMove && i == 0)
                        continue;

                    if (MentionsX0(operands[i]))
                        return false;
                }

                // Past a branch we cannot say what reached X0.
                if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.IndirectJump)
                    return false;

                // The prologue overwrote X0 before ever reading it.
                if (isMove && operands.Count > 0 && MentionsX0(operands[0]))
                    return true;
            }
        }
        catch
        {
            // Undecodable body: assume it uses `this`, so nothing is rewritten on a guess.
        }

        return false;
    }

    /// <summary>
    /// The <c>(object, native int)</c> constructor a delegate's <c>newobj</c> must call, as a descriptor.
    /// An instantiated generic type carries its own constructor list only on the definition, so the
    /// definition's constructor is projected onto the instance - the same machinery generic calls use
    /// (see FINDING-010), because emitting the definition's own constructor would reference an open <c>T</c>.
    /// </summary>
    private static IMethodDescriptor? FindDelegateCtor(TypeAnalysisContext delegateType)
    {
        if (delegateType is GenericInstanceTypeAnalysisContext instance)
            return instance.GenericType.Methods
                .FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 2 })?
                .ToMethodDescriptorOnInstance(instance);

        return delegateType.Methods
            .FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 2 })?
            .ToMethodDescriptor();
    }

    /// <summary>
    /// Whether <paramref name="type"/> is a delegate type. The <c>IsDelegate</c> property only recognises the
    /// instantiated form, and IL2CPP's allocations frequently name the generic *definition*
    /// (<c>Comparison`1</c> rather than <c>Comparison&lt;AISkillFVO&gt;</c>), so the base chain is walked too.
    /// </summary>
    private static bool IsDelegateType(TypeAnalysisContext type)
    {
        if (type.IsDelegate)
            return true;

        var current = type.BaseType;

        for (var depth = 0; current != null && depth < 32; depth++)
        {
            if (current.Namespace == "System" && current.Name is "MulticastDelegate" or "Delegate")
                return true;

            current = current.BaseType;
        }

        return false;
    }

    /// <summary>
    /// The MethodInfo a delegate allocation targets, or null when this is not a delegate creation.
    /// IL2CPP emits the delegate type's allocation and the target method's MethodInfo as two separate
    /// instructions, so the method has to be picked up from the neighbouring <c>Move</c>.
    /// </summary>
    private static Instruction? FindDelegateTarget(MethodAnalysisContext context, Instruction newobj)
    {
        var instructions = context.ControlFlowGraph!.Instructions;
        var index = instructions.IndexOf(newobj);

        if (index < 0)
            return null;

        for (var i = index + 1; i < instructions.Count; i++)
        {
            var candidate = instructions[i];

            if (candidate is { OpCode: OpCode.Move, Operands: [_, RuntimeMethodInfoAnalysisContext] })
                return candidate;

            // Stop at the first instruction that consumes the new object - the target, if any, comes first.
            if (candidate.Operands.Any(o => ReferenceEquals(o, newobj.Operands[0])))
                return null;
        }

        return null;
    }

    // Try find the follow up CallVoid for a constructor, after a Newobj.
    private static Instruction? FindConstructorCall(MethodAnalysisContext context, Instruction newobj)
    {
        var newObject = newobj.Operands[0];

        // The allocation and the constructor call routinely end up in different blocks
        var instructions = context.ControlFlowGraph!.Instructions;
        var index = instructions.IndexOf(newobj);

        if (index < 0)
            return null;

        for (var i = index + 1; i < instructions.Count; i++)
        {
            var candidate = instructions[i];

            if (candidate is not { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" }, ..] })
                continue;

            var receiver = ConstructorReceiverIndex(candidate);

            if (candidate.Operands.Count > receiver && ReferenceEquals(candidate.Operands[receiver], newObject))
                return candidate;
        }

        return null;
    }

    private static CilOpCode? FloatArithmeticConversion(Instruction instruction)
    {
        if (instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo))
            return null;

        return (instruction.Operands[0] as LocalVariable)?.Type?.FullName switch
        {
            "System.Single" => CilOpCodes.Conv_R4,
            "System.Double" => CilOpCodes.Conv_R8,
            _ => null,
        };
    }

    private static void LoadOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType = null)
    {
        var instructions = method.CilMethodBody!.Instructions;

        var module = method.DeclaringModule!;

        // A null reference reaches us as an integer zero, which would otherwise be emitted as a literal 0
        // and read back as a cast from a number.
        if (expectedType is { IsValueType: false } && IsZeroConstant(operand))
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        // A zeroed struct reaches us as an integer zero as well. A number is not convertible to a
        // struct in C#, so materialise the default value of that struct instead of the literal.
        if (expectedType is { } zeroed && IsCompositeValueType(zeroed) && IsZeroConstant(operand))
        {
            var zero = new CilLocalVariable(zeroed.ToTypeSignature());
            method.CilMethodBody.LocalVariables.Add(zero);
            instructions.Add(CilOpCodes.Ldloca, zero);
            instructions.Add(CilOpCodes.Initobj, zeroed.ToTypeSignature().ToTypeDefOrRef());
            instructions.Add(CilOpCodes.Ldloc, zero);
            return;
        }

        switch (operand)
        {
            case Immediate { Value: >= int.MinValue and <= int.MaxValue } immediate:
                instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                break;
            case Immediate immediate:
                instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                break;
            case FloatLiteral f:
                instructions.Add(CilOpCodes.Ldc_R4, f.Value);
                break;
            case DoubleLiteral d:
                instructions.Add(CilOpCodes.Ldc_R8, d.Value);
                break;
            case StringLiteral s:
                instructions.Add(CilOpCodes.Ldstr, s.Value);
                break;
            case LocalVariable local:
                LoadLocal(local, method, locals);
                break;
            case ArrayLength arrayLength:
                LoadLocal(arrayLength.Array, method, locals);
                instructions.Add(CilOpCodes.Ldlen);
                instructions.Add(CilOpCodes.Conv_I4);
                break;
            case AddressOf { Target: LocalVariable addressed }:
                // Taking the value here instead was tried (S33, fix46) and measured worse: the emitter's
                // notion of the expected type is not reliable enough to tell "wants a pointer" from
                // "wants a value", so it traded one error shape for a bigger one (CS0030 +537).
                instructions.Add(CilOpCodes.Ldloca, locals[addressed]);
                break;
            case AddressOf { Target: ArrayAccess elementAddress }:
                LoadLocal(elementAddress.Array, method, locals);
                LoadOperand(elementAddress.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema,
                    ((SzArrayTypeAnalysisContext)elementAddress.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayAccess arrayAccess:
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelem,
                    ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case FieldReference field:
                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Ldsfld, field.Field.ToFieldDescriptor());
                    break;
                }

                // IL2CPP inlines small BCL methods into their callers, so a body can end up reading a
                // BCL internal field directly (`List<T>._size`, `String.m_stringLength`). Those members
                // are invisible to the emitted assembly and C# cannot name them at all, so the site
                // would otherwise not compile. Where such a field *is* the backing store of a public
                // property, read the property: same value, same semantics, nothing approximated.
                if (TryEmitEquivalentProperty(field, method, locals, instructions))
                    break;

                LoadLocal(field.Local, method, locals);
                instructions.Add(CilOpCodes.Ldfld, field.Field.ToFieldDescriptor());
                break;
            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    LoadLocal(local2, method, locals);

                    // A load through a managed pointer (byref) dereferences it to yield the referent.
                    if (local2.Type is ByRefTypeAnalysisContext { ElementType: { } referent })
                        instructions.Add(referent.IsValueType
                            ? new CilInstruction(CilOpCodes.Ldobj, referent.ToTypeSignature().ToTypeDefOrRef())
                            : new CilInstruction(CilOpCodes.Ldind_Ref));
                    break;
                }
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unmanaged memory load: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeMethodInfoAnalysisContext runtimeMethod:
                // A delegate constructor takes its target as a native pointer, which is exactly ldftn.
                if (expectedType?.FullName == "System.IntPtr")
                {
                    instructions.Add(CilOpCodes.Ldftn, runtimeMethod.RepresentedMethod.ToMethodDescriptor());
                    break;
                }

                //Not fully implemented, these basically shouldn't actually ever exist in the final IL.
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeFieldInfoAnalysisContext runtimeField:
                // fieldof(F), e.g. the handle InitializeArray takes.
                if (expectedType?.FullName == "System.RuntimeFieldHandle")
                {
                    instructions.Add(CilOpCodes.Ldtoken, runtimeField.RepresentedField.ToFieldDescriptor());
                    break;
                }

                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext:
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case TypeAnalysisContext type:
                //typeof(T)
                var corLibScope = module.CorLibTypeFactory.CorLibScope;
                var typeFromHandle = corLibScope
                    .CreateTypeReference("System", "Type")
                    .CreateMemberReference("GetTypeFromHandle", MethodSignature.CreateStatic(
                        corLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false),
                        [corLibScope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)]));

                instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Call, typeFromHandle);
                break;
            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unknown operand: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldnull);
                break;
        }
    }
    
    /// <summary>
    /// Recognises "is this object exactly of type T" and emits <c>obj.GetType() == typeof(T)</c>.
    ///
    /// Two shapes reach here. (a) the type is named directly by the comparison operand. (b) the runtime
    /// type was materialised into a local first, so the comparison reads <c>[handle]</c>; that is only
    /// accepted when the handle is defined once (by a <c>typeof</c> load) and used once, by this very
    /// comparison - i.e. it exists solely to carry the type. Matching shape (b) on operand types alone
    /// was measured worse (S33, CS0030 +537): plain object/object comparisons satisfy it too.
    /// </summary>
    private static bool TryEmitExactTypeComparison(MethodAnalysisContext context, Instruction instruction, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var left = instruction.Operands[1];
        var right = instruction.Operands[2];

        IOperand typeOperand;
        LocalVariable objLocal;
        Instruction? consumedHandle = null;

        if (TryResolveSingleUseTypeHandle(context, left, out var leftType, out var leftDefinition)
            && TryResolveObjectSide(right, out var rightObject))
            (typeOperand, objLocal, consumedHandle) = (leftType, rightObject, leftDefinition);
        else if (TryResolveSingleUseTypeHandle(context, right, out var rightType, out var rightDefinition)
                 && TryResolveObjectSide(left, out var leftObject))
            (typeOperand, objLocal, consumedHandle) = (rightType, leftObject, rightDefinition);
        else if (left is TypeAnalysisContext && IsKlassPointerLoad(right, out var rightLocal))
            (typeOperand, objLocal) = (left, rightLocal);
        else if (right is TypeAnalysisContext && IsKlassPointerLoad(left, out var leftLocal))
            (typeOperand, objLocal) = (right, leftLocal);
        else
            return false;

        var module = method.DeclaringModule!;
        var instructions = method.CilMethodBody!.Instructions;

        var getType = module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Object")
            .CreateMemberReference("GetType", MethodSignature.CreateInstance(
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false)));

        LoadLocal(objLocal, method, locals);
        instructions.Add(CilOpCodes.Callvirt, getType);
        LoadOperand(typeOperand, method, locals, writeLine); // emits typeof(T)
        instructions.Add(CilOpCodes.Ceq);

        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }

        StoreToOperand(instruction.Operands[0], method, locals, writeLine);

        // The handle's definition is now part of the comparison above. Leaving it would emit
        // `IntPtr p = (IntPtr)typeof(T)`, a conversion C# does not have.
        if (consumedHandle != null)
        {
            consumedHandle.OpCode = OpCode.Nop;
            consumedHandle.SetOperands();
        }

        return true;
    }

    // The object half of a type comparison: the object itself, or its klass pointer read at offset 0.
    private static bool TryResolveObjectSide(IOperand operand, out LocalVariable local)
    {
        if (IsKlassPointerLoad(operand, out local))
            return !IsTypeHandleLocal(local);

        if (operand is LocalVariable { Type: { IsValueType: false } } direct && !IsTypeHandleLocal(direct))
        {
            local = direct;
            return true;
        }

        local = null!;
        return false;
    }

    // A local that stands for a type rather than for an instance of one.
    private static bool IsTypeHandleLocal(LocalVariable local) => local.Type is RuntimeClassTypeAnalysisContext
        or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext
        or StaticFieldStorageTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext;

    /// <summary>
    /// Resolves <c>[handle]</c> (or the handle local itself) to the type it carries, but only when the
    /// handle is written exactly once - by a <c>typeof</c> load - and mentioned exactly twice in total
    /// (that load, and this comparison). That "single definition, single use" gate is what keeps this
    /// from rewriting ordinary comparisons.
    /// </summary>
    private static bool TryResolveSingleUseTypeHandle(MethodAnalysisContext context, IOperand operand,
        out TypeAnalysisContext type, out Instruction? definition)
    {
        type = null!;
        definition = null;

        var handle = operand switch
        {
            MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable baseLocal } => baseLocal,
            LocalVariable local => local,
            _ => null,
        };

        if (handle == null || !IsTypeHandleLocal(handle))
            return false;

        var writes = 0;
        var mentions = 0;

        foreach (var candidate in context.ControlFlowGraph!.Instructions)
        {
            if (candidate.Operands.Count > 0 && ReferenceEquals(candidate.Operands[0], handle))
            {
                writes++;
                definition = candidate;
            }

            foreach (var candidateOperand in candidate.Operands)
                if (MentionsLocal(candidateOperand, handle))
                    mentions++;
        }

        if (writes != 1 || mentions != 2 || definition is not { OpCode: OpCode.Move } || definition.Operands.Count < 2)
            return false;

        if (definition.Operands[1] is not TypeAnalysisContext carried)
            return false;

        type = carried;
        return true;
    }

    private static bool MentionsLocal(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable candidate => ReferenceEquals(candidate, local),
        MemoryOperand memory => MentionsLocal(memory.Base!, local) || (memory.Index != null && MentionsLocal(memory.Index, local)),
        AddressOf addressOf => MentionsLocal(addressOf.Target, local),
        _ => false,
    };
    
    private static bool IsKlassPointerLoad(IOperand operand, out LocalVariable local)
    {
        if (operand is MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable { Type.IsValueType: false } baseLocal })
        {
            local = baseLocal;
            return true;
        }

        local = null!;
        return false;
    }

    private static void PushDefaultOf(TypeAnalysisContext type, CilInstructionCollection instructions)
    {
        //TODO Remove this, we should be handling arguments correctly in ISIL resolution, this is a hack to emit balanced stacks.
        //TODO At the *very* least we should emit a console.writeline saying that we did this.
        if (!type.IsValueType)
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        switch (type.FullName)
        {
            case "System.Single": instructions.Add(CilOpCodes.Ldc_R4, 0f); break;
            case "System.Double": instructions.Add(CilOpCodes.Ldc_R8, 0d); break;
            case "System.Int64" or "System.UInt64": instructions.Add(CilOpCodes.Ldc_I8, 0L); break;
            default: instructions.Add(CilOpCodes.Ldc_I4_0); break;
        }
    }

    private static bool IsBoolean(IOperand operand, MethodAnalysisContext context) =>
        operand is LocalVariable { Type: { } type } && type == context.AppContext.SystemTypes.SystemBooleanType;

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };

    // A value type that a machine word cannot stand in for: a struct (or a nullable), as opposed to a
    // primitive or an enum, both of which are just integers at the CLR level.
    private static bool IsCompositeValueType(TypeAnalysisContext type) =>
        type is { IsValueType: true, IsEnumType: false }
        && type.FullName is not ("System.Boolean" or "System.Char" or "System.SByte" or "System.Byte"
            or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32"
            or "System.Int64" or "System.UInt64" or "System.Single" or "System.Double"
            or "System.IntPtr" or "System.UIntPtr" or "System.Void");
    
    private static TypeAnalysisContext? DestinationType(IOperand destination) =>
        destination switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            _ => null
        };

    private static void LoadLocal(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            return;
        }

        var parameter = method.Parameters.FirstOrDefault(p => p.Name == local.Name);

        if (parameter != null)
            instructions.Add(CilOpCodes.Ldarg, parameter);
        else
            instructions.Add(CilOpCodes.Ldloc, locals[local]);
    }

    private static void StoreToOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;

        switch (operand)
        {
            case LocalVariable local:
                instructions.Add(CilOpCodes.Stloc, locals[local]);
                break;

            case FieldReference field:
                var fieldDescriptor = field.Field.ToFieldDescriptor();

                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Stsfld, fieldDescriptor);
                    break;
                }

                // stfld wants the object underneath the value, but the value is already on the stack, so
                // park it in a temporary while we load the object.
                var scratch = new CilLocalVariable(fieldDescriptor.Signature!.FieldType);
                method.CilMethodBody!.LocalVariables.Add(scratch);

                instructions.Add(CilOpCodes.Stloc, scratch);
                LoadLocal(field.Local, method, locals);
                instructions.Add(CilOpCodes.Ldloc, scratch);
                instructions.Add(CilOpCodes.Stfld, fieldDescriptor);
                break;

            case ArrayAccess arrayAccess:
                // stelem needs array and index before the value, so the same trick as stfld
                var elementType = ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType;
                var elementScratch = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(elementScratch);

                instructions.Add(CilOpCodes.Stloc, elementScratch);
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldloc, elementScratch);
                instructions.Add(CilOpCodes.Stelem, elementType.ToTypeSignature().ToTypeDefOrRef());
                break;

            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    // Can pointer assignments just be ignored because it's C#? (Move [local], 123)
                    instructions.Add(CilOpCodes.Stloc, locals[local2]);
                    break;
                }
                instructions.Add(CilOpCodes.Pop);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Store into unknown operand: {operand}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Pop);
                break;
        }
    }
}
