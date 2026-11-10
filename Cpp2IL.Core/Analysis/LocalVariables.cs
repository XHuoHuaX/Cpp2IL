using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

public static class LocalVariables
{
    public static int MaxTypePropagationLoopCount = 5000;

    private const long StaticFieldsOffset64 = 0xB8;
    private const long StaticFieldsOffset32 = 0x5C;

    public static void CreateAll(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var instructions = cfg.Instructions;

        // Get all registers
        var registers = new List<Register>();
        foreach (var instruction in instructions)
            registers.AddRange(GetRegisters(instruction));

        // Remove duplicates
        registers = registers.Distinct().ToList();

        // Map those to locals
        var locals = new Dictionary<Register, LocalVariable>();
        for (var i = 0; i < registers.Count; i++)
        {
            var register = registers[i];
            locals.Add(register, new LocalVariable($"v{i}", register));
        }

        // Replace registers with locals
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is Register register)
                    instruction.SetOperand(i, locals[register]);

                if (operand is AddressOf { Target: Register addressed })
                    instruction.SetOperand(i, new AddressOf(locals[addressed]));

                if (operand is MemoryOperand memory)
                {
                    if (memory.Base != null)
                    {
                        var baseRegister = (Register)memory.Base;
                        memory.Base = locals[baseRegister];
                    }

                    if (memory.Index != null)
                    {
                        var index = (Register)memory.Index;
                        memory.Index = locals[index];
                    }

                    instruction.SetOperand(i, memory);
                }
            }
        }

        // The registers that hold a frame pointer rather than data, per target.
        static bool IsFrameRegister(string? name) => name is "rsp" or "rbp" or "ebp" or "sp" or "x29" or "fp";

        // IL2CPP addresses a stack slot as <frame register> + offset, e.g. `[v3 @ rsp+8]`. After the
        // register->local mapping that is a MemoryOperand based on the local holding the *frame pointer*,
        // which is not a memory load at all: it names a distinct slot of the current frame. Promote each
        // (frame local, offset) pair to a local of its own, so downstream sees a variable rather than an
        // unmanaged load. Without this the x64 backend drops ~71% of its bodies to
        // "Unmanaged memory load" (610,510 of 858,023 issues on a Unity 2018.2 x64 build).
        var slotLocals = new Dictionary<(Register, long), LocalVariable>();
        var promoteSlots = System.Environment.GetEnvironmentVariable("CPP2IL_NO_SLOT_PROMOTE") != "1";
        foreach (var instruction in promoteSlots ? instructions : System.Linq.Enumerable.Empty<Instruction>())
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand { Index: null, Scale: 0 } memory
                    || memory.Base is not LocalVariable frame
                    || !IsFrameRegister(frame.Register.Name))
                    continue;

                var key = (frame.Register, memory.Addend);
                if (!slotLocals.TryGetValue(key, out var slot))
                {
                    slot = new LocalVariable($"slot_{memory.Addend:X}", frame.Register);
                    slotLocals[key] = slot;
                }

                instruction.SetOperand(i, slot);
            }
        }

        method.Locals = locals.Select(kv => kv.Value).Concat(slotLocals.Values).ToList();
        // Return local names
        var retValIndex = 0;
        foreach (var instruction in instructions)
        {
            if (instruction.OpCode != OpCode.Return || instruction.Operands.Count != 1) continue;

            var returnLocal = (LocalVariable)instruction.Sources[0];

            returnLocal.Name = $"returnVal{retValIndex + 1}";
            returnLocal.IsReturn = true;
            retValIndex++;
        }

        // Add parameter names
        var paramLocals = new List<LocalVariable>();

        var operandOffset = method.IsStatic ? 0 : 1; // 'this'

        // 'this' param
        if (!method.IsStatic && method.Locals.Count > 0 && method.ParameterOperands.Count > 0)
        {
            var thisOperand = (Register)method.ParameterOperands[0];
            var thisLocal = method.Locals.FirstOrDefault(l => l.Register.Number == thisOperand.Number && l.Register.Version == -1)
                            // SSA does not always keep the entry value at version -1 (a method that
                            // overwrites its own `this` register, or a differing initial version, leaves
                            // no -1 local). Falling back is only safe when the register number identifies
                            // exactly one local - then it must be the parameter and cannot be a
                            // re-assignment. Ambiguous cases keep the warning rather than guessing.
                            ?? (method.Locals.Count(l => l.Register.Number == thisOperand.Number) == 1
                                ? method.Locals.First(l => l.Register.Number == thisOperand.Number)
                                : null);

            if (thisLocal != null)
            {
                thisLocal.Name = "this";
                thisLocal.IsThis = true;
                paramLocals.Add(thisLocal);
            }
            else
            {
                method.AddWarning($"'this' local not found (operand: {thisOperand})");
            }
        }

        // Check if method has MethodInfo*
        var hasMethodInfo = (method.ParameterOperands.Count - operandOffset) > method.Parameters.Count;
        var methodInfoIndex = method.ParameterOperands.Count - 1;

        // Add normal parameter names
        for (var i = 0; i < method.Parameters.Count; i++)
        {
            var operandIndex = i + operandOffset;
            if (hasMethodInfo && operandIndex == methodInfoIndex)
                break; // Skip MethodInfo*

            if (operandIndex >= method.ParameterOperands.Count)
                break;

            if (method.ParameterOperands[operandIndex] is not Register reg)
                continue;

            var local = method.Locals.FirstOrDefault(l => l.Register.Number == reg.Number && l.Register.Version == -1);
            if (local == null)
                continue;

            local.Name = method.Parameters[i].ParameterName;
            paramLocals.Add(local);
        }

        // Add MethodInfo*
        if (hasMethodInfo)
        {
            var methodInfoOperand = (Register)method.ParameterOperands[methodInfoIndex];
            var methodInfoLocal = method.Locals.FirstOrDefault(l => l.Register.Number == methodInfoOperand.Number && l.Register.Version == -1);

            if (methodInfoLocal != null)
            {
                methodInfoLocal.Name = "methodInfo";
                methodInfoLocal.IsMethodInfo = true;
                paramLocals.Add(methodInfoLocal);
            }
        }

        method.ParameterLocals = paramLocals;

        // the hidden return buffer takes the first argument register. we type it as the return
        // type so stores into it resolve to fields
        if (method.AppContext.Binary.PointerSizeBytes == 8
            && method.AppContext.InstructionSet.CallingConventionResolver?.HiddenReturnBufferRegister(method) is { } bufferRegister
            && method.Locals.FirstOrDefault(l => l.Register.Number == bufferRegister.Number && l.Register.Version == -1) is { } bufferLocal)
        {
            bufferLocal.Name = "returnBuffer";
            bufferLocal.Type = method.ReturnType;
        }
    }

    public static void RemoveUnused(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        cfg.BuildUseDefLists();

        var usedLocals = new HashSet<LocalVariable>();

        foreach (var block in cfg.Blocks)
        {
            foreach (var usedVar in block.Use.OfType<LocalVariable>())
                usedLocals.Add(usedVar);

            foreach (var definedVar in block.Def.OfType<LocalVariable>())
                usedLocals.Add(definedVar);
        }

        method.Locals.RemoveAll(x => !usedLocals.Contains(x));
    }

    private static List<Register> GetRegisters(Instruction instruction)
    {
        var registers = new List<Register>();

        foreach (var operand in instruction.Operands)
        {
            if (operand is AddressOf { Target: Register addressed })
            {
                if (!registers.Contains(addressed))
                    registers.Add(addressed);
            }

            if (operand is Register register)
            {
                if (!registers.Contains(register))
                    registers.Add(register);
            }

            if (operand is MemoryOperand memory)
            {
                if (memory.Base != null)
                {
                    var baseRegister = (Register)memory.Base;
                    if (!registers.Contains(baseRegister))
                        registers.Add(baseRegister);
                }

                if (memory.Index != null)
                {
                    var index = (Register)memory.Index;
                    if (!registers.Contains(index))
                        registers.Add(index);
                }
            }
        }

        return registers;
    }

    /// <summary>
    /// Resolves field accesses and propagates types together, to a fixpoint, while the method is
    /// still in SSA form (every local has a single, version-stable definition).
    ///
    /// The two are mutually enabling and so cannot be ordered as separate passes: a typed base lets
    /// <see cref="MetadataResolver.ResolveFieldOffsets"/> turn <c>[base + offset]</c> into a
    /// <see cref="FieldReference"/>, a resolved field load types its result with the field's type,
    /// and that result is in turn the base of the next access (directly, or after flowing through
    /// moves/phis). Both steps are monotonic - each only ever resolves an operand or fills a
    /// previously-unknown type - so the loop converges.
    /// </summary>
    /// <summary>
    /// Diagnostic (<c>CPP2IL_ADD_PROBE=&lt;type-substring&gt;</c>): reports whether the offset of an
    /// `Add object, constant` would resolve to a field of the type being addressed.
    ///
    /// That shape is how a *value-type* field's address reaches the ISIL - the native code computes
    /// `base + offset` so it can pass a byref, and nothing turns that back into a field. Before writing
    /// the rewrite it is worth knowing whether the offset even lands on a field boundary: on a miss the
    /// honest answer is to leave the method alone rather than invent one.
    /// </summary>
    private static void ProbeAddOffsets(MethodAnalysisContext method, string filter)
    {
        if (method.ControlFlowGraph is not { } cfg)
            return;

        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.OpCode != OpCode.Add || instruction.Operands.Count != 3)
                continue;

            if (instruction.Operands[1] is not LocalVariable { Type: { } baseType })
                continue;

            if (instruction.Operands[2] is not Immediate offsetOperand)
                continue;

            if (!baseType.FullName.Contains(filter, System.StringComparison.Ordinal))
                continue;

            var offset = (int)offsetOperand.Value;
            var matches = new List<string>();
            var inventory = new List<string>();

            // A generic instance carries no fields of its own - they live on the generic type definition.
            // The offset is per-instantiation though (the same definition reports a different offset for
            // Rect and for RectOffset), so the definition's fields are what has to be searched.
            var declaring = baseType is GenericInstanceTypeAnalysisContext instance ? instance.GenericType : baseType;

            for (var type = declaring; type != null; type = type.BaseType)
                foreach (var field in type.Fields)
                {
                    inventory.Add($"{field.Name}@{field.Offset:X}");

                    if (field.Offset == offset)
                        matches.Add($"{field.DeclaringType?.Name}.{field.Name}");
                }

            System.Console.WriteLine($"[add-probe]\t{method.DeclaringType?.Name}::{method.Name}\t{baseType.FullName}+{offset:X}\tmatches={matches.Count}\t{string.Join(" | ", matches.Take(3))}");
            System.Console.WriteLine($"[add-probe-fields]\t{declaring?.FullName}\tf[{declaring?.Fields.Count}]\t{string.Join(" ", inventory.Take(200))}");
        }
    }

    public static void ResolveTypesAndFields(MethodAnalysisContext method)
    {
        // Seed types from fixed ground truth - the method's own signature, and type-metadata global
        // loads. Applied once up front and, being applied first, they win over anything inferred later.
        PropagateFromReturn(method);
        PropagateFromParameters(method);
        SeedRuntimeClassTypes(method);
        SeedNewobjResults(method);
        SeedMethodInfoTypes(method);
        SeedComparisonResults(method);
        SeedFloatLiterals(method);

        // Everywhere there's a CallVoid after a Newobj, we can resolve the constructor call.
        MetadataResolver.ResolveConstructorCalls(method);

        // Everything else is mutually enabling and so runs to a fixpoint: a typed receiver lets an
        // ambiguous call resolve, a resolved call types its return value and arguments, a typed base
        // lets a field offset resolve, a field load types its result, and any of those can be the
        // receiver/base of the next step. Every pass is monotonic - it only resolves an operand or
        // fills a previously-unknown type - so the loop converges.
        var changed = true;
        var loopCount = 0;

        while (changed)
        {
            if (MaxTypePropagationLoopCount != -1 && ++loopCount > MaxTypePropagationLoopCount)
                throw new DecompilerException($"Type and field resolution not settling! (looped {MaxTypePropagationLoopCount} times)");

            changed = false;
            changed |= MetadataResolver.ResolveCallsViaMethodInfo(method);
            changed |= MetadataResolver.ResolveAmbiguousCalls(method);
            changed |= MetadataResolver.ResolveVirtualCalls(method);
            changed |= PropagateFromCallParameters(method);
            changed |= MetadataResolver.ResolveFieldOffsets(method);
            changed |= MetadataResolver.ResolveValueTypeFieldAddress(method);
            changed |= RgctxResolver.Run(method);
            changed |= PropagateStaticFieldStorage(method);
            changed |= TypeAddressedLocals(method);
            changed |= PropagateTypesOnce(method);
        }

        if (System.Environment.GetEnvironmentVariable("CPP2IL_ADD_PROBE") is { Length: > 0 } probeFilter)
            ProbeAddOffsets(method, probeFilter);

        if (!_layoutChecked && System.Environment.GetEnvironmentVariable("CPP2IL_LAYOUT_CHECK") == "1")
        {
            _layoutChecked = true;
            GenericInstanceFieldLayout.SelfCheck(method.AppContext);
            GenericInstanceFieldLayout.SelfCheckGenericSizes(method.AppContext);
        }

        if (!_fieldTypesProbed && System.Environment.GetEnvironmentVariable("CPP2IL_FIELD_TYPES") is { Length: > 0 } fieldTypeFilter)
        {
            _fieldTypesProbed = true;
            GenericInstanceFieldLayout.ProbeFieldTypes(method.AppContext, fieldTypeFilter);
        }
    }

    private static bool _layoutChecked;
    private static bool _fieldTypesProbed;

    // A type-metadata global load (Move local, typeof(T)) puts the runtime class pointer for T into
    // the local - an Il2CppClass*, not an instance of T. That is known exactly from the instruction,
    // so it is seeded as ground truth (overriding any prior guess) before the inference fixpoint,
    // rather than letting a monotonic pass first mistype the local as T itself.
    private static void SeedRuntimeClassTypes(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is TypeAnalysisContext type and not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext))
                destination.Type = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        }
    }

    /// <summary>
    /// Gives each <c>Newobj</c> destination the type being allocated. Called once up front from
    /// <see cref="ResolveTypesAndFields"/>, and again later once the class operand has actually been
    /// resolved to a <see cref="TypeAnalysisContext"/> - at the early point it is frequently still a raw
    /// address, so the local keeps whatever coarse type it was handed (typically the generic *definition*),
    /// which then decompiles as the unbound name in <c>List&lt;&gt; x = ...</c> (CS7003).
    /// </summary>
    public static void SeedNewobjResults(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Newobj || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination && InstantiatedType(instruction.Operands[1]) is { } type)
                destination.Type = type;
        }
    }

    private static TypeAnalysisContext? InstantiatedType(IOperand classOperand) =>
        classOperand switch
        {
            LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var t } } => t,
            RuntimeClassTypeAnalysisContext { RepresentedType: var t } => t,
            TypeAnalysisContext type => type, //not sure this is actually valid but for completeness
            _ => null,
        };

    // A method/field-metadata global load (Move local, methodof(M) / fieldof(F)) puts a MethodInfo*
    // or FieldInfo* into the local. MetadataResolver already resolved the address to a context naming
    // the member; that same context is the local's type (a runtime handle, recoverable via its
    // RepresentedMethod/RepresentedField).
    private static void SeedMethodInfoTypes(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext)
                destination.Type = (TypeAnalysisContext)instruction.Operands[1];
        }
    }

    // A comparison (CheckEqual, CheckLess, ...) writes a 0/1 result into its destination, so that local
    // is a System.Boolean regardless of what the compared operands are.
    private static void SeedComparisonResults(MethodAnalysisContext method)
    {
        var booleanType = method.AppContext.SystemTypes.SystemBooleanType;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode is < OpCode.CheckEqual or > OpCode.CheckLessOrEqual)
                continue;

            if (instruction.Destination is LocalVariable destination)
                destination.Type = booleanType;
        }
    }
    
    //Handles typing of locals for ref/out params. Returns whether anything new was typed
    public static bool TypeAddressedLocals(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not MethodAnalysisContext calledMethod)
                continue;

            var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

            // the receiver of a value type's instance method is a pointer to the value
            if (!calledMethod.IsStatic && firstArg < instruction.Operands.Count
                && instruction.Operands[firstArg] is AddressOf { Target: LocalVariable receiver }
                && calledMethod.DeclaringType is { IsValueType: true } declaringType)
                changed |= SetTypeIfUnknown(receiver, declaringType);

            var paramOffset = firstArg + (calledMethod.IsStatic ? 0 : 1);

            for (var i = paramOffset; i < instruction.Operands.Count; i++)
            {
                var parameterIndex = i - paramOffset;
                if (parameterIndex > calledMethod.Parameters.Count - 1) // Probably MethodInfo*
                    continue;

                if (instruction.Operands[i] is AddressOf { Target: LocalVariable referenced }
                    && calledMethod.Parameters[parameterIndex].ParameterType is ByRefTypeAnalysisContext { ElementType: { } referencedType })
                    changed |= SetTypeIfUnknown(referenced, referencedType);
            }
        }

        return changed;
    }

    // Fills in a local's type only when it is currently unknown, keeping propagation monotonic (a
    // type, once set, is never changed) so the fixpoint terminates. Returns whether it set anything.
    private static bool SetTypeIfUnknown(LocalVariable local, TypeAnalysisContext? type)
    {
        if (type == null || local.Type != null)
            return false;

        // An open generic *definition* is not a value type. Taking one as a local's type produces a
        // ClassSig naming something like `Seq`1` with no arguments, which is not legal C# and brings
        // CS7003 with CS0246/CS8370 cascading off it. Refusing it here leaves the local unknown, and the
        // emitter's own rule turns unknown into object - the same degradation it already applies to every
        // type it cannot name.
        if (type is { GenericParameters.Count: > 0 } and not GenericInstanceTypeAnalysisContext)
            return false;

        local.Type = type;
        return true;
    }

    /// <summary>
    /// Branch counters for the static-field-storage propagation, gated by CPP2IL_SF_DIAG=1.
    /// Evidence first: an ISIL dump showed that `[..+0xB8]` (static_fields) was accessed 82 times in
    /// 40 sampled methods and resolved to a FieldReference zero times, i.e. static field READS never
    /// become ldsfld. These counters tell us which guard rejects them, instead of guessing.
    /// </summary>
    public static readonly System.Collections.Concurrent.ConcurrentDictionary<string, int> StaticFieldDiag = new();
    private static readonly bool SfDiagEnabled = System.Environment.GetEnvironmentVariable("CPP2IL_SF_DIAG") == "1";
    private static void SfDiag(string key)
    {
        if (SfDiagEnabled)
            StaticFieldDiag.AddOrUpdate(key, 1, (_, v) => v + 1);
    }

    /// <summary>Public sink so other analysis passes can feed the same histogram.</summary>
    public static void SfDiagPub(string key) => SfDiag(key);

    private static bool PropagateStaticFieldStorage(MethodAnalysisContext method)
    {
        var staticFieldsOffset = method.AppContext.Binary.is32Bit ? StaticFieldsOffset32 : StaticFieldsOffset64;
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is not LocalVariable destination || destination.Type is StaticFieldStorageTypeAnalysisContext)
                continue;

            if (instruction.Operands[1] is not MemoryOperand { Index: null, Scale: 0 } memory || memory.Addend != staticFieldsOffset)
                continue;

            SfDiag($"sf_read_candidate");

            if (memory.Base is not LocalVariable baseLocal)
            {
                SfDiag("skip_base_not_local");
                continue;
            }

            var owner = baseLocal.Type switch
            {
                RuntimeClassTypeAnalysisContext { RepresentedType: var direct } => direct,
                // ARM64 / metadata 24.x loads the class handle through one extra indirection: the
                // codegen emits `Move klass,[typeof(T)]` and then `LDR X,[klass + static_fields]`.
                // Cpp2IL types the metadata-usage load itself as an opaque
                // RuntimeClassTypeAnalysisContext (which has no fields), so the intermediate local
                // stays untyped and the direct rule above never fires - the static field then shows
                // up as an opaque memory access. Look through exactly that one indirection.
                null => FindClassHandleOwner(method, baseLocal),
                _ => null,
            };

            if (owner == null)
            {
                // Classify WHY the one-indirection walk failed, so the histogram itself names the
                // shapes instead of us guessing from a biased sample.
                SfDiag(baseLocal.Type == null
                    ? "skip_owner_null_from_untyped_base:" + ClassifyBaseDef(method, baseLocal)
                    : "skip_owner_null_from_typed_base");
                continue;
            }

            SfDiag("sf_storage_typed");
            destination.Type = new StaticFieldStorageTypeAnalysisContext(owner, owner.DeclaringAssembly);
            changed = true;
        }

        return changed;
    }

    /// <summary>
    /// If <paramref name="local"/> is defined by a single load with no addend from a local typed as
    /// <see cref="RuntimeClassTypeAnalysisContext"/>, returns the type that handle represents.
    /// This is the one-indirection class-handle load the ARM64 codegen emits before touching
    /// <c>Il2CppClass::static_fields</c>.
    /// </summary>
    private static TypeAnalysisContext? FindClassHandleOwner(MethodAnalysisContext method, LocalVariable local)
        => FindClassHandleOwnerCore(method, local, 0);

    private static TypeAnalysisContext? FindClassHandleOwnerCore(MethodAnalysisContext method, LocalVariable local, int depth)
    {
        // Depth limit: phi cycles are legal in the IR and must not spin.
        if (depth > 4)
            return null;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.Operands.Count == 0 || instruction.Operands[0] is not LocalVariable dst || dst.Name != local.Name)
                continue;

            // A merge point: `Phi dst, src1, src2, ...`. Looking through it is only sound when every
            // incoming value resolves to the SAME class handle; otherwise the handle is genuinely
            // ambiguous at this merge and we must not pick one of them.
            // This is the dominant failure shape (26,441 of 35,276 static-field bases): the class
            // handle is materialised in two branches and merged, so the first definition is a Phi.
            if (instruction.OpCode == OpCode.Phi)
            {
                TypeAnalysisContext? agreed = null;
                for (var i = 1; i < instruction.Operands.Count; i++)
                {
                    if (instruction.Operands[i] is not LocalVariable input)
                        return null;

                    var viaInput = FindClassHandleOwnerCore(method, input, depth + 1);
                    if (viaInput == null)
                        return null;

                    if (agreed == null)
                        agreed = viaInput;
                    else if (!ReferenceEquals(agreed, viaInput) && agreed.FullName != viaInput.FullName)
                        return null; // conflicting handles - do not invent a winner
                }

                return agreed;
            }

            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                return null;

            // only the first definition counts - a phi or a second definition means we cannot say
            if (instruction.Operands[1] is MemoryOperand { Index: null, Scale: 0, Addend: 0 } memory
                && memory.Base is LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented } })
                return represented;

            return null;
        }

        return null;
    }

    /// <summary>
    /// Diagnostic only: names the shape of the first definition of <paramref name="local"/> so the
    /// sfdiag histogram classifies why <see cref="FindClassHandleOwner"/> failed, instead of us
    /// guessing from a small biased sample.
    /// </summary>
    private static string ClassifyBaseDef(MethodAnalysisContext method, LocalVariable local)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.Operands.Count == 0 || instruction.Operands[0] is not LocalVariable dst || dst.Name != local.Name)
                continue;

            if (instruction.OpCode != OpCode.Move)
                return "first_def_is_" + instruction.OpCode;

            if (instruction.Operands.Count < 2)
                return "move_without_source";

            return instruction.Operands[1] switch
            {
                MemoryOperand { Index: not null } => "move_deref_indexed",
                MemoryOperand { Scale: not 0 } => "move_deref_scaled",
                MemoryOperand { Addend: not 0 } => "move_deref_with_addend",
                MemoryOperand { Base: LocalVariable { Type: RuntimeMethodInfoAnalysisContext } } => "move_deref_of_methodinfo",
                MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext } } => "move_deref_of_classhandle_but_untyped_dst",
                MemoryOperand { Base: LocalVariable { Type: null } } => "move_deref_of_untyped_base",
                MemoryOperand { Base: LocalVariable { Type: not null } } => "move_deref_of_other_typed",
                MemoryOperand { Base: not LocalVariable } => "move_deref_of_non_local",
                LocalVariable { Type: RuntimeClassTypeAnalysisContext } => "move_from_classhandle_local",
                LocalVariable => "move_from_local",
                _ => "move_from_" + instruction.Operands[1].GetType().Name,
            };
        }

        return "no_local_def";
    }

    // A single propagation sweep over every move and phi. Returns whether it filled in any type.
    private static bool PropagateTypesOnce(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Move:
                    changed |= PropagateMove(instruction, method.AppContext.Binary.PointerSizeBytes);
                    break;
                case OpCode.Phi:
                    changed |= PropagatePhi(instruction);
                    break;
                case OpCode.Add or OpCode.Subtract:
                    changed |= PropagateArithmetic(instruction, method);
                    break;
                // A product is never pointer arithmetic, so an integer operand really does make the result an
                // integer. Without this the product of two ints stays untyped, degrades to object, and every
                // later use becomes `object >> int`, `object + int` (CS0019) - the shifts are how the compiler
                // spells those divisions in the original code.
                case OpCode.Multiply:
                    changed |= PropagateArithmetic(instruction, method) || PropagateIntegerResult(instruction, method);
                    break;
                case OpCode.Divide or OpCode.Modulo:
                    changed |= PropagateArithmetic(instruction, method) || PropagateIntegerResult(instruction, method);
                    break;
                case OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Not or OpCode.Negate
                    or OpCode.ShiftLeft or OpCode.ShiftRight:
                    changed |= PropagateBooleanResult(instruction, method) || PropagateIntegerResult(instruction, method);
                    break;
            }
        }

        return changed;
    }

    // A local assigned a float/double literal (a lifted rodata constant load) is that float type
    private static void SeedFloatLiterals(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands[0] is not LocalVariable destination)
                continue;

            destination.Type = instruction.Operands[1] switch
            {
                FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
                DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
                _ => destination.Type,
            };
        }
    }

    // Arithmetic on a float operand is float arithmetic, so the result is that float type.
    private static bool PropagateArithmetic(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands is not [LocalVariable { Type: null } destination, var left, var right])
            return false;

        if ((FloatOperandType(left, method) ?? FloatOperandType(right, method)) is not { } floatType)
            return false;

        return SetTypeIfUnknown(destination, floatType);
    }

    // An integer operand makes the result an integer. Excludes bool operands so flag logic stays boolean.
    private static bool PropagateIntegerResult(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands[0] is not LocalVariable { Type: null } destination)
            return false;

        for (var i = 1; i < instruction.Operands.Count; i++)
            if (IntegerResultType(instruction.Operands[i], method) is { } integerType)
                return SetTypeIfUnknown(destination, integerType);

        return false;
    }

    // The logical operators are also defined on bool - `&`, `|`, `^` and `!` on booleans yield a
    // boolean - so a bitwise op with boolean operands is flag logic, and its result is bool. Nothing
    // else types these: the integer rule above deliberately leaves boolean operands alone. Left
    // untyped, the result degrades to object and every later use becomes `object & int`, `~object`.
    private static bool PropagateBooleanResult(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands[0] is not LocalVariable { Type: null } destination)
            return false;

        if (instruction.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight)
            return false; // no boolean shift: a bool operand here would be a mistyped integer

        for (var i = 1; i < instruction.Operands.Count; i++)
            if (BooleanOperandType(instruction.Operands[i]) != null)
                return SetTypeIfUnknown(destination, method.AppContext.SystemTypes.SystemBooleanType);

        return false;
    }

    private static TypeAnalysisContext? BooleanOperandType(IOperand operand) => operand switch
    {
        LocalVariable { Type: { FullName: "System.Boolean" } boolean } => boolean,
        FieldReference { Field.FieldType: { FullName: "System.Boolean" } boolean } => boolean,
        _ => null,
    };

    private static TypeAnalysisContext? IntegerResultType(IOperand operand, MethodAnalysisContext method)
    {
        var type = operand switch
        {
            LocalVariable { Type: { } localType } => localType,
            FieldReference field => field.Field.FieldType,
            _ => null,
        };

        return type?.FullName switch
        {
            "System.Byte" or "System.SByte" or "System.Int16" or "System.UInt16"
                or "System.Int32" or "System.UInt32" or "System.Char" => method.AppContext.SystemTypes.SystemInt32Type,
            "System.Int64" or "System.UInt64" => method.AppContext.SystemTypes.SystemInt64Type,
            _ => null,
        };
    }

    private static TypeAnalysisContext? FloatOperandType(IOperand operand, MethodAnalysisContext method) =>
        operand switch
        {
            FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
            DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
            LocalVariable { Type: { FullName: "System.Single" } single } => single,
            LocalVariable { Type: { FullName: "System.Double" } @double } => @double,
            _ => null,
        };

    private static bool PropagateMove(Instruction move, int pointerSize)
    {
        var destination = move.Operands[0];
        var source = move.Operands[1];

        // Move local, local: copy a known type in whichever direction is missing it.
        if (destination is LocalVariable destLocal && source is LocalVariable sourceLocal)
            return SetTypeIfUnknown(destLocal, sourceLocal.Type) || SetTypeIfUnknown(sourceLocal, destLocal.Type);

        // Move local, field: a field load types its result with the field's type. This is the edge
        // that lets the loaded value go on to be the base of a further field access.
        if (destination is LocalVariable loadDest && source is FieldReference loadField)
            return SetTypeIfUnknown(loadDest, loadField.Field.FieldType);

        // Move field, local: a field store types the stored value with the field's type.
        if (destination is FieldReference storeField && source is LocalVariable storeSource)
            return SetTypeIfUnknown(storeSource, storeField.Field.FieldType);

        // An element of T[] is a T, whether we loaded it (reference arrays) or only computed its address
        if (destination is LocalVariable { Type: null } elementDest
            && source is MemoryOperand { Base: LocalVariable { Type: SzArrayTypeAnalysisContext { ElementType: { } elementType } } } elementAccess
            && (elementAccess.Index != null || elementAccess.Addend >= 4L * pointerSize))
            return SetTypeIfUnknown(elementDest, elementType);

        // Move local, [byref]: dereferencing a managed pointer to a reference type yields that referent
        // (a struct byref accesses fields directly with no deref, so this only fires for class referents).
        if (destination is LocalVariable { Type: null } derefDest
            && source is MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable { Type: ByRefTypeAnalysisContext { ElementType: { IsValueType: false } referent } } })
            return SetTypeIfUnknown(derefDest, referent);

        // Move local, [obj]: offset 0 of a reference-typed value is its klass pointer.
        if (destination is LocalVariable { Type: null } klassDest
            && source is MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable { Type: { } baseType } }
            && baseType is not (RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext or ByRefTypeAnalysisContext)
            && !baseType.IsValueType)
            return SetTypeIfUnknown(klassDest, new RuntimeClassTypeAnalysisContext(baseType, baseType.DeclaringAssembly));

        return false;
    }

    // A phi is a copy from each predecessor's value, so types flow both ways across it - mirroring
    // the bidirectional Move copies it decays into once SSA is destroyed.
    private static bool PropagatePhi(Instruction phi)
    {
        if (phi.Operands[0] is not LocalVariable destination)
            return false;

        var changed = false;

        // Forward: an untyped phi result takes the type of any typed input.
        if (destination.Type == null)
        {
            for (var i = 1; i < phi.Operands.Count; i++)
            {
                if (phi.Operands[i] is LocalVariable { Type: { } inputType })
                {
                    changed = SetTypeIfUnknown(destination, inputType);
                    break;
                }
            }
        }

        // Backward: a typed phi result types each of its still-untyped inputs.
        if (destination.Type != null)
        {
            for (var i = 1; i < phi.Operands.Count; i++)
            {
                if (phi.Operands[i] is LocalVariable input)
                    changed |= SetTypeIfUnknown(input, destination.Type);
            }
        }

        return changed;
    }

    private static bool PropagateFromCallParameters(MethodAnalysisContext method)
    {
        var changed = false;

        // A lea and the call it's passed to are still separate here. The address only gets folded into the
        // call later, so an argument's address-of has to be found through the local carrying it.
        var addressesOf = new Dictionary<LocalVariable, LocalVariable>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands[0] is LocalVariable pointer
                && instruction.Operands[1] is AddressOf { Target: LocalVariable pointee })
                addressesOf[pointer] = pointee;
        }

        LocalVariable? Addressed(IOperand operand) => operand switch
        {
            AddressOf { Target: LocalVariable direct } => direct,
            LocalVariable local when addressesOf.TryGetValue(local, out var indirect) => indirect,
            _ => null
        };

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            if (instruction.Operands[0] is not MethodAnalysisContext calledMethod)
                continue;

            // Return value: a constructor yields its declaring type, otherwise the declared return type.
            if (instruction.Destination is LocalVariable returnValue)
            {
                var producedType = calledMethod.Name is ".ctor" or ".cctor" ? calledMethod.DeclaringType : calledMethod.ReturnType;

                // NOTE: substituting the receiver's arguments into the return type here was tried and
                // reverted - it threw ArgumentOutOfRangeException on five methods (the operand layout is
                // not uniform across call shapes). The open-definition refusal in SetTypeIfUnknown covers
                // the same defect from the other end without touching operand indexing.

                if (producedType != method.AppContext.SystemTypes.SystemVoidType)
                    changed |= SetTypeIfUnknown(returnValue, producedType);
            }


            // Call operands
            // 0. Target
            // 1. ReturnValue
            // 2. thisParam
            // ... parameters

            // CallVoid operands
            // 0. Target
            // 1. thisParam
            // ... parameters
            var thisParamIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

            // 'this' param
            if (!calledMethod.IsStatic
                && instruction.Operands[thisParamIndex] is LocalVariable thisParam)
            {
                changed |= SetTypeIfUnknown(thisParam, calledMethod.DeclaringType);
            }

            // Value type instance method, first arg is address of value, but we need to type the value
            if (!calledMethod.IsStatic
                && Addressed(instruction.Operands[thisParamIndex]) is { } addressedReceiver
                && calledMethod.DeclaringType is { IsValueType: true } valueType)
            {
                changed |= SetTypeIfUnknown(addressedReceiver, valueType);
            }

            // Remaining arguments map positionally onto the callee's declared parameters.
            var paramOffset = calledMethod.IsStatic ? 1 : 2;
            if (instruction.OpCode == OpCode.Call) // Skip the return value operand
                paramOffset += 1;

            for (var i = paramOffset; i < instruction.Operands.Count; i++)
            {
                var parameterIndex = i - paramOffset;
                if (parameterIndex > calledMethod.Parameters.Count - 1) // Probably MethodInfo*
                    continue;

                var parameterType = calledMethod.Parameters[parameterIndex].ParameterType;

                if (parameterType is ByRefTypeAnalysisContext { ElementType: { } referencedType }
                    && Addressed(instruction.Operands[i]) is { } referenced)
                {
                    changed |= SetTypeIfUnknown(referenced, referencedType);
                    continue;
                }

                if (instruction.Operands[i] is LocalVariable local)
                    changed |= SetTypeIfUnknown(local, parameterType);
            }
        }

        return changed;
    }

    private static void PropagateFromParameters(MethodAnalysisContext method)
    {
        // 'this'
        if (!method.IsStatic)
        {
            var thisLocal = method.ParameterLocals.FirstOrDefault(p => p.IsThis);
            if (thisLocal != null)
                thisLocal.Type = method.DeclaringType is { GenericParameters.Count: > 0 } generic
                    ? new GenericInstanceTypeAnalysisContext(generic, generic.GenericParameters)
                    : method.DeclaringType;
        }

        if (method.ParameterLocals.FirstOrDefault(p => p.IsMethodInfo) is { } methodInfoLocal && method.DeclaringType is { } owner)
            methodInfoLocal.Type = new RuntimeMethodInfoAnalysisContext(method, owner.DeclaringAssembly);

        if (method.Parameters.Count == 0)
            return;

        // Normal params
        var paramIndex = 0;
        foreach (var local in method.ParameterLocals)
        {
            if (local.IsThis || local.IsMethodInfo)
                continue;

            if (paramIndex >= method.Parameters.Count)
                break;

            local.Type = method.Parameters[paramIndex].ParameterType;
            paramIndex++;
        }
    }

    private static void PropagateFromReturn(MethodAnalysisContext method)
    {
        var returns = method.ControlFlowGraph!.Instructions.Where(i => i.OpCode == OpCode.Return);

        foreach (var instruction in returns)
        {
            if (instruction.Operands.Count == 1 && instruction.Operands[0] is LocalVariable local)
                local.Type = method.ReturnType;
        }
    }
}
