using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using Cpp2IL.Core.Api;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.ProcessingLayers;

public class AttributeInjectorProcessingLayer : Cpp2IlProcessingLayer
{
    public override string Name => "Attribute Injector";
    public override string Id => "attributeinjector";

    private static bool _useEzDiffMode;

    /// <summary>
    /// Attributes that C# reserves for the compiler: user code may not mention them, and mentioning one
    /// is a hard error (CS8335, "do not use ...; it is reserved for compiler use"). IL still carries them,
    /// because Roslyn synthesises them from ordinary syntax (`in` / `ref readonly` / `scoped`) and IL2CPP
    /// copies whatever the IL says into metadata.
    /// Emitting one therefore makes the rebuilt source unparsable, while dropping it is lossless: the
    /// syntax that generated it regenerates it on the next compile. This is a language rule, not a
    /// property of any particular game.
    /// </summary>
    private static readonly HashSet<string> CompilerReservedAttributes = new(StringComparer.Ordinal)
    {
        "System.Runtime.CompilerServices.IsReadOnlyAttribute",
    };

    public override void Process(ApplicationAnalysisContext appContext, Action<int, int>? progressCallback = null)
    {
        //EZ diff mode removes token attributes and method address/rva fields to make diffing using e.g. git easier
        _useEzDiffMode = appContext.GetExtraData<string>("attr-injector-use-ez-diff") != null;

        InjectAttributeAttribute(appContext);

        if (!_useEzDiffMode)
            InjectTokenAttribute(appContext);

        InjectAddressAttribute(appContext);
        InjectFieldOffsetAttribute(appContext);
    }

    private static void InjectFieldOffsetAttribute(ApplicationAnalysisContext appContext)
    {
        var fieldOffsetAttributes = appContext.InjectTypeIntoAllAssemblies("Cpp2ILInjected", "FieldOffsetAttribute", appContext.SystemTypes.SystemAttributeType);

        var offsetFields = fieldOffsetAttributes.InjectFieldToAllAssemblies("Offset", appContext.SystemTypes.SystemStringType, FieldAttributes.Public);

        var fieldOffsetConstructors = fieldOffsetAttributes.InjectConstructor(false);

        foreach (var assemblyAnalysisContext in appContext.Assemblies)
        {
            var offsetField = offsetFields[assemblyAnalysisContext];

            var fieldOffsetConstructor = fieldOffsetConstructors[assemblyAnalysisContext];

            foreach (var f in assemblyAnalysisContext.Types.SelectMany(t => t.Fields))
            {
                if (f.CustomAttributes == null || f.BackingData == null || f.IsStatic)
                    continue;

                var newAttribute = new AnalyzedCustomAttribute(fieldOffsetConstructor);

                //This loop is not done parallel because f.Offset has heavy lock contention
                newAttribute.Fields.Add(new(offsetField, new CustomAttributePrimitiveParameter($"0x{f.Offset:X}", newAttribute, CustomAttributeParameterKind.Field, 0)));
                f.CustomAttributes.Add(newAttribute);
            }
        }
    }

    private static void InjectAddressAttribute(ApplicationAnalysisContext appContext)
    {
        var addressAttributes = appContext.InjectTypeIntoAllAssemblies("Cpp2ILInjected", "AddressAttribute", appContext.SystemTypes.SystemAttributeType);

        var rvaFields = addressAttributes.InjectFieldToAllAssemblies("RVA", appContext.SystemTypes.SystemStringType, FieldAttributes.Public);
        var offsetFields = addressAttributes.InjectFieldToAllAssemblies("Offset", appContext.SystemTypes.SystemStringType, FieldAttributes.Public);
        var lengthFields = addressAttributes.InjectFieldToAllAssemblies("Length", appContext.SystemTypes.SystemStringType, FieldAttributes.Public);

        var addressConstructors = addressAttributes.InjectConstructor(false);

        foreach (var assemblyAnalysisContext in appContext.Assemblies)
        {
            var rvaField = rvaFields[assemblyAnalysisContext];
            var offsetField = offsetFields[assemblyAnalysisContext];
            var lengthField = lengthFields[assemblyAnalysisContext];

            var addressConstructor = addressConstructors[assemblyAnalysisContext];

            foreach (var m in assemblyAnalysisContext.Types.SelectMany(t => t.Methods))
            {
                if (m.CustomAttributes == null || m.UnderlyingPointer == 0)
                    continue;

                var newAttribute = new AnalyzedCustomAttribute(addressConstructor);

                if (!_useEzDiffMode)
                {
                    newAttribute.Fields.Add(new(rvaField, new CustomAttributePrimitiveParameter($"0x{m.Rva:X}", newAttribute, CustomAttributeParameterKind.Field, 0)));
                    if (appContext.Binary.TryMapVirtualAddressToRaw(m.UnderlyingPointer, out var offset))
                        newAttribute.Fields.Add(new(offsetField, new CustomAttributePrimitiveParameter($"0x{offset:X}", newAttribute, CustomAttributeParameterKind.Field, 1)));
                }

                newAttribute.Fields.Add(new(lengthField, new CustomAttributePrimitiveParameter($"0x{m.RawBytes.Length:X}", newAttribute, CustomAttributeParameterKind.Field, newAttribute.Fields.Count)));
                m.CustomAttributes.Add(newAttribute);
            }
        }
    }

    private static void InjectTokenAttribute(ApplicationAnalysisContext appContext)
    {
        var tokenAttributes = appContext.InjectTypeIntoAllAssemblies("Cpp2ILInjected", "TokenAttribute", appContext.SystemTypes.SystemAttributeType);

        var tokenFields = tokenAttributes.InjectFieldToAllAssemblies("Token", appContext.SystemTypes.SystemStringType, FieldAttributes.Public);

        var tokenConstructors = tokenAttributes.InjectConstructor(false);

        foreach (var assemblyAnalysisContext in appContext.Assemblies)
        {
            var tokenField = tokenFields[assemblyAnalysisContext];

            var tokenConstructor = tokenConstructors[assemblyAnalysisContext];

            var toProcess = assemblyAnalysisContext.Types.SelectMany(ctx => ctx.Methods.Cast<HasCustomAttributes>()
                    .Concat(ctx.Fields)
                    .Concat(ctx.Events)
                    .Concat(ctx.Properties)
                    .Append(ctx))
                .Append(assemblyAnalysisContext);

            Parallel.ForEach(toProcess, context =>
            {
                if (context.CustomAttributes == null || context.Token == 0)
                    return;

                var newAttribute = new AnalyzedCustomAttribute(tokenConstructor);
                newAttribute.Fields.Add(new(tokenField, new CustomAttributePrimitiveParameter($"0x{context.Token:X}", newAttribute, CustomAttributeParameterKind.Field, 0)));
                context.CustomAttributes.Add(newAttribute);
            });
        }
    }

    private static void InjectAttributeAttribute(ApplicationAnalysisContext appContext)
    {
        if (appContext.MetadataVersion >= 29f)
        {
            //All attributes should be fully serializable anyway, as they're stored in metadata
            //However, we still need to read them all
            var toAnalyze = appContext.Assemblies.SelectMany(ctx => ctx.Types)
                .SelectMany(ctx => ctx.Methods
                    .SelectMany(m => m.Parameters.Cast<HasCustomAttributes>().Append(m))
                    .Concat(ctx.Fields)
                    .Concat(ctx.Events)
                    .Concat(ctx.Properties)
                    .Append(ctx));

            foreach (var hasCustomAttributes in toAnalyze)
                hasCustomAttributes.AnalyzeCustomAttributeData();

            // MiscUtils.ExecuteParallel(toAnalyze, ctx => ctx.AnalyzeCustomAttributeData());
            return;
        }

        var attributeAttributes = appContext.InjectTypeIntoAllAssemblies("Cpp2ILInjected", "AttributeAttribute", appContext.SystemTypes.SystemAttributeType);

        // This attribute is emitted once PER original attribute, so a member with two attributes of
        // the same (or even different) types carries two of them. Without an explicit
        // [AttributeUsage(AllowMultiple = true)] the injected type defaults to AllowMultiple = false
        // and the C# compiler rejects every second occurrence with CS0579 ("attribute repeated").
        AttributeInjectionUtils.ApplyAttributeUsageAttribute(appContext, attributeAttributes, AttributeTargets.All, true);

        var attributeTypeFields = attributeAttributes.InjectFieldToAllAssemblies("Type", appContext.SystemTypes.SystemTypeType, FieldAttributes.Public);
        var attributeRvaFields = attributeAttributes.InjectFieldToAllAssemblies("RVA", appContext.SystemTypes.SystemStringType, FieldAttributes.Public);
        var attributeOffsetFields = attributeAttributes.InjectFieldToAllAssemblies("Offset", appContext.SystemTypes.SystemStringType, FieldAttributes.Public);

        var attributeConstructors = attributeAttributes.InjectConstructor(false);

        foreach (var assemblyAnalysisContext in appContext.Assemblies)
        {
            var typeField = attributeTypeFields[assemblyAnalysisContext];
            var rvaField = attributeRvaFields[assemblyAnalysisContext];
            var offsetField = attributeOffsetFields[assemblyAnalysisContext];

            var attributeConstructor = attributeConstructors[assemblyAnalysisContext];

            var toProcess = assemblyAnalysisContext.Types
                .SelectMany(ctx => ctx.Methods.SelectMany(m => m.Parameters.Cast<HasCustomAttributes>().Append(m))
                    .Concat(ctx.Fields)
                    .Concat(ctx.Events)
                    .Concat(ctx.Properties)
                    .Append(ctx))
                .Append(assemblyAnalysisContext);

            MiscUtils.ExecuteParallel(toProcess, c => ProcessCustomAttributesForContext(c, typeField, rvaField, offsetField, attributeConstructor));
        }
    }

    /// <summary>
    /// Returns the name that <c>[DefaultMember]</c> must carry for <paramref name="context"/>, or null when
    /// <paramref name="attribute"/> is not a DefaultMemberAttribute or the context is not a type with a
    /// parameterized property (i.e. not an indexer at all).
    /// The C# compiler only records the type's own indexer there; explicit interface implementations are named
    /// <c>Ns.IFace.Item</c> and never become the default member.
    /// </summary>
    private static string? TryInferDefaultMemberName(AnalyzedCustomAttribute attribute, HasCustomAttributes context)
    {
        if (attribute.Constructor.DeclaringType?.FullName != "System.Reflection.DefaultMemberAttribute")
            return null;

        if (context is not TypeAnalysisContext typeContext)
            return null;

        var indexers = typeContext.Properties
            .Where(p => (p.Getter?.Parameters.Count ?? 0) > 0 || (p.Setter?.Parameters.Count ?? 0) > 1)
            .ToList();

        return indexers.Count == 0 ? null : (indexers.FirstOrDefault(p => !p.Name.Contains('.')) ?? indexers[0]).Name;
    }

    private static void ProcessCustomAttributesForContext(HasCustomAttributes context, FieldAnalysisContext typeField, FieldAnalysisContext rvaField, FieldAnalysisContext offsetField, MethodAnalysisContext ctor)
    {
        var seenReplacements = new HashSet<string>(StringComparer.Ordinal);
        // A bare [Attr] cannot express "twice": C# only permits a repeated attribute when the attribute
        // type opts into AllowMultiple, which a parameterless-ctor attribute effectively never does.
        // IL2CPP metadata can still list the same attribute twice on one member - the game's own C#
        // did not, so the duplicate comes from attribute-generator resolution - and the C# compiler
        // then rejects the whole assembly with CS0579. That is a declaration-phase error, which also
        // silences every method body of the assembly (docs/FINDING-012), so it must not be left in.
        var seenPlainAttributes = new HashSet<string>(StringComparer.Ordinal);

        if (_useEzDiffMode)
            context.CustomAttributes = [];
        else
        {
            context.AnalyzeCustomAttributeData(false);

            if (context.CustomAttributes == null)
                return;
        }

        for (var index = 0; index < context.CustomAttributes.Count; index++)
        {
            var attribute = context.CustomAttributes[index];

            if (CompilerReservedAttributes.Contains(attribute.Constructor.DeclaringType?.FullName ?? string.Empty))
            {
                context.CustomAttributes.RemoveAt(index);
                index--;
                continue;
            }

            if (attribute.IsSuitableForEmission)
            {
                //Attribute has all required parameters, so we don't need an injected one
                if (!attribute.HasAnyParameters && !attribute.AnyFieldsOrPropsSet
                                                   && attribute.Constructor.DeclaringType != null
                                                   && !seenPlainAttributes.Add(attribute.Constructor.DeclaringType.FullName!))
                {
                    context.CustomAttributes.RemoveAt(index);
                    index--;
                }

                continue;
            }

            //DefaultMemberAttribute has exactly one ctor parameter - the default member name - and no
            //parameterless ctor, so pre-29 metadata (which cannot read attribute blobs) always flattens it
            //into AttributeAttribute(Type, RVA, Offset). That placeholder carries no name, so no decompiler
            //can tell a parameterized property from an ordinary method: ILSpy gives up with
            //"C# has no syntax for parameterized property" and emits get_Item/set_Item, which then fails to
            //implement IEnumerable/IList/IDictionary indexers (CS0535/CS0683/CS0470).
            //The name is not a guess: the C# compiler writes [DefaultMember(X)] where X is the indexer's own
            //name, and IL2CPP keeps every property, so it is read back from the declaring type.
            if (attribute.ConstructorParameters.Count == 0 && TryInferDefaultMemberName(attribute, context) is { } defaultMemberName)
            {
                attribute.ConstructorParameters.Add(new CustomAttributePrimitiveParameter(defaultMemberName, attribute, CustomAttributeParameterKind.ConstructorParam, 0));
                continue;
            }

            //Get ptr, and from it, rva and offset
            var generatorPtr = context.CaCacheGeneratorAnalysis!.UnderlyingPointer;
            var generatorRva = context.AppContext.Binary.GetRva(generatorPtr);
            if (!context.AppContext.Binary.TryMapVirtualAddressToRaw(generatorPtr, out var offsetInBinary))
                offsetInBinary = 0;

            // The replacement attribute carries only (Type, RVA, Offset), all derived from the member
            // rather than from the individual attribute. Two attributes of the same type on one member
            // therefore produce two byte-identical injected attributes, which the C# compiler rejects
            // with CS0579 ("attribute repeated"). Deduplicating is lossless: identical replacements are
            // indistinguishable, so nothing is dropped that the replacement could have expressed.
            var dedupeKey = $"{attribute.Constructor.DeclaringType.FullName}|{generatorRva:X}|{offsetInBinary:X}";
            if (!seenReplacements.Add(dedupeKey))
            {
                context.CustomAttributes.RemoveAt(index);
                index--;
                continue;
            }

            //Create replacement attribute
            var replacementAttribute = new AnalyzedCustomAttribute(ctor);

            //Add the 3 fields to the replacement attribute
            replacementAttribute.Fields.Add(new(typeField, new CustomAttributeTypeParameter(attribute.Constructor.DeclaringType, replacementAttribute, CustomAttributeParameterKind.Field, 0)));
            replacementAttribute.Fields.Add(new(rvaField, new CustomAttributePrimitiveParameter($"0x{generatorRva:X}", replacementAttribute, CustomAttributeParameterKind.Field, 1)));
            replacementAttribute.Fields.Add(new(offsetField, new CustomAttributePrimitiveParameter($"0x{offsetInBinary:X}", replacementAttribute, CustomAttributeParameterKind.Field, 2)));

            //Replace the original attribute with the replacement attribute
            context.CustomAttributes[index] = replacementAttribute;
        }
    }
}
