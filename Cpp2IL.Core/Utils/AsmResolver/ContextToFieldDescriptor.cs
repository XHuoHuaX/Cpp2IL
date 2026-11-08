using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils.AsmResolver;

public static class ContextToFieldDescriptor
{
    private static FieldDefinition GetFieldDefinition(this FieldAnalysisContext context)
    {
        return context.GetExtraData<FieldDefinition>("AsmResolverField") ?? throw new($"AsmResolver field not found in method analysis context for {context}");
    }

    internal static FieldSignature ToFieldSignature(this FieldAnalysisContext context)
    {
        return new FieldSignature(context.ToTypeSignature());
    }

    public static IFieldDescriptor ToFieldDescriptor(this FieldAnalysisContext context)
    {
        return context is ConcreteGenericFieldAnalysisContext concreteField
            ? concreteField.ToFieldDescriptor()
            : context.GetFieldDefinition();
    }

    public static IFieldDescriptor ToFieldDescriptor(this ConcreteGenericFieldAnalysisContext context)
    {
        // The signature has to be the *instantiated* one. Using the base field's signature emits
        // `TweenerCore<T1,T2,TPOptions>::endValue` - a reference to a field on the open definition -
        // which is not legal IL for an instance whose owner is closed. That is what produced source like
        // ((TweenerCore<, , >)(object)t).endValue.
        //
        // The owner needs the same care: DeclaringType is typed as TypeAnalysisContext, so calling
        // ToTypeSignature() on it binds the *base* overload and produces the open definition again -
        // overload resolution is static, so the generic-instance overload is only reached by matching.
        var owner = context.DeclaringType is GenericInstanceTypeAnalysisContext generic
            ? generic.ToTypeSignature()
            : context.DeclaringType.ToTypeSignature();

        return new MemberReference(
            owner.ToTypeDefOrRef(),
            context.Name,
            context.ToFieldSignature());
    }
}
