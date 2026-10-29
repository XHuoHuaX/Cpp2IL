using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils.AsmResolver;

public static class ContextToMethodDescriptor
{
    private static MethodDefinition GetMethodDefinition(this MethodAnalysisContext context)
    {
        return context.GetExtraData<MethodDefinition>("AsmResolverMethod") ?? throw new($"AsmResolver method not found in method analysis context for {context}");
    }

    private static MethodSignature ToMethodSignature(this MethodAnalysisContext context)
    {
        var returnType = context.ReturnType.ToTypeSignature();
        var parameters = context.Parameters.Select(p => p.ToTypeSignature());

        return context.IsStatic
            ? MethodSignature.CreateStatic(returnType, context.GenericParameters.Count, parameters)
            : MethodSignature.CreateInstance(returnType, context.GenericParameters.Count, parameters);
    }

    public static IMethodDescriptor ToMethodDescriptor(this MethodAnalysisContext context)
    {
        if (context is ConcreteGenericMethodAnalysisContext concreteMethod)
            return concreteMethod.ToMethodDescriptor();

        var definition = context.GetMethodDefinition();

        // A call to a generic method *definition* with no recovered instantiation cannot be written in
        // C#: the type parameters are not in scope at the call site (CS7003, and ILSpy renders them as
        // `Foo<T>()`, which is CS0246). IL2CPP shares generic bodies, so the instantiation is sometimes
        // simply not recoverable. Close it with object arguments - the call stays well formed and the
        // casts already wrapping its result keep working, whereas guessing a concrete type would be a
        // silent wrong value.
        var genericParameterCount = context.GenericParameters.Count;
        if (genericParameterCount == 0)
            return definition;

        var memberReference = new MemberReference(
            context.DeclaringType?.ToTypeSignature().ToTypeDefOrRef(),
            context.Name,
            context.ToMethodSignature());

        var arguments = new TypeSignature[genericParameterCount];
        for (var i = 0; i < arguments.Length; i++)
            arguments[i] = PlaceholderForGenericParameter(context.AppContext, context.GenericParameters[i]).ToTypeSignature();

        return memberReference.MakeGenericInstanceMethod(arguments);
    }

    /// <summary>
    /// The type to use when a recovered generic argument is unknown. Prefer the parameter's own first
    /// real constraint (a `where T : Component` style constraint), because instantiating with plain
    /// <c>object</c> then fails with CS0311; fall back to <c>object</c>. This keeps the call valid
    /// without inventing a specific type - the invented type would be a silent wrong value.
    /// </summary>
    private static TypeAnalysisContext PlaceholderForGenericParameter(ApplicationAnalysisContext appContext,
        GenericParameterTypeAnalysisContext parameter)
    {
        foreach (var constraint in parameter.ConstraintTypes)
        {
            var name = constraint?.FullName;
            if (name is null or "System.Object" or "System.ValueType" or "System.Enum")
                continue;

            return constraint;
        }

        return appContext.SystemTypes.SystemObjectType;
    }

    public static IMethodDescriptor ToMethodDescriptor(this ConcreteGenericMethodAnalysisContext context)
    {
        var memberReference = new MemberReference(
            context.DeclaringType?.ToTypeSignature().ToTypeDefOrRef(),
            context.Name,
            context.BaseMethodContext.ToMethodSignature());

        var methodGenericParameters = context.MethodGenericParameters;
        if (methodGenericParameters.Count == 0)
            return memberReference;

        // A concrete instantiation must never be expressed in terms of the callee's own generic
        // parameters - that produces `GetComponent<T>()` in a method that declares no `T`, which is
        // CS0246/CS7003 and cannot compile. It happens because IL2CPP shares generic bodies, so the
        // instantiation is sometimes unrecoverable; substituting object keeps the call well-formed
        // without inventing a specific type (that would be a silent wrong value).
        var objectType = context.AppContext.SystemTypes.SystemObjectType;
        var typeSignatures = methodGenericParameters.Select(p =>
            p is GenericParameterTypeAnalysisContext gp && IsOwnParameter(gp, context, objectType)
                ? objectType.ToTypeSignature()
                : p.ToTypeSignature());

        return memberReference.MakeGenericInstanceMethod(typeSignatures);
    }

    /// <summary>
    /// True when the generic parameter belongs to the callee itself (or its declaring type) rather than
    /// to whoever instantiated it - i.e. the instantiation was not recovered.
    /// </summary>
    private static bool IsOwnParameter(GenericParameterTypeAnalysisContext parameter, ConcreteGenericMethodAnalysisContext context,
        TypeAnalysisContext objectType)
    {
        if (ReferenceEquals(parameter, objectType))
            return false;

        if (ReferenceEquals(parameter.Owner, context.BaseMethodContext))
            return true;

        // The same method can exist as several context instances (one per lookup), so the identity check
        // above is not enough - fall back to comparing full names.
        var ownerName = OwnerName(parameter.Owner);
        if (ownerName == null)
            return false;

        if (ownerName == context.BaseMethodContext.FullName)
            return true;

        for (var type = context.BaseMethodContext.DeclaringType; type != null; type = type.DeclaringType)
            if (ReferenceEquals(parameter.Owner, type) || ownerName == type.FullName)
                return true;

        return false;
    }

    private static string? OwnerName(HasGenericParameters owner) => owner switch
    {
        MethodAnalysisContext method => method.FullName,
        TypeAnalysisContext type => type.FullName,
        _ => null
    };
}
