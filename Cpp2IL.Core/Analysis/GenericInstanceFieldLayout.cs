using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Resolves field offsets on generic types, which are all 0 in the metadata.
//
// The layout is per-instantiation, not per-definition: the same `TweenerCore`3` puts `startValue` at
// 0x124 when the type argument is `Rect` and at 0x144 when it is `Color2`, because the base class is
// generic too and its size follows the arguments. So the arguments have to be substituted into every
// field type before anything is measured.
public static class GenericInstanceFieldLayout
{
    private const int MaxNesting = 16;

    /// <summary>
    /// Measured, not assumed: switching this to 4 (the "0x122 rounded to 0x124" reading of one
    /// TweenerCore site) dropped the self-check from 27429 ok / 1336 miss to 11594 / 17171. Eight is
    /// the rule; whatever explains that site, it is not a smaller alignment.
    /// </summary>

    /// <summary>
    /// Finds the instance field that starts exactly at <paramref name="targetOffset"/>.
    ///
    /// Returns null whenever the layout cannot be determined exactly - an unknown field type, a base
    /// class whose arguments do not line up, nesting too deep. Callers must treat null as "no answer",
    /// never as "no field there": guessing here would put a wrong field name into the output.
    /// </summary>
    /// <param name="definition">The generic type definition.</param>
    /// <param name="targetOffset">Byte offset from the start of the object.</param>
    /// <param name="arguments">The instantiation's type arguments, in declaration order.</param>
    public static FieldAnalysisContext? FindFieldAtOffset(TypeAnalysisContext definition, long targetOffset,
        IReadOnlyList<TypeAnalysisContext>? arguments = null)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        if (BuildSubstitution(definition, arguments) is not { } substitution)
            return null;

        var chain = new List<(TypeAnalysisContext Type, Dictionary<string, TypeAnalysisContext> Map)>();

        for (var type = definition; type != null; type = type.BaseType)
        {
            // A base class may re-order or wrap its arguments (`class A<T> : B<List<T>>`). Only the
            // same-name case can be mapped through the single substitution table we have, so anything
            // else is a miss rather than a guess.
            if (type == definition)
            {
                chain.Insert(0, (type, substitution));
                continue;
            }

            if (BuildSubstitution(type, arguments) is not { } baseSubstitution)
                return null;

            chain.Insert(0, (type, baseSubstitution));
        }

        var offset = 2L * pointerSize;

        foreach (var (type, map) in chain)
            foreach (var field in type.Fields)
            {
                if (field.IsStatic)
                    continue;

                if (GetSizeAndAlignment(Substitute(field.FieldType, map), pointerSize, map, 0) is not var (size, alignment))
                    return null;

                offset = Align(offset, alignment);

                if (offset == targetOffset)
                    return field;

                offset += size;
            }

        return null;
    }

    /// <summary>
    /// Measures a non-generic type's own fields the same way, so the substitution and alignment rules
    /// can be checked against metadata that does carry real offsets. Used by the layout self-check.
    /// </summary>
    public static long? ComputeOwnFieldOffset(TypeAnalysisContext definition, FieldAnalysisContext field)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;
        var offset = 2L * pointerSize;

        foreach (var candidate in definition.Fields)
        {
            if (candidate.IsStatic)
                continue;

            if (GetSizeAndAlignment(candidate.FieldType, pointerSize, EmptyMap, 0) is not var (size, alignment))
                return null;

            offset = Align(offset, alignment);

            if (candidate == field)
                return offset;

            offset += size;
        }

        return null;
    }

    private static readonly Dictionary<string, TypeAnalysisContext> EmptyMap = [];

    private static Dictionary<string, TypeAnalysisContext>? BuildSubstitution(TypeAnalysisContext definition, IReadOnlyList<TypeAnalysisContext>? arguments)
    {
        var parameters = definition.GenericParameters;

        if (parameters.Count == 0)
            return EmptyMap;

        if (arguments == null || arguments.Count != parameters.Count)
            return null;

        var map = new Dictionary<string, TypeAnalysisContext>(parameters.Count, StringComparer.Ordinal);

        for (var index = 0; index < parameters.Count; index++)
            if (parameters[index].Name is { } name)
                map[name] = arguments[index];

        return map;
    }

    private static TypeAnalysisContext Substitute(TypeAnalysisContext fieldType, Dictionary<string, TypeAnalysisContext> map)
    {
        if (fieldType is GenericParameterTypeAnalysisContext parameter
            && parameter.Name is { } name
            && map.TryGetValue(name, out var actual))
            return actual;

        return fieldType;
    }

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize,
        Dictionary<string, TypeAnalysisContext> map, int depth)
    {
        if (depth > MaxNesting)
            return null;

        if (fieldType is PointerTypeAnalysisContext)
            return (pointerSize, pointerSize);

        if (fieldType is GenericParameterTypeAnalysisContext parameter)
            return parameter.Name is { } name && map.TryGetValue(name, out var actual)
                ? GetSizeAndAlignment(actual, pointerSize, map, depth + 1)
                : null;

        if (!fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize, map, depth + 1);

        switch (fieldType.FullName)
        {
            case "System.Boolean" or "System.Byte" or "System.SByte":
                return (1, 1);
            case "System.Int16" or "System.UInt16" or "System.Char":
                return (2, 2);
            case "System.Int32" or "System.UInt32" or "System.Single":
                return (4, 4);
            case "System.Int64" or "System.UInt64" or "System.Double":
                return (8, 8);
            case "System.IntPtr" or "System.UIntPtr":
                return (pointerSize, pointerSize);
        }

        // A user-defined value type: size is its fields laid out in order (no object header), padded
        // to its widest alignment. Explicit-layout structs would need their padding honoured and this
        // does not do that - if one shows up the self-check reports the mismatch.
        long size = 0;
        long widest = 1;

        foreach (var field in fieldType.Fields)
        {
            if (field.IsStatic)
                continue;

            if (GetSizeAndAlignment(Substitute(field.FieldType, map), pointerSize, map, depth + 1) is not var (innerSize, innerAlignment))
                return null;

            size = Align(size, innerAlignment) + innerSize;

            if (innerAlignment > widest)
                widest = innerAlignment;
        }

        return (Align(size, widest), widest);
    }

    private static long Align(long value, long alignment) => alignment <= 1 ? value : (value + alignment - 1) & ~(alignment - 1);

    /// <summary>
    /// Checks the layout arithmetic against metadata that actually carries offsets.
    ///
    /// A non-generic type's fields have real offsets, so asking this resolver to find the field at each
    /// of those offsets must give that field back. Any miss means the size/alignment/substitution rules
    /// are wrong, and the generic case must not be enabled until they are right - a wrong answer there
    /// puts a wrong field name into the output, which is worse than leaving the offset as arithmetic.
    /// </summary>
    public static void SelfCheck(ApplicationAnalysisContext appContext)
    {
        var ok = 0;
        var miss = 0;
        var skipped = 0;
        var failures = new List<string>();

        foreach (var assembly in appContext.Assemblies)
            foreach (var type in assembly.Types)
            {
                if (type.GenericParameters.Count > 0 || type.IsValueType || type.Fields.Count == 0)
                {
                    skipped++;
                    continue;
                }

                foreach (var field in type.Fields)
                {
                    if (field.IsStatic || field.Offset < 0)
                    {
                        skipped++;
                        continue;
                    }

                    var found = FindFieldAtOffset(type, field.Offset);

                    if (ReferenceEquals(found, field))
                    {
                        ok++;
                        continue;
                    }

                    miss++;

                    if (failures.Count < 12)
                        failures.Add($"{type.FullName}.{field.Name}@{field.Offset:X} -> {(found == null ? "null" : found.Name)}");
                }
            }

        System.Console.WriteLine($"[LayoutCheck] ok={ok} miss={miss} skipped={skipped}");

        foreach (var failure in failures)
            System.Console.WriteLine($"[LayoutCheck-fail] {failure}");
    }
}
