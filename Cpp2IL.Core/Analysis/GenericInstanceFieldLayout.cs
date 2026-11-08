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
    /// The extended layout walk is behind a switch, default off.
    ///
    /// It measures 97.75% correct against real metadata, and that is not enough: the part that is
    /// wrong returns a *wrong* field rather than none, which types a load as the wrong member and
    /// costs the whole method its clean recovery - enabling it took clean from 27430 to 27142.
    /// Default off keeps that from happening; turn it on once the self-check reaches 100%.
    /// </summary>
    /// <summary>Why the most recent <see cref="FindFieldAtOffset"/> returned null. Diagnostics only.</summary>
    [ThreadStatic] public static string? LastMissReason;

    private static readonly bool UseExtendedLayout = Environment.GetEnvironmentVariable("CPP2IL_GENERIC_LAYOUT") == "1";

    /// <summary>
    /// The original, conservative walk: only when no base class has fields, and only when every field
    /// type has a known size. This is what runs by default.
    /// </summary>
    private static FieldAnalysisContext? FindFieldAtOffsetLegacy(TypeAnalysisContext definition, long targetOffset)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        for (var baseType = definition.BaseType; baseType != null; baseType = baseType.BaseType)
            if (baseType.Fields.Any(f => !f.IsStatic))
                return null;

        var offset = 2L * pointerSize;

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic)
                continue;

            if (GetSizeAndAlignment(field.FieldType, pointerSize, EmptyMap, 0) is not var (size, alignment))
                return null;

            offset = Align(offset, alignment);

            if (offset == targetOffset)
                return field;

            offset += size;
        }

        return null;
    }

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
        IReadOnlyList<TypeAnalysisContext>? arguments = null, bool forceExtended = false)
    {
        // Two callers want different things from this. ResolveFieldOffsets (a memory read through a
        // reference-typed field) has always used the conservative walk and works; switching it to the
        // extended one costs 305 clean recoveries. The value-type address rewrite has no other way to
        // name anything at all, and with it B1 drops. So the switch stays off globally and is forced on
        // for that caller alone.
        if (!forceExtended && !UseExtendedLayout)
            return FindFieldAtOffsetLegacy(definition, targetOffset);

        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        if (BuildSubstitution(definition, arguments) is not { } substitution)
        {
            LastMissReason = "definition-substitution";
            return null;
        }

        var chain = new List<(TypeAnalysisContext Type, Dictionary<string, TypeAnalysisContext> Map)>();

        for (var type = definition; type != null; type = type.BaseType)
        {
            if (type == definition)
            {
                chain.Insert(0, (type, substitution));
                continue;
            }

            // A base class is frequently a *closed* generic instance (`Task<int>`, `Tweener<int,int,…>`).
            // Its arguments are on itself, not in the `arguments` list handed to this call - that list
            // describes the definition we started from, and is empty when it is not generic at all.
            if (type is GenericInstanceTypeAnalysisContext baseInstance)
            {
                if (BuildSubstitution(baseInstance.GenericType, baseInstance.GenericArguments) is not { } baseMap)
                {
                    LastMissReason = "closed-base-substitution:" + baseInstance.FullName;
                    return null;
                }

                chain.Insert(0, (baseInstance.GenericType, baseMap));
                continue;
            }

            // An open base (`class A<T> : B<T>`): the arguments flow through by name.
            if (BuildSubstitution(type, arguments) is not { } baseSubstitution)
            {
                LastMissReason = "open-base-substitution:" + type.FullName;
                return null;
            }

            chain.Insert(0, (type, baseSubstitution));
        }

        var offset = 2L * pointerSize;

        foreach (var (type, map) in chain)
            foreach (var field in type.Fields)
            {
                if (field.IsStatic)
                    continue;

                if (GetSizeAndAlignment(Substitute(field.FieldType, map), pointerSize, map, 0) is not var (size, alignment))
                {
                    LastMissReason = "unknown-size:" + field.FieldType.FullName;
                    return null;
                }

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

        // An unmapped type parameter measures as a pointer, matching the original conservative rule -
        // returning null here instead silently cost 87 clean recoveries on the default path.
        if (fieldType is GenericParameterTypeAnalysisContext parameter)
            return parameter.Name is { } name && map.TryGetValue(name, out var actual)
                ? GetSizeAndAlignment(actual, pointerSize, map, depth + 1)
                : (pointerSize, pointerSize);

        if (!fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize, map, depth + 1);

        // Nullable<T> is refused wholesale: the indirect check reads it as 12 bytes for int and 24 for
        // decimal, while this computes 8 and 20. Both plausible repairs (widen the field alignment, or
        // widen the struct alignment) fix it and break NativeArray<T> in the same step, so the shape is
        // not understood well enough to model - refusing it is the honest answer, and the check records
        // how many observations that costs (42).
        if (fieldType.FullName.StartsWith("System.Nullable`1", StringComparison.Ordinal))
            return null;


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

        // A non-generic value type reports real offsets for its own fields; a generic instance reports 0
        // for every one of them. Where the real offsets exist, use them: an explicit-layout union
        // overlaps its members, so laying them out in sequence overstates the size. ValidationState
        // showed exactly that - StateUnion measured 16 bytes instead of 4, which put HasMatched 12 bytes
        // too far and mistyped every field after it.
        if (fieldType is not GenericInstanceTypeAnalysisContext && fieldType.Fields.Any(f => !f.IsStatic && f.Offset >= 0))
        {
            long endOffset = 0;
            long widestKnown = 1;

            foreach (var field in fieldType.Fields)
            {
                if (field.IsStatic)
                    continue;

                if (GetSizeAndAlignment(Substitute(field.FieldType, map), pointerSize, map, depth + 1) is not var (knownSize, knownAlignment))
                    return null;

                if (field.Offset + knownSize > endOffset)
                    endOffset = field.Offset + knownSize;

                if (knownAlignment > widestKnown)
                    widestKnown = knownAlignment;
            }

            return (Align(endOffset, widestKnown), widestKnown);
        }

        // A user-defined value type: size is its fields laid out in order (no object header), padded
        // to its widest alignment. Explicit-layout structs would need their padding honoured and this
        // does not do that - if one shows up the self-check reports the mismatch.
        //
        // A generic instance carries no fields of its own - they live on the definition, with the
        // arguments substituted. Getting that right is what makes Nullable<bool> measure 2 bytes
        // instead of 0; at 0 every field laid out after it lands 8 bytes early.
        var fieldsOwner = fieldType;
        var fieldsMap = map;

        // IL2CPP lays the fields of a *generic* struct out against the pointer width, not against each
        // field's natural alignment. Measured on Nullable<int>: it occupies 12 bytes (hasValue at 0, then
        // 7 bytes of padding, then value at 8), where natural alignment would give 5 rounded to 8. That
        // 12 is read straight off a non-generic struct that embeds it, so it is not a guess.
        var minimumFieldAlignment = 1L;

        if (fieldType is GenericInstanceTypeAnalysisContext genericInstance)
        {
            if (BuildSubstitution(genericInstance.GenericType, genericInstance.GenericArguments) is not { } instanceMap)
                return null;

            fieldsOwner = genericInstance.GenericType;
            fieldsMap = instanceMap;
            minimumFieldAlignment = 1;   // measured: widening this to the pointer size breaks NativeArray<T> (24 vs 16)
        }

        long size = 0;
        long widest = 1;

        foreach (var field in fieldsOwner.Fields)
        {
            if (field.IsStatic)
                continue;

            if (GetSizeAndAlignment(Substitute(field.FieldType, fieldsMap), pointerSize, fieldsMap, depth + 1) is not var (innerSize, innerAlignment))
                return null;

            // Offsets use the widened alignment; the struct's own alignment for the trailing padding
            // stays natural. Without that split Nullable<int> comes out 16 instead of 12 - the value
            // lands correctly at 8, then rounding the total up to 8 overshoots.
            var fieldAlignment = Math.Max(innerAlignment, minimumFieldAlignment);

            size = Align(size, fieldAlignment) + innerSize;

            if (innerAlignment > widest)
                widest = innerAlignment;
        }

        return (Align(size, widest), widest);
    }

    /// <summary>
    /// Validates generic instance sizes against **indirect** ground truth.
    ///
    /// The previous check only graded non-generic types, because only they carry real offsets - and it
    /// turned out to be a placebo: going from 95.4% to 98.86% moved clean by nothing, since what the
    /// extended layout changes is generic instances. This checks the thing that actually matters.
    ///
    /// The trick is that a generic instance's size can leak into a non-generic type's offsets: when a
    /// non-generic value type embeds a generic value-type field, the gap to the next field *is* that
    /// instance's size. `Nullable<bool>` sits in such a slot in several BCL structs, so its 2 bytes can
    /// be confirmed instead of assumed.
    /// </summary>
    public static void SelfCheckGenericSizes(ApplicationAnalysisContext appContext)
    {
        var pointerSize = appContext.Binary.PointerSizeBytes;
        var ok = 0;
        var miss = 0;
        var skipped = 0;
        var failures = new List<string>();

        foreach (var assembly in appContext.Assemblies)
            foreach (var type in assembly.Types)
            {
                if (type.GenericParameters.Count > 0 || !type.IsValueType)
                    continue;

                var fields = type.Fields
                    .Where(f => !f.IsStatic && f.Offset >= 0)
                    .OrderBy(f => f.Offset)
                    .ToList();

                for (var index = 0; index + 1 < fields.Count; index++)
                {
                    if (fields[index].FieldType is not GenericInstanceTypeAnalysisContext)
                        continue;

                    var observed = fields[index + 1].Offset - fields[index].Offset;

                    if (observed <= 0)
                        continue;

                    if (GetSizeAndAlignment(fields[index].FieldType, pointerSize, EmptyMap, 0) is not var (measured, _))
                    {
                        skipped++;
                        continue;
                    }

                    if (measured == observed)
                    {
                        ok++;
                        continue;
                    }

                    miss++;

                    if (failures.Count < 12)
                        failures.Add($"{type.FullName}.{fields[index].Name} expected={observed} mine={measured} ({fields[index].FieldType.FullName})");
                }
            }

        System.Console.WriteLine($"[GenericSizeCheck] ok={ok} miss={miss} skipped={skipped}");

        foreach (var failure in failures)
            System.Console.WriteLine($"[GenericSizeCheck-fail] {failure}");
    }

    private static long Align(long value, long alignment) => alignment <= 1 ? value : (value + alignment - 1) & ~(alignment - 1);

    /// <summary>
    /// Diagnostic (<c>CPP2IL_FIELD_TYPES=&lt;type-substring&gt;</c>): prints each field with its metadata
    /// offset and what the sizer decides about it, next to what the sizer computed. This is how a
    /// self-check miss gets attributed to a specific field type instead of guessed at.
    /// </summary>
    public static void ProbeFieldTypes(ApplicationAnalysisContext appContext, string filter)
    {
        var pointerSize = appContext.Binary.PointerSizeBytes;

        foreach (var assembly in appContext.Assemblies)
            foreach (var type in assembly.Types)
            {
                if (!type.FullName.Contains(filter, StringComparison.Ordinal))
                    continue;

                System.Console.WriteLine($"[field-types] {type.FullName} base={(type.BaseType == null ? "-" : type.BaseType.FullName)} value={type.IsValueType}");

                var offset = 2L * pointerSize;

                foreach (var field in type.Fields)
                {
                    if (field.IsStatic)
                        continue;

                    var fieldType = field.FieldType;
                    var measured = GetSizeAndAlignment(fieldType, pointerSize, EmptyMap, 0);
                    var ownText = measured is { } m ? $"size={m.Size} align={m.Alignment} mine=0x{Align(offset, m.Alignment):X}" : "size=?";

                    // Only the disagreements: a correct run is a long list of matching numbers, and the
                    // question is always "which field first goes wrong".
                    var agrees = measured is { } mm && Align(offset, mm.Alignment) == field.Offset;

                    if (!agrees)
                        System.Console.WriteLine($"[field-types-miss]\t{field.Name}\tmeta=0x{field.Offset:X}\t{fieldType.FullName}\tvalue={fieldType.IsValueType}\t{fieldType.GetType().Name}\t{ownText}");

                    if (measured is { } m2)
                        offset = Align(offset, m2.Alignment) + m2.Size;
                }
            }
    }

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
        var wrongFailures = new List<string>();
        var reasons = new Dictionary<string, int>(StringComparer.Ordinal);
        var wrongField = 0;

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

                    LastMissReason = null;
                    var found = FindFieldAtOffset(type, field.Offset);

                    if (ReferenceEquals(found, field))
                    {
                        ok++;
                        continue;
                    }

                    miss++;

                    // A wrong field is worse than no field: it types a load as the wrong member. Keep
                    // the two apart so the count that matters is visible on its own.
                    var reason = found != null ? "wrong-field" : LastMissReason ?? "not-on-chain";

                    if (found != null)
                        wrongField++;

                    reasons[reason] = reasons.TryGetValue(reason, out var seen) ? seen + 1 : 1;

                    // Wrong-field samples are worth more than null ones: null means "no answer", which
                    // is safe, while a wrong field silently mistypes the member.
                    if (found != null && wrongFailures.Count < 10)
                        wrongFailures.Add($"{type.FullName}.{field.Name}@{field.Offset:X} -> {found.Name}@{found.Offset:X}");
                    else if (found == null && failures.Count < 6)
                        failures.Add($"{type.FullName}.{field.Name}@{field.Offset:X} -> null [{reason}]");
                }
            }

        System.Console.WriteLine($"[LayoutCheck] ok={ok} miss={miss} skipped={skipped} wrong={wrongField}");

        foreach (var (reason, count) in reasons.OrderByDescending(pair => pair.Value))
            System.Console.WriteLine($"[LayoutCheck-reason] {count}\t{reason}");

        foreach (var failure in wrongFailures)
            System.Console.WriteLine($"[LayoutCheck-wrong] {failure}");

        foreach (var failure in failures)
            System.Console.WriteLine($"[LayoutCheck-fail] {failure}");
    }
}
