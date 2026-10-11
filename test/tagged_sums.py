"""Check complete tagged sums against independently assembled native values."""
from functools import lru_cache
import itertools
import json
from pathlib import Path
from emitted_model import Extent, Model, Record, same
from open_parameters import target_name


def verify_tagged_sums(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    prefix = 'Agda2SysML.AlgebraicValues.'
    roots = {}
    for operation in ('encode', 'decode', 'schemaAt', 'slotAt', 'sourceConstructor', 'nativeConstructor', 'tabulate'):
        rows = [o for o in report['obligations'] if o['symbol'].startswith(prefix + operation + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], ('sum operation missing', operation)
        roots[operation] = target_name(rows[0]['target'])

    uncached = model.invoke
    @lru_cache(maxsize=32768)
    def invoke(symbol, arguments, check, depth):
        return uncached(symbol, arguments, check, depth)
    model.invoke = lambda symbol, arguments, check=True, depth=0: invoke(symbol, tuple(arguments), check, depth)
    model.boundary = lru_cache(maxsize=32768)(model.boundary)

    def field(typ, suffix):
        matches = [(f, t) for f, t, _, _ in model.carriers[typ][1]
                   if f.endswith(suffix) or f.split('<', 1)[0].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def constructor(typ, source):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if c['symbol'].startswith(source + '#')]
        assert len(matches) == 1, (typ, source, matches)
        return matches[0]

    def replace(record, f, value):
        return Record(record.type, tuple((k, value if k == f else v) for k, v in record.fields))

    source_type = model.calculations[roots['encode']][0][-1][1]
    native_type = model.results[roots['encode']]
    schema_type = model.calculations[roots['encode']][0][-2][1]
    tag_field, tag_type = field(native_type, '.tag')
    slots_field, slots_type = field(native_type, '.slots')
    proof_field, proof_type = field(native_type, '.admissible')
    parameter_field, _ = field(native_type, '.parameter0')
    source_here = constructor(source_type, prefix + 'Sum.here')
    source_there = constructor(source_type, prefix + 'Sum.there')
    selected = constructor(tag_type, prefix + 'Tag.selected')
    later = constructor(tag_type, prefix + 'Tag.later')
    no_slots = constructor(slots_type, prefix + 'Slots.noSlots')
    slot = constructor(slots_type, prefix + 'Slots.slot')
    at_selected = constructor(proof_type, prefix + 'Active.at-selected')
    at_later = constructor(proof_type, prefix + 'Active.at-later')
    tagged = constructor(native_type, prefix + 'tagged')
    maybe_field, maybe_type = field(slots_type, '.payload2')
    nothing = constructor(maybe_type, 'Agda.Builtin.Maybe.Maybe.nothing')
    just = constructor(maybe_type, 'Agda.Builtin.Maybe.Maybe.just')
    fields_type = model.calculations[source_here][0][-1][1]
    native_fields_type = model.calculations[at_selected][0][-1][1]
    nil = constructor(fields_type, prefix + 'Fields.nil')
    cons = constructor(fields_type, prefix + 'Fields.cons')
    empty = constructor(native_fields_type, prefix + 'NativeFields.empty')
    entry = constructor(native_fields_type, prefix + 'NativeFields.entry')
    atom_schema_type = model.calculations[source_here][0][-3][1]
    member_type = model.calculations[cons][0][-2][1]
    row_type = next(t for f, t, _, _ in model.carriers[member_type][1] if f == 'familyArgument1')
    row_index, _ = field(row_type, '.index0')
    row_value, _ = field(row_type, '.value')
    member_index, _ = field(member_type, '.index0')
    member_value, _ = field(member_type, '.value')
    project = next(target_name(o['target']) for o in report['obligations']
                   if o['symbol'].startswith(prefix + 'nativeProject#') and '@' not in o['symbol']
                   and o['sourceKind'] == 'behavior' and o['status'] == 'discharged')
    position_type = model.calculations[project][0][-2][1]
    quote = lambda text: "'" + text.replace('\\', '\\\\').replace("'", "\\'") + "'"
    # A supplied native callback captures complete fields and reads them by
    # position. Tabulation must preserve repeated types and distinct values.
    tabulation_model = Model((output / 'model.sysml').read_text() + f'''
calc def tabulationRoundtrip {{
  in typeArgument0 : Base::Anything [0..*];
  in familyArgument1 : {quote(row_type)} [0..*];
  in schema : {quote(atom_schema_type)} [1];
  in fields : {quote(native_fields_type)} [1];
  return result : {quote(native_fields_type)} [1] = {quote(roots['tabulate'])}(
    typeArgument0, familyArgument1, schema,
    {{ in element : Base::Anything [1]; in position : {quote(position_type)} [1];
       return result : {quote(member_type)} [1];
       {quote(project)}(typeArgument0, familyArgument1, element, schema, position, fields) }});
}}
''')
    tabulation_comparisons = 0
    comparisons = rejected = repeated_schemas = 0
    construction_comparisons = lookup_comparisons = schema_refusals = 0

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('inconsistent tagged sum admitted')

    for atoms in ((False, True), (0, 7, 10**40)):
        extent = atoms if type(atoms[0]) is bool else Extent('natural atoms', lambda value: type(value) is int and value >= 0)
        payloads = {(atom, choice): Record('OpaquePayload', (('choice', choice),
                    ('detail', Record('Detail', (('atom', atom), ('history', (atom, atom, 10**40)))))))
                    for atom in atoms for choice in range(2)}
        relation = tuple(Record(row_type, ((row_index, atom), (row_value, payloads[atom, choice])))
                         for atom in atoms for choice in range(2))
        binding = {'typeArgument0': extent, 'familyArgument1': relation}

        def call(symbol, values):
            parameters = [binding[f] for f, _, _, _ in model.calculations[symbol][0] if f in binding]
            return model.invoke(symbol, [*parameters, *values])

        @lru_cache(maxsize=None)
        def atom_schema(layout):
            return Record(atom_schema_type, (('typeArgument0', extent), ('items', layout)))

        @lru_cache(maxsize=None)
        def schema(layouts):
            return Record(schema_type, (('typeArgument0', extent), ('items', tuple(atom_schema(x) for x in layouts))))

        @lru_cache(maxsize=None)
        def member(atom, choice):
            return Record(member_type, (('typeArgument0', extent), ('familyArgument1', relation),
                          (member_index, atom), (member_value, payloads[atom, choice])))

        @lru_cache(maxsize=None)
        def fields(layout, choices, native=False):
            if not layout:
                return call(empty if native else nil, [])
            return call(entry if native else cons, [layout[0], atom_schema(layout[1:]), member(layout[0], choices[0]),
                        fields(layout[1:], choices[1:], native)])

        for layout in ((), (atoms[0],), (atoms[0], atoms[0]), (atoms[0], atoms[-1], atoms[0])):
            for choices in itertools.product(range(2), repeat=len(layout)):
                supplied = fields(layout, choices, True)
                actual = tabulation_model.invoke('tabulationRoundtrip',
                    [extent, relation, atom_schema(layout), supplied])
                assert same(actual, supplied), 'tabulation lost a position, value, schema, or evidence field'
                tabulation_comparisons += 1

        @lru_cache(maxsize=None)
        def absent(layouts):
            if not layouts:
                return call(no_slots, [])
            return call(slot, [atom_schema(layouts[0]), schema(layouts[1:]),
                        call(nothing, [atom_schema(layouts[0])]), absent(layouts[1:])])

        @lru_cache(maxsize=None)
        def values(layouts, chosen, choices):
            first, rest = layouts[0], layouts[1:]
            head_schema, tail_schema = atom_schema(first), schema(rest)
            if chosen == 0:
                xs = fields(first, choices, True)
                source = call(source_here, [head_schema, tail_schema, fields(first, choices)])
                tag = call(selected, [head_schema, tail_schema])
                slots = call(slot, [head_schema, tail_schema, call(just, [head_schema, xs]), absent(rest)])
                proof = call(at_selected, [head_schema, tail_schema, xs])
            else:
                source_tail, _, tag_tail, slots_tail, proof_tail = values(rest, chosen - 1, choices)
                source = call(source_there, [head_schema, tail_schema, source_tail])
                tag = call(later, [head_schema, tail_schema, tag_tail])
                slots = call(slot, [head_schema, tail_schema, call(nothing, [head_schema]), slots_tail])
                proof = call(at_later, [head_schema, tail_schema, tag_tail, slots_tail, proof_tail])
            native = call(tagged, [schema(layouts), tag, slots, proof])
            return source, native, tag, slots, proof

        a, b = atoms[:2]
        layouts_to_check = (((),), ((), ()), ((a,), (a,)), ((a, a), (b,), ()),
                            ((), (b, a, b), (a, a), ()), ((a, b), (), (a, b), (), (b,)))
        for layouts in layouts_to_check:
            for chosen, layout in enumerate(layouts):
                for choices in itertools.product(range(2), repeat=len(layout)):
                    source, expected, tag, slots, _ = values(layouts, chosen, choices)
                    encoded = call(roots['encode'], [schema(layouts), source])
                    decoded = call(roots['decode'], [schema(layouts), expected])
                    assert same(encoded, expected), ('encoding changed complete tag, slots or evidence', layouts, chosen, choices)
                    assert same(decoded, source), ('decoding changed constructor or complete payload', layouts, chosen, choices)
                    comparisons += 2
                    repeated_schemas += int(layouts.count(layout) > 1)
                    source_payload = fields(layout, choices)
                    native_payload = fields(layout, choices, True)
                    assert same(call(roots['sourceConstructor'], [schema(layouts), tag, source_payload]), source)
                    assert same(call(roots['nativeConstructor'], [schema(layouts), tag, native_payload]), expected)
                    construction_comparisons += 2
                    for other, other_layout in enumerate(layouts):
                        # A tag depends only on position and schema, not the payload.
                        other_tag = values(layouts, other, (0,) * len(other_layout))[2]
                        assert same(call(roots['schemaAt'], [schema(layouts), other_tag]), atom_schema(other_layout))
                        expected_slot = (call(just, [atom_schema(layout), native_payload]) if other == chosen
                                         else call(nothing, [atom_schema(other_layout)]))
                        assert same(call(roots['slotAt'], [schema(layouts), other_tag, slots]), expected_slot)
                        lookup_comparisons += 2

        layouts = ((a,), (a,))
        source, first, first_tag, first_slots, first_proof = values(layouts, 0, (0,))
        _, second, second_tag, second_slots, second_proof = values(layouts, 1, (1,))
        inactive = call(nothing, [atom_schema((a,))])
        bad_slots = replace(first_slots, maybe_field, inactive)
        for value in (replace(first, tag_field, second_tag), replace(first, slots_field, second_slots),
                      replace(first, proof_field, second_proof), replace(first, slots_field, bad_slots),
                      replace(first, parameter_field, schema(((b,), (a,)))),
                      Record(first.type, tuple((k, v) for k, v in first.fields if k != proof_field))):
            refuse(lambda value=value: call(roots['decode'], [schema(layouts), value]))
        # A slot that should be inactive carries a complete second payload.
        tail_field, _ = field(slots_type, '.payload3')
        active_tail = values(layouts[1:], 0, (1,))[3]
        both_active = replace(first_slots, tail_field, active_tail)
        refuse(lambda: call(roots['decode'], [schema(layouts), replace(first, slots_field, both_active)]))
        refuse(lambda: call(roots['encode'], [schema(((b,), (a,))), source]))
        refuse(lambda: call(cons, [a, atom_schema(()), member(b, 0), fields((), ())]))

        before = rejected
        distinct_layouts = ((a,), (b,), ())
        _, _, chosen_tag, chosen_slots, _ = values(distinct_layouts, 0, (0,))
        for operation, native in (('sourceConstructor', False), ('nativeConstructor', True)):
            refuse(lambda operation=operation, native=native: call(roots[operation],
                [schema(distinct_layouts), chosen_tag, fields((b,), (0,), native)]))
            refuse(lambda operation=operation, native=native: call(roots[operation],
                [schema(distinct_layouts), chosen_tag, fields((), (), native)]))
            refuse(lambda operation=operation, native=native: call(roots[operation],
                [schema(((b,), (b,), ())), chosen_tag, fields((a,), (0,), native)]))
        refuse(lambda: call(roots['slotAt'], [schema(distinct_layouts), first_tag, chosen_slots]))
        refuse(lambda: call(roots['slotAt'], [schema(distinct_layouts), chosen_tag, first_slots]))
        refuse(lambda: call(roots['schemaAt'], [schema(((b,), (b,), ())), chosen_tag]))
        schema_refusals += rejected - before

    return {'operations': len(roots), 'comparisons': comparisons, 'invalidCasesRejected': rejected,
            'constructionComparisons': construction_comparisons, 'lookupComparisons': lookup_comparisons,
            'computedSchemaRefusals': schema_refusals,
            'tabulationComparisons': tabulation_comparisons,
            'repeatedConstructorSchemas': repeated_schemas, 'completePayloadsAndEvidencePreserved': True}


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_tagged_sums(sys.argv[1]), indent=2))
