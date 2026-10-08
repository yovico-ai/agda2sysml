"""Execute ordered dependent fields and positions from the emitted SysML.

The reference builds complete native results independently of the translated
algorithm. Equal atoms at different positions retain distinct member payloads.
"""
from functools import lru_cache
import itertools
import json
from pathlib import Path
from emitted_model import Extent, Model, Record, same
from open_parameters import target_name


def verify_structured_indices(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    prefix = 'Agda2SysML.AlgebraicValues.'
    suffix = '<type parameter 0, type family 1>'
    roots = {}
    for operation in ('encodeFields', 'decodeFields', 'project', 'nativeProject', 'append', 'nativeAppend'):
        rows = [o for o in report['obligations'] if o['symbol'].startswith(prefix + operation + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], ('field operation missing', operation)
        roots[operation] = target_name(rows[0]['target'])

    uncached = model.invoke
    @lru_cache(maxsize=32768)
    def invoke(symbol, arguments, check, depth):
        return uncached(symbol, arguments, check, depth)
    model.invoke = lambda symbol, arguments, check=True, depth=0: invoke(symbol, tuple(arguments), check, depth)
    # Native values and this model are immutable throughout the comparisons.
    # Validate a repeated complete value once per carrier and recursion depth.
    boundary = model.boundary
    model.boundary = lru_cache(maxsize=32768)(boundary)

    def call(operation, values, binding):
        return model.invoke(prefix + operation + suffix, [*binding, *values])

    member_type = model.results[roots['project']]
    member_fields = model.carriers[member_type][1]
    row_type = next(t for f, t, _, _ in member_fields if f == 'familyArgument1')
    row_fields = model.carriers[row_type][1]
    row_index = next(f for f, _, _, _ in row_fields if f.endswith('.index0'))
    row_payload = next(f for f, _, _, _ in row_fields if f.endswith('.value'))
    member_index = next(f for f, _, _, _ in member_fields if f.endswith('.index0'))
    member_payload = next(f for f, _, _, _ in member_fields if f.endswith('.value'))
    schema_type = model.calculations[roots['encodeFields']][0][-2][1]
    comparisons = repeated_positions = rejected = binding_cases = append_comparisons = 0

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('inconsistent ordered schema was admitted')

    for atoms in ((False, True), (0, 7, 10**40)):
        extent = (atoms if type(atoms[0]) is bool else
                  Extent('all natural atoms', lambda value: type(value) is int and value >= 0))
        # Proof-relevant, nested payloads distinguish repeated atoms and cannot
        # be replaced by booleans or numbers without changing a full result.
        payloads = {(atom, choice): Record('OpaqueMember', (('choice', choice),
                    ('nested', Record('OpaqueDetail', (('atom', atom), ('repeated', (atom, atom)))))))
                    for atom in atoms for choice in range(2)}
        relation = tuple(Record(row_type, ((row_index, atom), (row_payload, payloads[atom, choice])))
                         for atom in atoms for choice in range(2))
        binding = (extent, relation)

        @lru_cache(maxsize=None)
        def schema(atoms):
            return Record(schema_type, (('typeArgument0', extent), ('items', atoms)))

        @lru_cache(maxsize=None)
        def member(atom, choice):
            return Record(member_type, (('typeArgument0', extent), ('familyArgument1', relation),
                          (member_index, atom), (member_payload, payloads[atom, choice])))

        @lru_cache(maxsize=None)
        def fields(layout, choices, native=False):
            if not layout:
                return call('NativeFields.empty' if native else 'Fields.nil', [], binding)
            atom, *tail = layout
            return call('NativeFields.entry' if native else 'Fields.cons',
                        [atom, schema(tuple(tail)), member(atom, choices[0]),
                         fields(tuple(tail), choices[1:], native)], binding)

        @lru_cache(maxsize=None)
        def position(layout, ordinal):
            atom = layout[ordinal]
            if ordinal == 0:
                return call('Position.first', [atom, schema(layout[1:])], binding)
            return call('Position.next', [atom, layout[0], schema(layout[1:]),
                        position(layout[1:], ordinal - 1)], binding)

        for length in range(5):
            for layout in itertools.product(atoms, repeat=length):
                for choices in itertools.product(range(2), repeat=length):
                    source = fields(layout, choices)
                    expected = fields(layout, choices, True)
                    encoded = model.invoke(roots['encodeFields'], [*binding, schema(layout), source])
                    decoded = model.invoke(roots['decodeFields'], [*binding, schema(layout), expected])
                    assert same(encoded, expected) and same(decoded, source), ('complete field transport changed', layout, choices)
                    comparisons += 2
                    for ordinal, atom in enumerate(layout):
                        args = [*binding, atom, schema(layout), position(layout, ordinal)]
                        reference = member(atom, choices[ordinal])
                        assert same(model.invoke(roots['project'], [*args, source]), reference)
                        assert same(model.invoke(roots['nativeProject'], [*args, expected]), reference)
                        comparisons += 2
                        repeated_positions += int(layout.count(atom) > 1)

        inputs = [(layout, choices) for length in range(3)
                  for layout in itertools.product(atoms, repeat=length)
                  for choices in itertools.product(range(2), repeat=length)]
        for (left, left_choices), (right, right_choices) in itertools.product(inputs, repeat=2):
            layout, choices = left + right, left_choices + right_choices
            appended = model.invoke(roots['append'], [*binding, schema(left), schema(right),
                                    fields(left, left_choices), fields(right, right_choices)])
            native = model.invoke(roots['nativeAppend'], [*binding, schema(left), schema(right),
                                  fields(left, left_choices, True), fields(right, right_choices, True)])
            assert same(appended, fields(layout, choices)), ('source append lost/reordered members', left, right)
            assert same(native, fields(layout, choices, True)), ('native append lost/reordered members', left, right)
            assert same(model.invoke(roots['encodeFields'], [*binding, schema(layout), appended]), native)
            assert same(model.invoke(roots['decodeFields'], [*binding, schema(layout), native]), appended)
            append_comparisons += 4

        a, b = atoms[:2]
        source = fields((a, b, a), (0, 1, 1))
        refuse(lambda: model.invoke(roots['encodeFields'], [*binding, schema((b, a, a)), source]))
        refuse(lambda: model.invoke(roots['encodeFields'], [*binding, schema((a, b)), source]))
        refuse(lambda: call('Fields.cons', [a, schema(()), member(b, 0), fields((), ())], binding))
        refuse(lambda: call('Fields.cons', [a, schema((a,)), member(a, 0), fields((b,), (0,))], binding))
        refuse(lambda: model.invoke(roots['project'], [*binding, b, schema((a, b, a)), position((a, b, a), 2), source]))
        refuse(lambda: model.invoke(roots['project'], [*binding, a, schema((a, b, a)), position((a,), 0), source]))
        refuse(lambda: model.invoke(roots['append'], [*binding, schema((b, a, a)), schema(()), source, fields((), ())]))
        refuse(lambda: model.invoke(roots['nativeAppend'], [*binding, schema(()), schema((b, a, a)),
                      fields((), (), True), fields((a, b, a), (0, 1, 1), True)]))

    opaque_atoms = (Record('OpaqueAtom', (('id', 0),)), Record('OpaqueAtom', (('id', 1),)))
    for stored, supplied in (((True, False), (False, True)),
                             ((10**40, 7, 0), (0, 7, 10**40)),
                             (opaque_atoms[::-1], opaque_atoms)):
        source = call('Fields.nil', [], (stored, ()))
        source_type = model.results[prefix + 'Fields.nil' + suffix]
        layout = source.get(source_type + '.index0')
        encoded = model.invoke(roots['encodeFields'], [supplied, (), layout, source])
        assert same(encoded, call('NativeFields.empty', [], (supplied, ())))
        decoded = model.invoke(roots['decodeFields'], [supplied, (), layout, encoded])
        assert same(decoded, call('Fields.nil', [], (supplied, ())))
        binding_cases += 1

    source = call('Fields.nil', [], ((False,), ()))
    layout = source.get(model.results[prefix + 'Fields.nil' + suffix] + '.index0')
    refuse(lambda: model.invoke(roots['encodeFields'], [(False, True), (), layout, source]))

    return {'operations': 6, 'comparisons': comparisons, 'appendComparisons': append_comparisons,
            'repeatedPositions': repeated_positions,
            'invalidSchemasRejected': rejected, 'completeMembersPreserved': True,
            'reorderedBindings': binding_cases,
            'source': 'parsed emitted SysML'}


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_structured_indices(sys.argv[1]), indent=2))
