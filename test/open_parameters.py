"""Execute the real self-specification algorithms from parsed native SysML."""
import itertools
import json
from pathlib import Path
from emitted_model import Extent, Model, Parser, Record, same


def target_name(reference):
    return Parser(__import__('emitted_model').tokens(reference)).qualified().removeprefix('AgdaModel::')


def verify_open_parameters(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    roots = {}
    for source in ('Resolution.resolve', 'Foundation.orElse', 'Foundation._++_'):
        rows = [o for o in report['obligations'] if source + '#' in o['symbol']
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['rule'] == 'native.open-parameters' and rows[0]['target'], ('open algorithm not translated', source)
        roots[source] = target_name(rows[0]['target'])
    resolve, or_else, append = [roots[s] for s in ('Resolution.resolve', 'Foundation.orElse', 'Foundation._++_')]
    list_type = model.calculations[resolve][0][1][1]
    maybe_type = model.calculations[or_else][0][1][1]
    resolution_type = model.results[resolve]
    maybe_fields = model.carriers[maybe_type][1]
    resolution_fields = model.carriers[resolution_type][1]
    just_field = next(f for f, _, _, _ in maybe_fields if '.just<' in f)
    resolved_field = next(f for f, _, _, _ in resolution_fields if '.resolved<' in f)
    ambiguous_fields = [f for f, _, _, _ in resolution_fields if '.ambiguous<' in f]

    def constructor_tag(carrier, suffix):
        tag_type = next(typ for field, typ, _, _ in model.carriers[carrier][1] if field == 'constructor')
        constructors = model.carriers[tag_type][1]
        return tag_type + '::' + next(c for c in constructors if '.' + suffix + '<' in c)

    def listing(extent, values):
        return Record(list_type, (('typeArgument0', extent), ('items', tuple(values))))

    def optional(extent, payload=None):
        return Record(maybe_type, (('typeArgument0', extent),
                     ('constructor', constructor_tag(maybe_type, 'nothing' if payload is None else 'just')))
                     + (() if payload is None else ((just_field, payload),)))

    # The same emitted algorithms are used at each extent, without generated
    # concrete specializations. Include empty, infinite and opaque domains;
    # opaque values themselves contain nested records/sequences and repetitions.
    opaque = [Record('Opaque', (('id', n), ('nested', Record('Nested', (('items', (n, n)),))))) for n in range(3)]
    domains = [
        ((), []),
        ((False, True), [False, True]),
        (Extent('finite naturals', lambda x: type(x) is int and x >= 0), [0, 7, 10**40]),
        (tuple(opaque), opaque),
    ]
    comparisons = 0
    for extent, values in domains:
        lists = [tuple(xs) for n in range(4) for xs in itertools.product(values, repeat=n)]
        lists += [tuple(values[:1] * 20)] if values else []
        for xs in lists:
            actual = model.invoke(resolve, [extent, listing(extent, xs)])
            expected_tag = constructor_tag(resolution_type, 'missing' if not xs else 'resolved' if len(xs) == 1 else 'ambiguous')
            assert same(actual.get('constructor'), expected_tag), ('resolution branch', xs, actual)
            assert same(actual.get('typeArgument0'), extent), 'resolution changed type parameter'
            if len(xs) == 1:
                assert same(actual.get(resolved_field), xs[0]), 'resolution changed singleton payload'
            if len(xs) > 1:
                assert same(actual.get(ambiguous_fields[0]), xs[0]) and same(actual.get(ambiguous_fields[1]), xs[1]), 'resolution changed leading payloads'
                assert same(actual.get(ambiguous_fields[2]), listing(extent, xs[2:])), 'resolution changed tail/order/repetitions'
            comparisons += 1
        for xs, ys in itertools.product(lists[:14], repeat=2):
            actual = model.invoke(append, [extent, listing(extent, xs), listing(extent, ys)])
            assert same(actual, listing(extent, xs + ys)), ('append changed complete list', xs, ys, actual)
            comparisons += 1
        options = [optional(extent)] + [optional(extent, value) for value in values]
        for left, fallback in itertools.product(options, repeat=2):
            actual = model.invoke(or_else, [extent, left, fallback])
            expected = fallback if left.get('constructor') == constructor_tag(maybe_type, 'nothing') else left
            assert same(actual, expected), ('orElse changed full result', left, fallback, actual)
            comparisons += 1

    def rejected(action):
        try:
            action()
        except AssertionError:
            return
        raise AssertionError('invalid type-parameter binding was admitted')

    # Empty payloads still carry the parameter. Payload checks alone cannot
    # detect these mismatches. Reordered extents have the same interpretation.
    rejected(lambda: model.invoke(resolve, [(False,), listing((True,), ())]))
    rejected(lambda: model.invoke(resolve, [(), listing((), (True,))]))
    rejected(lambda: model.invoke(or_else, [(False, True), optional((False, True), 123), optional((False, True))]))
    rejected(lambda: model.invoke(append, [(True,), listing((True,), (True,)), listing((False,), ())]))
    model.invoke(resolve, [(False, True), listing((True, False), (True, False))])

    # The self specification's Root record has two parameters, one phantom.
    # Check parameter order and preservation without adding an Agda fixture.
    root_constructor = next(s for s in model.calculations
                            if s.endswith('Selection.root<type parameter 0, type parameter 1>'))
    root_inputs = model.calculations[root_constructor][0]
    kind_type = root_inputs[-1][1]
    kind_value = kind_type + '::' + model.carriers[kind_type][1][0]
    id_extent, metadata_extent = domains[2][0], domains[1][0]
    root = model.invoke(root_constructor, [id_extent, metadata_extent, 7, kind_value])
    assert same(root.get('typeArgument0'), id_extent) and same(root.get('typeArgument1'), metadata_extent), 'phantom/order parameter loss'
    rejected(lambda: model.invoke(root_constructor, [metadata_extent, id_extent, 7, kind_value]))

    # Mutate the actual parsed output: removing the input parameter contract
    # must be detected by the empty-list mismatch, even though the algorithm
    # then constructs an otherwise admissible result at the caller's extent.
    inputs, body, assertions = model.calculations[resolve]
    input_contracts = [a for a in assertions if "input0" in repr(a)]
    assert input_contracts, 'no parsed input parameter constraint'
    model.calculations[resolve] = (inputs, body, [a for a in assertions if a not in input_contracts])
    try:
        model.invoke(resolve, [(False,), listing((True,), ())])
    except AssertionError as error:
        raise AssertionError('mutation did not reach the missing input-contract boundary') from error
    model.calculations[resolve] = (inputs, body, assertions)
    return {'algorithms': list(roots), 'comparisons': comparisons, 'invalidBindingsRejected': 5,
            'mutationDetected': True, 'parsedCalculations': len(model.calculations),
            'infiniteExtent': True, 'phantomParameter': True, 'parameterOrder': True,
            'source': 'parsed emitted SysML'}


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_open_parameters(sys.argv[1]), indent=2))
