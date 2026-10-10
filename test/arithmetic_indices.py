"""Execute captured-index and bounds operations from the emitted SysML.

The references construct complete vectors, ordinals, spans and order evidence;
they do not evaluate the compiler's internal representation.
"""
from functools import lru_cache
import itertools
import json
from pathlib import Path
from emitted_model import Model, Record, same
from open_parameters import target_name


def verify_arithmetic_indices(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    uncached = model.invoke

    @lru_cache(maxsize=16384)
    def cached(symbol, arguments, check, depth):
        return uncached(symbol, arguments, check, depth)
    model.invoke = lambda symbol, arguments, check=True, depth=0: cached(symbol, tuple(arguments), check, depth)

    def operation(name):
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.' + name + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], name
        return target_name(rows[0]['target'])

    names = ('CapturedIndices.append', 'CapturedIndices.captureSlot', 'CapturedIndices.runtimeSlot',
             'Derivations.shift-order', 'Derivations.Trace.shift-preserves-bounds',
             'RecursiveValues.left-bound', 'RecursiveValues.right-bound')
    roots = {name: operation(name) for name in names}
    laws = {}
    statement_names = {'capture-lookup': 'CapturedIndices.capture-lookup',
                       'runtime-lookup': 'CapturedIndices.runtime-lookup'}
    statement_names.update({name: name for name in ('Derivations.Trace.length-append',
        'NaturalValues.addition-preserves', 'NaturalValues.multiplication-preserves',
        'NaturalValues.subtraction-preserves', 'NaturalValues.equality-preserves',
        'NaturalValues.comparison-preserves')})
    for name, source in statement_names.items():
        rows = [r for r in report['nativeStatements']
                if r['symbol'].startswith('Agda2SysML.' + source + '#')]
        assert len(rows) == 1 and rows[0]['status'] == 'translated', name
        laws[name] = target_name(rows[0]['target'])
    comparisons = rejected = mutations = 0
    samples = {}

    def expect(symbol, arguments, expected):
        nonlocal comparisons
        assert same(model.invoke(symbol, arguments), expected), (symbol, arguments)
        samples[symbol] = (arguments, expected)
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('inconsistent arithmetic index or evidence admitted')

    def law(symbol, arguments):
        for (_, typ, low, high), value in zip(model.calculations[symbol][0], arguments):
            model.boundary(typ, low, high, value)
        expect(symbol, arguments, True)

    def bound_arguments(symbol, args, bindings):
        return [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                  if f.startswith('typeArgument')], *args]

    def constructor(typ, suffix, args, bindings=None):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return model.invoke(matches[0], args if bindings is None else bound_arguments(matches[0], args, bindings))

    prefix = 'Agda2SysML.BooleanLowering.'
    @lru_cache(maxsize=None)
    def fin(n, i):
        assert 0 <= i < n
        return model.invoke(prefix + 'Fin.first', [n-1]) if i == 0 else model.invoke(
            prefix + 'Fin.next', [n-1, fin(n-1, i-1)])

    @lru_cache(maxsize=None)
    def vec(extent, values):
        suffix = '<type parameter 0>'
        result = model.invoke(prefix + 'Vec.[]' + suffix, [extent])
        for n, value in enumerate(reversed(values)):
            result = model.invoke(prefix + 'Vec._∷_' + suffix, [extent, n, value, result])
        return result

    append = roots['CapturedIndices.append']
    captured_slot = roots['CapturedIndices.captureSlot']
    runtime_slot = roots['CapturedIndices.runtimeSlot']
    opaque = tuple(Record('OpaquePayload', (('id', n), ('history', (n, n)))) for n in (11, 10**40))
    different_sizes = 0
    for extent in ((False, True), opaque):
        for c, n in itertools.product(range(4), repeat=2):
            for left in itertools.product(extent, repeat=c):
                for right in itertools.product(extent, repeat=n):
                    xs, ys = vec(extent, left), vec(extent, right)
                    expect(append, [extent, c, n, xs, ys], vec(extent, left + right))
                    different_sizes += c != n
                    for i in range(c):
                        expect(captured_slot, [c, n, fin(c, i)], fin(c+n, i))
                        law(laws['capture-lookup'], [extent, c, n, xs, ys, fin(c, i)])
                    for i in range(n):
                        expect(runtime_slot, [c, n, fin(n, i)], fin(c+n, c+i))
                        law(laws['runtime-lookup'], [extent, c, n, xs, ys, fin(n, i)])

    huge = 10**40
    expect(captured_slot, [huge, huge+1, fin(huge, 0)], fin(2*huge+1, 0))
    expect(runtime_slot, [3, huge, fin(huge, 0)], fin(huge+3, 3))

    shift_order = roots['Derivations.shift-order']
    order_type = model.results[shift_order]
    @lru_cache(maxsize=None)
    def order(a, b):
        assert 0 <= a <= b
        if a == 0:
            return constructor(order_type, '.z≤n', [b])
        return constructor(order_type, '.s≤s', [a-1, b-1, order(a-1, b-1)])

    for offset in range(4):
        for a in range(4):
            for b in (a, a+1, a+3, 10**40):
                expect(shift_order, [offset, a, b, order(a, b)], order(offset+a, offset+b))

    shift_bounds = roots['Derivations.Trace.shift-preserves-bounds']
    bounds_type = model.results[shift_bounds]
    bound_inputs = model.calculations[shift_bounds][0]
    span_type = next(t for f, t, _, _ in bound_inputs if f == 'input2')
    extents = [(False, True), (), opaque, ()]

    def span(identity, start, end):
        return constructor(span_type, '.span', [*extents, identity, start, end])

    def within(limit, value, start, end):
        return constructor(bounds_type, '.within', [*extents, limit, value, order(start, end), order(end, limit)])

    for offset, start, width in itertools.product(range(3), repeat=3):
        end = start + width
        for limit in (end, end+2, 10**40):
            for identity in opaque:
                original = span(identity, start, end)
                evidence = within(limit, original, start, end)
                shifted = span(identity, offset+start, offset+end)
                expect(shift_bounds, [*extents, offset, limit, original, evidence],
                       within(offset+limit, shifted, offset+start, offset+end))

    bindings = {'typeArgument' + str(i): opaque for i in range(4)}
    recursive_order_type = model.results[roots['RecursiveValues.left-bound']]
    @lru_cache(maxsize=None)
    def recursive_order(a, b):
        assert 0 <= a <= b
        if a == 0:
            return constructor(recursive_order_type, '.zero-le', [b], bindings)
        return constructor(recursive_order_type, '.successor-le',
                           [a-1, b-1, recursive_order(a-1, b-1)], bindings)
    for a, b in itertools.product(range(5), repeat=2):
        for name, lower in (('RecursiveValues.left-bound', a), ('RecursiveValues.right-bound', b)):
            expect(roots[name], bound_arguments(roots[name], [a, b], bindings), recursive_order(lower, a+b))

    values = (0, 1, 2, 7, 10**40, 10**40+1, 2**128, 2**128+1)
    for name, symbol in laws.items():
        if name.startswith('NaturalValues.'):
            for a, b in itertools.product(values, repeat=2):
                law(symbol, [a, b])

    length_law = laws['Derivations.Trace.length-append']
    list_types = [typ for field, typ, _, _ in model.calculations[length_law][0] if field.startswith('input')]
    def list_value(typ, values):
        return Record(typ, tuple((field, bindings[field]) for field, _, _, _ in model.carriers[typ][1]
                                 if field.startswith('typeArgument')) + (('items', values),))
    lists = [values for size in range(4) for values in itertools.product(opaque, repeat=size)]
    for left, right in itertools.product(lists, repeat=2):
        law(length_law, bound_arguments(length_law,
            [list_value(list_types[0], left), list_value(list_types[1], right)], bindings))

    extent = opaque
    xs, ys = vec(extent, (opaque[0],)), vec(extent, (opaque[1], opaque[0]))
    refuse(lambda: model.invoke(append, [extent, 0, 2, xs, ys]))
    refuse(lambda: model.invoke(append, [extent, 1, 1, xs, ys]))
    refuse(lambda: model.invoke(append, [extent, -1, 2, xs, ys]))
    refuse(lambda: model.invoke(append, [extent, 1, float('inf'), xs, ys]))
    refuse(lambda: model.invoke(captured_slot, [1, 2, fin(2, 1)]))
    refuse(lambda: model.invoke(runtime_slot, [2, 1, fin(2, 1)]))
    refuse(lambda: law(laws['capture-lookup'], [extent, 1, 2, xs, ys, fin(2, 1)]))
    refuse(lambda: law(laws['runtime-lookup'], [extent, 1, 2, xs, ys, fin(1, 0)]))
    refuse(lambda: model.invoke(shift_order, [2, 1, 2, order(0, 2)]))
    refuse(lambda: model.invoke(shift_order, [2, 1, 2, order(1, 3)]))
    original = span(opaque[0], 1, 2)
    evidence = within(3, original, 1, 2)
    refuse(lambda: model.invoke(shift_bounds, [*extents, 2, 4, original, evidence]))
    refuse(lambda: model.invoke(shift_bounds, [*extents, 2, 3, span(opaque[1], 1, 2), evidence]))

    # Every newly claimed operation/law must be exercised by a check that
    # detects replacing its body, independently of its input contracts.
    assert samples.keys() == set(roots.values()) | set(laws.values())
    for symbol, (arguments, expected) in samples.items():
        inputs, body, assertions = model.calculations[symbol]
        cached.cache_clear()
        model.calculations[symbol] = inputs, ('literal', False), assertions
        try:
            try:
                actual = model.invoke(symbol, arguments)
            except AssertionError:
                actual = None
            assert not same(actual, expected), ('body mutation escaped', symbol)
            mutations += 1
        finally:
            model.calculations[symbol] = inputs, body, assertions
            cached.cache_clear()
    return dict(operations=len(roots), statements=len(laws), comparisons=comparisons,
                invalidCasesRejected=rejected, bodyMutationsDetected=mutations,
                differentContextSizes=different_sizes, completeEvidencePreserved=True,
                source='parsed emitted SysML')


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_arithmetic_indices(sys.argv[1]), indent=2))
