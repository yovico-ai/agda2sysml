"""Compare the actual compiler-core algorithms parsed from emitted SysML.

The reference implements the source constructor equations, including arbitrary
substitutions with different source and target context sizes. No compiler IR is
used to execute the target.
"""
from functools import lru_cache
import itertools
import json
from pathlib import Path
from emitted_model import Model, Record, same
from open_parameters import target_name


def verify_recursive_core(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    # Immutable native values and pure calculations allow reuse of successful
    # validations. Clear the cache before every constraint mutation.
    uncached_invoke = model.invoke
    @lru_cache(maxsize=16384)
    def cached_invoke(symbol, arguments, check, depth):
        return uncached_invoke(symbol, arguments, check, depth)
    model.invoke = lambda symbol, arguments, check=True, depth=0: cached_invoke(symbol, tuple(arguments), check, depth)
    prefix = 'Agda2SysML.BooleanLowering.'
    roots = {}
    for name in ('lookup', 'remove', 'source', 'target', 'lower'):
        rows = [o for o in report['obligations'] if o['symbol'].startswith(prefix + name + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['target'] and rows[0]['status'] == 'discharged', ('core operation missing', name, rows)
        roots[name] = target_name(rows[0]['target'])

    def calc(name, suffix=''):
        found = [s for s in model.calculations if s == prefix + name + suffix]
        assert len(found) == 1, ('missing native calculation', name, suffix)
        return found[0]

    def call(name, values, suffix=''):
        return model.invoke(calc(name, suffix), values)

    boolean = '<Agda.Builtin.Bool.Bool>'
    open_type = '<type parameter 0>'
    expr_vectors = [s for s in model.calculations if s.startswith(prefix + 'Vec.[]<') and 'Expr' in s]
    assert len(expr_vectors) == 1, ('dependent vector schema is not shared', expr_vectors)
    dependent = expr_vectors[0].removeprefix(prefix + 'Vec.[]')

    @lru_cache(maxsize=None)
    def fin(n, i):
        assert 0 <= i < n
        return call('Fin.first', [n - 1]) if i == 0 else call('Fin.next', [n - 1, fin(n - 1, i - 1)])

    @lru_cache(maxsize=None)
    def vec(values, suffix=boolean, captured=()):
        result = call('Vec.[]', list(captured), suffix)
        for n, value in enumerate(reversed(values)):
            result = call('Vec._∷_', [*captured, n, value, result], suffix)
        return result

    @lru_cache(maxsize=None)
    def source_value(n, tree):
        tag, *args = tree
        if tag == 'value': return call('Cases.value', [n, args[0]])
        if tag == 'read': return call('Cases.read-var', [n, fin(n, args[0])])
        i, yes, no = args
        return call('Cases.split', [n - 1, fin(n, i), source_value(n - 1, yes), source_value(n - 1, no)])

    @lru_cache(maxsize=None)
    def expr_value(m, expression):
        tag, *args = expression
        if tag == 'literal': return call('Expr.literal', [m, args[0]])
        if tag == 'input': return call('Expr.input', [m, fin(m, args[0])])
        return call('Expr.conditional', [m, *(expr_value(m, x) for x in args)])

    def source(tree, env):
        tag, *args = tree
        if tag == 'value': return args[0]
        if tag == 'read': return env[args[0]]
        i, yes, no = args
        return source(yes if env[i] else no, env[:i] + env[i+1:])

    def target(expression, env):
        tag, *args = expression
        if tag == 'literal': return args[0]
        if tag == 'input': return env[args[0]]
        test, yes, no = args
        return target(yes if target(test, env) else no, env)

    def lower(tree, bindings):
        tag, *args = tree
        if tag == 'value': return ('literal', args[0])
        if tag == 'read': return bindings[args[0]]
        i, yes, no = args
        rest = bindings[:i] + bindings[i+1:]
        return ('conditional', bindings[i], lower(yes, rest), lower(no, rest))

    def trees(n):
        basic = [('value', False), ('value', True)] + [('read', i) for i in range(n)]
        if n:
            branches = trees(n - 1)
            basic += [('split', i, yes, no) for i in range(n) for yes, no in itertools.product(branches[:5], repeat=2)]
            # Include nested deletion at every position, not only the head.
            basic += [('split', i, branches[-1], branches[-2]) for i in range(n)]
        return basic

    def expressions(m):
        basic = [('literal', False), ('literal', True)] + [('input', i) for i in range(m)]
        return basic + [('conditional', test, basic[-1], basic[0]) for test in basic]

    comparisons = dict(lookup=0, remove=0, source=0, target=0, lower=0, preservation=0)
    for n in range(1, 5):
        for values in itertools.product((False, True), repeat=n):
            native = vec(values)
            for i in range(n):
                assert same(call('lookup', [n, fin(n, i), native], boolean), values[i])
                comparisons['lookup'] += 1
                assert same(call('remove', [n - 1, fin(n, i), native], boolean), vec(values[:i] + values[i+1:]))
                comparisons['remove'] += 1
    # The open schema must retain opaque payloads and repeated ordered values.
    extent = (Record('Opaque', (('id', 7),)), Record('Opaque', (('id', 11),)))
    for n in range(1, 4):
        for values in itertools.product(extent, repeat=n):
            native = vec(values, open_type, (extent,))
            for i in range(n):
                assert same(model.invoke(roots['lookup'], [extent, n, fin(n, i), native]), values[i])
                comparisons['lookup'] += 1
                assert same(model.invoke(roots['remove'], [extent, n - 1, fin(n, i), native]), vec(values[:i] + values[i+1:], open_type, (extent,)))
                comparisons['remove'] += 1
    for n in range(4):
        for tree in trees(n):
            native_tree = source_value(n, tree)
            for env in itertools.product((False, True), repeat=n):
                assert same(model.invoke(roots['source'], [n, native_tree, vec(env)]), source(tree, env))
                comparisons['source'] += 1
        for expression in expressions(n):
            native_expression = expr_value(n, expression)
            for env in itertools.product((False, True), repeat=n):
                assert same(model.invoke(roots['target'], [n, native_expression, vec(env)]), target(expression, env))
                comparisons['target'] += 1
    unequal_sizes = 0
    for n, m in itertools.product(range(4), repeat=2):
        terms = expressions(m)
        bindings_set = [tuple(terms[(i + shift) % len(terms)] for i in range(n)) for shift in range(len(terms))]
        for tree in trees(n):
            native_tree = source_value(n, tree)
            for bindings in bindings_set:
                expected = lower(tree, bindings)
                result = model.invoke(roots['lower'], [n, m, native_tree, vec(tuple(expr_value(m, t) for t in bindings), dependent, (m,))])
                assert same(result, expr_value(m, expected)), ('complete lower result differs', n, m, tree, bindings)
                comparisons['lower'] += 1
                unequal_sizes += n != m
                for env in itertools.product((False, True), repeat=m):
                    assert same(model.invoke(roots['target'], [m, result, vec(env)]), source(tree, tuple(target(t, env) for t in bindings)))
                    comparisons['preservation'] += 1

    rejected = 0
    def refuse(action):
        nonlocal rejected
        try: action()
        except AssertionError: rejected += 1; return
        raise AssertionError('invalid recursive value or index was admitted')

    def changed(value, field, replacement):
        return Record(value.type, tuple((key, replacement if key == field else item) for key, item in value.fields))

    f = fin(2, 1)
    v = vec((False, True))
    refuse(lambda: call('lookup', [1, f, v], boolean))
    refuse(lambda: call('remove', [0, f, v], boolean))
    refuse(lambda: call('Fin.next', [0, fin(1, 0)]))
    refuse(lambda: call('Vec._∷_', [0, True, v], boolean))
    for value in (f, v, source_value(2, ('read', 1)), expr_value(2, ('input', 1))):
        count_field = next(key for key, _ in value.fields if key.endswith('.node-count'))
        refuse(lambda value=value, count_field=count_field: model.boundary(value.type, 1, 1, changed(value, count_field, 0)))
    refuse(lambda: model.invoke(roots['lower'], [0, 2, source_value(0, ('value', True)), vec((), dependent, (1,))]))
    refuse(lambda: call('Vec._∷_', [2, 0, expr_value(1, ('literal', True)), vec((), dependent, (2,))], dependent))
    # Removing an emitted captured-index contract must change acceptance. This
    # empty vector has no payload whose type could mask a missing binding check.
    inputs, body, assertions = model.calculations[roots['lower']]
    vector_contracts = [a for a in assertions if 'input3' in repr(a)]
    assert vector_contracts, 'no parsed dependent vector input contract'
    cached_invoke.cache_clear()
    model.calculations[roots['lower']] = inputs, body, [a for a in assertions if a not in vector_contracts]
    model.invoke(roots['lower'], [0, 2, source_value(0, ('value', True)), vec((), dependent, (1,))])
    model.calculations[roots['lower']] = inputs, body, assertions
    assert unequal_sizes > 0
    return {'algorithms': list(roots), 'comparisons': comparisons, 'totalComparisons': sum(comparisons.values()),
            'differentContextSizeComparisons': unequal_sizes, 'invalidCasesRejected': rejected,
            'capturedIndexMutationDetected': True, 'opaquePayloads': True,
            'source': 'parsed emitted SysML'}


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_recursive_core(sys.argv[1]), indent=2))
