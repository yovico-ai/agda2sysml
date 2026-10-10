"""Evaluate supplied decision trees and ordered rules from parsed native SysML."""
import itertools
import json
from pathlib import Path
from emitted_model import BodyCalculation, CalculationValue, CallableSignature, Extent, Model, Record, same, sequence
from open_parameters import target_name


SOURCES = ('evaluate', 'evaluatePartial', 'select', 'withFallback', 'restrict', 'normalize')


def verify_callable_fields(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    roots = {}
    for source in SOURCES:
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.DecisionTree.' + source + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], source
        roots[source] = target_name(rows[0]['target'])
    additions = """
attribute def FieldInput {
  attribute key : ScalarValues::Natural [1];
  attribute payload : Base::Anything [1];
}
attribute def FieldOutcome {
  attribute source : Base::Anything [1];
  attribute stamp : ScalarValues::Natural [1];
}
calc def fieldBelow { in x : FieldInput [1]; return result : ScalarValues::Boolean [1] = x.key < 7; }
calc def fieldAbove { in x : FieldInput [1]; return result : ScalarValues::Boolean [1] = x.key > 7; }
calc def fieldAlways { in x : FieldInput [1]; return result : ScalarValues::Boolean [1] = true; }
calc def fieldNever { in x : FieldInput [1]; return result : ScalarValues::Boolean [1] = false; }
calc def fieldEcho { in x : FieldInput [1]; return result : Base::Anything [1] = x.payload; }
calc def fieldWrap { in x : FieldInput [1]; return result : FieldOutcome [1] = new FieldOutcome(source = x.payload, stamp = x.key); }
calc def fieldWrong { in x : FieldInput [1]; return result : ScalarValues::Natural [1] = x.key; }
calc def fieldBadOutput { in x : FieldInput [1]; return result : Base::Anything [1] = true; }
calc def fieldBadDomain { in x : ScalarValues::Natural [1]; return result : ScalarValues::Boolean [1] = x < 7; }
calc def fieldWrongArity { in x : FieldInput [1]; in y : FieldInput [1]; return result : ScalarValues::Boolean [1] = true; }
"""
    model = Model(text + additions)
    payloads = tuple(Record('CompleteOutcome', (('state', n), ('reason', reason),
                     ('history', (n, n, 10**40)), ('nested', Record('Evidence', (('id', n),)))))
                     for n, reason in itertools.product((0, 7, 10**40), ('accepted', 'refused')))
    samples = tuple(Record('FieldInput', (('key', n), ('payload', p)))
                    for n, p in itertools.product((0, 1, 7, 10**40), payloads))
    inputs = Extent('decision inputs', lambda x: isinstance(x, Record) and x.type == 'FieldInput')
    outputs = Extent('complete outcomes', lambda x: isinstance(x, Record) and x.type in ('CompleteOutcome', 'FieldOutcome'))
    bindings = {'typeArgument0': inputs, 'typeArgument1': outputs}
    comparisons = rejected = 0

    def call(symbol, *values):
        return model.invoke(symbol, [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                                     if f.startswith(('typeArgument', 'familyArgument'))], *values])

    def runtime_inputs(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def constructors(typ):
        shape = next(sh for sh in report['algebraicCarriers'] if target_name(sh['target']) == typ)
        return {c['symbol'].split('#', 1)[0].rsplit('.', 1)[-1]: target_name(c['target'])
                for c in shape['constructors']}

    tree_type = runtime_inputs(roots['evaluate'])[0][1]
    partial_type = runtime_inputs(roots['evaluatePartial'])[0][1]
    rules_type = runtime_inputs(roots['select'])[0][1]
    rule_type = next(t for f, t, _, _ in model.carriers[rules_type][1] if f == 'items')
    tree_constructors, partial_constructors = constructors(tree_type), constructors(partial_type)
    rule_constructor = constructors(rule_type)['rule']
    for typ in (tree_type, partial_type, rule_type):
        assert model.carriers[typ][0] == 'record'
        assert any(isinstance(t, CallableSignature) for _, t, _, _ in model.carriers[typ][1])

    def callback(name):
        return CalculationValue('field' + name)

    def tree(value, partial=False):
        tag, *args = value
        ctors = partial_constructors if partial else tree_constructors
        if tag == 'miss': return call(ctors[tag])
        if tag in ('leaf', 'yield'): return call(ctors[tag], callback(args[0]))
        return call(ctors[tag], callback(args[0]), tree(args[1], partial), tree(args[2], partial))

    def predicate(name, value):
        return {'Below': value.get('key') < 7, 'Above': value.get('key') > 7,
                'Always': True, 'Never': False}[name]

    def effect(name, value):
        return value.get('payload') if name == 'Echo' else Record('FieldOutcome', (('source', value.get('payload')), ('stamp', value.get('key'))))

    def expected(value, argument):
        tag, *args = value
        if tag == 'miss': return None
        if tag in ('leaf', 'yield'): return effect(args[0], argument)
        return expected(args[1] if predicate(args[0], argument) else args[2], argument)

    maybe_type = model.results[roots['evaluatePartial']]
    maybe_constructors = constructors(maybe_type)
    def maybe(value):
        return call(maybe_constructors['nothing']) if value is None else call(maybe_constructors['just'], value)

    def expect(actual, wanted):
        nonlocal comparisons
        assert same(actual, wanted), (actual, wanted)
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('invalid callable field admitted')

    leaves = [('leaf', e) for e in ('Echo', 'Wrap')]
    trees = leaves + [('branch', g, a, b) for g, a, b in itertools.product(('Below', 'Above', 'Always', 'Never'), leaves, leaves)]
    trees += [('branch', 'Below', trees[-2], ('branch', 'Above', trees[2], trees[3]))]
    partial_leaves = [('miss',), ('yield', 'Echo'), ('yield', 'Wrap')]
    partials = partial_leaves + [('test', g, a, b) for g, a, b in itertools.product(('Below', 'Above', 'Always', 'Never'), partial_leaves, partial_leaves)]
    partials += [('test', 'Below', partials[-2], ('test', 'Above', partials[3], partials[4]))]
    for source in trees:
        supplied = tree(source)
        for argument in samples:
            expect(call(roots['evaluate'], supplied, argument), expected(source, argument))
    for source in partials:
        supplied = tree(source, True)
        for argument in samples:
            wanted = expected(source, argument)
            expect(call(roots['evaluatePartial'], supplied, argument), maybe(wanted))
        for fallback in (trees[0], trees[1], trees[-1]):
            rebuilt = call(roots['withFallback'], supplied, tree(fallback))
            for argument in samples:
                wanted = expected(source, argument)
                expect(call(roots['evaluate'], rebuilt, argument),
                       expected(fallback, argument) if wanted is None else wanted)

    def rules(values):
        return Record(rules_type, (('typeArgument0', inputs), ('typeArgument1', outputs),
                      ('items', tuple(call(rule_constructor, callback(g), callback(e)) for g, e in values))))
    projections = {}
    for member in ('guard', 'effect'):
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.DecisionTree.Rule.' + member + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged'
        projections[member] = target_name(rows[0]['target'])
        assert isinstance(model.results[projections[member]], CallableSignature)
    for guard, result in itertools.product(('Below', 'Above', 'Always', 'Never'), ('Echo', 'Wrap')):
        supplied = call(rule_constructor, callback(guard), callback(result))
        projected_guard = call(projections['guard'], supplied)
        projected_effect = call(projections['effect'], supplied)
        for argument in samples:
            expect(model.invoke_callback(projected_guard, argument), predicate(guard, argument))
            expect(model.invoke_callback(projected_effect, argument), effect(result, argument))
    candidates = [('Never', 'Wrap'), ('Always', 'Echo'), ('Below', 'Wrap'), ('Above', 'Echo')]
    for length in range(4):
        for source in itertools.product(candidates, repeat=length):
            supplied = rules(source)
            for argument in samples:
                wanted = next((effect(e, argument) for g, e in source if predicate(g, argument)), None)
                expect(call(roots['select'], supplied, argument), maybe(wanted))

    laws = {}
    for source in ('restrict-true', 'restrict-false', 'normalization-preserves-evaluation', 'normalization-sound'):
        rows = [r for r in report['nativeStatements'] if r['status'] == 'translated'
                and r['symbol'].startswith('Agda2SysML.DecisionTree.' + source + '#') and '@' not in r['symbol']]
        assert len(rows) == 1, source
        laws[source] = target_name(rows[0]['target'])

    def evidence(law, value):
        typ = runtime_inputs(laws[law])[-1][1]
        return call(constructors(typ)['refl'], value)

    # Keep callbacks produced by distinct invocations alive together, then
    # invoke them after more normalizations/restrictions have run.
    retained = [(source, call(roots['normalize'], tree(source))) for source in trees]
    closure_comparisons = 0
    for source, normalized in reversed(retained):
        for argument in samples:
            wanted = expected(source, argument)
            expect(call(roots['select'], normalized, argument), maybe(wanted))
            expect(call(laws['normalization-preserves-evaluation'], tree(source), argument), True)
            expect(call(laws['normalization-sound'], tree(source), argument, wanted,
                        evidence('normalization-sound', maybe(wanted))), True)
            closure_comparisons += 3
    source = [('Below', 'Wrap'), ('Above', 'Echo'), ('Always', 'Wrap')]
    supplied = rules(source)
    restrictions = [(guard, call(roots['restrict'], callback(guard), supplied))
                    for guard in ('Below', 'Above', 'Always', 'Never')]
    for guard, restricted in reversed(restrictions):
        assert len(sequence(restricted.get('items'))) == len(source)
        for argument in samples:
            enabled = predicate(guard, argument)
            wanted = next((effect(e, argument) for g, e in source if enabled and predicate(g, argument)), None)
            expect(call(roots['select'], restricted, argument), maybe(wanted))
            law = 'restrict-true' if enabled else 'restrict-false'
            expect(call(laws[law], callback(guard), supplied, argument, evidence(law, enabled)), True)
            closure_comparisons += 2
        # Composition captures an already captured callback.
        repeated = call(roots['restrict'], callback('Above'), restricted)
        for argument in samples:
            wanted = next((effect(e, argument) for g, e in source
                           if predicate('Above', argument) and predicate(guard, argument) and predicate(g, argument)), None)
            expect(call(roots['select'], repeated, argument), maybe(wanted))
            closure_comparisons += 1

    # Mutate parsed lambda bodies, independently of compiler terms. Both
    # constants must change an observable selected outcome.
    def mutate(node, replacement):
        if not isinstance(node, (list, tuple)): return node
        if node and node[0] == 'body': return (*node[:3], ('literal', replacement))
        return type(node)(mutate(x, replacement) for x in node)
    mutations_detected = 0
    for replacement in (False, True):
        original = model.calculations[roots['restrict']]
        model.calculations[roots['restrict']] = (original[0], mutate(original[1], replacement), original[2])
        try:
            changed = call(roots['restrict'], callback('Below'), supplied)
            assert any(not same(call(roots['select'], changed, argument),
                                maybe(next((effect(e, argument) for g, e in source
                                            if predicate('Below', argument) and predicate(g, argument)), None)))
                       for argument in samples), 'captured-lambda mutation escaped behavior checks'
            mutations_detected += 1
        finally:
            model.calculations[roots['restrict']] = original

    for bad in (BodyCalculation((('x', 'ScalarValues::Natural'),), 'ScalarValues::Boolean', ('literal', True), {}),
                BodyCalculation((('x', 'Base::Anything'), ('y', 'Base::Anything')), 'ScalarValues::Boolean', ('literal', True), {})):
        refuse(lambda bad=bad: call(roots['select'], call(roots['restrict'], bad, supplied), samples[0]))
    refuse(lambda: call(laws['restrict-true'], callback('Never'), supplied, samples[0], evidence('restrict-true', True)))
    refuse(lambda: call(laws['normalization-sound'], tree(trees[0]), samples[0], payloads[-1],
                        evidence('normalization-sound', maybe(payloads[-1]))))

    # Invalid signatures, cardinalities, domains, results and parameter bindings
    # are checked at the generated boundaries, including reconstructed trees.
    for bad in (42, callback('Wrong'), callback('WrongArity')):
        refuse(lambda bad=bad: call(rule_constructor, bad, callback('Echo')))
    malformed = call(rule_constructor, callback('Always'), callback('Echo'))
    guard_field = next(f for f, t, _, _ in model.carriers[rule_type][1]
                       if isinstance(t, CallableSignature) and t.result == 'ScalarValues::Boolean')
    for bad in ((), (callback('Always'), callback('Never')), 42):
        changed = Record(rule_type, tuple((f, bad if f == guard_field else v) for f, v in malformed.fields))
        refuse(lambda changed=changed: model.boundary(rule_type, 1, 1, changed))
    supplied = call(rule_constructor, callback('BadDomain'), callback('Echo'))
    invalid_rules = Record(rules_type, (('typeArgument0', inputs), ('typeArgument1', outputs), ('items', (supplied,))))
    refuse(lambda: call(roots['select'], invalid_rules, samples[0]))
    invalid_leaf = call(tree_constructors['leaf'], callback('BadOutput'))
    refuse(lambda: call(roots['evaluate'], invalid_leaf, samples[0]))
    invalid_partial = call(partial_constructors['yield'], callback('BadOutput'))
    rebuilt = call(roots['withFallback'], invalid_partial, tree(leaves[0]))
    refuse(lambda: call(roots['evaluate'], rebuilt, samples[0]))
    refuse(lambda: call(roots['evaluate'], tree(leaves[0]), True))
    bindings = {'typeArgument0': (samples[0],), 'typeArgument1': outputs}
    refuse(lambda: call(roots['evaluate'], tree(leaves[0]), samples[-1]))
    return {'operations': len(SOURCES), 'comparisons': comparisons, 'invalidCasesRejected': rejected,
            'capturedLambdaComparisons': closure_comparisons, 'nativeStatements': len(laws),
            'lambdaMutationsDetected': mutations_detected}
