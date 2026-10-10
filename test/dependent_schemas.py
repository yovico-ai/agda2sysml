"""Check captured schema domains through unchanged relation-spec operations."""
import json
from functools import lru_cache
from pathlib import Path
from emitted_model import BoundCalculation, CalculationValue, Model, Record, same
from open_parameters import target_name


def verify_dependent_schemas(output):
    boolean = _verify(output, (False, True), ('false', 'true'))
    states = tuple(Record('DependentState', (('code', code),)) for code in (17, 10**30))
    structured = _verify(output, states,
        tuple('new DependentState(code = ' + str(dict(state.fields)['code']) + ')' for state in states),
        'attribute def DependentState { attribute code : ScalarValues::Natural [1]; }\n')
    result = dict(boolean)
    for key in ('comparisons', 'invalidCasesRejected', 'bodyMutationsDetected'):
        result[key] += structured[key]
    result['structuredStates'] = True
    return result


def _verify(output, states, state_expressions, state_prelude=''):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    names = ('RelationRule.Witness', 'RelationRule.before', 'RelationRule.after',
             'RelationRule.premises', 'Edge.Parameter', 'Edge.constraint',
             'EndpointConditions.admitted')

    def target(source, role='behavior'):
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.Relations.' + source + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == role]
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], source
        return target_name(rows[0]['target'])

    roots = {name: target(name) for name in names}
    bindings = {'typeArgument0': states}
    source_state, target_state = states
    comparisons = rejections = mutations = 0

    def fields(typ):
        return [(f, t) for f, t, _, _ in model.carriers[typ][1]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def record(typ, values):
        parameters = [(f, bindings[f]) for f, _, _, _ in model.carriers[typ][1]
                      if f.startswith(('typeArgument', 'familyArgument'))]
        assert len(fields(typ)) == len(values), (typ, fields(typ), values)
        return Record(typ, (*parameters, *zip((f for f, _ in fields(typ)), values)))

    def call(symbol, *args):
        parameters = [bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                      if f.startswith(('typeArgument', 'familyArgument'))]
        return model.invoke(symbol, [*parameters, *args])

    def expect(actual, expected):
        nonlocal comparisons
        while isinstance(actual, BoundCalculation) and isinstance(expected, CalculationValue):
            actual = actual.value
        assert same(actual, expected), (actual, expected)
        comparisons += 1

    def refuse(action):
        nonlocal rejections
        try:
            action()
        except AssertionError:
            rejections += 1
            return
        raise AssertionError('invalid captured schema admitted')

    rule_type = target('RelationRule', 'structure')
    witness_type, before_sig, after_sig, premise_type = [t for _, t in fields(rule_type)]
    witness_member_type = before_sig.argument
    witness_row_type = dict(fields(witness_type))['items']
    witnesses = tuple(record(witness_row_type, [i]) for i in (17, 23))
    witness = record(witness_type, [witnesses])
    other = record(witness_type, [(record(witness_row_type, [42]),)])
    members = [record(witness_member_type, [witness, i]) for i in (17, 23)]
    premise_row_type = dict(fields(premise_type))['items']
    # Equal witness payloads remain distinct from their schema identity.
    evidence = tuple(Record('DependentEvidence', (('steps', (i, i, 10**30)),)) for i in (1, 2))
    rows = [record(premise_row_type, [witness, witness, member, proof])
            for member, proof in zip(members, evidence)]
    premises = record(premise_type, [witness, tuple(rows)])

    def quote(name):
        return "'" + name.replace('\\', '\\\\').replace("'", "\\'") + "'"

    prelude = state_prelude + 'attribute def DependentEvidence { attribute steps : ScalarValues::Natural [0..*] ordered nonunique; }\n' + '\n'.join(
        'calc def ' + quote(name) + ' { in a : ' + quote(sig.argument)
        + ' [1]; return result : Base::Anything [1] = ' + value + '; }'
        for name, sig, value in [('dependentBefore', before_sig, state_expressions[0]),
                                 ('dependentAfter', after_sig, state_expressions[1])])
    model = Model(text + '\n' + prelude)
    invoke = model.invoke
    @lru_cache(maxsize=16384)
    def cached_invoke(symbol, arguments, check, depth):
        return invoke(symbol, arguments, check, depth)
    model.invoke = lambda symbol, arguments, check=True, depth=0: cached_invoke(symbol, tuple(arguments), check, depth)
    before, after = CalculationValue('dependentBefore'), CalculationValue('dependentAfter')
    rule = record(rule_type, [witness, before, after, premises])
    for name, expected in zip(names[:4], [witness, before, after, premises]):
        expect(call(roots[name], rule), expected)
    reordered = record(witness_type, [witnesses[::-1]])
    expect(call(roots['RelationRule.premises'], record(rule_type, [reordered, before, after, premises])), premises)
    empty = record(premise_type, [witness, ()])
    expect(call(roots['RelationRule.premises'], record(rule_type, [witness, before, after, empty])), empty)
    refuse(lambda: call(roots['RelationRule.premises'], record(rule_type,
        [witness, before, after, record(premise_type, [other, ()])])))
    for member in members:
        for position, expected in [(1, source_state), (2, target_state)]:
            bound = model.evaluate(('project', ('literal', rule), fields(rule_type)[position][0]), {})
            expect(model.invoke_callback_many(bound, [member]), expected)
            foreign = record(witness_member_type, [other, 42])
            refuse(lambda: model.invoke_callback_many(bound, [foreign]))
    refuse(lambda: call(roots['RelationRule.premises'], record(rule_type, [other, before, after, premises])))
    bad_row = record(premise_row_type, [witness, other, members[0], evidence[0]])
    refuse(lambda: model.boundary(premise_type, 1, 1, record(premise_type, [witness, (bad_row,)]), 0))
    bad_row = record(premise_row_type, [other, other, record(witness_member_type, [other, 42]), evidence[0]])
    refuse(lambda: model.boundary(premise_type, 1, 1, record(premise_type, [witness, (bad_row,)]), 0))
    bad_row = record(premise_row_type, [witness, witness, record(witness_member_type, [other, 42]), evidence[0]])
    refuse(lambda: model.boundary(premise_type, 1, 1, record(premise_type, [witness, (bad_row,)]), 0))

    edge_type = target('Edge', 'structure')
    constraint_type = fields(edge_type)[1][1]
    constraint_row_type = dict(fields(constraint_type))['items']
    constraint_rows = [record(constraint_row_type, [witness, witness, source_state, target_state, member, proof])
                       for member, proof in zip(members, evidence)]
    constraints = record(constraint_type, [witness, tuple(constraint_rows)])
    edge = record(edge_type, [witness, constraints])
    expect(call(roots['Edge.Parameter'], edge), witness)
    expect(call(roots['Edge.constraint'], edge), constraints)
    refuse(lambda: call(roots['Edge.constraint'], record(edge_type, [other, constraints])))

    conditions_ctor = target('conditions', 'structure')
    runtime = [t for f, t, _, _ in model.calculations[conditions_ctor][0]
               if not f.startswith(('typeArgument', 'familyArgument'))]
    source_eq, target_eq, premise_member_type = runtime[-3:]

    def constructor(typ):
        return next(target_name(c['target']) for sh in report['algebraicCarriers']
                    if target_name(sh['target']) == typ for c in sh['constructors'])

    left, right = call(constructor(source_eq), source_state), call(constructor(target_eq), target_state)
    cases = []
    computed_rows = []
    condition_values = []
    admissions = []
    for member, proof in zip(members, evidence):
        admission = record(premise_member_type, [witness, premises, member, proof])
        conditions = call(conditions_ctor, rule, source_state, target_state, member, left, right, admission)
        condition_values.append(conditions)
        admissions.append(admission)
        computed_rows.append(record(constraint_row_type, [witness, witness, source_state, target_state, member, conditions]))
        expect(call(roots['EndpointConditions.admitted'], conditions), admission)
        refuse(lambda: call(conditions_ctor, rule, target_state, source_state, member, left, right, admission))
        wrong = record(premise_member_type, [other, premises, member, proof])
        refuse(lambda: model.boundary(premise_member_type, 1, 1, wrong, 0))
        wrong = record(premise_member_type, [witness, premises, member, evidence[1] if proof == evidence[0] else evidence[0]])
        refuse(lambda: model.boundary(premise_member_type, 1, 1, wrong, 0))
        cases.append((roots['EndpointConditions.admitted'], conditions, admission, wrong))
    computed_constraint = record(constraint_type, [witness, tuple(computed_rows)])
    computed_edge = record(edge_type, [witness, computed_constraint])
    emit_rule = target('emitRule')
    actual_edge = call(emit_rule, rule)
    assert model.equal(actual_edge, computed_edge), 'computed schema changed its complete endpoint witnesses'
    comparisons += 1
    cases.append((emit_rule, rule, computed_edge, edge))
    emit = target('emit')
    source_list = model.calculations[emit][0][-1][1]
    for rules in [(), (rule,), (rule, rule), (rule, record(rule_type, [witness, before, after, empty]), rule)]:
        source = record(source_list, [rules])
        actual = call(emit, source)
        expected = record(actual.type, [tuple(call(emit_rule, value) for value in rules)])
        assert model.equal(actual, expected), 'emit changed the ordered rule list or repeated positions'
        comparisons += 1
    cases.append((emit, source, expected, record(actual.type, [()])))
    complete, sound = target('relation-complete'), target('relation-sound')
    permitted, first, later = [target(name, 'structure') for name in
                                ('Permits.permitted', 'Related.first', 'Related.later')]
    here, there = [target(name, 'structure') for name in ('Connected.here', 'Connected.there')]
    membership_type = model.calculations[here][0][-1][1]
    edge_list = actual.type
    empty_rule = record(rule_type, [witness, before, after, empty])
    empty_edge = call(emit_rule, empty_rule)
    for prefix in [(), (rule,), (empty_rule,), (rule, empty_rule)]:
        for suffix in [(), (rule,)]:
            for member, conditions, admission in zip(members, condition_values, admissions):
                rules = (*prefix, rule, *suffix)
                tail_rules = record(source_list, [suffix])
                tail_edges = record(edge_list, [tuple(computed_edge for _ in suffix)])
                permit = call(permitted, rule, source_state, target_state, member, left, right, admission)
                related = call(first, rule, tail_rules, source_state, target_state, permit)
                membership = record(membership_type, [witness, computed_constraint, source_state, target_state, member, conditions])
                connected = call(here, computed_edge, tail_edges, source_state, target_state, member, membership)
                current_rules = (rule, *suffix)
                current_edges = tuple(computed_edge for _ in current_rules)
                for preceding in reversed(prefix):
                    preceding_edge = empty_edge if preceding == empty_rule else computed_edge
                    related = call(later, preceding, record(source_list, [current_rules]), source_state, target_state, related)
                    connected = call(there, preceding_edge, record(edge_list, [current_edges]),
                                     source_state, target_state, connected)
                    current_rules = (preceding, *current_rules)
                    current_edges = (preceding_edge, *current_edges)
                source_rules = record(source_list, [rules])
                assert model.equal(call(complete, source_rules, source_state, target_state, related), connected)
                assert model.equal(call(sound, source_rules, source_state, target_state, connected), related)
                comparisons += 2
                refuse(lambda: call(complete, source_rules, target_state, source_state, related))
                refuse(lambda: call(sound, source_rules, target_state, source_state, connected))
                wrong_rules = record(source_list, [tuple(empty_rule for _ in rules)])
                refuse(lambda: call(complete, wrong_rules, source_state, target_state, related))
                refuse(lambda: call(sound, wrong_rules, source_state, target_state, connected))
                if len(prefix) == 2 and suffix and member == members[-1]:
                    cases.append((complete, (source_rules, source_state, target_state, related), connected, related))
                    cases.append((sound, (source_rules, source_state, target_state, connected), related, connected))
    cases += [(roots[name], rule, expected, replacement)
              for name, expected, replacement in zip(names[:4], [witness, before, after, premises], [other, after, before, ()])]
    cases += [(roots['Edge.Parameter'], edge, witness, other), (roots['Edge.constraint'], edge, constraints, ())]
    for symbol, arg, expected, replacement in cases:
        inputs, body, assertions = model.calculations[symbol]
        cached_invoke.cache_clear()
        model.calculations[symbol] = (inputs, ('literal', replacement), assertions)
        try:
            try:
                actual = call(symbol, *(arg if isinstance(arg, tuple) else (arg,)))
            except AssertionError:
                actual = None
            while isinstance(actual, BoundCalculation) and isinstance(expected, CalculationValue):
                actual = actual.value
            assert not same(actual, expected), 'body mutation escaped detection'
            mutations += 1
        finally:
            model.calculations[symbol] = (inputs, body, assertions)
            cached_invoke.cache_clear()
    return dict(operations=len(names)+4, comparisons=comparisons, invalidCasesRejected=rejections,
                bodyMutationsDetected=mutations, capturedDomains=True, completeEvidencePreserved=True)
