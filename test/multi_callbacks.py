"""Execute existing multiargument operations from parsed emitted SysML."""
import itertools
import json
from pathlib import Path
from emitted_model import CalculationValue, CallableSignature, Model, Record, same
from open_parameters import target_name


def verify_multi_callbacks(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    names = ('ComputedIndices.replace', 'ComputedIndices.replaceArgs',
             'DependencyScope.evaluate', 'DependencyScope.evaluateArgs',
             'Derivations.Trace.combine', 'SequenceValues.caseList', 'SequenceValues.caseSequence')
    roots = {}
    for name in names:
        rows = [o for o in report['obligations'] if 'Agda2SysML.' + name + '#' in o['symbol']
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], name
        roots[name] = target_name(rows[0]['target'])

    def parameters(symbol):
        return [f for f, _, _, _ in model.calculations[symbol][0]
                if f.startswith(('typeArgument', 'familyArgument'))]

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0] if f not in parameters(symbol)]

    def constructor(typ, suffix=None):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if suffix is None or c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def field(typ, suffix):
        matches = [f for f, _, _, _ in model.carriers[typ][1]
                   if f.split('#', 1)[0].endswith(suffix) or f.split('<', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def call(symbol, bindings, *values):
        return model.invoke(symbol, [*[bindings[f] for f in parameters(symbol)], *values])

    def make(typ, suffix, bindings, *values):
        return call(constructor(typ, suffix), bindings, *values)

    def listing(typ, bindings, values):
        return Record(typ, (*((f, bindings[f]) for f, _, _, _ in model.carriers[typ][1]
                             if f.startswith(('typeArgument', 'familyArgument'))), ('items', tuple(values))))

    def quote(value):
        return "'" + value.replace('\\', '\\\\').replace("'", "\\'") + "'"

    additions = ['attribute def MultiPayload { attribute id : ScalarValues::Natural; '
                 'attribute nested : ScalarValues::Natural [0..*] ordered nonunique; }']
    def callback(name, domains, result, expression):
        additions.append('calc def ' + quote(name) + ' { ' + ''.join(
            f'in a{i} : {quote(t)} [1]; ' for i, t in enumerate(domains))
            + f'return result : {quote(result)} [1] = {expression}; }}')
        return CalculationValue(name)

    def literal(value):
        if isinstance(value, Record):
            return 'new ' + quote(value.type) + '(' + ', '.join(quote(k) + ' = ' + literal(v) for k, v in value.fields) + ')'
        if isinstance(value, tuple):
            if not value: return 'null'
            elements = [literal(v) for v in value]
            return '(' + ', '.join(elements + (['null'] if len(elements) == 1 else [])) + ')'
        if isinstance(value, bool): return 'true' if value else 'false'
        if isinstance(value, int): return str(value)
        if isinstance(value, str) and '::' in value: return '::'.join(map(quote, value.rsplit('::', 1)))
        raise AssertionError(('unsupported test literal', value))

    def refresh():
        nonlocal model
        model = Model(text + '\n' + '\n'.join(additions))

    comparisons = rejected = mutations = 0
    def expect(actual, expected):
        nonlocal comparisons
        assert same(actual, expected), ('changed complete result', comparisons)
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        try: action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('invalid multiargument callback binding admitted')

    def mutate(symbol, bindings, values, wrong, expected):
        nonlocal mutations
        inputs, body, assertions = model.calculations[symbol]
        model.calculations[symbol] = (inputs, ('literal', wrong), assertions)
        try:
            assert not same(call(symbol, bindings, *values), expected), 'body mutation escaped the reference result'
            mutations += 1
        finally:
            model.calculations[symbol] = (inputs, body, assertions)

    payloads = tuple(Record('MultiPayload', (('id', n), ('nested', (n, n, 1000000)))) for n in range(4))
    # The two callback arguments have different domains. Both influence calls.
    evaluate, evaluate_args = (roots['DependencyScope.' + n] for n in ('evaluate', 'evaluateArgs'))
    signature, term_type = [t for _, t in runtime(evaluate)]
    args_type = runtime(evaluate_args)[-1][1]
    list_type = signature.arguments[1]
    table = callback('multiTable', signature.arguments, signature.result,
                     'if a0 ? SequenceFunctions::head(a1.items) else '
                     'SequenceFunctions::head(SequenceFunctions::tail(a1.items))')
    wrong_arity = callback('multiUnary', ('Base::Anything',), 'Base::Anything', 'a0')
    refresh()
    bindings = {'typeArgument0': (False, True), 'typeArgument1': payloads}
    def args_value(trees):
        return make(args_type, '.none', bindings) if not trees else make(
            args_type, '.next', bindings, expression(trees[0]), args_value(trees[1:]))
    def expression(tree):
        if tree[0] == 'literal': return make(term_type, '.literal', bindings, payloads[tree[1]])
        return make(term_type, '.call', bindings, tree[1], args_value(tree[2]))
    def interpret(tree):
        return payloads[tree[1]] if tree[0] == 'literal' else interpret(tree[2][0 if tree[1] else 1])
    trees = [('literal', i) for i in range(4)]
    trees += [('call', b, (x, y)) for b, x, y in itertools.product((False, True), trees[:3], trees[1:])]
    trees += [('call', False, (trees[0], trees[-1]))]
    for tree in trees:
        expect(call(evaluate, bindings, table, expression(tree)), interpret(tree))
    for group in ((), tuple(trees[:3]), tuple(trees[-4:]), tuple(trees[::3])):
        expect(call(evaluate_args, bindings, table, args_value(group)), listing(list_type, bindings, map(interpret, group)))
    refuse(lambda: call(evaluate, bindings, wrong_arity, expression(trees[0])))
    refuse(lambda: call(evaluate, {**bindings, 'typeArgument1': payloads[:1]}, table, expression(trees[1])))
    mutate(evaluate, bindings, (table, expression(trees[0])), payloads[1], payloads[0])
    mutate(evaluate_args, bindings, (table, args_value(trees[:2])), listing(list_type, bindings, payloads[1::-1]), listing(list_type, bindings, payloads[:2]))

    # Ordered branch callbacks receive the head and the complete tail.
    for name in ('caseList', 'caseSequence'):
        symbol = roots['SequenceValues.' + name]
        _, branch, sequence_type = [t for _, t in runtime(symbol)]
        sequence_value = lambda bindings, values: listing(sequence_type, bindings, values)
        tail = 'a1.items'
        if name == 'caseSequence':
            def support(name):
                row = next(o for o in report['obligations'] if 'Agda2SysML.SequenceValues.' + name + '#' in o['symbol']
                           and '@' not in o['symbol'] and o['sourceKind'] == 'behavior')
                return target_name(row['target'])
            encode, decode = support('encode'), support('decode')
            source_list = runtime(encode)[0][1]
            sequence_value = lambda bindings, values: call(encode, bindings, listing(source_list, bindings, values))
            tail = quote(decode) + '(' + ', '.join('a1.' + quote(p) for p in parameters(decode)) + ', a1).items'
        selected = callback('multi' + name, branch.arguments, branch.result,
                            'if SequenceFunctions::isEmpty(' + tail + ') ? a0 else SequenceFunctions::head(' + tail + ')')
        refresh()
        params = {p: payloads for p in parameters(symbol)}
        for size in range(4):
            for values in itertools.product(payloads[:3], repeat=size):
                expected = payloads[3] if not values else values[0] if len(values) == 1 else values[1]
                expect(call(symbol, params, payloads[3], selected, sequence_value(params, values)), expected)
        refuse(lambda: call(symbol, params, payloads[3], wrong_arity, sequence_value(params, payloads[:2])))
        bad_result = callback('bad' + name, branch.arguments, branch.result, '999')
        refresh()
        refuse(lambda: call(symbol, params, payloads[3], bad_result, sequence_value(params, payloads[:2])))
        mutate(symbol, params, (payloads[3], selected, sequence_value(params, payloads[:2])), payloads[0], payloads[1])

    # Combine retains both complete origin lists and the callback's full value.
    combine = roots['Derivations.Trace.combine']
    sig, left_type, right_type = [t for _, t in runtime(combine)]
    result_type = model.results[combine]
    params = {p: payloads for p in parameters(combine)}
    params['typeArgument4'], params['typeArgument5'] = payloads[:2], payloads[2:]
    origin_list = next(t for f, t, _, _ in model.carriers[left_type][1] if f == field(left_type, '.origins'))
    origin_type = next(t for f, t, _, _ in model.carriers[origin_list][1] if f == 'items')
    origins = [make(origin_type, '.checked', params, payloads[0]), make(origin_type, '.generated', params, payloads[1])]
    for ordinal in (0, 1):
        selected = callback('multiCombine' + str(ordinal), sig.arguments, sig.result, 'a' + str(ordinal))
        refresh()
        for a, b, left_origins, right_origins in itertools.product(payloads[:2], payloads[2:],
                ((), (origins[0],), tuple(origins)), ((), (origins[1],), tuple(reversed(origins)))):
            left = make(left_type, None, params, listing(origin_list, params, left_origins), a)
            right = make(right_type, None, params, listing(origin_list, params, right_origins), b)
            expected = make(result_type, None, params, listing(origin_list, params, left_origins + right_origins), (a, b)[ordinal])
            expect(call(combine, params, selected, left, right), expected)
        refuse(lambda: call(combine, params, wrong_arity, left, right))
    wrong = make(result_type, None, params, listing(origin_list, params, left_origins), b)
    mutate(combine, params, (selected, left, right), wrong, expected)

    # Substitution's second argument and result depend on its first argument.
    replace, replace_args = (roots['ComputedIndices.' + n] for n in ('replace', 'replaceArgs'))
    signatures_type, schema_type, _, _, substitution, expr_type = [t for _, t in runtime(replace)]
    position_type = substitution.arguments[1]
    args_type = runtime(replace_args)[-1][1]
    member_type = runtime(constructor(expr_type, '.literal'))[-1][1]
    row_type = next(t for f, t, _, _ in model.carriers[member_type][1] if f == 'familyArgument1')
    relation = tuple(Record(row_type, ((field(row_type, '.index0'), index), (field(row_type, '.value'), payloads[2*index+choice])))
                     for index in (0, 1) for choice in (0, 1))
    params = {'typeArgument0': (0, 1), 'familyArgument1': relation}
    source_layout, target_layout = (0, 1, 0), (1, 0, 0)
    source_schema, target_schema = [listing(schema_type, params, xs) for xs in (source_layout, target_layout)]
    signature_type = runtime(constructor(expr_type, '.call'))[-3][1]
    signature = make(signature_type, None, params, source_schema, 0)
    # Public fields of an instantiated module must use the canonical record,
    # while preserving the alias's source obligation and complete field value.
    copied_fields = {}
    for name in ('inputs', 'output'):
        rows = [o for o in report['obligations'] if 'Agda2SysML.ComputedIndices._#' in o['symbol']
                and '.Signature.' + name + '#' in o['symbol'] and '@' not in o['symbol']
                and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], name
        assert rows[0]['source']['checkedDefinition'] == rows[0]['symbol']
        copied_fields[name] = target_name(rows[0]['target'])
        assert runtime(copied_fields[name]) == [('input0', signature_type)]
    projection_comparisons = 0
    for layout in ((), (0,), (1, 0, 1), (0, 0, 1, 0)):
        inputs = listing(schema_type, params, layout)
        for output in (0, 1):
            value = make(signature_type, None, params, inputs, output)
            expect(call(copied_fields['inputs'], params, value), inputs)
            expect(call(copied_fields['output'], params, value), output)
            projection_comparisons += 2
    refuse(lambda: call(copied_fields['output'], {**params, 'typeArgument0': (1,)}, signature))
    mutate(copied_fields['output'], params, (signature,), 1, 0)
    fs = listing(signatures_type, params, (signature,))
    ref_type = runtime(constructor(expr_type, '.call'))[-2][1]
    ref = make(ref_type, '.here', params, signature, listing(signatures_type, params, ()))
    def member(index, choice):
        return Record(member_type, (*params.items(), (field(member_type, '.index0'), index),
                      (field(member_type, '.value'), payloads[2*index+choice])))
    def position(layout, ordinal):
        if ordinal == 0: return make(position_type, '.first', params, layout[0], listing(schema_type, params, layout[1:]))
        return make(position_type, '.next', params, layout[ordinal], layout[0], listing(schema_type, params, layout[1:]), position(layout[1:], ordinal-1))
    operation_type = runtime(constructor(expr_type, '.apply'))[-2][1]
    operation_signature = [t for _, t in runtime(constructor(operation_type)) if isinstance(t, CallableSignature)]
    proof_type = operation_signature[-1].result
    proof_values = [0 if t == 'Base::Anything' else member(0, 0) for _, t in runtime(constructor(proof_type))]
    assert all(t in ('Base::Anything', member_type) for _, t in runtime(constructor(proof_type)))
    proof = make(proof_type, None, params, *proof_values)
    operation_bindings = [callback('multiOperation' + str(i), sig.arguments, sig.result,
                                  literal(proof if i == 2 else member(0, 0)))
                          for i, sig in enumerate(operation_signature)]
    refresh()
    operation = make(operation_type, None, params, signature, *operation_bindings)
    def expr(tree, layout):
        schema = listing(schema_type, params, layout)
        if tree[0] == 'local':
            return make(expr_type, '.local', params, fs, schema, layout[tree[1]], position(layout, tree[1]))
        if tree[0] in ('call', 'apply'):
            return make(expr_type, '.' + tree[0], params, fs, schema, signature,
                        ref if tree[0] == 'call' else operation, actuals(tree[1], layout))
        return make(expr_type, '.literal', params, fs, schema, tree[1], member(tree[1], tree[2]))
    def atom(tree, layout):
        if tree[0] == 'local': return layout[tree[1]]
        return 0 if tree[0] in ('call', 'apply') else tree[1]
    def actuals(trees, layout):
        schema = listing(schema_type, params, layout)
        if not trees: return make(args_type, '.none', params, fs, schema)
        return make(args_type, '.argument', params, fs, schema, atom(trees[0], layout),
                    listing(schema_type, params, [atom(t, layout) for t in trees[1:]]), expr(trees[0], layout), actuals(trees[1:], layout))
    first = position(source_layout, 0)
    first_tag = first.get('constructor')
    returned = [expr(('literal', i, c), target_layout) for i, c in ((0,0),(0,1),(1,0))]
    replacement = callback('multiReplacement', substitution.arguments, substitution.result,
        'if a0 == 1 ? ' + literal(returned[2]) + ' else if a1.' + quote('constructor') + ' == '
        + literal(first_tag) + ' ? ' + literal(returned[0]) + ' else ' + literal(returned[1]))
    wrong_index = callback('multiWrongIndex', substitution.arguments, substitution.result, literal(returned[2]))
    refresh()
    trees = [('local', i) for i in range(3)] + [('literal', i, c) for i in (0,1) for c in (0,1)]
    branch = (trees[0], trees[1], trees[2])
    trees += [('call', branch), ('apply', branch), ('call', (('apply', branch), trees[1], trees[2]))]
    def substitute(tree):
        if tree[0] == 'literal': return tree
        if tree[0] in ('call', 'apply'): return (tree[0], tuple(map(substitute, tree[1])))
        i = tree[1]
        return ('literal', source_layout[i], 1 if i == 2 else 0)
    for tree in trees:
        expect(call(replace, params, fs, source_schema, target_schema, atom(tree, source_layout), replacement, expr(tree, source_layout)), expr(substitute(tree), target_layout))
    for size in range(4):
        for group in itertools.product(trees[:3], repeat=size):
            indices = listing(schema_type, params, [atom(t, source_layout) for t in group])
            expect(call(replace_args, params, fs, source_schema, target_schema, indices, replacement, actuals(group, source_layout)), actuals(tuple(map(substitute, group)), target_layout))
    group = (trees[-1], trees[1], trees[-2])
    indices = listing(schema_type, params, [atom(t, source_layout) for t in group])
    expect(call(replace_args, params, fs, source_schema, target_schema, indices, replacement, actuals(group, source_layout)),
           actuals(tuple(map(substitute, group)), target_layout))
    values = (fs, source_schema, target_schema, 0, replacement, expr(trees[0], source_layout))
    refuse(lambda: call(replace, params, *values[:4], wrong_arity, values[-1]))
    refuse(lambda: call(replace, params, *values[:4], wrong_index, values[-1]))
    refuse(lambda: call(replace, params, fs, target_schema, target_schema, 0, replacement, values[-1]))
    mutate(replace, params, values, returned[1], returned[0])
    group = (trees[0], trees[2])
    indices = listing(schema_type, params, (0, 0))
    wrong = actuals((('literal',0,1), ('literal',0,0)), target_layout)
    expected = actuals(tuple(map(substitute, group)), target_layout)
    mutate(replace_args, params, (fs, source_schema, target_schema, indices, replacement, actuals(group, source_layout)), wrong, expected)
    return {'operations': len(roots), 'comparisons': comparisons, 'invalidBindingsRejected': rejected,
            'copiedProjectionRoots': len(copied_fields), 'copiedProjectionComparisons': projection_comparisons,
            'bodyMutationsDetected': mutations, 'dependentArguments': True, 'completeResultsAndOriginsPreserved': True}
