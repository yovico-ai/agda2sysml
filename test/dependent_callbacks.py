"""Exercise the original first-order evaluator through parsed native SysML.

Supplied callbacks are SysML calculations. The reference interpreter below
operates on an independent expression tree and compares complete member values.
"""
import json
from pathlib import Path
from emitted_model import CalculationValue, CallableSignature, Model, Record, same
from open_parameters import target_name


def verify_dependent_callbacks(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    sources = ('lookup', 'nativeLookup', 'evaluate', 'evaluateArgs',
               'nativeEvaluate', 'nativeEvaluateArgs')
    roots = {}
    for source in sources:
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.FirstOrder.' + source + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], source
        roots[source] = target_name(rows[0]['target'])

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def constructor(typ, suffix=None):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if suffix is None or c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def field(typ, suffix):
        matches = [f for f, _, _, _ in model.carriers[typ][1]
                   if f.split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def quote(s):
        return "'" + s.replace('\\', '\\\\').replace("'", "\\'") + "'"

    member_type = model.results[roots['evaluate']]
    signature_type, signatures_type, ref_type, table_type, fields_type = [t for _, t in runtime(roots['lookup'])]
    native_table_type, native_fields_type = [t for _, t in runtime(roots['nativeLookup'])][-2:]
    _, schema_type, _, _, expr_type, _ = [t for _, t in runtime(roots['evaluate'])]
    native_expr_type = runtime(roots['nativeEvaluate'])[-2][1]
    args_type = runtime(roots['evaluateArgs'])[-2][1]
    native_args_type = runtime(roots['nativeEvaluateArgs'])[-2][1]
    local_constructor = constructor(expr_type, '.local')
    position_type = runtime(local_constructor)[-1][1]
    operation_type = runtime(constructor(expr_type, '.apply'))[-2][1]
    operation_constructor = constructor(operation_type)
    callbacks = [t for _, t in runtime(operation_constructor) if isinstance(t, CallableSignature)]
    assert len(callbacks) == 3
    proof_type = callbacks[-1].result
    proof_constructor = constructor(proof_type)
    member_index, member_value = field(member_type, '.index0'), field(member_type, '.value')
    row_type = next(t for f, t, _, _ in model.carriers[member_type][1] if f == 'familyArgument1')
    row_index, row_value = field(row_type, '.index0'), field(row_type, '.value')

    additions = []
    def callback(name, domain, result, expression):
        additions.append(f"calc def {quote(name)} {{ in x : {quote(domain)} [1]; "
                         f"return result : {quote(result)} [1] = {expression}; }}")
        return CalculationValue(name)

    def member_expression(typ, ordinal):
        head = next(f for f, t, _, _ in model.carriers[typ][1] if t == member_type)
        tail = next(f for f, t, _, _ in model.carriers[typ][1] if t == typ)
        return 'x' + ('.' + quote(tail)) * ordinal + '.' + quote(head)

    source_callbacks = [callback('dependentSource' + str(i), fields_type, member_type,
                                 member_expression(fields_type, i)) for i in (0, 2)]
    native_callbacks = [callback('dependentNative' + str(i), native_fields_type, member_type,
                                 member_expression(native_fields_type, i)) for i in (0, 2)]
    head = member_expression(fields_type, 0)
    proof_inputs = []
    for f, t, _, _ in model.calculations[proof_constructor][0]:
        if f.startswith(('typeArgument', 'familyArgument')):
            proof_inputs.append('x.' + quote(f))
        elif t == member_type:
            proof_inputs.append(head)
        else:
            assert t == 'Base::Anything', ('unexpected equality witness input', f, t)
            proof_inputs.append(head + '.' + quote(member_index))
    evidence = callback('dependentEvidence', fields_type, proof_type,
                        quote(proof_constructor) + '(' + ', '.join(proof_inputs) + ')')
    wrong_result = callback('dependentWrongIndex', fields_type, member_type,
                            member_expression(fields_type, 1))
    wrong_evidence = callback('dependentWrongEvidence', fields_type, proof_type,
        quote(proof_constructor) + '(' + ', '.join(x.replace(head, member_expression(fields_type, 1))
                                                  for x in proof_inputs) + ')')
    additions.append('calc def dependentWrongArity { in x : Base::Anything [1]; '
                     'in y : Base::Anything [1]; return result : Base::Anything [1] = x; }')
    model = Model(text + '\n' + '\n'.join(additions))

    # Test values and captured environments remain immutable. Retain each
    # validated object so an identity cannot be reused for a different value;
    # invalid cases below construct fresh values and still check every contract.
    checked_values = {}
    boundary = model.boundary
    def cached_boundary(carrier, low, high, value, depth):
        key = (id(carrier), low, high, id(value))
        if key not in checked_values:
            boundary(carrier, low, high, value, depth)
            checked_values[key] = (carrier, value)
    model.boundary = cached_boundary

    comparisons = rejected = evidence_checks = mutations = 0
    def expect(actual, expected):
        nonlocal comparisons
        assert same(actual, expected), ('changed complete result', actual, expected)
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('invalid dependent callback binding admitted')

    for atoms in ((False, True), (7, 10**40),
                  (Record('TypeAtom', (('id', 1),)), Record('TypeAtom', (('id', 2),)))):
        a, b = atoms
        payloads = {(i, choice): Record('Payload', (('choice', choice),
                    ('evidence', Record('Detail', (('atom', atom), ('steps', (choice, choice, 10**40)))))))
                    for i, atom in enumerate(atoms) for choice in range(2)}
        relation = tuple(Record(row_type, ((row_index, atom), (row_value, payloads[i, choice])))
                         for i, atom in enumerate(atoms) for choice in range(2))
        bindings = {'typeArgument0': atoms, 'familyArgument1': relation}

        def call(symbol, *values):
            return model.invoke(symbol, [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                                           if f.startswith(('typeArgument', 'familyArgument'))], *values])

        def make(typ, suffix, *values):
            return call(constructor(typ, suffix), *values)

        def schema(values, typ=schema_type):
            parameters = tuple((f, bindings[f]) for f, _, _, _ in model.carriers[typ][1]
                               if f.startswith(('typeArgument', 'familyArgument')))
            return Record(typ, (*parameters, ('items', tuple(values))))

        def member(atom, choice):
            i = next(i for i, value in enumerate(atoms) if same(atom, value))
            return Record(member_type, (('typeArgument0', atoms), ('familyArgument1', relation),
                          (member_index, atom), (member_value, payloads[i, choice])))

        def fields(layout, values, native=False):
            typ = native_fields_type if native else fields_type
            if not layout:
                return make(typ, '.empty' if native else '.nil')
            return make(typ, '.entry' if native else '.cons', layout[0], schema(layout[1:]), values[0],
                        fields(layout[1:], values[1:], native))

        def position(layout, ordinal):
            if ordinal == 0:
                return make(position_type, '.first', layout[0], schema(layout[1:]))
            return make(position_type, '.next', layout[ordinal], layout[0], schema(layout[1:]),
                        position(layout[1:], ordinal - 1))

        layouts = ((a, b, a), (b,))
        signatures = tuple(make(signature_type, None, schema(layout), layout[0]) for layout in layouts)
        fs = schema(signatures, signatures_type)
        context_layout = (a, b, a)
        context = schema(context_layout)

        def table(native=False):
            typ = native_table_type if native else table_type
            result = make(typ, '.noCalculations' if native else '.noFunctions')
            cbs = native_callbacks if native else source_callbacks
            for i in reversed(range(len(signatures))):
                result = make(typ, '.calculation' if native else '.function', signatures[i],
                              schema(signatures[i+1:], signatures_type), cbs[1 if i == 0 else 0], result)
            return result

        def reference(ordinal):
            result = make(ref_type, '.here', signatures[ordinal], schema(signatures[ordinal+1:], signatures_type))
            for i in reversed(range(ordinal)):
                result = make(ref_type, '.there', signatures[ordinal], signatures[i],
                              schema(signatures[i+1:], signatures_type), result)
            return result

        operation = make(operation_type, None, signatures[0], source_callbacks[0], native_callbacks[0], evidence)

        def result_atom(tree):
            tag, *values = tree
            if tag == 'local': return context_layout[values[0]]
            if tag == 'literal': return atoms[values[0]]
            if tag == 'call': return layouts[values[0]][0]
            return a

        def expression(tree, native=False):
            typ = native_expr_type if native else expr_type
            tag, *values = tree
            atom = result_atom(tree)
            if tag == 'local':
                return make(typ, '.input' if native else '.local', fs, context, atom,
                            position(context_layout, values[0]))
            if tag == 'literal':
                return make(typ, '.value' if native else '.literal', fs, context, atom, member(atom, values[1]))
            if tag == 'call':
                ordinal, arguments = values
                return make(typ, '.invoke' if native else '.call', fs, context, signatures[ordinal],
                            reference(ordinal), arguments_value(arguments, native))
            return make(typ, '.applyNative' if native else '.apply', fs, context, signatures[0], operation,
                        arguments_value(values[0], native))

        def arguments_value(trees, native=False):
            typ = native_args_type if native else args_type
            if not trees:
                return make(typ, '.noArgs' if native else '.none', fs, context)
            return make(typ, '.actual' if native else '.argument', fs, context, result_atom(trees[0]),
                        schema(tuple(map(result_atom, trees[1:]))), expression(trees[0], native),
                        arguments_value(trees[1:], native))

        def interpret(tree, values):
            tag, *args = tree
            if tag == 'local': return values[args[0]]
            if tag == 'literal': return member(atoms[args[0]], args[1])
            if tag == 'call': return interpret(args[1][2 if args[0] == 0 else 0], values)
            return interpret(args[0][0], values)

        tables = (table(), table(True))
        simple = [('local', i) for i in range(3)] + [('literal', i, choice) for i in range(2) for choice in range(2)]
        args = (('local', 0), ('call', 1, (('local', 1),)), ('literal', 0, 1))
        trees = simple + [('call', 0, args), ('apply', args),
                         ('apply', (('call', 0, args), ('local', 1), ('local', 2)))]
        for choices in ((0, 0, 0), (0, 1, 1), (1, 0, 0), (1, 1, 1)):
            values = tuple(member(atom, choice) for atom, choice in zip(context_layout, choices))
            for native in (False, True):
                env = fields(context_layout, values, native)
                evaluate = roots['nativeEvaluate' if native else 'evaluate']
                eval_args = roots['nativeEvaluateArgs' if native else 'evaluateArgs']
                for tree in trees:
                    expect(call(evaluate, fs, context, result_atom(tree), tables[native], expression(tree, native), env),
                           interpret(tree, values))
                for arguments in ((), args, tuple(trees[:3])):
                    layout = tuple(map(result_atom, arguments))
                    expect(call(eval_args, fs, context, schema(layout), tables[native], arguments_value(arguments, native), env),
                           fields(layout, tuple(interpret(t, values) for t in arguments), native))
                lookup = roots['nativeLookup' if native else 'lookup']
                for i, layout in enumerate(layouts):
                    actuals = tuple(member(atom, choices[j]) for j, atom in enumerate(layout))
                    expect(call(lookup, signatures[i], fs, reference(i), tables[native], fields(layout, actuals, native)),
                           actuals[2 if i == 0 else 0])

            source = fields(context_layout, values)
            witness_field = next(f for f, t, _, _ in model.carriers[operation_type][1]
                                 if isinstance(t, CallableSignature) and t.result == proof_type)
            binding = model.evaluate(('project', ('literal', operation), witness_field), {})
            witness = model.invoke_callback(binding, source)
            model.boundary(proof_type, 1, 1, witness, 0)
            evidence_checks += 1

        source = fields(context_layout, tuple(member(atom, 0) for atom in context_layout))
        refuse(lambda: call(roots['lookup'], signatures[1], fs, reference(0), tables[0], source))
        refuse(lambda: make(operation_type, None, signatures[0], CalculationValue('dependentWrongArity'), native_callbacks[0], evidence))
        refuse(lambda: make(operation_type, None, signatures[0], source_callbacks[0], native_callbacks[0], source_callbacks[0]))
        for bad_source, bad_proof in ((wrong_result, evidence), (source_callbacks[0], wrong_evidence)):
            bad = make(operation_type, None, signatures[0], bad_source, native_callbacks[0], bad_proof)
            binding = model.evaluate(('project', ('literal', bad), witness_field), {})
            refuse(lambda: model.invoke_callback(binding, source))

        # Same carrier and index, different complete payload: this mutation
        # must be caught by the reference result, not merely a type boundary.
        for native in (False, True):
            symbol = roots['nativeEvaluate' if native else 'evaluate']
            inputs, body, assertions = model.calculations[symbol]
            typ = native_fields_type if native else fields_type
            head_field = next(f for f, t, _, _ in model.carriers[typ][1] if t == member_type)
            env = fields(context_layout, tuple(member(atom, 0) for atom in context_layout), native)
            model.calculations[symbol] = (inputs, ('project', ('reference', inputs[-1][0]), head_field), assertions)
            try:
                actual = call(symbol, fs, context, a, tables[native], expression(('literal', 0, 1), native), env)
                assert not same(actual, member(a, 1)), 'evaluator body mutation was not detected'
                mutations += 1
            finally:
                model.calculations[symbol] = (inputs, body, assertions)

    return {'operations': len(roots), 'comparisons': comparisons,
            'evidenceCallbacksExercised': evidence_checks, 'invalidBindingsRejected': rejected,
            'bodyMutationsDetected': mutations}
