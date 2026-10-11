"""Execute specialization conversions and their laws from emitted SysML."""
import json
from pathlib import Path
from emitted_model import CalculationValue, CallableSignature, Model, Parser, Record, same, tokens
from open_parameters import target_name


def verify_index_closures(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    roots = {}
    for operation in ('encode', 'decode', 'specializeOperation'):
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.Specialization.' + operation + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], operation
        roots[operation] = target_name(rows[0]['target'])
    carriers = {target_name(s['target']): s for s in report['algebraicCarriers']}
    bindings, additions, samples = {}, [], {}
    comparisons = rejected = mutations = 0

    def quote(value):
        return "'" + value.replace('\\', '\\\\').replace("'", "\\'") + "'"

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def arguments(symbol, values):
        return [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                  if f.startswith(('typeArgument', 'familyArgument'))], *values]

    def call(symbol, *values):
        args = arguments(symbol, values)
        result = model.invoke(symbol, args)
        if symbol in roots.values(): samples.setdefault(symbol, []).append((args, result))
        return result

    def constructor(typ, name):
        found = [target_name(c['target']) for c in carriers[typ]['constructors']
                 if target_name(c['target']).split('<', 1)[0].endswith('.' + name)]
        assert len(found) == 1, (typ, name, found)
        return found[0]

    def field(typ, suffix):
        found = [f for f, _, _, _ in model.carriers[typ][1]
                 if f.split('#', 1)[0].split('<', 1)[0].endswith(suffix)]
        assert len(found) == 1, (typ, suffix, found)
        return found[0]

    def record(typ, values):
        return Record(typ, tuple((f, bindings[f] if f.startswith(('typeArgument', 'familyArgument')) else values[f])
                                for f, _, _, _ in model.carriers[typ][1]))

    def literal(value):
        if isinstance(value, Record):
            return 'new ' + quote(value.type) + '(' + ', '.join(quote(k) + ' = ' + literal(v) for k, v in value.fields) + ')'
        if isinstance(value, tuple):
            if not value: return 'null'
            return '(' + ', '.join([literal(v) for v in value] + (['null'] if len(value) == 1 else [])) + ')'
        if isinstance(value, int): return str(value)
        if isinstance(value, str) and '::' in value: return '::'.join(map(quote, value.rsplit('::', 1)))
        raise AssertionError(('unsupported literal', value))

    def callback(name, signature, expression):
        additions.append('calc def ' + quote(name) + ' { ' + ''.join(
            f'in a{i} : {quote(t)} [1]; ' for i, t in enumerate(signature.arguments))
            + f'return result : {quote(signature.result)} [1] = {expression}; }}')
        return CalculationValue(name)

    checked, invoked = {}, {}
    def refresh():
        nonlocal model
        model = Model(text + '\n' + '\n'.join(additions))
        checked.clear(); invoked.clear()
        boundary, invoke = model.boundary, model.invoke
        def cached_boundary(carrier, low, high, value, depth=0):
            key = (id(carrier), low, high, id(value))
            if key not in checked:
                boundary(carrier, low, high, value, depth)
                checked[key] = (carrier, value)
        def cached_invoke(symbol, args, check=True, depth=0):
            key = (symbol, tuple(map(id, args)), check)
            if key not in invoked:
                invoked[key] = (tuple(args), invoke(symbol, args, check, depth))
            return invoked[key][1]
        model.boundary, model.invoke = cached_boundary, cached_invoke

    def expect(actual, expected):
        nonlocal comparisons
        assert same(actual, expected), 'changed complete specialization value'
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        checked.clear(); invoked.clear()
        try: action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('invalid specialization value admitted')

    # Interpret nested trees with a nonconstant, order-sensitive family meaning.
    # Payloads remain opaque, complete records, independent of that interpretation.
    trees = [('parameter', 0), ('parameter', 1), ('atom', 0), ('atom', 1),
             ('family', 0, ()), ('family', 1, (('parameter', 0), ('parameter', 1), ('parameter', 0))),
             ('family', 0, (('family', 1, (('parameter', 1), ('atom', 0))), ('parameter', 0)))]
    replacements = (('atom', 1), ('family', 1, (('atom', 0), ('family', 0, ()), ('atom', 0))))

    def meaning(tree):
        tag, *parts = tree
        if tag == 'parameter': return meaning(replacements[parts[0]])
        if tag == 'atom': return parts[0] + 1
        values = [meaning(t) for t in parts[1]]
        return 10 + parts[0] + len(values) + (3 * values[0] if values else 0)

    def subtrees(tree):
        return [tree] + ([t for child in tree[2] for t in subtrees(child)] if tree[0] == 'family' else [])
    indices = tuple(sorted({meaning(t) for tree in trees + list(replacements) for t in subtrees(tree)} | {0, 1, 2, 10, 11}))
    bindings.update(typeArgument0=(0, 1), typeArgument1=(0, 1), typeArgument2=indices,
                    typeArgument3=(0, 1), typeArgument4=(0, 1))
    encode, decode, specialize = (roots[n] for n in ('encode', 'decode', 'specializeOperation'))
    atom_sig, family_sig, schema_type, replacement_sig, source_type, member_type = [t for _, t in runtime(encode)]
    assert model.results[encode] == member_type and model.results[decode] == member_type
    row_type = next(t for f, t, _, _ in model.carriers[schema_type][1] if f == 'items')
    payloads = {(i, n): Record('SpecializationPayload', (('key', n), ('history', (i, n, n, 10**40))))
                for i in indices for n in range(2)}
    rows = tuple(record(row_type, {field(row_type, '.index0'): i, field(row_type, '.value'): p})
                 for (i, _), p in payloads.items())
    schema = record(schema_type, {'items': rows})
    member = lambda i, n: record(member_type, {field(member_type, '.index0'): schema,
                                field(member_type, '.index1'): i, field(member_type, '.value'): payloads[i, n]})
    additions.append('attribute def SpecializationPayload { attribute key : ScalarValues::Natural; '
                     'attribute history : ScalarValues::Natural [0..*] ordered nonunique; }')
    atom = callback('closureAtomMeaning', atom_sig, 'a0 + 1')
    list_field = field(family_sig.arguments[1], 'items')
    items = 'a1.' + quote(list_field)
    family = callback('closureFamilyMeaning', family_sig,
                      '10 + a0 + SequenceFunctions::size(' + items + ') + '
                      '(if SequenceFunctions::size(' + items + ') == 0 ? 0 else 3 * SequenceFunctions::head(' + items + '))')

    def construct(symbol, *values):
        prefix = runtime(symbol)[:len(runtime(symbol)) - len(values)]
        assert all(t == schema_type for _, t in prefix), (symbol, prefix)
        return call(symbol, *([schema] * len(prefix)), *values)

    def list_of(typ, values):
        result = construct(constructor(typ, '[]'))
        for value in reversed(values): result = construct(constructor(typ, '_∷_'), value, result)
        return result

    def value(typ, tree):
        tag, *parts = tree
        if tag in ('parameter', 'atom'):
            return construct(constructor(typ, tag), parts[0])
        symbol = constructor(typ, 'family')
        list_type = runtime(symbol)[-1][1]
        return construct(symbol, parts[0], list_of(list_type, [value(typ, t) for t in parts[1]]))

    refresh()
    closed_type = replacement_sig.result
    for typ in (source_type, closed_type, schema_type, row_type, member_type):
        assert not any(isinstance(t, CallableSignature) for _, t, _, _ in model.carriers[typ][1]), \
            ('callback identity stored in specialization data', typ)
    replacement_outputs = [value(closed_type, t) for t in replacements]
    expression = 'if a0 == 0 ? ' + literal(replacement_outputs[0]) + ' else ' + literal(replacement_outputs[1])
    replacement = callback('closureReplacement', replacement_sig, expression)
    equivalent = callback('closureEquivalentReplacement', replacement_sig, expression)
    different = callback('closureDifferentReplacement', replacement_sig,
                         'if a0 == 0 ? ' + literal(replacement_outputs[1]) + ' else ' + literal(replacement_outputs[0]))
    refresh()
    common = [atom, family, schema, replacement]
    for tree in trees:
        t, i = value(source_type, tree), meaning(tree)
        for n in range(2):
            x = member(i, n)
            expect(call(encode, *common, t, x), x)
            expect(call(decode, *common, t, x), x)
            expect(call(decode, *common, t, call(encode, *common, t, x)), x)
            expect(call(encode, *common, t, call(decode, *common, t, x)), x)
            # The same value is valid with a separately named, extensionally
            # equal callback. No function identity is stored in its data.
            expect(call(encode, atom, family, schema, equivalent, t, x), x)

    operation_signature = runtime(specialize)[-2][1]
    cases = []
    for j, (input_tree, output_tree) in enumerate(((trees[0], trees[0]), (trees[-1], trees[1]), (trees[1], trees[-1]))):
        i, o = meaning(input_tree), meaning(output_tree)
        expression = 'if a0 == ' + literal(member(i, 0)) + ' ? ' + literal(member(o, 1)) + ' else ' + literal(member(o, 0))
        operation = callback('closureOperation' + str(j), operation_signature, expression)
        cases.append((input_tree, output_tree, operation))
    wrong_operation = callback('closureWrongOperation', operation_signature, literal(member(0, 0)))
    refresh()
    for input_tree, output_tree, operation in cases:
        for n in range(2):
            expect(call(specialize, *common, value(source_type, input_tree), value(source_type, output_tree),
                        operation, member(meaning(input_tree), n)), member(meaning(output_tree), 1-n))

    laws = {}
    for name in ('instantiate-preserves', 'source-roundtrip', 'target-roundtrip', 'operation-preserves'):
        rows = [s for s in report['nativeStatements']
                if s['symbol'].startswith('Agda2SysML.Specialization.' + name + '#') and '@' not in s['symbol']]
        assert len(rows) == 1 and rows[0]['status'] == 'translated', name
        laws[name] = target_name(rows[0]['target'])
    for tree in trees:
        t, i = value(source_type, tree), meaning(tree)
        expect(call(laws['instantiate-preserves'], *common, t), True)
        for n in range(2):
            for name in ('source-roundtrip', 'target-roundtrip'):
                expect(call(laws[name], *common, t, member(i, n)), True)
    for input_tree, output_tree, operation in cases:
        for n in range(2):
            expect(call(laws['operation-preserves'], *common, value(source_type, input_tree), value(source_type, output_tree),
                        operation, member(meaning(input_tree), n)), True)

    def replace(item, f, changed):
        return Record(item.type, tuple((k, changed if k == f else v) for k, v in item.fields))

    t, i = value(source_type, trees[-1]), meaning(trees[-1])
    valid = member(i, 0)
    for symbol in (encode, decode):
        refuse(lambda: call(symbol, *common, t, member(0, 0)))
        invalid = replace(valid, field(member_type, '.value'), Record('SpecializationPayload', (('key', 99), ('history', (i, 99)))))
        refuse(lambda: call(symbol, *common, t, invalid))
        alien_schema = replace(schema, 'items', ())
        refuse(lambda: call(symbol, atom, family, alien_schema, replacement, t, valid))
        count = next(f for f, _ in t.fields if f.endswith('.node-count'))
        refuse(lambda: call(symbol, *common, replace(t, count, 0), valid))
        refuse(lambda: call(symbol, atom, family, schema, different,
                            value(source_type, trees[0]), member(meaning(trees[0]), 0)))
    refuse(lambda: call(specialize, *common, t, t, wrong_operation, valid))

    # One constant result must not pass the complete conversion/operation corpus.
    for symbol in roots.values():
        inputs, body, assertions = model.calculations[symbol]
        wrong = Parser(tokens(literal(samples[symbol][0][1]))).expression()
        model.calculations[symbol] = (inputs, wrong, assertions)
        checked.clear(); invoked.clear()
        detected = False
        for args, expected in samples[symbol]:
            try: actual = model.invoke(symbol, args)
            except AssertionError: detected = True; break
            if not same(actual, expected): detected = True; break
        assert detected, ('undetected conversion mutation', symbol)
        mutations += 1
        model.calculations[symbol] = (inputs, body, assertions)
        checked.clear(); invoked.clear()
    return dict(operations=len(roots), statements=len(laws), comparisons=comparisons,
                invalidCasesRejected=rejected, bodyMutationsDetected=mutations,
                completePayloadsPreserved=True, functionIdentityNotStored=True)
