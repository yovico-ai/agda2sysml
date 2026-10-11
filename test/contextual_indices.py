"""Check computed dependent membership in emitted SysML, with runtime callbacks."""
import json
from pathlib import Path
from emitted_model import BodyCalculation, CalculationValue, Model, Record, same
from open_parameters import target_name


def verify_contextual_indices(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    roots = {}
    names = {'DependentRecords.Record': ('encode', 'decode', 'native', 'forgetInput', 'admitInput'),
             'IndexedValues.Family': ('encode', 'decode', 'admit-result',
                                     'constructor-result-contract', 'constructor-result-reflects',
                                     'constructor-result-refuses-mismatch')}
    for module, operations in names.items():
        for operation in operations:
            name = module + '.' + operation
            rows = [o for o in report['obligations'] if o['symbol'].startswith('Agda2SysML.' + name + '#')
                    and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
            assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], name
            roots[name] = target_name(rows[0]['target'])
    laws = {}
    for name in ('constructor-index', 'constructor-result-reflects'):
        rows = [s for s in report['nativeStatements'] if s['symbol'].startswith('Agda2SysML.IndexedValues.Family.' + name + '#')]
        assert len(rows) == 1 and rows[0]['status'] == 'translated', name
        laws[name] = target_name(rows[0]['target'])
    def root(module, operation):
        return roots[module + '.' + operation]
    def quote(s):
        return "'" + s.replace('\\', '\\\\').replace("'", "\\'") + "'"
    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]
    def field(typ, suffix):
        found = [f for f, _, _, _ in model.carriers[typ][1]
                 if f.split('#', 1)[0].split('<', 1)[0].endswith(suffix)]
        assert len(found) == 1, (typ, suffix, found)
        return found[0]
    def field_type(typ, suffix):
        return next(t for f, t, _, _ in model.carriers[typ][1] if f == field(typ, suffix))
    def ctor(typ):
        found = [target_name(c['target']) for sh in report['algebraicCarriers']
                 if target_name(sh['target']) == typ for c in sh['constructors']]
        assert len(found) == 1, (typ, found)
        return found[0]
    bindings = {}
    mutation_samples = {}
    def record(typ, values):
        return Record(typ, tuple((f, bindings[f] if f.startswith(('typeArgument', 'familyArgument')) else values[f])
                                for f, _, _, _ in model.carriers[typ][1]))
    def call(symbol, *values):
        arguments = [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                       if f.startswith(('typeArgument', 'familyArgument'))], *values]
        result = model.invoke(symbol, arguments)
        if symbol in roots.values():
            mutation_samples.setdefault(symbol, []).append((arguments, result))
        return result
    def construct(typ, *values):
        return call(ctor(typ), *values)
    additions = []
    def callback(name, signature, expression):
        additions.append('calc def ' + quote(name) + ' { ' + ''.join(
            f'in a{i} : {quote(t)} [1]; ' for i, t in enumerate(signature.arguments))
            + f'return result : {quote(signature.result)} [1] = {expression}; }}')
        return CalculationValue(name)
    def refresh():
        nonlocal model
        model = Model(text + '\n' + '\n'.join(additions))
        checked = {}
        boundary = model.boundary
        def cached(carrier, low, high, value, depth=0):
            key = (id(carrier), low, high, id(value))
            if key not in checked:
                boundary(carrier, low, high, value, depth)
                checked[key] = (carrier, value)
        model.boundary = cached
    comparisons = rejected = mutations = 0
    def expect(actual, expected):
        nonlocal comparisons
        assert same(actual, expected), 'changed complete contextual value'
        comparisons += 1
    def refuse(action):
        nonlocal rejected
        try: action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('inconsistent contextual membership admitted')
    def replace(value, f, x):
        return Record(value.type, tuple((k, x if k == f else v) for k, v in value.fields))

    module = 'DependentRecords.Record'
    encode, decode, native, forget, admit = [root(module, op) for op in names[module]]
    index_sig, schema_type, source_type = [t for _, t in runtime(encode)]
    native_type = model.results[encode]
    raw_type = model.results[forget]
    fibre_type = field_type(native_type, '.snd')
    carrier_type = field_type(fibre_type, '.fst')
    proof_type = field_type(fibre_type, '.snd')
    member_type = field_type(source_type, '.snd')
    row_type = next(t for f, t, _, _ in model.carriers[schema_type][1] if f == 'items')
    identity = callback('contextIndex', index_sig, 'a0')
    equivalent = callback('contextEquivalentIndex', index_sig, 'if a0 == 0 ? 0 else 7')
    wrong = callback('contextWrongIndex', index_sig, '7')
    op_sig = runtime(native)[-2][1]
    operation = callback('contextOperation', op_sig, 'a0')
    def copy_expression(typ, reference, changes):
        return 'new ' + quote(typ) + '(' + ', '.join(quote(f) + ' = ' +
            changes.get(f, reference + '.' + quote(f)) for f, _, _, _ in model.carriers[typ][1]) + ')'
    member_reference = 'a0.' + quote(field(source_type, '.snd'))
    changed_member = copy_expression(member_type, member_reference, {field(member_type, '.value'):
        "new OpaqueMember(key = 1, history = (a0." + quote(field(source_type, '.fst')) + ", 1, 1, " + str(10**40) + '))'})
    transform = callback('contextTransform', op_sig, copy_expression(source_type, 'a0',
                         {field(source_type, '.snd'): changed_member}))
    refresh()
    indices = (0, 7, 10**40)
    bindings.update(typeArgument3=indices, typeArgument4=indices)
    payloads = {(i, n): Record('OpaqueMember', (('key', n), ('history', (i, n, n, 10**40))))
                for i in indices for n in range(2)}
    rows = tuple(record(row_type, {field(row_type, '.index0'): i, field(row_type, '.value'): p})
                 for (i, _), p in payloads.items())
    schema = record(schema_type, {'items': rows})
    def member(i, n=0):
        return record(member_type, {field(member_type, '.index0'): schema,
                      field(member_type, '.index1'): i, field(member_type, '.value'): payloads[i, n]})
    samples = {}
    for i in indices:
        for n in range(2):
            m = member(i, n)
            source = construct(source_type, schema, identity, i, m)
            carrier = construct(carrier_type, schema, i, m)
            proof = construct(proof_type, i)
            fibre = construct(fibre_type, schema, i, carrier, proof)
            expected = construct(native_type, schema, identity, i, fibre)
            raw = construct(raw_type, schema, i, carrier)
            expect(call(encode, identity, schema, source), expected)
            expect(call(decode, identity, schema, expected), source)
            expect(call(native, identity, schema, operation, expected), expected)
            expect(call(forget, identity, schema, expected), raw)
            expect(call(admit, identity, schema, raw, proof), expected)
            samples[i, n] = source, expected, raw, proof
    source, expected, raw, proof = samples[0, 0]
    expect(call(native, identity, schema, transform, expected), samples[0, 1][1])
    expect(call(encode, equivalent, schema, source), expected)
    expect(call(decode, equivalent, schema, expected), source)
    refuse(lambda: call(encode, wrong, schema, source))
    refuse(lambda: call(decode, wrong, schema, expected))
    refuse(lambda: call(admit, wrong, schema, raw, proof))
    refuse(lambda: call(admit, identity, schema, raw, samples[7, 0][3]))
    bad_source = replace(source, field(source_type, '.snd'), member(7))
    refuse(lambda: call(encode, identity, schema, bad_source))
    narrow_schema = replace(schema, 'items', rows[:1])
    refuse(lambda: call(encode, identity, narrow_schema, source))
    # forgetInput performs no callback evaluation in its body: its input
    # membership contract must reject a value indexed by another callback.
    refuse(lambda: call(forget, wrong, schema, expected))
    inputs, body, assertions = model.calculations[forget]
    model.calculations[forget] = inputs, body, []
    try:
        expect(call(forget, wrong, schema, expected), raw)
        mutations += 1
    finally:
        model.calculations[forget] = inputs, body, assertions

    module = 'IndexedValues.Family'
    encode, decode, admit = [root(module, op) for op in ('encode', 'decode', 'admit-result')]
    index_sig, _, source_type = [t for _, t in runtime(encode)]
    fibre_type = model.results[encode]
    carrier_type = field_type(fibre_type, '.fst')
    proof_type = field_type(fibre_type, '.snd')
    member_type = field_type(carrier_type, '.snd')
    row_type = next(t for f, t, _, _ in model.carriers[member_type][1] if f == 'familyArgument5')
    member_value = field(member_type, '.value')
    additions.append('attribute def IndexPayload { attribute key : ScalarValues::Natural [1]; '
                     'attribute history : ScalarValues::Natural [0..*] ordered nonunique; }')
    key = '(a1.' + quote(member_value) + ' as IndexPayload).key'
    identity = callback('contextResultIndex', index_sig, 'if a0 ? 7 else ' + key)
    equivalent = callback('contextEquivalentResultIndex', index_sig, 'if ' + key + ' == 0 ? 0 else 7')
    wrong = callback('contextWrongResultIndex', index_sig, '7')
    refresh()
    tags = (False, True)
    bindings.update(typeArgument3=indices, typeArgument4=tags)
    payloads = {i: Record('IndexPayload', (('key', i), ('history', (i, i, 10**40)))) for i in indices}
    relation = tuple(Record(row_type, ((field(row_type, '.index0'), t), (field(row_type, '.value'), payloads[i])))
                     for t in tags for i in indices)
    bindings['familyArgument5'] = relation
    samples = {}
    for t in tags:
        for i in indices:
            m = record(member_type, {field(member_type, '.index0'): t, member_value: payloads[i]})
            selected = 7 if t else i
            source = construct(source_type, identity, t, m)
            carrier = construct(carrier_type, t, m)
            proof = construct(proof_type, selected)
            expected = construct(fibre_type, identity, selected, carrier, proof)
            expect(call(encode, identity, selected, source), expected)
            expect(call(decode, identity, selected, expected), source)
            expect(call(admit, identity, selected, carrier, proof), expected)
            for operation in ('constructor-result-contract', 'constructor-result-reflects'):
                expect(call(root(module, operation), identity, t, m, selected, proof), proof)
            expect(call(laws['constructor-index'], identity, t, m), True)
            expect(call(laws['constructor-result-reflects'], identity, t, m, selected, proof), True)
            samples[t, i] = source, expected, carrier, proof
    source, expected, carrier, proof = samples[False, 0]
    expect(call(encode, equivalent, 0, source), expected)
    expect(call(decode, equivalent, 0, expected), source)
    refuse(lambda: call(encode, wrong, 0, source))
    refuse(lambda: call(decode, wrong, 0, expected))
    refuse(lambda: call(admit, wrong, 0, carrier, proof))
    refuse(lambda: call(encode, identity, 7, source))
    refuse(lambda: call(admit, identity, 0, carrier, samples[False, 7][3]))
    m = record(member_type, {field(member_type, '.index0'): False, member_value: payloads[0]})
    for operation in ('constructor-result-contract', 'constructor-result-reflects'):
        refuse(lambda operation=operation: call(root(module, operation), identity, False, m, 7, proof))
    refuses = root(module, 'constructor-result-refuses-mismatch')
    signature = runtime(refuses)[-2][1]
    impossible = BodyCalculation((('proof', signature.arguments[0]),), signature.result,
                                 ('literal', Record(signature.result, ())), {})
    # A mismatching proof fails the input contract. Even with a valid proof,
    # a callback cannot fabricate a member of the empty result carrier.
    refuse(lambda: call(refuses, identity, False, m, 7, impossible, proof))
    refuse(lambda: call(refuses, identity, False, m, 0, impossible, proof))
    for name, values in (('constructor-index', [identity, False, m]),
                         ('constructor-result-reflects', [identity, False, m, 0, proof])):
        symbol = laws[name]
        saved = model.calculations[symbol]
        model.calculations[symbol] = saved[0], ('literal', False), saved[2]
        try:
            assert call(symbol, *values) is False, 'false indexed law was not observed'
            mutations += 1
        finally:
            model.calculations[symbol] = saved
    for symbol, cases in mutation_samples.items():
        arguments, expected = cases[0]
        altered = next(value for _, value in cases if not same(value, expected))
        inputs, body, assertions = model.calculations[symbol]
        model.calculations[symbol] = inputs, ('literal', altered), assertions
        try:
            try:
                actual = model.invoke(symbol, arguments)
            except AssertionError:
                mutations += 1
            else:
                assert not same(actual, expected), ('body mutation escaped', symbol)
                mutations += 1
        finally:
            model.calculations[symbol] = inputs, body, assertions
    return {'operations': len(roots), 'nativeStatements': len(laws), 'comparisons': comparisons, 'invalidCasesRejected': rejected,
            'mutationsDetected': mutations}
