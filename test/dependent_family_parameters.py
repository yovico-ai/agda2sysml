"""Exercise partial and dependent families from the unchanged self specification."""
import json
from pathlib import Path
from emitted_model import CalculationValue, Model, Record, same
from open_parameters import target_name


def verify_dependent_family_parameters(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    roots = {}
    groups = {'DependentSums.Constructors': ('encode', 'decode', 'native', 'dispatch'),
              'SpecializedFamilies.Instantiation': ('encode', 'decode', 'specialize')}
    for module, operations in groups.items():
        for operation in operations:
            source = 'Agda2SysML.' + module + '.' + operation
            rows = [o for o in report['obligations'] if o['symbol'].startswith(source + '#')
                    and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
            assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], source
            roots[module, operation] = target_name(rows[0]['target'])
    bindings, samples = {}, {}
    additions = []
    comparisons = rejected = mutations = 0

    def quote(s):
        return "'" + s.replace('\\', '\\\\').replace("'", "\\'") + "'"

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def field(typ, suffix):
        matches = [f for f, _, _, _ in model.carriers[typ][1]
                   if f.split('#', 1)[0].split('<', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def field_type(typ, suffix):
        return next(t for f, t, _, _ in model.carriers[typ][1] if f == field(typ, suffix))

    def record(typ, values):
        return Record(typ, tuple((f, bindings[f] if f.startswith(('typeArgument', 'familyArgument')) else values[f])
                                for f, _, _, _ in model.carriers[typ][1]))

    def call(symbol, *values):
        args = [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                  if f.startswith(('typeArgument', 'familyArgument'))], *values]
        result = model.invoke(symbol, args)
        if symbol in roots.values():
            samples.setdefault(symbol, []).append((args, result))
        return result

    def construct(typ, *values):
        names = [target_name(c['target']) for sh in report['algebraicCarriers']
                 if target_name(sh['target']) == typ for c in sh['constructors']]
        assert len(names) == 1, (typ, names)
        return call(names[0], *values)

    def callback(name, signature, expression):
        additions.append('calc def ' + quote(name) + ' { ' + ''.join(
            f'in a{i} : {quote(t)} [1]; ' for i, t in enumerate(signature.arguments))
            + f'return result : {quote(signature.result)} [1] = {expression}; }}')
        return CalculationValue(name)

    def refresh():
        nonlocal model
        model = Model(text + '\n' + '\n'.join(additions))
        boundary, checked = model.boundary, {}
        def cached(typ, low, high, value, depth=0):
            key = (id(typ), low, high, id(value))
            if key not in checked:
                boundary(typ, low, high, value, depth)
                checked[key] = (typ, value)
        model.boundary = cached

    def expect(actual, expected):
        nonlocal comparisons
        assert same(actual, expected), 'dependent family changed complete payload or evidence'
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('inconsistent dependent family was admitted')

    def replace(value, name, new):
        return Record(value.type, tuple((f, new if f == name else x) for f, x in value.fields))

    # Cases below use actual emitted carrier and constructor signatures. Opaque
    # payloads include repeated data and a large natural to detect lossy copies.
    module = 'DependentSums.Constructors'
    encode, decode, native, dispatch = [roots[module, op] for op in groups[module]]
    index_sig, schema_type, source_type = [t for _, t in runtime(encode)]
    native_type = model.results[encode]
    payload_type = field_type(source_type, '.snd')
    native_payload_type = field_type(native_type, '.snd')
    prefix_type = field_type(payload_type, '.fst')
    member_type = field_type(payload_type, '.snd')
    fibre_type = field_type(native_payload_type, '.snd')
    carrier_type = field_type(fibre_type, '.fst')
    proof_type = field_type(fibre_type, '.snd')
    index_type = index_sig.result
    prefix_row = field_type(prefix_type, 'familyArgument5')
    index_row = field_type(index_type, 'familyArgument6')
    schema_row = field_type(schema_type, 'items')
    additions.append('attribute def FamilyPrefix { attribute chosen : ' + quote(index_type) + '; '
                     'attribute alternate : ' + quote(index_type) + '; }')
    get_prefix = '(a1.' + quote(field(prefix_type, '.value')) + ' as FamilyPrefix)'
    index_fn = callback('dependentFamilyIndex', index_sig, get_prefix + '.chosen')
    wrong_index_fn = callback('dependentFamilyWrongIndex', index_sig, get_prefix + '.alternate')
    operation = callback('dependentFamilyIdentity', runtime(native)[-2][1], 'a0')
    dispatch_sig = runtime(dispatch)[-2][1]
    additions.append('attribute def DependentDispatchResult { attribute tag : '
                     + quote(dispatch_sig.arguments[0]) + '; attribute payload : '
                     + quote(dispatch_sig.arguments[1]) + '; }')
    branch = callback('dependentFamilyBranch', dispatch_sig,
                      'new DependentDispatchResult(tag = a0, payload = a1)')
    encode_static = {f for f, _, _, _ in model.calculations[encode][0]
                     if f.startswith(('typeArgument', 'familyArgument'))}
    result_slots = [f for f, _, _, _ in model.calculations[dispatch][0]
                    if f.startswith('typeArgument') and f not in encode_static]
    assert len(result_slots) == 1, result_slots
    refresh()
    tags = (False, True)
    bindings['typeArgument4'] = tags
    index_payloads = {(tag, i): Record('FamilyIndex', (('tag', tag), ('number', i),
                        ('history', (i, i, 10**40)))) for tag in tags for i in (0, 7)}
    bindings['familyArgument6'] = tuple(record(index_row, {field(index_row, '.index0'): tag,
        field(index_row, '.value'): value}) for (tag, _), value in index_payloads.items())
    indices = {(tag, i): record(index_type, {field(index_type, '.index0'): tag,
                 field(index_type, '.value'): value}) for (tag, i), value in index_payloads.items()}
    prefixes = {(tag, i): Record('FamilyPrefix', (('chosen', indices[tag, i]),
                 ('alternate', indices[tag, 7-i]))) for tag, i in indices}
    bindings['familyArgument5'] = tuple(record(prefix_row, {field(prefix_row, '.index0'): tag,
        field(prefix_row, '.value'): value}) for (tag, _), value in prefixes.items())
    members = {(tag, i, token): Record('FamilyMember', (('token', token), ('tag', tag),
               ('evidence', Record('FamilyEvidence', (('steps', (i, i, 10**40)),)))))
               for tag, i in indices for token in (0, 1)}
    schema = record(schema_type, {'items': tuple(record(schema_row,
        {field(schema_row, '.index0'): tag, field(schema_row, '.index1'): indices[tag, i],
         field(schema_row, '.value'): value}) for (tag, i, _), value in members.items())})
    sum_cases = {}
    for (tag, i, token), value in members.items():
        prefix = record(prefix_type, {field(prefix_type, '.index0'): tag,
                        field(prefix_type, '.value'): prefixes[tag, i]})
        member = record(member_type, {field(member_type, '.index0'): schema,
                        field(member_type, '.index1'): tag, field(member_type, '.index2'): indices[tag, i],
                        field(member_type, '.value'): value})
        payload = construct(payload_type, tag, schema, index_fn, prefix, member)
        source = construct(source_type, schema, index_fn, tag, payload)
        carrier = construct(carrier_type, tag, schema, indices[tag, i], member)
        proof = construct(proof_type, tag, indices[tag, i])
        fibre = construct(fibre_type, tag, schema, indices[tag, i], carrier, proof)
        native_payload = construct(native_payload_type, tag, schema, index_fn, prefix, fibre)
        expected = construct(native_type, schema, index_fn, tag, native_payload)
        expect(call(encode, index_fn, schema, source), expected)
        expect(call(decode, index_fn, schema, expected), source)
        expect(call(native, index_fn, schema, operation, expected), expected)
        sum_cases[tag, i, token] = source, expected, prefix, member, fibre, proof
    results = {key: Record('DependentDispatchResult', (('tag', key[0]),
                ('payload', case[0].get(field(source_type, '.snd')))))
               for key, case in sum_cases.items()}
    bindings[result_slots[0]] = tuple(results.values())
    for key, case in sum_cases.items():
        expect(call(dispatch, index_fn, schema, branch, case[1]), results[key])
    source, expected, prefix, member, fibre, proof = sum_cases[False, 0, 0]
    refuse(lambda: call(encode, wrong_index_fn, schema, source))
    refuse(lambda: call(decode, wrong_index_fn, schema, expected))
    refuse(lambda: call(dispatch, wrong_index_fn, schema, branch, expected))
    result_extent = bindings[result_slots[0]]
    bindings[result_slots[0]] = result_extent[1:]
    refuse(lambda: call(dispatch, index_fn, schema, branch, expected))
    bindings[result_slots[0]] = result_extent
    refuse(lambda: construct(payload_type, False, schema, index_fn, prefix, sum_cases[True, 0, 0][3]))
    refuse(lambda: construct(payload_type, False, schema, index_fn, prefix, sum_cases[False, 7, 0][3]))
    refuse(lambda: construct(fibre_type, False, schema, indices[False, 0],
                           fibre.get(field(fibre_type, '.fst')), sum_cases[False, 7, 0][5]))
    bad_row = replace(schema.get('items')[0], field(schema_row, '.index0'), True)
    refuse(lambda: model.boundary(schema_row, 1, 1, bad_row))
    bad_schema = replace(schema, 'items', (bad_row, *schema.get('items')[1:]))
    refuse(lambda: call(encode, index_fn, bad_schema, source))
    bad_member = replace(member, field(member_type, '.index1'), True)
    refuse(lambda: model.boundary(member_type, 1, 1, bad_member))

    module = 'SpecializedFamilies.Instantiation'
    encode, decode, specialize = [roots[module, op] for op in groups[module]]
    index_sig, _, _, same_type, source_type = [t for _, t in runtime(encode)]
    native_type = model.results[encode]
    member_type = field_type(source_type, '.snd')
    fibre_type = field_type(native_type, '.snd')
    carrier_type = field_type(fibre_type, '.fst')
    proof_type = field_type(fibre_type, '.snd')
    row_type = field_type(member_type, 'familyArgument6')
    additions.append('attribute def StaticFamilyPrefix { attribute key : ScalarValues::Natural; '
                     'attribute history : ScalarValues::Natural [0..*] ordered nonunique; }')
    index_fn = callback('staticFamilyIndex', index_sig, '(a0 as StaticFamilyPrefix).key')
    wrong_index_fn = callback('staticFamilyWrongIndex', index_sig, '7')
    operation = callback('staticFamilyIdentity', runtime(specialize)[-2][1], 'a0')
    refresh()
    keys, indices = (False, True), (0, 7, 10**40)
    prefixes = {i: Record('StaticFamilyPrefix', (('key', i), ('history', (i, i, 10**40)))) for i in indices}
    values = {(key, i, token): Record('StaticFamilyMember', (('key', key), ('token', token),
                ('proof', Record('StaticFamilyEvidence', (('indices', (i, i, 10**40)),)))))
              for key in keys for i in indices for token in (0, 1)}
    bindings.update(typeArgument4=keys, typeArgument5=indices, typeArgument7=tuple(prefixes.values()))
    bindings['familyArgument6'] = tuple(record(row_type, {field(row_type, '.index0'): key,
        field(row_type, '.index1'): i, field(row_type, '.value'): value})
        for (key, i, _), value in values.items())
    static_cases = {}
    for (key, i, token), value in values.items():
        member = record(member_type, {field(member_type, '.index0'): key,
                        field(member_type, '.index1'): i, field(member_type, '.value'): value})
        source = construct(source_type, key, index_fn, prefixes[i], member)
        carrier = construct(carrier_type, key, i, member)
        proof = construct(proof_type, i)
        fibre = construct(fibre_type, key, i, carrier, proof)
        expected = construct(native_type, key, index_fn, prefixes[i], fibre)
        same_key = construct(same_type, key)
        expect(call(encode, index_fn, key, key, same_key, source), expected)
        expect(call(decode, index_fn, key, key, same_key, expected), source)
        expect(call(specialize, index_fn, key, key, same_key, operation, expected), expected)
        static_cases[key, i, token] = source, expected, member, fibre, proof, same_key
    source, expected, member, fibre, proof, same_key = static_cases[False, 0, 0]
    refuse(lambda: call(encode, index_fn, False, True, same_key, source))
    refuse(lambda: call(decode, index_fn, False, True, same_key, expected))
    refuse(lambda: call(specialize, index_fn, False, True, same_key, operation, expected))
    refuse(lambda: call(encode, index_fn, False, False, static_cases[True, 0, 0][5], source))
    refuse(lambda: call(encode, wrong_index_fn, False, False, same_key, source))
    refuse(lambda: construct(source_type, False, index_fn, prefixes[0], static_cases[True, 0, 0][2]))
    refuse(lambda: construct(source_type, False, index_fn, prefixes[0], static_cases[False, 7, 0][2]))
    refuse(lambda: construct(fibre_type, False, 0, fibre.get(field(fibre_type, '.fst')),
                           static_cases[False, 7, 0][4]))
    relation = bindings['familyArgument6']
    bindings['familyArgument6'] = relation[1:]
    refuse(lambda: call(encode, index_fn, False, False, same_key, source))
    bindings['familyArgument6'] = relation

    # Each operation is checked against multiple different complete values;
    # replacing its body by another valid result must be observable.
    assert set(samples) == set(roots.values())
    for symbol, cases in samples.items():
        arguments, expected = cases[0]
        changed = next(value for _, value in cases if not same(value, expected))
        inputs, body, assertions = model.calculations[symbol]
        model.calculations[symbol] = inputs, ('literal', changed), assertions
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
    return {'operations': len(roots), 'comparisons': comparisons,
            'invalidCasesRejected': rejected, 'mutationsDetected': mutations}
