"""Execute the existing dependent-record adapter through its closed-level API."""
import itertools
import json
from pathlib import Path
from emitted_model import Extent, Model, Record, same
from open_parameters import target_name


def verify_dependent_record_path(output, model_file='model.sysml', report_file='correspondence.json'):
    output = Path(output)
    report = json.loads((output / report_file).read_text())
    model = Model((output / model_file).read_text())
    prefix = 'Agda2SysML.DependentRecords.KnownProjection.'
    roots = {}
    for operation in ('encode', 'decode', 'forgetInput', 'admitInput', 'Bound.input-contract-required'):
        rows = [o for o in report['obligations'] if o['symbol'].startswith(prefix + operation + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], ('record operation missing', operation, rows)
        roots[operation] = target_name(rows[0]['target'])
    laws = {}
    for law in ('prefix-preserves', 'encode-decode', 'input-contract-sufficient'):
        rows = [o for o in report['nativeStatements']
                if o['symbol'].startswith(prefix + 'Bound.' + law + '#') and '@' not in o['symbol']]
        assert len(rows) == 1 and rows[0]['status'] == 'translated' and rows[0]['target'], ('record law missing', law, rows)
        laws[law] = target_name(rows[0]['target'])

    source_type = model.calculations[roots['encode']][0][-1][1]
    native_type = model.results[roots['encode']]
    raw_type = model.results[roots['forgetInput']]
    proof_type = model.calculations[roots['admitInput']][0][-1][1]
    def fields(typ):
        return [f for f, _, _, _ in model.carriers[typ][1] if '.fst<' in f or '.snd<' in f]
    def field_type(typ, field):
        return next(t for f, t, _, _ in model.carriers[typ][1] if f == field)
    source_first, source_second = fields(source_type)
    native_first, native_second = fields(native_type)
    raw_first, raw_second = fields(raw_type)
    prefix_type = field_type(source_type, source_first)
    member_type = field_type(source_type, source_second)
    fibre_type = field_type(native_type, native_second)
    carrier_type = field_type(raw_type, raw_second)
    # Aggregate generation disambiguates shared family names with schema hashes.
    def family_field(typ, suffix):
        matches = [f for f, _, _, _ in model.carriers[typ][1]
                   if f.split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, ('ambiguous family field', typ, suffix, matches)
        return matches[0]
    member_index = family_field(member_type, '.index0')
    member_value = family_field(member_type, '.value')
    row_type = next(t for f, t, _, _ in model.carriers[member_type][1] if f == 'familyArgument2')
    row_index = family_field(row_type, '.index0')
    row_value = family_field(row_type, '.value')

    constructors = {target_name(c['target']): target_name(sh['target'])
                    for sh in report['algebraicCarriers'] for c in sh['constructors']}
    def construct(typ, values, bindings):
        names = [s for s, result in constructors.items() if result == typ]
        assert len(names) == 1, ('ambiguous record/equality constructor', typ, names)
        symbol = names[0]
        parameters = [bindings[field] for field, _, _, _ in model.calculations[symbol][0] if field in bindings]
        return model.invoke(symbol, [*parameters, *values])
    def replace(record, field, value):
        return Record(record.type, tuple((k, value if k == field else v) for k, v in record.fields))
    rejected = comparisons = statement_comparisons = mutations = 0
    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('inconsistent dependent record was admitted')

    contexts = tuple(Record('Context', (('owner', owner), ('history', (owner, owner, 10**40)))) for owner in ('a', 'b'))
    for indices in ((False, True), (0, 7, 10**40)):
        extent = indices if type(indices[0]) is bool else Extent('all natural indices', lambda x: type(x) is int and x >= 0)
        payloads = {(index, token): Record('Member', (('token', token),
                    ('nested', Record('Evidence', (('index', index), ('steps', (token, token, 10**40)))))))
                    for index in indices for token in range(3)}
        relation = tuple(Record(row_type, ((row_index, index), (row_value, payload)))
                         for (index, _), payload in payloads.items())
        bindings = {'typeArgument0': contexts, 'typeArgument1': extent, 'familyArgument2': relation}
        call_bindings = [bindings[f] for f, _, _, _ in model.calculations[roots['encode']][0] if f in bindings]
        def member(index, token):
            return Record(member_type, (('typeArgument1', extent), ('familyArgument2', relation),
                          (member_index, index), (member_value, payloads[index, token])))
        for context, index, token in itertools.product(contexts, indices, range(3)):
            p = construct(prefix_type, [context, index], bindings)
            m = member(index, token)
            source = construct(source_type, [p, m], bindings)
            carrier = construct(carrier_type, [index, m], bindings)
            proof = construct(proof_type, [index], bindings)
            fibre = construct(fibre_type, [index, carrier, proof], bindings)
            expected = construct(native_type, [p, fibre], bindings)
            raw = construct(raw_type, [p, carrier], bindings)
            encoded = model.invoke(roots['encode'], [*call_bindings, source])
            assert same(encoded, expected), 'encode changed context, member, index or equality evidence'
            assert same(model.invoke(roots['decode'], [*call_bindings, expected]), source), 'decode changed complete source record'
            assert same(model.invoke(roots['forgetInput'], [*call_bindings, expected]), raw), 'forgetInput changed prefix or carrier'
            assert same(model.invoke(roots['admitInput'], [*call_bindings, raw, proof]), expected), 'admission changed complete native record'
            assert same(model.invoke(roots['Bound.input-contract-required'], [*call_bindings, expected]), proof), \
                'required input contract changed the complete equality evidence'
            for law, values in (('prefix-preserves', [source]), ('encode-decode', [expected]),
                                ('input-contract-sufficient', [raw, proof])):
                assert model.invoke(laws[law], [*call_bindings, *values]) is True, ('record constraint failed', law)
                statement_comparisons += 1
            comparisons += 5

        index, other = indices[:2]
        p = construct(prefix_type, [contexts[0], index], bindings)
        m = member(index, 0)
        carrier = construct(carrier_type, [index, m], bindings)
        proof = construct(proof_type, [index], bindings)
        fibre = construct(fibre_type, [index, carrier, proof], bindings)
        native = construct(native_type, [p, fibre], bindings)
        raw = construct(raw_type, [p, carrier], bindings)
        wrong_carrier = construct(carrier_type, [other, member(other, 0)], bindings)
        wrong_raw = construct(raw_type, [p, wrong_carrier], bindings)
        wrong_proof = construct(proof_type, [other], bindings)
        # Mutate actual parsed target bodies: wrong evidence and a false law
        # must both be detected by the behavior/contract checks.
        source = construct(source_type, [p, m], bindings)
        for symbol, args, wrong, expected in (
                (roots['Bound.input-contract-required'], [*call_bindings, native], wrong_proof, proof),
                (laws['prefix-preserves'], [*call_bindings, source], False, True),
                (laws['encode-decode'], [*call_bindings, native], False, True),
                (laws['input-contract-sufficient'], [*call_bindings, raw, proof], False, True)):
            saved = model.calculations[symbol]
            model.calculations[symbol] = (saved[0], ('literal', wrong), saved[2])
            try:
                try:
                    actual = model.invoke(symbol, args)
                except AssertionError:
                    mutations += 1
                else:
                    assert not same(actual, expected), 'schema-boundary body mutation escaped verification'
                    mutations += 1
            finally:
                model.calculations[symbol] = saved
        refuse(lambda: model.invoke(roots['admitInput'], [*call_bindings, wrong_raw, proof]))
        refuse(lambda: model.invoke(laws['input-contract-sufficient'], [*call_bindings, wrong_raw, proof]))
        refuse(lambda: model.invoke(roots['admitInput'], [*call_bindings, construct(raw_type, [p, carrier], bindings), wrong_proof]))
        capture = next(f for f, _, _, _ in model.carriers[fibre_type][1] if '.capture0' in f)
        refuse(lambda: model.invoke(roots['decode'], [*call_bindings, replace(native, native_second, replace(fibre, capture, other))]))
        refuse(lambda: model.invoke(laws['encode-decode'], [*call_bindings, replace(native, native_second, replace(fibre, capture, other))]))
        refuse(lambda: model.invoke(roots['encode'], [*call_bindings, construct(source_type, [p, member(other, 0)], bindings)]))
        outside_context = construct(prefix_type, [contexts[1], index], bindings)
        outside_source = construct(source_type, [outside_context, m], bindings)
        narrowed_context = [contexts[:1], *call_bindings[1:]]
        refuse(lambda: model.invoke(roots['encode'], [*narrowed_context, outside_source]))
        narrowed_family = [*call_bindings[:-1], relation[:1]]
        refuse(lambda: model.invoke(roots['encode'], [*narrowed_family, construct(source_type, [p, member(index, 0)], bindings)]))
    return {'comparisons': comparisons, 'invalidCasesRejected': rejected, 'operations': len(roots),
            'nativeStatements': len(laws), 'statementComparisons': statement_comparisons, 'bodyMutationsDetected': mutations}
