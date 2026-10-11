"""Execute existing universe-polymorphic operations from emitted SysML.

Source names select acceptance cases only. No fixed-level source adapters are
introduced and no checked Agda expressions are used as an execution shortcut.
"""
import itertools
import json
from pathlib import Path
from emitted_model import Extent, Model, Record, same
from open_parameters import target_name


def verify_symbolic_levels(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    roots = {}
    comparisons = rejected = 0

    def operation(source):
        rows = [r for r in report['obligations'] if r['symbol'].startswith('Agda2SysML.' + source + '#')
                and '@' not in r['symbol'] and r['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], source
        symbol = target_name(rows[0]['target'])
        roots[source] = symbol
        return symbol

    def compare(actual, expected):
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
        raise AssertionError('invalid input admitted')

    def fields(typ):
        return model.carriers[typ][1]

    def field(typ, suffix):
        matches = [f for f, _, _, _ in fields(typ) if f.endswith(suffix) or f.split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def change(value, key, replacement):
        return Record(value.type, tuple((k, replacement if k == key else v) for k, v in value.fields))

    def constructor(typ, suffix=None):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if suffix is None or c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def invoke(symbol, bindings, *values):
        parameters = [bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                      if f.startswith(('typeArgument', 'familyArgument'))]
        return model.invoke(symbol, [*parameters, *values])

    sequence_ops = {s: operation('SequenceValues.' + s)
                    for s in ('encode', 'decode', 'length', 'size', '_++_', 'append')}
    sequence_laws = {}
    for name in ('source-roundtrip', 'target-roundtrip', 'length-preserves', 'append-preserves'):
        rows = [r for r in report['nativeStatements']
                if r['symbol'].startswith('Agda2SysML.SequenceValues.' + name + '#')]
        assert len(rows) == 1 and rows[0]['status'] == 'translated', name
        sequence_laws[name] = target_name(rows[0]['target'])
    list_type = model.calculations[sequence_ops['encode']][0][-1][1]
    seq_type = model.results[sequence_ops['encode']]
    slot = next(f for f, _, _, _ in fields(list_type) if f.startswith('typeArgument'))
    empty, prepend = (constructor(seq_type, suffix) for suffix in ('.empty', '.prepend'))
    opaque = tuple(Record('Opaque', (('identity', n), ('evidence', (n, n, 10**40)))) for n in range(3))
    for domain in ((False, True), opaque, (0, 7, 10**40)):
        extent = Extent('naturals', lambda x: type(x) is int and x >= 0) if type(domain[0]) is int else domain
        bindings = {slot: extent}
        listing = lambda xs: Record(list_type, ((slot, extent), ('items', tuple(xs))))

        def sequence(xs):
            result = invoke(empty, bindings)
            for value in reversed(xs):
                result = invoke(prepend, bindings, value, result)
            return result

        samples = [xs for n in range(4) for xs in itertools.product(domain, repeat=n)]
        for xs in samples:
            source, target = listing(xs), sequence(xs)
            compare(invoke(sequence_ops['encode'], bindings, source), target)
            compare(invoke(sequence_ops['decode'], bindings, target), source)
            compare(invoke(sequence_ops['length'], bindings, source), len(xs))
            compare(invoke(sequence_ops['size'], bindings, target), len(xs))
            for name, value in (('source-roundtrip', source), ('target-roundtrip', target),
                                ('length-preserves', source)):
                compare(invoke(sequence_laws[name], bindings, value), True)
        for xs, ys in itertools.product(samples[:7], repeat=2):
            compare(invoke(sequence_ops['_++_'], bindings, listing(xs), listing(ys)), listing(xs + ys))
            compare(invoke(sequence_ops['append'], bindings, sequence(xs), sequence(ys)), sequence(xs + ys))
            compare(invoke(sequence_laws['append-preserves'], bindings, listing(xs), listing(ys)), True)
        refuse(lambda: invoke(sequence_ops['encode'], bindings, change(listing(domain), slot, ())))
        target = sequence(domain[:2])
        refuse(lambda: invoke(sequence_ops['decode'], bindings,
                              change(target, field(seq_type, '.node-count'), 0)))
        refuse(lambda: invoke(sequence_ops['append'], bindings,
                              change(target, slot, ()), sequence(())))

        symbol = sequence_ops['_++_']
        saved = model.calculations[symbol]
        model.calculations[symbol] = (saved[0], ('reference', 'input0'), saved[2])
        try:
            refuse(lambda: compare(invoke(symbol, bindings, listing(domain), listing(domain)), listing(domain + domain)))
        finally:
            model.calculations[symbol] = saved

    # Public constructors copied by a module application must resolve to real
    # canonical constructor calculations at that application's parameter slots.
    # Read those targets from source correspondence, then check complete values
    # against an independent sequence construction plan.
    alias_rows = [r for r in report['obligations']
                  if r['symbol'].startswith('Agda2SysML.SchemaConcatenation._#')
                  and r['sourceKind'] == 'structure'
                  and r['symbol'].rsplit('.', 1)[-1].split('#', 1)[0] in ('empty', 'prepend')]
    assert len(alias_rows) == 4
    aliases = {}
    for row in alias_rows:
        assert row['status'] == 'discharged' and row['target'], ('missing constructor root', row['symbol'])
        assert row['source']['checkedDefinition'] == row['symbol'], 'alias provenance replaced'
        name = row['symbol'].rsplit('.', 1)[-1].split('#', 1)[0]
        aliases.setdefault(name, set()).add(target_name(row['target']))
    assert all(len(targets) == 1 for targets in aliases.values()), 'equivalent aliases split identities'
    alias_empty, alias_prepend = (next(iter(aliases[name])) for name in ('empty', 'prepend'))
    alias_type = model.results[alias_empty]
    assert alias_type == model.results[alias_prepend]
    alias_slot = model.calculations[alias_empty][0][0][0]
    assert alias_slot != slot, 'module parameter telescope was not instantiated'
    alias_comparisons = 0
    for domain in ((False, True), (0, 7, 10**40), opaque):
        def expected_sequence(xs):
            return Record(alias_type, ((alias_slot, domain),
                ('constructor', alias_type + '.constructor-tag::' + (alias_prepend if xs else alias_empty)),
                (alias_type + '.node-count', len(xs) + 1),
                (alias_prepend + '.payload0', xs[0] if xs else ()),
                (alias_prepend + '.payload1', expected_sequence(xs[1:]) if xs else ())))

        for n in range(4):
            for xs in itertools.product(domain, repeat=n):
                actual = model.invoke(alias_empty, [domain])
                for value in reversed(xs):
                    actual = model.invoke(alias_prepend, [domain, value, actual])
                compare(actual, expected_sequence(xs))
                alias_comparisons += 1
        refuse(lambda: model.invoke(alias_prepend, [domain, Record('Outside', ()), expected_sequence(())]))
        refuse(lambda: model.invoke(alias_prepend, [domain[:1], domain[0], expected_sequence(domain)]))
        refuse(lambda: model.invoke(alias_prepend,
                                    [domain, domain[0], change(expected_sequence(()), alias_type + '.node-count', 0)]))
    saved = model.calculations[alias_prepend]
    model.calculations[alias_prepend] = (saved[0], ('reference', 'input1'), saved[2])
    try:
        refuse(lambda: compare(model.invoke(alias_prepend, [domain, domain[0], expected_sequence(())]),
                               expected_sequence((domain[0],))))
    finally:
        model.calculations[alias_prepend] = saved

    for prefix in ('DependentFamilies.Family.', 'DependentRecords.Record.F.'):
        encode, decode = (operation(prefix + s) for s in ('encode', 'decode'))
        member_type = model.calculations[encode][0][-1][1]
        fibre_type = model.results[encode]
        index_slot = next(f for f, _, _, _ in fields(member_type) if f.startswith('typeArgument'))
        family_slot, row_type = next((f, t) for f, t, _, _ in fields(member_type) if f.startswith('familyArgument'))
        member_index, member_value = field(member_type, '.index0'), field(member_type, '.value')
        row_index, row_value = field(row_type, '.index0'), field(row_type, '.value')
        first, second = [f for f, _, _, _ in fields(fibre_type)
                         if f.startswith(('Agda.Builtin.Sigma.Σ.fst<', 'Agda.Builtin.Sigma.Σ.snd<'))]
        carrier_type = next(t for f, t, _, _ in fields(fibre_type) if f == first)
        proof_type = next(t for f, t, _, _ in fields(fibre_type) if f == second)
        for domain in ((False, True), (0, 7, 10**40), opaque):
            payloads = {(i, n): Record('Payload', (('index', i), ('history', (n, n, 10**40))))
                        for i in domain for n in range(3)}
            relation = tuple(Record(row_type, ((row_index, i), (row_value, value)))
                             for (i, _), value in payloads.items())
            bindings = {f: opaque for f, _, _, _ in model.calculations[encode][0] if f.startswith('typeArgument')}
            bindings.update({index_slot: domain, family_slot: relation})

            def member(index, n):
                return Record(member_type, ((index_slot, domain), (family_slot, relation),
                                            (member_index, index), (member_value, payloads[index, n])))

            def construct(typ, *values):
                return invoke(constructor(typ), bindings, *values)

            for index, n in itertools.product(domain, range(3)):
                value = member(index, n)
                carrier = construct(carrier_type, index, value)
                proof = construct(proof_type, index)
                expected = construct(fibre_type, index, carrier, proof)
                compare(invoke(encode, bindings, index, value), expected)
                compare(invoke(decode, bindings, index, expected), value)
            index, other = domain[:2]
            value = member(index, 0)
            carrier = construct(carrier_type, index, value)
            proof = construct(proof_type, index)
            native = construct(fibre_type, index, carrier, proof)
            refuse(lambda: invoke(encode, bindings, other, value))
            refuse(lambda: invoke(decode, bindings, other, native))
            refuse(lambda: invoke(decode, bindings, index,
                                  change(native, second, construct(proof_type, other))))
            refuse(lambda: invoke(decode, bindings, index,
                                  change(native, field(fibre_type, '.capture0'), other)))
            refuse(lambda: invoke(encode, {**bindings, family_slot: ()}, index, value))

    assert len(roots) == 10
    return {'operations': len(roots), 'comparisons': comparisons, 'invalidCasesRejected': rejected,
            'nativeStatementsExercised': len(sequence_laws), 'bodyMutationDetected': True,
            'constructorAliasRoots': len(alias_rows), 'constructorAliasComparisons': alias_comparisons,
            'constructorAliasMutationDetected': True,
            'completeValuesAndEvidencePreserved': True, 'source': 'parsed emitted SysML'}


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_symbolic_levels(sys.argv[1]), indent=2))
