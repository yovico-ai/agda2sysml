"""Execute the dependent computation laws admitted by cross-scope inference."""
import json
from pathlib import Path
from emitted_model import BodyCalculation, Extent, Model, Record
from open_parameters import target_name


def verify_family_scope(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    roots = {}
    for law in ('beta', 'record-field-computation'):
        rows = [r for r in report['nativeStatements']
                if r['symbol'].startswith('Agda2SysML.DefinitionalReduction.' + law + '#')]
        assert len(rows) == 1 and rows[0]['status'] == 'translated', (law, rows)
        roots[law] = target_name(rows[0]['target'])

    def field(typ, suffix):
        names = [f for f, _, _, _ in model.carriers[typ][1]
                 if f.split('#', 1)[0].split('<', 1)[0].endswith(suffix)]
        assert len(names) == 1, (typ, suffix, names)
        return names[0]

    def row(typ, index, value):
        return Record(typ, ((field(typ, '.index0'), index), (field(typ, '.value'), value)))

    def member(typ, bindings, index, value):
        return Record(typ, tuple((f, bindings[f]) for f, _, _, _ in model.carriers[typ][1]
                                if f in bindings)
                      + ((field(typ, '.index0'), index), (field(typ, '.value'), value)))

    def callback(signature, value):
        # A supplied constant calculation with the actual emitted signature.
        # The law's dependent callback contracts still check its result index.
        return BodyCalculation(tuple(('x' + str(i), t) for i, t in enumerate(signature.arguments)),
                               signature.result, ('reference', 'captured'), {'captured': value})

    comparisons = rejected = mutations = 0

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('incompatible dependent callback result was admitted')

    opaque = tuple(Record('Context', (('id', i), ('history', (i, i, 10**40)))) for i in ('a', 'b'))
    for values in (opaque, (0, 7, 10**40)):
        extent = values if isinstance(values[0], Record) else Extent('naturals', lambda x: type(x) is int and x >= 0)
        for index in values:
            other = next(v for v in values if v != index)
            for token in range(3):
                payload = Record('Payload', (('token', token), ('evidence', (index, index, 10**40))))
                for law, symbol in roots.items():
                    inputs = model.calculations[symbol][0]
                    bindings = {}
                    if law == 'beta':
                        body_sig, argument_sig = inputs[-3][1], inputs[-2][1]
                        bindings['typeArgument1'] = extent
                        # Keep the member valid in its own family, then reject
                        # it at the dependent callback's expected input index.
                        bindings['familyArgument2'] = tuple(row(inputs[1][1], x, payload) for x in (index, other))
                        a = member(argument_sig.result, bindings, index, payload)
                        pair_type = body_sig.arguments[0]
                        pair = Record(pair_type, tuple(bindings.items())
                                      + ((field(pair_type, '.fst'), index), (field(pair_type, '.snd'), a)))
                        bindings['familyArgument3'] = (row(inputs[2][1], pair, payload),)
                        b = member(body_sig.result, bindings, pair, payload)
                        callbacks = [callback(body_sig, b), callback(argument_sig, a)]
                        wrong = member(argument_sig.result, bindings, other, payload)
                        bad_callbacks = [callbacks[0], callback(argument_sig, wrong)]
                    else:
                        first_sig, second_sig = inputs[-3][1], inputs[-2][1]
                        bindings = {'typeArgument1': extent, 'typeArgument2': extent,
                                    'familyArgument3': tuple(row(inputs[2][1], x, payload) for x in (index, other))}
                        b = member(second_sig.result, bindings, index, payload)
                        callbacks = [callback(first_sig, index), callback(second_sig, b)]
                        wrong = member(second_sig.result, bindings, other, payload)
                        bad_callbacks = [callbacks[0], callback(second_sig, wrong)]
                    static = [bindings[f] for f, _, _, _ in inputs if f in bindings]
                    args = [*static, *callbacks, index]
                    assert model.invoke(symbol, args) is True, law
                    comparisons += 1
                    refuse(lambda: model.invoke(symbol, [*static, *bad_callbacks, index]))
                    saved = model.calculations[symbol]
                    model.calculations[symbol] = (saved[0], ('literal', False), saved[2])
                    try:
                        assert model.invoke(symbol, args) is False, 'false law mutation escaped'
                        mutations += 1
                    finally:
                        model.calculations[symbol] = saved
    return {'nativeStatements': len(roots), 'comparisons': comparisons,
            'invalidBindingsRejected': rejected, 'bodyMutationsDetected': mutations}
