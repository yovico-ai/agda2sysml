"""Execute the existing finite-natural adapter and arithmetic from native SysML."""
import itertools
import json
from pathlib import Path
from emitted_model import Model, Record, same
from open_parameters import target_name


def verify_natural_values(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    prefix = 'Agda2SysML.NaturalValues.'
    roots = {}
    for operation in ('encode', 'decode', 'successor', 'add', 'multiply', 'subtract', 'equal', 'less'):
        rows = [o for o in report['obligations'] if o['symbol'].startswith(prefix + operation + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], ('missing natural operation', operation)
        roots[operation] = target_name(rows[0]['target'])

    def field(typ, suffix):
        matches = [(f, t) for f, t, _, _ in model.carriers[typ][1] if f.split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def constructor(source):
        rows = [c for shape in report['algebraicCarriers'] for c in shape['constructors']
                if c['symbol'].startswith(prefix + source + '#')]
        assert len(rows) == 1, (source, rows)
        return rows[0]

    native_type = model.results[roots['encode']]
    value_field, extended_type = field(native_type, '.value')
    proof_field, proof_type = field(native_type, '.finite-proof')
    index_field, _ = field(proof_type, '.index0')
    finite_constructor = constructor('ExtendedNatural.finite')
    infinity_constructor = constructor('ExtendedNatural.infinity')
    proof_constructor = constructor('IsFinite.finite-value')
    value_payload = target_name(finite_constructor['payload'][0]['target']).rsplit('::', 1)[-1]
    proof_payload = target_name(proof_constructor['payload'][0]['target']).rsplit('::', 1)[-1]

    def tag(typ, con):
        _, tag_type = field(typ, 'constructor')
        return ('constructor', tag_type + '::' + target_name(con['target']))

    def finite(n):
        return Record(extended_type, (tag(extended_type, finite_constructor), (value_payload, n)))

    def evidence(n, index=None):
        return Record(proof_type, (tag(proof_type, proof_constructor),
                      (index_field, finite(n if index is None else index)), (proof_payload, n)))

    def native(n):
        return Record(native_type, ((value_field, finite(n)), (proof_field, evidence(n))))

    values = (0, 1, 2, 7, 10**40, 10**40 + 1, 2**128, 2**128 + 1)
    comparisons = 0
    for n in values:
        assert same(model.invoke(roots['encode'], [n]), native(n)), 'encoding changed value or complete evidence'
        assert model.invoke(roots['decode'], [native(n)]) == n, 'decoding changed the finite payload'
        assert same(model.invoke(roots['successor'], [native(n)]), native(n + 1)), 'successor changed its complete result'
        comparisons += 3
    for a, b in itertools.product(values, repeat=2):
        for operation, expected in (('add', native(a + b)), ('multiply', native(a * b)),
                                    ('subtract', native(max(0, a - b))), ('equal', a == b), ('less', a < b)):
            assert same(model.invoke(roots[operation], [native(a), native(b)]), expected), ('natural operation', operation, a, b)
            comparisons += 1

    infinity = Record(extended_type, (tag(extended_type, infinity_constructor),))
    invalid = (
        Record(native_type, ((value_field, infinity), (proof_field, evidence(0)))),
        Record(native_type, ((value_field, finite(7)), (proof_field, evidence(8)))),
        Record(native_type, ((value_field, finite(7)), (proof_field, evidence(7, 8)))),
        native(-1), native(float('inf')), Record(native_type, ((value_field, finite(0)),)),
    )
    for value in invalid:
        try:
            model.invoke(roots['decode'], [value])
        except AssertionError:
            continue
        raise AssertionError('invalid natural value/evidence admitted')
    return {'operations': len(roots), 'comparisons': comparisons, 'invalidCasesRejected': len(invalid)}
