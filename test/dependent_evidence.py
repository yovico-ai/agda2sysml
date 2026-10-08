"""Check the real self Evidence carriers/selectors from parsed emitted SysML."""
import json
from pathlib import Path
from emitted_model import Extent, Model, Record, same
from open_parameters import target_name


def verify_dependent_evidence(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())

    def root(source, role):
        rows = [o for o in report['obligations'] if source + '#' in o['symbol']
                and '@' not in o['symbol'] and o['sourceKind'] == role]
        assert len(rows) == 1 and rows[0]['rule'] == 'native.open-parameters' and rows[0]['target'], ('dependent root not translated', source)
        return target_name(rows[0]['target'])

    evidence_type = root('Requirements.Evidence', 'structure')
    behavior = root('Requirements.behavior-requires-semantics', 'behavior')
    statement = root('Requirements.statement-requires-preservation', 'behavior')
    retained = root('Requirements.retained-proof-is-admissible', 'behavior')
    evidence_report = next(c for c in report['algebraicCarriers'] if target_name(c['target']) == evidence_type)
    id_field, kind_field = [target_name(i['target']).split('::')[-1] for i in evidence_report['indices']]
    tag_type = next(typ for field, typ, _, _ in model.carriers[evidence_type][1] if field == 'constructor')
    kind_type = next(typ for field, typ, _, _ in model.carriers[evidence_type][1] if field == kind_field)
    bound_rows = {f['position']: f['rowType'] for f in evidence_report['familyParameters']}
    family_reports = {c['relationParameter']: c for c in report['algebraicCarriers']
                      if c['relationParameter'] is not None
                      and c['familyParameters'][0]['rowType'] == bound_rows.get(c['relationParameter'])}
    family_types = {slot: target_name(c['target']) for slot, c in family_reports.items()}
    cases = [('structural', 'structure'), ('semantic', 'behavior'), ('statement-preserved', 'statement'),
             ('proof-retained', 'proof-source'), ('reduction-source-retained', 'reduction-source'), ('assumption-declared', 'external-assumption')]

    def field_ending(carrier, ending):
        return next(field for field, _, _, _ in model.carriers[carrier][1] if field.rsplit('#', 1)[0].endswith(ending))

    def payload(slot, identity, token):
        return Record('ProofPayload', (('family', slot), ('owner', identity), ('token', token),
                    ('nested', Record('ProofDetails', (('steps', (token, token, 10**40)),)))))

    def row(slot, identity, value):
        row_type = target_name(family_reports[slot]['familyParameters'][0]['rowType'])
        return Record(row_type, ((field_ending(row_type, '.index0'), identity), (field_ending(row_type, '.value'), value)))

    def member(slot, identity, value, extent, relations):
        typ = family_types[slot]
        return Record(typ, (('typeArgument0', extent), (f'familyArgument{slot}', relations[slot-1]),
                      (field_ending(typ, '.index0'), identity), (field_ending(typ, '.value'), value)))

    def replace(record, field, value):
        return Record(record.type, tuple((k, value if k == field else v) for k, v in record.fields))

    def ctor(slot):
        return next(c for c in evidence_report['constructors'] if f'.{cases[slot-1][0]}<' in c['target'])

    def make_evidence(slot, identity, value, extent, relations):
        constructor = ctor(slot)
        name = target_name(constructor['target'])
        fields = [(f'typeArgument0', extent)] + [(f'familyArgument{i}', relation) for i, relation in enumerate(relations, 1)]
        fields += [('constructor', tag_type + '::' + name), (id_field, identity),
                   (kind_field, kind_type + '::' + kind_type + '.' + cases[slot-1][1])]
        for c in evidence_report['constructors']:
            for i, p in enumerate(c['payload']):
                field = target_name(p['target']).split('::')[-1]
                fields.append((field, (identity if i == 0 else value) if c is constructor else ()))
        return Record(evidence_type, tuple(fields))

    comparisons = 0
    opaque_ids = [Record('DeclarationIdentity', (('name', name),)) for name in ('first', 'second', 'third')]
    domains = [(tuple((0, 7, 19)), (0, 7, 19)),
               (Extent('finite naturals', lambda x: type(x) is int and x >= 0), (0, 7, 10**40)),
               (tuple(opaque_ids), tuple(opaque_ids))]
    for extent, identities in domains:
        relations = tuple(tuple(row(slot, identity, payload(slot, identity, token)) for identity in identities for token in range(2)) for slot in range(1, 7))
        bindings = [extent, *relations]
        for identity in identities:
            for slot in range(1, 7):
                values = []
                for token in range(2):
                    native = member(slot, identity, payload(slot, identity, token), extent, relations)
                    expected = make_evidence(slot, identity, native, extent, relations)
                    actual = model.invoke(target_name(ctor(slot)['target']), bindings + [identity, native])
                    assert same(actual, expected), ('constructor lost index/kind/payload', slot, identity)
                    values.append(actual)
                    comparisons += 1
                    if slot in (2, 3):
                        selected = model.invoke(behavior if slot == 2 else statement, bindings + [identity, actual])
                        assert same(selected, native), 'selector changed proof payload or family/index'
                        comparisons += 1
                    if slot == 4:
                        wrapped = model.invoke(retained, bindings + [identity, native])
                        assert same(wrapped, expected), 'retention wrapper changed complete evidence'
                        comparisons += 1
                assert not same(values[0], values[1]), 'distinct proof-relevant values collapsed'

    extent, identities = domains[0]
    relations = tuple(tuple(row(slot, identity, payload(slot, identity, token)) for identity in identities for token in range(2)) for slot in range(1, 7))
    bindings = [extent, *relations]
    native = member(2, 0, payload(2, 0, 0), extent, relations)
    evidence = make_evidence(2, 0, native, extent, relations)
    rejected_count = 0

    def rejected(action):
        nonlocal rejected_count
        try:
            action()
        except AssertionError:
            rejected_count += 1
            return
        raise AssertionError('invalid dependent evidence was admitted')

    rejected(lambda: model.invoke(behavior, bindings + [7, evidence]))
    wrong_kind = replace(evidence, kind_field, kind_type + '::' + kind_type + '.statement')
    rejected(lambda: model.boundary(evidence_type, 1, 1, wrong_kind))
    rejected(lambda: model.invoke(behavior, bindings + [0, make_evidence(3, 0, member(3, 0, payload(3, 0, 0), extent, relations), extent, relations)]))
    rejected(lambda: model.invoke(target_name(ctor(2)['target']), bindings + [0, member(3, 0, payload(3, 0, 0), extent, relations)]))
    rejected(lambda: model.invoke(target_name(ctor(2)['target']), bindings + [0, member(2, 0, payload(2, 0, 99), extent, relations)]))
    empty_relations = ((),) * 6
    rejected(lambda: model.invoke(target_name(ctor(2)['target']), [extent, *empty_relations, 0, member(2, 0, payload(2, 0, 0), extent, empty_relations)]))
    bad_domain = list(relations); bad_domain[0] += (row(1, 1000, payload(1, 1000, 0)),)
    rejected(lambda: model.invoke(target_name(ctor(2)['target']), [extent, *bad_domain, 0, native]))
    narrow = list(relations); narrow[1] = relations[1][:1]
    wrong_binding = make_evidence(2, 0, member(2, 0, payload(2, 0, 0), extent, narrow), extent, relations)
    rejected(lambda: model.boundary(evidence_type, 1, 1, wrong_binding))
    reverse = tuple(tuple(reversed(r)) for r in relations)
    model.invoke(target_name(ctor(2)['target']), bindings + [0, member(2, 0, payload(2, 0, 0), extent, reverse)])

    # Remove a binding assertion from the actual parsed carrier constraint.
    # The same structurally valid but wrongly bound proof then becomes admitted.
    validity = target_name(evidence_report['admissibility'])
    inputs, body, assertions = model.calculations[validity]
    def remove_binding(ast):
        if ast[0] == 'call' and ast[1] == 'SequenceFunctions::includesOnly' and 'familyArgument2' in repr(ast):
            return ('literal', True)
        return tuple(remove_binding(x) if isinstance(x, tuple) and x and isinstance(x[0], str) else
                     [remove_binding(y) if isinstance(y, tuple) else y for y in x] if isinstance(x, list) else x for x in ast)
    changed = remove_binding(body)
    assert changed != body, 'binding mutation missed the emitted constraint'
    model.calculations[validity] = (inputs, changed, assertions)
    model.boundary(evidence_type, 1, 1, wrong_binding)
    model.calculations[validity] = (inputs, body, assertions)
    return {'constructors': 6, 'selectorsAndWrapping': 3, 'comparisons': comparisons,
            'invalidCasesRejected': rejected_count, 'distinctProofsPreserved': True,
            'infiniteIndexDomain': True, 'bindingMutationDetected': True,
            'source': 'parsed emitted SysML'}


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_dependent_evidence(sys.argv[1]), indent=2))
