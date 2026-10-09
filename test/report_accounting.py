"""Evaluate existing accounting operations from their emitted SysML contracts."""
from functools import lru_cache
import itertools
import json
from pathlib import Path
from emitted_model import Extent, Model, Record, same
from open_parameters import target_name


def verify_report_accounting(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    prefix = 'Agda2SysML.Diagnostics.Accounting.'
    roots = {}
    for operation in ('before-count', 'after-count', 'Before.sources', 'After.sources'):
        rows = [o for o in report['obligations'] if o['symbol'].startswith(prefix + operation + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], operation
        roots[operation] = target_name(rows[0]['target'])
        assert len([f for f, _, _, _ in model.calculations[roots[operation]][0]
                    if f.startswith('input')]) == 2, 'unused function leaked into runtime inputs'

    uncached = model.invoke
    @lru_cache(maxsize=32768)
    def invoke(symbol, arguments, check, depth):
        return uncached(symbol, arguments, check, depth)
    model.invoke = lambda symbol, arguments, check=True, depth=0: invoke(symbol, tuple(arguments), check, depth)
    model.boundary = lru_cache(maxsize=32768)(model.boundary)

    def constructor(typ, stem):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if c['symbol'].startswith('Agda2SysML.Coverage.Inventory.' + stem + '#')]
        assert len(matches) == 1, (typ, stem, matches)
        return matches[0]

    def field(typ, suffix):
        matches = [(f, t) for f, t, _, _ in model.carriers[typ][1]
                   if f.split('<', 1)[0].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    comparisons = refusals = 0
    def refuse(action):
        nonlocal refusals
        try:
            action()
        except AssertionError:
            refusals += 1
            return
        raise AssertionError('invalid accounting input admitted')

    reasons_a = tuple(Record('BeforeReason', (('code', n), ('detail', (n, n)))) for n in range(2))
    reasons_b = tuple(Record('AfterReason', (('code', n), ('detail', (n, n)))) for n in range(2))
    for side, count_name, sources_name, reasons in (
            ('before', 'before-count', 'Before.sources', reasons_a),
            ('after', 'after-count', 'After.sources', reasons_b)):
        count, sources = roots[count_name], roots[sources_name]
        ids_type = model.calculations[count][0][-2][1]
        report_type = model.calculations[count][0][-1][1]
        empty = constructor(report_type, 'Report.empty')
        entry = constructor(report_type, 'Report.entry')
        entry_type = model.calculations[entry][0][-2][1]
        translated = constructor(entry_type, 'Entry.translated')
        textual = constructor(entry_type, 'Entry.textual')
        evidence_type = model.calculations[translated][0][-1][1]
        evidence_index, _ = field(evidence_type, '.index0')
        evidence_value, _ = field(evidence_type, '.value')
        row_type = next(t for f, t, _, _ in model.carriers[evidence_type][1] if f == 'familyArgument3')
        row_index, _ = field(row_type, '.index0')
        row_value, _ = field(row_type, '.value')
        for identities in ((False, True), (0, 9, 10**40)):
            extent = identities if type(identities[0]) is bool else Extent('all natural identities', lambda x: type(x) is int and x >= 0)
            payloads = {i: Record('Evidence', (('identity', i), ('payload', (i, i, 10**40)))) for i in identities}
            relation = tuple(Record(row_type, ((row_index, i), (row_value, payloads[i]))) for i in identities)
            bindings = {'typeArgument0': extent, 'typeArgument1': reasons_a,
                        'typeArgument2': reasons_b, 'familyArgument3': relation}

            def call(symbol, args):
                return model.invoke(symbol, [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0] if f in bindings], *args])

            def ids(items):
                return Record(ids_type, (('typeArgument0', extent), ('items', tuple(items))))

            def evidence(i):
                return Record(evidence_type, (('typeArgument0', extent), ('familyArgument3', relation),
                              (evidence_index, i), (evidence_value, payloads[i])))

            def build(items, statuses):
                if not items:
                    return call(empty, [])
                i, rest = items[0], items[1:]
                value = call(translated, [i, evidence(i)]) if statuses[0] else call(textual, [i, reasons[len(rest) % 2]])
                return call(entry, [i, ids(rest), value, build(rest, statuses[1:])])

            layouts = ((), (identities[0],), (identities[1], identities[0]),
                       (identities[0],) * 3, (identities[1], identities[0], identities[1], identities[0]))
            for items in layouts:
                for statuses in itertools.product((False, True), repeat=len(items)):
                    value = build(items, statuses)
                    assert call(count, [ids(items), value]) == sum(statuses), (side, items, statuses)
                    assert same(call(sources, [ids(items), value]), ids(items)), (side, items, statuses)
                    comparisons += 2

            items = (identities[0], identities[1])
            value = build(items, (True, False))
            for operation in (count, sources):
                refuse(lambda operation=operation: call(operation, [ids(items[::-1]), value]))
                refuse(lambda operation=operation: call(operation, [ids(items[:1]), value]))
            refuse(lambda: call(translated, [identities[0], evidence(identities[1])]))
            refuse(lambda: call(textual, [identities[0], Record('UnknownReason', (('code', 99),))]))
            wrong_member = Record(evidence_type, (('typeArgument0', extent), ('familyArgument3', relation),
                (evidence_index, identities[0]), (evidence_value, Record('UnknownEvidence', ()))))
            refuse(lambda: call(translated, [identities[0], wrong_member]))

    return {'operations': len(roots), 'comparisons': comparisons, 'invalidCasesRejected': refusals,
            'repeatedIdentitiesPreserved': True, 'unusedRuntimeInputs': 0}
