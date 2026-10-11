"""Exercise original unary callback operations through parsed native SysML."""
import itertools
import json
from pathlib import Path
from emitted_model import CalculationValue, CallableSignature, Extent, Model, Record, same
from open_parameters import target_name


SOURCES = ('BooleanLowering.map', 'Diagnostics.Accounting.mapEntry',
           'Diagnostics.Accounting.mapReport', 'Diagnostics.Located.annotate',
           'NaturalValues.caseNat', 'NaturalValues.nativeCase',
           'SourceAlignment.Direct.mapMaybe', 'SourceAlignment.Direct.rename')


def verify_native_callbacks(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    roots = {}
    for source in SOURCES:
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.' + source + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], source
        roots[source] = target_name(rows[0]['target'])
    model = Model(text)
    for symbol in roots.values():
        assert sum(isinstance(t, CallableSignature) for _, t, _, _ in model.calculations[symbol][0]) == 1

    def quote(s):
        return "'" + s.replace('\\', '\\\\').replace("'", "\\'") + "'"

    # Supplied callbacks are native calculation bodies parsed by the same
    # independent oracle. No host-language callback substitutes for invocation.
    additions = []
    def callback(symbol, domain, result, body):
        additions.append(f"calc def {quote(symbol)} {{ in x : {domain} [1]; "
                         f"return result : {result} [1] = {body}; }}")
        return CalculationValue(symbol)

    natural = 'ScalarValues::Natural'
    any_value = 'Base::Anything'
    increment = callback('testIncrement', natural, natural, 'x + 1')
    double = callback('testDouble', natural, natural, 'x * 2')
    identity = callback('testIdentity', any_value, any_value, 'x')
    wrong_boolean = callback('testWrongBoolean', any_value, 'ScalarValues::Boolean', 'true')
    wrap = callback('testWrap', any_value, any_value, "new 'CallbackPayload'('value' = x)")
    additions.append("attribute def 'CallbackPayload' { attribute 'value' : Base::Anything [1]; }")

    bindings = {}
    def call(symbol, args):
        return model.invoke(symbol, [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                                     if f.startswith(('typeArgument', 'familyArgument'))], *args])

    def constructor(typ, suffix):
        rows = [target_name(c['target']) for sh in report['algebraicCarriers']
                if target_name(sh['target']) == typ for c in sh['constructors']
                if c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(rows) == 1, (typ, suffix, rows)
        return rows[0]

    def field(typ, suffix):
        rows = [(f, t) for f, t, _, _ in model.carriers[typ][1]
                if f.split('<', 1)[0].split('#', 1)[0].endswith(suffix)]
        assert len(rows) == 1, (typ, suffix, rows)
        return rows[0]

    comparisons = refusals = 0
    def expect(symbol, args, expected):
        nonlocal comparisons
        actual = call(symbol, args)
        assert same(actual, expected), (symbol, args, actual, expected)
        comparisons += 1

    def refuse(action):
        nonlocal refusals
        try:
            action()
        except AssertionError:
            refusals += 1
            return
        raise AssertionError('invalid native callback binding admitted')

    naturals = Extent('all finite naturals', lambda x: type(x) is int and x >= 0)
    opaque = tuple(Record('DomainValue', (('id', n), ('nested', Record('Detail', (('items', (n, n)),)))))
                   for n in (0, 7, 10**40))
    wrapped = Extent('wrapped domain values', lambda x: isinstance(x, Record) and x.type == 'CallbackPayload')
    values = (0, 1, 2, 7, 10**40, 2**128)

    native_case = roots['NaturalValues.nativeCase']
    native_type = next(t.argument for _, t, _, _ in model.calculations[native_case][0]
                       if isinstance(t, CallableSignature))
    decode = next(s for s in model.calculations if s == 'Agda2SysML.NaturalValues.decode')
    encode = next(s for s in model.calculations if s == 'Agda2SysML.NaturalValues.encode')
    decoded_increment = callback('testDecodedIncrement', quote(native_type), natural,
                                 f'{quote(decode)}(x) + 1')
    decoded_wrap = callback('testDecodedWrap', quote(native_type), any_value,
                            f"new 'CallbackPayload'('value' = {quote(decode)}(x))")
    annotate = roots['Diagnostics.Located.annotate']
    reason_type = model.calculations[annotate][0][-1][1]
    category_type = next(t.result for _, t, _, _ in model.calculations[annotate][0]
                         if isinstance(t, CallableSignature))
    categories = model.carriers[category_type][1]
    classifiers = [callback('testCategory' + str(i), quote(reason_type), quote(category_type),
                            quote(category_type) + '::' + quote(c)) for i, c in enumerate(categories)]
    model = Model(text + '\n' + '\n'.join(additions))

    for n in values:
        bindings = {'typeArgument0': naturals}
        expect(roots['NaturalValues.caseNat'], [99, increment, n], 99 if n == 0 else n)
        expect(roots['NaturalValues.caseNat'], [99, double, n], 99 if n == 0 else 2*(n-1))
        expect(native_case, [99, decoded_increment, model.invoke(encode, [n])], 99 if n == 0 else n)
        bindings = {'typeArgument0': wrapped}
        zero = Record('CallbackPayload', (('value', opaque[0]),))
        expected = zero if n == 0 else Record('CallbackPayload', (('value', n-1),))
        expect(roots['NaturalValues.caseNat'], [zero, wrap, n], expected)
        expect(native_case, [zero, decoded_wrap, model.invoke(encode, [n])], expected)

    bindings = {'typeArgument0': naturals}
    for invalid in (wrong_boolean, 42):
        refuse(lambda invalid=invalid: call(roots['NaturalValues.caseNat'], [0, invalid, 7]))

    vector_map = roots['BooleanLowering.map']
    input_vec = model.calculations[vector_map][0][-1][1]
    output_vec = model.results[vector_map]
    def vector(typ, items):
        if not items:
            return call(constructor(typ, '.[]'), [])
        return call(constructor(typ, '._∷_'), [len(items)-1, items[0], vector(typ, items[1:])])
    for extent, samples, fn, target_extent, transform in (
            (naturals, values, increment, naturals, lambda n: n+1),
            (naturals, values, double, naturals, lambda n: n*2),
            (opaque, opaque, identity, opaque, lambda x: x),
            (opaque, opaque, wrap, wrapped, lambda x: Record('CallbackPayload', (('value', x),)))):
        bindings = {'typeArgument0': extent, 'typeArgument1': target_extent}
        for n in range(4):
            for items in itertools.product(samples[:3], repeat=n):
                expect(vector_map, [n, fn, vector(input_vec, items)],
                       vector(output_vec, tuple(map(transform, items))))
        items = (samples[-1], samples[0], samples[-1])
        expect(vector_map, [len(items), fn, vector(input_vec, items)], vector(output_vec, tuple(map(transform, items))))
        refuse(lambda: call(vector_map, [1, fn, vector(input_vec, ())]))
    bindings = {'typeArgument0': naturals, 'typeArgument1': naturals}
    refuse(lambda: call(vector_map, [1, wrong_boolean, vector(input_vec, (7,))]))
    bindings = {'typeArgument0': opaque, 'typeArgument1': naturals}
    refuse(lambda: call(vector_map, [1, increment, vector(input_vec, (opaque[0],))]))

    maybe_map = roots['SourceAlignment.Direct.mapMaybe']
    rename = roots['SourceAlignment.Direct.rename']
    maybe_type = model.results[maybe_map]
    checked_type = model.results[rename]
    bindings = {'typeArgument0': opaque, 'typeArgument1': naturals}
    nothing, just = constructor(maybe_type, '.nothing'), constructor(maybe_type, '.just')
    var, global_, apply = [constructor(checked_type, '.Checked.' + c) for c in ('var', 'global', 'apply')]
    def checked(tree):
        tag, *args = tree
        return call({'var': var, 'global': global_, 'apply': apply}[tag],
                    [checked(x) for x in args] if tag == 'apply' else args)
    def renamed(tree, transform):
        tag, *args = tree
        return ('var', transform(args[0])) if tag == 'var' else (('apply', *(renamed(x, transform) for x in args))
                                                               if tag == 'apply' else tree)
    trees = [('var', n) for n in values] + [('global', x) for x in opaque]
    trees += [('apply', left, right) for left, right in itertools.product(trees[:4], repeat=2)]
    trees += [('apply', trees[0], ('apply', trees[-1], trees[0]))]
    for fn, transform in ((increment, lambda n: n+1), (double, lambda n: 2*n)):
        expect(maybe_map, [fn, call(nothing, [])], call(nothing, []))
        for n in values:
            expect(maybe_map, [fn, call(just, [n])], call(just, [transform(n)]))
        for tree in trees:
            expect(rename, [fn, checked(tree)], checked(renamed(tree, transform)))
    refuse(lambda: call(maybe_map, [wrong_boolean, call(just, [7])]))
    refuse(lambda: call(rename, [wrong_boolean, checked(('var', 7))]))

    bindings = {'typeArgument0': opaque, 'typeArgument1': opaque, 'typeArgument2': naturals}
    source_field, _ = field(reason_type, '.source')
    models_field, list_type = field(reason_type, '.models')
    message_field, _ = field(reason_type, '.message')
    reason_ctor = constructor(reason_type, '.reason')
    classified_ctor = constructor(model.results[annotate], '.classified')
    for source, message in itertools.product(opaque, values):
        models = Record(list_type, (('typeArgument1', opaque), ('items', (source, source, opaque[-1]))))
        reason = call(reason_ctor, [source, models, message])
        assert reason.get(source_field) == source and reason.get(models_field) == models and reason.get(message_field) == message
        for fn, category in zip(classifiers, categories):
            expect(annotate, [fn, reason], call(classified_ctor, [reason, category_type + '::' + category]))
    refuse(lambda: call(annotate, [increment, reason]))

    map_entry, map_report = [roots['Diagnostics.Accounting.' + s] for s in ('mapEntry', 'mapReport')]
    before_entry = model.calculations[map_entry][0][-1][1]
    after_entry = model.results[map_entry]
    before_report = model.calculations[map_report][0][-1][1]
    after_report = model.results[map_report]
    ids_type = model.calculations[map_report][0][-2][1]
    translated = constructor(before_entry, '.Entry.translated')
    evidence_type = model.calculations[translated][0][-1][1]
    evidence_index, _ = field(evidence_type, '.index0')
    evidence_value, _ = field(evidence_type, '.value')
    row_type = next(t for f, t, _, _ in model.carriers[evidence_type][1] if f == 'familyArgument3')
    row_index, _ = field(row_type, '.index0')
    row_value, _ = field(row_type, '.value')
    identities = (0, 7, 10**40)
    payloads = {i: Record('Evidence', (('identity', i), ('nested', opaque[i % len(opaque)]))) for i in identities}
    relation = tuple(Record(row_type, ((row_index, i), (row_value, payloads[i]))) for i in identities)

    for fn, after_extent, transform in ((identity, opaque, lambda x: x),
                                        (wrap, wrapped, lambda x: Record('CallbackPayload', (('value', x),)))):
        bindings = {'typeArgument0': naturals, 'typeArgument1': opaque,
                    'typeArgument2': after_extent, 'familyArgument3': relation}
        def ids(items):
            return Record(ids_type, (('typeArgument0', naturals), ('items', tuple(items))))
        def evidence(i):
            return Record(evidence_type, (('typeArgument0', naturals), ('familyArgument3', relation),
                          (evidence_index, i), (evidence_value, payloads[i])))
        def entry(typ, i, is_translated, reason):
            ctor = constructor(typ, '.Entry.translated' if is_translated else '.Entry.textual')
            return call(ctor, [i, evidence(i) if is_translated else reason])
        def report_value(typ, entry_type, items, statuses, transform):
            if not items:
                return call(constructor(typ, '.Report.empty'), [])
            i, rest = items[0], items[1:]
            return call(constructor(typ, '.Report.entry'),
                        [i, ids(rest), entry(entry_type, i, statuses[0], transform(opaque[len(rest) % len(opaque)])),
                         report_value(typ, entry_type, rest, statuses[1:], transform)])
        for i, status, reason in itertools.product(identities, (False, True), opaque):
            expect(map_entry, [fn, i, entry(before_entry, i, status, reason)],
                   entry(after_entry, i, status, transform(reason)))
        for items in ((), (0,), (7, 0), (10**40, 7, 10**40), (0, 0, 7, 0)):
            for statuses in itertools.product((False, True), repeat=len(items)):
                before = report_value(before_report, before_entry, items, statuses, lambda x: x)
                after = report_value(after_report, after_entry, items, statuses, transform)
                expect(map_report, [fn, ids(items), before], after)
        value = entry(before_entry, 0, False, opaque[0])
        refuse(lambda: call(map_entry, [fn, 7, value]))
        refuse(lambda: call(map_entry, [wrong_boolean, 0, value]))
        value = report_value(before_report, before_entry, (0, 7), (True, False), lambda x: x)
        refuse(lambda: call(map_report, [fn, ids((7, 0)), value]))
        refuse(lambda: call(map_report, [wrong_boolean, ids((0, 7)), value]))

    return {'operations': len(roots), 'comparisons': comparisons, 'invalidCasesRejected': refusals}
