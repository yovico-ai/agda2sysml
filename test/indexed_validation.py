"""Check indexed validation decisions and complete witnesses in emitted SysML."""
import itertools
import json
from pathlib import Path

from emitted_model import BoundCalculation, BodyCalculation, CalculationValue, CallableSignature, Model, Parser, Record, same, sequence as values_sequence, tokens
from open_parameters import target_name


def verify_indexed_validation(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    retained = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.Relations.relation-sound#')
                and '@' not in o['symbol'] and o['kind'] == 'behavior']
    assert len(retained) == 1 and retained[0]['status'] == 'discharged' and retained[0]['target'], \
        'sequence comparison prevented reduction of a checked recursive index helper'
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    roots, bindings, samples = {}, {}, {}
    comparisons = refused = mutations = 0

    def root(name):
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.' + name + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], name
        roots[name] = target_name(rows[0]['target'])
        return roots[name]

    def constructor(typ, suffix):
        rows = [target_name(c['target']) for sh in report['algebraicCarriers']
                if target_name(sh['target']) == typ for c in sh['constructors']
                if c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(rows) == 1, (typ, suffix, rows)
        return rows[0]

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def field(typ, suffix):
        found = [f for f, _, _, _ in model.carriers[typ][1]
                 if f.split('<', 1)[0].split('#', 1)[0].endswith(suffix)]
        assert len(found) == 1, (typ, suffix, found)
        return found[0]

    def record(typ, values):
        return Record(typ, tuple((f, bindings[f] if f.startswith(('typeArgument', 'familyArgument')) else values[f])
                                for f, _, _, _ in model.carriers[typ][1]))

    def quote(value):
        return "'" + value.replace('\\', '\\\\').replace("'", "\\'") + "'"

    def literal(value):
        if isinstance(value, Record):
            return 'new ' + quote(value.type) + '(' + ', '.join(quote(k) + ' = ' + literal(v) for k, v in value.fields) + ')'
        if isinstance(value, tuple):
            if not value: return 'null'
            return '(' + ', '.join([literal(v) for v in value] + (['null'] if len(value) == 1 else [])) + ')'
        if type(value) is bool: return 'true' if value else 'false'
        if type(value) is int: return str(value)
        if isinstance(value, str) and '::' in value: return '::'.join(map(quote, value.rsplit('::', 1)))
        raise AssertionError(('unsupported test value', value))

    def expression(symbol, values):
        return quote(symbol) + '(' + ', '.join([
            *[literal(bindings[f]) for f, _, _, _ in model.calculations[symbol][0]
              if f.startswith(('typeArgument', 'familyArgument'))], *values]) + ')'

    def args(symbol, values):
        return [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                  if f.startswith(('typeArgument', 'familyArgument'))], *values]

    def call(symbol, *values):
        return model.invoke(symbol, args(symbol, values))

    def check(symbol, values, expected):
        nonlocal comparisons
        arguments = args(symbol, values)
        result = model.invoke(symbol, arguments)
        assert equal_value(result, expected), ('incorrect complete indexed result', symbol, difference(result, expected))
        samples.setdefault(symbol, []).append((arguments, expected))
        comparisons += 1
        return result

    def equal_value(actual, expected):
        if isinstance(actual, (CalculationValue, BoundCalculation, BodyCalculation)):
            return isinstance(expected, (CalculationValue, BoundCalculation, BodyCalculation))
        if isinstance(actual, Record) and isinstance(expected, Record):
            if actual.type != expected.type or dict(actual.fields).keys() != dict(expected.fields).keys(): return False
            fields = model.carriers.get(actual.type, (None, [], []))[1]
            many = {f for f, _, low, high in fields if low != 1 or high != 1}
            return all(equal_value(values_sequence(a), values_sequence(expected.get(f))) if f in many
                       else equal_value(a, expected.get(f)) for f, a in actual.fields)
        if isinstance(actual, tuple) and isinstance(expected, tuple):
            return len(actual) == len(expected) and all(equal_value(a, b) for a, b in zip(actual, expected))
        return same(actual, expected)

    def difference(actual, expected, path='result'):
        if type(actual) is not type(expected): return path, type(actual).__name__, type(expected).__name__
        if isinstance(actual, Record):
            if actual.type != expected.type: return path, actual.type, expected.type
            if [f for f, _ in actual.fields] != [f for f, _ in expected.fields]:
                return path, 'different field ordering', [f for f, _ in actual.fields], [f for f, _ in expected.fields]
            for (f, a), (_, b) in zip(actual.fields, expected.fields):
                if not same(a, b): return difference(a, b, path + '.' + f)
        if isinstance(actual, tuple):
            if len(actual) != len(expected): return path, len(actual), len(expected)
            for i, (a, b) in enumerate(zip(actual, expected)):
                if not same(a, b): return difference(a, b, path + '[' + str(i) + ']')
        return path, repr(actual)[:200], repr(expected)[:200]

    def refuse(action):
        nonlocal refused
        try:
            action()
        except AssertionError:
            refused += 1
            return
        raise AssertionError('inconsistent indexed input admitted')

    def cache():
        checked, invoked = {}, {}
        boundary, invoke = model.boundary, model.invoke
        def cached_boundary(carrier, low, high, value, depth=0):
            key = (id(carrier), low, high, id(value))
            if key not in checked:
                boundary(carrier, low, high, value, depth)
                checked[key] = (carrier, value)
        def cached_invoke(symbol, arguments, check=True, depth=0):
            key = (symbol, tuple(map(id, arguments)), check)
            if key not in invoked:
                invoked[key] = (tuple(arguments), invoke(symbol, arguments, check, depth))
            return invoked[key][1]
        model.boundary, model.invoke = cached_boundary, cached_invoke

    cache()
    classify = root('Coverage.Inventory.classify')
    strict = root('Coverage.Inventory.strict')
    strict_accepts = root('Coverage.Inventory.strict-accepts-complete')
    law_rows = [o for o in report['nativeStatements']
                if o['symbol'].startswith('Agda2SysML.Coverage.Inventory.strict-refuses-textual#')
                and '@' not in o['symbol'] and o['status'] == 'translated']
    assert len(law_rows) == 1
    strict_refuses = target_name(law_rows[0]['target'])
    ids_type, report_type = [t for _, t in runtime(classify)]
    empty = constructor(report_type, 'Report.empty')
    entry = constructor(report_type, 'Report.entry')
    entry_type = runtime(entry)[-2][1]
    translated = constructor(entry_type, 'Entry.translated')
    textual = constructor(entry_type, 'Entry.textual')
    evidence_type = runtime(translated)[-1][1]
    row_type = next(t for f, t, _, _ in model.carriers[evidence_type][1] if f == 'familyArgument2')
    decision_type = model.results[classify]
    yes = constructor(decision_type, 'Dec.yes')
    no = constructor(decision_type, 'Dec.no')
    all_type = runtime(yes)[-1][1]
    done = constructor(all_type, 'AllTranslated.done')
    next_proof = constructor(all_type, 'AllTranslated.next')
    maybe_type = model.results[strict]
    just = constructor(maybe_type, '.just')
    nothing = constructor(maybe_type, '.nothing')
    complete_type = runtime(just)[-1][1]
    complete = constructor(complete_type, '.complete')
    present = constructor(model.results[strict_accepts], '.present')
    textual_type = runtime(strict_refuses)[-1][1]
    at_head = constructor(textual_type, '.at-head')
    in_tail = constructor(textual_type, '.in-tail')
    identities = tuple(Record('Identity', (('ordinal', n), ('history', (n, n, 10**30)))) for n in (0, 10**30))
    reasons = tuple(Record('Reason', (('message', n), ('detail', (n, n)))) for n in (0, 1))
    payloads = {i: Record('Evidence', (('owner', i), ('history', (i, i, 10**30)))) for i in identities}
    relation = tuple(Record(row_type, ((field(row_type, '.index0'), i),
                                      (field(row_type, '.value'), payloads[i]))) for i in identities)
    bindings.update(typeArgument0=identities, typeArgument1=reasons, familyArgument2=relation)

    def ids(items):
        return record(ids_type, {'items': tuple(items)})

    def evidence(i):
        return record(evidence_type, {field(evidence_type, '.index0'): i,
                                      field(evidence_type, '.value'): payloads[i]})

    def build(items, statuses):
        if not items:
            return call(empty), call(done), None
        i, rest = items[0], items[1:]
        tail, proof, fallback = build(rest, statuses[1:])
        item = call(translated, i, evidence(i)) if statuses[0] else call(textual, i, reasons[len(rest) % 2])
        result = call(entry, i, ids(rest), item, tail)
        witness = call(next_proof, i, ids(rest), evidence(i), tail, proof) if all(statuses) else None
        textual_proof = (call(in_tail, i, ids(rest), item, tail, fallback) if fallback is not None else None) if statuses[0] \
            else call(at_head, i, ids(rest), reasons[len(rest) % 2], tail)
        return result, witness, textual_proof

    a, b = identities
    layouts = ((), (a,), (b,), (a, b), (b, b, a), (a, b, a, b))
    for items in layouts:
        for statuses in itertools.product((False, True), repeat=len(items)):
            value, proof, fallback = build(items, statuses)
            if all(statuses):
                check(classify, [ids(items), value], call(yes, ids(items), value, proof))
                complete_value = call(complete, ids(items), value, proof)
                check(strict, [ids(items), value], call(just, ids(items), value, complete_value))
                check(strict_accepts, [ids(items), value, proof], call(present, ids(items), value, complete_value))
            else:
                result = call(classify, ids(items), value)
                assert result.get('constructor') == decision_type + '.constructor-tag::' + no
                comparisons += 1
                check(strict, [ids(items), value], call(nothing, ids(items), value))
                check(strict_refuses, [ids(items), value, fallback], True)
            for operation in (classify, strict):
                refuse(lambda operation=operation: call(operation, ids((*items, a)), value))

    validate = root('Mapping.Validation.validate')
    transfer = root('Mapping.Validation.accepted-symbol-fits')
    accepts = root('Mapping.Validation.validate-accepts-compatible')
    excludes = root('Mapping.Validation.acceptance-excludes-refusal')
    callback_type, role_type, candidates_type = [t for _, t in runtime(validate)]
    roles = tuple(role_type + '::' + c for c in model.carriers[role_type][1])
    mapping_decision = callback_type.result
    fit_yes = constructor(mapping_decision, 'Dec.yes')
    fit_no = constructor(mapping_decision, 'Dec.no')
    fit_type = runtime(fit_yes)[-1][1]
    refutation_type = runtime(fit_no)[-1][1]
    fit_row = next(t for f, t, _, _ in model.carriers[fit_type][1] if f == 'familyArgument1')
    fits = {(role, symbol): Record('Fits', (('role', role), ('symbol', symbol), ('details', (10**30, 10**30))))
            for n, role in enumerate(roles) for i, symbol in enumerate(identities) if i == n % 2}
    fit_relation = tuple(Record(fit_row, ((field(fit_row, '.index0'), role),
                                         (field(fit_row, '.index1'), symbol),
                                         (field(fit_row, '.value'), evidence)))
                         for (role, symbol), evidence in fits.items())
    bindings.update(typeArgument0=identities, familyArgument1=fit_relation)

    def fit(role, symbol):
        return record(fit_type, {field(fit_type, '.index0'): role,
                                 field(fit_type, '.index1'): symbol,
                                 field(fit_type, '.value'): fits[role, symbol]})

    # A failed decision has an empty contextual evidence domain. This callback
    # must never return successfully if the implementation wrongly invokes it.
    refute_name = 'testMissingFit'
    additions = [f'calc def {quote(refute_name)} {{ in proof : {quote(fit_type)} [1]; '
                 f'return result : {quote(refutation_type.result)} [1] = null; }}']
    refutation = f'{{ in proof : {quote(fit_type)} [1]; return result : {quote(refutation_type.result)} [1]; null }}'
    negative = expression(fit_no, ['role', 'symbol', refutation])
    decision = negative
    for (role, symbol), evidence_value in reversed(list(fits.items())):
        positive = expression(fit_yes, ['role', 'symbol', literal(fit(role, symbol))])
        decision = f'(if role == {literal(role)} ? (if symbol == {literal(symbol)} ? {positive} else {negative}) else {decision})'
    additions.append(f'calc def testFitDecision {{ in role : {quote(role_type)} [1]; in symbol : Base::Anything [1]; '
                     f'return result : {quote(mapping_decision)} [1] = {decision}; }}')
    model = Model(text + '\n' + '\n'.join(additions))
    cache()
    checker = CalculationValue('testFitDecision')
    result_type = model.results[validate]
    accepted = constructor(result_type, '.accepted')
    rejected = constructor(result_type, '.refused')
    acceptance_type = runtime(accepted)[-1][1]
    refusal_type = runtime(rejected)[-1][1]
    unique = constructor(acceptance_type, '.unique-compatible')
    unresolved = constructor(refusal_type, '.unresolved')
    ambiguous = constructor(refusal_type, '.ambiguous')
    incompatible = constructor(refusal_type, '.incompatible')
    equality_type = runtime(transfer)[-1][1]
    refl = constructor(equality_type, '.refl')
    success = constructor(model.results[accepts], '.success')

    def candidates(items):
        return record(candidates_type, {'items': tuple(items)})

    for role in roles:
        for items in ((), (a,), (b,), (a, b), (b, b), (b, a, b)):
            sequence = candidates(items)
            if not items:
                expected = call(rejected, role, sequence, call(unresolved, role))
            elif len(items) > 1:
                expected = call(rejected, role, sequence, call(ambiguous, role, items[0], items[1], candidates(items[2:])))
            elif (role, items[0]) in fits:
                witness = call(unique, role, items[0], fit(role, items[0]))
                expected = call(accepted, role, sequence, witness)
                check(transfer, [role, sequence, witness, items[0], call(refl, sequence)], fit(role, items[0]))
                check(accepts, [checker, role, items[0], fit(role, items[0])], call(success, role, sequence, witness))
                other = identities[1 - identities.index(items[0])]
                refuse(lambda: call(transfer, role, sequence, witness, other, call(refl, sequence)))
                contradictory = call(incompatible, role, items[0], CalculationValue(refute_name))
                refuse(lambda: call(excludes, role, sequence, witness, contradictory))
            else:
                # Compare every data field; the callback carries a contextual
                # binding, so verify its negative branch separately below.
                expected = call(rejected, role, sequence, call(incompatible, role, items[0], CalculationValue(refute_name)))
            check(validate, [checker, role, sequence], expected)

    for symbol in (classify, strict, validate):
        rows = samples[symbol]
        args0, expected = rows[0]
        changed = next(value for _, value in rows[1:] if not equal_value(value, expected))
        mutant = Model(text + '\n' + '\n'.join(additions))
        inputs, _, assertions = mutant.calculations[symbol]
        mutant.calculations[symbol] = (inputs, Parser(tokens(literal(changed))).expression(), assertions)
        try:
            actual = mutant.invoke(symbol, args0)
            detected = not equal_value(actual, expected)
        except AssertionError:
            detected = True
        assert detected, ('constant-result mutation escaped', symbol)
        mutations += 1

    return {'operations': len(roots), 'statements': 1, 'comparisons': comparisons,
            'invalidCasesRejected': refused, 'bodyMutationsDetected': mutations}
