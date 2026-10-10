"""Execute recursive substitution and instantiation from the emitted SysML."""
import json
from pathlib import Path
from emitted_model import CalculationValue, Model, Parser, Record, same, tokens
from open_parameters import target_name


def verify_specialized_callbacks(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    roots = {}
    for operation in ('substitute', 'substituteArgs', 'instantiate'):
        source = 'Agda2SysML.Specialization.' + operation + '#'
        rows = [o for o in report['obligations'] if o['symbol'].startswith(source)
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], operation
        roots[operation] = target_name(rows[0]['target'])
    carriers = {target_name(s['target']): s for s in report['algebraicCarriers']}
    bindings, samples = {}, {s: [] for s in roots.values()}
    comparisons = rejected = mutations = 0

    def quote(value):
        return "'" + value.replace('\\', '\\\\').replace("'", "\\'") + "'"

    def literal(value):
        if isinstance(value, Record):
            return 'new ' + quote(value.type) + '(' + ', '.join(quote(k) + ' = ' + literal(v) for k, v in value.fields) + ')'
        if isinstance(value, tuple):
            if not value: return 'null'
            return '(' + ', '.join([literal(v) for v in value] + (['null'] if len(value) == 1 else [])) + ')'
        if isinstance(value, int): return str(value)
        if isinstance(value, str) and '::' in value: return '::'.join(map(quote, value.rsplit('::', 1)))
        raise AssertionError(('unsupported literal', value))

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def arguments(symbol, values):
        return [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                  if f.startswith(('typeArgument', 'familyArgument'))], *values]

    def call(symbol, *values):
        args = arguments(symbol, values)
        result = model.invoke(symbol, args)
        if symbol in samples: samples[symbol].append((args, result))
        return result

    def constructor(typ, name):
        found = [target_name(c['target']) for c in carriers[typ]['constructors']
                 if target_name(c['target']).split('<', 1)[0].endswith('.' + name)]
        assert len(found) == 1, (typ, name, found)
        return found[0]

    def list_of(typ, values):
        nil, cons = constructor(typ, '[]'), constructor(typ, '_∷_')
        result = call(nil)
        for value in reversed(values): result = call(cons, value, result)
        return result

    # Distinct source and target domains, with opaque payloads that cannot be
    # replaced by Boolean representatives without losing observable data.
    payload = lambda domain, key: Record('SubstitutionPayload', (('domain', domain), ('key', key),
                                        ('history', (key, key, 10**40))))
    for slot in (0, 1, 2, 6, 7):
        bindings['typeArgument' + str(slot)] = tuple(payload(slot, i) for i in (0, 1))
    bindings['familyArgument5'] = ()
    atoms, families = bindings['typeArgument0'], bindings['typeArgument1']
    parameters = bindings['typeArgument6']
    targets = bindings['typeArgument7']

    def value(typ, tree, domain):
        tag, *parts = tree
        if tag == 'parameter': return call(constructor(typ, tag), domain[parts[0]])
        if tag == 'atom': return call(constructor(typ, tag), atoms[parts[0]])
        symbol = constructor(typ, 'family')
        list_type = runtime(symbol)[-1][1]
        return call(symbol, families[parts[0]], list_of(list_type, [value(typ, child, domain) for child in parts[1]]))

    def substitute(tree, replacements):
        tag, *parts = tree
        if tag == 'parameter': return replacements[parts[0]]
        if tag == 'atom': return tree
        return ('family', parts[0], tuple(substitute(child, replacements) for child in parts[1]))

    trees = [('parameter', 0), ('parameter', 1), ('atom', 0), ('atom', 1),
             ('family', 0, ()), ('family', 1, (('parameter', 0), ('parameter', 1), ('parameter', 0))),
             ('family', 0, (('family', 1, (('parameter', 1), ('atom', 0))), ('parameter', 0)))]
    deep = ('parameter', 1)
    for i in range(4):
        deep = ('family', i % 2, (deep, ('atom', i % 2)))
    trees.append(deep)
    replacements = [(('parameter', 1), ('parameter', 0)),
                    (('family', 0, (('parameter', 0), ('atom', 1), ('parameter', 0))),
                     ('family', 1, (('parameter', 1), ('parameter', 1))))]
    closed = (('atom', 1), ('family', 1, (('atom', 0), ('family', 0, ()), ('atom', 0))))
    signatures = {op: runtime(symbol)[0][1] for op, symbol in roots.items()}
    source_type = runtime(roots['substitute'])[-1][1]
    target_type = model.results[roots['substitute']]
    closed_type = model.results[roots['instantiate']]
    additions = ['attribute def SubstitutionPayload { attribute domain : ScalarValues::Natural; '
                 'attribute key : ScalarValues::Natural; '
                 'attribute history : ScalarValues::Natural [0..*] ordered nonunique; }']
    callbacks = []
    for i, (sig, typ, repl, domain) in enumerate(
            [(signatures['substitute'], target_type, r, targets) for r in replacements]
            + [(signatures['instantiate'], closed_type, closed, ())]):
        outputs = [value(typ, t, domain) for t in repl]
        name = 'substitutionReplacement' + str(i)
        expression = '(if (a0 as SubstitutionPayload).key == 0 ? ' + literal(outputs[0]) + ' else ' + literal(outputs[1]) + ')'
        additions.append('calc def ' + quote(name) + ' { in a0 : ' + quote(sig.arguments[0])
                         + ' [1]; return result : ' + quote(sig.result) + ' [1] = ' + expression + '; }')
        callbacks.append(CalculationValue(name))
    model = Model(text + '\n' + '\n'.join(additions))

    # Cache immutable carrier checks, clearing on each validity mutation.
    boundary, checked = model.boundary, {}
    def cached(typ, low, high, item, depth=0):
        key = (id(typ), low, high, id(item))
        if key not in checked:
            boundary(typ, low, high, item, depth)
            checked[key] = (typ, item)
    model.boundary = cached
    # Generated constructor expressions can repeat the same pure recursive
    # call for its payload and node count. Retain argument objects so identity
    # keys cannot be reused, including callback bindings with lexical context.
    invoke, invoked = model.invoke, {}
    def cached_invoke(symbol, arguments, check=True, depth=0):
        key = (symbol, tuple(map(id, arguments)), check)
        if key not in invoked:
            invoked[key] = (tuple(arguments), invoke(symbol, arguments, check, depth))
        return invoked[key][1]
    model.invoke = cached_invoke

    def expect(actual, expected):
        nonlocal comparisons
        assert same(actual, expected), 'substitution changed complete payload, order, binding or multiplicity'
        comparisons += 1

    def reject(action):
        nonlocal rejected
        checked.clear()
        invoked.clear()
        try: action()
        except AssertionError: rejected += 1
        else: raise AssertionError('inconsistent recursive callback input was admitted')

    lists = [(), *[(t,) for t in trees], tuple(trees), (trees[0], trees[0], trees[-1]), tuple(reversed(trees))]
    for callback, replacement in zip(callbacks, replacements):
        for tree in trees:
            expect(call(roots['substitute'], callback, value(source_type, tree, parameters)),
                   value(target_type, substitute(tree, replacement), targets))
        source_list = runtime(roots['substituteArgs'])[-1][1]
        target_list = model.results[roots['substituteArgs']]
        for ts in lists:
            expect(call(roots['substituteArgs'], callback, list_of(source_list, [value(source_type, t, parameters) for t in ts])),
                   list_of(target_list, [value(target_type, substitute(t, replacement), targets) for t in ts]))
    for tree in trees:
        expect(call(roots['instantiate'], callbacks[-1], value(source_type, tree, parameters)),
               value(closed_type, substitute(tree, closed), ()))

    impossible = constructor(closed_type, 'parameter')
    empty_type = runtime(impossible)[-1][1]
    fake_empty = Record(empty_type, ())
    reject(lambda: model.boundary(empty_type, 1, 1, fake_empty))
    reject(lambda: call(impossible, fake_empty))
    validity = target_name(carriers[empty_type]['admissibility'])
    inputs, body, assertions = model.calculations[validity]
    model.calculations[validity] = (inputs, ('literal', True), assertions)
    checked.clear()
    invoked.clear()
    model.boundary(empty_type, 1, 1, fake_empty)
    model.calculations[validity] = (inputs, body, assertions)
    checked.clear()
    invoked.clear()

    def replace(item, field, changed):
        return Record(item.type, tuple((f, changed if f == field else x) for f, x in item.fields))

    for symbol in roots.values():
        args, expected = samples[symbol][-1]
        supplied = args[-1]
        count = next(f for f, _ in supplied.fields if f.endswith('.node-count'))
        for bad_count in (0, supplied.get(count) + 1):
            reject(lambda: model.invoke(symbol, [*args[:-1], replace(supplied, count, bad_count)]))
        changed = list(args)
        slot = next(i for i, (f, _, _, _) in enumerate(model.calculations[symbol][0]) if f == 'typeArgument6')
        changed[slot] = ()
        reject(lambda: model.invoke(symbol, changed))
        # Replacing a complete algorithm with one well-typed constant must be
        # detected on the varied corpus even if all its contracts still hold.
        inputs, body, assertions = model.calculations[symbol]
        wrong = Parser(tokens(literal(samples[symbol][0][1]))).expression()
        model.calculations[symbol] = (inputs, wrong, assertions)
        checked.clear()
        invoked.clear()
        detected = False
        for arguments_, result in samples[symbol]:
            try: actual = model.invoke(symbol, arguments_)
            except AssertionError: detected = True; break
            if not same(actual, result): detected = True; break
        assert detected, ('undetected constant-body mutation', symbol)
        mutations += 1
        model.calculations[symbol] = (inputs, body, assertions)
        checked.clear()
        invoked.clear()
    return dict(operations=len(roots), comparisons=comparisons, invalidCasesRejected=rejected,
                bodyMutationsDetected=mutations, differentParameterDomains=True,
                recursiveLists=True, emptyConstraintMutationDetected=True,
                completePayloadsPreserved=True)
