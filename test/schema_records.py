"""Exercise stored type-family bindings through the original Agda operations."""
import itertools
import json
from pathlib import Path
from emitted_model import CalculationValue, Model, Record, same
from open_parameters import target_name


def verify_schema_records(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    names = ('OpenParameters.Transport.encodeValue', 'OpenParameters.Transport.decodeValue',
             'OpenParameters.Transport.encodeList', 'OpenParameters.Transport.decodeList',
             'FamilyRelations.Transport.encodeAt', 'FamilyRelations.Transport.decodeAt',
             'FamilyRelations.Transport.select', 'FamilyRelations.Transport.reindex',
             'OpenParameters.Transport.pack', 'OpenParameters.Transport.Container.contents',
             'OpenParameters.Transport.Container.typeArgument', 'OpenParameters.Transport.Container.sameParameter',
             'OpenParameters.Transport.resolve-parameter-preserves')
    roots = {}
    for source in names:
        rows = [o for o in report['obligations'] if o['symbol'].startswith('Agda2SysML.' + source + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], source
        roots[source] = target_name(rows[0]['target'])

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def field(typ, suffix):
        matches = [f for f, _, _, _ in model.carriers[typ][1]
                   if f.split('#', 1)[0].endswith(suffix) or f.split('<', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def quote(value):
        return "'" + value.replace('\\', '\\\\').replace("'", "\\'") + "'"

    def literal(value):
        if isinstance(value, Record):
            return 'new ' + quote(value.type) + '(' + ', '.join(quote(k) + ' = ' + literal(v) for k, v in value.fields) + ')'
        if isinstance(value, tuple):
            if not value: return 'null'
            return '(' + ', '.join([literal(v) for v in value] + (['null'] if len(value) == 1 else [])) + ')'
        if isinstance(value, bool): return 'true' if value else 'false'
        if isinstance(value, int): return str(value)
        if isinstance(value, str) and '::' in value: return '::'.join(map(quote, value.rsplit('::', 1)))
        raise AssertionError(('unsupported test literal', value))

    prelude = ('attribute def SchemaSource { attribute key : ScalarValues::Natural; '
               'attribute steps : ScalarValues::Natural [0..*] ordered nonunique; }\n'
               'attribute def SchemaNative { attribute key : ScalarValues::Natural; '
               'attribute steps : ScalarValues::Natural [0..*] ordered nonunique; }\n'
               'attribute def SchemaEvidence { attribute key : ScalarValues::Natural; '
               'attribute steps : ScalarValues::Natural [0..*] ordered nonunique; }\n')
    additions = []
    def callback(name, signature, expression):
        additions.append('calc def ' + quote(name) + ' { ' + ''.join(
            f'in a{i} : {quote(t)} [1]; ' for i, t in enumerate(signature.arguments))
            + f'return result : {quote(signature.result)} [1] = {expression}; }}')
        return CalculationValue(name)

    def refresh():
        nonlocal model
        model = Model(text + '\n' + prelude + '\n'.join(additions))
        # Values are immutable, and the cache retains each object to prevent
        # identity reuse. A new model starts with a new cache, including mutations.
        checked = {}
        boundary = model.boundary
        def cached(carrier, low, high, value, depth):
            key = (id(carrier), low, high, id(value))
            if key not in checked:
                boundary(carrier, low, high, value, depth)
                checked[key] = (carrier, value)
        model.boundary = cached

    comparisons = rejected = mutations = callback_checks = 0
    def expect(actual, expected):
        nonlocal comparisons
        assert same(actual, expected), ('changed complete schema-bound value', comparisons)
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        try: action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('invalid stored-schema value admitted')

    bindings = {}
    def record(typ, values):
        parameters = [(f, bindings[f]) for f, _, _, _ in model.carriers[typ][1]
                      if f.startswith(('typeArgument', 'familyArgument'))]
        return Record(typ, (*parameters, *values.items()))

    def call(symbol, *values):
        return model.invoke(symbol, [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                                      if f.startswith(('typeArgument', 'familyArgument'))], *values])

    projection_aliases = {}
    projection_comparisons = projection_mutations = 0

    def alias(module, name):
        key = module, name
        if key not in projection_aliases:
            rows = [o for o in report['obligations']
                    if o['symbol'].startswith('Agda2SysML.' + module + '.Transport._#')
                    and o['symbol'].rsplit('.', 1)[-1].split('#', 1)[0] == name
                    and o['sourceKind'] == 'behavior']
            assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], key
            assert rows[0]['source']['checkedDefinition'] == rows[0]['symbol'], 'projection alias provenance lost'
            projection_aliases[key] = target_name(rows[0]['target'])
        return projection_aliases[key]

    def projected(module, name, binding, expected, arguments=None):
        nonlocal projection_comparisons
        result = call(alias(module, name), binding)
        if arguments is not None:
            result = model.invoke_callback_many(result, arguments, True, 0)
        expect(result, expected)
        projection_comparisons += 1

    def mutate_projection(module, name, binding, wrong, expected):
        nonlocal projection_mutations
        symbol = alias(module, name)
        saved = model.calculations[symbol]
        model.calculations[symbol] = (saved[0], ('literal', wrong), saved[2])
        try:
            refuse(lambda: projected(module, name, binding, expected))
            projection_mutations += 1
        finally:
            model.calculations[symbol] = saved

    statement_names = (*( 'OpenParameters.Transport.' + name for name in
                         ('payload-roundtrip', 'append-preserves', 'orElse-preserves', 'resolve-preserves')), *(
        'FamilyRelations.Transport.' + name for name in (
            'index-preserves', 'payload-roundtrip-at', 'reindex-payload-preserves',
            'selection-preserves', 'source-roundtrip-at', 'wrapping-preserves')))
    statements = {name: target_name(next(r['target'] for r in report['nativeStatements']
                  if r['symbol'].startswith('Agda2SysML.' + name + '#') and r['status'] == 'translated'))
                  for name in statement_names}
    exercised = set()
    statement_mutations = 0
    def law(name, *values):
        assert call(statements[name], *values) is True, ('false stored-schema law', name)
        exercised.add(name)

    def mutate_law(name, arguments, helper, wrong):
        nonlocal statement_mutations
        saved = model.calculations[helper]
        model.calculations[helper] = (saved[0], ('literal', wrong), saved[2])
        try:
            refuse(lambda: law(name, *arguments))
            statement_mutations += 1
        finally:
            model.calculations[helper] = saved

    def ctor(typ):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']]
        assert len(matches) == 1, (typ, matches)
        return matches[0]

    encode, decode, encode_list, decode_list = [roots[source] for source in names[:4]]
    pack, contents, classifier_of, evidence_of = [roots[source] for source in names[8:12]]
    resolve_parameter = roots[names[12]]
    container_type = model.results[pack]
    binding_type = runtime(encode)[0][1]
    value_type = model.results[encode]
    source_list, value_list = runtime(encode_list)[1][1], model.results[encode_list]
    slots = {f.split('<', 1)[0].rsplit('.', 1)[-1]: (f, t) for f, t, _, _ in model.carriers[binding_type][1]
             if not f.startswith(('typeArgument', 'familyArgument'))}
    approximation_type = slots['_≈_'][1]
    approximation_row = next(t for f, t, _, _ in model.carriers[approximation_type][1] if f == 'items')
    approximation_member = slots['same'][1].result
    member_type = slots['admitted'][1].result
    member_row = next(t for f, t, _, _ in model.carriers[member_type][1] if f == 'familyArgument3')
    sources = tuple(Record('SchemaSource', (('key', i), ('steps', (i, i, 10**30)))) for i in range(3))
    natives = tuple(Record('SchemaNative', (('key', 7-i), ('steps', (i+4, i+4, 10**30)))) for i in range(3))
    evidence = {(c, i): Record('SchemaEvidence', (('key', 10*c+i), ('steps', (c, i, i))))
                for c in (0, 1) for i in range(3)}
    bindings.update(typeArgument0=sources, typeArgument1=natives, typeArgument2=(0, 1))
    relation = tuple(Record(member_row, ((field(member_row, '.index0'), c),
                     (field(member_row, '.index1'), native), (field(member_row, '.value'), evidence[c, i])))
                     for c in (0, 1) for i, native in enumerate(natives))
    bindings['familyArgument3'] = relation
    approximate_rows = tuple(record(approximation_row, {field(approximation_row, '.index0'): c,
        field(approximation_row, '.index1'): c, field(approximation_row, '.value'): evidence[c, 0]}) for c in (0, 1))
    approximation = record(approximation_type, {'items': approximate_rows})
    def membership(c, i):
        return record(member_type, {field(member_type, '.index0'): c,
            field(member_type, '.index1'): natives[i], field(member_type, '.value'): evidence[c, i]})
    def approximate(c):
        return record(approximation_member, {field(approximation_member, '.index0'): approximation,
            field(approximation_member, '.index1'): c, field(approximation_member, '.index2'): c,
            field(approximation_member, '.value'): evidence[c, 0]})
    def choose(argument, inputs, outputs):
        expression = literal(outputs[-1])
        for value, result in reversed(list(zip(inputs[:-1], outputs[:-1]))):
            expression = f'if {argument} == {literal(value)} ? {literal(result)} else ({expression})'
        return expression
    def reflexive(signature):
        symbol = ctor(signature.result)
        assert len(runtime(symbol)) == 1
        return quote(symbol) + '(' + ', '.join(literal(bindings[f]) if f.startswith(('typeArgument', 'familyArgument')) else 'a0'
                                              for f, _, _, _ in model.calculations[symbol][0]) + ')'

    for classifier in (0, 1):
        callbacks = {}
        expressions = {'same': choose('a0', (0, 1), [approximate(c) for c in (0, 1)]),
            'same-members': 'a4', 'encode': choose('a0', sources, natives),
            'admitted': choose('a0', sources, [membership(classifier, i) for i in range(3)]),
            'decode': choose('a0', natives, sources),
            'source-roundtrip': reflexive(slots['source-roundtrip'][1]),
            'native-roundtrip': reflexive(slots['native-roundtrip'][1])}
        for name, expression in expressions.items():
            callbacks[name] = callback('schema' + str(classifier) + name, slots[name][1], expression)
        refresh()
        binding = record(binding_type, {slots['_≈_'][0]: approximation, slots['classifier'][0]: classifier,
                                       **{slots[name][0]: value for name, value in callbacks.items()}})
        projected('OpenParameters', '_≈_', binding, approximation)
        projected('OpenParameters', 'classifier', binding, classifier)
        projected('OpenParameters', 'same', binding, approximate(classifier), [classifier])
        for i in range(3):
            projected('OpenParameters', 'encode', binding, natives[i], [sources[i]])
            projected('OpenParameters', 'admitted', binding, membership(classifier, i), [sources[i]])
            projected('OpenParameters', 'decode', binding, sources[i], [natives[i], membership(classifier, i)])
            projected('OpenParameters', 'same-members', binding, membership(classifier, i),
                      [classifier, classifier, approximate(classifier), natives[i], membership(classifier, i)])
        refuse(lambda: model.invoke_callback_many(call(alias('OpenParameters', 'decode'), binding),
                                                  [natives[0], membership(1-classifier, 0)], True, 0))
        mutate_projection('OpenParameters', 'classifier', binding, 1-classifier, classifier)
        # Payload is a type binder after the runtime binding. Exercise two
        # unrelated structured extents, preserving the complete binding,
        # classifier, equality witness, and payload through all projections.
        for extent in (sources, natives):
            bindings['typeArgument4'] = extent
            containers = [record(container_type, {
                field(container_type, '.index0'): binding,
                field(container_type, '.parameter0'): binding,
                field(container_type, '.typeArgument'): classifier,
                field(container_type, '.sameParameter'): approximate(classifier),
                field(container_type, '.contents'): payload}) for payload in extent]
            for payload, expected in zip(extent, containers):
                expect(call(pack, binding, payload), expected)
                expect(call(contents, expected), payload)
                expect(call(classifier_of, expected), classifier)
                expect(call(evidence_of, expected), approximate(classifier))
            refuse(lambda: call(pack, binding, natives[0] if extent is sources else sources[0]))
            bad = Record(containers[0].type, tuple((f, approximate(1-classifier)
                if f == field(container_type, '.sameParameter') else value) for f, value in containers[0].fields))
            refuse(lambda: call(contents, bad))
            for symbol, arguments, wrong, expected in [
                    (pack, (binding, extent[0]), containers[1], containers[0]),
                    (contents, (containers[0],), extent[1], extent[0]),
                    (classifier_of, (containers[0],), 1-classifier, classifier),
                    (evidence_of, (containers[0],), approximate(1-classifier), approximate(classifier))]:
                inputs, body, assertions = model.calculations[symbol]
                model.calculations[symbol] = inputs, ('literal', wrong), assertions
                try:
                    try:
                        result = call(symbol, *arguments)
                    except AssertionError:
                        mutations += 1
                    else:
                        assert not same(result, expected), 'mixed-parameter body mutation escaped comparison'
                        mutations += 1
                finally:
                    model.calculations[symbol] = inputs, body, assertions
        def invoke_field(name, arguments):
            bound = model.evaluate(('project', ('literal', binding), slots[name][0]), {})
            return model.invoke_callback_many(bound, arguments, True, 0)
        values = [call(ctor(value_type), binding, native, membership(classifier, i)) for i, native in enumerate(natives)]
        list_constructors = [target_name(c['target']) for sh in report['algebraicCarriers']
                             if target_name(sh['target']) == value_list for c in sh['constructors']]
        nil = next(c for c in list_constructors if len(runtime(c)) == 1)
        cons = next(c for c in list_constructors if len(runtime(c)) == 3)
        def value_listing(items):
            result = call(nil, binding)
            for item in reversed(items):
                result = call(cons, binding, item, result)
            return result
        def variant(typ, suffix, *values):
            symbol = next(target_name(c['target']) for sh in report['algebraicCarriers']
                          if target_name(sh['target']) == typ for c in sh['constructors']
                          if c['symbol'].split('#', 1)[0].endswith(suffix))
            return call(symbol, *values)
        def right_helper(name):
            body = model.calculations[statements['OpenParameters.Transport.' + name]][1]
            assert body[0] == '==' and body[2][0] == 'call', body
            return body[2][1]
        lists = [record(source_list, {'items': tuple(sources[i] for i in ordinals)})
                 for ordinals in ((), (0,), (0, 0), (2, 0, 1))]
        for xs, ys in itertools.product(lists, repeat=2):
            law('OpenParameters.Transport.append-preserves', binding, xs, ys)
        append_native = right_helper('append-preserves')
        mutate_law('OpenParameters.Transport.append-preserves', (binding, lists[1], lists[1]),
                   append_native, value_listing(values[1:2]))
        or_else_native = right_helper('orElse-preserves')
        source_maybe = runtime(statements['OpenParameters.Transport.orElse-preserves'])[1][1]
        choices = [variant(source_maybe, '.nothing'),
                   *(variant(source_maybe, '.just', source) for source in sources)]
        for first, fallback in itertools.product(choices, repeat=2):
            law('OpenParameters.Transport.orElse-preserves', binding, first, fallback)
        mutate_law('OpenParameters.Transport.orElse-preserves', (binding, choices[1], choices[2]),
                   or_else_native, variant(model.results[or_else_native], '.just', binding, values[1]))
        resolve_native = right_helper('resolve-preserves')
        mutate_law('OpenParameters.Transport.resolve-preserves', (binding, lists[1]), resolve_native,
                   variant(model.results[resolve_native], '.resolved', binding, values[1]))
        outside = record(source_list, {'items': (natives[0],)})
        refuse(lambda: law('OpenParameters.Transport.append-preserves', binding, outside, lists[0]))
        refuse(lambda: law('OpenParameters.Transport.resolve-preserves', binding, outside))
        saved = model.calculations[resolve_parameter]
        model.calculations[resolve_parameter] = (saved[0], ('literal', approximate(1-classifier)), saved[2])
        try:
            refuse(lambda: call(resolve_parameter, binding, lists[1]))
            mutations += 1
        finally:
            model.calculations[resolve_parameter] = saved
        for source, value in zip(sources, values):
            expect(call(encode, binding, source), value)
            expect(call(decode, binding, value), source)
            law('OpenParameters.Transport.payload-roundtrip', binding, value)
        mutate_law('OpenParameters.Transport.payload-roundtrip', (binding, values[0]), encode, values[1])
        for size in range(4):
            for ordinals in itertools.product(range(3), repeat=size):
                xs = record(source_list, {'items': tuple(sources[i] for i in ordinals)})
                ys = value_listing([values[i] for i in ordinals])
                expect(call(encode_list, binding, xs), ys)
                expect(call(decode_list, binding, ys), xs)
                law('OpenParameters.Transport.resolve-preserves', binding, xs)
                expect(call(resolve_parameter, binding, xs), approximate(classifier))
        # Every supplied proof callback is executable, with complete evidence.
        for source, native, value in zip(sources, natives, values):
            for name, args in [('source-roundtrip', [source]),
                               ('native-roundtrip', [native, value.get(field(value_type, '.evidence'))])]:
                result = invoke_field(name, args)
                model.boundary(slots[name][1].result, 1, 1, result, 0)
                callback_checks += 1
        for c in (0, 1):
            expect(invoke_field('same', [c]), approximate(c))
            for i in range(3):
                expect(invoke_field('same-members', [c, c, approximate(c), natives[i], membership(c, i)]), membership(c, i))
        another_schema = record(approximation_type, {'items': approximate_rows[:1]})
        wrong_family = record(approximation_member, {
            field(approximation_member, '.index0'): another_schema,
            field(approximation_member, '.index1'): 0, field(approximation_member, '.index2'): 0,
            field(approximation_member, '.value'): evidence[0, 0]})
        refuse(lambda: invoke_field('same-members', [0, 0, wrong_family, natives[0], membership(0, 0)]))
        reordered_schema = record(approximation_type, {'items': approximate_rows[::-1]})
        reordered_member = record(approximation_member, {
            field(approximation_member, '.index0'): reordered_schema,
            field(approximation_member, '.index1'): 0, field(approximation_member, '.index2'): 0,
            field(approximation_member, '.value'): evidence[0, 0]})
        expect(invoke_field('same-members', [0, 0, reordered_member, natives[0], membership(0, 0)]), membership(0, 0))
        wrong = record(member_type, {field(member_type, '.index0'): 1-classifier,
            field(member_type, '.index1'): natives[0], field(member_type, '.value'): evidence[1-classifier, 0]})
        refuse(lambda: call(ctor(value_type), binding, natives[0], wrong))
        wrong = record(member_type, {field(member_type, '.index0'): classifier,
            field(member_type, '.index1'): natives[0], field(member_type, '.value'): evidence[classifier, 1]})
        refuse(lambda: call(ctor(value_type), binding, natives[0], wrong))
        refuse(lambda: call(encode, binding, natives[0]))
        for symbol, arguments, wrong, expected in [
                (encode, (binding, sources[0]), values[1], values[0]),
                (decode, (binding, values[0]), sources[1], sources[0]),
                (encode_list, (binding, record(source_list, {'items': sources[:2]})),
                 value_listing(values[1::-1]), value_listing(values[:2])),
                (decode_list, (binding, value_listing(values[:2])),
                 record(source_list, {'items': sources[1::-1]}), record(source_list, {'items': sources[:2]}))]:
            inputs, body, assertions = model.calculations[symbol]
            model.calculations[symbol] = (inputs, ('literal', wrong), assertions)
            try:
                assert not same(call(symbol, *arguments), expected), 'body mutation escaped comparison'
                mutations += 1
            finally:
                model.calculations[symbol] = (inputs, body, assertions)
    # An independently indexed source family and a stored membership family.
    # The same payloads are used at two indices; neither the index nor evidence
    # can be recovered by merely inspecting the payload.
    encode_at, decode_at, select, reindex = [roots[source] for source in names[4:8]]
    binding_type, _, source_type = [t for _, t in runtime(encode_at)]
    at_type = model.results[encode_at]
    row_type = next(t for f, t, _, _ in model.carriers[at_type][1] if f == field(at_type, '.value'))
    slots = {f.split('<', 1)[0].rsplit('.', 1)[-1]: (f, t) for f, t, _, _ in model.carriers[binding_type][1]
             if not f.startswith(('typeArgument', 'familyArgument'))}
    member_type = slots['admitted'][1].result
    schema_type = slots['member'][1]
    schema_row = next(t for f, t, _, _ in model.carriers[schema_type][1] if f == 'items')
    source_row = next(t for f, t, _, _ in model.carriers[source_type][1] if f == 'familyArgument2')
    bindings.clear()
    bindings.update(typeArgument0=(0, 1), typeArgument1=natives)
    bindings['familyArgument2'] = tuple(Record(source_row, (
        (field(source_row, '.index0'), c), (field(source_row, '.value'), source)))
        for c in (0, 1) for source in sources)
    source_members = {(c, i): record(source_type, {
        field(source_type, '.index0'): c, field(source_type, '.value'): source})
        for c in (0, 1) for i, source in enumerate(sources)}
    schema_rows = tuple(record(schema_row, {field(schema_row, '.index0'): c,
        field(schema_row, '.index1'): native, field(schema_row, '.value'): evidence[c, i]})
        for c in (0, 1) for i, native in enumerate(natives))
    schema = record(schema_type, {'items': schema_rows})
    members = {(c, i): record(member_type, {field(member_type, '.index0'): schema,
        field(member_type, '.index1'): c, field(member_type, '.index2'): native,
        field(member_type, '.value'): evidence[c, i]}) for c in (0, 1) for i, native in enumerate(natives)}
    def at_index(expressions):
        return 'if a0 == 0 ? (' + expressions[0] + ') else (' + expressions[1] + ')'
    def proof_expression(signature, arguments):
        symbol = ctor(signature.result)
        assert len(runtime(symbol)) == len(arguments), (symbol, runtime(symbol), arguments)
        return quote(symbol) + '(' + ', '.join([
            literal(bindings[f]) for f, _, _, _ in model.calculations[symbol][0]
            if f.startswith(('typeArgument', 'familyArgument'))] + arguments) + ')'
    expressions = {
        'encode': at_index([choose('a1', [source_members[c, i] for i in range(3)], natives) for c in (0, 1)]),
        'admitted': at_index([choose('a1', [source_members[c, i] for i in range(3)],
                                    [members[c, i] for i in range(3)]) for c in (0, 1)]),
        'decode': at_index([choose('a1', natives, [source_members[c, i] for i in range(3)]) for c in (0, 1)]),
        'source-roundtrip': proof_expression(slots['source-roundtrip'][1], ['a0', 'a1']),
        'payload-roundtrip': proof_expression(slots['payload-roundtrip'][1], ['a1'])}
    callbacks = {name: callback('indexedSchema' + name, slots[name][1], expression)
                 for name, expression in expressions.items()}
    refresh()
    binding = record(binding_type, {slots['member'][0]: schema,
                                   **{slots[name][0]: value for name, value in callbacks.items()}})
    projected('FamilyRelations', 'member', binding, schema)
    for c in (0, 1):
        for i in range(3):
            projected('FamilyRelations', 'encode', binding, natives[i], [c, source_members[c, i]])
            projected('FamilyRelations', 'admitted', binding, members[c, i], [c, source_members[c, i]])
            projected('FamilyRelations', 'decode', binding, source_members[c, i], [c, natives[i], members[c, i]])
        refuse(lambda: model.invoke_callback_many(call(alias('FamilyRelations', 'decode'), binding),
                                                  [c, natives[0], members[1-c, 0]], True, 0))
    mutate_projection('FamilyRelations', 'member', binding, record(schema_type, {'items': ()}), schema)
    equality_type = next(t for f, t, _, _ in model.carriers[at_type][1] if f == field(at_type, '.index-equality'))
    equalities = {c: call(ctor(equality_type), c) for c in (0, 1)}
    values = {}
    for c in (0, 1):
        for i, native in enumerate(natives):
            row = call(ctor(row_type), binding, c, native, members[c, i])
            values[c, i] = call(ctor(at_type), binding, c, row, equalities[c])
            expect(call(encode_at, binding, c, source_members[c, i]), values[c, i])
            expect(call(decode_at, binding, c, values[c, i]), source_members[c, i])
            expect(call(select, binding, c, values[c, i]), native)
            expect(call(reindex, binding, c, c, equalities[c], values[c, i]), values[c, i])
            for name in ('index-preserves', 'selection-preserves', 'source-roundtrip-at', 'wrapping-preserves'):
                law('FamilyRelations.Transport.' + name, binding, c, source_members[c, i])
            law('FamilyRelations.Transport.payload-roundtrip-at', binding, c, values[c, i])
            law('FamilyRelations.Transport.reindex-payload-preserves', binding, c, c, equalities[c], values[c, i])
            for name, args in [('source-roundtrip', [c, source_members[c, i]]),
                               ('payload-roundtrip', [c, native, members[c, i]])]:
                bound = model.evaluate(('project', ('literal', binding), slots[name][0]), {})
                result = model.invoke_callback_many(bound, args, True, 0)
                model.boundary(slots[name][1].result, 1, 1, result, 0)
                callback_checks += 1
    for c in (0, 1):
        for name in ('index-preserves', 'selection-preserves', 'source-roundtrip-at', 'wrapping-preserves'):
            refuse(lambda: law('FamilyRelations.Transport.' + name, binding, c, source_members[1-c, 0]))
        refuse(lambda: law('FamilyRelations.Transport.payload-roundtrip-at', binding, c, values[1-c, 0]))
        refuse(lambda: law('FamilyRelations.Transport.reindex-payload-preserves', binding, c, 1-c,
                           equalities[c], values[c, 0]))
        for name, arguments, helper, wrong in [
                ('index-preserves', (binding, c, source_members[c, 0]), encode_at, values[1-c, 0]),
                ('selection-preserves', (binding, c, source_members[c, 0]), encode_at, values[c, 1]),
                ('wrapping-preserves', (binding, c, source_members[c, 0]), encode_at, values[c, 1]),
                ('source-roundtrip-at', (binding, c, source_members[c, 0]), decode_at, source_members[c, 1]),
                ('payload-roundtrip-at', (binding, c, values[c, 0]), encode_at, values[c, 1]),
                ('reindex-payload-preserves', (binding, c, c, equalities[c], values[c, 0]), reindex, values[c, 1])]:
            mutate_law('FamilyRelations.Transport.' + name, arguments, helper, wrong)
        refuse(lambda: call(encode_at, binding, c, source_members[1-c, 0]))
        refuse(lambda: call(decode_at, binding, c, values[1-c, 0]))
        refuse(lambda: call(ctor(row_type), binding, c, natives[0], members[1-c, 0]))
        refuse(lambda: call(reindex, binding, c, 1-c, equalities[c], values[c, 0]))
        for symbol, arguments, wrong, expected in [
                (encode_at, (binding, c, source_members[c, 0]), values[c, 1], values[c, 0]),
                (decode_at, (binding, c, values[c, 0]), source_members[c, 1], source_members[c, 0]),
                (select, (binding, c, values[c, 0]), natives[1], natives[0]),
                (reindex, (binding, c, c, equalities[c], values[c, 0]), values[c, 1], values[c, 0])]:
            inputs, body, assertions = model.calculations[symbol]
            model.calculations[symbol] = (inputs, ('literal', wrong), assertions)
            try:
                assert not same(call(symbol, *arguments), expected), 'indexed body mutation escaped comparison'
                mutations += 1
            finally:
                model.calculations[symbol] = (inputs, body, assertions)
    assert exercised == set(statement_names), ('unexecuted schema laws', set(statement_names) - exercised)
    assert len(projection_aliases) == 11
    return {'operations': len(roots), 'statements': len(exercised), 'statementMutationsDetected': statement_mutations,
            'comparisons': comparisons, 'invalidBindingsRejected': rejected,
            'projectionAliasRoots': len(projection_aliases), 'projectionAliasComparisons': projection_comparisons,
            'projectionAliasMutationsDetected': projection_mutations,
            'bodyMutationsDetected': mutations, 'proofCallbackChecks': callback_checks}
