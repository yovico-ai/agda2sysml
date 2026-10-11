"""Exercise dependent matches through the actual emitted SysML calculations.

Reference contexts are ordinary tuples; a layout is a mask choosing which
runtime slots bind lexical variables. Expected values never use target bodies.
"""
from functools import lru_cache
import itertools
import json
from pathlib import Path
from emitted_model import Model, Record, same
from open_parameters import target_name


def verify_dependent_patterns(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text())
    invoke = model.invoke

    @lru_cache(maxsize=16384)
    def cached(symbol, arguments, check, depth):
        return invoke(symbol, arguments, check, depth)
    model.invoke = lambda symbol, arguments, check=True, depth=0: cached(symbol, tuple(arguments), check, depth)
    model.boundary = lru_cache(maxsize=32768)(model.boundary)

    names = [f'RelationBindings.{n}' for n in ('lookup', 'position', 'boundValues', 'embed', 'evaluate', 'lower')]
    names += ['Sharing.expand', 'Derivations.Trace.Readiness.combine-ready']
    roots = {}
    for name in names:
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.' + name + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], name
        roots[name] = target_name(rows[0]['target'])
    law_names = [f'RelationBindings.{n}' for n in ('lookup-preserves', 'nonbinding-preserves-position',
                 'endpoint-preserves', 'equation-complete', 'equation-sound', 'new-binding-position')] + ['Sharing.reconstruction']
    laws = {}
    for name in law_names:
        rows = [s for s in report['nativeStatements'] if s['symbol'].startswith('Agda2SysML.' + name + '#')]
        assert len(rows) == 1 and rows[0]['status'] == 'translated', name
        laws[name] = target_name(rows[0]['target'])
    comparisons = rejected = mutations = 0
    samples = {}

    def expect(symbol, arguments, expected):
        nonlocal comparisons
        assert same(model.invoke(symbol, arguments), expected), (symbol, arguments)
        samples[symbol] = arguments, expected
        comparisons += 1

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('inconsistent dependent value admitted')

    def calculation(source):
        matches = [n for n in model.calculations if n.startswith('Agda2SysML.' + source + '<')]
        assert len(matches) == 1, (source, matches)
        return matches[0]

    def bound(symbol, bindings, values):
        fields = model.calculations[symbol][0]
        return [*[bindings[f] for f, _, _, _ in fields if f.startswith(('typeArgument', 'familyArgument'))], *values]

    def call(source, bindings, *values):
        symbol = calculation(source)
        return model.invoke(symbol, bound(symbol, bindings, values))

    def check_operation(source, bindings, values, expected):
        symbol = roots[source]
        expect(symbol, bound(symbol, bindings, values), expected)

    def law(source, bindings, values):
        symbol = laws[source]
        expect(symbol, bound(symbol, bindings, values), True)

    def family(member_type, slot, bindings, identities):
        fields = model.carriers[member_type][1]
        row_type = next(t for f, t, _, _ in fields if f == f'familyArgument{slot}')
        row_fields = model.carriers[row_type][1]
        index_field = next(f for f, _, _, _ in fields if '.index0' in f)
        value_field = next(f for f, _, _, _ in fields if '.value' in f)
        row_index = next(f for f, _, _, _ in row_fields if '.index0' in f)
        row_value = next(f for f, _, _, _ in row_fields if '.value' in f)
        payloads = {identity: tuple(Record('OpaqueEvidence', (('owner', identity), ('history', (i, i, 10**40))))
                                    for i in range(2)) for identity in identities}
        rows = tuple(Record(row_type, ((row_index, identity), (row_value, value)))
                     for identity, values in payloads.items() for value in values)
        bindings[f'familyArgument{slot}'] = rows

        def member(identity, token=0):
            value = payloads[identity][token]
            return Record(member_type, tuple((f, bindings[f]) for f, _, _, _ in fields
                                            if f.startswith(('typeArgument', 'familyArgument')))
                          + ((index_field, identity), (value_field, value)))
        return member

    different_sizes = 0
    for types in ((False, True), tuple(Record('TypeIdentity', (('name', n),)) for n in ('x', 'y'))):
        bindings = {'typeArgument0': types}
        snoc = calculation('RelationBindings.Values.snoc')
        member = family(model.calculations[snoc][0][-1][1], 1, bindings, types)

        @lru_cache(maxsize=None)
        def context(ts):
            if not ts:
                return call('RelationBindings.Context.empty', bindings)
            return call('RelationBindings.Context._▻_', bindings, context(ts[:-1]), ts[-1])

        @lru_cache(maxsize=None)
        def values(ts, data):
            if not ts:
                return call('RelationBindings.Values.none', bindings)
            return call('RelationBindings.Values.snoc', bindings, context(ts[:-1]), ts[-1],
                        values(ts[:-1], data[:-1]), data[-1])

        @lru_cache(maxsize=None)
        def variable(ts, i):
            if i == len(ts)-1:
                return call('RelationBindings.Variable.newest', bindings, ts[i], context(ts[:-1]))
            return call('RelationBindings.Variable.older', bindings, ts[i], context(ts[:-1]), ts[-1], variable(ts[:-1], i))

        for n in range(4):
            for ts in itertools.product(types, repeat=n):
                data = tuple(member(t, i % 2) for i, t in enumerate(ts))
                runtime, env = context(ts), values(ts, data)
                for mask in itertools.product((False, True), repeat=n):
                    layout = call('RelationBindings.Layout.start', bindings)
                    lexical_types = ()
                    for i, (t, binding) in enumerate(zip(ts, mask)):
                        layout = call('RelationBindings.Layout.' + ('bind' if binding else 'nonbinding'), bindings,
                                      context(ts[:i]), context(lexical_types), t, layout)
                        if binding:
                            lexical_types += (t,)
                    lexical = context(lexical_types)
                    chosen = tuple(i for i, binding in enumerate(mask) if binding)
                    lexical_data = tuple(data[i] for i in chosen)
                    lexical_env = values(lexical_types, lexical_data)
                    different_sizes += len(ts) != len(lexical_types)
                    check_operation('RelationBindings.boundValues', bindings, [runtime, lexical, layout, env], lexical_env)
                    law('RelationBindings.new-binding-position', bindings, [runtime, lexical, types[0], layout])

                    def endpoint_laws(t, endpoint, datum):
                        args = [runtime, lexical, t, layout, endpoint, env]
                        law('RelationBindings.endpoint-preserves', bindings, args)
                        refl = 'Agda.Builtin.Equality._≡_.refl<level 0, type family 1<captured index 0>>'
                        proof = model.invoke(refl, bound(refl, bindings, [t, datum]))
                        for name in ('equation-complete', 'equation-sound'):
                            law('RelationBindings.' + name, bindings, args + [datum, proof])

                    for i, source_i in enumerate(chosen):
                        t, datum = ts[source_i], data[source_i]
                        p, embedded = variable(lexical_types, i), variable(ts, source_i)
                        check_operation('RelationBindings.embed', bindings, [runtime, lexical, t, layout, p], embedded)
                        check_operation('RelationBindings.position', bindings, [runtime, t, embedded], source_i)
                        check_operation('RelationBindings.lookup', bindings, [runtime, t, embedded, env], datum)
                        law('RelationBindings.lookup-preserves', bindings, [runtime, lexical, t, layout, p, env])
                        law('RelationBindings.nonbinding-preserves-position', bindings,
                            [runtime, lexical, t, types[0], layout, p])
                        endpoint = call('RelationBindings.Endpoint.reference', bindings, lexical, t, p)
                        lowered = call('RelationBindings.Endpoint.reference', bindings, runtime, t, embedded)
                        check_operation('RelationBindings.lower', bindings, [runtime, lexical, t, layout, endpoint], lowered)
                        check_operation('RelationBindings.evaluate', bindings, [runtime, t, lowered, env], datum)
                        endpoint_laws(t, endpoint, datum)
                    for t in types:
                        datum = member(t, 1)
                        endpoint = call('RelationBindings.Endpoint.literal', bindings, lexical, t, datum)
                        lowered = call('RelationBindings.Endpoint.literal', bindings, runtime, t, datum)
                        check_operation('RelationBindings.lower', bindings, [runtime, lexical, t, layout, endpoint], lowered)
                        check_operation('RelationBindings.evaluate', bindings, [runtime, t, lowered, env], datum)
                        endpoint_laws(t, endpoint, datum)

        t, other = types
        p = variable((t,), 0)
        lookup = roots['RelationBindings.lookup']
        refuse(lambda: model.invoke(lookup, bound(lookup, bindings,
               [context((other,)), t, p, values((other,), (member(other),))])))
        refuse(lambda: call('RelationBindings.Values.snoc', bindings, context(()), t,
                            values((), ()), member(other)))
        bad_layout = call('RelationBindings.Layout.nonbinding', bindings, context(()), context(()), t,
                          call('RelationBindings.Layout.start', bindings))
        embed = roots['RelationBindings.embed']
        refuse(lambda: model.invoke(embed, bound(embed, bindings, [context((t,)), context((t,)), t, bad_layout, p])))
        literal = call('RelationBindings.Endpoint.literal', bindings, context(()), t, member(t, 0))
        start = call('RelationBindings.Layout.start', bindings)
        refl = 'Agda.Builtin.Equality._≡_.refl<level 0, type family 1<captured index 0>>'
        proof = model.invoke(refl, bound(refl, bindings, [t, member(t, 0)]))
        for name in ('equation-complete', 'equation-sound'):
            symbol = laws['RelationBindings.' + name]
            refuse(lambda: model.invoke(symbol, bound(symbol, bindings,
                   [context(()), context(()), t, start, literal, values((), ()), member(t, 1), proof])))

    # Cross-module cases below exercise the same refinement rule with trees
    # and evidence indexed by a list of checked origins.
    def native_list(typ, bindings, items):
        return Record(typ, tuple((f, tuple(items) if f == 'items' else bindings[f])
                                for f, _, _, _ in model.carriers[typ][1]))

    for labels in ((0, 10**40), tuple(Record('Label', (('value', n),)) for n in ('left', 'right'))):
        bindings = {'typeArgument0': labels}
        atom = lambda label: call('Sharing.Tree.atom', bindings, label)
        fork = lambda label, left, right: call('Sharing.Tree.fork', bindings, label, left, right)
        trees = [atom(label) for label in labels]
        trees += [fork(label, left, right) for label, left, right in itertools.product(labels, trees, trees)]
        trees += [fork(labels[0], trees[2], trees[3])]
        # Repeated store values must not identify distinct reference positions.
        store_values = tuple(trees + trees[:2])
        inline_atom = calculation('Sharing.Shared.inline-atom')
        list_type = next(t for f, t, _, _ in model.calculations[inline_atom][0] if f == 'input0')
        store = native_list(list_type, bindings, store_values)

        def at(which, *args):
            symbol = next(n for n in model.calculations
                          if n.startswith('Agda2SysML.Sharing.At.' + which + '<Agda2SysML.Sharing.Tree<'))
            return model.invoke(symbol, bound(symbol, bindings, args))

        def evidence(items, position):
            tail = native_list(list_type, bindings, items[1:])
            if position == 0:
                return at('here', items[0], tail)
            return at('there', items[position], items[0], tail, position-1, evidence(items[1:], position-1))

        references = []
        for i, tree in enumerate(store_values):
            ref = call('Sharing.Shared.reference', bindings, store, i, tree, evidence(store_values, i))
            references.append(ref)
            check_operation('Sharing.expand', bindings, [store, tree, ref], tree)
            law('Sharing.reconstruction', bindings, [store, tree, ref])
        for i, label in enumerate(labels):
            shared = call('Sharing.Shared.inline-atom', bindings, store, label)
            check_operation('Sharing.expand', bindings, [store, trees[i], shared], trees[i])
            law('Sharing.reconstruction', bindings, [store, trees[i], shared])
        for label, a, b in itertools.product(labels, range(4), range(4)):
            tree = fork(label, trees[a], trees[b])
            shared = call('Sharing.Shared.inline-fork', bindings, store, label, trees[a], trees[b], references[a], references[b])
            check_operation('Sharing.expand', bindings, [store, tree, shared], tree)
            law('Sharing.reconstruction', bindings, [store, tree, shared])
        refuse(lambda: call('Sharing.Shared.reference', bindings, store, 1, trees[0], evidence(store_values, 0)))
        refuse(lambda: call('Sharing.Shared.reference', bindings, store, 0, trees[1], evidence(store_values, 0)))
        expand = roots['Sharing.expand']
        refuse(lambda: model.invoke(expand, bound(expand, bindings, [store, trees[1], references[0]])))

    checked = (Record('CheckedNode', (('id', 7),)), Record('CheckedNode', (('id', 10**40),)))
    bindings = dict(typeArgument0=checked, typeArgument1=('rule',), typeArgument2=('target',), typeArgument3=('byte',))
    ready_input = calculation('Derivations.Trace.Readiness.Ready.input')
    ready_fields = {f: t for f, t, _, _ in model.calculations[ready_input][0]}
    member = family(ready_fields['input2'], 4, bindings, checked)
    list_type = ready_fields['input1']

    def origins(xs):
        return native_list(list_type, bindings,
                           [call('Derivations.Trace.Origin.checked', bindings, c) for c in xs])

    @lru_cache(maxsize=None)
    def ready(xs):
        if not xs:
            return call('Derivations.Trace.Readiness.Ready.empty', bindings)
        return call('Derivations.Trace.Readiness.Ready.input', bindings, xs[0], origins(xs[1:]),
                    member(xs[0], len(xs) % 2), ready(xs[1:]))

    # Preserve the distinct evidence payloads on both sides of concatenation.
    def append_expected(xs, ys):
        if not xs:
            return ready(ys)
        tail_origins = origins(xs[1:] + ys)
        return call('Derivations.Trace.Readiness.Ready.input', bindings, xs[0], tail_origins,
                    member(xs[0], len(xs) % 2), append_expected(xs[1:], ys))

    lists = [xs for n in range(3) for xs in itertools.product(checked, repeat=n)]
    for xs, ys in itertools.product(lists, repeat=2):
        check_operation('Derivations.Trace.Readiness.combine-ready', bindings,
                        [origins(xs), origins(ys), ready(xs), ready(ys)], append_expected(xs, ys))
    combine = roots['Derivations.Trace.Readiness.combine-ready']
    refuse(lambda: model.invoke(combine, bound(combine, bindings,
           [origins((checked[1],)), origins(()), ready((checked[0],)), ready(())])))
    generated = native_list(list_type, bindings, [call('Derivations.Trace.Origin.generated', bindings, 'rule')])
    refuse(lambda: model.invoke(combine, bound(combine, bindings,
           [generated, origins(()), ready((checked[0],)), ready(())])))

    for symbol in [*roots.values(), *laws.values()]:
        assert symbol in samples, ('operation lacks a behavior check', symbol)
        args, expected = samples[symbol]
        inputs, body, assertions = model.calculations[symbol]
        model.calculations[symbol] = inputs, ('literal', False), assertions
        cached.cache_clear()
        try:
            try:
                result = model.invoke(symbol, args)
            except AssertionError:
                result = None
            assert not same(result, expected), ('body mutation escaped', symbol)
            mutations += 1
        finally:
            model.calculations[symbol] = inputs, body, assertions
            cached.cache_clear()
    return dict(operations=len(roots), statements=len(laws), comparisons=comparisons, invalidCasesRejected=rejected,
                bodyMutationsDetected=mutations, differentContextSizes=different_sizes,
                completeEvidencePreserved=True)
