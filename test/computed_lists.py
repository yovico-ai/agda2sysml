"""Execute computed list indices with complete typed payloads and witnesses."""
import itertools
import json
from pathlib import Path

from emitted_model import CalculationValue, Model, Parser, Record, same, tokens
from open_parameters import target_name


def verify_computed_lists(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)
    roots, statements, bindings, samples = {}, {}, {}, {}
    comparisons = refused = mutations = 0

    def root(name):
        rows = [o for o in report['obligations']
                if o['symbol'].startswith('Agda2SysML.' + name + '#')
                and '@' not in o['symbol'] and o['kind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], name
        roots[name] = target_name(rows[0]['target'])
        return roots[name]

    def statement(name):
        rows = [o for o in report['nativeStatements']
                if o['symbol'].startswith('Agda2SysML.' + name + '#')
                and '@' not in o['symbol'] and o['status'] == 'translated']
        assert len(rows) == 1, name
        statements[name] = target_name(rows[0]['target'])
        return statements[name]

    def runtime(symbol):
        return [(f, t) for f, t, _, _ in model.calculations[symbol][0]
                if not f.startswith(('typeArgument', 'familyArgument'))]

    def constructor(typ, suffix):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def field(typ, suffix):
        matches = [f for f, _, _, _ in model.carriers[typ][1]
                   if f.split('<', 1)[0].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    def record(typ, values):
        return Record(typ, tuple((f, bindings[f] if f.startswith(('typeArgument', 'familyArgument')) else values[f])
                                for f, _, _, _ in model.carriers[typ][1]))

    def arguments(symbol, values):
        return [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                  if f.startswith(('typeArgument', 'familyArgument'))], *values]

    def call(symbol, *values):
        return model.invoke(symbol, arguments(symbol, values))

    def check(symbol, values, expected):
        nonlocal comparisons
        args = arguments(symbol, values)
        actual = model.invoke(symbol, args)
        assert same(actual, expected), ('complete computed-list result changed', symbol, comparisons)
        samples.setdefault(symbol, []).append((args, expected))
        comparisons += 1

    def refuse(action):
        nonlocal refused
        try:
            action()
        except AssertionError:
            refused += 1
            return
        raise AssertionError('inconsistent computed-list input admitted')

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
        raise AssertionError(('unsupported test literal', value))

    def expression(symbol, values):
        return quote(symbol) + '(' + ', '.join([
            *[literal(bindings[f]) for f, _, _, _ in model.calculations[symbol][0]
              if f.startswith(('typeArgument', 'familyArgument'))], *values]) + ')'

    # Cache only immutable values; retain references to prevent identity reuse.
    boundary, invoke = model.boundary, model.invoke
    checked, invoked = {}, {}
    def cached_boundary(carrier, low, high, value, depth=0):
        key = (id(carrier), low, high, id(value))
        if key not in checked:
            boundary(carrier, low, high, value, depth)
            checked[key] = (carrier, value)
    def cached_invoke(symbol, args, check=True, depth=0):
        key = (symbol, tuple(map(id, args)), check)
        if key not in invoked:
            invoked[key] = (tuple(args), invoke(symbol, args, check, depth))
        return invoked[key][1]
    model.boundary, model.invoke = cached_boundary, cached_invoke

    prefix = 'UniverseLevels.Runtime.'
    runtime_types, erase, restore, lower, lookup, native_lookup = [root(prefix + name)
        for name in ('runtimeTypes', 'erase', 'restore', 'lower', 'lookup', 'nativeLookup')]
    environment_roundtrip = statement(prefix + 'environment-roundtrip')
    lookup_preserves = statement(prefix + 'lookup-preserves')
    slots_type, env_type = [t for _, t in runtime(erase)]
    types_type, values_type = model.results[runtime_types], model.results[erase]
    position_type = runtime(lower)[-1][1]
    index_type = model.results[lower]
    slot_type = next(t for f, t, _, _ in model.carriers[slots_type][1] if f == 'items')
    level, value = [constructor(slot_type, '.' + name) for name in ('level', 'value')]
    empty, static, dynamic = [constructor(env_type, '.' + name) for name in ('empty', 'static', 'dynamic')]
    nil, cons = [constructor(values_type, '.' + name) for name in ('nil', 'cons')]
    here, skip_level, skip_value = [constructor(position_type, '.' + name) for name in ('here', 'skipLevel', 'skipValue')]
    first, next_index = [constructor(index_type, '.' + name) for name in ('first', 'next')]
    meaning_type = runtime(dynamic)[-2][1]
    row_type = next(t for f, t, _, _ in model.carriers[meaning_type][1] if f == 'familyArgument1')
    atoms = tuple(Record('TypeIdentity', (('name', n), ('history', (n, n, 10**40)))) for n in (0, 7))
    payloads = {(t, choice): Record('TypedPayload', (('owner', t), ('choice', choice), ('history', (choice, 10**40, choice))))
                for t in atoms for choice in (0, 1)}
    relation = tuple(Record(row_type, ((field(row_type, '.index0'), t), (field(row_type, '.value'), p)))
                     for (t, _), p in payloads.items())
    bindings.update(typeArgument0=atoms, familyArgument1=relation)

    def meaning(t, choice):
        return record(meaning_type, {field(meaning_type, '.index0'): t,
                                     field(meaning_type, '.value'): payloads[t, choice]})
    def slots(items):
        return record(slots_type, {'items': tuple(call(level, x) if tag == 'L' else call(value, x) for tag, x in items)})
    def types(items):
        return record(types_type, {'items': tuple(x for tag, x in items if tag == 'V')})
    def build(items, choices):
        if not items:
            return call(empty), call(nil)
        (tag, x), rest = items[0], items[1:]
        env, values = build(rest, choices if tag == 'L' else choices[1:])
        if tag == 'L':
            return call(static, slots(rest), x, env), values
        payload = meaning(x, choices[0])
        return call(dynamic, slots(rest), x, payload, env), call(cons, types(rest), x, payload, values)
    def position(items, selected):
        (_, t), rest = items[selected], items[selected+1:]
        p, ix = call(here, t, slots(rest)), call(first, t, types(rest))
        for offset in reversed(range(selected)):
            tag, x = items[offset]
            if tag == 'L':
                p = call(skip_level, t, slots(items[offset+1:]), x, p)
            else:
                p = call(skip_value, t, slots(items[offset+1:]), x, p)
                ix = call(next_index, t, types(items[offset+1:]), x, ix)
        return p, ix

    a, b = atoms
    layouts = ((), (('L', 0),), (('L', 10**40), ('L', 7)), (('V', a),),
               (('L', 0), ('V', a), ('L', 10**40)), (('V', b), ('L', 1), ('V', a)),
               (('V', a), ('V', a), ('V', b)), (('L', 4), ('V', b), ('V', b), ('L', 0), ('V', a)))
    for items in layouts:
        count = sum(tag == 'V' for tag, _ in items)
        for choices in itertools.product((0, 1), repeat=count):
            env, values = build(items, choices)
            check(runtime_types, [slots(items)], types(items))
            check(erase, [slots(items), env], values)
            check(restore, [slots(items), values], env)
            check(environment_roundtrip, [slots(items), env], True)
            ordinal = 0
            for selected, (tag, t) in enumerate(items):
                if tag == 'L': continue
                p, ix = position(items, selected)
                check(lower, [t, slots(items), p], ix)
                check(lookup, [t, slots(items), p, env], meaning(t, choices[ordinal]))
                check(native_lookup, [t, types(items), ix, values], meaning(t, choices[ordinal]))
                check(lookup_preserves, [t, slots(items), p, env], True)
                other = atoms[1 - atoms.index(t)]
                refuse(lambda: call(lower, other, slots(items), p))
                ordinal += 1
            refuse(lambda: call(erase, slots((*items, ('L', 1))), env))
            refuse(lambda: call(restore, slots((*items, ('V', a))), values))

    encode_member, decode_member = [root('StructuredIndices.Fibre.' + name) for name in ('encodeMember', 'decodeMember')]
    member_roundtrip = statement('StructuredIndices.Fibre.member-roundtrip')
    encode_sig, decode_sig, source_law, target_law, binding_type, schema_type, member_type = [t for _, t in runtime(encode_member)]
    sources = tuple(Record('SourceAtom', (('key', n), ('history', (n, 10**40)))) for n in (0, 7))
    targets = tuple(Record('TargetAtom', (('key', n), ('history', (10**40, n)))) for n in (8, 3))
    bindings.update(typeArgument0=sources, typeArgument1=targets)
    layouts = ((), (0,), (1,), (0, 0), (0, 1), (1, 0, 1))
    schemas = [record(schema_type, {'items': tuple(sources[i] for i in items)}) for items in layouts]
    member_values = [Record('DependentMember', (('ordinal', i), ('payload', (i, 10**40, i)))) for i in range(len(layouts))]
    row_type = next(t for f, t, _, _ in model.carriers[binding_type][1] if f == 'items')
    rows = tuple(record(row_type, {field(row_type, '.index0'): index, field(row_type, '.value'): payload})
                 for index, payload in zip(schemas, member_values))
    binding = record(binding_type, {'items': rows})
    members = [record(member_type, {field(member_type, '.index0'): binding,
                                    field(member_type, '.index1'): index,
                                    field(member_type, '.value'): payload})
               for index, payload in zip(schemas, member_values)]
    additions = []
    def callback(name, signature, body):
        additions.append('calc def ' + quote(name) + ' { in argument : ' + quote(signature.argument)
                         + ' [1]; return result : ' + quote(signature.result) + ' [1] = ' + body + '; }')
        return CalculationValue(name)
    encode = callback('testEncodeAtom', encode_sig,
                      '(if argument == ' + literal(sources[0]) + ' ? ' + literal(targets[0]) + ' else ' + literal(targets[1]) + ')')
    decode = callback('testDecodeAtom', decode_sig,
                      '(if argument == ' + literal(targets[0]) + ' ? ' + literal(sources[0]) + ' else ' + literal(sources[1]) + ')')
    source_refl, target_refl = [constructor(signature.result, '.refl') for signature in (source_law, target_law)]
    source_inverse = callback('testSourceInverse', source_law, expression(source_refl, ['argument']))
    target_inverse = callback('testTargetInverse', target_law, expression(target_refl, ['argument']))
    broken_decode = callback('testBrokenDecode', decode_sig, literal(sources[0]))
    model = Model(text + '\n' + '\n'.join(additions))
    boundary, invoke = model.boundary, model.invoke
    checked, invoked = {}, {}
    model.boundary, model.invoke = cached_boundary, cached_invoke
    conversion = [encode, decode, source_inverse, target_inverse, binding]
    for i, (index, member) in enumerate(zip(schemas, members)):
        check(encode_member, [*conversion, index, member], member)
        check(decode_member, [*conversion, index, member], member)
        check(member_roundtrip, [*conversion, index, member], True)
        wrong_index = schemas[(i + 1) % len(schemas)]
        refuse(lambda: call(encode_member, *conversion, wrong_index, member))
        refuse(lambda: call(decode_member, *conversion, wrong_index, member))
    for symbol in (encode_member, decode_member):
        refuse(lambda: call(symbol, encode, broken_decode, source_inverse, target_inverse, binding, schemas[2], members[2]))

    for symbol in (erase, restore, lower, lookup, encode_member, decode_member):
        args, expected = samples[symbol][0]
        changed = next(value for _, value in samples[symbol][1:] if not same(value, expected))
        mutant = Model(text + '\n' + '\n'.join(additions))
        inputs, _, assertions = mutant.calculations[symbol]
        mutant.calculations[symbol] = (inputs, Parser(tokens(literal(changed))).expression(), assertions)
        try:
            detected = not same(mutant.invoke(symbol, args), expected)
        except AssertionError:
            detected = True
        assert detected, ('constant-result mutation escaped', symbol)
        mutations += 1

    return {'operations': len(roots), 'statements': len(statements), 'comparisons': comparisons, 'invalidCasesRejected': refused,
            'bodyMutationsDetected': mutations}
