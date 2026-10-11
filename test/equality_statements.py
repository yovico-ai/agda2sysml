"""Execute native theorem statements, retaining their input evidence.

Names below are corpus acceptance expectations, never translation rules. The
oracle reads emitted SysML; checked Agda terms are not an execution shortcut.
"""
import itertools
import json
from pathlib import Path
from emitted_model import CalculationValue, Extent, Model, Record, same
from open_parameters import target_name


EXPECTED = {
    'AlgebraicValues.constantDispatch-first', 'AlgebraicValues.constantDispatch-second',
    'Coverage.Inventory.no-silent-omissions', 'DecisionTree.choose-false',
    'DecisionTree.choose-true', 'DecisionTree.fallback-preserves',
    'DecisionTree.guardedValue-accepts', 'DecisionTree.guardedValue-refuses',
    'Derivations.Trace.marks-preserve-bytes', 'Derivations.Trace.measured-bytes',
    'Diagnostics.Accounting.After.no-silent-omissions',
    'Diagnostics.Accounting.Before.no-silent-omissions', 'NaturalIndices.length-index',
    'DependentRecords.ProjectedInput.Input.F.decode-encode',
    'DependentRecords.ProjectedInput.Input.F.encode-decode', 'StructuredIndices.transport-inverse',
    'NaturalValues.source-roundtrip', 'NaturalValues.successor-preserves',
    'NaturalValues.target-roundtrip', 'RecursiveValues.count-preserves',
    'RecursiveValues.tag-preserves', 'RecursiveValues.payload-preserves',
    'RecursiveValues.forest-roundtrip', 'RecursiveValues.native-forest-roundtrip',
    'RecursiveValues.source-roundtrip', 'RecursiveValues.target-roundtrip',
    'Resolution.missing-exactly-empty', 'Resolution.resolved-exactly-one',
    'Resolution.singleton-resolves', 'SchemaConcatenation.associative',
    'Sharing.at-functional', 'SourceOccurrences.Catalog.catalog-identities-preserved',
    'SourceOccurrences.Catalog.resolved-is-unique',
}


def verify_equality_statements(output):
    ordering = Model('''attribute def EqualityFields {
      attribute binding : ScalarValues::Boolean [0..*];
      attribute payload : ScalarValues::Boolean [0..*] ordered nonunique;
    }''')
    sample = lambda binding, payload: Record('EqualityFields', (('binding', binding), ('payload', payload)))
    original = sample((False, True), (True, False, True))
    assert ordering.equal(original, sample((True, False), (True, False, True)))
    assert not ordering.equal(original, sample((True, False), (False, True, True)))
    assert not ordering.equal(original, sample((True, False), (True, False)))
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    model = Model((output / 'model.sysml').read_text() + '''
calc def statementIdentity { in x : Base::Anything [1]; return result : Base::Anything [1] = x; }
calc def admissionClassify {
  in x : Base::Anything [1];
  return result : 'Agda2SysML.DeclarationSelection.Roles' [1] =
    (if x == 0 ? 'Agda2SysML.DeclarationSelection.Roles.one'(
      'Agda2SysML.Obligations.Kind'::'Agda2SysML.Obligations.Kind.structure')
    else 'Agda2SysML.DeclarationSelection.Roles.more'(
      'Agda2SysML.Obligations.Kind'::'Agda2SysML.Obligations.Kind.behavior',
      'Agda2SysML.DeclarationSelection.Roles.one'(
        'Agda2SysML.Obligations.Kind'::'Agda2SysML.Obligations.Kind.statement')));
}
''')
    rows = report['nativeStatements']
    translated = {r['symbol'].split('#', 1)[0].removeprefix('Agda2SysML.'): r
                  for r in rows if r['status'] == 'translated'}
    assert EXPECTED <= translated.keys(), ('missing authored laws', EXPECTED - translated.keys())
    for row in rows:
        original = [o for o in report['obligations'] if o['symbol'] == row['symbol']]
        proof = [o for o in original if o['sourceKind'] == 'proof-source']
        assert proof and all(o['rule'] == 'source.proof' and o['target'] is None for o in proof)
        statement = [o for o in original if o['sourceKind'] == 'statement']
        assert len(statement) == 1
        if row['status'] == 'translated':
            assert statement[0]['rule'] == 'native.equality-statement'
            assert statement[0]['target'] == row['target'] and target_name(row['target']) in model.constraints
            assert row['reason'] is None and row['reasonCode'] is None
        else:
            assert row['target'] is None and row['reason'] and row['reasonCode']
            assert statement[0]['rule'] == 'source.statement'
    assert any(r['status'] == 'textual' for r in rows), 'unsupported statements silently disappeared'

    comparisons = rejected = 0
    exercised = set()
    premise_mutation = False

    def law(name, arguments):
        nonlocal comparisons
        symbol = target_name(translated[name]['target'])
        # The oracle's carrier-validity constraints deliberately accept raw
        # values. A theorem invocation has normal typed input boundaries.
        for (_, typ, low, high), value in zip(model.calculations[symbol][0], arguments):
            model.boundary(typ, low, high, value)
        assert model.invoke(symbol, arguments) is True, ('false translated law', name, arguments)
        comparisons += 1
        exercised.add(name)

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('invalid theorem input admitted')

    def operation(source):
        matches = [o for o in report['obligations'] if o['symbol'].startswith('Agda2SysML.' + source + '#')
                   and '@' not in o['symbol'] and o['sourceKind'] == 'behavior' and o['target']]
        assert len(matches) == 1, (source, matches)
        return target_name(matches[0]['target'])

    def inputs(name):
        return model.calculations[target_name(translated[name]['target'])][0]

    def constructor(typ, suffix):
        matches = [target_name(c['target']) for sh in report['algebraicCarriers']
                   if target_name(sh['target']) == typ for c in sh['constructors']
                   if c['symbol'].split('#', 1)[0].endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]

    opaque = tuple(Record('Opaque', (('id', n), ('history', (n, n, 10**40)))) for n in range(3))
    for domain in ((False, True), opaque):
        for left, right in itertools.product(domain, repeat=2):
            for name in ('DecisionTree.choose-true', 'DecisionTree.choose-false'):
                law(name, [domain, left, right])
            for name in ('AlgebraicValues.constantDispatch-first', 'AlgebraicValues.constantDispatch-second'):
                # The chosen schema is empty; retain its atom/family bindings.
                law(name, [(), domain, (), left, right])
        for value in domain:
            for name in ('DecisionTree.guardedValue-accepts', 'DecisionTree.guardedValue-refuses',
                         'Resolution.singleton-resolves'):
                law(name, [domain, value])

    encode = operation('NaturalValues.encode')
    for n in (0, 1, 2, 7, 10**40, 2**128 + 1):
        native = model.invoke(encode, [n])
        law('NaturalValues.source-roundtrip', [n])
        law('NaturalValues.target-roundtrip', [native])
        law('NaturalValues.successor-preserves', [n])
    refuse(lambda: law('NaturalValues.source-roundtrip', [-1]))
    refuse(lambda: law('NaturalValues.target-roundtrip', [Record(model.results[encode], ())]))

    associative = 'SchemaConcatenation.associative'
    list_type = inputs(associative)[1][1]
    extent = Extent('all naturals', lambda x: type(x) is int and x >= 0)
    listing = lambda values, domain=extent: Record(list_type, (('typeArgument0', domain), ('items', tuple(values))))
    sequences = ((), (0,), (7, 7), (10**40, 0, 7))
    for xs, ys, zs in itertools.product(sequences, repeat=3):
        law(associative, [extent, listing(xs), listing(ys), listing(zs)])
    law(associative, [(False, True), listing((True, False, True), (True, False)),
                     listing((), (False, True)), listing((False,), (True, False))])
    refuse(lambda: law(associative, [(True,), listing((), (False,)), listing((), (True,)), listing((), (True,))]))

    # Recursive values retain every ordered child and payload in the equality,
    # with the same general lowering used for scalar and sequence statements.
    source_law = 'RecursiveValues.source-roundtrip'
    tree_type = inputs(source_law)[-1][1]
    forest_type = model.calculations[constructor(tree_type, '.node')][0][-1][1]
    node = constructor(tree_type, '.node')
    empty, cons = (constructor(forest_type, suffix) for suffix in ('.empty', '.next'))
    binding = [(False, True), opaque]
    call = lambda symbol, *values: model.invoke(symbol, [*binding, *values])
    nil = call(empty)
    trees = [call(node, tag, payload, nil) for tag, payload in itertools.product(binding[0], opaque)]
    forests = [nil, call(cons, trees[0], nil), call(cons, trees[0], call(cons, trees[0], nil)),
               call(cons, trees[1], call(cons, trees[0], nil))]
    trees += [call(node, True, opaque[2], forest) for forest in forests[1:]]
    for tree in trees:
        law(source_law, [*binding, tree])
        law('RecursiveValues.count-preserves', [*binding, tree])
        law('RecursiveValues.tag-preserves', [*binding, tree])
        law('RecursiveValues.payload-preserves', [*binding, tree])
        native = call(operation('RecursiveValues.encode'), tree)
        law('RecursiveValues.target-roundtrip', [*binding, native])
    for forest in forests:
        law('RecursiveValues.forest-roundtrip', [*binding, forest])
        native = call(operation('RecursiveValues.encodeForest'), forest)
        law('RecursiveValues.native-forest-roundtrip', [*binding, native])
    # Extents are unordered bindings, not source-level constructor payloads.
    law(source_law, [(True, False), opaque[::-1], trees[0]])
    # A valid but changed decoded tree must falsify each new projection law.
    decode = operation('RecursiveValues.decode')
    saved = model.calculations[decode]
    for name, wrong in [('RecursiveValues.tag-preserves', trees[3]),
                        ('RecursiveValues.payload-preserves', trees[1])]:
        model.calculations[decode] = (saved[0], ('literal', wrong), saved[2])
        try:
            refuse(lambda: law(name, [*binding, trees[0]]))
        finally:
            model.calculations[decode] = saved
    for name in ('RecursiveValues.tag-preserves', 'RecursiveValues.payload-preserves'):
        refuse(lambda: law(name, [(False,), opaque[:1], trees[-1]]))

    # Safely recursive calculations can also occur in dependent contracts.
    # Check the complete generated inequality witnesses, not just their tags
    # or the successful admission of the two source operations.
    sum_bound = operation('RecursiveValues.child-sum-bound')
    decreases = operation('RecursiveValues.child-decreases')
    membership_type = model.calculations[sum_bound][0][-1][1]
    head = constructor(membership_type, '.head')
    tail = constructor(membership_type, '.tail')
    le_type, lt_type = model.results[sum_bound], model.results[decreases]
    zero_le, successor_le = (constructor(le_type, suffix) for suffix in ('.zero-le', '.successor-le'))
    zero_lt, successor_lt = (constructor(lt_type, suffix) for suffix in ('.zero-below', '.successor-below'))
    fixed_bindings = dict(zip(('typeArgument0', 'typeArgument1'), binding))

    def bound_call(symbol, *values):
        parameters = [fixed_bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                      if f.startswith('typeArgument')]
        return model.invoke(symbol, [*parameters, *values])

    def witness(a, b, strict=False):
        assert 0 <= a < b if strict else 0 <= a <= b
        if a == 0:
            return bound_call(zero_lt if strict else zero_le, b - int(strict))
        return bound_call(successor_lt if strict else successor_le, a - 1, b - 1,
                          witness(a - 1, b - 1, strict))

    # Independent counts come from the construction plan above, not the
    # emitted count calculation whose use inside contracts is under test.
    counted = [(trees[0], 1), (trees[-3], 2), (trees[-1], 3)]
    index_samples = []
    index_comparisons = 0
    for children in ((counted[0],), (counted[0], counted[0]),
                     (counted[2], counted[0], counted[1])):
        suffixes = [nil]
        for child, _ in reversed(children):
            suffixes.append(call(cons, child, suffixes[-1]))
        suffixes.reverse()
        total = sum(n for _, n in children)
        for position, (child, count) in enumerate(children):
            membership = bound_call(head, child, suffixes[position + 1])
            for earlier in reversed(range(position)):
                membership = bound_call(tail, child, children[earlier][0], suffixes[earlier + 1], membership)
            for symbol, values, expected in (
                (sum_bound, [child, suffixes[0], membership], witness(count, total)),
                (decreases, [child, suffixes[0], False, opaque[0], membership], witness(count, total + 1, True)),
            ):
                args = [*binding, *values]
                assert same(model.invoke(symbol, args), expected), ('dependent count contract changed', symbol)
                index_samples.append((symbol, args, expected))
                index_comparisons += 1
            # A valid membership for a different child/forest must not satisfy
            # the actual dependent input contract.
            refuse(lambda: call(sum_bound, child, nil, membership))
            wrong_child = trees[1] if same(child, trees[0]) else trees[0]
            refuse(lambda: call(sum_bound, wrong_child, suffixes[0], membership))

    # Selection returns complete membership evidence. Compute the expected
    # flattened inventory and witness position independently of select and
    # roots-for; exercise both clauses, repeated IDs and multiple roles.
    omissions = operation('DeclarationSelection.Selection.no-silent-omissions')
    selection_inputs = model.calculations[omissions][0]
    id_list, root_type, id_member, root_member = [a[1] for a in selection_inputs[-4:]]
    root_ctor = constructor(root_type, '.root')
    root_list = model.calculations[constructor(root_member, '.here')][0][-1][1]
    selection_bindings = {'typeArgument0': (0, 7, 10**40), 'typeArgument1': opaque}

    def selection_call(symbol, *values):
        parameters = [selection_bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                      if f.startswith('typeArgument')]
        return model.invoke(symbol, [*parameters, *values])

    def selection_list(typ, values):
        return Record(typ, tuple((f, selection_bindings[f]) for f, _, _, _ in model.carriers[typ][1]
                                if f.startswith('typeArgument')) + (('items', tuple(values)),))

    def membership(typ, list_type, values, position):
        value = values[position]
        witness = selection_call(constructor(typ, '.here'), value,
                                 selection_list(list_type, values[position + 1:]))
        for earlier in reversed(range(position)):
            witness = selection_call(constructor(typ, '.there'), value, values[earlier],
                                     selection_list(list_type, values[earlier + 1:]), witness)
        return witness

    kind = 'Agda2SysML.Obligations.Kind::Agda2SysML.Obligations.Kind.'
    classify = CalculationValue('admissionClassify')
    for ids in ((0,), (7,), (7, 0), (0, 7, 0), (10**40, 7)):
        roots = [tuple(selection_call(root_ctor, value, kind + role)
                       for role in (('structure',) if value == 0 else ('behavior', 'statement')))
                 for value in ids]
        flattened = tuple(root for group in roots for root in group)
        for position, value in enumerate(ids):
            id_witness = membership(id_member, id_list, ids, position)
            for role_position, root_value in enumerate(roots[position]):
                role_witness = membership(root_member, root_list, roots[position], role_position)
                expected = membership(root_member, root_list, flattened,
                                      sum(map(len, roots[:position])) + role_position)
                args = [*selection_bindings.values(), classify, value, selection_list(id_list, ids),
                        root_value, id_witness, role_witness]
                assert same(model.invoke(omissions, args), expected), 'selection witness changed'
                index_samples.append((omissions, args, expected))
                index_comparisons += 1
                wrong = args.copy()
                wrong[4] = selection_list(id_list, ())
                refuse(lambda: model.invoke(omissions, wrong))
                wrong = args.copy()
                wrong[3] = 7 if value == 0 else 0
                refuse(lambda: model.invoke(omissions, wrong))
                wrong = args.copy()
                wrong[5] = selection_call(root_ctor, value, kind + 'external-assumption')
                refuse(lambda: model.invoke(omissions, wrong))

    index_body_mutations = 0
    for symbol in (sum_bound, decreases, omissions):
        saved = model.calculations[symbol]
        constant = next(expected for name, _, expected in index_samples if name == symbol)
        model.calculations[symbol] = (saved[0], ('literal', constant), saved[2])
        detected = False
        try:
            for name, args, expected in index_samples:
                if name != symbol:
                    continue
                try:
                    assert same(model.invoke(symbol, args), expected)
                except AssertionError:
                    detected = True
                    break
            assert detected, ('constant witness mutation escaped', symbol)
            index_body_mutations += 1
        finally:
            model.calculations[symbol] = saved

    # The static family argument captures a runtime schema. The complete
    # binding and index must reach every nested helper call in the statement.
    captured_mutations = 0
    extent = (0, 7, 10**40)
    identity = CalculationValue('statementIdentity')
    def field(typ, suffix):
        matches = [f for f, _, _, _ in model.carriers[typ][1] if f.endswith(suffix)]
        assert len(matches) == 1, (typ, suffix, matches)
        return matches[0]
    def captured_record(typ, fields):
        return Record(typ, tuple((f, extent if f.startswith('typeArgument') else fields[f])
                                for f, _, _, _ in model.carriers[typ][1]))
    for name in ('DependentRecords.ProjectedInput.Input.F.decode-encode',
                 'StructuredIndices.transport-inverse'):
        signature = inputs(name)
        schema_type = signature[5][1]
        member_type = signature[-1][1]
        row_type = next(t for f, t, _, _ in model.carriers[schema_type][1] if f == 'items')
        rows = tuple(captured_record(row_type, {field(row_type, '.index0'): i,
                     field(row_type, '.value'): value}) for i in extent for value in opaque)
        schema = captured_record(schema_type, {'items': rows})
        other_schema = captured_record(schema_type, {'items': rows[:-1]})
        def member(i, value):
            return captured_record(member_type, {field(member_type, '.index0'): schema,
                field(member_type, '.index1'): i, field(member_type, '.value'): value})
        symbol = target_name(translated[name]['target'])
        helper = model.calculations[symbol][1][1][1]
        if name.endswith('decode-encode'):
            inverse = 'DependentRecords.ProjectedInput.Input.F.encode-decode'
            encode_helper = model.calculations[target_name(translated[inverse]['target'])][1][1][1]
            def encoded(i, value):
                return model.invoke(encode_helper, [extent, schema, i, member(i, value)])
            for i, value in itertools.product(extent, opaque):
                law(name, [extent, extent, extent, identity, identity, schema, i, member(i, value)])
                law(inverse, [extent, extent, extent, identity, identity, schema, i, encoded(i, value)])
            trials = [(name, helper, member(0, opaque[1]), member(0, opaque[0])),
                      (inverse, encode_helper, encoded(0, opaque[1]), encoded(0, opaque[0]))]
            for statement, changed_helper, wrong, argument in trials:
                saved = model.calculations[changed_helper]
                model.calculations[changed_helper] = (saved[0], ('literal', wrong), saved[2])
                try:
                    refuse(lambda: law(statement, [extent, extent, extent, identity, identity, schema, 0, argument]))
                    captured_mutations += 1
                finally:
                    model.calculations[changed_helper] = saved
            refuse(lambda: law(name, [extent, extent, extent, identity, identity, other_schema, 0, member(0, opaque[0])]))
            refuse(lambda: law(inverse, [extent, extent, extent, identity, identity, schema, 7, encoded(0, opaque[0])]))
        else:
            witness_type = signature[-2][1]
            refl = constructor(witness_type, '.refl')
            for i, value in itertools.product(extent, opaque):
                witness = model.invoke(refl, [extent, i])
                law(name, [extent, extent, extent, identity, identity, schema, i, i, witness, member(i, value)])
            witness = model.invoke(refl, [extent, 0])
            args = [extent, extent, extent, identity, identity, schema, 0, 0, witness, member(0, opaque[0])]
            saved = model.calculations[helper]
            model.calculations[helper] = (saved[0], ('literal', member(0, opaque[1])), saved[2])
            try:
                refuse(lambda: law(name, args))
                captured_mutations += 1
            finally:
                model.calculations[helper] = saved
            refuse(lambda: law(name, args[:7] + [7] + args[8:]))
            refuse(lambda: law(name, args[:5] + [other_schema] + args[6:]))

    vector_law = 'NaturalIndices.length-index'
    vector_type = inputs(vector_law)[-1][1]
    vector_nil, vector_cons = (constructor(vector_type, suffix) for suffix in ('.[]', '._∷_'))
    vector = model.invoke(vector_nil, [opaque])
    for size in range(5):
        law(vector_law, [opaque, size, vector])
        refuse(lambda: law(vector_law, [opaque, size + 1, vector]))
        vector = model.invoke(vector_cons, [opaque, size, opaque[size % len(opaque)], vector])

    # Equality premises remain full indexed witnesses, not Boolean assumptions.
    for name, values in (('Resolution.missing-exactly-empty', ()),
                         ('Resolution.resolved-exactly-one', (opaque[0],))):
        fields = inputs(name)
        xs = Record(fields[1][1], (('typeArgument0', opaque), ('items', values)))
        resolved = model.invoke(operation('Resolution.resolve'), [opaque, xs])
        evidence_type = fields[-1][1]
        refl = constructor(evidence_type, '.refl')
        witness = model.invoke(refl, [opaque, resolved])
        args = [opaque, xs, *values, witness]
        law(name, args)
        bad = Record(evidence_type, tuple((f, () if '.payload' in f else v) for f, v in witness.fields))
        refuse(lambda: law(name, args[:-1] + [bad]))
        # A perfectly valid witness for a different conclusion must fail too.
        other_xs = Record(fields[1][1], (('typeArgument0', opaque), ('items', (opaque[1],))))
        other = model.invoke(operation('Resolution.resolve'), [opaque, other_xs])
        wrong_witness = model.invoke(refl, [opaque, other])
        refuse(lambda: law(name, args[:-1] + [wrong_witness]))
        if name == 'Resolution.missing-exactly-empty':
            symbol = target_name(translated[name]['target'])
            saved = model.calculations[symbol]
            retained = [a for a in saved[2] if 'input1' not in repr(a)]
            assert len(retained) < len(saved[2]), 'missing premise index contracts'
            model.calculations[symbol] = (saved[0], saved[1], retained)
            try:
                # The conclusion is true for [], but a witness about a
                # different resolution must only be admitted after mutation.
                assert model.invoke(symbol, args[:-1] + [wrong_witness]) is True
                premise_mutation = True
            finally:
                model.calculations[symbol] = saved

    bindings = {**{'typeArgument' + str(i): opaque for i in range(4)},
                **{'familyArgument' + str(i): () for i in range(4)}}
    def bound_arguments(symbol, values):
        return [*[bindings[f] for f, _, _, _ in model.calculations[symbol][0]
                  if f.startswith(('typeArgument', 'familyArgument'))], *values]
    def bound_call(symbol, *values):
        return model.invoke(symbol, bound_arguments(symbol, values))
    def bound_law(name, *values):
        law(name, bound_arguments(target_name(translated[name]['target']), values))
    def list_value(typ, values):
        return Record(typ, tuple((f, bindings[f]) for f, _, _, _ in model.carriers[typ][1]
                                if f in bindings) + (('items', tuple(values)),))
    identity = CalculationValue('statementIdentity')

    name = 'DecisionTree.fallback-preserves'
    partial_type, tree_type = inputs(name)[-3][1], inputs(name)[-2][1]
    fallback = bound_call(constructor(tree_type, '.leaf'), identity)
    for partial in (bound_call(constructor(partial_type, '.miss')),
                    bound_call(constructor(partial_type, '.yield'), identity)):
        for value in opaque:
            bound_law(name, partial, fallback, value)

    name = 'Derivations.Trace.measured-bytes'
    doc_type = inputs(name)[-1][1]
    bytes_ctor = constructor(doc_type, '.bytes')
    byte_list = model.calculations[bytes_ctor][0][-1][1]
    plain = bound_call(bytes_ctor, list_value(byte_list, (opaque[0], opaque[0], opaque[2])))
    marked = bound_call(constructor(doc_type, '.mark'), opaque[1], plain)
    appended = bound_call(constructor(doc_type, '.append'), marked, plain)
    for doc in (plain, marked, appended):
        bound_law(name, doc)
        bound_law('Derivations.Trace.marks-preserve-bytes', identity, doc)

    for name in ('Coverage.Inventory.no-silent-omissions',
                 'Diagnostics.Accounting.Before.no-silent-omissions',
                 'Diagnostics.Accounting.After.no-silent-omissions'):
        ids_type, report_type = inputs(name)[-2][1], inputs(name)[-1][1]
        empty = bound_call(constructor(report_type, '.empty'))
        entry = constructor(report_type, '.entry')
        entry_type = model.calculations[entry][0][-2][1]
        item = bound_call(constructor(entry_type, '.textual'), opaque[0], opaque[1])
        singleton = bound_call(entry, opaque[0], list_value(ids_type, ()), item, empty)
        pair = bound_call(entry, opaque[0], list_value(ids_type, (opaque[0],)), item, singleton)
        for values, report_value in (((), empty), ((opaque[0],), singleton), ((opaque[0], opaque[0]), pair)):
            bound_law(name, list_value(ids_type, values), report_value)

    name = 'Sharing.at-functional'
    at_type, ids_type = inputs(name)[-1][1], inputs(name)[1][1]
    witness = bound_call(constructor(at_type, '.here'), opaque[0], list_value(ids_type, (opaque[1],)))
    xs = list_value(ids_type, opaque[:2])
    bound_law(name, xs, 0, opaque[0], opaque[0], witness, witness)
    refuse(lambda: bound_law(name, xs, 1, opaque[0], opaque[0], witness, witness))

    name = 'SourceOccurrences.Catalog.resolved-is-unique'
    ids_type, proof_type = inputs(name)[-3][1], inputs(name)[-1][1]
    refl = constructor(proof_type, '.refl')
    maybe_type = model.calculations[refl][0][-1][1]
    just = bound_call(constructor(maybe_type, '.just'), opaque[0])
    witness = bound_call(refl, just)
    bound_law(name, list_value(ids_type, (opaque[0],)), opaque[0], witness)
    refuse(lambda: bound_law(name, list_value(ids_type, opaque[:2]), opaque[0], witness))

    name = 'SourceOccurrences.Catalog.catalog-identities-preserved'
    catalogue_type = inputs(name)[-1][1]
    item_type = next(t for f, t, _, _ in model.carriers[catalogue_type][1] if f == 'items')
    occurrence = constructor(item_type, '.occurrence')
    key_type, owner_type = [t for f, t, _, _ in model.calculations[occurrence][0] if f.startswith('input')][:2]
    key_ctor = constructor(key_type, '.key')
    path_type = model.calculations[key_ctor][0][-1][1]
    key = bound_call(key_ctor, opaque[0], list_value(path_type, (0, 7, 7)))
    owner = bound_call(constructor(owner_type, '.just'), opaque[1])
    item = bound_call(occurrence, key, owner, opaque[2], opaque[0])
    for values in ((), (item,), (item, item)):
        bound_law(name, identity, list_value(catalogue_type, values))

    assert EXPECTED <= exercised, ('authored laws not executed', EXPECTED - exercised)

    # A changed conclusion must be observable, rather than treated as true
    # merely because the declaration originated from an Agda proof.
    symbol = target_name(translated['NaturalValues.source-roundtrip']['target'])
    saved = model.calculations[symbol]
    model.calculations[symbol] = (saved[0], ('literal', False), saved[2])
    refuse(lambda: law('NaturalValues.source-roundtrip', [7]))
    model.calculations[symbol] = saved
    return {'expectedStatements': len(EXPECTED), 'executedStatements': len(exercised),
            'comparisons': comparisons, 'invalidCasesRejected': rejected,
            'conclusionMutationDetected': True, 'premiseMutationDetected': premise_mutation,
            'computedIndexMutationsDetected': 2 + captured_mutations,
            'admittedIndexOperations': 3, 'admittedIndexComparisons': index_comparisons,
            'admittedIndexBodyMutationsDetected': index_body_mutations,
            'proofSourcesRetained': True}


if __name__ == '__main__':
    import sys
    print(json.dumps(verify_equality_statements(sys.argv[1]), indent=2))
