"""Compare complete outcomes from the self-spec's compiled callback consumers.

The target is parsed model.sysml, not the compiler's expression inventory.
"""
import itertools
import json
from pathlib import Path
from emitted_model import CalculationValue, Extent, Model, Record, same
from open_parameters import target_name


def verify_callbacks(output):
    output = Path(output)
    report = json.loads((output / 'correspondence.json').read_text())
    text = (output / 'model.sysml').read_text()
    model = Model(text)

    def root(source):
        rows = [o for o in report['obligations'] if o['symbol'].startswith(source + '#')
                and '@' not in o['symbol'] and o['sourceKind'] == 'behavior']
        assert len(rows) == 1 and rows[0]['status'] == 'discharged' and rows[0]['target'], ('callback consumer missing', source, rows)
        return target_name(rows[0]['target'])

    choose = root('Agda2SysML.DecisionTree.choose')
    guarded = root('Agda2SysML.DecisionTree.guardedValue')
    dispatch = root('Agda2SysML.AlgebraicValues.constantDispatch')
    comparisons = rejected = 0
    payloads = tuple(Record('Outcome', (('state', n), ('reason', reason),
                    ('detail', Record('Detail', (('history', (n, n, 10**40)),)))))
                     for n in (0, 7, 10**40) for reason in ('accepted', 'refused'))
    domains = ((False, True), (0, 7, 10**40), payloads)
    for values in domains:
        extent = values
        for flag, positive, negative in itertools.product((False, True), values, values):
            actual = model.invoke(choose, [extent, flag, positive, negative])
            assert same(actual, positive if flag else negative), 'tree changed a captured complete outcome'
            comparisons += 1
        # Rebind the same target to an unbounded natural domain.
        if type(values[0]) is int:
            extent = Extent('all naturals', lambda x: type(x) is int and x >= 0)
        for flag, value in itertools.product((False, True), values):
            actual = model.invoke(guarded, [extent, flag, value])
            typ = model.results[guarded]
            tag = actual.get('constructor')
            assert ('Maybe.just<' if flag else 'Maybe.nothing<') in tag, 'rule changed guard/refusal choice'
            fields = model.carriers[typ][1]
            present = [f for f, _, _, _ in fields if '.just<' in f and '.payload' in f]
            assert len(present) == 1
            assert same(actual.get(present[0]), value if flag else ()), 'rule erased an effect or retained an inactive effect'
            comparisons += 1

    # The two nullary constructor alternatives still carry exact schema and
    # binding metadata. Construct them through the emitted native calculations.
    atom_binding = (False, True)
    family_binding = ()
    # Resolve instantiated constructor calculations by the dispatch input type.
    input_type = model.calculations[dispatch][0][-1][1]
    sum_report = next(c for c in report['algebraicCarriers'] if target_name(c['target']) == input_type)
    assert len(sum_report['constructors']) == 2
    # Constructor helpers may share the same family while differing by fibre.
    constructors = {c['symbol'].split('#')[0].rsplit('.', 1)[-1]: target_name(c['target'])
                    for c in sum_report['constructors']}
    # Detailed dependent construction is verified below against the actual
    # signature, rather than assuming constructor parameter elision.
    assert set(constructors) == {'here', 'there'}
    suffix = '<type parameter 0, type family 1>'
    nil_fields = model.invoke('Agda2SysML.AlgebraicValues.Fields.nil' + suffix,
                              [atom_binding, family_binding])
    here_inputs = model.calculations[constructors['here']][0]
    empty = Record(here_inputs[-3][1], (('typeArgument0', atom_binding), ('items', ())))
    schemas_type = here_inputs[-2][1]
    def schemas(values):
        return Record(schemas_type, (('typeArgument0', atom_binding), ('items', tuple(values))))
    singleton = model.invoke(constructors['here'], [atom_binding, family_binding, empty, schemas(()), nil_fields])
    alternatives = (
        model.invoke(constructors['here'], [atom_binding, family_binding, empty, schemas((empty,)), nil_fields]),
        model.invoke(constructors['there'], [atom_binding, family_binding, empty, schemas((empty,)), singleton]),
    )
    for values in domains:
        for branch, positive, negative in itertools.product((0, 1), values, values):
            actual = model.invoke(dispatch, [atom_binding, values, family_binding, positive, negative, alternatives[branch]])
            assert same(actual, positive if branch == 0 else negative), 'handler changed a complete captured branch result'
            comparisons += 1

    def refuse(action):
        nonlocal rejected
        try:
            action()
        except AssertionError:
            rejected += 1
            return
        raise AssertionError('invalid callback boundary admitted')

    refuse(lambda: model.invoke(choose, [(False,), True, True, False]))
    refuse(lambda: model.invoke(guarded, [(False,), True, True]))
    refuse(lambda: model.invoke(choose, [(False, True), 1, True, False]))
    refuse(lambda: model.invoke(dispatch, [atom_binding, (False, True), family_binding, True, False, singleton]))
    # A late Result type parameter now permits the original generic dispatch
    # calculation. Its supplied handler and sum must have the same schema.
    generic = root('Agda2SysML.AlgebraicValues.dispatch')
    handler_type = model.calculations[generic][0][-2][1]
    handler_report = next(c for c in report['algebraicCarriers'] if target_name(c['target']) == handler_type)
    handlers = {c['symbol'].split('#')[0].rsplit('.', 1)[-1]: target_name(c['target'])
                for c in handler_report['constructors']}
    signature = model.calculations[handlers['branch']][0][-2][1]
    quote = lambda value: "'" + value.replace('\\', '\\\\').replace("'", "\\'") + "'"
    model = Model(text + '\ncalc def singletonHandler { in value : ' + quote(signature.arguments[0])
                  + ' [1]; return result : ' + quote(signature.result) + ' [1] = true; }')
    bindings = [atom_binding, (False, True), family_binding]
    none = model.invoke(handlers['none'], bindings)
    one = model.invoke(handlers['branch'], [*bindings, empty, schemas(()), CalculationValue('singletonHandler'), none])
    assert model.invoke(generic, [*bindings, schemas((empty,)), one, singleton]) is True
    comparisons += 1
    refuse(lambda: model.invoke(generic, [*bindings, schemas((empty,)), one, alternatives[0]]))
    native_dispatch = root('Agda2SysML.AlgebraicValues.nativeDispatch')
    encoder = root('Agda2SysML.AlgebraicValues.encode')
    encoded = model.invoke(encoder, [atom_binding, family_binding, schemas((empty,)), singleton])
    assert model.invoke(native_dispatch, [*bindings, schemas((empty,)), one, encoded]) is True
    comparisons += 1
    refuse(lambda: model.invoke(native_dispatch, [*bindings, schemas((empty, empty)), one, encoded]))
    return {'comparisons': comparisons, 'invalidCasesRejected': rejected, 'operations': 5}
