"""Independent interpreter for the emitted native SysML expression subset.

This is a test oracle. It reads model.sysml, never compiler expression JSON.
The production model is also checked by the pinned OMG parser/validator.
Unsupported syntax fails explicitly; assertions and carrier cardinalities are
checked as well as returned values. Native type extents may be infinite.
"""
from dataclasses import dataclass
import re


@dataclass(frozen=True)
class Record:
    type: str
    fields: tuple

    def get(self, field):
        return dict(self.fields).get(field, ())


@dataclass(frozen=True)
class Extent:
    name: str
    member: object


@dataclass(frozen=True)
class CalculationValue:
    """A native calculation usage bound to a parsed calculation definition."""
    symbol: str


@dataclass(frozen=True)
class CallableSignature:
    argument: str
    result: str
    assertions: tuple


@dataclass
class BoundCalculation:
    value: object
    signature: CallableSignature
    scope: str
    environment: dict


def sequence(value):
    return value if isinstance(value, tuple) else (value,)


def same(left, right):
    if type(left) is not type(right):
        return False
    return left == right


def includes(extent, values):
    if isinstance(extent, Extent):
        return all(extent.member(value) for value in sequence(values))
    return all(any(same(value, member) for member in sequence(extent)) for value in sequence(values))


def same_extent(left, right):
    if isinstance(left, Extent) or isinstance(right, Extent):
        return same(left, right)
    return includes(left, right) and includes(right, left)


TOKEN = re.compile(r"/\*.*?\*/|//[^\n]*|'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\"|"
                   r"::|->|==|!=|<=|>=|\.\.|[(){}\[\],;.=+*<>:-]|[0-9]+|[^\s(){}\[\],;.=+*<>:'\"/-]+", re.S)


def tokens(text):
    return [m.group() for m in TOKEN.finditer(text) if not m.group().startswith(('/*', '//'))]


def name(token):
    if token.startswith("'"):
        return re.sub(r"\\(.)", r"\1", token[1:-1])
    return token


class Parser:
    def __init__(self, values):
        self.values = values
        self.i = 0

    def peek(self):
        return self.values[self.i] if self.i < len(self.values) else None

    def pop(self):
        value = self.peek()
        if value is None:
            raise AssertionError('unexpected end of native expression')
        self.i += 1
        return value

    def take(self, token):
        if self.peek() == token:
            self.i += 1
            return True
        return False

    def expect(self, token):
        actual = self.pop()
        assert actual == token, (token, actual, self.values[max(0, self.i-5):self.i+5])

    def qualified(self):
        parts = [name(self.pop())]
        while self.take('::'):
            parts.append(name(self.pop()))
        return '::'.join(parts)

    def multiplicity(self):
        low = high = 1
        if self.take('['):
            low = int(self.pop())
            high = low
            if self.take('..'):
                value = self.pop()
                high = None if value == '*' else int(value)
            self.expect(']')
        return low, high

    def callable_body(self):
        self.expect('{')
        self.expect('in'); assert self.qualified() == 'argument'; self.expect(':')
        domain = self.qualified()
        assert self.multiplicity() == (1, 1); self.expect(';')
        self.expect('return'); assert self.qualified() == 'result'; self.expect(':')
        codomain = self.qualified()
        assert self.multiplicity() == (1, 1); self.expect(';')
        contracts = []
        while self.take('assert'):
            self.expect('constraint'); self.expect('{')
            contracts.append(self.expression()); self.expect('}')
        self.expect('}')
        return CallableSignature(domain, codomain, tuple(contracts))

    PRECEDENCE = {'or': 1, 'and': 2, '==': 3, '!=': 3, '<': 4, '>': 4,
                  '<=': 4, '>=': 4, 'hastype': 4, 'istype': 4, 'as': 4, '+': 5, '-': 5, '*': 6}

    def expression(self, minimum=0):
        if self.take('if'):
            condition = self.expression()
            self.expect('?')
            yes = self.expression()
            self.expect('else')
            left = ('if', condition, yes, self.expression())
        elif self.take('not'):
            left = ('not', self.expression(7))
        elif self.take('new'):
            carrier = self.qualified()
            self.expect('(')
            fields = []
            if not self.take(')'):
                while True:
                    field = self.qualified()
                    self.expect('=')
                    fields.append((field, self.expression()))
                    if self.take(')'):
                        break
                    self.expect(',')
            left = ('new', carrier, fields)
        elif self.take('('):
            elements = [self.expression()]
            while self.take(','):
                elements.append(self.expression())
            self.expect(')')
            left = elements[0] if len(elements) == 1 else ('sequence', elements)
        else:
            value = self.peek()
            if value in ('true', 'false', 'null', '*') or value.isdecimal():
                self.pop()
                left = ('literal', {'true': True, 'false': False, 'null': (), '*': float('inf')}.get(value, int(value) if value.isdecimal() else None))
            else:
                reference = self.qualified()
                if self.take('('):
                    arguments = []
                    if not self.take(')'):
                        while True:
                            arguments.append(self.expression())
                            if self.take(')'):
                                break
                            self.expect(',')
                    left = ('call', reference, arguments)
                else:
                    left = ('reference', reference)
        while True:
            if self.take('.'):
                left = ('project', left, self.qualified())
            elif self.take('('):
                arguments = []
                if not self.take(')'):
                    while True:
                        arguments.append(self.expression())
                        if self.take(')'):
                            break
                        self.expect(',')
                left = ('apply', left, arguments)
            elif self.take('->'):
                quantifier = self.pop()
                assert quantifier in ('forAll', 'exists'), ('unsupported native quantifier', quantifier)
                self.expect('{')
                self.expect('in')
                binder = name(self.pop())
                self.expect(';')
                condition = self.expression()
                self.expect('}')
                left = ('forall' if quantifier == 'forAll' else 'exists', left, binder, condition)
            elif self.peek() in self.PRECEDENCE and self.PRECEDENCE[self.peek()] >= minimum:
                op = self.pop()
                right = ('reference', self.qualified()) if op in ('as', 'istype', 'hastype') else self.expression(self.PRECEDENCE[op] + 1)
                left = (op, left, right)
            else:
                return left


def definition_blocks(text):
    values = tokens(text)
    for i in range(len(values) - 3):
        if values[i] in ('calc', 'constraint', 'attribute', 'enum') and values[i+1] == 'def' and values[i+3] == '{':
            depth, j = 1, i + 4
            while depth:
                depth += (values[j] == '{') - (values[j] == '}')
                j += 1
            yield values[i], name(values[i+2]), values[i+4:j-1]


class Model:
    def __init__(self, text):
        self.calculations = {}
        self.carriers = {}
        self.results = {}
        self.constraints = set()
        self.field_modes = {}
        for kind, symbol, body in definition_blocks(text):
            if kind == 'enum':
                self.carriers[symbol] = ('enum', [name(body[i+1]) for i in range(len(body)-1) if body[i] == 'enum'], [])
                continue
            parser = Parser(body)
            inputs, fields, assertions, result = [], [], [], None
            while parser.peek() is not None:
                if parser.take('assert'):
                    parser.expect('constraint')
                    if parser.peek() != '{':
                        parser.pop()
                    parser.expect('{')
                    assertions.append(parser.expression())
                    parser.expect('}')
                elif parser.peek() in ('in', 'attribute', 'ref'):
                    prefix = parser.pop()
                    assert prefix != 'ref' or parser.peek() == 'calc', 'unsupported reference field'
                    if parser.take('calc'):
                        field = parser.qualified()
                        low, high = parser.multiplicity()
                        carrier = parser.callable_body()
                        (fields if kind == 'attribute' else inputs).append((field, carrier, low, high))
                        continue
                    if parser.take('redefines'):
                        while parser.pop() != ';':
                            pass
                        continue
                    field = parser.qualified()
                    parser.expect(':')
                    carrier = parser.qualified()
                    low = high = 1
                    if parser.take('['):
                        low = int(parser.pop())
                        high = low
                        if parser.take('..'):
                            value = parser.pop()
                            high = None if value == '*' else int(value)
                        parser.expect(']')
                    qualifiers = set()
                    while not parser.take(';'):
                        qualifier = parser.pop()
                        assert qualifier in ('ordered', 'nonunique'), 'unsupported multiplicity qualifier'
                        qualifiers.add(qualifier)
                    if kind == 'attribute':
                        self.field_modes[symbol, field] = ('ordered' in qualifiers, 'nonunique' in qualifiers)
                    (fields if kind == 'attribute' else inputs).append((field, carrier, low, high))
                elif parser.take('return'):
                    if parser.take('ref'):
                        parser.expect('calc'); assert parser.qualified() == 'result'
                        assert parser.multiplicity() == (1, 1)
                        parser.expect('=')
                        result = parser.expression()
                        self.results[symbol] = parser.callable_body()
                        continue
                    parser.qualified()
                    parser.expect(':')
                    self.results[symbol] = parser.qualified()
                    if parser.take('['):
                        parser.expect('1'); parser.expect(']')
                    parser.expect('=')
                    result = parser.expression()
                    parser.expect(';')
                elif kind == 'constraint' and result is None:
                    self.results[symbol] = 'ScalarValues::Boolean'
                    self.constraints.add(symbol)
                    result = parser.expression()
                else:
                    raise AssertionError(('unsupported emitted definition', kind, symbol, parser.peek()))
            if kind == 'attribute':
                self.carriers[symbol] = ('record', fields, assertions)
            else:
                assert result is not None, ('missing native body', symbol)
                self.calculations[symbol] = (inputs, result, assertions)

    def equal(self, left, right):
        """Data-value equality respects declared feature ordering (KerML 7.4.2).

        In particular an unordered extent is not an ordered source list. Keep
        all declared payload/evidence fields; do not erase metadata by name.
        """
        if type(left) is not type(right):
            return False
        if same(left, right):
            return True
        if isinstance(left, tuple):
            return len(left) == len(right) and all(self.equal(x, y) for x, y in zip(left, right))
        if not isinstance(left, Record) or left.type not in self.carriers:
            return same(left, right)
        if left.type != right.type:
            return False
        for field, _, _, _ in self.carriers[left.type][1]:
            x, y = left.get(field), right.get(field)
            if isinstance(x, Extent) or isinstance(y, Extent):
                if not same(x, y): return False
                continue
            xs, ys = sequence(x), sequence(y)
            ordered, nonunique = self.field_modes.get((left.type, field), (False, False))
            if ordered:
                if not self.equal(xs, ys): return False
            elif nonunique:
                remaining = list(ys)
                for value in xs:
                    match = next((i for i, other in enumerate(remaining) if self.equal(value, other)), None)
                    if match is None: return False
                    remaining.pop(match)
                if remaining: return False
            elif not (self.includes(xs, ys) and self.includes(ys, xs)):
                return False
        return True

    def includes(self, extent, values):
        if isinstance(extent, Extent):
            return includes(extent, values)
        return all(any(self.equal(value, member) for member in sequence(extent)) for value in sequence(values))

    def invoke(self, symbol, arguments, check=True, depth=0):
        assert depth < 500, 'native recursion did not terminate'
        symbol = symbol.removeprefix('AgdaModel::')
        inputs, body, assertions = self.calculations[symbol]
        assert len(inputs) == len(arguments), ('native arity mismatch', symbol, len(arguments), len(inputs))
        env = {field: value for (field, _, _, _), value in zip(inputs, arguments)}
        env.update({symbol + '::' + field: value for field, value in list(env.items())})
        for (field, carrier, _, _), value in zip(inputs, arguments):
            if isinstance(carrier, CallableSignature):
                assert isinstance(value, (CalculationValue, BoundCalculation)), 'callable binding is not a calculation'
                binding = BoundCalculation(value, carrier, symbol + '::' + field, dict(env))
                env[field] = env[symbol + '::' + field] = binding
        if check and symbol not in self.constraints:
            for (_, carrier, low, high), value in zip(inputs, arguments):
                self.boundary(carrier, low, high, value, depth)
        result = self.evaluate(body, env, check, depth)
        if isinstance(self.results[symbol], CallableSignature):
            result = BoundCalculation(result, self.results[symbol], symbol + '::result', dict(env))
        env['result'] = env[symbol + '::result'] = result
        if check:
            self.boundary(self.results[symbol], 1, 1, result, depth)
            assert all(self.evaluate(condition, env, True, depth) is True for condition in assertions), ('native calculation assertion failed', symbol)
        return result

    def boundary(self, carrier, low, high, value, depth=0):
        if isinstance(carrier, CallableSignature):
            values = sequence(value)
            assert len(values) >= low and (high is None or len(values) <= high), 'callback cardinality mismatch'
            for callback in values:
                assert isinstance(callback, (CalculationValue, BoundCalculation)), 'callable binding is not a calculation'
                while isinstance(callback, BoundCalculation):
                    callback = callback.value
                inputs = self.calculations[callback.symbol][0]
                assert len(inputs) == 1, 'callback arity mismatch'
                for expected, actual in ((carrier.argument, inputs[0][1]), (carrier.result, self.results[callback.symbol])):
                    assert expected == 'Base::Anything' or actual == 'Base::Anything' or expected == actual, 'callback type mismatch'
            return
        if carrier in ('Boolean', 'Natural'):
            carrier = 'ScalarValues::' + carrier
        if isinstance(value, Extent):
            assert low == 0 and high is None and carrier == 'Base::Anything', 'extent used as a single value'
            return
        values = sequence(value)
        assert len(values) >= low and (high is None or len(values) <= high), ('native cardinality failed', carrier, low, high, value)
        for element in values:
            if carrier in ('Base::Anything', 'ScalarValues::Boolean', 'ScalarValues::Natural'):
                assert carrier == 'Base::Anything' or (type(element) is bool if carrier.endswith('Boolean') else type(element) is int and element >= 0), ('native primitive type failed', carrier, element)
            elif self.carriers[carrier][0] == 'enum':
                assert element in [carrier + '::' + c for c in self.carriers[carrier][1]], ('native enumeration failed', carrier, element)
            else:
                assert isinstance(element, Record) and element.type == carrier, ('native record type failed', carrier, element)
                _, fields, assertions = self.carriers[carrier]
                for field, typ, lower, upper in fields:
                    self.boundary(typ, lower, upper, element.get(field), depth)
                env = dict(element.fields)
                env['self'] = env[carrier + '::self'] = element
                assert all(self.evaluate(c, env, True, depth) is True for c in assertions), ('native carrier assertion failed', carrier, element)

    def evaluate(self, ast, env, check=True, depth=0):
        op, *args = ast
        ev = lambda node: self.evaluate(node, env, check, depth)
        if op == 'literal': return args[0]
        if op == 'reference': return env.get(args[0], args[0])
        if op == 'project':
            value = ev(args[0])
            if isinstance(value, tuple):
                assert len(value) == 1, ('projection multiplicity', value)
                value = value[0]
            assert isinstance(value, Record), ('projection from non-record', value)
            member = value.get(args[1])
            fields = self.carriers.get(value.type, (None, [], []))[1]
            signature = next((typ for field, typ, _, _ in fields if field == args[1]), None)
            if isinstance(signature, CallableSignature) and member != ():
                context = dict(value.fields)
                context.update({value.type + '::' + f: v for f, v in value.fields})
                context['self'] = context[value.type + '::self'] = value
                return BoundCalculation(member, signature, value.type + '::' + args[1], context)
            return member
        if op == 'new': return Record(args[0], tuple((field, ev(value)) for field, value in args[1]))
        if op == 'if': return ev(args[1] if ev(args[0]) else args[2])
        if op == 'not': return not ev(args[0])
        if op == 'sequence': return tuple(value for node in args[0] for value in sequence(ev(node)))
        if op in ('forall', 'exists'):
            values = ev(args[0])
            combine = all if op == 'forall' else any
            return combine(self.evaluate(args[2], {**env, args[1]: value}, check, depth) for value in sequence(values))
        if op == 'call':
            symbol, nodes = args
            values = [ev(node) for node in nodes]
            if symbol in env:
                assert len(values) == 1, 'callback invocation arity mismatch'
                return self.invoke_callback(env[symbol], values[0], check, depth + 1)
            if symbol.startswith('SequenceFunctions::'):
                method = symbol.split('::')[-1]
                if method == 'includes': return self.includes(*values)
                if method == 'includesOnly':
                    if any(isinstance(value, Extent) for value in values): return same_extent(*values)
                    return self.includes(*values) and self.includes(*reversed(values))
                if method == 'equals':
                    left, right = map(sequence, values)
                    return len(left) == len(right) and all(self.equal(x, y) for x, y in zip(left, right))
                seq = sequence(values[0])
                if method == 'head': return seq[0] if seq else ()
                if method == 'tail': return seq[1:]
                if method == 'size': return len(seq)
                if method == 'isEmpty': return not seq
                raise AssertionError(('unsupported native library operation', symbol))
            return self.invoke(symbol, values, check, depth + 1)
        if op == 'apply':
            assert len(args[1]) == 1, 'callback invocation arity mismatch'
            return self.invoke_callback(ev(args[0]), ev(args[1][0]), check, depth + 1)
        if op in ('as', 'hastype', 'istype'):
            value, typ = ev(args[0]), args[1][1]
            matches = typ == 'Base::Anything' or (isinstance(value, Record) and value.type == typ)
            return value if matches and op == 'as' else (() if op == 'as' else matches)
        left = ev(args[0])
        if op == 'and': return bool(left and ev(args[1]))
        if op == 'or': return bool(left or ev(args[1]))
        right = ev(args[1])
        if op == '==': return self.equal(left, right)
        if op == '!=': return not self.equal(left, right)
        if op == '<': return left < right
        if op == '>': return left > right
        if op == '<=': return left <= right
        if op == '>=': return left >= right
        if op == '+': return left + right
        if op == '-': return left - right
        if op == '*': return left * right
        raise AssertionError(('unsupported native expression', ast))

    def invoke_callback(self, binding, argument, check=True, depth=0):
        if isinstance(binding, CalculationValue):
            return self.invoke(binding.symbol, [argument], check, depth)
        assert isinstance(binding, BoundCalculation), 'invocation target is not callable'
        signature = binding.signature
        if check:
            self.boundary(signature.argument, 1, 1, argument, depth)
        result = self.invoke_callback(binding.value, argument, check, depth)
        if check:
            self.boundary(signature.result, 1, 1, result, depth)
            env = {**binding.environment, binding.scope + '::argument': argument,
                   binding.scope + '::result': result}
            assert all(self.evaluate(c, env, True, depth) is True for c in signature.assertions), 'callback contract failed'
        return result
