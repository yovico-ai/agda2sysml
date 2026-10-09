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
                elif parser.take('in') or parser.take('attribute'):
                    if parser.take('calc'):
                        field = parser.qualified()
                        parser.expect('{')
                        parser.expect('in'); parser.expect("'argument'"); parser.expect(':')
                        domain = parser.qualified()
                        parser.expect('['); parser.expect('1'); parser.expect(']'); parser.expect(';')
                        parser.expect('return'); parser.expect("'result'"); parser.expect(':')
                        codomain = parser.qualified()
                        parser.expect('['); parser.expect('1'); parser.expect(']'); parser.expect(';')
                        contracts = []
                        while parser.take('assert'):
                            parser.expect('constraint'); parser.expect('{')
                            contracts.append(parser.expression()); parser.expect('}')
                        parser.expect('}')
                        inputs.append((field, CallableSignature(domain, codomain, tuple(contracts)), 1, 1))
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
                    while not parser.take(';'):
                        assert parser.pop() in ('ordered', 'nonunique'), 'unsupported multiplicity qualifier'
                    (fields if kind == 'attribute' else inputs).append((field, carrier, low, high))
                elif parser.take('return'):
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
        env['result'] = env[symbol + '::result'] = result
        if check:
            self.boundary(self.results[symbol], 1, 1, result, depth)
            assert all(self.evaluate(condition, env, True, depth) is True for condition in assertions), ('native calculation assertion failed', symbol)
        return result

    def boundary(self, carrier, low, high, value, depth=0):
        if isinstance(carrier, CallableSignature):
            assert isinstance(value, (CalculationValue, BoundCalculation)), 'callable binding is not a calculation'
            while isinstance(value, BoundCalculation):
                value = value.value
            inputs = self.calculations[value.symbol][0]
            assert len(inputs) == 1, 'callback arity mismatch'
            for expected, actual in ((carrier.argument, inputs[0][1]), (carrier.result, self.results[value.symbol])):
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
            return value.get(args[1])
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
                if method == 'includes': return includes(*values)
                if method == 'includesOnly': return same_extent(*values)
                if method == 'equals':
                    left, right = map(sequence, values)
                    return len(left) == len(right) and all(same(x, y) for x, y in zip(left, right))
                seq = sequence(values[0])
                if method == 'head': return seq[0] if seq else ()
                if method == 'tail': return seq[1:]
                if method == 'size': return len(seq)
                if method == 'isEmpty': return not seq
                raise AssertionError(('unsupported native library operation', symbol))
            return self.invoke(symbol, values, check, depth + 1)
        if op in ('as', 'hastype', 'istype'):
            value, typ = ev(args[0]), args[1][1]
            matches = typ == 'Base::Anything' or (isinstance(value, Record) and value.type == typ)
            return value if matches and op == 'as' else (() if op == 'as' else matches)
        left = ev(args[0])
        if op == 'and': return bool(left and ev(args[1]))
        if op == 'or': return bool(left or ev(args[1]))
        right = ev(args[1])
        if op == '==': return same(left, right)
        if op == '!=': return not same(left, right)
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
