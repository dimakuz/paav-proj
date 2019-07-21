import dataclasses
import enum
import logging
import typing

from analyze import lang

LOG = logging.getLogger(__name__)


class Parity(enum.Enum):
    TOP = enum.auto()

    ODD = enum.auto()
    EVEN = enum.auto()

    BOTTOM = enum.auto()

    def join(self, other):
        return _PARITY_JOIN[
            max(self.value, other.value),
            min(self.value, other.value),
        ]

    def meet(self, other):
        return _PARITY_MEET[
            max(self.value, other.value),
            min(self.value, other.value),
        ]

_PARITY_JOIN = {
    (Parity.BOTTOM.value, Parity.BOTTOM.value): Parity.BOTTOM,
    (Parity.BOTTOM.value, Parity.EVEN.value): Parity.EVEN,
    (Parity.BOTTOM.value, Parity.ODD.value): Parity.ODD,
    (Parity.BOTTOM.value, Parity.TOP.value): Parity.TOP,
    (Parity.EVEN.value, Parity.EVEN.value): Parity.EVEN,
    (Parity.EVEN.value, Parity.ODD.value): Parity.TOP,
    (Parity.EVEN.value, Parity.TOP.value): Parity.TOP,
    (Parity.ODD.value, Parity.ODD.value): Parity.ODD,
    (Parity.ODD.value, Parity.TOP.value): Parity.TOP,
    (Parity.TOP.value, Parity.TOP.value): Parity.TOP,
}

_PARITY_MEET = {
    (Parity.BOTTOM.value, Parity.BOTTOM.value): Parity.BOTTOM,
    (Parity.BOTTOM.value, Parity.EVEN.value): Parity.BOTTOM,
    (Parity.BOTTOM.value, Parity.ODD.value): Parity.BOTTOM,
    (Parity.BOTTOM.value, Parity.TOP.value): Parity.BOTTOM,
    (Parity.EVEN.value, Parity.EVEN.value): Parity.EVEN,
    (Parity.EVEN.value, Parity.ODD.value): Parity.BOTTOM,
    (Parity.EVEN.value, Parity.TOP.value): Parity.EVEN,
    (Parity.ODD.value, Parity.ODD.value): Parity.ODD,
    (Parity.ODD.value, Parity.TOP.value): Parity.ODD,
    (Parity.TOP.value, Parity.TOP.value): Parity.TOP,
}


def transforms(stmt_type):
    def decorator(func):
        ParityState.TRANSFORMERS[stmt_type] = func
        return func
    return decorator


@dataclasses.dataclass
class ParityState:
    symbols: typing.Mapping[lang.Symbol, Parity]

    TRANSFORMERS = {}

    def join(self, other):
        res = {}
        for symbol in self.symbols:
            res[symbol] = self[symbol].join(other[symbol])
        return ParityState(res)

    def __str__(self):
        res = {str(key): value.name for key, value in self.symbols.items()}
        return str(res)

    def copy(self):
        return ParityState(self.symbols.copy())

    def transform(self, statement):
        res = self.copy()
        try:
            transformer = self.TRANSFORMERS[type(statement)]
        except KeyError:
            LOG.warning(f'No transformer for {statement}')
            # FIXME
            return res
        transformer(res, statement)
        return res

    @classmethod
    def initial(cls, symbols):
        return cls(
            symbols={
                symbol: Parity.BOTTOM
                for symbol in symbols
            }
        )

    def reset(self):
        for key in self.symbols:
            self[key] = Parity.BOTTOM

    def __getitem__(self, key):
        return self.symbols[key]

    def __setitem__(self, key, value):
        self.symbols[key] = value

    def diff(self, other):
        # Debugging only
        res = {}
        for key in self.symbols:
            if self[key] == other[key]:
                continue
            res[str(key)] = (str(other[key]), str(self[key]))
        return res

@transforms(lang.VarAssignment)
def var_assignment(state, statement):
    state.symbols[statement.lval] = state[statement.rval]


@transforms(lang.ValAssignment)
def val_assignment(state, statement):
    if statement.rval % 2:
        p = Parity.ODD
    else:
        p = Parity.EVEN
    state[statement.lval] = p


@transforms(lang.QMarkAssignment)
def qmark_assignment(state, statement):
    state[statement.lval] = Parity.TOP


@transforms(lang.VarIncAssignment)
@transforms(lang.VarDecAssignment)
def incdec_assignment(state, statement):
    p = state[statement.rval]
    if p is Parity.ODD:
        p = Parity.EVEN
    elif p is Parity.EVEN:
        p = Parity.ODD
    state[statement.lval] = p


@transforms(lang.Skip)
def skip(state, statement):
    pass

@transforms(lang.Assume)
def assume(state, statement):
    expr = statement.expr
    if isinstance(expr, lang.Falsehood):
        state.reset()
    elif isinstance(expr, lang.Truth):
        return
    elif isinstance(expr, lang.EqualsVal):
        if state[expr.lval] == Parity.ODD and (expr.rval % 2 == 0):
            state.reset()
        elif state[expr.lval] == Parity.EVEN and (expr.rval % 2 == 1):
            state.reset()
    elif isinstance(expr, lang.EqualsVar):
        res = state[expr.lval].meet(state[expr.rval])
        state[expr.lval] = res
        state[expr.rval] = res
    elif isinstance(expr, (lang.NotEqualsVar, lang.NotEqualsVal)):
        # No new info unless we implement equality tracking
        pass
    else:
        LOG.warning(f'Missing handling for {expr}')
