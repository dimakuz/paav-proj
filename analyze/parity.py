import dataclasses
import enum
import typing

from analyze import lang


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
            res[symbol] = self.symbols[symbol].join(other.symbols[symbol])
        return ParityState(res)

    def __str__(self):
        res = {str(key): value.name for key, value in self.symbols.items()}
        return str(res)

    def copy(self):
        return ParityState(self.symbols.copy())

    def transform(self, statement):
        res = self.copy()
        transformer = self.TRANSFORMERS[type(statement)]
        transformer(res, statement)
        return res


@transforms(lang.VarAssignment)
def var_assignment(state, statement):
    state.symbols[statement.lval] = state.symbols[statement.rval]


@transforms(lang.ValAssignment)
def val_assignment(state, statement):
    if statement.rval % 2:
        p = Parity.ODD
    else:
        p = Parity.EVEN
    state.symbols[statement.lval] = p


@transforms(lang.QMarkAssignment)
def qmark_assignment(state, statement):
    state.symbols[statement.lval] = Parity.TOP


@transforms(lang.VarIncAssignment)
@transforms(lang.VarDecAssignment)
def qmark_assignment(state, statement):
    p = state.symbol[statement.rval]
    if p is Parity.ODD:
        p = Parity.EVEN
    elif p is Parity.EVEN:
        p = parity.ODD
    state.symbols[statement.lval] = p


class ParityAbstractDomain:
    def __init__(self, symbols):
        self._symbols = symbols

    def initial_state(self):
        return ParityState(
            symbols={
                symbol: Parity.BOTTOM
                for symbol in self._symbols
            }
        )
