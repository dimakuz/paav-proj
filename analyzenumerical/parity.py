import copy
import dataclasses
import logging
import typing

from pysmt import shortcuts

from analyzenumerical import lang as lang_num
from analyzeframework import abstract
from analyzeframework import lang


LOG = logging.getLogger(__name__)

ODD_atom = 1
EVEN_atom = 0

ODD = frozenset((ODD_atom,))
EVEN = frozenset((EVEN_atom,))
TOP = ODD.union(EVEN)
BOTTOM = frozenset()


def _get_val_parity(val):
    if val % 2 == 1:
        return ODD
    else:
        return EVEN


def _parity_name(val):
    return {
        ODD: 'O',
        EVEN: 'E',
        TOP: '⊤',
        BOTTOM: '⊥',
    }[val]


def transforms(stmt_type):
    def decorator(func):
        ParityState.TRANSFORMERS[stmt_type] = func
        return func
    return decorator


@dataclasses.dataclass
class ParityState(abstract.AbstractState):
    modulo: typing.Mapping[lang.Symbol, typing.Set[object]]
    samepar: typing.Mapping[lang.Symbol, typing.Set[lang.Symbol]]
    antipar: typing.Mapping[lang.Symbol, typing.Set[lang.Symbol]]

    def join(self, other, is_loop):
        modulo = {}
        for symbol in self.modulo:
            modulo[symbol] = self.modulo[symbol].union(other.modulo[symbol])

        samepar = {}
        for symbol in self.samepar:
            samepar[symbol] = self.samepar[symbol].union(other.samepar[symbol])

        antipar = {}
        for symbol in self.antipar:
            antipar[symbol] = self.antipar[symbol].union(other.antipar[symbol])

        return ParityState(modulo, samepar, antipar)

    def __str__(self):
        lines = []
        for symbol in self.modulo:
            samepar = ','.join(s.name for s in self.samepar[symbol])
            antipar = ','.join(s.name for s in self.antipar[symbol])
            lines.append(
                f'{symbol.name}: {_parity_name(self.modulo[symbol])}, '
                f'[{samepar}], [{antipar}]'
            )
        return '\n'.join(lines)

    @classmethod
    def initial(cls, symbols):
        return cls(
            modulo={symbol: BOTTOM for symbol in symbols},
            samepar={symbol: set() for symbol in symbols},
            antipar={symbol: set() for symbol in symbols}
        )

    def initialize_head(self, vars):
        pass

    def reset(self):
        for key in self.modulo:
            self.modulo[key] = BOTTOM
            self.samepar[key].clear()
            self.antipar[key].clear()

    def formula(self):
        clauses = []

        # ODD <-> ! EVEN
        for symbol in self.modulo:
            clauses.append(
                shortcuts.Iff(
                    lang_num.Odd(symbol).formula(),
                    shortcuts.Not(lang_num.Even(symbol).formula()),
                ),
            )

        # Encode discovered modulo state:
        for symbol, value in self.modulo.items():
            if value == EVEN:
                formula = lang_num.Even(symbol).formula()
            elif value == ODD:
                formula = lang_num.Odd(symbol).formula()
            else:
                continue
            clauses.append(formula)

        # Encode similar parity:
        for symbol, value in self.samepar.items():
            if not value:
                continue

            clauses.append(
                shortcuts.Implies(
                    shortcuts.And(
                        *(lang_num.Even(o).formula() for o in value),
                    ),
                    lang_num.Even(symbol).formula(),
                ),
            )
            clauses.append(
                shortcuts.Implies(
                    shortcuts.And(
                        *(lang_num.Odd(o).formula() for o in value),
                    ),
                    lang_num.Odd(symbol).formula(),
                ),
            )

        # Encode anti parity:
        for symbol, value in self.antipar.items():
            if not value:
                continue

            clauses.append(
                shortcuts.Implies(
                    shortcuts.And(
                        *(lang_num.Even(o).formula() for o in value),
                    ),
                    lang_num.Odd(symbol).formula(),
                ),
            )
            clauses.append(
                shortcuts.Implies(
                    shortcuts.And(
                        *(lang_num.Odd(o).formula() for o in value),
                    ),
                    lang_num.Even(symbol).formula(),
                ),
            )

        return shortcuts.And(*clauses)


@ParityState.transforms(lang_num.VarAssignment)
def var_assignment(state, statement):
    state.modulo[statement.lval] = state.modulo[statement.rval]

    for key in state.samepar:
        state.samepar[key].discard(statement.lval)
        state.antipar[key].discard(statement.lval)

    state.samepar[statement.lval] = {statement.rval}
    state.antipar[statement.lval].clear()


@ParityState.transforms(lang_num.ValAssignment)
def val_assignment(state, statement):
    state.modulo[statement.lval] = _get_val_parity(statement.rval)

    for key in state.samepar:
        state.samepar[key].discard(statement.lval)
        state.antipar[key].discard(statement.lval)

    state.samepar[statement.lval].clear()
    state.antipar[statement.lval].clear()


@ParityState.transforms(lang_num.QMarkAssignment)
def qmark_assignment(state, statement):
    state.modulo[statement.lval] = TOP

    for key in state.samepar:
        state.samepar[key].discard(statement.lval)
        state.antipar[key].discard(statement.lval)

    state.samepar[statement.lval].clear()
    state.antipar[statement.lval].clear()


@ParityState.transforms(lang_num.VarIncAssignment)
@ParityState.transforms(lang_num.VarDecAssignment)
def incdec_assignment(state, statement):
    rval_modulo = state.modulo[statement.rval]
    if rval_modulo == BOTTOM:
        raise RuntimeError('Referencing BOT symbol')
    elif rval_modulo == TOP:
        p = TOP
    else:
        p = TOP.difference(rval_modulo)
    state.modulo[statement.lval] = p

    for key in state.samepar:
        state.samepar[key].discard(statement.lval)
        state.antipar[key].discard(statement.lval)

    if statement.rval != statement.lval:
        state.samepar[statement.lval].clear()
        state.antipar[statement.lval] = {statement.rval}
    else:
        tmp = state.samepar[statement.lval]
        state.samepar[statement.lval] = state.antipar[statement.lval]
        state.antipar[statement.lval] = tmp


@ParityState.transforms(lang.Skip)
@ParityState.transforms(lang.Assert)
def noop(state, statement):
    pass

@ParityState.transforms(lang.Assume)
def assume(state, statement):
    expr = statement.expr
    if isinstance(expr, lang.Falsehood):
        state.reset()
    elif isinstance(expr, lang.Truth):
        pass
    elif isinstance(expr, lang_num.EqualsVal):
        if state.modulo[expr.lval] == ODD and (expr.rval % 2 == 0):
            state.reset()
        elif state.modulo[expr.lval] == EVEN and (expr.rval % 2 == 1):
            state.reset()
        state.modulo[expr.lval] = _get_val_parity(expr.rval)
    elif isinstance(expr, lang_num.EqualsVar):
        res = state.modulo[expr.lval].intersection(state.modulo[expr.rval])
        state.modulo[expr.lval] = res
        state.modulo[expr.rval] = res

        state.samepar[expr.lval].add(expr.rval)
        state.samepar[expr.rval].add(expr.lval)
    elif isinstance(expr, (lang_num.NotEqualsVar, lang_num.NotEqualsVal)):
        # No new info unless we implement equality tracking
        pass
    else:
        LOG.warning(f'Missing handling for {expr}')