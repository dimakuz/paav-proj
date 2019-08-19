import dataclasses
import enum
import itertools
import logging
import typing

from pysmt import shortcuts

from analyzeframework import abstract
from analyzenumerical import lang as lang_num
from analyzeframework import lang

LOG = logging.getLogger(__name__)


# Constants
class _C(enum.Enum):
    TOP = enum.auto()
    BOTTOM = enum.auto()

_SPECIAL = (_C.TOP, _C.BOTTOM)


def _const_name(val):
    if val is _C.TOP:
        return '⊤'
    elif val is _C.BOTTOM:
        return '⊥'
    else:
        return str(val)

def _const_join(a, b):
    if a == b:
        return a
    elif a is _C.BOTTOM:
        return b
    elif a is _C.TOP:
        return a
    else:
        return _C.TOP


@dataclasses.dataclass
class DiffMatrix:
    val: typing.Mapping[typing.Tuple[lang.Symbol, lang.Symbol], int]

    @classmethod
    def initial(cls, vars):
        return cls(
            val={
                key: _C.BOTTOM
                for key in itertools.product(vars, vars)
                if key[0] < key[1]
            }
        )

    def __setitem__(self, key, value):
        if key[0] == key[1]:
            return
        if key[0] >= key[1]:
            key = (key[1], key[0])
            if value not in _SPECIAL:
                value = -value
        self.val[key] = value

    def __getitem__(self, key):
        if key[0] == key[1]:
            return 0
        if key[0] >= key[1]:
            key = (key[1], key[0])
        return self.val[key]

    def join(self, other):
        return DiffMatrix(
            val={
                key: _const_join(
                    self.val[key],
                    other.val[key],
                )
                for key in self.val
            },
        )

    def reset(self):
        for key in self.val:
            self.val[key] = _C.BOTTOM

    def formula(self):
        clauses = []
        for key, value in self.val.items():
            if value in _SPECIAL:
                continue
            clauses.append(
                shortcuts.Equals(
                    shortcuts.Int(value),
                    shortcuts.Minus(
                        shortcuts.Symbol(key[0].name, shortcuts.INT),
                        shortcuts.Symbol(key[1].name, shortcuts.INT),
                    ),
                ),
            )
        return shortcuts.And(clauses)

    def __str__(self):
        factoids = []
        for key, value in self.val.items():
            factoids.append(
                f'{key[0].name} - {key[1].name} = {_const_name(value)}',
            )
        return '\n'.join(factoids)


@dataclasses.dataclass
class SumState(abstract.AbstractState):
    const: typing.Mapping[lang.Symbol, int]
    diff: DiffMatrix

    def reset(self):
        for sym in self.const:
            self.const[sym] = _C.BOTTOM
        self.diff.reset()

    @classmethod
    def initial(cls, vars):
        return cls(
            const={sym: _C.BOTTOM for sym in vars},
            diff=DiffMatrix.initial(vars),
        )

    def initialize_head(self, vars):
        pass

    def join(self, other, is_loop):
        return SumState(
            const={
                sym: _const_join(
                    self.const[sym],
                    other.const[sym],
                ) for sym in self.const
            },
            diff=self.diff.join(other.diff)
        )

    def formula(self):
        clauses = []

        # Constant propogation
        for sym, val in self.const.items():
            if val is _C.TOP:
                continue
            clauses.append(
                shortcuts.Equals(
                    shortcuts.Symbol(sym.name, shortcuts.INT),
                    shortcuts.Int(val),
                ),
            )

        clauses =  shortcuts.And(clauses)
        return shortcuts.And(
            clauses,
            self.diff.formula(),
        )

    def __str__(self):
        lines = []
        for sym in self.const:
            line = f'{sym.name}: {_const_name(self.const[sym])}'
            lines.append(line)

        lines = [' '.join(lines)]
        lines.append(str(self.diff))
        return '\n'.join(lines)

    def post_transform(self):
        # Augment diff state with const propogation info
        for sym1, val1 in self.const.items():
            for sym2, val2 in self.const.items():
                if val1 not in _SPECIAL and val2 not in _SPECIAL:
                    self.diff[sym1, sym2] = val1 - val2


@SumState.transforms(lang_num.VarAssignment)
def var_assignment(state, statement):
    if statement.lval == statement.rval:
        return

    state.const[statement.lval] = state.const[statement.rval]
    for sym in state.const:
        if sym == statement.rval:
            state.diff[statement.lval, sym] = 0
        else:
            state.diff[statement.lval, sym] = _C.TOP


@SumState.transforms(lang_num.ValAssignment)
def val_assignment(state, statement):
    state.const[statement.lval] = statement.rval
    for sym in state.const:
        state.diff[statement.lval, sym] = _C.TOP


@SumState.transforms(lang_num.QMarkAssignment)
def qmark_assignment(state, statement):
    state.const[statement.lval] = _C.TOP
    for sym in state.const:
        state.diff[statement.lval, sym] = _C.TOP


@SumState.transforms(lang_num.VarIncAssignment)
def inc_assignment(state, statement):
    rval = state.const[statement.rval]
    if rval is _C.TOP:
        lval = rval
    else:
        lval = rval + 1
    state.const[statement.lval] = lval

    if statement.lval == statement.rval:
        for sym in state.const:
            if state.diff[statement.lval, sym] not in _SPECIAL:
                state.diff[statement.lval, sym] -= 1
    else:
        for sym in state.const:
            if sym == statement.rval:
                state.diff[statement.lval, sym] = 1
            else:
                state.diff[statement.lval, sym] = _C.TOP


@SumState.transforms(lang_num.VarDecAssignment)
def dec_assignment(state, statement):
    rval = state.const[statement.rval]
    if rval is _C.TOP:
        lval = rval
    else:
        lval = rval - 1
    state.const[statement.lval] = lval

    if statement.lval == statement.rval:
        for sym in state.const:
            if state.diff[statement.lval, sym] not in _SPECIAL:
                state.diff[statement.lval, sym] += 1
    else:
        for sym in state.const:
            if sym == statement.rval:
                state.diff[statement.lval, sym] = -1
            else:
                state.diff[statement.lval, sym] = _C.TOP


@SumState.transforms(lang.Skip)
@SumState.transforms(lang.Assert)
def noop(state, statement):
    pass


@SumState.transforms(lang.Assume)
def assume(state, statement):
    expr = statement.expr
    if isinstance(expr, lang.Falsehood):
        state.reset()
    elif isinstance(expr, lang.Truth):
        pass
    elif isinstance(expr, lang_num.EqualsVal):
        state.const[expr.lval] = expr.rval
    elif isinstance(expr, lang_num.EqualsVar):
        state.const[expr.lval] = state.const[expr.rval]
        state.diff[expr.lval, expr.rval] = 0
    elif isinstance(expr, lang_num.NotEqualsVar):
        if (
            state.const[expr.lval] == state.const[expr.rval]
            and
            state.const[expr.lval] is not _C.TOP
        ) or (
            state.diff[expr.lval, expr.rval] == 0
        ):
            state.reset()
    elif isinstance(expr, lang_num.NotEqualsVal):
        if state.const[expr.lval] == expr.rval:
            state.reset()
    else:
        LOG.warning(f'Missing handling for {expr}')
