import dataclasses
import enum
import itertools
import logging
import typing

import more_itertools
from pysmt import shortcuts

from analyzeframework import abstract
from analyzenumerical import lang as lang_num
from analyzeframework import lang

LOG = logging.getLogger(__name__)
MAX_COMBINATION_SIZE = 3


# Constants
class _C(enum.Enum):
    TOP = enum.auto()
    BOTTOM = enum.auto()

    def __add__(self, other):
        return _C.TOP

    def __sub__(self, other):
        return _C.TOP

    def __neg__(self):
        return _C.TOP

    def __eq__(self, other):
        return False

    def __str__(self):
        return _const_name(self)


TOP = _C.TOP
BOTTOM = _C.BOTTOM

_SPECIAL = (TOP, BOTTOM)


def _const_name(val):
    if val is TOP:
        return '⊤'
    elif val is BOTTOM:
        return '⊥'
    else:
        return str(val)


def _const_join(a, b):
    if a == b:
        return a
    elif a is BOTTOM:
        return b
    elif a is TOP:
        return a
    else:
        return TOP


@dataclasses.dataclass
class SumTracker(dict):
    sums: typing.Mapping[typing.Set[lang.Symbol], int]

    @classmethod
    def initial(cls, vars):
        sums = {}
        for i in range(1, MAX_COMBINATION_SIZE + 1):
            for key in itertools.combinations(vars, i):
                sums[frozenset(key)] = BOTTOM
        return cls(sums)

    def reset(self):
        for key in self:
            self[key] = BOTTOM

    def join(self, other):
        return SumTracker(
            sums={
                key: _const_join(self[key], other[key])
                for key in self.sums
            }
        )

    def formula(self):
        clauses = []
        for syms, val in self.sums.items():
            if val in _SPECIAL:
                continue
            clauses.append(
                shortcuts.Equals(
                    shortcuts.Int(val),
                    shortcuts.Plus(
                        *(
                            shortcuts.Symbol(s.name, shortcuts.INT)
                            for s in syms
                        ),
                    ),
                ),
            )
        return shortcuts.And(clauses)

    def __str__(self):
        return '\n'.join(
            '{vars}={val}'.format(
                vars='+'.join(s.name for s in key),
                val=val,
            ) for key, val in self.sums.items()
            if val not in _SPECIAL
        )

    def __setitem__(self, key, val):
        self.sums[frozenset(key)] = val

    def __getitem__(self, key):
        return self.sums[frozenset(key)]

    def items(self):
        return self.sums.items()

    def keys(self):
        return self.sums.keys()


@dataclasses.dataclass
class DiffMatrix:
    val: typing.Mapping[typing.Tuple[lang.Symbol, lang.Symbol], int]

    @classmethod
    def initial(cls, vars):
        return cls(
            val={
                key: BOTTOM
                for key in itertools.product(vars, vars)
                if key[0] < key[1]
            }
        )

    def __setitem__(self, key, value):
        if key[0] == key[1]:
            return
        if key[0] >= key[1]:
            key = (key[1], key[0])
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
            self.val[key] = BOTTOM

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
            if value in _SPECIAL:
                continue
            factoids.append(
                f'{key[0].name} - {key[1].name} = {_const_name(value)}',
            )
        return '\n'.join(factoids)


@dataclasses.dataclass
class SumState(abstract.AbstractState):
    vars: typing.List[lang.Symbol]
    diff: DiffMatrix
    sums: SumTracker

    def reset(self):
        self.diff.reset()
        self.sums.reset()

    @classmethod
    def initial(cls, vars):
        return cls(
            vars=vars,
            diff=DiffMatrix.initial(vars),
            sums=SumTracker.initial(vars),
        )

    def initialize_head(self, vars):
        pass

    def join(self, other, arbitrary_term=None):
        return SumState(
            vars=self.vars,
            diff=self.diff.join(other.diff),
            sums=self.sums.join(other.sums),
        )

    def formula(self):
        return shortcuts.And(
            self.diff.formula(),
            self.sums.formula(),
        )

    def __str__(self):
        return f'{self.sums}\n{self.diff}'

    def post_transform(self):
        self._deduce_deltas()
        self._deduce_vars()
        self._deduce_sums()
        self._deduce_deltas()

    def _deduce_deltas(self):
        for s1 in self.vars:
            for s2 in self.vars:
                if self.diff[s1, s2] not in _SPECIAL:
                    continue

                if (
                    self.sums[{s1}] not in _SPECIAL
                    and
                    self.sums[{s2}] not in _SPECIAL
                ):
                    self.diff[s1, s2] = (
                        self.sums[{s1}] - self.sums[{s2}]
                    )

                for s3 in self.vars:
                    if (
                        self.diff[s1,s3] not in _SPECIAL
                        and
                        self.diff[s3, s2] not in _SPECIAL
                    ):
                        self.diff[s1, s2] = (
                            self.diff[s1, s3] + self.diff[s3, s2]
                        )

    def _deduce_vars(self):
        for sym in self.vars:
            if self.sums[{sym}] not in _SPECIAL:
                continue

            for other in self.vars:
                if (
                    self.diff[sym, other] not in _SPECIAL
                    and
                    self.sums[{other}] not in _SPECIAL
                ):
                    self.sums[{sym}] = (
                        self.sums[{other}] + self.diff[sym, other]
                    )

    def _deduce_sums(self):
        for key, value in self.sums.items():
            if value not in _SPECIAL:
                continue
            for part in more_itertools.set_partitions(key):
                if all(
                    self.sums[p] not in _SPECIAL for p in part
                ):
                    self.sums[key] = sum(self.sums[p] for p in part)
                    break

def _delta(new, old):
    if new in _SPECIAL or old in _SPECIAL:
        return TOP
    else:
        return new - old


def _sym_assign_sym(state, lval, rval):
    old_val = state.sums[{lval}]
    new_val = state.sums[{rval}]
    delta = _delta(new_val, old_val)

    if delta not in _SPECIAL:
        # Adjust sums that include lval by known delta
        for key in state.sums:
            if lval in key:
                state.sums[key] += delta

        # Adjust deltas
        for sym in state.vars:
            state.diff[lval, sym] -= delta
    else:
        # Delta unknown, reset related sums
        for key in state.sums:
            if lval in key:
                state.sums[key] = TOP

        # Reset related deltas
        for sym in state.vars:
            state.diff[lval, sym] = TOP
        # Set delta 0 to rval
        state.diff[lval, rval] = 0


def _sym_assume_sym(state, lval, rval):
    old_val = state.sums[{lval}]
    new_val = state.sums[{rval}]
    delta = _delta(new_val, old_val)

    if delta not in _SPECIAL:
        # Adjust sums that include lval by known delta
        for key in state.sums:
            if lval in key:
                state.sums[key] += delta

        # Adjust deltas
        for sym in state.vars:
            state.diff[lval, sym] -= delta
    else:
        # Set delta 0 to rval
        state.diff[lval, rval] = 0


@SumState.transforms(lang_num.VarAssignment)
def var_assignment(state, statement):
    if statement.lval == statement.rval:
        return
    _sym_assign_sym(state, statement.lval, statement.rval)


def _sym_assign_val(state, lval, rval):
    old_val = state.sums[{lval}]
    new_val = rval
    delta = _delta(new_val, old_val)

    if delta not in _SPECIAL:
        # Adjust sums that include lval by known delta
        for key in state.sums:
            if lval in key:
                state.sums[key] += delta

        # Adjust deltas
        for sym in state.vars:
            state.diff[lval, sym] -= delta
    else:
        # Delta unknown, reset related sums
        for key in state.sums:
            if lval in key:
                state.sums[key] = TOP
        state.sums[{lval}] = new_val

        # Reset related deltas
        for sym in state.vars:
            state.diff[lval, sym] = TOP


def _sym_assume_val(state, lval, rval):
    old_val = state.sums[{lval}]
    new_val = rval
    delta = _delta(new_val, old_val)

    if delta not in _SPECIAL:
        # Adjust sums that include lval by known delta
        for key in state.sums:
            if lval in key:
                state.sums[key] += delta

        # Adjust deltas
        for sym in state.vars:
            state.diff[lval, sym] -= delta
    else:
        # Delta unknown, reset related sums
        for key in state.sums:
            if lval in key:
                state.sums[key] = TOP
        state.sums[{lval}] = new_val


@SumState.transforms(lang_num.ValAssignment)
def val_assignment(state, statement):
    _sym_assign_val(state, statement.lval, statement.rval)


@SumState.transforms(lang_num.QMarkAssignment)
def qmark_assignment(state, statement):
    for key in state.sums.keys():
        if statement.lval in key:
            state.sums[key] = TOP

    # Reset related deltas
    for sym in state.vars:
        state.diff[statement.lval, sym] = TOP


@SumState.transforms(lang_num.VarIncAssignment)
def inc_assignment(state, statement):
    if statement.lval == statement.rval:
        delta = 1
    else:
        old_val = state.sums[{statement.lval}]
        new_val = state.sums[{statement.rval}] + 1
        delta = _delta(new_val, old_val)

    if delta not in _SPECIAL:
        # Adjust sums that include lval by known delta
        for key in state.sums:
            if statement.lval in key:
                state.sums[key] += delta

        # Adjust known deltas
        for sym in state.vars:
            state.diff[statement.lval, sym] -= delta
    else:
        # Delta unknown, reset related sums
        for key in state.sums:
            if statement.lval in key:
                state.sums[key] = TOP
        state.sums[{statement.lval}] = new_val

        # Reset related deltas
        for sym in state.vars:
            state.diff[statement.lval, sym] = TOP

    # If lval != rval, set their delta to 1
    if statement.lval != statement.rval:
        state.diff[statement.lval, statement.rval] = 1


@SumState.transforms(lang_num.VarDecAssignment)
def dec_assignment(state, statement):
    if statement.lval == statement.rval:
        delta = -1
    else:
        old_val = state.sums[{statement.lval}]
        new_val = state.sums[{statement.rval}] - 1
        delta = new_val - old_val

    if delta not in _SPECIAL:
        # Adjust sums that include lval by known delta
        for key in state.sums:
            if statement.lval in key:
                state.sums[key] += delta

        # Adjust known deltas
        for sym in state.vars:
            state.diff[statement.lval, sym] -= delta
    else:
        # Delta unknown, reset related sums
        for key in state.sums:
            if statement.lval in key:
                state.sums[key] = TOP
        state.sums[{statement.lval}] = new_val

        # Reset related deltas
        for sym in state.vars:
            state.diff[statement.lval, sym] = TOP

    # If lval != rval, set their delta to 1
    if statement.lval != statement.rval:
        state.diff[statement.lval, statement.rval] = -1


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
        known_val = state.sums[{expr.lval}]
        if known_val not in _SPECIAL and known_val != expr.rval:
            state.reset()
        else:
            _sym_assume_val(state, expr.lval, expr.rval)
    elif isinstance(expr, lang_num.EqualsVar):
        known_delta = state.diff[expr.lval, expr.rval]
        if known_delta not in _SPECIAL and known_val != 0:
            state.reset()
        else:
            _sym_assume_sym(state, expr.lval, expr.rval)
    elif isinstance(expr, lang_num.NotEqualsVar):
        if (
            state.sums[{expr.lval}] == state.sums[{expr.rval}]
        ) or (
            state.diff[expr.lval, expr.rval] == 0
        ):
            state.reset()
    elif isinstance(expr, lang_num.NotEqualsVal):
        if state.sum[{expr.lval}] == expr.rval:
            state.reset()
    else:
        LOG.warning(f'Missing handling for {expr}')
