import copy
import dataclasses
import logging
import typing

from pysmt import shortcuts

from analyzeshape import lang as lang_shape
from analyzeframework import abstract
from analyzeframework import lang


LOG = logging.getLogger(__name__)

ODD_atom = 1
EVEN_atom = 0

ODD = frozenset((ODD_atom,))
EVEN = frozenset((EVEN_atom,))
TOP = ODD.union(EVEN)
BOTTOM = frozenset()


class ThreeValuedBool:
    val: float

    def __init__(self, val):
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def _not(self):
        return ThreeValuedBool(1 - val)

    def _and(self, other):
        return ThreeValuedBool(min(self.val, other.val))

    def _or(self, other):
        return ThreeValuedBool(max(self.val, other.val))


TRUE = ThreeValuedBool(1)
FALSE = ThreeValuedBool(0)
MAYBE = ThreeValuedBool(0.5)


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
        ShapeState.TRANSFORMERS[stmt_type] = func
        return func
    return decorator


@dataclasses.dataclass
class ShapeState(abstract.AbstractState):
    indiv: typing.Set[int]
    var: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    reach: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    cycle: typing.Mapping[int, ThreeValuedBool]
    shared: typing.Mapping[int, ThreeValuedBool]
    sm: typing.Mapping[int, ThreeValuedBool]
    n: typing.Mapping[typing.Tuple[int, int], ThreeValuedBool]

    def _indiv_eq(self, u, v):
        if (u != v):
            return FALSE
        else:
            return self.sm(u)

    def _is_shared(self, v):
        self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.n[(u1,v)]._and(self.n[(u2,v)])._and(self._indiv_eq(u1,u2)._not())
                )
            )

    def _is_reachable(self, var, v):
        # self.var[var][v]._or(self._exists(lambda v1 : self.var[var][v1]._and())
        return None

    def _exists(self, pred):
        return ThreeValuedBool(max(pred(v) for v in self.indiv))

    def _forall(self, pred):
        return ThreeValuedBool(min(pred(v) for v in self.indiv))

    def join(self, other):

        # TODO

        return ShapeState()

    def __str__(self):
        
        # TODO

        return ''

    @classmethod
    def initial(cls, symbols):
        return cls(
            indiv=set(),
            var={symbol: dict() for symbol in symbols},
            reach={symbol: dict() for symbol in symbols},
            cycle=dict(),
            shared=dict(),
            sm=dict(),
            n=dict()
        )
        
    def reset(self):
        indiv.clear()
        cycle.clear()
        shared.clear()
        sm.clear()
        n.clear()
        for key in self.var:
            self.var[key].clear()
            self.reach[key].clear()

    def formula(self):
        return ''


@ShapeState.transforms(lang_shape.VarVarAssignment)
def var_var_assignment(state, statement):

    lval = statement.lval
    rval = statement.rval

    state.var[lval] = state.var[rval]
    state.reach[lval] = state.reach[rval]


@ShapeState.transforms(lang_shape.VarNewAssignment)
def var_new_assignment(state, statement):

    lval = statement.lval

    v = max(indiv) + 1
    for u in state.indiv:
        state.var[lval][u] = FALSE
        state.n[(u,v)] = FALSE
        state.n[(v,u)] = FALSE

    for key in state.var:
        state.var[key][v] = FALSE
        state.reach[key][v] = FALSE

    state.var[lval][v] = TRUE
    state.reach[lval][v] = TRUE

    state.cycle[v] = FALSE
    state.shared[v] = FALSE
    state.sm[v] = FALSE

    indiv.add(v)


@ShapeState.transforms(lang_shape.VarNextAssignment)
def var_next_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    if state._exists(lambda u : state.var[rval][u]) != TRUE:
        raise RuntimeError('Possible null pointer reference detected')

    for v in state.indiv:
        state.var[lval][v] = state._exists(lambda u : state.var[rval][u]._and(state.n[(u, v)]))
        state.reach[lval][v] = state.reach[rval][v]._and(state.cycle[v]._or(state.var[rval][v]._not()))


@ShapeState.transforms(lang_shape.VarNullAssignment)
def var_null_assignment(state, statement):

    lval = statement.lval

    for u in state.indiv:
        state.var[lval][u] = FALSE
        state.reach[lval][u] = FALSE


@ShapeState.transforms(lang_shape.NextVarAssignment)
def next_var_assignment(state, statement):
    return ''


@ShapeState.transforms(lang_shape.NextNullAssignment)
def next_null_assignment(state, statement):
    
    lval = statement.lval
    if state._exists(lambda u : state.var[lval][u]) != TRUE:
        raise RuntimeError('Possible null pointer reference detected')

    cstate = state.copy()

    for v in state.indiv:

        for key in state.var:
            if cstate.cycle[v]._and(cstate.reach[lval][v]):
                state.reach[key][v] = cstate._is_reachable(key, v)
            else:
                

        if cstate._exists(lambda u : cstate.var[lval][u]._and(cstate.n[(u, v)])) != FALSE:
            state.shared[v] = cstate.shared[v]._and(self._is_shared(v))

    state.reach[lval] = cstate.var[lval]

@ShapeState.transforms(lang.Skip)
@ShapeState.transforms(lang.Assert)
def noop(state, statement):
    pass

@ShapeState.transforms(lang.Assume)
def assume(state, statement):
    expr = statement.expr
    if isinstance(expr, lang.Falsehood):
        state.reset()
    elif isinstance(expr, lang.Truth):
        pass
    elif isinstance(expr, lang_shape.EqualsVarVar):

        # TODO
        pass
    elif isinstance(expr, lang_shape.NotEqualsVarVar):
        # TODO
        pass
    elif isinstance(expr, lang_shape.EqualsVarNext):
        pass
    elif isinstance(expr, lang_shape.NotEqualsVarNext):
        pass
    elif isinstance(expr, lang_shape.EqualsVarNull):
        pass
    elif isinstance(expr, lang_shape.NotEqualsVarNull):
        pass
    else:
        LOG.warning(f'Missing handling for {expr}')