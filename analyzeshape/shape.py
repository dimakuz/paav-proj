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

    def _summarizable(self, u, v):
        return all(self.var[key][u] == self.var[key][v] and \
                    self.reach[key][u] == self.reach[key][v] for key in self.var) and \
                    self.cycle[u] == self.cycle[v] and \
                    self.shared[u] == self.shared[v]

    def _summarize(self, u, v):
        if sm[u] == FALSE:
            self._merge_left_into_right(u, v)
        else:
            self._merge_left_into_right(v, u)

    def _merge_left_into_right(self, u, v):
        for w in self.indiv:
            if self.n[(w,v)] != self.n[(w,u)]:
                self.n[(w,v)] = MAYBE
            if self.n[(v,w)] != self.n[(u,w)]:
                self.n[(v,w)] = MAYBE
        self.indiv.remove(u)
        for key in self.var:
            self.var[key].pop(u)
            self.reach[key].pop(u)
        self.cycle.pop(u)
        self.shared.pop(u)
        self.sm.pop(u)
        for w in self.indiv:
            self.n.pop((u,w))
            self.n.pop((w,u))
        self.n.pop((u,u))
        self.sm[v] = MAYBE

    # Equality taking summary nodes into account
    def _indiv_eq(self, u, v):
        if (u != v):
            return FALSE
        else:
            return self.sm(u)._not()

    # Is the individual heap shared
    def _is_shared(self, v):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.n[(u1,v)]._and(self.n[(u2,v)])._and(self._indiv_eq(u1,u2)._not())
                )
            )

    # Is the individual reachable from variable
    def _is_reachable(self, var, v):
        return self.var[var][v]._or(self._exists(lambda v1 : self.var[var][v1]._and(self.n_plus[(v1,v)])))

    # Transitive closure of n
    def _n_plus(self):
        n_plus = self.n.copy()
        for u in indiv:
            for v,w in indiv:
                n_plus[(v,w)] = n_plus[(v,w)]._or(n_plus[(v,u)]._and(n_plus[(u,w)]))
        return n_plus

    def _exists(self, pred):
        return ThreeValuedBool(max(pred(v) for v in self.indiv))

    def _forall(self, pred):
        return ThreeValuedBool(min(pred(v) for v in self.indiv))

    def join(self, other):

        # Discard self state when dealing with 3-valued logic structures
        new_state = other.deepcopy()
        for u,v in self.indiv:
            if new_state._summarizable(u,v):
                new_state._summarize(u,v)


        return new_state

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
    state.n[(v,v)] = FALSE

    state.cycle[v] = FALSE
    state.shared[v] = FALSE
    state.sm[v] = FALSE

    indiv.add(v)


@ShapeState.transforms(lang_shape.VarNextAssignment)
def var_next_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    cstate = state.deepcopy()
    var = cstate.var
    reach = cstate.reach
    n = cstate.n
    cycle = cstate.cycle
    exists = cstate._exists

    if exists(lambda u : var[rval][u]) != TRUE:
        raise RuntimeError('Possible null pointer reference detected')

    for v in state.indiv:
        state.var[lval][v] = exists(lambda u : var[rval][u]._and(n[(u, v)]))
        state.reach[lval][v] = reach[rval][v]._and(cycle[v]._or(var[rval][v]._not()))


@ShapeState.transforms(lang_shape.VarNullAssignment)
def var_null_assignment(state, statement):

    lval = statement.lval

    for u in state.indiv:
        state.var[lval][u] = FALSE
        state.reach[lval][u] = FALSE


@ShapeState.transforms(lang_shape.NextVarAssignment)
def next_var_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    cstate = state.deepcopy()
    var = cstate.var
    reach = cstate.reach
    n = cstate.n
    cycle = cstate.cycle
    exists = cstate._exists
    is_reachable = cstate._is_reachable
    is_shared = cstate._is_shared

    if exists(lambda u : var[lval][u]) != TRUE:
        raise RuntimeError('Possible null pointer reference detected')

    for v in state.indiv:

        for key in state.var:
            state.reach[key][v] = reach[key][v]._or(
                exists(lambda u : reach[key][u]._and(var[lval][u]))._and(reach[rval][v]))

        state.cycle[v] = cycle[v]._or(exists(lambda u : var[lval][u]._and(reach[rval][u]))._and(reach[rval][v]))

        if var[rval][v]._and(exists(lambda u : n[(u, v)])) != FALSE:
            state.shared[v] = shared[v]._or(is_shared(v))

        for w in state.indiv:
            state.n[(v,w)] = (var[lval][v]._not()._and(n[(v,w)]))._or(var[lval][v]._and(var[rval][w]))


@ShapeState.transforms(lang_shape.NextNullAssignment)
def next_null_assignment(state, statement):
    
    lval = statement.lval
    cstate = state.deepcopy()
    var = cstate.var
    reach = cstate.reach
    n = cstate.n
    cycle = cstate.cycle
    exists = cstate._exists
    is_reachable = cstate._is_reachable
    is_shared = cstate._is_shared

    if exists(lambda u : var[lval][u]) != TRUE:
        raise RuntimeError('Possible null pointer reference detected')

    for v in state.indiv:

        for key in state.var:
            if cycle[v]._and(reach[lval][v]) != FALSE:
                state.reach[key][v] = is_reachable(key, v)
            else:
                state.reach[key][v] = reach[key][v]._and(exists(lambda u : reach[key][u]._and(var[lval][u]))\
                    ._and(reach[lval][v]._and(var[lval][v]._not()))._not())

        state.cycle[v] = cycle[v]._and(reach[lval][v]._and(exists(lambda u : var[lval][u]._and(cycle[u]))._not()))

        if exists(lambda u : var[lval][u]._and(n[(u, v)])) != FALSE:
            state.shared[v] = shared[v]._and(is_shared(v))

        for w in state.indiv:
            state.n[(v,w)] = (var[lval][v]._not()._and(n[(v,w)]))._or(FALSE)

    state.reach[lval] = var[lval]


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