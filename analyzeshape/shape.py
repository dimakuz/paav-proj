import copy
import dataclasses
import logging
import typing

from pysmt import shortcuts

from analyzeshape import lang as lang_shape
from analyzeframework import abstract
from analyzeframework import lang
from analyzeshape import structure


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
        ShapeState.TRANSFORMERS[stmt_type] = func
        return func
    return decorator


@dataclasses.dataclass
class ShapeState(abstract.AbstractState):
    structures: typing.Set[Structure]

    def join(self, other):

        new_structures = []
        # Discard self state when dealing with 3-valued logic structures
        for st in other.structures:
            new_st = st.deepcopy()
            for u,v in st.indiv:
                if u in new_st.indiv and v in new_st.indiv:
                    if new_st._summarizable(u,v):
                        new_st._summarize(u,v)
            new_structures.add(new_st)

        return ShapeState(new_structures)

    def __str__(self):
        
        # TODO

        return ''

    @classmethod
    def initial(cls, symbols):
        return cls(
            structures=set([Structure().initial(symbols)])
        )
        
    def reset(self):
        for st in structures:
            st.reset()

    def formula(self):
        return return shortcuts.And(*clauses)


@ShapeState.transforms(lang_shape.VarVarAssignment)
def var_var_assignment(state, statement):

    for st in state.structures:
        lval = statement.lval
        rval = statement.rval

        state.var[lval] = state.var[rval]
        state.reach[lval] = state.reach[rval]


@ShapeState.transforms(lang_shape.VarNewAssignment)
def var_new_assignment(state, statement):

    for st in state.structures:
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
    
    for st in state.structures:
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

    for st in state.structures:
        lval = statement.lval

        for u in state.indiv:
            state.var[lval][u] = FALSE
            state.reach[lval][u] = FALSE


@ShapeState.transforms(lang_shape.NextVarAssignment)
def next_var_assignment(state, statement):
    
    for st in state.structures:
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
    
    for st in state.structures:
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