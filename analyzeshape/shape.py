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
    structures: typing.Set[structure.Structure]

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
        st_str = ','.join(str(st) for st in self.structures)
        return f'[{st_str}]'

    @classmethod
    def initial(cls, symbols):
        return cls(
            structures=set([Structure().initial(symbols)])
        )
        
    def reset(self):
        for st in structures:
            st.reset()

    def formula(self):
        formulas = [st.formula() for st in self.structures]
        return shortcuts.And(*formulas)

    def post_transform(self):
        pass # TODO


@ShapeState.transforms(lang_shape.VarVarAssignment)
def var_var_assignment(state, statement):

    for st in state.structures:
        lval = statement.lval
        rval = statement.rval
        cstate = state.deepcopy()
        var = cstate.var
        reach = cstate.reach

        for v in state.indiv:
            state.var[lval][v] = var[rval][v]
            state.reach[lval][v] = reach[rval][v]


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
        not_null = cstate._var_not_null

        if not_null(lval) == FALSE:
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
        is_reachable = cstate._phi_reach
        is_shared = cstate._phi_shared
        not_null = cstate._var_not_null

        if not_null(lval) == FALSE:
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
        is_reachable = cstate._phi_reach
        is_shared = cstate._phi_shared
        not_null = cstate._var_not_null

        if not_null(lval) == FALSE:
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

        lval = statement.lval
        rval = statement.rval
        passed = [st for st in state.structures if (st._var_eq(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()
        
    elif isinstance(expr, lang_shape.NotEqualsVarVar):

        lval = statement.lval
        rval = statement.rval
        passed = [st for st in state.structures if (st._var_eq(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.EqualsVarNext):

        lval = statement.lval
        rval = statement.rval
        passed = [st for st in state.structures if (st._var_next_eq(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.NotEqualsVarNext):
        
        lval = statement.lval
        rval = statement.rval
        passed = [st for st in state.structures if (st._var_next_eq(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.EqualsVarNull):
        
        lval = statement.lval
        passed = [st for st in state.structures if (st._var_not_null(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.NotEqualsVarNull):
        
        lval = statement.lval
        passed = [st for st in state.structures if (st._var_not_null(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    else:
        LOG.warning(f'Missing handling for {expr}')