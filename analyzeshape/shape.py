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

def focus(structure, var):
    workset = [structure]
    answerset = []
    while workset:
        st = workset.pop(0)
        maybe_indivs = [u for u in st.indiv if st.var[u] == MAYBE]
        if not maybe_indivs and coerce(st):
            answerset.append(st)
        else:
            for u in maybe_indivs:
                st0 = st.deepcopy()
                st0.var[u] = TRUE
                workset.append(st0)
                st1 = st.deepcopy()
                st1.var[u] = FALSE
                workset.append(st1)
                if (st.sm[u] == MAYBE):
                    st2 = st.deepcopy()
                    v = st2.copy(u)
                    st2.var[u] = TRUE
                    st2.var[v] = FALSE
                    workset.append(s2)
    return answerset

def focus_var_deref(structure, var):
    workset = [structure]
    answerset = []
    while workset:
        st = workset.pop(0)
        maybe_indivs = [(u,u1) for u,u1 in st.indiv if st.var[u1] == TRUE and st.n[(u1,u)] == MAYBE]
        if not maybe_indivs and coerce(st):
            answerset.append(st)
        else:
            for (u,u1) in maybe_indivs:
                st0 = st.deepcopy()
                st0.n[(u1,u)] = TRUE
                workset.append(st0)
                st1 = st.deepcopy()
                st0.n[(u1,u)] = FALSE
                workset.append(st1)
                if (st.sm[u] == MAYBE):
                    st2 = st.deepcopy()
                    v = st2.copy(u)
                    st0.n[(u1,u)] = TRUE
                    st0.n[(u1,v)] = FALSE
                    workset.append(s2)
    return 

def coerce(structure):
    #TODO
    pass

@dataclasses.dataclass
class ShapeState(abstract.AbstractState):
    structures: typing.Set[structure.Structure]

    def join(self, other):

        # Discard self state when dealing with 3-valued logic structures
        # This is the embed operation from paper
        for st in other.structures:
            indiv_copy = st.indiv.copy()
            for u,v in indiv_copy:
                if u in st.indiv and v in st.indiv and u < v and st._summarizable(u, v):
                    st._summarize(u, v)
        return other

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
        return shortcuts.Or(*formulas)

    def post_transform(self):
        self.structures = [st for st in self.structures if coerce(st)]


@ShapeState.transforms(lang_shape.VarVarAssignment)
def var_var_assignment(state, statement):

    lval = statement.lval
    rval = statement.rval
    state.structures = focus(state.structures, rval)

    for st in state.structures:

        cstate = state.deepcopy()
        var = cstate.var
        reach = cstate.reach

        for v in state.indiv:
            state.var[lval][v] = var[rval][v]
            state.reach[lval][v] = reach[rval][v]


@ShapeState.transforms(lang_shape.VarNewAssignment)
def var_new_assignment(state, statement):

    lval = statement.lval

    for st in state.structures:
        v = max(st.indiv) + 1
        for u in st.indiv:
            st.var[lval][u] = FALSE
            st.n[(u,v)] = FALSE
            st.n[(v,u)] = FALSE

        for key in st.var:
            st.var[key][v] = FALSE
            st.reach[key][v] = FALSE

        st.var[lval][v] = TRUE
        st.reach[lval][v] = TRUE
        st.n[(v,v)] = FALSE

        st.cycle[v] = FALSE
        st.shared[v] = FALSE
        st.sm[v] = FALSE

        st.indiv.add(v)


@ShapeState.transforms(lang_shape.VarNextAssignment)
def var_next_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    state.structures = focus_var_deref(state.structures, rval)

    for st in state.structures:
        cstate = st.deepcopy()
        var = cstate.var
        reach = cstate.reach
        n = cstate.n
        cycle = cstate.cycle
        exists = cstate._exists
        not_null = cstate._var_not_null

        if not_null(lval) == FALSE:
            raise RuntimeError('Possible null pointer reference detected')

        for v in st.indiv:
            st.var[lval][v] = exists(lambda u : var[rval][u]._and(n[(u, v)]))
            st.reach[lval][v] = reach[rval][v]._and(cycle[v]._or(var[rval][v]._not()))


@ShapeState.transforms(lang_shape.VarNullAssignment)
def var_null_assignment(state, statement):

    lval = statement.lval

    for st in state.structures:
        for u in st.indiv:
            st.var[lval][u] = FALSE
            st.reach[lval][u] = FALSE


@ShapeState.transforms(lang_shape.NextVarAssignment)
def next_var_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    state.structures = focus(state.structures, rval)
    state.structures = focus(state.structures, lval)

    for st in state.structures:

        cstate = st.deepcopy()
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

        for v in st.indiv:

            for key in st.var:
                st.reach[key][v] = reach[key][v]._or(
                    exists(lambda u : reach[key][u]._and(var[lval][u]))._and(reach[rval][v]))

            st.cycle[v] = cycle[v]._or(exists(lambda u : var[lval][u]._and(reach[rval][u]))._and(reach[rval][v]))

            if var[rval][v]._and(exists(lambda u : n[(u, v)])) != FALSE:
                st.shared[v] = shared[v]._or(is_shared(v))

            for w in st.indiv:
                st.n[(v,w)] = (var[lval][v]._not()._and(n[(v,w)]))._or(var[lval][v]._and(var[rval][w]))


@ShapeState.transforms(lang_shape.NextNullAssignment)
def next_null_assignment(state, statement):
    
    lval = statement.lval
    state.structures = focus(state.structures, lval)

    for st in state.structures:
        cstate = st.deepcopy()
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

        for v in st.indiv:

            for key in st.var:
                if cycle[v]._and(reach[lval][v]) != FALSE:
                    st.reach[key][v] = is_reachable(key, v)
                else:
                    st.reach[key][v] = reach[key][v]._and(exists(lambda u : reach[key][u]._and(var[lval][u]))\
                        ._and(reach[lval][v]._and(var[lval][v]._not()))._not())

            st.cycle[v] = cycle[v]._and(reach[lval][v]._and(exists(lambda u : var[lval][u]._and(cycle[u]))._not()))

            if exists(lambda u : var[lval][u]._and(n[(u, v)])) != FALSE:
                st.shared[v] = shared[v]._and(is_shared(v))

            for w in st.indiv:
                st.n[(v,w)] = (var[lval][v]._not()._and(n[(v,w)]))._or(FALSE)

        st.reach[lval] = var[lval]


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
        state.structures = focus(state.structures, lval)
        state.structures = focus(state.structures, rval)

        passed = [st for st in state.structures if (st._var_eq(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()
        
    elif isinstance(expr, lang_shape.NotEqualsVarVar):

        lval = statement.lval
        rval = statement.rval
        state.structures = focus(state.structures, lval)
        state.structures = focus(state.structures, rval)

        passed = [st for st in state.structures if (st._var_eq(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.EqualsVarNext):

        lval = statement.lval
        rval = statement.rval
        state.structures = focus(state.structures, lval)
        state.structures = focus_var_deref(state.structures, rval)

        passed = [st for st in state.structures if (st._var_next_eq(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.NotEqualsVarNext):
        
        lval = statement.lval
        rval = statement.rval
        state.structures = focus(state.structures, lval)
        state.structures = focus_var_deref(state.structures, rval)

        passed = [st for st in state.structures if (st._var_next_eq(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.EqualsVarNull):
        
        lval = statement.lval
        state.structures = focus(state.structures, lval)

        passed = [st for st in state.structures if (st._var_not_null(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.NotEqualsVarNull):
        
        lval = statement.lval
        state.structures = focus(state.structures, lval)

        passed = [st for st in state.structures if (st._var_not_null(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    else:
        LOG.warning(f'Missing handling for {expr}')