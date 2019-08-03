import copy
import dataclasses
import logging
import typing
import copy

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

TRUE = structure.ThreeValuedBool.TRUE
FALSE = structure.ThreeValuedBool.FALSE
MAYBE = structure.ThreeValuedBool.MAYBE


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
    structures: typing.List[structure.Structure]

    def focus(self, var):
        workset = self.structures
        answerset = []
        while workset:
            st = workset.pop(0)
            u = next((u for u in st.indiv if st.var[var][u] == MAYBE), None)
            if not u:
                if st.coerce():
                    answerset.append(st)
            else:
                st0 = copy.deepcopy(st)
                st0.var[u] = TRUE
                workset.append(st0)
                st1 = copy.deepcopy(st)
                st1.var[u] = FALSE
                workset.append(st1)
                if st.sm[u] == MAYBE:
                    st2 = copy.deepcopy(st)
                    v = st2.copy_indiv(u)
                    st2.var[u] = TRUE
                    st2.var[v] = FALSE
                    workset.append(st2)
        self.structures = answerset
        LOG.debug('num of structures %d\n', len(self.structures))

    def focus_var_deref(self, var):
        workset = self.structures
        answerset = []
        while workset:
            st = workset.pop(0)
            res = next(((v,u) for u in st.indiv for v in st.indiv if\
                st.var[var][v] == TRUE and st.n[(v,u)] == MAYBE), None)
            if not res:
                if st.coerce():
                    answerset.append(st)
            else:
                (u,v) = res
                st0 = copy.deepcopy(st)
                st0.n[(v,u)] = TRUE
                workset.append(st0)
                st1 = copy.deepcopy(st)
                st0.n[(v,u)] = FALSE
                workset.append(st1)
                if st.sm[u] == MAYBE:
                    st2 = copy.deepcopy(st)
                    w = st2.copy_indiv(u)
                    st0.n[(v,u)] = TRUE
                    st0.n[(v,w)] = FALSE
                    workset.append(st2)
        self.structures = answerset
        LOG.debug('num of structures %d\n', len(self.structures))

    def join(self, other):

        # Discard self state when dealing with 3-valued logic structures
        # This is the embed operation from paper
        for st in other.structures:
            indiv_copy = copy.deepcopy(st.indiv)
            for u in indiv_copy:
                for v in indiv_copy:
                    if u in st.indiv and v in st.indiv and u < v and st.summarizable(u, v):
                        LOG.debug('something is summarizable!!! %s %s',u,v)
                        st.summarize(u, v)
        return other

    def __str__(self):
        st_str = ','.join(str(st) for st in self.structures)
        return f'[{st_str}]'

    @classmethod
    def initial(cls, symbols):
        return cls(
            structures=[structure.Structure.initial(symbols)]
        )
        
    def reset(self):
        self.structures = []

    def formula(self):
        formulas = [st.formula() for st in self.structures]
        return shortcuts.Or(*formulas)

    def post_transform(self):
        new_structures = []
        for st in self.structures:
            if st.coerce():
                new_structures.append(st)
        self.structures = new_structures


@ShapeState.transforms(lang_shape.VarVarAssignment)
def var_var_assignment(state, statement):

    lval = statement.lval
    rval = statement.rval
    state.focus(rval)

    for st in state.structures:

        cstate = copy.deepcopy(st)
        var = cstate.var
        reach = cstate.reach

        for v in st.indiv:
            st.var[lval][v] = var[rval][v]
            st.reach[lval][v] = reach[rval][v]


@ShapeState.transforms(lang_shape.VarNewAssignment)
def var_new_assignment(state, statement):

    lval = statement.lval

    for st in state.structures:
        v = max(st.indiv) + 1 if st.indiv else 0
        for u in st.indiv:
            st.var[lval][u] = FALSE
            st.n[(u,v)] = FALSE
            st.n[(v,u)] = FALSE

        for key in st.var:
            LOG.debug('key %s', key)
            st.var[key][v] = FALSE
            st.reach[key][v] = FALSE

        st.var[lval][v] = TRUE
        st.reach[lval][v] = TRUE
        st.n[(v,v)] = FALSE


        LOG.debug('st.var %s', st.var)

        st.cycle[v] = FALSE
        st.shared[v] = FALSE
        st.sm[v] = FALSE

        st.indiv.add(v)


@ShapeState.transforms(lang_shape.VarNextAssignment)
def var_next_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    state.focus_var_deref(rval)

    for st in state.structures:
        cstate = copy.deepcopy(st)
        var = cstate.var
        reach = cstate.reach
        n = cstate.n
        cycle = cstate.cycle
        shared = cstate.shared
        exists = cstate._exists
        not_null = cstate._var_not_null

        if not_null(rval) == FALSE:
            raise RuntimeError(f'Possible null pointer reference detected in {statement}')

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
    state.focus(lval)
    state.focus(rval)

    for st in state.structures:

        cstate = copy.deepcopy(st)
        var = cstate.var
        reach = cstate.reach
        n = cstate.n
        cycle = cstate.cycle
        shared = cstate.shared
        exists = cstate._exists
        is_reachable = cstate._v_reach
        is_shared = cstate._v_shared
        not_null = cstate._var_not_null

        if not_null(lval) == FALSE:
            raise RuntimeError(f'Possible null pointer reference detected in {statement}')

        for v in st.indiv:

            for key in st.var:
                st.reach[key][v] = \
                    reach[key][v]._or(
                        exists(lambda u : reach[key][u]._and(var[lval][u]))._and(reach[rval][v])
                    )

            st.cycle[v] = \
                cycle[v]._or(
                    exists(lambda u : var[lval][u]._and(reach[rval][u]))._and(reach[rval][v])
                )

            st.shared[v] = \
                (
                    (
                        var[rval][v]._and(exists(lambda u : n[(u, v)]))
                    )._and(
                        shared[v]._or(is_shared(v))
                    )
                )._or(
                    (
                        (var[rval][v]._and(exists(lambda u : n[(u, v)])))._not()
                    )._and(
                        shared[v]
                    )
                )

            for w in st.indiv:
                st.n[(v,w)] = \
                    (
                        (
                            var[lval][v]._not()
                        )._and(
                            n[(v,w)]
                        )
                    )._or(
                        var[lval][v]._and(var[rval][w])
                    )


@ShapeState.transforms(lang_shape.NextNullAssignment)
def next_null_assignment(state, statement):
    
    lval = statement.lval
    state.focus(lval)

    for st in state.structures:
        cstate = copy.deepcopy(st)
        var = cstate.var
        reach = cstate.reach
        n = cstate.n
        cycle = cstate.cycle
        shared = cstate.shared
        exists = cstate._exists
        is_reachable = cstate._v_reach
        is_shared = cstate._v_shared
        not_null = cstate._var_not_null

        if not_null(lval) == FALSE:
            raise RuntimeError(f'Possible null pointer reference detected in {statement}')

        for v in st.indiv:

            for key in st.var:

                st.reach[key][v] = \
                    (
                        (
                            cycle[v]._and(reach[lval][v])
                        )._and(
                            is_reachable(key, v)
                        )
                    )._or(
                        (
                            (cycle[v]._and(reach[lval][v]))._not()
                        )._and(
                            (
                                reach[key][v]
                            )._and(
                                (
                                    exists(lambda u : reach[key][u]._and(var[lval][u]))\
                                    ._and(reach[lval][v]._and(var[lval][v]._not()))
                                )._not()
                            )
                        )
                    )

            st.cycle[v] = \
                cycle[v]._and(
                    (
                        reach[lval][v]._and(exists(lambda u : var[lval][u]._and(cycle[u])))
                    )._not()
                )

            st.shared[v] = \
                (
                    (
                        exists(lambda u : var[lval][u]._and(n[(u, v)]))
                    )._and(
                        shared[v]._and(is_shared(v))
                    )
                )._or(
                    (
                        (exists(lambda u : var[lval][u]._and(n[(u, v)])))._not()
                    )._and(
                        shared[v]
                    )
                )

            for w in st.indiv:
                st.n[(v,w)] = \
                    (
                        (
                            var[lval][v]._not()
                        )._and(
                            n[(v,w)]
                        )
                    )._or(FALSE)

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

        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus(rval)

        passed = [st for st in state.structures if (st._var_eq(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()
        
    elif isinstance(expr, lang_shape.NotEqualsVarVar):

        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus(rval)

        passed = [st for st in state.structures if (st._var_eq(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.EqualsVarNext):

        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus_var_deref(rval)

        passed = [st for st in state.structures if (st._var_next_eq(lval, rval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.NotEqualsVarNext):
        
        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus_var_deref(rval)

        passed = [st for st in state.structures if (st._var_next_eq(lval, rval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.EqualsVarNull):
        
        lval = expr.lval
        state.focus(lval)

        passed = [st for st in state.structures if (st._var_not_null(lval) == FALSE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    elif isinstance(expr, lang_shape.NotEqualsVarNull):
        
        lval = expr.lval
        state.focus(lval)

        passed = [st for st in state.structures if (st._var_not_null(lval) == TRUE)]
        if passed:
            state.structures = passed
        else:
            state.reset()

    else:
        LOG.warning(f'Missing handling for {expr}')