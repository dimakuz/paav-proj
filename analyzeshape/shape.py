import copy
import dataclasses
import logging
import typing
import copy
import collections

from pysmt import shortcuts

from analyzeshape import lang as lang_shape, three_valued_logic
from analyzeframework import abstract
from analyzeframework import lang
from analyzeshape import structure

from sympy import *


LOG = logging.getLogger(__name__)

TRUE = structure.three_valued_logic.ThreeValuedBool.TRUE
FALSE = structure.three_valued_logic.ThreeValuedBool.FALSE
MAYBE = structure.three_valued_logic.ThreeValuedBool.MAYBE



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
            if u is None:
                answerset.append(st)
            else:
                st0 = st.copy()
                st0.var[var][u] = TRUE
                workset.append(st0)
                st1 = st.copy()
                st1.var[var][u] = FALSE
                workset.append(st1)
                if st.sm[u] == MAYBE:
                    st2 = st.copy()
                    v = st2.copy_indiv(u)
                    st2.var[var][u] = TRUE
                    st2.var[var][v] = FALSE
                    workset.append(st2)
        self.structures = answerset
        # LOG.debug('num of structures focus %d\n', len(self.structures))

    def focus_var_deref(self, var):
        workset = self.structures
        answerset = []
        while workset:
            st = workset.pop(0)
            res = next(((v,u) for u in st.indiv for v in st.indiv if\
                st.var[var][v] == TRUE and st.n[(v,u)] == MAYBE), None)
            if res is None:
                answerset.append(st)
            else:
                (v,u) = res
                st0 = st.copy()
                st0.n[(v,u)] = TRUE
                workset.append(st0)
                st1 = st.copy()
                st1.n[(v,u)] = FALSE
                workset.append(st1)
                if st.sm[u] == MAYBE:
                    st2 = st.copy()
                    w = st2.copy_indiv(u)
                    st2.n[(v,u)] = TRUE
                    st2.n[(v,w)] = FALSE
                    workset.append(st2)
        self.structures = answerset
        # LOG.debug('num of structures focus ver deref %d\n', len(self.structures))


    def join(self, other, arbitrary_term):


        structures = [st for st in self.structures]
        LOG.debug('begin join num of structures self %d num of structures other %d', len(self.structures), len(other.structures))

        other.embed()

        # If we are at an assume node we have an arbitrary value, so we ignore the sizes of the summary nodes
        # while comparing, so that we can factor the size with the arbitrary value
        # Otherwise we compare normally, taking sizes into account

        if arbitrary_term is None:
            for st in other.structures:
                if st not in self.structures:
                    structures.append(st)
        else:
            for st in other.structures:
                canonical_map = None
                for next_st in structures:

                    canonical_map = next_st.get_canonical_map(st, True)

                    # LOG.debug('found canonical map? %s', str(canonical_map is not None))
                    if canonical_map:

                        summary_nodes = [v for v in canonical_map if next_st.sm[v] == MAYBE]
                        if summary_nodes:
                            add = False
                            next_st_copy = next_st.copy()
                            for v in summary_nodes:
                                # Counterpart in st
                                u = canonical_map[v]

                                # Adding arbitraray term only once
                                if arbitrary_term not in next_st_copy.size[v].free_symbols and expand(st.size[u]) != expand(next_st_copy.size[v]):

                                    # LOG.debug('old structure:\n %s', st)
                                    # LOG.debug('new structure:\n %s', next_st)

                                    # LOG.debug('old v size: %s', str(next_st_copy.size[v]))
                                    # LOG.debug('st size is %s', st.size[u])

                                    # new_size = arbitrary_term * (st.size[u] - next_st_copy.size[v])

                                    # new_size -= next_st_copy.size[v]
                                    # LOG.debug('after subsctract st - old %s', new_size)
                                    # new_size *= arbitrary_term

                                    # next_st_copy.size[v] += new_size
                                    next_st_copy.size[v] += arbitrary_term * (st.size[u] - next_st_copy.size[v])
                        
                                    # LOG.debug('new v size: %s', str(next_st_copy.size[v]))
                                    add = True

                            if add and next_st_copy not in structures:
                                structures.append(next_st_copy)
                        break

                # New structure, add to list of structures
                if not canonical_map:
                    # LOG.debug('did not find canonical map, adding to structures')
                    structures.append(st)

        LOG.debug('end join num of structures %d', len(structures))
        state = ShapeState(structures)
        # if arbitrary_term is not None and 't-' in str(arbitrary_term):
        #    LOG.debug('state in the end %s', state)
        return state
        # return ShapeState(structures)


    # Embed operation from paper where we look for summarizable nodes
    def embed(self):
        for st in self.structures:
            indiv_copy = copy.deepcopy(st.indiv)
            for u in indiv_copy:
                for v in indiv_copy:
                    if u in st.indiv and v in st.indiv and u < v and st._v_canonical_eq(u, st, v):
                        st._v_embed(u, v)

    def __str__(self):
        return f'{len(self.structures)} structure(s)'
        # if self.structures:
        #    return f'num of structures: {len(self.structures)}\n{str(self.structures[0])}'
        # else:
        #    return f'num of structures: {len(self.structures)}'

    def full_str(self):
        st_str = '\n\n'.join(str(st) for st in self.structures)
        return f'[{st_str}]'
        # if self.structures:
        #    return f'num of structures: {len(self.structures)}\n{str(self.structures[0])}'
        # else:
        #    return f'num of structures: {len(self.structures)}'

    @classmethod
    def initial(cls, symbols):
        return cls(
            structures=[]
        )

    def initialize_head(self, symbols):
        self.structures = [structure.Structure.initial(symbols)]

    def formula(self):
        formulas = [st.formula() for st in self.structures]
        return shortcuts.Or(*formulas)

    def post_transform(self):
        new_structures = []
        for st in self.structures:
            if st.coerce():
                new_structures.append(st)
        self.structures = new_structures
        # LOG.debug('num of structures coerce all %d\n', len(self.structures))


@ShapeState.transforms(lang_shape.VarVarAssignment)
def var_var_assignment(state, statement):

    lval = statement.lval
    rval = statement.rval
    state.focus(rval)

    for st in state.structures:

        for v in st.indiv:
            st.var[lval][v] = st.var[rval][v]
            st.reach[lval][v] = st.reach[rval][v]


@ShapeState.transforms(lang_shape.VarNewAssignment)
def var_new_assignment(state, statement):

    lval = statement.lval

    for st in state.structures:
        v = max(st.indiv) + 1 if st.indiv else 0
        for u in st.indiv:
            st.var[lval][u] = FALSE
            st.reach[lval][u] = FALSE
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
        st.size[v] = Integer(1)

        st.indiv.append(v)


@ShapeState.transforms(lang_shape.VarNextAssignment)
def var_next_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    state.focus_var_deref(rval)

    valid_st = state.structures.copy()

    for st in state.structures:

        stcopy = st.copy()
        var = stcopy.var
        reach = stcopy.reach
        n = stcopy.n
        cycle = stcopy.cycle
        exists = stcopy._exists
        not_null = stcopy._var_not_null

        # Possible null pointer reference detected
        if not_null(rval) == FALSE:
            valid_st.remove(st)
            continue

        for v in st.indiv:
            st.var[lval][v] = exists(lambda u : var[rval][u]._and(n[(u, v)]))
            st.reach[lval][v] = reach[rval][v]._and(cycle[v]._or(var[rval][v]._not()))

    state.structures = valid_st


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

    valid_st = state.structures.copy()

    for st in state.structures:

        stcopy = st.copy()
        var = stcopy.var
        reach = stcopy.reach
        n = stcopy.n
        cycle = stcopy.cycle
        shared = stcopy.shared

        exists = stcopy._exists
        is_shared = stcopy._v_shared
        not_null = stcopy._var_not_null

        # Possible null pointer reference detected
        if not_null(lval) == FALSE:
            valid_st.remove(st)
            continue

        for v in st.indiv:

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

        stcopy.n = st.n
        stcopy.update_n_plus()

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

    state.structures = valid_st


@ShapeState.transforms(lang_shape.NextNullAssignment)
def next_null_assignment(state, statement):

    lval = statement.lval
    state.focus(lval)

    valid_st = state.structures.copy()

    for st in state.structures:

        stcopy = st.copy()
        var = stcopy.var
        reach = stcopy.reach
        n = stcopy.n
        cycle = stcopy.cycle
        shared = stcopy.shared

        exists = stcopy._exists
        is_reachable = stcopy._v_reach
        is_shared = stcopy._v_shared
        not_null = stcopy._var_not_null

        # Possible null pointer reference detected
        if not_null(lval) == FALSE:
            valid_st.remove(st)
            continue

        for v in st.indiv:

            for w in st.indiv:
                st.n[(v,w)] = \
                    (
                        (
                            var[lval][v]._not()
                        )._and(
                            n[(v,w)]
                        )
                    )._or(FALSE)

        stcopy.n = st.n
        stcopy.update_n_plus()

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

        st.reach[lval] = var[lval]

    state.structures = valid_st


@ShapeState.transforms(lang.Skip)
@ShapeState.transforms(lang.Assert)
def noop(state, statement):
    pass

@ShapeState.transforms(lang.Assume)
def assume(state, statement):
    expr = statement.expr
    if isinstance(expr, lang.Falsehood):
        state.structures = []
    elif isinstance(expr, lang.Truth):
        pass
    elif isinstance(expr, lang_shape.EqualsVarVar):

        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus(rval)

        state.structures = [st for st in state.structures if (st._var_eq(lval, rval) == TRUE)]
        
    elif isinstance(expr, lang_shape.NotEqualsVarVar):

        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus(rval)

        state.structures = [st for st in state.structures if (st._var_eq(lval, rval) == FALSE)]

    elif isinstance(expr, lang_shape.EqualsVarNext):

        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus_var_deref(rval)

        state.structures = [st for st in state.structures if (st._var_next_eq(lval, rval) == TRUE)]

    elif isinstance(expr, lang_shape.NotEqualsVarNext):
        
        lval = expr.lval
        rval = expr.rval
        state.focus(lval)
        state.focus_var_deref(rval)

        state.structures = [st for st in state.structures if (st._var_next_eq(lval, rval) == FALSE)]

    elif isinstance(expr, lang_shape.EqualsVarNull):
        
        lval = expr.lval
        state.focus(lval)

        state.structures = [st for st in state.structures if (st._var_not_null(lval) == FALSE)]

    elif isinstance(expr, lang_shape.NotEqualsVarNull):
        
        lval = expr.lval
        state.focus(lval)

        state.structures = [st for st in state.structures if (st._var_not_null(lval) == TRUE)]

    else:
        LOG.warning(f'Missing handling for {expr}')
