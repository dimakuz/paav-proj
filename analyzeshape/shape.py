import copy
import dataclasses
import logging
import typing
import copy

from pysmt import shortcuts, fnode

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



def transforms(stmt_type):
    def decorator(func):
        ShapeState.TRANSFORMERS[stmt_type] = func
        return func
    return decorator


@dataclasses.dataclass
class ShapeState(abstract.AbstractState):
    structures: typing.List[structure.Structure]
    # in_loop: bool
    # arbitrary_size: fnode.FNode=shortcuts.Int(1)

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
                    # st2.size[u] = shortcuts.simplify(shortcuts.Minus(st2.size[u], shortcuts.Int(1)))
                    # st2.size[v] = shortcuts.simplify(shortcuts.Minus(st2.size[v], shortcuts.Int(1)))
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
                    # st2.size[u] = shortcuts.simplify(shortcuts.Minus(st2.size[u], shortcuts.Int(1)))
                    # st2.size[w] = shortcuts.simplify(shortcuts.Minus(st2.size[w], shortcuts.Int(1)))
                    workset.append(st2)
        self.structures = answerset
        # LOG.debug('num of structures focus ver deref %d\n', len(self.structures))


    def join(self, other, arbitrary_term):

        # for st in self.structures:
            # LOG.debug('begin is arb in array? %s', arbitrary_term in st.arbitrary_terms)

        structures = [st for st in self.structures]

        # LOG.debug('loop top %s', loop_top)
        # LOG.debug('in loop before %s', other.in_loop)
        LOG.debug('begin join num of structures self %d num of structures other %d', len(self.structures), len(other.structures))

        other.embed()

        # If we are at an assume node we have an arbitrary value, so we ignore the sizes of the summary nodes
        # while comparing, so that we can factor the size with the arbitrary value
        # Otherwise we compare normally, taking sizes into account
        # ignore_size = arbitrary_term is not None

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
                        # if arbitrary_visits and other.in_loop:

                        if 'CONST' in arbitrary_term:
                            break

                        # LOG.debug('we are about to add a new structure')

                        summary_nodes = [v for v in canonical_map if next_st.sm[v] == MAYBE]
                        if summary_nodes:
                            add = False
                            next_st_copy = next_st.copy()
                            # CHANGE NEXT_ST
                            # v is in next_st
                            for v in summary_nodes:
                                # Counterpart in st
                                u = canonical_map[v]
                                # LOG.debug('arbitrary size is %s', arbitrary_visits)
                                # updated_size = st.size[v]
                                # old_size = next_st.size[v]
                                # if next_st_copy.sm[v] == MAYBE:

                                
                                # LOG.debug('old v size: %s', str(shortcuts.simplify(next_st_copy.size[v])))
                                 #if structure._size_always_larger(st.size[u], next_st_copy.size[v]) and \
                                #     structure._size_new_name(next_st_copy.size[v], arbitrary_visits.symbol_name()):

                                # elif structure._size_always_larger(st.size[u], next_st_copy.size[v]) and \
                                    # structure._size_new_name(next_st_copy.size[v], arbitrary_visits.symbol_name()):
                                # if not next_st_copy.size[v].has_term(arbitrary_term) and st.size[u] != next_st_copy.size[v]:
                                if st.size[u] != next_st_copy.size[v]:

                                    LOG.debug('old v size: %s', str(next_st_copy.size[v]))

                                    new_size = structure.AbstractSize(st.size[u].terms)
                                    # if 'CONST' in arbitrary_term:
                                    #     next_st_copy.size[v] = new_size

                                    # else:
                                    new_size.substract(next_st_copy.size[v])
                                    new_size.multiply(arbitrary_term)
                                    # if new_size.is_const():
                                        # new_size.multiply(arbitrary_term)
                                    next_st_copy.size[v].add(new_size)

                                    # next_st_copy.size[v] = shortcuts.simplify(next_st_copy.size[v])

                                    # # Update length
                                    # for key in next_st_copy.var:
                                    #     if next_st_copy.reach[key][v]:
                                    #         for u in next_st_copy.indiv:
                                    #             if next_st_copy.reach[key][u]:
                                    #                 next_st_copy.length[key][u] = next_st_copy._v_length(key, u)
                        

                                    LOG.debug('new v size: %s', str(next_st_copy.size[v]))

                                    add = True


                                
                                # LOG.debug('new v size: %s', str(shortcuts.simplify(next_st_copy.size[v])))

                            if add:
                                # LOG.debug('and we are doing it!')
                                # next_st_copy.arbitrary_terms.append(arbitrary_term)
                                # if next_st in structures:
                                # structures.remove(next_st)
                                structures.append(next_st_copy)
                        break

                # New structure, add to list of structures
                if not canonical_map:
                    # LOG.debug('did not find canonical map, adding to structures')
                    structures.append(st)
                # elif arbitrary_visits:
                #     LOG.debug('found a map, did not add but updated next_st (likely)')
                # else:
                #     LOG.debug('found a map, did not add and did not update anything')

        # if arbitrary_visits:
            # self.in_loop = False
            # self.arbitrary_size = shortcuts.Int(1)

        # if other.in_loop or loop_top:
            # self.in_loop = True
        # LOG.debug('in loop after %s', self.in_loop)

        LOG.debug('end join num of structures %d', len(structures))
        # for st in structures:
            # LOG.debug('end is arb in array? %s', arbitrary_term in st.arbitrary_terms)
        state = ShapeState(structures)
        if arbitrary_term is not None:
            LOG.debug('state in the end %s', state)
        return state
        # return ShapeState(structures)


    # Embed operation from paper where we look for summarizable nodes
    def embed(self):
        for st in self.structures:
            indiv_copy = copy.deepcopy(st.indiv)
            for u in indiv_copy:
                for v in indiv_copy:
                    if u in st.indiv and v in st.indiv and u < v and st._v_canonical_eq(u, st, v):
                        # LOG.debug('something is summarizable!!! %s %s',u,v)
                        st._v_embed(u, v)

    def __str__(self):
        # meta = f'arb={str(self.arbitrary_size)}, in_loop={self.in_loop}'
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
            # in_loop=False,
            # arbitrary_size=shortcuts.Int(1)
        )

    def initialize_head(self, symbols):
        self.structures = [structure.Structure.initial(symbols)]

    def formula(self):
        formulas = [st.formula() for st in self.structures]
        return shortcuts.And(*formulas)

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

            # st.length[lval][v] = st.length[lval][v]


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

            # st.length[lval][u] = shortcuts.Int(-1)

        for key in st.var:
            st.var[key][v] = FALSE
            st.reach[key][v] = FALSE

        st.var[lval][v] = TRUE
        st.reach[lval][v] = TRUE
        st.n[(v,v)] = FALSE

        # st.length[lval][v] = shortcuts.Int(1)

        st.cycle[v] = FALSE
        st.shared[v] = FALSE
        st.sm[v] = FALSE
        st.size[v] = structure.AbstractSize({'1':1})

        st.indiv.append(v)


@ShapeState.transforms(lang_shape.VarNextAssignment)
def var_next_assignment(state, statement):
    
    lval = statement.lval
    rval = statement.rval
    state.focus_var_deref(rval)

    valid_st = state.structures.copy()

    for st in state.structures:

        exists = st._exists
        not_null = st._var_not_null

        # Possible null pointer reference detected
        if not_null(rval) == FALSE:
            valid_st.remove(st)
            continue

        u = st._var_get_indiv(rval)
        for v in st.indiv:
            st.var[lval][v] = exists(lambda u : st.var[rval][u]._and(st.n[(u, v)]))
            st.reach[lval][v] = st.reach[rval][v]._and(st.cycle[v]._or(st.var[rval][v]._not()))

        #     if st.reach[rval][v] == FALSE:
        #         st.length[lval][v] = shortcuts.Int(-1)
        #     else:
        #         st.length[lval][v] = shortcuts.simplify(shortcuts.Minus(st.length[rval][v], st.size[u]))

        # if st.cycle[u] == FALSE:
        #     st.length[lval][v] = shortcuts.Int(-1)



    state.structures = valid_st


@ShapeState.transforms(lang_shape.VarNullAssignment)
def var_null_assignment(state, statement):

    lval = statement.lval

    for st in state.structures:
        for u in st.indiv:
            st.var[lval][u] = FALSE
            st.reach[lval][u] = FALSE

            # st.length[lval][u] = shortcuts.Int(-1)


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

        u = st._var_get_indiv(lval)
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

                # if st.reach[key][u] and st.reach[rval][v]:
                #     st.length[key][v] = shortcuts.simplify(shortcuts.Plus(st.length[key][u], st.length[rval][v]))

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

                # if st.reach[key][v] == FALSE:
                #     st.length[key][v] = shortcuts.Int(-1)


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