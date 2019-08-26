import copy
import dataclasses
import typing
import logging
import types
import copy
import itertools

from pysmt import shortcuts, fnode
from analyzeshape import lang as lang_shape
from analyzeframework import lang
from enum import IntEnum

LOG = logging.getLogger(__name__)



# def _size_eq(v_size, u_size):

#     constraints = shortcuts.And(_size_get_constraints(v_size), _size_get_constraints(u_size))
#     cex = shortcuts.get_model(shortcuts.And(constraints, shortcuts.NotEquals(v_size, u_size)))

#     return cex is None

def _size_eq(v_size, u_size):
    constraints = shortcuts.And(_size_get_constraints(v_size), _size_get_constraints(u_size))
    return shortcuts.And(constraints, shortcuts.Equals(v_size, u_size))

def _size_always_larger(v_size, u_size):

    constraints = shortcuts.And(_size_get_constraints(v_size), _size_get_constraints(u_size))
    cex = shortcuts.get_model(shortcuts.And(constraints, shortcuts.LE(v_size, u_size)))

    return cex is None

def _size_get_constraints(v_size):
    v_arbitrary_sizes = shortcuts.get_free_variables(v_size)
    return shortcuts.And(*(shortcuts.GE(arbitrary_size, shortcuts.Int(0)) for arbitrary_size in v_arbitrary_sizes))
    # arb = shortcuts.And(*(shortcuts.GE(arbitrary_size, shortcuts.Int(0)) \
    #     for arbitrary_size in v_arbitrary_sizes if "ARB" in arbitrary_size.symbol_name()))
    # const = shortcuts.And(*(shortcuts.Equals(arbitrary_size, shortcuts.Int(1)) \
    #     for arbitrary_size in v_arbitrary_sizes if "CONST" in arbitrary_size.symbol_name()))
    # return shortcuts.And(arb, const)


def _size_new_name(v_size, name):
    v_arbitrary_sizes = shortcuts.get_free_variables(v_size)
    return name not in (arbitrary_size.symbol_name() for arbitrary_size in v_arbitrary_sizes)

# def _size_even(v_size):
    # return shortcuts.Equals(v_size, shortcuts.Times(shortcuts.FreshSymbol(shortcuts.INT), shortcuts.Int(2)))



class AbstractSize():

    terms: {}

    def add(self, other):
        for variable in self.terms:
            if variable in other.terms:
                self.terms[variable] += other.terms[variable]
        for variable in other.terms:
            if variable not in self.terms:
                self.terms[variable] = +other.terms[variable]

        self.terms = {variable: factor for variable, factor in self.terms.items() if factor != 0}
        return self

    def substract(self, other):
        for variable in self.terms:
            if variable in other.terms:
                self.terms[variable] -= other.terms[variable]
        for variable in other.terms:
            if variable not in self.terms:
                self.terms[variable] = -other.terms[variable]

        self.terms = {variable: factor for variable, factor in self.terms.items() if factor != 0}
        return self

    def multiply(self, term):
        self.terms[term] = self.terms['1']
        self.terms.pop('1')
        return self

    def has_term(self, term):
        return term in self.terms

    def is_const(self):
        return len(self.terms) == 1 and '1' in self.terms

    def even(self):
        return all(factor % 2 == 0 for variable, factor in self.terms.items())

    def __eq__(self, other):
        return self.terms == other.terms

    def __str__(self):

        def pretty_print(factor, variable):
            if variable == '1':
                return str(factor)
            else:
                if factor == 1:
                    return variable
                else:
                    return f'{factor}*{variable}'

        return ' + '.join(pretty_print(factor, variable) for variable, factor in self.terms.items())

    def __init__(self, new_terms):
        self.terms = new_terms

SIZE_ONE = AbstractSize({'1':1})
INVALID = AbstractSize({'1':-1})
SIZE_ZERO = AbstractSize({})



class ThreeValuedBool(IntEnum):
    TRUE = 2
    MAYBE = 1
    FALSE = 0

    def _not(self):

        if self == TRUE:
            return FALSE
        elif self == FALSE:
            return TRUE
        else:
            return MAYBE

    def _and(self, other):
        if self == FALSE or other == FALSE:
            return FALSE
        elif self == MAYBE or other == MAYBE:
            return MAYBE
        else:
            return TRUE

    def _or(self, other):
        if self == TRUE or other == TRUE:
            return TRUE
        elif self == MAYBE or other == MAYBE:
            return MAYBE
        else:
            return FALSE

    def __str__(self):
        if self == TRUE:
            return 'TRUE'
        elif self == MAYBE:
            return 'MAYBE'
        else:
            return 'FALSE'


TRUE = ThreeValuedBool.TRUE
FALSE = ThreeValuedBool.FALSE
MAYBE = ThreeValuedBool.MAYBE


@dataclasses.dataclass
class Structure:
    indiv: typing.List[int]
    var: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    reach: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    cycle: typing.Mapping[int, ThreeValuedBool]
    shared: typing.Mapping[int, ThreeValuedBool]
    sm: typing.Mapping[int, ThreeValuedBool]
    n: typing.Mapping[typing.Tuple[int, int], ThreeValuedBool]
    n_plus: typing.Mapping[typing.Tuple[int, int], ThreeValuedBool]

    size: typing.Mapping[int, AbstractSize]

    loop: typing.List[str]

    # old_size: typing.Mapping[int, fnode.FNode]
    # length: typing.Mapping[lang.Symbol, typing[int, fnode.FNode]]

    constr: typing.Set[typing.Tuple[int, callable, callable, callable]]

    def copy(self):
        newst = Structure.initial(self.var.keys())
        newst.indiv = copy.deepcopy(self.indiv)
        for var in self.var:
            newst.var[var] = copy.deepcopy(self.var[var])
            newst.reach[var] = copy.deepcopy(self.reach[var])
            # newst.length[var] = copy.deepcopy(self.length[var])
        newst.cycle = copy.deepcopy(self.cycle)
        newst.shared = copy.deepcopy(self.shared)
        newst.sm = copy.deepcopy(self.sm)
        newst.n = copy.deepcopy(self.n)

        newst.size = copy.deepcopy(self.size)
        newst.loop = copy.deepcopy(self.loop)
        return newst


    # Equality should be agnostic to the label assigned to each individual, which means this is the graph isomporphism problem
    # This is the efficient version from the paper, that compares canonical representations of an individual
    def __eq__(self, other):

        if self.get_canonical_map(other, False):
            return True
        else:
            return False


    def get_canonical_map(self, other, ignore_size):

        # Different size - different structure
        if len(self.indiv) != len(other.indiv):
            return None

        # We asume that the structures are after the embed operation and there are no
        # two individuals that are canonically equal to each other
        canonical_map = {}
        for v in self.indiv:

            u = next((w for w in other.indiv if self._v_canonical_eq(v, other, w) and self.sm[v] == other.sm[w]), None)

            if u is not None:
                if ignore_size:
                    canonical_map[v] = u
                elif self.size[v] == other.size[u]:
                    canonical_map[v] = u
                else:
                    # LOG.debug('self %s, other %s', str(self.size[v]), str(other.size[u]))
                    # if _size_eq(self.size[v], other.size[u]):
                    #     LOG.debug('they were equal after all...')
                    #     canonical_map[v] = u
                    # else:
                    return None
            else:
                # No canonical individual in other structure - different structure

                # u = next((w for w in other.indiv if self._v_canonical_eq(v, other, w) and \
                #     self.sm[v] == other.sm[w]), None)
                # if u is None:
                #     LOG.debug('really a different indiv!')
                # else:
                #     LOG.debug('there is a matching u=v%s !', u)
                #     LOG.debug('self size %s', self.size[v])
                #     LOG.debug('other size of u %s', other.size[u])
                #     LOG.debug('are sizes equal? %s', str(self.size[v])==str(other.size[u]))
                #     for w in other.indiv:
                #         LOG.debug('other size %s', other.size[w])
                return None
            # canonical_map[v] = u

        for v in self.indiv:
            n_fit = all(self.n[(v,u)] == other.n[(canonical_map[v],canonical_map[u])] for u in self.indiv)
            if not n_fit:
                # No n predicate fit - different structure
                return None

        return canonical_map


    @classmethod
    def init_constr(cls, symbols):

        constr = set()

        # Coerce fixing functions
        def fix_shared(st,v):
            st.shared[v] = TRUE
        def fix_shared_not(st,v):
            st.shared[v] = FALSE
        def fix_cycle(st,v):
            st.cycle[v] = TRUE
        def fix_cycle_not(st,v):
            st.cycle[v] = FALSE
        def fix_n_not(st,v1,v2):
            st.n[(v1,v2)] = FALSE
        def fix_sm_not(st,v1,v2): # v1=v2 if this function is called
            # old_size = st.size[v1]
            st.sm[v1] = FALSE
            st.size[v1] = SIZE_ONE
            # LOG.debug('setting size to 1 to v%d !!', v1)
            # if not st._v_get_copied_in_focus(v1):
            #     prev_sm = st._v_get_prev_sm(v1)
            #     LOG.debug('FIX get prev_sm for v%d: %s', v1, prev_sm if prev_sm is not None else 'None')
            #     LOG.debug(st)
            #     st.size[prev_sm] = shortcuts.simplify(shortcuts.Plus(
            #         st.size[prev_sm], shortcuts.Minus(old_size, shortcuts.Int(1))
            #     ))

        def get_reach_lh(var):
            def reach_lh(st,v):
                return st._v_reach(var,v)
            return reach_lh

        def get_reach_rh(var):
            def reach_rh(st,v):
                return st.reach[var][v]
            return reach_rh

        def get_reach_fix(var):
            def reach_fix(st,v):
                st.reach[var][v] = TRUE
            return reach_fix

        def get_reach_not_lh(var):
            def reach_not_lh(st,v):
                return st._v_reach(var,v)._not()
            return reach_not_lh

        def get_reach_not_rh(var):
            def reach_not_rh(st,v):
                return st.reach[var][v]._not()
            return reach_not_rh

        def get_reach_not_fix(var):
            def reach_not_fix(st,v):
                st.reach[var][v] = FALSE
            return reach_not_fix

        def get_var_not_lh(var):
            def var_not_lh(st,v):
                return st._v_not_var(var,v)
            return var_not_lh

        def get_var_not_rh(var):
            def var_not_rh(st,v):
                return st.var[var][v]._not()
            return var_not_rh

        def get_var_not_fix(var):
            def var_not_fix(st,v):
                st.var[var][v] = FALSE
            return var_not_fix

        def get_sm_not_lh(var):
            def sm_not_lh(st,v1,v2):
                return st._v_both_var(var,v1,v2)
            return sm_not_lh

        for var in symbols:

            constr.add((f'reach-{var}', 1, 
                get_reach_lh(var), get_reach_rh(var), get_reach_fix(var)))

            constr.add((f'reach-{var}-not', 1, 
                get_reach_not_lh(var), get_reach_not_rh(var), get_reach_not_fix(var)))

            constr.add((f'var-{var}-not', 1, 
                get_var_not_lh(var), get_var_not_rh(var), get_var_not_fix(var)))

            constr.add((f'sm-{var}-not', 2, 
                get_sm_not_lh(var), lambda st,v1,v2: st._v_can_fix_sm(v1,v2), fix_sm_not))

        constr.add(('shared', 1, 
            lambda st,v: st._v_shared(v), lambda st,v: st.shared[v], fix_shared))

        constr.add(('shared-not', 1, 
            lambda st,v: st._v_shared(v)._not(), lambda st,v: st.shared[v]._not(), fix_shared_not))

        constr.add(('cycle', 1, 
            lambda st,v: st._v_cycle(v), lambda st,v: st.cycle[v], fix_cycle))

        constr.add(('cycle-not', 1, 
            lambda st,v: st._v_cycle(v)._not(), lambda st,v: st.cycle[v]._not(), fix_cycle_not))

        constr.add(('n-not', 2, 
            lambda st,v1,v2: st._v_not_n(v1,v2), lambda st,v1,v2: st.n[(v1,v2)]._not(), fix_n_not))

        constr.add(('n-not-shared', 2, 
            lambda st,v1,v2: st._v_not_n_hs(v1,v2), lambda st,v1,v2: st.n[(v1,v2)]._not(), fix_n_not))

        constr.add(('sm-not', 2, 
            lambda st,v1,v2: st._v_both_n(v1,v2), lambda st,v1,v2: st._v_can_fix_sm(v1,v2), fix_sm_not))
        
        constr.add(('sm-not-shared', 2, 
            lambda st,v1,v2: st._v_both_n_hs(v1,v2), lambda st,v1,v2: st._v_can_fix_sm(v1,v2), fix_sm_not))

        return constr


    def __str__(self):
        lines = []
        for symbol in self.var:
            var = ', '.join(f'v{v} = {str(self.var[symbol][v])}' for v in self.indiv)
            lines.append(f'var_{symbol.name}: [{var}]')

        for symbol in self.var:
            reach = ', '.join(f'v{v} = {str(self.reach[symbol][v])}' for v in self.indiv)
            lines.append(f'reach_{symbol.name}: [{reach}]')

        cycle = ', '.join(f'v{v} = {str(self.cycle[v])}' for v in self.indiv)
        lines.append(f'cycle: [{cycle}]')

        shared = ', '.join(f'v{v} = {str(self.shared[v])}' for v in self.indiv)
        lines.append(f'shared: [{shared}]')

        sm = ', '.join(f'v{v} = {str(self.sm[v])}' for v in self.indiv)
        lines.append(f'sm: [{sm}]')

        size = ', '.join(f'v{v} = {str(self.size[v])}' for v in self.indiv)
        lines.append(f'size: [{size}]')

        n = ', '.join(f'v{v0},v{v1} = {str(self.n[(v0,v1)])}' for v0 in self.indiv for v1 in self.indiv)
        lines.append(f'n: [{n}]')

        return '\n'.join(lines)


    # Equality based on unary predicates
    def _v_canonical_eq(self, u, other, v):
        return all(self.var[key][u] == other.var[key][v] and \
                    self.reach[key][u] == other.reach[key][v] for key in self.var) and \
                    self.cycle[u] == other.cycle[v] and \
                    self.shared[u] == other.shared[v]

    def copy_indiv(self, u):
        v = max(self.indiv) + 1
        for key in self.var:
            self.var[key][v] = self.var[key][u]
            self.reach[key][v] = self.reach[key][u]
            # self.length[key][v] = self.length[key][u].deepcopy()
        self.cycle[v] = self.cycle[u]
        self.shared[v] = self.shared[u]
        self.sm[v] = self.sm[u]
        self.size[v] = copy.deepcopy(self.size[u])
        self.n[(v,v)] = self.n[(u,u)]
        for w in self.indiv:
            self.n[(v,w)] = self.n[(u,w)]
            self.n[(w,v)] = self.n[(w,u)]
        self.indiv.append(v)
        return v

    # Summarize v into u
    def _v_embed(self, u, v):
        self.indiv.remove(v)
        self._v_update_embedded(u, v)
        for key in self.var:
            self.var[key].pop(v)
            self.reach[key].pop(v)
            # self.length[key].pop(v)
        self.cycle.pop(v)
        self.shared.pop(v)
        self.sm.pop(v)
        self.n.pop((v,v))
        for w in self.indiv:
            self.n.pop((v,w))
            self.n.pop((w,v))
        self.size.pop(v)

    # Hackish but relatively fast way to compare size formula
    def _v_size_eq(self, u, other, v):
        return self.size[u] == other.size[v]

    # def _v_get_copied_in_focus(self, v):
    #     copied = next((u for u in self.indiv if self.n[(v,u)] != FALSE and u != v and self.sm[u] == MAYBE), None)

    #     LOG.debug('found copied for v%d: %s', v, copied if copied is not None else 'None')
    #     # LOG.debug(self)
    #     return copied is not None

    def _v_update_embedded(self, u, v):
        for w in self.indiv:
            if self.n[(w,u)] != self.n[(w,v)]:
                self.n[(w,u)] = MAYBE
            if self.n[(u,w)] != self.n[(v,w)]:
                self.n[(u,w)] = MAYBE        
        self.sm[u] = MAYBE
        self.size[u].add(self.size[v])

    def _v_can_fix_sm(self, v1, v2):
        eq = self._v_eq(v1, v2)
        # if eq == MAYBE:

        #     # Is there a next node which was copied during focus operation?
        #     # If not, we hope to find a previous summary node so we can fix node size
        #     if not self._v_get_copied_in_focus(v1):
        #         prev_sm = self._v_get_prev_sm(v1)
        #         LOG.debug('CAN FIX get prev_sm for v%d: %s', v1, prev_sm if prev_sm is not None else 'None')
        #         LOG.debug(self)

        #         # If not, the structure is unrepairable
        #         if prev_sm is None:
        #             return FALSE

        return eq


    # Equality taking summary nodes into account
    def _v_eq(self, v1, v2):
        if (v1 != v2):
            return FALSE
        else:
            return self.sm[v1]._not()

    def _v_get_prev_sm(self, v):
        u = next((w for w in self.indiv if self.n[(w,v)] != FALSE and v != w), None)
        if u is None:
            return None
        # visited = [prev_v]
        while self.sm[u] == FALSE:
            u = next((w for w in self.indiv if self.n[(w,u)] != FALSE and u != w), None)
            # LOG.debug('current v%d', prev_v)
            if u is None:
                return None
            # visited.append(prev_v)
        return u

    # Is the individual heap shared
    def _v_shared(self, v):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.n[(u1,v)]._and(self.n[(u2,v)])._and(self._v_eq(u1,u2)._not())
                )
            )

    # Is the individual reachable from variable
    def _v_reach(self, var, v):
        return self.var[var][v]._or(self._exists(lambda u : self.var[var][u]._and(self.n_plus[(u,v)])))

    # Symbolic length between variable and individual
    # def _v_length(self, var, v):

    #     u = self._var_get_indiv(var)
    #     length = self.size[u].add(self.size[v])

    #     u = next((w for w in self.indiv if self.n[(u,w)] != FALSE and u != w), None)
    #     while u != v:
    #         if u is None:
    #             return INVALID
    #         length = length.add(self.size[u])
    #         u = next((w for w in self.indiv if self.n[(u,w)] != FALSE and u != w), None)

    #     return length


    # Is the individual resides on a cycle
    def _v_cycle(self, v):
        return self.n_plus[(v,v)]

    def _v_not_var(self, var, v):
        return self._exists(lambda u : self.var[var][u]._and(self._v_eq(v, u)._not()))

    def _v_not_n(self, v1, v2):
        return self._exists(lambda u : self.n[(v1,u)]._and(self._v_eq(u, v2)._not()))

    def _v_not_n_hs(self, v1, v2):
        return self._exists(lambda u : self.n[(u,v2)]._and(self._v_eq(u, v1)._not())._and(self.shared[v2]._not()))

    def _v_both_n(self, v1, v2):
        return self._exists(lambda u : self.n[(u,v1)]._and(self.n[(u,v2)]))

    def _v_both_n_hs(self, v1, v2):
        return self._exists(lambda u : self.n[(v1,u)]._and(self.n[(v2,u)])._and(self.shared[u]._not()))

    def _v_both_var(self, var, v1, v2):
        return self.var[var][v1]._and(self.var[var][v2])

    def _var_not_null(self, var1):
        return self._exists(lambda u : self.var[var1][u])

    def _var_eq(self, var1, var2):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.var[var1][u1]._and(self.var[var2][u2])._and(self._v_eq(u1, u2))))

    def _var_next_eq(self, var1, var2):
        return self._exists(lambda u1 : \
            self._exists(lambda u2: \
                self.var[var1][u1]._and(self.var[var2][u2])._and(self.n[(u1,u2)])
                )
            )

    def _var_reach(self, var1, var2):
        return self._exists(lambda u : self.var[var2][u]._and(self.reach[var1][u]))

    def _var_get_length(self, var1, var2):
        v1 = self._var_get_indiv(var1)
        v2 = self._var_get_indiv(var2)

        if v1 is None or v2 is None:
            return INVALID

        size = SIZE_ZERO

        v = next((w for w in self.indiv if self.n[(v1,w)] != FALSE and v1 != w), None)
        while v != v2:
            if v is None:
                return INVALID
            size.add(self.size[v])
            v = next((w for w in self.indiv if self.n[(v,w)] != FALSE and v != w), None)

        return size

    # def _var_get_length(self, var1, var2):
    #     u = self._var_get_indiv(var2)
    #     return shortcuts.Minus(shortcuts.Minus(self.length[var1][u], self.size[var1]), self.size[var2])

    def _var_get_indiv(self, var):
        return next((u for u in self.indiv if self.var[var][u] != FALSE), None)

    # Assuming var1 is not null
    # def _var_get_size(self, var1):
    #     v1 = next((u for u in self.indiv if self.var[var1][u] == TRUE), None)

    #     if v1 is None or v2 is None:
    #         return shortcuts.Int(-1)

    #     return self.size[v1]


    # Transitive closure of n
    def update_n_plus(self):
        self.n_plus = copy.deepcopy(self.n)
        for u in self.indiv:
            for v in self.indiv:
                for w in self.indiv:
                    self.n_plus[(v,w)] = self.n_plus[(v,w)]._or(self.n_plus[(v,u)]._and(self.n_plus[(u,w)]))

    def _exists(self, pred):
        return max(pred(v) for v in self.indiv) if self.indiv else FALSE

    def _forall(self, pred):
        return min(pred(v) for v in self.indiv) if self.indiv else TRUE


    @classmethod
    def initial(cls, symbols):
        return cls(
            indiv=[],
            var={symbol: dict() for symbol in symbols},
            reach={symbol: dict() for symbol in symbols},
            cycle=dict(),
            shared=dict(),
            sm=dict(),
            n=dict(),
            n_plus=dict(),
            size=dict(),
            loop=[],
            constr=cls.init_constr(symbols)
        )

    def coerce(self):

        self.update_n_plus()
        old_size = copy.deepcopy(self.size)

        for constraint in self.constr:
            (name, par_num, lh, rh, fix) = constraint
            if par_num == 1:
                for v in self.indiv:
                    if lh(self,v) == TRUE:
                        res = rh(self,v)
                        if res == FALSE:
                            # LOG.debug('removing %s : (v)=v%s', name, v)
                            return False
                        elif res == MAYBE:
                            # LOG.debug('fixing %s : (v)=v%s', name, v)
                            fix(self,v)
            elif par_num == 2:
                for v1 in self.indiv:
                    for v2 in self.indiv:
                        if lh(self,v1,v2) == TRUE:
                            res = rh(self,v1,v2)
                            if res == FALSE:
                                # LOG.debug('removing %s : (v1)=v%s, (v2)=v%s', name, v1, v2)
                                return False
                            elif res == MAYBE:
                                # LOG.debug('fixing %s : (v1)=v%s, (v2)=v%s', name, v1, v2)
                                fix(self,v1,v2)


        return self.coerce_size(old_size)


    def coerce_size(self, old_size):

        for v in self.indiv:
            # LOG.debug('comparing sizes %s and %s for v%d', self.size[v], old_size[v], v)
            if self.sm[v] == FALSE and old_size[v] != SIZE_ONE:

                LOG.debug('node v%d is not equal: new size is %s, old size is %s', v, self.size[v], old_size[v])
                u = next((u for u in self.indiv if self.n[(v,u)] != FALSE and u != v and self.sm[u] == MAYBE), None)


                LOG.debug('is there a next node that fixes? %s', u if u is not None else 'No!')

                if u is None:
                    u = self._v_get_prev_sm(v)

                    LOG.debug('is there a prev summary node that fixes? %s', u if u is not None else 'No!')
                    if u is None:
                        # No previous summary node that can take the size
                        return False
                    else:
                        old_size[v].substract(self.size[v])
                        self.size[u].add(old_size[v])

                        LOG.debug('fixing and setting v%d to have size %s', u, self.size[u])
                else:
                    self.size[u].substract(SIZE_ONE)
                    # Concretisizing next node too and later join will handle the structure merge 
                    if (self.size[u] == SIZE_ONE):
                        self.sm[u] = FALSE 
                    LOG.debug('fixing and setting v%d to have size %s', u, self.size[u])

        return True


    # def coerce_length(self):

    #     for var in self.var:
    #         u = self._var_get_indiv(var)

    #         # Size of node and length from variable to itself don't fit
    #         if not self._size_eq(self.size[u], self.length[var][u]):

    #             v = next((w for w in self.indiv if self.n[(u,w)] != FALSE and u != w), None)

    #             if v is None:
    #                 #TODO must fix previous

    #             length_to_next = shortcuts.simplify(shortcuts.Plus(self.size[u], self.size[v]))
    #             if not self._size_eq(length_to_next, self.length[var][v]):
    #                 #TODO must fix previous

    #             # Can easy fix
    #             diff = shortcuts.Minus(self.length[var][u], self.size[u])
    #             for var2 in self.var:
    #                 if self.reach[var2][u] != FALSE:
    #                     self.length[var2][u] = shortcuts.simplify(shortcuts.Minus(self.length[var2][u], diff))



    def formula(self):
        clauses = []

        for var1 in self.var:
            clauses.append(
                shortcuts.Iff(
                    lang_shape.EqualsVarNull(var1).formula(),
                    shortcuts.Bool(self._var_not_null(var1) == FALSE)
                ),
            )
            for var2 in self.var:
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.EqualsVarVar(var1, var2).formula(),
                        shortcuts.Bool(self._var_eq(var1, var2) == TRUE)
                    ),
                )
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.EqualsVarNext(var1, var2).formula(),
                        shortcuts.Bool(self._var_next_eq(var1, var2) == TRUE)
                    ),
                )
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.Ls(var1, var2).formula(),
                        shortcuts.Bool(self._var_reach(var1, var2) == TRUE)
                    ),
                )
                len12 = self._var_get_length(var1, var2)
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.Even(var1, var2).formula(),
                        shortcuts.And(
                            shortcuts.Bool(len12 != INVALID),
                            shortcuts.Bool(len12.even())
                        )
                    ),
                )
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.Odd(var1, var2).formula(),
                        shortcuts.And(
                            shortcuts.Bool(len12 != INVALID),
                            shortcuts.Bool(not len12.even())
                        )
                    ),
                )
                if str(var1) == 'y' and str(var2) == 'yy':
                    LOG.debug('var1= %s, var2=%s, len=%s', var1, var2, len12)
                for var3 in self.var:
                    for var4 in self.var:
                        len34 = self._var_get_length(var3, var4)

                        if str(var3) == 'z' and str(var4) == 'zz':
                            LOG.debug('var3= %s, var4=%s, len=%s', var3, var4, len34)
                        clauses.append(
                            shortcuts.Iff(
                                lang_shape.Len(var1, var2, var3, var4).formula(),
                                shortcuts.And(
                                    shortcuts.Bool(len12 != INVALID),
                                    shortcuts.Bool(len34 != INVALID),
                                    shortcuts.Bool(len12 == len34)
                                )
                            )
                        )

        return shortcuts.And(*clauses)
