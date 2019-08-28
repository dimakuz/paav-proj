import copy
import dataclasses
import typing
import logging
import types
import copy
import itertools
import collections

from pysmt import shortcuts
from analyzeshape import lang as lang_shape
from analyzeframework import lang
from enum import IntEnum

LOG = logging.getLogger(__name__)


class AbstractSize():

    terms: collections.OrderedDict()

    def add(self, other):
        for variable in self.terms:
            if variable in other.terms:
                self.terms[variable] += other.terms[variable]
        for variable in other.terms:
            if variable not in self.terms:
                self.terms[variable] = +other.terms[variable]

        # self.terms = {variable: factor for variable, factor in self.terms.items() if factor != 0 or variable == '1'}
        for variable, factor in list(self.terms.items()):
            if factor == 0 and variable != '1':
                self.terms.pop(variable)

        return self

    def substract(self, other):
        for variable in self.terms:
            if variable in other.terms:
                self.terms[variable] -= other.terms[variable]
        for variable in other.terms:
            if variable not in self.terms:
                self.terms[variable] = -other.terms[variable]

        # self.terms = {variable: factor for variable, factor in self.terms.items() if factor != 0 or variable == '1'}
        for variable, factor in list(self.terms.items()):
            if factor == 0 and variable != '1':
                self.terms.pop(variable)

        return self

    def multiply(self, variable):
        self.terms[variable] = self.terms['1']
        self.terms['1'] = 0
        return self

    def has_term(self, term):
        return term in self.terms.keys()

    def is_negative(self):
        return any((var, fac) for (var, fac) in self.terms.items() if 'PERM' in var and fac < 0)

    def even(self):
        return all(factor % 2 == 0 for variable, factor in self.terms.items())

    def variables_eq(self, other):
        return set(self.terms.keys()) == set(other.terms.keys())

    def get_last_term(self):
        return next(reversed(self.terms))

    def extract_variable(self, variable):
        factor = self.terms[variable]
        size = AbstractSize(self.terms)
        size.terms.pop(variable)
        for var, fac in size.terms.items():
            if fac % factor == 0:
                size.terms[var] /= -factor
            else:
                return INVALID
        return size

    def substitute(self, variable, size):
        if variable in self.terms.keys():
            factor = self.terms[variable]
            self.terms.pop(variable)
            temp_size = AbstractSize(size.terms)
            for var, fac in temp_size.terms.items():
                temp_size.terms[var] *= factor
            self.add(temp_size)

    def __eq__(self, other):
        return self.terms == other.terms

    def __str__(self):

        def pretty_print(factor, variable):
            prefix = ''
            if factor < 0:
                prefix = '- '
            else:
                prefix = '+ '
            if variable == '1':
                return prefix + str(factor)
            else:
                if abs(factor) == 1:
                    return prefix + variable
                else:
                    return f'{prefix}{abs(factor)}*{variable}'

        return ' '.join(pretty_print(factor, variable) for variable, factor in self.terms.items())

    def __init__(self, newterms):
        self.terms = copy.deepcopy(newterms)

INVALID = AbstractSize(collections.OrderedDict([('1', -1)]))
SIZE_ONE = AbstractSize(collections.OrderedDict([('1', 1)]))
SIZE_ZERO = AbstractSize(collections.OrderedDict([('1', 0)]))


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

    constr: typing.Set[typing.Tuple[int, callable, callable, callable]]

    def copy(self):
        newst = Structure.initial(self.var.keys())
        newst.indiv = copy.deepcopy(self.indiv)
        for var in self.var:
            newst.var[var] = copy.deepcopy(self.var[var])
            newst.reach[var] = copy.deepcopy(self.reach[var])
        newst.cycle = copy.deepcopy(self.cycle)
        newst.shared = copy.deepcopy(self.shared)
        newst.sm = copy.deepcopy(self.sm)
        newst.n = copy.deepcopy(self.n)
        newst.size = copy.deepcopy(self.size)
        return newst


    # Equality should be agnostic to the label assigned to each individual, which means this is the graph isomporphism problem
    # This is the efficient version from the paper, that compares canonical representations of an individual
    def __eq__(self, other):

        if self.get_canonical_map(other, False):
            return True
        else:
            return False


    def get_canonical_map(self, other, ignore_arbitrary_sizes):

        # Different size - different structure
        if len(self.indiv) != len(other.indiv):
            return None

        # We asume that the structures are after the embed operation and there are no
        # two individuals that are canonically equal to each other
        canonical_map = {}
        for v in self.indiv:

            u = next((w for w in other.indiv if self._v_canonical_eq(v, other, w) and self.sm[v] == other.sm[w] and \
                self.size[v].variables_eq(other.size[w])), None)

            if u is not None:
                if ignore_arbitrary_sizes:
                    canonical_map[v] = u
                elif self.size[v] == other.size[u]:
                    canonical_map[v] = u
                else:
                    return None
            else:
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
            st.sm[v1] = FALSE
            st.size[v1] = AbstractSize(collections.OrderedDict([('1', 1)]))

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
                get_sm_not_lh(var), lambda st,v1,v2: st._v_eq(v1,v2), fix_sm_not))

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
            lambda st,v1,v2: st._v_both_n(v1,v2), lambda st,v1,v2: st._v_eq(v1,v2), fix_sm_not))
        
        constr.add(('sm-not-shared', 2, 
            lambda st,v1,v2: st._v_both_n_hs(v1,v2), lambda st,v1,v2: st._v_eq(v1,v2), fix_sm_not))

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

    def _v_after_focus_eq(self, u, other, v):
        return all(self.reach[key][u] == other.reach[key][v] for key in self.var) and \
                    self.cycle[u] == other.cycle[v] and \
                    self.shared[u] == other.shared[v]

    def copy_indiv(self, u):
        v = max(self.indiv) + 1
        for key in self.var:
            self.var[key][v] = self.var[key][u]
            self.reach[key][v] = self.reach[key][u]
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
        for w in self.indiv:
            if self.n[(w,u)] != self.n[(w,v)]:
                self.n[(w,u)] = MAYBE
            if self.n[(u,w)] != self.n[(v,w)]:
                self.n[(u,w)] = MAYBE
        self.sm[u] = MAYBE
        self.size[u].add(self.size[v])
        self._v_remove(v)

    def _v_remove(self, v):
        self.indiv.remove(v)
        for key in self.var:
            self.var[key].pop(v)
            self.reach[key].pop(v)
        self.cycle.pop(v)
        self.shared.pop(v)
        self.sm.pop(v)
        self.n.pop((v,v))
        for w in self.indiv:
            self.n.pop((v,w))
            self.n.pop((w,v))
        self.size.pop(v)

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
                self.var[var1][u1]._and(self.var[var2][u2])._and(self.n[(u2,u1)])
                )
            )

    def _var_reach(self, var1, var2):
        return self._exists(lambda u : self.var[var2][u]._and(self.reach[var1][u]))


    def _var_get_length(self, var1, var2):
        v1 = self._var_get_indiv(var1)
        v2 = self._var_get_indiv(var2)

        if v1 is None or v2 is None:
            return INVALID

        size = AbstractSize(collections.OrderedDict([('1', 0)]))

        v = next((w for w in self.indiv if self.n[(v1,w)] != FALSE and v1 != w), None)
        while v != v2:
            if v is None:
                return INVALID
            size.add(self.size[v])
            v = next((w for w in self.indiv if self.n[(v,w)] != FALSE and v != w), None)

        return size

    def _var_get_indiv(self, var):
        return next((u for u in self.indiv if self.var[var][u] != FALSE), None)


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
            constr=cls.init_constr(symbols)
        )

    def coerce(self):

        self.update_n_plus()
        old_size = copy.deepcopy(self.size)

        # LOG.debug('begining coerce session')
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

                # LOG.debug('node v%d is not equal: new size is %s, old size is %s', v, self.size[v], old_size[v])
                u = next((u for u in self.indiv if self.n[(v,u)] != FALSE and u != v \
                    and self._v_after_focus_eq(u, self, v) and self.sm[u] == MAYBE), None)


                # LOG.debug('is there a next node that fixes? %s', u if u is not None else 'No!')

                if u is None:
                    # u = self._v_get_prev_sm(v)

                    # # LOG.debug('is there a prev summary node that fixes? %s', u if u is not None else 'No!')
                    # if u is None:
                    #     # No previous summary node that can take the size
                    #     return False
                    # else:

                        
                    # LOG.debug('have to fix v%d that have size %s and v%d that have size %s', v, old_size[v], u, self.size[u])
                    # old_size[v].substract(self.size[v])
                    old_size[v].substract(SIZE_ONE) # Diff to add to prev node
                    
                    # LOG.debug('old size is: %s, last factor %s',old_size[v],isinstance(old_size[v].get_last_term(), str))
                    volatile_variable = old_size[v].get_last_term()

                    if 'TEMP' not in volatile_variable:
                        LOG.debug('a size is not symbolic!! %s', old_size[v])
                        # assert False
                        return False


                    volatile_size = old_size[v].extract_variable(volatile_variable)

                    if volatile_size == INVALID:
                        LOG.debug('a size is not an integer!! %s', old_size[v])
                        assert False
                        return False

                    # Substitute
                    for w in self.indiv:
                        self.size[w].substitute(volatile_variable, volatile_size)
                        if self.size[w] == SIZE_ONE:
                            self._v_concretisize(w)
                        elif self.size[w] == SIZE_ZERO:
                            self._v_remove(w)
                        elif self.size[w].is_negative():
                            LOG.debug('a size was found to be negative!!!! %s', self.size[w])
                            assert False
                            return False

                    # else:
                    #     self.size[u].add(old_size[v])

                    # LOG.debug('fixing and setting v%d to have size %s', u, self.size[u])
                else:
                    self.size[u].substract(SIZE_ONE)
                    # Concretisizing next node too and later join will handle the structure merge 
                    if (self.size[u] == SIZE_ONE):
                        self._v_concretisize(u)

                    # Possible shared node that shouldn't have been
                    # Also, the length between the nodes is not preserved anyway
                    w = next((w for w in self.indiv if self.n[(v,w)] != FALSE and self.n[(u,w)] != FALSE and w != v and w != u), None)
                    if w is not None:
                        # LOG.debug('found v%d that fits into the description (v%d and v%d)', w, u, v)
                        self.n[(v,w)] = FALSE

                    # LOG.debug('fixing and setting v%d to have size %s', u, self.size[u])

                # TODO: check if this fix is good enough!!
                break

        return True

    def _v_concretisize(self, v):
        self.sm[v] = FALSE
        self.n[(v,v)] = FALSE
        for u in self.indiv:
            if self.sm[u] == FALSE:
                if self.n[(u,v)] == MAYBE:
                    self.n[(u,v)] = TRUE
                if self.n[(v,u)] == MAYBE:
                    self.n[(v,u)] = TRUE



    def formula(self):
        clauses = []

        for var1 in self.var:
            clauses.append(
                shortcuts.Implies(
                    shortcuts.Bool(self._var_not_null(var1) == FALSE),
                    lang_shape.EqualsVarNull(var1).formula()
                ),
            )
            clauses.append(
                shortcuts.Implies(
                    shortcuts.Bool(self._var_not_null(var1) == TRUE),
                    lang_shape.NotEqualsVarNull(var1).formula()
                ),
            )
            for var2 in self.var:
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.Bool(self._var_eq(var1, var2) == TRUE),
                        lang_shape.EqualsVarVar(var1, var2).formula()
                    ),
                )
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.Bool(self._var_eq(var1, var2) == FALSE),
                        lang_shape.NotEqualsVarVar(var1, var2).formula()
                    ),
                )
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.Bool(self._var_next_eq(var1, var2) == TRUE),
                        lang_shape.EqualsVarNext(var1, var2).formula()
                    ),
                )
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.Bool(self._var_next_eq(var1, var2) == FALSE),
                        lang_shape.NotEqualsVarNext(var1, var2).formula()
                    ),
                )
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.Bool(self._var_reach(var1, var2) == TRUE),
                        lang_shape.Ls(var1, var2).formula(),
                    ),
                )
                len12 = self._var_get_length(var1, var2)
                if str(var1) == 'y' and str(var2) == 'yy':
                    LOG.debug('var1= %s, var2=%s, len=%s', var1, var2, len12)
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.And(
                            shortcuts.Bool(len12 != INVALID),
                            shortcuts.Bool(len12.even())
                        ),
                        lang_shape.Even(var1, var2).formula()
                    ),
                )
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.And(
                            shortcuts.Bool(len12 != INVALID),
                            shortcuts.Bool(len12.even() == False)
                        ),
                        lang_shape.Odd(var1, var2).formula()
                    ),
                )
                for var3 in self.var:
                    for var4 in self.var:
                        len34 = self._var_get_length(var3, var4)
                        clauses.append(
                            shortcuts.Implies(
                                shortcuts.And(
                                    shortcuts.Bool(len12 != INVALID),
                                    shortcuts.Bool(len34 != INVALID),
                                    shortcuts.Bool(len12 == len34)
                                ),
                                lang_shape.Len(var1, var2, var3, var4).formula()
                            )
                        )

        return shortcuts.And(*clauses)
