import copy
import dataclasses
import typing
import logging
import types
import itertools
import collections

from pysmt import shortcuts
from analyzeshape import lang as lang_shape, three_valued_logic
from analyzeframework import lang
from sympy import *

LOG = logging.getLogger(__name__)


INVALID = Integer(-1)
SIZE_ONE = Integer(1)
SIZE_ZERO = Integer(0)

TRUE = three_valued_logic.ThreeValuedBool.TRUE
FALSE = three_valued_logic.ThreeValuedBool.FALSE
MAYBE = three_valued_logic.ThreeValuedBool.MAYBE


def is_negative(size):

    factored = factor(size)

    if not factored.args:
        return size < 0

    for farg in factored.args:
        perm_symbols = {sym for sym in farg.free_symbols if str(sym).startswith('P')}
        temp_symbols = {sym for sym in size.free_symbols if str(sym).startswith('T')}
        if perm_symbols:
            for arg in farg.args:
                if perm_symbols.intersection(arg.free_symbols):
                    expr = arg
                    for sym in arg.free_symbols:
                        expr = arg.subs(sym, 1)
                    if expr < 0:
                        return True
        elif temp_symbols:
            for arg in farg.args:
                if temp_symbols.intersection(arg.free_symbols):
                    expr = arg
                    for sym in arg.free_symbols:
                        expr = arg.subs(sym, 1)
                    if expr < 0:
                        return True
        else:
            if farg < 0:
                return True

def is_even(size):
    factors = factor_list(size)
    return any(factor for factor in factors if isinstance(factor, Integer) and factor % 2 == 0)


@dataclasses.dataclass
class Structure:
    indiv: typing.List[int]
    var: typing.Mapping[lang.Symbol, typing.Mapping[int, three_valued_logic.ThreeValuedBool]]
    reach: typing.Mapping[lang.Symbol, typing.Mapping[int, three_valued_logic.ThreeValuedBool]]
    cycle: typing.Mapping[int, three_valued_logic.ThreeValuedBool]
    shared: typing.Mapping[int, three_valued_logic.ThreeValuedBool]
    sm: typing.Mapping[int, three_valued_logic.ThreeValuedBool]
    n: typing.Mapping[typing.Tuple[int, int], three_valued_logic.ThreeValuedBool]
    n_plus: typing.Mapping[typing.Tuple[int, int], three_valued_logic.ThreeValuedBool]
    size: typing.Mapping[int, Expr]
    arbitrary_terms_stack: typing.List[Symbol]

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
        newst.arbitrary_terms_stack = copy.deepcopy(self.arbitrary_terms_stack)
        return newst


    def get_matching_structure(self, structures):
        for st in structures:
            canonical_map = st.get_canonical_map(self, True)
            if canonical_map:
                return st, canonical_map
        return None, None


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
                self.size[v].free_symbols == other.size[w].free_symbols), None)

            if u is not None:
                if ignore_arbitrary_sizes:
                    canonical_map[v] = u
                elif expand(self.size[v]) == expand(other.size[u]):
                    canonical_map[v] = u
                else:
                    return None
            else:
                return None

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
            st.size[v1] = Integer(1)

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

    def _v_concretisize(self, v):
        self.sm[v] = FALSE
        self.n[(v,v)] = FALSE
        for u in self.indiv:
            if self.sm[u] == FALSE:
                if self.n[(u,v)] == MAYBE:
                    self.n[(u,v)] = TRUE
                if self.n[(v,u)] == MAYBE:
                    self.n[(v,u)] = TRUE

    # Summarize v into u
    def _v_embed(self, u, v):
        for w in self.indiv:
            if self.n[(w,u)] != self.n[(w,v)]:
                self.n[(w,u)] = MAYBE
            if self.n[(u,w)] != self.n[(v,w)]:
                self.n[(u,w)] = MAYBE
        self.sm[u] = MAYBE
        self.size[u] += self.size[v]
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
            return Integer(-1)

        size = Integer(0)
        v = v1
        while v != v2:
            v = next((w for w in self.indiv if self.n[(v,w)] != FALSE and v != w), None)
            if v is None:
                return Integer(-1)
            size += self.size[v]

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
            arbitrary_terms_stack=[],
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
                            return False
                        elif res == MAYBE:
                            fix(self,v)
            elif par_num == 2:
                for v1 in self.indiv:
                    for v2 in self.indiv:
                        if lh(self,v1,v2) == TRUE:
                            res = rh(self,v1,v2)
                            if res == FALSE:
                                return False
                            elif res == MAYBE:
                                fix(self,v1,v2)


        return self.coerce_size(old_size)


    def coerce_size(self, old_size):

        for v in self.indiv:
            if self.sm[v] == FALSE and old_size[v] != SIZE_ONE:

                u = next((u for u in self.indiv if self.n[(v,u)] != FALSE and u != v \
                    and self._v_after_focus_eq(u, self, v) and self.sm[u] == MAYBE), None)

                if u is None:

                    old_size[v] -= 1 # Diff to add to prev node
                    volatile_variable = self.arbitrary_terms_stack[-1] if self.arbitrary_terms_stack else None

                    if not str(volatile_variable).startswith('T') or volatile_variable not in old_size[v].free_symbols:
                        return False

                    (volatile_size,) = solveset(old_size[v], volatile_variable) 

                    for w in self.indiv:
                        if volatile_variable in self.size[w].free_symbols:
                            self.size[w] = self.size[w].subs(volatile_variable, volatile_size)
                            if self.size[w] == 1:
                                self._v_concretisize(w)
                            elif self.size[w] == 0:
                                self._v_remove(w)
                            elif is_negative(self.size[w]): # Illegal state
                                return False

                    self.arbitrary_terms_stack.pop()

                else:
                    self.size[u] -= 1
                    # Concretisizing next node too and later join will handle the structure merge 
                    if self.size[u] == 1:
                        self._v_concretisize(u)

                    # Possible shared node that shouldn't have been and the length between the nodes is not preserved anyway
                    w = next((w for w in self.indiv if self.n[(v,w)] != FALSE and self.n[(u,w)] != FALSE and w != v and w != u), None)
                    if w is not None:
                        self.n[(v,w)] = FALSE
                break

        return True


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
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.And(
                            shortcuts.Bool(len12 != -1),
                            shortcuts.Bool(is_even(len12))
                        ),
                        lang_shape.Even(var1, var2).formula()
                    ),
                )
                clauses.append(
                    shortcuts.Implies(
                        shortcuts.And(
                            shortcuts.Bool(len12 != -1),
                            shortcuts.Bool(not is_even(len12))
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
                                    shortcuts.Bool(len12 != -1),
                                    shortcuts.Bool(len34 != -1),
                                    shortcuts.Bool(expand(len12) == expand(len34))
                                ),
                                lang_shape.Len(var1, var2, var3, var4).formula()
                            )
                        )

        return shortcuts.And(*clauses)
