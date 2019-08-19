import copy
import dataclasses
import typing
import logging
import types
import copy
import itertools

from pysmt import shortcuts
from analyzeshape import lang as lang_shape
from analyzeframework import lang
from enum import IntEnum

LOG = logging.getLogger(__name__)


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

    constr: typing.Set[typing.Tuple[str, int, callable, callable, callable]]

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
        return newst


    # Equality should be agnostic to the label assigned to each individual, which means this is
    # the graph isomporphism problem
    # This is the efficient version from the paper, that compares canonical representations of an individual
    def __eq__(self, other):

        # Different size - different structure
        if len(self.indiv) != len(other.indiv):
            return False

        # We asume that the structures are after the embed operation and there are no
        # two individuals that are canonically equal to each other
        canonical_map = dict()
        for v in self.indiv:
            u = next((w for w in other.indiv if self._v_canonical_eq(v, other, w)), None)
            if u is None:
                # No canonical individual in other structure - different structure
                return False
            canonical_map[v] = u

        for v in self.indiv:
            n_fit = all(self.n[(v,u)] == other.n[(canonical_map[v],canonical_map[u])] for u in self.indiv)
            if not n_fit:
                # No n predicate fit - different structure
                return False

        return True


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

        n = ', '.join(f'v{v0},v{v1} = {str(self.n[(v0,v1)])}' for v0 in self.indiv for v1 in self.indiv)
        lines.append(f'n: [{n}]')

        return '\n'.join(lines)


    # Equality based on unary predicates
    def _v_canonical_eq(self, u, other, v):
        return all(self.var[key][u] == other.var[key][v] and \
                    self.reach[key][u] == other.reach[key][v] for key in self.var) and \
                    self.cycle[u] == other.cycle[v] and \
                    self.shared[u] == other.shared[v] and \
                    self.sm[u] == other.sm[v]

    def copy_indiv(self, u):
        v = max(self.indiv) + 1
        for key in self.var:
            self.var[key][v] = self.var[key][u]
            self.reach[key][v] = self.reach[key][u]
        self.cycle[v] = self.cycle[u]
        self.shared[v] = self.shared[u]
        self.sm[v] = self.sm[u]
        self.n[(v,v)] = self.n[(u,u)]
        for w in self.indiv:
            self.n[(v,w)] = self.n[(u,w)]
            self.n[(w,v)] = self.n[(w,u)]
        self.indiv.append(v)
        return v

    # Summarize v into u
    def _v_embed(self, u, v):
        self.indiv.remove(v)
        for w in self.indiv:
            if self.n[(w,u)] != self.n[(w,v)]:
                self.n[(w,u)] = MAYBE
            if self.n[(u,w)] != self.n[(v,w)]:
                self.n[(u,w)] = MAYBE
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
        self.sm[u] = MAYBE


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
                self.var[var1][u1]._and(self.var[var2][u2])._and(self.n[(u1,u2)])
                )
            )

    def _var_reach(self, var1, var2):
        return self._exists(lambda u : self.var[var2][u]._and(self.reach[var1][u]))


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
            constr=cls.init_constr(symbols)
        )

    def coerce(self):

        self.update_n_plus()

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
        return True


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

        return shortcuts.And(*clauses)
