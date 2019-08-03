import copy
import dataclasses
import typing
import logging
import types
import copy

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

        return ThreeValuedBool(2 - self)

    def _and(self, other):
        return ThreeValuedBool(min(self, other))

    def _or(self, other):
        return ThreeValuedBool(max(self, other))

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
    indiv: typing.Set[int]
    var: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    reach: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    cycle: typing.Mapping[int, ThreeValuedBool]
    shared: typing.Mapping[int, ThreeValuedBool]
    sm: typing.Mapping[int, ThreeValuedBool]
    n: typing.Mapping[typing.Tuple[int, int], ThreeValuedBool]

    constr: typing.Set[typing.Tuple[int, callable, callable, callable]]


    @classmethod
    def init_constr(cls, symbols):

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
        def fix_reach(st,var,v):
            st.reach[var][v] = TRUE
        def fix_reach_not(st,var,v):
            st.reach[var][v] = FALSE
        def fix_var_not(st,var,v):
            st.var[var][v] = FALSE
        def fix_sm_not(st,v):
            st.sm[v] = FALSE

        constr = set()

        constr.add((1, lambda st,v: st._v_shared(v),             lambda st,v: st.shared[v],              fix_shared))
        constr.add((1, lambda st,v: st._v_shared(v)._not(),      lambda st,v: st.shared[v]._not(),       fix_shared_not))
        constr.add((1, lambda st,v: st._v_cycle(v),              lambda st,v: st.cycle[v],               fix_cycle))
        constr.add((1, lambda st,v: st._v_cycle(v)._not(),       lambda st,v: st.cycle[v]._not(),        fix_cycle_not))

        constr.add((2, lambda st,v1,v2: st._v_not_n(v1,v2),      lambda st,v1,v2: st.n[(v1,v2)]._not(),  fix_n_not))
        constr.add((2, lambda st,v1,v2: st._v_not_n_hs(v1,v2),   lambda st,v1,v2: st.n[(v1,v2)]._not(),  fix_n_not))

        constr.add((1, lambda st,v: st._v_n(v),                  lambda st,v: st.sm[v]._not(),            fix_sm_not))
        constr.add((1, lambda st,v: st._v_n_hs(v),               lambda st,v: st.sm[v]._not(),            fix_sm_not))

        for var in symbols: 
            constr.add((1, lambda st,v: st._v_reach(var,v),          lambda st,v: st.reach[var][v],         fix_reach))
            constr.add((1, lambda st,v: st._v_reach(var,v)._not(),   lambda st,v: st.reach[var][v]._not(),  fix_reach_not))
            constr.add((1, lambda st,v: st._v_not_var(var,v),        lambda st,v: st.var[var][v]._not(),    fix_var_not))

            constr.add((1, lambda st,v: st.var[var][v],          lambda st,v: st.sm[v]._not(),            fix_sm_not))

        return constr


    def __str__(self):
        lines = []
        for symbol in self.var:
            var = ', '.join(f'v{v} = {str(self.var[symbol][v])}' for v in self.indiv)
            lines.append(f'var_{symbol.name}: [{var}]')

            reach = ', '.join(f'v{v} = {str(self.reach[symbol][v])}' for v in self.indiv)
            lines.append(f'reach_{symbol.name}: [{reach}]')

        cycle = ', '.join(f'v{v} = {str(self.cycle[v])}' for v in self.indiv)
        lines.append(f'cycle: [{cycle}]')

        shared = ', '.join(f'v{v} = {str(self.shared[v])}' for v in self.indiv)
        lines.append(f'shared: [{shared}]')

        sm = ', '.join(f'v{v} = {str(self.sm[v])}' for v in self.indiv)
        lines.append(f'sm: [{sm}]')

        return '\n'.join(lines)


    def summarizable(self, u, v):
        return all(self.var[key][u] == self.var[key][v] and \
                    self.reach[key][u] == self.reach[key][v] for key in self.var) and \
                    self.cycle[u] == self.cycle[v] and \
                    self.shared[u] == self.shared[v]

    def copy_indiv(self, u):
        v = max(self.indiv) + 1
        for key in self.var:
            self.var[key][v] = self.var[key][u]
            self.reach[key][v] = self.var[key][u]
        self.cycle[v] = self.cycle[u]
        self.shared[v] = self.shared[u]
        self.sm[v] = self.sm[u]
        self.n[(v,v)] = self.n[(u,u)]
        for w in self.indiv:
            self.n[(v,w)] = self.n[(u,w)]
            self.n[(w,v)] = self.n[(w,u)]
        self.indiv.add(v)
        return v

    def summarize(self, u, v):
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
        return self.var[var][v]._or(self._exists(lambda u : self.var[var][u]._and(self._n_plus()[(u,v)])))

    # Is the individual resides on a cycle
    def _v_cycle(self, v):
        return self._n_plus()[(v,v)]

    def _v_not_var(self, var, v):
        return self._exists(lambda u : self.var[var][u]._and(self._v_eq(v, u)._not()))

    def _v_not_n(self, v1, v2):
        return self._exists(lambda u : self.n[(v1,u)]._and(self._v_eq(u, v2)._not()))

    def _v_not_n_hs(self, v1, v2):
        return self._exists(lambda u : self.n[(u,v1)]._and(self._v_eq(u, v2)._not())._and(self.shared[v1]._not()))

    def _v_n(self, v):
        return self._exists(lambda u : self.n[(u,v)])

    def _v_n_hs(self, v):
        return self._exists(lambda u : self.n[(v,u)]._and(self.shared[u]._not()))

    def _var_not_null(self, var1):
        return self._exists(lambda u : self.var[var1][u])

    def _var_eq(self, var1, var2):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.var[var1][u1]._and(self.var[var1][u2])._and(self._v_eq(u1, u2))))

    def _var_next_eq(self, var1, var2):
        return self._exists(lambda u1 : \
            self._exists(lambda u2: \
                self.var[var1][u1]._and(self.var[var2][u2])._and(self.n[(u1,u2)])
                )
            )

    def _var_reach(self, var1, var2):
        return self._exists(lambda u : self.var[var2][u]._and(self.reach[var1][u]))


    # Transitive closure of n
    def _n_plus(self):
        n_plus = copy.deepcopy(self.n)
        for u in self.indiv:
            for v in self.indiv:
                for w in self.indiv:
                    n_plus[(v,w)] = n_plus[(v,w)]._or(n_plus[(v,u)]._and(n_plus[(u,w)]))
        return n_plus

    def _exists(self, pred):
        return ThreeValuedBool(max(pred(v) for v in self.indiv)) if self.indiv else FALSE

    def _forall(self, pred):
        return ThreeValuedBool(min(pred(v) for v in self.indiv)) if self.indiv else TRUE


    @classmethod
    def initial(cls, symbols):
        return cls(
            indiv=set(),
            var={symbol: dict() for symbol in symbols},
            reach={symbol: dict() for symbol in symbols},
            cycle=dict(),
            shared=dict(),
            sm=dict(),
            n=dict(),
            constr=cls.init_constr(symbols)
        )

    def coerce(self):
        return True

        # changed = True
        # while changed:
        #     changed = False
        #     for constraint in self.constr:
        #         (par_num, lh, rh, fix) = constraint
        #         if par_num == 1:
        #             for v in self.indiv:
        #                 if lh(self,v) == TRUE:
        #                     if rh(self,v) == FALSE:
        #                         return False
        #                     elif rh(self,v) == MAYBE:
        #                         fix(self,v)
        #                         changed = True
        #         elif par_num == 2:
        #             for v1 in self.indiv:
        #                 for v2 in self.indiv:
        #                     if lh(self,v1,v2) == TRUE:
        #                         if rh(self,v1,v2) == FALSE:
        #                             return False
        #                         elif rh(self,v1,v2) == MAYBE:
        #                             fix(self,v1,v2)
        #                             changed = True
        # return True


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
