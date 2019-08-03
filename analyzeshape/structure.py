import copy
import dataclasses
import typing
import logging
import types

from pysmt import shortcuts
from analyzeshape import lang as lang_shape
from analyzeframework import lang
from enum import Enum

LOG = logging.getLogger(__name__)


class ThreeValuedBool(Enum):
    TRUE = 1
    MAYBE = 0.5
    FALSE = 0

    def _not(self):
        return ThreeValuedBool(1 - self)

    def _and(self, other):
        return ThreeValuedBool(min(self, other))

    def _or(self, other):
        return ThreeValuedBool(max(self, other))


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


    def init_constr(self, symbols):

        constr = set()
        def fix_shared(v):
            self.shared[v] = TRUE
        def fix_shared_not(v):
            self.shared[v] = FALSE
        def fix_cycle(v):
            self.cycle[v] = TRUE
        def fix_cycle_not(v):
            self.cycle[v] = FALSE
        def fix_n_not(v1,v2):
            self.n[(v1,v2)] = FALSE
        def fix_reach(var,v):
            self.reach[var][v] = TRUE
        def fix_reach_not(var,v):
            self.reach[var][v] = FALSE
        def fix_var_not(var,v):
            self.var[var][v] = FALSE
        def fix_sm_not(v):
            self.sm[v] = FALSE

        constr.add((1, lambda v: self._v_shared(v),             lambda v: self.shared[v],              fix_shared))
        constr.add((1, lambda v: self._v_shared(v)._not(),      lambda v: self.shared[v]._not(),       fix_shared_not))
        constr.add((1, lambda v: self._v_cycle(v),              lambda v: self.cycle[v],               fix_cycle))
        constr.add((1, lambda v: self._v_cycle(v)._not(),       lambda v: self.cycle[v]._not(),        fix_cycle_not))

        constr.add((2, lambda v1,v2: self._v_not_n(v1,v2),      lambda v1,v2: self.n[(v1,v2)]._not(),  fix_n_not))
        constr.add((2, lambda v1,v2: self._v_not_n_hs(v1,v2),   lambda v1,v2: self.n[(v1,v2)]._not(),  fix_n_not))

        constr.add((1, lambda v: self._v_n(v),                  lambda v: self.sm[v]._not(),            fix_sm_not))
        constr.add((1, lambda v: self._v_n_hs(v),               lambda v: self.sm[v]._not(),            fix_sm_not))

        for var in symbols: 
            constr.add((1, lambda v: self._v_reach(var,v),          lambda v: self.reach[var][v],         fix_reach))
            constr.add((1, lambda v: self._v_reach(var,v)._not(),   lambda v: self.reach[var][v]._not(),  fix_reach_not))
            constr.add((1, lambda v: self._v_not_var(var,v),        lambda v: self.var[var][v]._not(),    fix_var_not))

            constr.add((1, lambda v: self.var[var][v],          lambda v: self.sm[v]._not(),            fix_sm_not))

        return constr


    def __str__(self):
        lines = []
        for symbol in self.var:
            var = ','.join(f'indiv-{v} = {self.var[symbol][v]}' for v in self.indiv)
            lines.append(f'var_{symbol.name}: [{var}]')

            reach = ','.join(f'indiv-{v} = {self.reach[symbol][v]}' for v in self.indiv)
            lines.append(f'reach_{symbol.name}: [{reach}]')

        cycle = ','.join(f'indiv-{v} = {self.cycle[v]}' for v in self.indiv)
        lines.append(f'cycle: [{cycle}]')

        shared = ','.join(f'indiv-{v} = {self.shared[v]}' for v in self.indiv)
        lines.append(f'cycle: [{shared}]')

        sm = ','.join(f'indiv-{v} = {self.sm[v]}' for v in self.indiv)
        lines.append(f'cycle: [{sm}]')

        return '\n'.join(lines)


    def _summarizable(self, u, v):
        return all(self.var[key][u] == self.var[key][v] and \
                    self.reach[key][u] == self.reach[key][v] for key in self.var) and \
                    self.cycle[u] == self.cycle[v] and \
                    self.shared[u] == self.shared[v]

    def _copy(self, u):
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

    def _summarize(self, u, v):
        self.indiv.pop(v)
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
            return self.sm(v1)._not()

    # Is the individual heap shared
    def _v_shared(self, v):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.n[(u1,v)]._and(self.n[(u2,v)])._and(self._indv_eq(u1,u2)._not())
                )
            )

    # Is the individual reachable from variable
    def _v_reach(self, var, v):
        LOG.debug('type var %s', type(var))
        LOG.debug('type v %s', type(v))
        return self.var[var][v]._or(self._exists(lambda u : self.var[var][u]._and(self._n_plus()[(u,v)])))

    # Is the individual resides on a cycle
    def _v_cycle(self, v):
        return self._n_plus()[(v,v)]

    def _v_not_var(self, var, v):
        return self._exists(lambda u : self.var[var][u]._and(self._indv_eq(v, u)._not()))

    def _v_not_n(self, v1, v2):
        return self._exists(lambda u : self.n[(v1,u)]._and(self._indv_eq(u, v2)._not()))

    def _v_not_n_hs(self, v1, v2):
        return self._exists(lambda u : self.n[(u,v1)]._and(self._indv_eq(u, v2)._not())._and(self.shared[v1]._not()))

    def _v_n(self, v):
        return self._exists(lambda u : self.n[(u,v)])

    def _v_n_hs(self, v):
        return self._exists(lambda u : self.n[(v,u)]._and(self.shared[u]._not()))

    def _var_not_null(self, var1):
        return self._exists(lambda u : self.var[var1][u])

    def _var_eq(self, var1, var2):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.var[var1][u1]._and(self.var[var1][u2])._and(self._indv_eq(u1, u2))))

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
        n_plus = self.n.deepcopy()
        for u in indiv:
            for v,w in indiv:
                n_plus[(v,w)] = n_plus[(v,w)]._or(n_plus[(v,u)]._and(n_plus[(u,w)]))
        return n_plus

    def _exists(self, pred):
        return ThreeValuedBool(max(pred(v).val for v in self.indiv))

    def _forall(self, pred):
        return ThreeValuedBool(min(pred(v).val for v in self.indiv))


    def __init__(self, symbols):
        LOG.debug('initializing structure!!')
        self.indiv = set()
        self.var = {symbol: dict() for symbol in symbols}
        self.reach = {symbol: dict() for symbol in symbols}
        self.cycle = dict()
        self.shared = dict()
        self.sm = dict()
        self.n = dict()
        self.constr = self.init_constr(symbols)
        
    def reset(self):
        indiv.clear()
        cycle.clear()
        shared.clear()
        sm.clear()
        n.clear()
        for key in self.var:
            self.var[key].clear()
            self.reach[key].clear()

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
