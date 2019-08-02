import copy
import dataclasses
import typing
import types

from pysmt import shortcuts
from analyzeshape import lang as lang_shape
from analyzeframework import lang
from enum import Enum


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

@dataclasses.dataclass
class Structure:
    indiv: typing.Set[int]
    var: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    reach: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    cycle: typing.Mapping[int, ThreeValuedBool]
    shared: typing.Mapping[int, ThreeValuedBool]
    sm: typing.Mapping[int, ThreeValuedBool]
    n: typing.Mapping[typing.Tuple[int, int], ThreeValuedBool]

    TYPE1_CONSTRAINTS_1VAR = typing.Mapping[types.FunctionType, types.FunctionType]
    TYPE1_CONSTRAINTS_2VAR = typing.Mapping[types.FunctionType, types.FunctionType]
    TYPE2_CONSTRAINTS_2VAR = typing.Set[types.FunctionType]

    def __init__(self):
        TYPE1_CONSTRAINTS_1VAR[lambda v: self._indv_shared(v)] = lambda v: self.shared[v]
        TYPE1_CONSTRAINTS_1VAR[lambda v: self._indv_shared(v)._not()] = lambda v: self.shared[v]._not()
        TYPE1_CONSTRAINTS_1VAR[lambda v: self._indv_cycle(v)] = lambda v: self.cycle[v]
        TYPE1_CONSTRAINTS_1VAR[lambda v: self._indv_cycle(v)._not()] = lambda v: self.cycle[v]._not()

        TYPE1_CONSTRAINTS_2VAR[lambda v1,v2: self._indv_not_n(v1,v2)] = lambda v1,v2: self.n[(v1,v2)]._not()
        TYPE1_CONSTRAINTS_2VAR[lambda v1,v2: self._indv_not_n_shared(v1,v2)] = lambda v1,v2: self.n[(v1,v2)]._not()

        TYPE2_CONSTRAINTS_2VAR.add(lambda v1,v2: self._indv_both_n(v1,v2))
        TYPE2_CONSTRAINTS_2VAR.add(lambda v1,v2: self._indv_both_n_shared(v1,v2))

        for var in self.var:
            TYPE1_CONSTRAINTS_1VAR[lambda v: self._indv_reach(var,v)] = lambda v: self.reach[var][v]
            TYPE1_CONSTRAINTS_1VAR[lambda v: self._indv_reach(var,v)._not()] = lambda v: self.reach[var][v]._not()
            TYPE1_CONSTRAINTS_1VAR[lambda v: self._indv_not_var(var,v)] = lambda v: self.var[var][v]._not()

            TYPE2_CONSTRAINTS_2VAR.add(lambda v1,v2: self._indv_both_var(var,v1,v2))


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
    def _indv_eq(self, v1, v2):
        if (v1 != v2):
            return FALSE
        else:
            return self.sm(v1)._not()

    # Is the individual heap shared
    def _indv_shared(self, v):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.n[(u1,v)]._and(self.n[(u2,v)])._and(self._indv_eq(u1,u2)._not())
                )
            )

    # Is the individual reachable from variable
    def _indv_reach(self, var, v):
        return self.var[var][v]._or(self._exists(lambda u : self.var[var][u]._and(self._n_plus()[(u,v)])))

    # Is the individual resides on a cycle
    def _indv_cycle(self, v):
        return self._n_plus()[(v,v)]

    def _indv_not_var(self, var, v):
        return self._exists(lambda u : self.var[var][u]._and(self._indv_eq(v, u)._not()))

    def _indv_not_n(self, v1, v2):
        return self._exists(lambda u : self.n[(v1,u)]._and(self._indv_eq(u, v2)._not()))

    def _indv_not_n_shared(self, v1, v2):
        return self._exists(lambda u : self.n[(u,v1)]._and(self._indv_eq(u, v2)._not())._and(self.shared[v1]._not()))

    def _indv_both_var(self, var, v1, v2):
        return self.var[var][v1]._and(self.var[var][v2])

    def _indv_both_n(self, v1, v2):
        return self._exists(lambda u : self.n[(u,v1)]._and(self.n[(u,v2)]))

    def _indv_both_n_shared(self, v1, v2):
        return self._exists(lambda u : self.n[(v1,u)]._and(self.n[(v2,u)])._and(self.shared[v]._not()))

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

    def initial(cls, symbols):
        return cls(
            indiv=set(),
            var={symbol: dict() for symbol in symbols},
            reach={symbol: dict() for symbol in symbols},
            cycle=dict(),
            shared=dict(),
            sm=dict(),
            n=dict()
        )
        
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
