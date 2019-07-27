import copy
import dataclasses
import typing

from pysmt import shortcuts
from analyzeshape import lang as lang_shape
from analyzeframework import lang


class ThreeValuedBool:
    val: float

    def __init__(self, val):
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def _not(self):
        return ThreeValuedBool(1 - val)

    def _and(self, other):
        return ThreeValuedBool(min(self.val, other.val))

    def _or(self, other):
        return ThreeValuedBool(max(self.val, other.val))


TRUE = ThreeValuedBool(1)
FALSE = ThreeValuedBool(0)
MAYBE = ThreeValuedBool(0.5)


@dataclasses.dataclass
class Structure:
    indiv: typing.Set[int]
    var: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    reach: typing.Mapping[lang.Symbol, typing.Mapping[int, ThreeValuedBool]]
    cycle: typing.Mapping[int, ThreeValuedBool]
    shared: typing.Mapping[int, ThreeValuedBool]
    sm: typing.Mapping[int, ThreeValuedBool]
    n: typing.Mapping[typing.Tuple[int, int], ThreeValuedBool]

    def _summarizable(self, u, v):
        return all(self.var[key][u] == self.var[key][v] and \
                    self.reach[key][u] == self.reach[key][v] for key in self.var) and \
                    self.cycle[u] == self.cycle[v] and \
                    self.shared[u] == self.shared[v]

    def _summarize(self, u, v):
        if sm[u] == MAYBE:
            self._merge_left_into_right(v, u)
        else:
            self._merge_left_into_right(u, v)

    def _merge_left_into_right(self, u, v):
        for w in self.indiv:
            if self.n[(w,v)] != self.n[(w,u)]:
                self.n[(w,v)] = MAYBE
            if self.n[(v,w)] != self.n[(u,w)]:
                self.n[(v,w)] = MAYBE
        self.indiv.remove(u)
        for key in self.var:
            self.var[key].pop(u)
            self.reach[key].pop(u)
        self.cycle.pop(u)
        self.shared.pop(u)
        self.sm.pop(u)
        for w in self.indiv:
            self.n.pop((u,w))
            self.n.pop((w,u))
        self.n.pop((u,u))
        self.sm[v] = MAYBE

    # Equality taking summary nodes into account
    def _indiv_eq(self, u, v):
        if (u != v):
            return FALSE
        else:
            return self.sm(u)._not()

    # Is the individual heap shared
    def _is_shared(self, v):
        return self._exists(lambda u1 : \
            self._exists(lambda u2 : \
                self.n[(u1,v)]._and(self.n[(u2,v)])._and(self._indiv_eq(u1,u2)._not())
                )
            )

    # Is the individual reachable from variable
    def _is_reachable(self, var, v):
        return self.var[var][v]._or(self._exists(lambda v1 : self.var[var][v1]._and(self.n_plus[(v1,v)])))

    # Transitive closure of n
    def _n_plus(self):
        n_plus = self.n.copy()
        for u in indiv:
            for v,w in indiv:
                n_plus[(v,w)] = n_plus[(v,w)]._or(n_plus[(v,u)]._and(n_plus[(u,w)]))
        return n_plus

    def _exists(self, pred):
        return ThreeValuedBool(max(pred(v).val for v in self.indiv))

    def _forall(self, pred):
        return ThreeValuedBool(min(pred(v).val for v in self.indiv))

    def __str__(self):
        
        # TODO

        return ''

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

            is_null = any(self.var[var1][v] != FALSE for v in self.indiv)
            clauses.append(
                shortcuts.Iff(
                    lang_shape.EqualsVarNull(var1).formula(),
                    shortcuts.Bool(is_null)
                ),
            )

            for var2 in self.var:

                is_eq = all(self.var[var1][v] == self.var[var2][v] for v in self.indiv)
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.EqualsVarVar(var1, var2).formula(),
                        shortcuts.Bool(is_eq)
                    ),
                )

                is_eq_next = self._exists(lambda v1 : \
                    self._exists(lambda v2: \
                        self.var[var1][v1]._and(self.var[var2][v2])._and(self.n[(v1,v2)])
                        )
                    )
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.EqualsVarNext(var1, var2).formula(),
                        shortcuts.Bool(is_eq_next)
                    ),
                )

                is_reachable = self._exists(lambda v2 : self.var[var2][v2]._and(self.reach[var1][v2]))
                clauses.append(
                    shortcuts.Iff(
                        lang_shape.Ls(var1, var2).formula(),
                        shortcuts.Bool(is_reachable)
                    ),
                )

        return shortcuts.And(*clauses)