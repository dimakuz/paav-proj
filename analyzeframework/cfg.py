import dataclasses
import typing

from pysmt import shortcuts

from analyzeframework import lang


@dataclasses.dataclass
class Edge:
    statement: lang.Statement
    predecessor: 'Node'
    successor: 'Node'

    def valid(self):
        if not isinstance(self.statement, lang.Assert):
            return True

        formula = shortcuts.And(
            self.predecessor.state.formula(),
            shortcuts.Not(
                self.statement.formula(),
            ),
        )
        cex = shortcuts.get_model(formula)
        return cex is None


@dataclasses.dataclass
class Node:
    name: str
    out_edges: typing.List[Edge] = dataclasses.field(default_factory=list)
    in_edges: typing.List[Edge] = dataclasses.field(default_factory=list)
    state: object = None
    visits: int = 0


class ControlFlowGraph:
    def __init__(self, lines):
        self.nodes = {}
        for line in lines:
            source_node = self._get_node(line.source)
            dest_node = self._get_node(line.destination)
            edge = Edge(
                line.statement,
                source_node,
                dest_node,
            )
            source_node.out_edges.append(edge)
            dest_node.in_edges.append(edge)
        self.head = next(n for n in self.nodes.values() if len(n.in_edges) == 0)

    def _get_node(self, key):
        return self.nodes.setdefault(key, Node(key))
