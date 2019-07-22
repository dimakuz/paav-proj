import urllib

import graphviz


def _node_label(node):
    return f'{node.name}\n{node.state}'


def _edge_color(edge):
    if edge.valid():
        return 'forestgreen'
    else:
        return 'red'

_URL_BASE = 'https://dreampuf.github.io/GraphvizOnline/#'

def dump_cfg(cfg):
    dot = graphviz.Digraph()
    for node in cfg.nodes.values():
        dot.node(node.name, label=_node_label(node))
        for edge in node.out_edges:
            dot.edge(
                tail_name=node.name,
                head_name=edge.successor.name,
                label=str(edge.statement),
                fontcolor=_edge_color(edge),
            )

    dot.node(cfg.head.name, shape='doublecircle')

    print(dot.source)
    print(f'{_URL_BASE}{urllib.parse.quote(dot.source, safe="")}')
