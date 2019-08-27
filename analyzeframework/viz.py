import subprocess
import urllib

import graphviz

from analyzeframework import tinyurl
from analyzeshape import structure


def _node_label(node):
    return f'{node.name} ({node.visits})\n{node.state}'


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
    print(
        tinyurl.shorten(
            f'{_URL_BASE}{urllib.parse.quote(dot.source, safe="")}',
        ),
    )


def _stnode_name(i, j):
    return f'{i},{j}'


def _stedge_style(val):
    if val == structure.ThreeValuedBool.MAYBE:
        return 'dashed'
    elif val == structure.ThreeValuedBool.TRUE:
        return 'solid'


def dump_shape(cfgnode):
    state = cfgnode.state
    dot = graphviz.Digraph()
    for i, st in enumerate(state.structures):
        with dot.subgraph(name=f'cluster_{i}') as c:
            c.attr(color='black')
            c.attr(label=f'Structure {i}')
            for sym, mapping in st.var.items():
                c.node(
                    _stnode_name(i, sym.name),
                    label=sym.name,
                    shape='box',
                )
                for node in st.indiv:
                    style = _stedge_style(mapping[node])
                    if style is None:
                        continue
                    c.edge(
                        head_name=_stnode_name(i, node),
                        tail_name=_stnode_name(i, sym.name),
                        style=style,
                    )
            for node in st.indiv:
                if st.sm[node] == structure.ThreeValuedBool.FALSE:
                    shape='circle'
                else:
                    shape='doublecircle'
                c.node(
                    _stnode_name(i, node),
                    label=str(node),
                    shape=shape,
                )
            for (f, t), val in st.n.items():
                style = _stedge_style(val)
                if style is None:
                    continue
                c.edge(
                    head_name=_stnode_name(i, t),
                    tail_name=_stnode_name(i, f),
                    label='n',
                    style=style,
                )
    print(
        cfgnode.name,
        tinyurl.shorten(
            f'{_URL_BASE}{urllib.parse.quote(dot.source, safe="")}',
        ),
    )
