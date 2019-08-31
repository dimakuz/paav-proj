import os
import subprocess
import urllib

import graphviz

from analyzeshape import structure
from analyzeshape import three_valued_logic


def _node_label(node):
    return f'{node.name} ({node.visits})\n{node.state}'


def _edge_color(edge):
    if edge.valid():
        return 'forestgreen'
    else:
        return 'red'


def create_cfg_dot(cfg):
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

    dot.node(
        cfg.head.name,
        label=f'Start node:\n{_node_label(cfg.head)}',
        fillcolor='green',
        style='filled'
    )
    return dot.source


def _stnode_name(i, j):
    return f'{i},{j}'


def _stedge_style(val):
    if val == three_valued_logic.MAYBE:
        return 'dashed'
    elif val == three_valued_logic.TRUE:
        return 'solid'


def create_shape_dot(cfgnode):
    state = cfgnode.state
    dot = graphviz.Digraph()
    dot.attr(label=f'Node {cfgnode.name}')
    dot.attr(labelloc='top')
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
                if st.sm[node] == three_valued_logic.FALSE:
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
    return dot.source

def output_png(src, path, title):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    subprocess.run(
        ('dot', '-Tpng', '-o', path),
        input=src,
        encoding='utf8',
    )
    print(f'{title}: file://{path}')
