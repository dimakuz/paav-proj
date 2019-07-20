import graphviz

def dump_cfg(cfg):
    dot = graphviz.Digraph(comment='CFG')
    for node in cfg.nodes.values():
        dot.node(node.name)
        for edge in node.out_edges:
            dot.edge(
                tail_name=node.name,
                head_name=edge.successor.name,
                label=str(edge.statement),
            )

    dot.node(cfg.head.name, shape='doublecircle')

    print(dot.source)
