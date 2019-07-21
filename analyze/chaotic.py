def chaotic_iteration(cfg):
    wl = [cfg.head]
    while wl:
        node = wl.pop(0)
        for edge in node.out_edges:
            next_node = edge.successor
            transformed_state = node.state.transform(edge.statement)
            joined_state = next_node.state.join(transformed_state)
            if joined_state != next_node.state:
                wl.append(next_node)
                next_node.state = joined_state
