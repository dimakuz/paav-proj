import logging

LOG = logging.getLogger(__name__)


def chaotic_iteration(cfg):
    wl = [cfg.head]
    while wl:
        node = wl.pop(0)
        node.visits += 1

        LOG.debug('pop node %r (visits: %d)', node.name, node.visits)
        for edge in node.out_edges:
            next_node = edge.successor
            transformed_state = node.state.transform(edge.statement)
            joined_state = next_node.state.join(transformed_state, next_node.arbitrary_visits())
            if next_node.visits == 0 or joined_state != next_node.state:
                wl.append(next_node)
                LOG.debug('append node %r',next_node.name)
                next_node.state = joined_state
