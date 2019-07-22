import logging

LOG = logging.getLogger(__name__)


def chaotic_iteration(cfg):
    wl = [cfg.head]
    while wl:
        node = wl.pop(0)
        LOG.debug('pop node %r', node.name)
        for edge in node.out_edges:
            next_node = edge.successor
            transformed_state = node.state.transform(edge.statement)
            joined_state = next_node.state.join(transformed_state)
            if joined_state != next_node.state:
                wl.append(next_node)
                LOG.debug(
                    'append node %r',
                    next_node.name,
                )
                next_node.state = joined_state
