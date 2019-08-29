import logging

LOG = logging.getLogger(__name__)


def chaotic_iteration(cfg):
    wl = [cfg.head]
    while wl:
        node = wl.pop(0)
        node.visits += 1

        LOG.debug('Pop node %r (visits: %d)', node.name, node.visits)
        for edge in node.out_edges:
            next_node = edge.successor
            LOG.debug('Next node is %r', next_node.name)
            LOG.debug('State before transform: %s', node.state)
            transformed_state = node.state.transform(edge.statement)
            LOG.debug('State after transform: %s', transformed_state)
            joined_state = next_node.state.join(transformed_state, next_node.arbitrary_term())
            joined_state.post_transform()
            if next_node.visits == 0 or joined_state != next_node.state:
                LOG.debug('State joined with %s', next_node.state)
                LOG.debug('State after join: %s', joined_state)
                wl.append(next_node)
                LOG.debug('Append node %r',next_node.name)
                next_node.state = joined_state
