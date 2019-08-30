from analyzeframework import chaotic
from analyzeframework import cfg
from analyzeframework import lang


def check_asserts(lexer, parser, input, abstract_state, asserts):
    with open(input) as f:
        parser.parse(lexer.tokenize(f.read()))
    control = cfg.ControlFlowGraph(parser.lines)

    for node in control.nodes.values():
        node.state = abstract_state.initial(parser.vars)

    chaotic.chaotic_iteration(control)

    for entry in asserts:
        src, dst, valid = entry
        edge = next(
            e for e in control.nodes[src].out_edges if e.successor.name == dst
        )
        assert type(edge.statement) is lang.Assert, (
            f'{src}->{dst} edge is not an assert: {edge.statement}'
        )
        assert edge.valid() == valid, (
            f'{src}->{dst} "{edge.statement}" does '
            f'not match expected value {valid}'
        )
