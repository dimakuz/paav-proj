import pytest

import sys
print(sys.path)

from analyze import chaotic
from analyze import cfg
from analyze import lang
from analyze import parser
from analyze import parity
from analyze import sum


@pytest.mark.parametrize(
    ('input_path, asserts'),
    (
        ('examples/reference', ()),
        ('examples/parity/reference', (('L6', 'L7', True),)),
        ('examples/parity/reference-extra',
         (
            ('L6', 'L7', True),
            ('L7', 'L8', False),
            ('L8', 'L9', True),
         ),
        ),
    ),
)
def test_parity_analysis(input_path, asserts):
    lex = parser.Lexer()
    par = parser.Parser()
    with open(input_path) as f:
        par.parse(lex.tokenize(f.read()))
    control = cfg.ControlFlowGraph(par.lines)
    state = parity.ParityState

    for node in control.nodes.values():
        node.state = state.initial(par.vars)

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