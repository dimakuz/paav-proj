import pytest

from analyzeframework import chaotic
from analyzeframework import cfg
from analyzenumerical import lang
from analyzenumerical import parser
from analyzenumerical import sum


@pytest.mark.parametrize(
    ('input_path, asserts'),
    (
        ('examples/reference', ()),
        ('examples/sum/reference', (('L6', 'L7', True),)),
        ('examples/parity/reference-extra',
         (
         ),
        ),
        ('examples/sum/example1', (('L5', 'L6', True),)),
        ('examples/sum/example2', (('L5', 'L6', True),)),
        ('examples/sum/example3', (('L11', 'L12', True),)),
        ('examples/sum/example4', (('L7', 'L8', True),)),
    ),
)
def test_sum_analysis(input_path, asserts):
    lex = parser.Lexer()
    par = parser.Parser()
    with open(input_path) as f:
        par.parse(lex.tokenize(f.read()))
    control = cfg.ControlFlowGraph(par.lines)
    state = sum.SumState

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
