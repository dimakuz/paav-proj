import pytest

from analyzeframework import chaotic
from analyzeframework import cfg
from analyzenumerical import lang
from analyzenumerical import parser
from analyzenumerical import parity


@pytest.mark.parametrize(
    ('input_path, asserts'),
    (
        ('examples/reference', ()),
        ('examples/parity/count-down',
         (('L7', 'L8', True),),
        ),
        ('examples/parity/reference', (('L6', 'L7', True),)),
        # ('examples/parity/reference-extra',
        #  (
        #     ('L6', 'L7', True),
        #     ('L7', 'L8', False),
        #     ('L8', 'L9', True),
        #  ),
        # ),
        ('examples/parity/reference-weird',
         (('L6', 'L7', False),
          ('L7', 'L8', True)),
        ),
        ('examples/parity/reference-extra', (('L6', 'L7', True),)),
        ('examples/parity/example1', (('L3', 'L4', True),)),
        ('examples/parity/example2', (('L3', 'L4', True),)),
        (
            'examples/parity/example3',
            (
                ('L4', 'L5', True),
                ('L5', 'L6', False),
                ('L4', 'L7', True),
                ('L7', 'L8', False),
            ),
        ),
        ('examples/parity/example4', (('L6', 'L7', True),)),
        (
            'examples/parity/example5',
            (
                ('L5', 'L6', False),
                ('L5', 'L7', False),
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
