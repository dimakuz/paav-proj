import pytest

from analyzenumerical import parser
from analyzenumerical import parity

from tests import harness


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
                ('L32', 'L5', True),
                ('L42', 'L5', True),
                ('L5', 'L6', False),
                ('L5', 'L7', False),
            ),
        ),
        (
            'examples/parity/example6',
            (
                ('L32', 'L5', True),
                ('L42', 'L5', True),
                ('L5', 'L6', False),
                ('L5', 'L7', False),
            ),
        ),
        (
            'examples/parity/example7',
            (
                ('L3', 'L4', True),
                ('L5', 'L6', True),
            ),
        ),
        (
            'examples/parity/example8',
            (
                ('L4', 'L5', True),
                ('L8', 'L9', True),
            ),
        ),
    ),
)
def test_parity_analysis(input_path, asserts):
    harness.check_asserts(
        lexer=parser.Lexer(),
        parser=parser.Parser(),
        input=input_path,
        abstract_state=parity.ParityState,
        asserts=asserts,
    )
