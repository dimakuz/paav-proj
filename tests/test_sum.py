import pytest

from analyzenumerical import parser
from analyzenumerical import sum

from tests import harness


@pytest.mark.parametrize(
    ('input_path, asserts'),
    (
        ('examples/reference', ()),
        ('examples/sum/reference', (('L6', 'L7', True),)),
        ('examples/sum/example1', (('L5', 'L6', True),)),
        ('examples/sum/example2', (('L5', 'L6', True),)),
        ('examples/sum/example3', (('L11', 'L12', True),)),
        ('examples/sum/example4', (('L7', 'L8', True),)),
        (
            'examples/sum/example5',
            (
                ('L11', 'L30', True),
                ('L21', 'L30', True),
                ('L30', 'L31', True),
            ),
        ),
    ),
)
def test_sum_analysis(input_path, asserts):
    harness.check_asserts(
        lexer=parser.Lexer(),
        parser=parser.Parser(),
        input=input_path,
        abstract_state=sum.SumState,
        asserts=asserts,
    )
