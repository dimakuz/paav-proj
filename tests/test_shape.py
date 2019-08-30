import pytest

from analyzeshape import parser
from analyzeshape import shape

from tests import harness


@pytest.mark.parametrize(
    ('input_path, asserts'),
    (
        (
            'examples/shape/list',
            (
            ),
        ),
        (
            'examples/shape/parity-bad',
            (
                ('L40', 'L41', True),
            ),
        ),
        (
            'examples/shape/reference',
            (
                ('L44', 'L45', True),
                ('L45', 'L46', True),
                ('L46', 'L47', True),
            ),
        ),
    ),
)
def test_shape_analysis(input_path, asserts):
    harness.check_asserts(
        lexer=parser.Lexer(),
        parser=parser.Parser(),
        input=input_path,
        abstract_state=shape.ShapeState,
        asserts=asserts,
    )
