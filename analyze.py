import argparse
import logging
import sys

from pysmt import shortcuts

from analyzeframework import chaotic
from analyzeframework import cfg
from analyzeframework import viz
from analyzenumerical import sum
from analyzenumerical import parser as num_parser
from analyzenumerical import parity
from analyzeshape import shape
from analyzeshape import parser as shape_parser


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('path', help='Path to source')
    parser.add_argument(
        '--type',
        choices=['parity', 'sum', 'shape'],
        required=True,
        help='Type of analysis to perform',
    )
    return parser.parse_args()


def main():
    opts = parse_args()
    logging.basicConfig(level=logging.DEBUG)

    if opts.type == 'parity':
        state = parity.ParityState
        lex = num_parser.Lexer()
        par = num_parser.Parser()
    elif opts.type == 'sum':
        state = sum.SumState
        lex = num_parser.Lexer()
        par = num_parser.Parser()
    elif opts.type == 'shape':
        state = shape.ShapeState
        lex = shape_parser.Lexer()
        par = shape_parser.Parser()

    with open(opts.path) as f:
        par.parse(lex.tokenize(f.read()))

    control = cfg.ControlFlowGraph(par.lines)
    for node in control.nodes.values():
        node.state = state.initial(par.vars)

    chaotic.chaotic_iteration(control)

    viz.dump_cfg(control)

if __name__ == '__main__':
    main()
