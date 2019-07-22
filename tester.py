import argparse
import logging
import sys

from pysmt import shortcuts

from framework import chaotic
from framework import cfg
from analyzenumerical import lang
from analyzenumerical import sum
from analyzenumerical import parser
from analyzenumerical import parity
from framework import viz


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('path', help='Path to source')
    parser.add_argument(
        '--type',
        choices=['parity', 'sum'],
        required=True,
        help='Type of analysis to perform',
    )
    return parser.parse_args()


def main():
    opts = parse_args()
    logging.basicConfig(level=logging.DEBUG)
    lex = parser.Lexer()
    par = parser.Parser()
    with open(opts.path) as f:
        par.parse(lex.tokenize(f.read()))
    control = cfg.ControlFlowGraph(par.lines)

    if opts.type == 'parity':
        state = parity.ParityState
    elif opts.type == 'sum':
        state = sum.SumState

    for node in control.nodes.values():
        node.state = state.initial(par.vars)

    chaotic.chaotic_iteration(control)

    viz.dump_cfg(control)

if __name__ == '__main__':
    main()
