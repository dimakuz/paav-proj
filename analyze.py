import argparse
import logging
import os
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
    parser.add_argument(
        '--debug',
        action='store_true',
        help='Show debug logs',
    )
    parser.add_argument(
        '--no-debug',
        dest='debug',
        action='store_false',
        help='Do not show debug logs',
    )
    parser.add_argument(
        '--output-dir',
        type=os.path.abspath,
        required=False,
        help='If specified, analysis products will be placed in this directory',
    )
    parser.set_defaults(debug=True, url=True)  # FIXME reverse later
    return parser.parse_args()


def main():
    opts = parse_args()
    if opts.debug:
        loglevel = logging.DEBUG
    else:
        loglevel = logging.WARNING
    logging.basicConfig(level=loglevel)
    logging.getLogger("urllib3").setLevel(logging.WARNING)


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

    control.head.state.initialize_head(par.vars)

    chaotic.chaotic_iteration(control)

    cfg_src = viz.create_cfg_dot(control)
    if opts.output_dir is not None:
        viz.output_png(
            cfg_src,
            f'{opts.output_dir}/cfg.png',
            title='Control flow graph',
        )
    else:
        print('Control flow graph:')
        print(cfg_src)

    if opts.type == 'shape':
        for node in control.nodes.values():
            node_src = viz.create_shape_dot(node)
            if opts.output_dir is not None:
                viz.output_png(
                    node_src,
                    f'{opts.output_dir}/{node.name}.png',
                    title=f'Node {node.name} structures',
                )
                with open(f'{opts.output_dir}/{node.name}.txt', 'w') as f:
                    f.write(node.state.full_str())
                print(
                    f'Node {node.name} state: '
                    f'file://{opts.output_dir}/{node.name}.txt'
                )
            else:
                print(f'Node {node.name}')
                print(node_src)
                print('==========================================')


if __name__ == '__main__':
    main()
