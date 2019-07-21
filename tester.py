import logging
import sys

from pysmt import shortcuts

from framework import chaotic
from framework import cfg
from analyzenumerical import lang
from analyzenumerical import parser
from analyzenumerical import parity
from framework import viz



def main():
    logging.basicConfig(level=logging.DEBUG)
    lex = parser.Lexer()
    par = parser.Parser()
    with open(sys.argv[1]) as f:
        par.parse(lex.tokenize(f.read()))
    control = cfg.ControlFlowGraph(par.lines)

    for node in control.nodes.values():
        node.state = parity.ParityState.initial(par.vars)

    chaotic.chaotic_iteration(control)

    viz.dump_cfg(control)

if __name__ == '__main__':
    main()
