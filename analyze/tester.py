import sys

from analyze import cfg
from analyze import parser
from analyze import viz


def main():
    lex = parser.Lexer()
    par = parser.Parser()
    with open(sys.argv[1]) as f:
        par.parse(lex.tokenize(f.read()))
    control = cfg.ControlFlowGraph(par.lines)
    viz.dump_cfg(control)

if __name__ == '__main__':
    main()
