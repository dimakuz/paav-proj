import sys

from analyze import cfg
from analyze import lang
from analyze import parser
from analyze import parity
from analyze import viz


def main():
    lex = parser.Lexer()
    par = parser.Parser()
    with open(sys.argv[1]) as f:
        par.parse(lex.tokenize(f.read()))
    control = cfg.ControlFlowGraph(par.lines)
    viz.dump_cfg(control)

    p = parity.ParityAbstractDomain(par.vars)
    ps1 = p.initial_state()
    ps2 = p.initial_state()
    ps2.symbols[lang.Symbol('i')] = parity.Parity.ODD
    print(ps1)
    print(ps2)
    print(ps1.join(ps2))
    ps1.symbols[lang.Symbol('j')] = parity.Parity.ODD
    print(ps1.join(ps2))
    ps1.symbols[lang.Symbol('i')] = parity.Parity.EVEN
    print(ps1.join(ps2))

    print('=============')
    print('Initial')
    ps = p.initial_state()
    print(ps)
    print(f'Execute {control.head.out_edges[0].statement}:')
    ps = ps.transform(control.head.out_edges[0].statement)
    print(ps)
    print(f'Execute {control.head.out_edges[0].successor.out_edges[0].statement}:')
    ps = ps.transform(control.head.out_edges[0].successor.out_edges[0].statement)
    print(ps)


if __name__ == '__main__':
    main()
