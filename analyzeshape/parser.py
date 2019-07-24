import sly

from analyzeshape import lang as lang_shape
from analyzeframework import lang

class Lexer(sly.Lexer):
    tokens = {NAME, LABEL, ASSIGN, EQUAL, NOTEQUAL, NULL, NEXT,
              ASSUME, SKIP, ASSERT, LPAREN, RPAREN, TRUE, FALSE, 
              ODD, EVEN, LEN, LS}
    ignore = '\t '

    ASSUME = r'assume'
    SKIP = r'skip'
    ASSERT = r'assert'
    TRUE = 'TRUE'
    FALSE = 'FALSE'
    ODD = 'ODD'
    EVEN = 'EVEN'
    LEN = 'LEN'
    LS = 'LS'
    NULL = 'NULL'
    NEW = 'new'
    LABEL = r'L\d+'
    NAME = r'[a-zA-Z_][a-zA-Z0-9_]*'
    NEXT = r'[a-zA-Z_][a-zA-Z0-9_]*\.n'
    ASSIGN = r':='
    EQUAL = r'='
    NOTEQUAL = r'!='
    LPAREN = r'\('
    RPAREN = r'\)'

    ignore_newline = r'\n+'
    def ignore_newline(self, t):
        self.lineno += t.value.count('\n')

    def error(self, t):
        print(f'Illegal character "{t}"')
        self.index += 1


class Parser(sly.Parser):
    tokens = Lexer.tokens

    def __init__(self):
        self.vars = set()
        self.statements = []

    @_('vars lines')
    def program(self, p):
        self.vars = p.vars
        self.lines = p.lines

    @_('sym vars')
    def vars(self, p):
        return [p.sym] + p.vars

    @_('sym')
    def vars(self, p):
        return [p.sym]

    @_('line')
    def lines(self, p):
        return [p.line]

    @_('line lines')
    def lines(self, p):
        return [p.line] + p.lines

    @_('LABEL stmt LABEL')
    def line(self, p):
        return lang.ProgramLine(
            source=p.LABEL0,
            statement=p.stmt,
            destination=p.LABEL1,
        )

    @_('SKIP')
    def stmt(self, p):
        return lang.Skip()

    @_('NAME')
    def sym(self, p):
        return lang.Symbol(p.NAME)

    @_('NEXT')
    def sym(self, p):
        return lang_shape.SymbolNext(p.NEXT)

    @_('sym ASSIGN sym')
    def stmt(self, p):
        return lang_shape.VarVarAssignment(p.sym0, p.sym1)

    @_('sym ASSIGN next')
    def stmt(self, p):
        return lang_shape.VarNextAssignment(p.sym, p.next)

    @_('next ASSIGN sym')
    def stmt(self, p):
        return lang_shape.NextVarAssignment(p.next, p.sym)

    @_('sym ASSIGN NEW')
    def stmt(self, p):
        return lang_shape.NewAssignment(p.sym)

    @_('sym ASSIGN NULL')
    def stmt(self, p):
        return lang_shape.VarNullAssignment(p.sym)

    @_('next ASSIGN NULL')
    def stmt(self, p):
        return lang_shape.NextNullAssignment(p.next)

    @_('ASSUME LPAREN expr RPAREN')
    def stmt(self, p):
        return lang.Assume(p.expr)

    @_('sym EQUAL sym')
    def expr(self, p):
        return lang_shape.EqualsVarVar(p.sym0, p.sym1)

    @_('sym EQUAL next')
    def expr(self, p):
        return lang_shape.EqualsVarNext(p.sym0, p.sym1next)

    @_('sym NOTEQUAL sym')
    def expr(self, p):
        return lang_shape.NotEqualsVarVar(p.sym0, p.sym1)

    @_('sym NOTEQUAL sym')
    def expr(self, p):
        return lang_shape.NotEqualsVarNext(p.sym0, p.sym1next)

    @_('TRUE')
    def expr(self, p):
        return lang.Truth()

    @_('FALSE')
    def expr(self, p):
        return lang.Falsehood()

    @_('ASSERT orc')
    def stmt(self, p):
        return lang.Assert(p.orc)

    @_('LPAREN andc RPAREN')
    def orc(self, p):
        return [p.andc]

    @_('LPAREN andc RPAREN orc')
    def orc(self, p):
        return [p.andc] + p.orc

    @_('pred')
    def andc(self, p):
        return [p.pred]

    @_('pred andc')
    def andc(self, p):
        return [p.pred] + p.andc

    @_('LS sym sym')
    def ls(self, p):
        return lang.Ls(p.sym0, p.sym1)

    @_('LEN sym sym EQUAL LEN sym sym')
    def len(self, p):
        return lang.Len(p.sym0, p.sym1, p.sym2, p.sym3)

    @_('EVEN sym sym')
    def even(self, p):
        return lang_shape.Even(p.sym0, p.sym1)

    @_('ODD sym sym')
    def odd(self, p):
        return lang_shape.Odd(p.sym0, p.sym1)
