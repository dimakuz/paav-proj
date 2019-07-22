import sly

from analyzenumerical import lang as lang_num
from analyzeframework import lang

class Lexer(sly.Lexer):
    tokens = {NAME, NUMBER, LABEL, PLUS, MINUS, ASSIGN, EQUAL, NOTEQUAL,
              ASSUME, SKIP, ASSERT, QMARK, LPAREN, RPAREN, TRUE, FALSE, ODD,
              EVEN, SUM}
    ignore = '\t '

    ASSUME = r'assume'
    SKIP = r'skip'
    ASSERT = r'assert'
    TRUE = 'TRUE'
    FALSE = 'FALSE'
    ODD = 'ODD'
    EVEN = 'EVEN'
    SUM = 'SUM'
    LABEL = r'L\d+'
    NAME = r'[a-zA-Z_][a-zA-Z0-9_]*'
    PLUS = r'\+'
    MINUS = r'-'
    ASSIGN = r':='
    EQUAL = r'='
    NOTEQUAL = r'!='
    QMARK = r'\?'
    LPAREN = r'\('
    RPAREN = r'\)'

    ignore_newline = r'\n+'
    def ignore_newline(self, t):
        self.lineno += t.value.count('\n')

    def error(self, t):
        print(f'Illegal character "{t}"')
        self.index += 1

    @_(r'\d+')
    def NUMBER(self, t):
        t.value = int(t.value)
        return t


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

    @_('sym ASSIGN sym')
    def stmt(self, p):
        return lang_num.VarAssignment(p.sym0, p.sym1)

    @_('sym ASSIGN NUMBER')
    def stmt(self, p):
        return lang_num.ValAssignment(p.sym, p.NUMBER)

    @_('sym ASSIGN QMARK')
    def stmt(self, p):
        return lang_num.QMarkAssignment(p.sym)

    @_('sym ASSIGN sym PLUS NUMBER')
    def stmt(self, p):
        return lang_num.VarIncAssignment(p.sym0, p.sym1)

    @_('sym ASSIGN sym MINUS NUMBER')
    def stmt(self, p):
        return lang_num.VarDecAssignment(p.sym0, p.sym1)

    @_('ASSUME LPAREN expr RPAREN')
    def stmt(self, p):
        return lang.Assume(p.expr)

    @_('sym EQUAL sym')
    def expr(self, p):
        return lang_num.EqualsVar(p.sym0, p.sym1)

    @_('sym NOTEQUAL sym')
    def expr(self, p):
        return lang_num.NotEqualsVar(p.sym0, p.sym1)

    @_('sym EQUAL NUMBER')
    def expr(self, p):
        return lang_num.EqualsVal(p.sym, p.NUMBER)

    @_('sym NOTEQUAL NUMBER')
    def expr(self, p):
        return lang_num.NotEqualsVal(p.sym, p.NUMBER)

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

    @_('EVEN sym')
    def pred(self, p):
        return lang_num.Even(p.sym)

    @_('ODD sym')
    def pred(self, p):
        return lang_num.Odd(p.sym)

    @_('SUM vars EQUAL SUM vars')
    def pred(self, p):
        return lang.SumEquals(p.vars0, p.vars1)
