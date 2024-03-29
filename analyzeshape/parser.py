import sly

from analyzeshape import lang as lang_shape
from analyzeframework import lang

class Lexer(sly.Lexer):
    tokens = {NAME, LABEL, ASSIGN, EQUAL, NOTEQUAL, NULL, NEXT,
              ASSUME, SKIP, ASSERT, LPAREN, RPAREN, TRUE, FALSE, 
              NEW, ODD, EVEN, LEN, LS}
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
    NEXT = r'\.n'
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

    @_('sym ASSIGN sym')
    def stmt(self, p):
        return lang_shape.VarVarAssignment(p.sym0, p.sym1)

    @_('sym ASSIGN sym NEXT')
    def stmt(self, p):
        return lang_shape.VarNextAssignment(p.sym0, p.sym1)

    @_('sym NEXT ASSIGN sym')
    def stmt(self, p):
        return lang_shape.NextVarAssignment(p.sym0, p.sym1)

    @_('sym ASSIGN NEW')
    def stmt(self, p):
        return lang_shape.VarNewAssignment(p.sym)

    @_('sym ASSIGN NULL')
    def stmt(self, p):
        return lang_shape.VarNullAssignment(p.sym)

    @_('sym NEXT ASSIGN NULL')
    def stmt(self, p):
        return lang_shape.NextNullAssignment(p.sym)

    @_('ASSUME LPAREN expr RPAREN')
    def stmt(self, p):
        return lang.Assume(p.expr)

    @_('ASSUME LPAREN pred_expr RPAREN')
    def stmt(self, p):
        return lang.Assume(p.pred_expr)

    @_('sym EQUAL sym')
    def pred_expr(self, p):
        return lang_shape.EqualsVarVar(p.sym0, p.sym1)

    @_('sym EQUAL NULL')
    def pred_expr(self, p):
        return lang_shape.EqualsVarNull(p.sym)

    @_('sym EQUAL sym NEXT')
    def pred_expr(self, p):
        return lang_shape.EqualsVarNext(p.sym0, p.sym1)

    @_('sym NOTEQUAL sym')
    def pred_expr(self, p):
        return lang_shape.NotEqualsVarVar(p.sym0, p.sym1)

    @_('sym NOTEQUAL NULL')
    def pred_expr(self, p):
        return lang_shape.NotEqualsVarNull(p.sym)

    @_('sym NOTEQUAL sym NEXT')
    def pred_expr(self, p):
        return lang_shape.NotEqualsVarNext(p.sym0, p.sym1)

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

    @_('pred_expr')
    def andc(self, p):
        return [p.pred_expr]

    @_('pred andc')
    def andc(self, p):
        return [p.pred] + p.andc

    @_('pred_expr andc')
    def andc(self, p):
        return [p.pred_expr] + p.andc

    @_('LS sym sym')
    def pred(self, p):
        return lang_shape.Ls(p.sym0, p.sym1)

    @_('LEN sym sym EQUAL LEN sym sym')
    def pred(self, p):
        return lang_shape.Len(p.sym0, p.sym1, p.sym2, p.sym3)

    @_('EVEN sym sym')
    def pred(self, p):
        return lang_shape.Even(p.sym0, p.sym1)

    @_('ODD sym sym')
    def pred(self, p):
        return lang_shape.Odd(p.sym0, p.sym1)
