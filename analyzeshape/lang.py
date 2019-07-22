import dataclasses
import typing

from pysmt import shortcuts
from analyzeframework import lang



@dataclasses.dataclass(frozen=True)
class SymbolNext:
    name: str

    def __str__(self):
        return f'{self.name}.n'


@dataclasses.dataclass
class EqualsVarVar(lang.Expression):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} = {self.rval}'


@dataclasses.dataclass
class NotEqualsVarVar(lang.Expression):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} != {self.rval}'


@dataclasses.dataclass
class EqualsVarNext(lang.Expression):
    lval: lang.Symbol
    rval: lang.SymbolNext

    def __str__(self):
        return f'{self.lval} = {self.rval}'


@dataclasses.dataclass
class NotEqualsVarNext(lang.Expression):
    lval: lang.Symbol
    rval: lang.SymbolNext

    def __str__(self):
        return f'{self.lval} != {self.rval}'


@dataclasses.dataclass
class EqualsVarNull(lang.Expression):
    lval: lang.Symbol

    def __str__(self):
        return f'{self.lval} = NULL'


@dataclasses.dataclass
class NotEqualsVarNull(lang.Expression):
    lval: lang.Symbol

    def __str__(self):
        return f'{self.lval} != NULL'


@dataclasses.dataclass
class VarAssignment(lang.Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval}'


@dataclasses.dataclass
class NewAssignment(lang.Statement):
    lval: str

    def __str__(self):
        return f'{self.lval} := new'


@dataclasses.dataclass
class NullAssignment(lang.Statement):
    lval: str

    def __str__(self):
        return f'{self.lval} := NULL'


@dataclasses.dataclass
class Odd(lang.Predicate):
    sym0: lang.Symbol
    sym1: lang.Symbol

    def __str__(self):
        return f'ODD {self.sym0} {self.sym1}'

    def formula(self):
        return shortcuts.Symbol(f'ODD-{self.sym0}-{self.sym1}')


@dataclasses.dataclass
class Even(lang.Predicate):
    sym0: lang.Symbol
    sym1: lang.Symbol

    def __str__(self):
        return f'EVEN {self.sym0} {self.sym1}'

    def formula(self):
        return shortcuts.Symbol(f'EVEN-{self.sym0}-{self.sym1}')


@dataclasses.dataclass
class Ls(lang.Predicate):
    sym0: lang.Symbol
    sym1: lang.Symbol

    def __str__(self):
        return f'LS {self.sym0} {self.sym1}'

    def formula(self):
        return shortcuts.Symbol(f'LS-{self.sym0}-{self.sym1}')


@dataclasses.dataclass
class Len(lang.Predicate):
    sym0: lang.Symbol
    sym1: lang.Symbol
    sym2: lang.Symbol
    sym3: lang.Symbol

    def __str__(self):
        return f'LEN {self.sym0} {self.sym1} = LEN {self.sym2} {self.sym3}'

    def formula(self):
        return shortcuts.Symbol(f'LEN-{self.sym0}-{self.sym1}-{self.sym2}-{self.sym3}')
