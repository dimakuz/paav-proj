import dataclasses
import typing

from pysmt import shortcuts
from analyzeframework import lang



@dataclasses.dataclass
class VarVarAssignment(lang.Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval}'


@dataclasses.dataclass
class VarNextAssignment(lang.Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval}.n'


@dataclasses.dataclass
class NextVarAssignment(lang.Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval}.n := {self.rval}'


@dataclasses.dataclass
class VarNewAssignment(lang.Statement):
    lval: str

    def __str__(self):
        return f'{self.lval} := new'


@dataclasses.dataclass
class VarNullAssignment(lang.Statement):
    lval: str

    def __str__(self):
        return f'{self.lval} := NULL'


@dataclasses.dataclass
class NextNullAssignment(lang.Statement):
    lval: str

    def __str__(self):
        return f'{self.lval}.n := NULL'


@dataclasses.dataclass
class EqualsVarVar(lang.Predicate):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} = {self.rval}'

    def formula(self):
        return shortcuts.Symbol(f'EQ-{self.lval}-{self.rval}')


@dataclasses.dataclass
class NotEqualsVarVar(lang.Predicate):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} != {self.rval}'

    def formula(self):
        return shortcuts.Not(shortcuts.Symbol(f'EQ-{self.lval}-{self.rval}'))


@dataclasses.dataclass
class EqualsVarNext(lang.Predicate):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} = {self.rval}.n'

    def formula(self):
        return shortcuts.Symbol(f'EQNEXT-{self.lval}-{self.rval}')


@dataclasses.dataclass
class NotEqualsVarNext(lang.Predicate):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} != {self.rval}.n'

    def formula(self):
        return shortcuts.Not(shortcuts.Symbol(f'EQNEXT-{self.lval}-{self.rval}'))


@dataclasses.dataclass
class EqualsVarNull(lang.Predicate):
    lval: lang.Symbol

    def __str__(self):
        return f'{self.lval} = NULL'

    def formula(self):
        return shortcuts.Symbol(f'NULL-{self.lval}')


@dataclasses.dataclass
class NotEqualsVarNull(lang.Predicate):
    lval: lang.Symbol

    def __str__(self):
        return f'{self.lval} != NULL'

    def formula(self):
        return shortcuts.Not(shortcuts.Symbol(f'NULL-{self.lval}'))


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
        return shortcuts.Equals(
                shortcuts.Symbol(f'LEN-{self.sym0}-{self.sym1}'),
                shortcuts.Symbol(f'LEN-{self.sym2}-{self.sym3}')
        )
