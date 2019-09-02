import dataclasses
import typing

from pysmt import shortcuts
from analyzeframework import lang


@dataclasses.dataclass
class EqualsVar(lang.Expression):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} = {self.rval}'


@dataclasses.dataclass
class NotEqualsVar(lang.Expression):
    lval: lang.Symbol
    rval: lang.Symbol

    def __str__(self):
        return f'{self.lval} != {self.rval}'


@dataclasses.dataclass
class EqualsVal(lang.Expression):
    lval: lang.Symbol
    rval: int

    def __str__(self):
        return f'{self.lval} = {self.rval}'


@dataclasses.dataclass
class NotEqualsVal(lang.Expression):
    lval: lang.Symbol
    rval: int

    def __str__(self):
        return f'{self.lval} != {self.rval}'


@dataclasses.dataclass
class VarAssignment(lang.Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval}'


@dataclasses.dataclass
class ValAssignment(lang.Statement):
    lval: str
    rval: int

    def __str__(self):
        return f'{self.lval} := {self.rval}'


@dataclasses.dataclass
class QMarkAssignment(lang.Statement):
    lval: str

    def __str__(self):
        return f'{self.lval} := ?'


@dataclasses.dataclass
class VarIncAssignment(lang.Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval} + 1'


@dataclasses.dataclass
class VarDecAssignment(lang.Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval} - 1'


@dataclasses.dataclass
class Odd(lang.Predicate):
    sym: lang.Symbol

    def __str__(self):
        return f'ODD {self.sym}'

    def formula(self):
        return shortcuts.Symbol(f'ODD-{self.sym}')


@dataclasses.dataclass
class Even(lang.Predicate):
    sym: lang.Symbol

    def __str__(self):
        return f'EVEN {self.sym}'

    def formula(self):
        return shortcuts.Symbol(f'EVEN-{self.sym}')


@dataclasses.dataclass
class SumEquals(lang.Predicate):
    lval: typing.List[lang.Symbol]
    rval: typing.List[lang.Symbol]

    def __str__(self):
        lval = ' '.join(str(s) for s in self.lval)
        rval = ' '.join(str(s) for s in self.rval)
        return f'SUM {lval} = SUM {rval}'

    def formula(self):
        return shortcuts.Equals(
            shortcuts.Plus(
                *(shortcuts.Symbol(v.name, shortcuts.INT) for v in self.lval),
                shortcuts.Int(0),
            ),
            shortcuts.Plus(
                *(shortcuts.Symbol(v.name, shortcuts.INT) for v in self.rval),
                shortcuts.Int(0),
            ),
        )

Assert = lang.Assert
