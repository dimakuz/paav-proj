import dataclasses
import typing

from pysmt import shortcuts


@dataclasses.dataclass(frozen=True)
class Symbol:
    name: str

    def __str__(self):
        return self.name

@dataclasses.dataclass
class Skip:
    def __str__(self):
        return 'skip'


@dataclasses.dataclass
class Expression:
    pass


@dataclasses.dataclass
class EqualsVar(Expression):
    lval: Symbol
    rval: Symbol

    def __str__(self):
        return f'{self.lval} = {self.rval}'


@dataclasses.dataclass
class NotEqualsVar(Expression):
    lval: Symbol
    rval: Symbol

    def __str__(self):
        return f'{self.lval} != {self.rval}'


@dataclasses.dataclass
class EqualsVal(Expression):
    lval: Symbol
    rval: int

    def __str__(self):
        return f'{self.lval} = {self.rval}'


@dataclasses.dataclass
class NotEqualsVal(Expression):
    lval: Symbol
    rval: int

    def __str__(self):
        return f'{self.lval} != {self.rval}'


@dataclasses.dataclass
class Truth(Expression):
    def __str__(self):
        return 'TRUE'


@dataclasses.dataclass
class Falsehood(Expression):
    def __str__(self):
        return 'FALSE'


@dataclasses.dataclass
class Statement:
    pass


@dataclasses.dataclass
class VarAssignment(Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval}'


@dataclasses.dataclass
class ValAssignment(Statement):
    lval: str
    rval: int

    def __str__(self):
        return f'{self.lval} := {self.rval}'


@dataclasses.dataclass
class QMarkAssignment(Statement):
    lval: str

    def __str__(self):
        return f'{self.lval} := ?'


@dataclasses.dataclass
class VarIncAssignment(Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval} + 1'


@dataclasses.dataclass
class VarDecAssignment(Statement):
    lval: str
    rval: str

    def __str__(self):
        return f'{self.lval} := {self.rval} - 1'

@dataclasses.dataclass
class Assume(Statement):
    expr: Expression

    def __str__(self):
        return f'assume({self.expr})'


@dataclasses.dataclass
class Predicate:
    pass


@dataclasses.dataclass
class Odd(Predicate):
    sym: Symbol

    def __str__(self):
        return f'ODD {self.sym}'

    def formula(self):
        return shortcuts.Symbol(f'ODD-{self.sym}')


@dataclasses.dataclass
class Even(Predicate):
    sym: Symbol

    def __str__(self):
        return f'EVEN {self.sym}'

    def formula(self):
        return shortcuts.Symbol(f'EVEN-{self.sym}')


@dataclasses.dataclass
class Assert(Statement):
    dnf: typing.List[typing.List[Predicate]]

    def __str__(self):
        clauses = [' '.join(str(p) for p in c) for c in self.dnf]
        dnf = ' '.join(f'({c})' for c in clauses)
        return f'assert {dnf}'

    def formula(self):
        clauses = []
        for e in self.dnf:
            preds = [x.formula() for x in e]
            clauses.append(shortcuts.And(*preds))
        return shortcuts.Or(*clauses)


@dataclasses.dataclass
class SumEquals(Predicate):
    lval: typing.List[Symbol]
    rval: typing.List[Symbol]

    def __str__(self):
        lval = ' '.join(str(s) for s in self.lval)
        rval = ' '.join(str(s) for s in self.rval)
        return 'SUM {lval} = SUM {rval}'

    def formula(self):
        lval = set(self.lval)
        rval = set(self.rval)
        lval, rval = lval - rval, rval - lval
        return shortcuts.Equals(
            shortcuts.Plus(
                *(shortcuts.Symbol(v.name, shortcuts.INT) for v in lval),
            ),
            shortcuts.Plus(
                *(shortcuts.Symbol(v.name, shortcuts.INT) for v in rval),
            ),
        )


@dataclasses.dataclass
class ProgramLine:
    source: str
    statement: Statement
    destination: str
