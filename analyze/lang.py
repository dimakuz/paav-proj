import dataclasses
import typing



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


@dataclasses.dataclass
class Even(Predicate):
    sym: Symbol

    def __str__(self):
        return f'EVEN {self.sym}'


@dataclasses.dataclass
class Assert(Statement):
    dnf: typing.List[typing.List[Predicate]]

    def __str__(self):
        clauses = [' '.join(str(p) for p in c) for c in self.dnf]
        dnf = ' '.join(f'({c})' for c in clauses)
        return f'assert {dnf}'


@dataclasses.dataclass
class ProgramLine:
    source: str
    statement: Statement
    destination: str
