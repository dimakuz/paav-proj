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
class Assume(Statement):
    expr: Expression

    def __str__(self):
        return f'assume({self.expr})'


@dataclasses.dataclass
class Predicate:
    pass


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
class ProgramLine:
    source: str
    statement: Statement
    destination: str
