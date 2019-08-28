import itertools
import collections
import copy

class AbstractSize():

    terms: collections.OrderedDict()

    def add(self, other):
        for variable in self.terms:
            if variable in other.terms:
                self.terms[variable] += other.terms[variable]
        for variable in other.terms:
            if variable not in self.terms:
                self.terms[variable] = +other.terms[variable]

        # self.terms = {variable: factor for variable, factor in self.terms.items() if factor != 0 or variable == '1'}
        for variable, factor in list(self.terms.items()):
            if factor == 0 and variable != '1':
                self.terms.pop(variable)

        return self

    def substract(self, other):
        for variable in self.terms:
            if variable in other.terms:
                self.terms[variable] -= other.terms[variable]
        for variable in other.terms:
            if variable not in self.terms:
                self.terms[variable] = -other.terms[variable]

        # self.terms = {variable: factor for variable, factor in self.terms.items() if factor != 0 or variable == '1'}
        for variable, factor in list(self.terms.items()):
            if factor == 0 and variable != '1':
                self.terms.pop(variable)

        return self

    def multiply(self, variable):
        self.terms[variable] = self.terms['1']
        self.terms['1'] = 0
        return self

    def has_term(self, term):
        return term in self.terms.keys()

    def is_negative(self):
        return any((var, fac) for (var, fac) in self.terms.items() if 'PERM' in var and fac < 0)

    def even(self):
        return all(factor % 2 == 0 for variable, factor in self.terms.items())

    def variables_eq(self, other):
        return set(self.terms.keys()) == set(other.terms.keys())

    def get_last_term(self):
        return next(reversed(self.terms))

    def extract_variable(self, variable):
        factor = self.terms[variable]
        size = AbstractSize(self.terms)
        size.terms.pop(variable)
        for var, fac in size.terms.items():
            if fac % factor == 0:
                size.terms[var] /= -factor
            else:
                return AbstractSize(collections.OrderedDict([('1', -1)]))
        return size

    def substitute(self, variable, size):
        if variable in self.terms.keys():
            factor = self.terms[variable]
            self.terms.pop(variable)
            temp_size = AbstractSize(size.terms)
            for var, fac in temp_size.terms.items():
                temp_size.terms[var] *= factor
            self.add(temp_size)

    def __eq__(self, other):
        return self.terms == other.terms

    def __str__(self):

        def pretty_print(factor, variable):
            prefix = ''
            if factor < 0:
                prefix = '- '
            else:
                prefix = '+ '
            if variable == '1':
                return prefix + str(factor)
            else:
                if abs(factor) == 1:
                    return prefix + variable
                else:
                    return f'{prefix}{abs(factor)}*{variable}'

        return ' '.join(pretty_print(factor, variable) for variable, factor in self.terms.items())

    def __init__(self, newterms):
        self.terms = copy.deepcopy(newterms)