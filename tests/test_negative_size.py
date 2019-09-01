import pytest

from analyzeshape import structure
from pysmt import shortcuts
import collections

from sympy import *


def test_negative_size_perm1():

	p1, p2 = symbols('p-L1 p-L2')

	expr = 2*p1 - p2*2 + 6
	assert(structure.is_negative(expr))


def test_negative_size_perm2():

	p1, p2 = symbols('p-L1 p-L2')

	expr = 2*p1 + p2*2 - 6
	assert(not structure.is_negative(expr))

def test_negative_size_both():

	p1, t1 = symbols('p-L1 t-L2')

	expr = 2*p1 - t1*2 - 6
	assert(not structure.is_negative(expr))

def test_negative_size_temp1():

	t1, t2 = symbols('t-L1 t-L2')

	expr = 2*t1 - t2*2 + 6
	assert(structure.is_negative(expr))

def test_negative_size_temp2():

	t1, t2 = symbols('t-L1 t-L2')

	expr = 2*t1 + t2*2 - 6
	assert(not structure.is_negative(expr))

def test_negative_size_none():

	expr = Integer(-50)
	assert(structure.is_negative(expr))


def test_negative_size_factored():

	p1, p2 = symbols('p-L1 p-L2')

	expr = (p1 - 5) * (3*p2 - 2)
	assert(not structure.is_negative(expr))
