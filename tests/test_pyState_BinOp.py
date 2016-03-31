import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path
import pytest
from pyPathGroup import PathGroup

test1 = """
x = 1.5 
y = 2.5
x = x {0} y
"""

test2 = """
x = 7
y = 5
x = x % y
"""

test3 = """
x = 2
x = x + 3.5
"""

test4 = """
a = 10
b = 1
c = 6
d = a ^ b ^ c
"""

test5 = """
a = 0x10325476
b = 0x98BADCFE
c = 0xEFCDAB89
d = 0x67452301
g = 0x12345678
e = (d ^ ((b & (c ^ a)) & g >> 2)) << 15
"""

test6 = """
h = pyState.BVV(1337,64)
h = h + 0xffffffffffffffff
"""

test7 = """
h = pyState.BVV(1337,64)
h = h * 0xffffffffffffff
"""

test8 = """
h = pyState.BVV(1337,64)
h = h - 1338
"""

test9 = """
def test(x,y):
    return x**y

x = test(2,4)**8
"""

test10 = """
s = "test" + " blerg"
s2 = pyState.String(8) + " blerg"
s3 = "This " + "is " + "a " + "test"
"""

test11 = """
l = [1,2,3] + [4,5,6]
"""

def test_pySym_BinOp_ListConcat():
    b = ast.parse(test11).body
    p = Path(b,source=test11)
    pg = PathGroup(p)
    pg.explore()

    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('l') == [1,2,3] + [4,5,6]


def test_pySym_BinOp_StrConcat():
    b = ast.parse(test10).body
    p = Path(b,source=test10)
    pg = PathGroup(p)
    pg.explore()

    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_str('s') == "test" + " blerg"
    
    assert len(pg.completed[0].state.any_str('s2')) == 8 + len(" blerg")
    assert pg.completed[0].state.any_str('s2').endswith(" blerg")

    assert pg.completed[0].state.any_str('s3') == "This " + "is " + "a " + "test"


def test_pySym_BinOp_Exp():
    b = ast.parse(test9).body
    p = Path(b,source=test9)
    pg = PathGroup(p)
    pg.explore()

    assert len(pg.completed) == 1
    assert len(pg.deadended) == 0

    assert pg.completed[0].state.any_int('x') == (2**4)**8

def test_pySym_BinOp_SafeBitVec():
    # Ensuring that we notice over and underflows

    #######
    # Add #
    #######
    b = ast.parse(test6).body
    p = Path(b,source=test6)
    pg = PathGroup(p)
    pg.explore()
    
    assert len(pg.completed) == 0
    assert len(pg.deadended) == 1

    #######
    # Mul #
    #######
    b = ast.parse(test7).body
    p = Path(b,source=test7)
    pg = PathGroup(p)
    pg.explore()

    assert len(pg.completed) == 0
    assert len(pg.deadended) == 1

    #######
    # Sub #
    #######
    b = ast.parse(test8).body
    p = Path(b,source=test8)
    pg = PathGroup(p)
    pg.explore()

    assert len(pg.completed) == 0
    assert len(pg.deadended) == 1




def test_pySym_BinOp_BitStuff():
    b = ast.parse(test5).body
    p = Path(b,source=test5)
    pg = PathGroup(p)
    pg.explore()
    
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('e') == 57065549561856


def test_pySym_BinOp_Xor():
    b = ast.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)
    pg.explore()
    
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('d') == 13


def test_pySym_BinOp():
    #######
    # Add #
    #######
    b = ast.parse(test1.format("+")).body
    p = Path(b,source=test1.format("+"))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_real('x') == 4.0

    #######
    # Sub #
    #######
    b = ast.parse(test1.format("-")).body
    p = Path(b,source=test1.format("-"))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_real('x') == -1.0

    #######
    # Mul #
    #######
    b = ast.parse(test1.format("*")).body
    p = Path(b,source=test1.format("*"))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_real('x') == 3.75

    #######
    # Div #
    #######
    b = ast.parse(test1.format("/")).body
    p = Path(b,source=test1.format("/"))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_real('x') == 0.6

    #######
    # Mod #
    #######
    b = ast.parse(test2.format("%")).body
    p = Path(b,source=test2.format("%"))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_int('x') == 2

def test_mixedTypes():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    print(p.state.solver)
    print(p.state.isSat())
    assert p.state.isSat()
    assert p.state.any_real('x') == 5.5

