import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path
import pytest
from pyPathGroup import PathGroup

test1 = """
x = 7
y = 2
if x == y:
    print("One")
else:
    x {0} 7
"""

test2 = """
x = 7
y = 2.0
if x == y:
    print("One")
else:
    x += y
"""

test3 = """
a = 0x10325476
b = 0x98BADCFE
c = 0xEFCDAB89
d = 0x67452301
g = 0x12345678
e = a ^ g
e ^= b
e |= c
e >>= 5
e &= 0x12345678
e <<= 20
"""

test4 = """
h = pyState.BVV(1337,64)
h += 0xffffffffffffffff
"""

test5 = """
h = pyState.BVV(1337,64)
h *= 0xffffffffffffff
"""

test6 = """
h = pyState.BVV(1337,64)
h -= 1338
"""

def test_pySym_AugAssign_SafeBitVec():
    # Ensuring that we notice over and underflows

    #######
    # Add #
    #######
    b = ast.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)
    pg.explore()
    
    assert len(pg.completed) == 0
    assert len(pg.deadended) == 1

    #######
    # Mul #
    #######
    b = ast.parse(test5).body
    p = Path(b,source=test5)
    pg = PathGroup(p)
    pg.explore()

    assert len(pg.completed) == 0
    assert len(pg.deadended) == 1

    #######
    # Sub #
    #######
    b = ast.parse(test6).body
    p = Path(b,source=test6)
    pg = PathGroup(p)
    pg.explore()
    
    assert len(pg.completed) == 0
    assert len(pg.deadended) == 1


def test_pySym_AugAssign_BitStuff():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    pg = PathGroup(p)
    pg.explore()

    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('e') == 38776701190144


def test_pySym_AugAssign_MixedTypes():
    #######
    # Add #
    #######
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    ifSide,elseSide = p.step()
    elseSide = elseSide.step()[0]

    assert elseSide.state.isSat()
    assert elseSide.state.any_real('x') == 9.0
    assert elseSide.state.getZ3Var('x').is_real()



def test_pySym_AugAssign():
    #######
    # Add #
    #######
    b = ast.parse(test1.format("+=")).body
    p = Path(b,source=test1.format("+="))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    ifSide,elseSide = p.step()
    elseSide = elseSide.step()[0]
    
    assert elseSide.state.isSat()
    assert elseSide.state.any_int('x') == 14

    ############
    # Subtract #
    ############
    b = ast.parse(test1.format("-=")).body
    p = Path(b,source=test1.format("-="))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    ifSide,elseSide = p.step()
    elseSide = elseSide.step()[0]

    assert elseSide.state.isSat()
    assert elseSide.state.any_int('x') == 0

    ############
    # Multiply #
    ############
    b = ast.parse(test1.format("*=")).body
    p = Path(b,source=test1.format("*="))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    ifSide,elseSide = p.step()
    elseSide = elseSide.step()[0]

    assert elseSide.state.isSat()
    assert elseSide.state.any_int('x') == 49

    ##########
    # Divide #
    ##########
    b = ast.parse(test1.format("/=")).body
    p = Path(b,source=test1.format("/="))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    ifSide,elseSide = p.step()
    elseSide = elseSide.step()[0]

    assert elseSide.state.isSat()
    assert elseSide.state.any_int('x') == 1

    ##########
    # Modulo #
    ##########
    b = ast.parse(test1.format("%=")).body
    p = Path(b,source=test1.format("%="))
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    ifSide,elseSide = p.step()
    elseSide = elseSide.step()[0]

    assert elseSide.state.isSat()
    assert elseSide.state.any_int('x') == 0

