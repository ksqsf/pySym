import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path
import pytest

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

