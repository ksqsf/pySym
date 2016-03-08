import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path
import pytest

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

