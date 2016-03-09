import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path
import pytest

test1 = """
def test():
    x = 5

x = 1
test()
y = 3
"""

test2 = """
def test(a,b,c):
    x = 5

x = 1
test(1,2.2,3.5)
y = 1
"""

test3 = """
def test(a,b=2,c=5.5):
    x = 5

x = 1.5
test(1,c=x+1)
y = 1
"""


def test_pySym_callwithKeyWordAndDefault():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_real('x') == 1.5
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('a') == 1
    assert p.state.any_int('b') == 2
    assert p.state.any_real('c') == 2.5
    assert p.state.any_int('x') == None



def test_pySym_callThreeArgs():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_int('x') == 1
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('a') == 1
    assert p.state.any_real('b') == 2.2
    assert p.state.any_real('c') == 3.5
    assert p.state.any_int('x') == None
    
    p = p.step()[0]
    assert p.state.isSat()
    assert p.state.any_int('x') == 5
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('a') == None
    assert p.state.any_real('b') == None
    assert p.state.any_real('c') == None
    assert p.state.any_int('x') == 1
    assert p.state.any_int('y') == 1


def test_pySym_CallNoArgs():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_int('x') == 1

    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('x') == None # New context means there should be no more x
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('x') == 5
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('x') == 1 # Back to original context
    assert p.state.any_int('y') == 3
