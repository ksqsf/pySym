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
