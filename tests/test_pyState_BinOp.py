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

