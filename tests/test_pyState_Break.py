import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path
import pytest
from pyPathGroup import PathGroup

test1 = """
x = 0
y = 1
while x < 10:
    if x == 5:
        if y == 1:
            break
    x += 1

y = 1
"""

def test_pySym_break():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    
    pg.explore()

    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') == 5


