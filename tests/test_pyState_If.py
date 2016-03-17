import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import logging
import Colorer
logging.basicConfig(level=logging.DEBUG,format='%(name)s - %(levelname)s - %(message)s', datefmt='%m/%d/%Y %I:%M:%S %p')


import ast
import z3
from pyPath import Path
from pyPathGroup import PathGroup
import pytest

test1 = """
x = 5
y = 6
if x == y or 2 == 2:
    print("yay!")
"""

test2 = """
x = 5
y = 5
if x == y and y + 2 == x + 2:
    print("yay!")
"""

def test_pySym_ifBoolOp():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    
    assert pg.explore(find=5)

    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)
    
    assert pg.explore(find=5)

