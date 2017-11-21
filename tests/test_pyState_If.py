import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import logging
from pySym import Colorer
logging.basicConfig(level=logging.DEBUG,format='%(name)s - %(levelname)s - %(message)s', datefmt='%m/%d/%Y %I:%M:%S %p')


import ast_parse
import z3
from pySym.pyPath import Path
from pySym.pyPathGroup import PathGroup
import pytest

test1 = """
x = 5
y = 6
if x == y or 2 == 2:
    pass
"""

test2 = """
x = 5
y = 5
if x == y and y + 2 == x + 2:
    pass
"""

test3 = """
s = pyState.String(8)
y = 0
if 2 > s.index('a'):
    y += 1
"""

test4 = """
s = pyState.String(8)
x = 5
y = 6
z = 0
if x == y or s.index('a') == 2:
    z += 1
"""

def test_pySym_If_StateSplit():
    b = ast_parse.parse(test3).body
    p = Path(b,source=test3)
    pg = PathGroup(p)

    pg.explore()
    
    # Splits into 8 possibilities and then if splits again
    assert len(pg.completed) == 8
    assert len(pg.deadended) == 8

    # Two of those states should hit the y+=1
    assert sum([p.state.any_int('y') for p in pg.completed]) == 2

    b = ast_parse.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)

    pg.explore()
    
    # Splits into 8 possibilities and then if splits again
    assert len(pg.completed) == 8
    assert len(pg.deadended) == 8

    # Two of those states should hit the y+=1
    assert sum([p.state.any_int('z') for p in pg.completed]) == 1

def test_pySym_ifBoolOp():
    b = ast_parse.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    
    pg.explore()

    b = ast_parse.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)
    
    pg.explore()

