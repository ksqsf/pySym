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
l = [1,2,3]
x = l[1]
"""

test2 = """
i = 2
l = [1,2,3]
x = l[i]
"""

def test_pyState_Subscript_VariableSubscript():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') == 3


def test_pyState_Subscript_AssignToVar():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') == 2

