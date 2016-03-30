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
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List

test1 = """
s = "Test"
x = s.index("{0}")
"""

test2 = """
s = pyState.String(10)
x = s.index('a')
"""

def test_function_String_Index_Symbolic():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)

    pg.explore()

    # Every index should be a possibility
    assert len(pg.completed) == 10
    
    indexes = []
    # Make sure we got all of them
    for path in pg.completed:
        indexes.append(path.state.any_int('x'))
    
    assert set(indexes) == set(range(10))


def test_function_String_Index():
    b = ast.parse(test1.format("T")).body
    p = Path(b,source=test1.format("T"))
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    assert pg.completed[0].state.any_int('x') == 0

    b = ast.parse(test1.format("t")).body
    p = Path(b,source=test1.format("t"))
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    assert pg.completed[0].state.any_int('x') == 3

    b = ast.parse(test1.format("es")).body
    p = Path(b,source=test1.format("es"))
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    assert pg.completed[0].state.any_int('x') == 1

    b = ast.parse(test1.format("st")).body
    p = Path(b,source=test1.format("st"))
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    assert pg.completed[0].state.any_int('x') == 2



