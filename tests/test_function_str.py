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
s = str(12)
s2 = str(1.2)
s3 = str([1,2,3])
"""

test2 = """
s = pyState.String(8)
x = str(s.index('a'))
"""

def test_function_str_statesplit():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 8

    set([int(p.state.any_str('x')) for p in pg.completed]) == set(range(8))


def test_function_str():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    
    assert pg.completed[0].state.any_str('s') == str(12)
    assert pg.completed[0].state.any_str('s2') == str(1.2)
    assert pg.completed[0].state.any_str('s3') == str([1,2,3])
