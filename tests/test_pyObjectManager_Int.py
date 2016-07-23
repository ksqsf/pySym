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
x = 1
"""

test2 = """
x = pyState.Int()
y = 5
"""

test3 = """
x = 12
"""

test4 = """
l = [pyState.Int(), pyState.Int()]
if l[0] != l[1]:
    pass
if l[0] == l[1]:
    pass

pass
"""

def test_pyObjectManager_Int_MultipleObj():
    b = ast.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)

    pg.explore(find=4)
    assert len(pg.found) == 1

    pg = PathGroup(p)
    pg.explore(find=6)

    assert len(pg.found) == 1

def test_pyObjectManager_Int_strPrint():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    x = pg.completed[0].state.getVar('x')
    assert x.__str__() == "12"

def test_pyObjectManager_Int_setTo():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    x = pg.completed[0].state.getVar('x')
    y = pg.completed[0].state.getVar('y')
    x.setTo(1337)
    assert pg.completed[0].state.any_int('x') == 1337
    x.increment()
    x.setTo(y)
    assert pg.completed[0].state.any_int('x') == 5


def test_pyObjectManager_Int_isStatic():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    x = pg.completed[0].state.getVar('x')
    
    assert x.isStatic()
    assert x.getValue() == 1


