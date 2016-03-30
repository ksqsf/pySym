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

def test_pyObjectManager_Int_isStatic():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1

    x = pg.completed[0].state.getVar('x')
    
    assert x.isStatic()
    assert x.getValue() == 1


