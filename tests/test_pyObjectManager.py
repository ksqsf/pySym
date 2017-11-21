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
from pySym.pyObjectManager.Int import Int
from pySym.pyObjectManager.Real import Real
from pySym.pyObjectManager.BitVec import BitVec
from pySym.pyObjectManager.List import List

test1 = """
l = [1,2.2,3]
q = [1,2,[3,4]]
"""

def test_pyObjectManager_getParent():
    b = ast_parse.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    
    l = pg.completed[0].state.getVar('l')
    i = l[2]
    
    # Make sure it returned the right object
    assert pg.completed[0].state.objectManager.getParent(i) == l

    q = pg.completed[0].state.getVar('q')
    i = q[2][0]
    
    # Check that it recurses fully
    assert pg.completed[0].state.objectManager.getParent(i) == q[2]


