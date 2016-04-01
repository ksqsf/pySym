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
x = ''.join(["1","2","3"])
y = ','.join(["4","5","6"])
z = "".join([str(i) for i in [1,2,3]])
"""


def test_function_strJoin():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    
    assert pg.completed[0].state.any_str('x') == ''.join(["1","2","3"])
    assert pg.completed[0].state.any_str('y') == ','.join(["4","5","6"])
    assert pg.completed[0].state.any_str('z') == "".join([str(i) for i in [1,2,3]])
