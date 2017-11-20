import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import logging
from pySym import Colorer
logging.basicConfig(level=logging.DEBUG,format='%(name)s - %(levelname)s - %(message)s', datefmt='%m/%d/%Y %I:%M:%S %p')

import ast_parse
import z3
from pyPath import Path
from pyPathGroup import PathGroup
import pytest
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List

test1 = """
l = [1,2,3]
l.clear()
"""

test2 = """
l = [1,2,3]
l.clear()
l.append(5)
"""

def test_function_String_clear_append():
    b = ast_parse.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)

    pg.explore()

    assert len(pg.completed) == 1

    assert pg.completed[0].state.any_list('l') == [5]


def test_function_String_clear_basic():
    b = ast_parse.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)

    pg.explore()

    assert len(pg.completed) == 1

    assert pg.completed[0].state.any_list('l') == []


