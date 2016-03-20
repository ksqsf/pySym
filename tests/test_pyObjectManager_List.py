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
l = [1,2.2,3]
"""

test2 = """
l = [1,2.2,[3,[4,5],6]]
"""

test3 = """
x = 3
l = [1,2,x,4]
"""

test4 = """
x = 3
l = [1,2,[x,4]]
"""

test5 = """
x = 3
l = [1,2,[x,4]]
x = 5
"""



def test_pyObjectManager_List_varInList():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('l') == [1,2,3,4]

    b = ast.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('l') == [1,2,[3,4]]


    # NOTE: This is correct behavior. Python resolves the object when creating the list
    # Updating the var later has no affect on the list
    b = ast.parse(test5).body
    p = Path(b,source=test5)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('l') == [1,2,[3,4]]



def test_pyObjectManager_List_BasicAssign():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('l') == [1,2.2,3]

def test_pyObjectManager_List_NestedList():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('l') == [1,2.2,[3,[4,5],6]]

