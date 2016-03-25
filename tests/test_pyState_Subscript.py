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

test3 = """
def test():
    return 4

l = [1,2,3,[test(),5]]
x = l[3][0]
"""

test4 = """
def test():
    return 4

l = [1,2,3,[test(),5]]
x = l[3]
"""

test5 = """
l = [1,2,3,[4,[5,6,7]]]
x = l[3][1]
"""

test6 = """
i = pyState.BVV(123,64)
l = [1,2.2,3.1415,4,i]
x = l[::2]
"""

test7 = """
i = pyState.BVV(123,64)
l = [1,2.2,3.1415,4,i]
x = l[::-1]
"""

test8 = """
i = pyState.BVV(123,64)
l = [1,2.2,3.1415,4,i,8,[1,2,3]]
x = l[:]
"""

test9 = """
i = pyState.BVV(123,64)
l = [1,2.2,3.1415,4,i,8,[1,2,3]]
x = l[::-1]
"""

test10 = """
i = pyState.BVV(123,64)
l = [1,2.2,3.1415,4,i,8,[1,2,3]]
x = l[1:7:2]
"""

test11 = """
l = [1,[2,3],4]
x = l[0:2][1][1]
"""

def test_pyState_nestedSlice():
    b = ast.parse(test11).body
    p = Path(b,source=test11)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') == 3


def test_pyState_SubscriptSlice():
    b = ast.parse(test6).body
    p = Path(b,source=test6)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('x') == [1, 3.1415, 123]

    b = ast.parse(test7).body
    p = Path(b,source=test7)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('x') == [123, 4, 3.1415, 2.2, 1]

    b = ast.parse(test8).body
    p = Path(b,source=test8)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('x') == [1,2.2,3.1415,4,123,8,[1,2,3]]

    b = ast.parse(test9).body
    p = Path(b,source=test9)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('x') == [1,2.2,3.1415,4,123,8,[1,2,3]][::-1]

    b = ast.parse(test10).body
    p = Path(b,source=test10)
    pg = PathGroup(p)

    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('x') == [2.2, 4, 8]



def test_pyState_AssignListFromSubscript():
    b = ast.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('x') == [4,5]

    b = ast.parse(test5).body
    p = Path(b,source=test5)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_list('x') == [5,6,7]



def test_pyState_Subscript_MultiDimentional():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    pg = PathGroup(p)
    
    pg.explore()
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') == 4


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

