import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyState import State
import pyState.Assign
import pytest
from pyPath import Path
from pyPathGroup import PathGroup
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec

test1 = "x = 1"
test2 = "x = 2"
test3 = "x = 3.1415"
test4 = """
x = pyState.Int()
"""
test5 = """
x = pyState.Real()
"""

test6 = """
i = pyState.BVV(123,64)
l = [1,2.2,3.1415,4,i,8,[1,2,3]]
"""

def test_recursiveCopy():
    b = ast.parse(test6).body
    p = Path(b,source=test6)
    pg = PathGroup(p)
    
    pg.explore()
    
    assert len(pg.completed) == 1

    s = pg.completed[0].state

    l = s.getVar('l')
    l2 = s.recursiveCopy(s.getVar('l'))
    
    assert l != l2
    
    l2[-1][2].value = 4
    
    assert l[-1][2].value != l2[-1][2].value


def test_any_n_real():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    pg = PathGroup(p)
    
    pg.explore()
    
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_real('x') == 3.1415
    # Duplicate test to ensure we're not destroying state
    assert pg.completed[0].state.any_n_real('x',10) == [3.1415]
    assert pg.completed[0].state.any_n_real('x',10) == [3.1415]

    b = ast.parse(test5).body
    p = Path(b,source=test5)
    pg = PathGroup(p)

    pg.explore()

    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_real('x') != None
    # Duplicate test to ensure we're not destroying state
    assert len(pg.completed[0].state.any_n_real('x',10)) == 10
    assert len(pg.completed[0].state.any_n_real('x',10)) == 10


def test_any_n_int():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    
    pg.explore()
    
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') == 1
    # Duplicate test to ensure we're not destroying state
    assert pg.completed[0].state.any_n_int('x',10) == [1]
    assert pg.completed[0].state.any_n_int('x',10) == [1]

    b = ast.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)
    
    pg.explore()
    
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') != None
    # Duplicate test to ensure we're not destroying state
    assert len(pg.completed[0].state.any_n_int('x',10)) == 10
    assert len(pg.completed[0].state.any_n_int('x',10)) == 10



def test_assignInt():
    s = State()
    assign = ast.parse(test1).body[0]
    pyState.Assign.handle(s,assign)

    # Basic dict checks
    assert type(s.objectManager.getVar("x",ctx=s.ctx)) == Int
    assert s.objectManager.getVar("x",ctx=s.ctx).getZ3Object().is_int()
    #assert len(s.solver.assertions()) == 1

    # Try solving it to ensure that works correctly
    assert s.isSat()
    
    # Ensure we're getting expected output
    assert s.any_int('x') == 1
    
    # Try assigning again
    assign = ast.parse(test2).body[0]
    pyState.Assign.handle(s,assign)
    
    # Basic dict checks
    assert type(s.objectManager.getVar("x",ctx=s.ctx)) == Int
    assert s.objectManager.getVar("x",ctx=s.ctx).getZ3Object().is_int()
    #assert len(s.solver.assertions()) == 2

    # Try solving it to ensure that works correctly
    assert s.isSat()
    
    # Ensure we're getting expected output
    assert s.any_int('x') == 2


def test_assignFloat():
    s = State()
    assign = ast.parse(test3).body[0]
    pyState.Assign.handle(s,assign)
    # Basic dict checks
    assert type(s.objectManager.getVar("x",ctx=s.ctx)) == Real
    assert s.objectManager.getVar("x",ctx=s.ctx).getZ3Object().is_real()
    #assert len(s.solver.assertions()) == 1

    # Try solving it to ensure that works correctly
    assert s.isSat()

    # This isn't an int, it will raise exception
    with pytest.raises(Exception):
       s.any_int('x')
    
    # We should get this back
    assert s.any_real('x') == 3.1415

def test_copy():
    s = State()
    assign = ast.parse("a = 1").body[0]

    s2 = s.copy()
    
    # Ensure it's actually being copied
    assert s != s2
    
    # Add something to one and make sure the other is empty
    pyState.Assign.handle(s,assign)
    assert s.any_int('a') == 1
    with pytest.raises(Exception):
        s2.any_int('a')
    #assert s.objectManager.variables != {0: {}, 1: {'ret': {'count': 0, 'varType': 'z3.IntSort()'}}}
    #assert s2.objectManager.localVars == {0: {}, 1: {'ret': {'count': 0, 'varType': 'z3.IntSort()'}}}

def test_any_int():
    s = State()
    assign = ast.parse("x = 12").body[0]
    pyState.Assign.handle(s,assign)

    assert s.any_int('x') == 12
    with pytest.raises(Exception):
        s.any_int('q') == None
    

def test_getZ3Var():
    s = State()
    assign = ast.parse("x = 12").body[0]
    pyState.Assign.handle(s,assign)
    x = s.objectManager.getVar('x',ctx=s.ctx)
    assert type(x) is Int
    
