import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyState import State
import pyState.Assign

test1 = "x = 1"
test2 = "x = 2"

def test_assignInt():
    s = State()
    assign = ast.parse(test1).body[0]
    pyState.Assign.handle(s,assign)
    
    # Basic dict checks
    assert "x" in s.localVars
    assert type(s.localVars["x"]["eval"]) == str
    assert type(s.getZ3Var("x")) == z3.ArithRef
    assert len(s.localVars['x']['expr']) == 1
    
    # Try solving it to ensure that works correctly
    assert s.isSat()
    
    # Ensure we're getting expected output
    assert s.any_int('x') == 1
    
    # Try assigning again
    assign = ast.parse(test2).body[0]
    pyState.Assign.handle(s,assign)
    
    # Basic dict checks
    assert "x" in s.localVars
    assert type(s.localVars["x"]["eval"]) == str
    assert type(s.getZ3Var("x")) == z3.ArithRef
    assert len(s.localVars['x']['expr']) == 1
    
    # Try solving it to ensure that works correctly
    assert s.isSat()
    
    # Ensure we're getting expected output
    assert s.any_int('x') == 2

def test_copy():
    s = State()
    assign = ast.parse("a = 1").body[0]

    s2 = s.copy()
    
    # Ensure it's actually being copied
    assert s != s2
    
    # Add something to one and make sure the other is empty
    pyState.Assign.handle(s,assign)
    assert s.localVars != {}
    assert s2.localVars == {}

def test_any_int():
    s = State()
    assign = ast.parse("x = 12").body[0]
    pyState.Assign.handle(s,assign)

    assert s.any_int('x') == 12
    assert s.any_int('q') == None
    

def test_getZ3Var():
    s = State()
    assign = ast.parse("x = 12").body[0]
    pyState.Assign.handle(s,assign)
    x = s.getZ3Var('x')
    assert type(x) == z3.ArithRef
    
