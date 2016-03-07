import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyState import State

test1 = "x = 1"
test2 = "x = 2"

def test_assignInt():
    s = State()
    assign = ast.parse(test1).body[0]
    s.handleAssign(assign)
    
    # Basic dict checks
    assert "x" in s.localVars
    assert type(s.localVars["x"]["var"]) == z3.ArithRef
    assert len(s.localVars['x']['expr']) == 1
    
    # Try solving it to ensure that works correctly
    assert s.isSat()
    
    # Ensure we're getting expected output
    assert s.any_int('x') == 1
    
    # Try assigning again
    assign = ast.parse(test2).body[0]
    s.handleAssign(assign)
    
    # Basic dict checks
    assert "x" in s.localVars
    assert type(s.localVars["x"]["var"]) == z3.ArithRef
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
    s.handleAssign(assign)
    assert s.localVars != {}
    assert s2.localVars == {}
