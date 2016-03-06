import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import symbolicExecutor
import ast
import z3

test1 = "x = 1"

def test_assignInt():
    assign = ast.parse(test1).body[0]
    localVars, globalVars = symbolicExecutor.handleAssign(assign)
    
    # Basic dict checks
    assert "x" in localVars
    assert type(localVars["x"]["var"]) == z3.ArithRef
    assert len(localVars['x']['expr']) == 1
    
    # Try solving it to ensure that works correctly
    s = z3.Solver()
    s.add(eval(localVars['x']['expr'][0]))
    
    assert s.check() == z3.sat
    m = s.model()
    assert m[localVars['x']['var']].is_int()
    assert m[localVars['x']['var']].as_long() == 1
