import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path

test1 = "x = 1\ny = 2"

simpleIf = """
x = 1
y = 1
if x > y:
    print("This shouldn't hit")
else:
    print("This should hit")
    x = 2
"""

def test_basicPathStep():
    b = ast.parse(test1).body
    p1 = Path(b,source=test1)
    p2 = p1.step()[0].step()[0]
    p1.printBacktrace()
    p2.printBacktrace()
    assert p2.state.any_int('x') == 1
    assert p2.state.any_int('y') == 2
    assert p1.state.any_int('x') == None
    assert p1.state.any_int('y') == None

def test_pathCopy():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    p2 = p.copy()
    assert p2 != p
    p = p.step()[0]
    assert p.state.any_int('x') == 1
    assert p2.state.any_int('x') == None

def test_simpleIf():
    b = ast.parse(simpleIf).body
    p = Path(b,source=simpleIf)
    # Step through the "if" statement
    p = p.step()[0]
    p = p.step()[0]
    p2 = p.step()
    ifSide = p2[0]
    elseSide = p2[1]
    
    # ifSide's path should now be inside, meaning only the print statement
    assert len(ifSide.path) == 1
    # Else should be in the else statement
    assert len(elseSide.path) == 2
    
    # Neither have anything to do after the if statement
    assert len(ifSide.callStack) == 0
    assert len(elseSide.callStack) == 0
    
    # If side should not be possible
    assert not ifSide.state.isSat()
    assert elseSide.state.isSat()
    
    # Track expected number of assertions
    assert len(ifSide.state.solver.assertions()) == 3
    assert len(elseSide.state.solver.assertions()) == 3
    
    # Make sure the answer makes sense
    assert ifSide.state.any_int('x') == None
    assert elseSide.state.any_int('x') == 1
