import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import symbolicExecutor
import ast
import z3
from pyPath import Path

test1 = "x = 1\ny = 2"

def test_basicPathStep():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    p.step()
    p.step()
    p.printBacktrace()
    assert p.state.any_int('x') == 1
    assert p.state.any_int('y') == 2

def test_pathCopy():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    p2 = p.copy()
    assert p2 != p
    p.step()
    assert p.state.any_int('x') == 1
    assert p2.state.any_int('x') == None
