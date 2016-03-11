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

test1 = """
def test2():
    return 5

def test():
    return test2() + test2()

x = test()
z = 1
"""

test2 = """
def test():
    return 5 + 1.5

x = test()

if x > 5:
    x = 1
else:
    x = 0

if x == 1:
    x = 1337

z = 1
"""

def test_pyPath_exploreWithIf():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)
    
    # Explore to the end
    assert pg.explore(find=15)
    
    assert len(pg.active) == 0
    assert len(pg.completed) == 0
    assert len(pg.errored) == 0
    assert len(pg.deadended) == 2
    assert len(pg.found) == 1

    assert pg.found[0].state.any_int('x') == 1337


def test_pyPath_exploreFindLine():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    
    # Explore to line 9 (z = 1)
    # Current setup means that z=1 will not actually be executed
    assert pg.explore(find=9)
    
    assert len(pg.active) == 0
    assert len(pg.completed) == 0
    assert len(pg.errored) == 0
    assert len(pg.deadended) == 0
    assert len(pg.found) == 1

    assert pg.found[0].state.any_int('x') == 10


def test_pyPath_stepThroughProgram():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    pg.step()
    pg.step()
    pg.step()
    pg.step()
    pg.step()
    pg.step()
    pg.step()
    pg.step()
    pg.step()
    pg.step()
    pg.step()

    assert len(pg.active) == 0
    assert len(pg.completed) == 1
    assert len(pg.errored) == 0
    assert len(pg.deadended) == 0
    assert len(pg.found) == 0
    
    assert pg.completed[0].state.any_int('x') == 10
    assert pg.completed[0].state.any_int('z') == 1

