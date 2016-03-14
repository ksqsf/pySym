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
x = 0
while x < 10:
    x += 1

y = 1
"""

test2 = """
def test():
    return 5

x = 0
while x < test():
    x += 1

y = 1
"""

def test_pySym_funcInWhileTest():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    pg = PathGroup(p)
    assert pg.explore(find=9)


    assert len(pg.active) == 0
    assert len(pg.completed) == 0
    assert len(pg.errored) == 0
    assert len(pg.deadended) == 6
    assert len(pg.found) == 1

    assert pg.found[0].state.isSat()
    assert pg.found[0].state.any_int('x') == 5


def test_pySym_simpleWhile():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    pg = PathGroup(p)
    assert pg.explore(find=6)


    assert len(pg.active) == 0
    assert len(pg.completed) == 0
    assert len(pg.errored) == 0
    assert len(pg.deadended) == 11
    assert len(pg.found) == 1

    assert pg.found[0].state.isSat()
    assert pg.found[0].state.any_int('x') == 10

