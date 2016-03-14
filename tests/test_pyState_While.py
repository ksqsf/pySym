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

test3 = """
def test(x,y):
    return x + y

x = 0
z = 0
while x < 5:
    y = 0
    while y < 3:
        z = z + test(x,y)
        y += 1
    x += 1

z = z
"""

test4 = """
def test(x,y):
    return x + y

x = 0
z = 0
while x < 5:
    y = 0
    while y < 3:
        z += test(x,y)
        y += 1
    x += 1

z = z
"""

test5 = """
def test(x,y):
    out = 2
    while x < y:
        out *= x
        x += 1
    
    return out

x = 0
z = 0
while x < 5:
    y = 0
    while y < 3:
        z += test(x,y)
        y += 1
    x += 1

z = z
"""


def test_pySym_complicated():
    b = ast.parse(test5).body
    p = Path(b,source=test5)
    pg = PathGroup(p)
    
    assert pg.explore(find=19)
    assert pg.found[0].state.any_int('z') == 26


def test_pySym_nestedWhile():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    pg = PathGroup(p)

    assert pg.explore(find=14)
    assert pg.found[0].state.any_int('z') == 45

    b = ast.parse(test4).body
    p = Path(b,source=test4)
    pg = PathGroup(p)
    assert pg.explore(find=14)
    assert pg.found[0].state.any_int('z') == 45



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

