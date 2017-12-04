import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))

import z3
import pySym
import pytest

def test_basic_project():
    proj = pySym.Project(os.path.join(myPath, "scripts", "basic_function.py"))
    pg = proj.factory.path_group()
    pg.explore()
    
    assert len(pg.deadended) == 1
    assert len(pg.completed) == 1
    assert pg.completed[0].state.any_int('x') == 1

