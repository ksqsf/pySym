import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import ast
import z3
from pyPath import Path
import pyState.Compare
import pytest

compare1 = """
x = {0}
y = {1}
if x {2} y:
    print("One")
else:
    print("Two")
    x = 7
"""

def test_pySym_Compare():
    ################
    # Greater Than #
    ################
    b = ast.parse(compare1.format(1,5,">")).body
    p = Path(b,source=compare1.format(1,5,">"))
    # Step through the "if" statement
    p = p.step()[0]
    p = p.step()[0]
    p2 = p.step()
    ifSide = p2[0]
    elseSide = p2[1]

    # If side should not be possible
    assert not ifSide.state.isSat()
    assert elseSide.state.isSat()

    # Track expected number of assertions
    assert len(ifSide.state.solver.assertions()) == 3
    assert len(elseSide.state.solver.assertions()) == 3

    # Make sure the answer makes sense
    assert ifSide.state.any_int('x') == None
    assert elseSide.state.any_int('x') == 1

    #########################
    # Greater Than Or Equal #
    #########################
    b = ast.parse(compare1.format(2,2,">=")).body
    p = Path(b,source=compare1.format(2,2,">="))
    # Step through the "if" statement
    p = p.step()[0]
    p = p.step()[0]
    p2 = p.step()
    ifSide = p2[0]
    elseSide = p2[1]

    # If side should be correct
    assert ifSide.state.isSat()
    assert not elseSide.state.isSat()

    # Track expected number of assertions
    assert len(ifSide.state.solver.assertions()) == 3
    assert len(elseSide.state.solver.assertions()) == 3

    # Make sure the answer makes sense
    assert ifSide.state.any_int('x') == 2
    assert elseSide.state.any_int('x') == None

    #############
    # Less Than #
    #############
    b = ast.parse(compare1.format(1,5,"<")).body
    p = Path(b,source=compare1.format(1,5,"<"))
    # Step through the "if" statement
    p = p.step()[0]
    p = p.step()[0]
    p2 = p.step()
    ifSide = p2[0]
    elseSide = p2[1]

    # If side should be correct
    assert ifSide.state.isSat()
    assert not elseSide.state.isSat()

    # Track expected number of assertions
    assert len(ifSide.state.solver.assertions()) == 3
    assert len(elseSide.state.solver.assertions()) == 3

    # Make sure the answer makes sense
    assert ifSide.state.any_int('x') == 1
    assert elseSide.state.any_int('x') == None

    ######################
    # Less Than Or Equal #
    ######################
    b = ast.parse(compare1.format(3,5,"<=")).body
    p = Path(b,source=compare1.format(3,5,"<="))
    # Step through the "if" statement
    p = p.step()[0]
    p = p.step()[0]
    p2 = p.step()
    ifSide = p2[0]
    elseSide = p2[1]
    
    # If side should be correct
    assert ifSide.state.isSat()
    assert not elseSide.state.isSat()

    # Track expected number of assertions
    assert len(ifSide.state.solver.assertions()) == 3
    assert len(elseSide.state.solver.assertions()) == 3

    # Make sure the answer makes sense
    assert ifSide.state.any_int('x') == 3
    assert elseSide.state.any_int('x') == None

    #########
    # Equal #
    #########
    b = ast.parse(compare1.format(1,5,"==")).body
    p = Path(b,source=compare1.format(1,5,"=="))
    # Step through the "if" statement
    p = p.step()[0]
    p = p.step()[0]
    p2 = p.step()
    ifSide = p2[0]
    elseSide = p2[1]

    # If side should not be correct
    assert not ifSide.state.isSat()
    assert elseSide.state.isSat()

    # Track expected number of assertions
    assert len(ifSide.state.solver.assertions()) == 3
    assert len(elseSide.state.solver.assertions()) == 3

    # Make sure the answer makes sense
    assert ifSide.state.any_int('x') == None
    assert elseSide.state.any_int('x') == 1

    #############
    # Not Equal #
    #############
    b = ast.parse(compare1.format(1,5,"!=")).body
    p = Path(b,source=compare1.format(1,5,"!="))
    # Step through the "if" statement
    p = p.step()[0]
    p = p.step()[0]
    p2 = p.step()
    ifSide = p2[0]
    elseSide = p2[1]

    # If side should be correct
    assert ifSide.state.isSat()
    assert not elseSide.state.isSat()

    # Track expected number of assertions
    assert len(ifSide.state.solver.assertions()) == 3
    assert len(elseSide.state.solver.assertions()) == 3

    # Make sure the answer makes sense
    assert ifSide.state.any_int('x') == 1
    assert elseSide.state.any_int('x') == None


def test_unhandled_input():
    """
    This is admittedly contrived tests to just excersize code paths
    """
    class fakeElement:
        def __init__(self):
            self.ops = []
            self.comparators = []
    
    element = fakeElement()
    element.ops += ["test","test"]
    element.comparators += ["test","test"]
   
    # We aren't handling multiple comps/ops at this point 
    with pytest.raises(Exception):
        pyState.Compare._handleLeftVar(True,False,element,"x")
