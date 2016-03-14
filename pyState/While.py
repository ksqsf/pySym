import logging
import z3
import ast
import pyState.Compare
from copy import deepcopy

logger = logging.getLogger("pyState:While")


def handle(state,element):
    """
    Attempt to handle the while element
    """
    
    # While is basically a repeated If statement, we want to take both sides

    stateIf = state
    stateElse = state.copy()
    ret_states = [stateIf,stateElse]

    # Check what type of test this is    
    if type(element.test) == ast.Compare:
        # Try to handle the compare
        ret = pyState.Compare.handle(stateIf,stateElse,element.test)
        
        # If we're waiting on resolution of a call, just return the initial state
        if type(ret) is pyState.ReturnObject:
            print(stateIf.callStack[-1]['path'][0].test.comparators)
            return [stateIf]
    
        # If we're good to go, pop the instructions
        stateIf.path.pop(0)
        stateElse.path.pop(0)

    else:
        err = "handle: I don't know how to handle type {0}".format(type(element.test))
        logger.error(err)
        raise Exception(err)


    # Check if statement. We'll have at least one instruction here, so treat this as a call
    # Saving off the current path so we can return to it and pick up at the next instruction
    cs = deepcopy(stateIf.path)
    # Only push our stack if it's not empty
    if len(cs) > 0:
        stateIf.pushCallStack(path=cs)

    # Our new path becomes the inside of the if statement
    stateIf.path = element.body

    # If state should get a copy of the loop we're now in
    stateIf.loop = deepcopy(element)
    # else side should be done with the loop
    stateElse.loop = None

    # Update the else's path
    # Check if there is an else path we need to take
    if len(element.orelse) > 0:
        cs = deepcopy(stateElse.path)
        if len(cs) > 0:
            stateElse.pushCallStack(path=cs)
        
        stateElse.path = element.orelse

    return ret_states 
