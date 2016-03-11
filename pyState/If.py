import logging
import z3
import ast
import pyState.Compare
from copy import deepcopy

logger = logging.getLogger("pyState:If")


def handle(state,element):
    """
    Attempt to handle the if element
    """
    
    # On If statements we want to take both options

    # path == we take the if statement
    stateIf = state

    # path2 == we take the else statement
    stateElse = state.copy()
    ret_states = [stateIf,stateElse]

    # Check if statement. We'll have at least one instruction here, so treat this as a call
    # Saving off the current path so we can return to it and pick up at the next instruction
    cs = deepcopy(stateIf.path[1:])
    # Only push our stack if it's not empty
    if len(cs) > 0:
        stateIf.callStack.append({
            'path': cs,
            'ctx': state.ctx,
            'retID': state.retID,
        })

    # Our new path becomes the inside of the if statement
    stateIf.path = element.body

    # Update the else's path
    # Check if there is an else path we need to take
    if len(element.orelse) > 0:
        cs = deepcopy(stateElse.path[1:])
        if len(cs) > 0:
            stateElse.callStack.append({
                'path': cs,
                'ctx': state.ctx,
                'retID': state.retID
            })
        stateElse.path = element.orelse


    # Check what type of test this is    
    if type(element.test) == ast.Compare:
        pyState.Compare.handle(stateIf,stateElse,element.test)

    else:
        logger.error("handle: I don't know how to handle type {0}".format(type(element.test)))
   
    # Return the new states
    return ret_states 
