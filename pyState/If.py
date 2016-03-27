import logging
import z3
import ast
import pyState.Compare, pyState.BoolOp
from copy import deepcopy

logger = logging.getLogger("pyState:If")


def handle(state,element):
    """
    Attempt to handle the if element
    """
    
    # On If statements we want to take both options

    # path == we take the if statement
    stateIf = state

    # Check what type of test this is    
    if type(element.test) == ast.Compare:
        # Try to handle the compare
        trueConstraint = pyState.Compare.handle(state,element.test)
        
        # If we're waiting on resolution of a call, just return the initial state
        if type(trueConstraint) is pyState.ReturnObject:
            return [state]

        # Important to copy after Constraint generation since it may have added to the state!
        stateElse = state.copy()
    
        # If we're good to go, pop the instructions
        stateIf.path.pop(0)
        stateElse.path.pop(0)
        
        # Add the constraints we just got
        stateIf.addConstraint(trueConstraint)
        stateElse.addConstraint(z3.Not(trueConstraint))


    elif type(element.test) == ast.BoolOp:
        trueConstraint = pyState.BoolOp.handle(state, element.test)
    
        # If we're waiting on resolution of a call, just return the initial state
        if type(trueConstraint) is pyState.ReturnObject:
            return [state]

        # Important to copy after Constraint generation since it may have added to the state!
        stateElse = state.copy()

        # Not waiting on anything, move forward
        stateIf.path.pop(0)
        stateElse.path.pop(0)
        
        #print(trueConstraint)
        # Add the constraints we just got
        stateIf.addConstraint(trueConstraint)
        stateElse.addConstraint(z3.Not(trueConstraint))

    else:
        logger.error("handle: I don't know how to handle type {0}".format(type(element.test)))

    ret_states = [stateIf,stateElse]

    # Check if statement. We'll have at least one instruction here, so treat this as a call
    # Saving off the current path so we can return to it and pick up at the next instruction
    cs = deepcopy(stateIf.path)
    # Only push our stack if it's not empty
    if len(cs) == 0:
        cs.append(ast.Pass(lineno=0,col_offset=0))
    stateIf.pushCallStack(cs,state.ctx,state.retID)

    # Our new path becomes the inside of the if statement
    stateIf.path = element.body
    # Once inside the If, we're no longer in a "loop" for this call
    stateIf.loop = None

    # Update the else's path
    # Check if there is an else path we need to take
    if len(element.orelse) > 0:
        cs = deepcopy(stateElse.path)
        if len(cs) > 0:
            stateElse.pushCallStack(cs,state.ctx,state.retID)
        
        stateElse.path = element.orelse
        stateElse.loop = None

    return ret_states 
