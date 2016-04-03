import logging
import z3
import ast
import pyState.Compare, pyState.BoolOp
from copy import deepcopy

logger = logging.getLogger("pyState:If")


def _handleConstraints(stateIf,stateElse,trueConstraint,element):
    # Add the constraints we just got
    stateIf.addConstraint(trueConstraint)
    stateElse.addConstraint(z3.Not(trueConstraint))

    ret_states = [stateIf,stateElse]

    # Check if statement. We'll have at least one instruction here, so treat this as a call
    # Saving off the current path so we can return to it and pick up at the next instruction
    cs = deepcopy(stateIf.path)
    # Only push our stack if it's not empty
    if len(cs) == 0:
        cs.append(ast.Pass(lineno=0,col_offset=0))
    stateIf.pushCallStack(cs,stateIf.ctx,stateIf.retID)

    # Our new path becomes the inside of the if statement
    stateIf.path = element.body
    # Once inside the If, we're no longer in a "loop" for this call
    stateIf.loop = None

    # Update the else's path
    # Check if there is an else path we need to take
    if len(element.orelse) > 0:
        cs = deepcopy(stateElse.path)
        if len(cs) > 0:
            stateElse.pushCallStack(cs,stateIf.ctx,stateIf.retID)

        stateElse.path = element.orelse
        stateElse.loop = None

    return ret_states


def handle(state,element):
    """
    Attempt to handle the if element
    """
    
    # On If statements we want to take both options

    # path == we take the if statement
    stateIf = state

    # Check what type of test this is    
    if type(element.test) == ast.Compare:
        trueConstraint = pyState.Compare.handle(state,element.test)
        
    elif type(element.test) == ast.BoolOp:
        trueConstraint = pyState.BoolOp.handle(state, element.test)
    
    else:
        logger.error("handle: I don't know how to handle type {0}".format(type(element.test)))

    # Normalize
    trueConstraint = trueConstraint if type(trueConstraint) is list else [trueConstraint]

    # Resolve calls if we need to
    retObjs = [x.state for x in trueConstraint if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    # Important to copy after Constraint generation since it may have added to the state!
    stateElse = state.copy()

    # Not waiting on anything, move forward
    stateIf.path.pop(0)
    stateElse.path.pop(0)
    
    ret = []

    for tc in trueConstraint:
        logger.debug("handling trueConstraint {0}".format(tc))
        ret += _handleConstraints(stateIf.copy(),stateElse.copy(),tc,element)
    
    return ret
