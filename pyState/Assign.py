import logging
import z3, z3util
import ast
from pyState import hasRealComponent, ReturnObject
import pyState.z3Helpers
import pyState.BinOp, pyState.Call
from copy import deepcopy
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List

logger = logging.getLogger("pyState:Assign")


def _handleAssignNum(state,target,value):
    """
    Handle assigning a number to a variable (i.e.: x = 1)
    Update local variable dict and return
    value should already be resolved via state.resolveObject (meaning it is now an expression)
    """
    # The "x" part of "x" = 1
    varName = target.id
    
    logger.debug("_handleAssignNum: Handling value {0} of type {1}".format(value,type(value)))
    
    # If we're waiting on a resolve, return state without pop-ing instruction
    if type(value) == ReturnObject:
        return [state]

    if type(value) in [Int, Real, BitVec]:
        value = value.getZ3Object()

    # Check if we have any Real vars to create the correct corresponding value (z3 doesn't mix types well)
    if hasRealComponent(value):
        x = state.getVar(varName,varType=Real).getZ3Object(increment=True)

    # See if our output should be a BitVec
    elif type(value) in [z3.BitVecRef, z3.BitVecNumRef]:
        x = state.getVar(varName,varType=BitVec,kwargs={'size':value.size()}).getZ3Object(increment=True)

    else: 
        x = state.getVar(varName,varType=Int).getZ3Object(increment=True)

    state.addConstraint(x == value)
    # Pop the instruction off
    state.path.pop(0) if len(state.path) > 0 else None

    # Return the state
    return [state]

def _handleAssignList(state,target,listObject):
    assert type(target) is ast.Name
    assert type(listObject) is ast.List

    l = state.resolveObject(listObject)

    # If we need to wait for a call to finish
    if type(l) is ReturnObject:
        return [state]

    state.setVar(varName=target.id,var=l)
    
    state.path.pop(0) if len(state.path) > 0 else None
    return [state]


def handle(state,element):
    """
    Attempt to handle the assign element
    """
    # Targets are what is being set
    targets = element.targets

    # Value is what to set them to
    value = element.value

    # Only handling single targets for now
    if len(targets) != 1:
        err = "Cannot handle multiple variable set at Line {0} Col {1}".format(element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)

    # Clear up the naming
    target = targets[0]

    # Call appropriate handlers
    if type(value) in [ast.Num, ast.Name, ast.BinOp, ReturnObject]:
        return _handleAssignNum(state,target,state.resolveObject(value))
    
    elif type(value) is ast.List:
        return _handleAssignList(state,target,value)

    elif type(value) is ast.Call:
        ret = state.resolveObject(value)
        # If we don't get a return object back, this is likely a simFunction call
        if type(ret) is not ReturnObject:
            return _handleAssignNum(state,target,ret)
        
        # Need to wait to resolve the object until the call has finished
        return [state]

    else:
        err = "Don't know how to assign type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
        logger.error(err)
        raise Exception(err)
    
