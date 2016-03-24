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
    
    logger.debug("_handleAssignNum: Handling {0} = {1}".format(target,value))
    
    if type(value) is Real:
        x = state.resolveObject(target,varType=Real)

    elif type(value) is BitVec:
        x = state.resolveObject(target,varType=BitVec,kwargs={'size':value.size})

    else:
        x = state.resolveObject(target,varType=Int)

    parent = state.objectManager.getParent(x)
    index = parent.index(x)

    state.addConstraint(x.getZ3Object(increment=True) == value.getZ3Object())

    # Return the state
    return [state]


def _handleAssignList(state,target,listObject):
    assert type(target) is ast.Name
    assert type(listObject) is List 

    # Resolve the object
    target = state.resolveObject(target,varType=List)
    parent = state.objectManager.getParent(target)
    index = parent.index(target)

    # Set the new list
    parent[index] = listObject

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

    # Resolve the value
    value = state.resolveObject(value)

    # Check for return object
    if type(value) == ReturnObject:
        return [state]

    # No return object, time to pop instruction
    state.path.pop(0) if len(state.path) > 0 else None

    if type(value) in [Int, Real, BitVec]:
        return _handleAssignNum(state,target,value)

    elif type(value) is List:
        return _handleAssignList(state,target,value)

    else:
        err = "Don't know how to assign type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
        logger.error(err)
        raise Exception(err)

