import logging
import z3, z3util
import ast
from pyState import hasRealComponent, ReturnObject
import pyState.z3Helpers
import pyState.BinOp, pyState.Call
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List
from pyObjectManager.String import String

logger = logging.getLogger("pyState:Assign")


def _handleAssignNum(target,value):
    """
    Handle assigning a number to a variable (i.e.: x = 1)
    Update local variable dict and return
    value should already be resolved via state.resolveObject (meaning it is now an expression)
    """

    # Implicitly taking value's state
    state = value.state.copy()

    logger.debug("_handleAssignNum: Handling {0} = {1}".format(type(target),type(value)))
    
    if type(value) is Real:
        x = state.resolveObject(target,varType=Real)

    elif type(value) is BitVec:
        x = state.resolveObject(target,varType=BitVec,kwargs={'size':value.size})

    else:
        x = state.resolveObject(target,varType=Int)

    ret = []

    for x2 in x:

        parent = state.objectManager.getParent(x2)
        index = parent.index(x2)
        parent[index] = value
        
        x2.state = x2.state.copy()

        x2.state.path.pop(0)

        # Return the state
        ret += [x2.state]
    
    return ret


def _handleAssignList(target,listObject):
    assert type(target) is ast.Name
    assert type(listObject) is List 

    state = listObject.state.copy()

    # Resolve the object
    targets = state.resolveObject(target,varType=List)

    ret = []

    for target in targets:

        parent = state.objectManager.getParent(target)
        index = parent.index(target)

        # Set the new list
        parent[index] = listObject.copy()

        target.state = target.state.copy()

        target.state.path.pop(0)

        ret += [target.state]

    return ret

def _handleAssignString(target,stringObject):
    assert type(target) is ast.Name
    assert type(stringObject) is String

    state = stringObject.state.copy()

    # Resolve the object
    targets = state.resolveObject(target,varType=String)

    ret = []

    for target in targets:

        parent = state.objectManager.getParent(target)
        index = parent.index(target)

        # Set the new list
        parent[index] = stringObject.copy()

        target.state = target.state.copy()

        target.state.path.pop(0)

        ret += [target.state]
    
    return ret


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
    values = state.resolveObject(value)

    # Normalize
    values = values if type(values) is list else [values]

    # Check for return object. Return all applicable
    retObjs = [x.state for x in values if type(x) is ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    ret = []
    
    # For every possible assign value, get the state
    for value in values:

        if type(value) in [Int, Real, BitVec]:
            ret += _handleAssignNum(target,value)
    
        elif type(value) is List:
            ret += _handleAssignList(target,value)
    
        elif type(value) is String:
            ret += _handleAssignString(target,value)
    
        else:
            err = "Don't know how to assign type {0}".format(type(value))
            logger.error(err)
            raise Exception(err)

    return ret
