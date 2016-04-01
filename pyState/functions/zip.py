from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
from pyObjectManager.List import List
import logging
import pyState

logger = logging.getLogger("pyState:functions:zip")


def handle(state,call,left,right):
    """
    Simulate zip funcion
    """
    # Resolve the object
    left = state.resolveObject(left)

    if type(left) is pyState.ReturnObject:
        return left
    
    # Don't want to lose track of our vars
    left = left.copy()

    right = state.resolveObject(right)

    if type(right) is pyState.ReturnObject:
        return right
    
    right = right.copy()

    # Only handling List and String objects for now
    if type(left) not in [List, String]:
        err = "handle: Don't know how to handle type {0}".format(type(left))
        logger.error(err)
        raise Exception(err)

    if type(right) not in [List, String]:
        err = "handle: Don't know how to handle type {0}".format(type(right))
        logger.error(err)
        raise Exception(err)
    print(left)
    print(right)
    # Create our output List
    newList = state.getVar('tmpZipList',ctx=1,varType=List)
    newList.increment()

    # Might as well use Python's own zip function to help us
    for (l,r) in zip(left,right):
        # TODO: This should really be a Tuple, but I haven't implemented that yet.
        tempList = state.getVar('tmpZipInner',ctx=1,varType=List)
        tempList.increment()
        tempList.variables = [l,r]
        newList.variables.append(tempList.copy())

    return newList.copy()
