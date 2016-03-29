import logging
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char

logger = logging.getLogger("pyState:SimFunction:List:append")


def handle(state,call,var):
    """
    Append var to list
    """
    
    # The root (i.e.: "l" in l.append())
    root = state.resolveObject(call.func.value)
    
    assert type(root) is List
    
    # Resolve what we're going to be appending
    var = state.resolveObject(var)
    
    if type(var) in [Int, Real, BitVec, Char]:
        root.append(var)
        state.addConstraint(root[-1].getZ3Object() == var.getZ3Object())
    
    elif type(var) is List:
        root.append(state.recursiveCopy(var))
    
    else:
        err = "handle: Don't know how to handle appending type {0}".format(type(var))
        logger.error(err)
        raise Exception(err)


