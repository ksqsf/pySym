import logging
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char
from pyObjectManager.String import String
import pyState

logger = logging.getLogger("pyState:SimFunction:List:append")


def handle(state,call,var,ctx=None):
    """
    Append var to list
    """
    ctx = ctx if ctx is not None else state.ctx
    
    # The root (i.e.: "l" in l.append())
    root = state.resolveObject(call.func.value,ctx=ctx)
    
    assert type(root) is List
    
    # Resolve what we're going to be appending
    varList = state.resolveObject(var,ctx=ctx)

    # Normalize
    varList = varList if type(varList) is list else [varList]

    # If we're waiting on a symbolic call, return
    retObjs = [x for x in varList if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    if len(varList) == 1:
        var = varList.pop()

        if type(var) in [Int, Real, BitVec, Char]:
            root.append(var)
            state.addConstraint(root[-1].getZ3Object() == var.getZ3Object())
        
        elif type(var) in [List, String]:
            root.append(state.recursiveCopy(var))
    
        else:
            err = "handle: Don't know how to handle appending type {0}".format(type(var))
            logger.error(err)
            raise Exception(err)

    else:
            err = "handle: Don't know how to handle state splitting yet"
            logger.error(err)
            raise Exception(err)



