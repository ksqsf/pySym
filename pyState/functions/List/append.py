import logging
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char
from pyObjectManager.String import String
import pyState
from copy import deepcopy

logger = logging.getLogger("pyState:SimFunction:List:append")


def handle(state,call,var,ctx=None):
    """
    Append var to list
    """
    ctx = ctx if ctx is not None else state.ctx
    
    # The root (i.e.: "l" in l.append())
    #root = state.resolveObject(call.func.value,ctx=ctx)
    
    #assert type(root) is List
    
    # Resolve what we're going to be appending
    varList = state.resolveObject(var,ctx=ctx)

    # Normalize
    varList = varList if type(varList) is list else [varList]

    # If we're waiting on a symbolic call, return
    retObjs = [x for x in varList if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    ret = []

    # Not sure how else to handle this. Probably shouldn't be popping instruction here, but...
    state.path.pop(0)
    
    for var in varList:
        # Get a new State
        s = state.copy()
        
        # Resolve Root
        root = s.resolveObject(call.func.value,ctx=ctx)

        assert type(root) is List

        # Append it
        root.append(deepcopy(var))
        
        # Add this to our returns
        retObj = pyState.ReturnObject(1)
        retObj.state = s

        ret.append(retObj)

    return ret



