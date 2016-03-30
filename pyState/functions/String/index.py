import logging
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char
from pyObjectManager.String import String
import ast

logger = logging.getLogger("pyState:SimFunction:String.index")


def handle(state,call,sub,start=None,end=None):
    """
    Determine location of char in string.
    """
    assert type(sub) is ast.Str 

    # The root (i.e.: "s" in s.index())
    root = state.resolveObject(call.func.value)

    assert type(root) is String

    # Resolve the vars
    sub = sub.s
    start = state.resolveObject(start) if start is not None else None
    end = state.resolveObject(end) if end is not None else None

    if type(start) not in [int,type(None)]:
        if not start.isStatic():
            err = "handle: Don't know how to handle appending type {0}".format(type(var))
            logger.error(err)
            raise Exception(err)
        start = start.getValue()

    if type(end) not in [int,type(None)]:
        if not end.isStatic():
            err = "handle: Don't know how to handle appending type {0}".format(type(var))
            logger.error(err)
            raise Exception(err)
        end = end.getValue()

    # Get the substring
    if start is None:
        start = 0
    
    if end is None:
        end = root.length()
    
    subStr = root[start:end]
    ret = []

    # Move the size window through the input
    for i in range(0,subStr.length() - len(sub) + 1):
        # If it is possible to have this index here, add it
        if subStr[i:i+len(sub)].canBe(sub):
            ret.append(Int('tempStrIndex',1,value=i))
        
        # If this is the only possible place, we must stop
        if subStr[i:i+len(sub)].mustBe(sub):
            break

    return ret


