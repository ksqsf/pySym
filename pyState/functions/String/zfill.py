import logging
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char
from pyObjectManager.String import String
import ast

logger = logging.getLogger("pyState:SimFunction:String.zfill")


def handle(state,call,width,ctx=None):
    """
    Simulate Python's zfill string method
    """
    ctx = ctx if ctx is not None else state.ctx

    # The root (i.e.: "s" in s.zfill())
    root = state.resolveObject(call.func.value,ctx=ctx)

    assert type(root) is String

    # Resolve the width
    width = state.resolveObject(width,ctx=ctx)

    # TODO: Add symbolic width capability
    if not width.isStatic():
        err = "handle: Don't know how to handle non static width"
        logger.error(err)
        raise Exception(err)

    # TODO: Add symbolic string capability
    if not root.isStatic():
        err = "handle: Don't know how to handle symbolic string"
        logger.error(err)
        raise Exception(err)

    # Get new str
    newString = state.getVar('tempZfillStr',ctx=1,varType=String)
    newString.increment()
    
    # Resolve the width
    width = width.getValue()

    # zfill will not truncate
    newString.setTo(root)
    
    # If we're already at our length, just return
    if newString.length() >= width:
        return newString

    # Add as many "0"s as needed
    while newString.length() < width:
        # Create the new Char
        c = state.getVar('tempCharZfill',ctx=1,varType=Char)
        c.increment()
        # Set it
        c.setTo('0')
        # Insert it
        newString.variables.insert(0,c.copy())

    return newString

"""
    # If we're indexing a Char, just change it into a String
    if type(sub) is Char:
        c = sub
        sub = String("tempIndex",1,state=state)
        sub.variables.append(c)

    assert type(sub) is String

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
    for i in range(0,subStr.length() - sub.length() + 1):
        # If it is possible to have this index here, add it
        if subStr[i:i+sub.length()].canBe(sub):
            ret.append(Int('tempStrIndex',1,value=i))
        
        # If this is the only possible place, we must stop
        if subStr[i:i+sub.length()].mustBe(sub):
            break

    return ret

"""
