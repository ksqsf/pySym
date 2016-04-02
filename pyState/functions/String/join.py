import logging
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char
from pyObjectManager.String import String
import ast
import pyState

logger = logging.getLogger("pyState:SimFunction:String.join")


def handle(state,call,elem,ctx=None):
    """
    Simulate Python's zfill string method
    """
    ctx = ctx if ctx is not None else state.ctx

    # The root (i.e.: "s" in s.join())
    root = state.resolveObject(call.func.value,ctx=ctx)

    assert type(root) is String

    # Resolve the elem
    elems = state.resolveObject(elem,ctx=ctx)

    elems = elems if type(elems) is list else [elems]

    # If we're waiting on a symbolic call, return
    retObjs = [x for x in elems if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    if len(elems) != 1:
        err = "handle: Don't know how to handle state splitting"
        logger.error(err)
        raise Exception(err)

    elem = elems.pop()

    if type(elem) is not List:
        err = "handle: Don't know how to handle non-List join iterators"
        logger.error(err)
        raise Exception(err)


    # Get new string
    newString = state.getVar('tempStrJoin',ctx=1,varType=String)
    newString.increment()

    # Loop through elem values
    for item in elem:
        if type(item) is String:
            newString.variables += item.variables + root.variables
        else:
            err = "handle: Don't know how to handle type {0}".format(type(item))
            logger.error(err)
            raise Exception(err)

    if root.length() > 0:
        # Remove the excess chars that may have built up
        newString = newString[:-root.length()]

    return newString.copy()

    """
    assert type(root) is String

    # Resolve the width
    width = state.resolveObject(width)

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
