import logging
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char
from pyObjectManager.String import String
import ast

logger = logging.getLogger("pyState:SimFunction:String.rstrip")


def handle(state,call,chars=None,ctx=None):
    """
    Simulate Python's rstrip string method
    """
    ctx = ctx if ctx is not None else state.ctx

    # The root (i.e.: "s" in s.rstrip())
    root = state.resolveObject(call.func.value,ctx=ctx)

    assert type(root) is String

    # Resolve the chars
    chars = state.resolveObject(chars,ctx=ctx) if chars is not None else state.getVar(varName='tempRstripstr',ctx=1,varType=String,kwargs={'string': " ","increment": True})

    # According to the docs, this should be String or None
    if type(chars) not in [String, Char]:
        err = "handle: Invalid argument type {0}".format(type(chars))
        logger.error(err)
        raise Exception(err)

    # Change input to always be a String object
    if type(chars) is Char:
        oldChars = chars
        chars = state.getVar(varName='tempRstripstr',ctx=1,varType=String,kwargs={'increment': True})
        chars.append(oldChars)


    # TODO: Add symbolic width capability
    if not chars.isStatic():
        err = "handle: Don't know how to handle non static chars arg"
        logger.error(err)
        raise Exception(err)

    # TODO: Add symbolic string capability
    if not root.isStatic():
        err = "handle: Don't know how to handle symbolic string"
        logger.error(err)
        raise Exception(err)

    # Get new str
    newString = state.getVar('temprStripStr',ctx=1,varType=String,kwargs={'increment':True})
    
    # Set new str to be the same as the old str
    newString.setTo(root)
    
    # Look char by char in reverse order to find target char
    for c in newString[::-1]:
        for f in chars:
            if c.mustBe(f):
                newString.pop()
                break
        else:
            break
    
    return newString.copy()
