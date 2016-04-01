from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
from pyObjectManager.List import List
from pyObjectManager.Char import Char
import logging
import pyState

logger = logging.getLogger("pyState:functions:ord")


def handle(state,call,obj,ctx=None):
    """
    Simulate ord funcion
    """
    ctx = ctx if ctx is not None else state.ctx

    # Resolve the object
    obj = state.resolveObject(obj,ctx=ctx)

    if type(obj) == pyState.ReturnObject:
        return obj
    
    # This is probably a script problem, not us
    if (type(obj) not in [String, Char]) or (type(obj) is String and obj.length() != 1):
        err = "handle: Invalid param for ord type {0}".format(type(obj))
        logger.error(err)
        raise Exception(err)

    # Only dealing with concrete values for now.
    if obj.isStatic():
        ret = state.getVar("tmpOrdVal",ctx=1,varType=Int)
        ret.increment()
        # Sanitize String to Char
        if type(obj) is String:
            obj = obj[0]
        ret.setTo(ord(obj.getValue()))

    # TODO: Deal with symbolic values (returning list of possibilities)
    else:
        err = "handle: Don't know how to handle symbolic Char/String for now"
        logger.error(err)
        raise Exception(err)


    return ret.copy()
