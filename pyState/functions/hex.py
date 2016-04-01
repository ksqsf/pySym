from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
from pyObjectManager.List import List
from pyObjectManager.Char import Char
import logging
import pyState

logger = logging.getLogger("pyState:functions:hex")


def handle(state,call,obj,ctx=None):
    """
    Simulate hex funcion
    """
    ctx = ctx if ctx is not None else state.ctx

    # Resolve the object
    obj = state.resolveObject(obj,ctx=ctx)

    if type(obj) == pyState.ReturnObject:
        return obj

    # This is probably a script problem, not us
    if type(obj) not in [Int, BitVec]:
        err = "handle: Invalid param for hex type {0}".format(type(obj))
        logger.error(err)
        raise Exception(err)

    # Only dealing with concrete values for now.
    if obj.isStatic():
        ret = state.getVar("tmpHexVal",ctx=1,varType=String)
        ret.increment()
        ret.setTo(hex(obj.getValue()))

    # TODO: Deal with symbolic values (returning list of possibilities)
    else:
        err = "handle: Don't know how to handle symbolic for now"
        logger.error(err)
        raise Exception(err)


    return ret.copy()
