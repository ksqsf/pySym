from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
from pyObjectManager.Char import Char
import logging
import pyState

logger = logging.getLogger("pyState:functions:int")


def handle(state,call,obj,base=10,ctx=None):
    """
    Simulate int funcion
    """
    ctx = ctx if ctx is not None else state.ctx

    # Resolve the object
    obj = state.resolveObject(obj,ctx=ctx)

    # If we're waiting on a function call
    if type(obj) is pyState.ReturnObject:
        return obj
    
    if type(obj) not in [Int, Real, BitVec, String, Char]:
        err = "handle: Don't know how to handle type {0}".format(type(obj))
        logger.error(err)
        raise Exception(err)

    # Check up-front types for int. Catch these issues
    if type(obj) in [Int, Real, BitVec] and type(base) is not int:
        err = "handle: Cannot use base variable when using non-string object".format(type(obj))
        logger.error(err)
        raise Exception(err)

    # Resolve base
    base = base if type(base) is int else state.resolveObject(base,ctx=ctx)

    # Only dealing with concrete values for now.
    if obj.isStatic() and (type(base) is int or base.isStatic()):
        val = obj.getValue()
        ret = state.getVar("tmpIntVal",ctx=1,varType=Int)
        ret.increment()
        base = base if type(base) is int else base.getValue()

        # int() doesn't like base set for non-strings
        if type(val) is str:
            ret.setTo(int(val,base))
        else:
            ret.setTo(int(val))


    # TODO: Deal with symbolic values (returning list of possibilities)
    else:
        err = "handle: Don't know how to handle symbolic ints for now"
        logger.error(err)
        raise Exception(err)


    return ret.copy()
