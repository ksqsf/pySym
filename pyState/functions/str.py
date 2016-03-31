from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
import logging

logger = logging.getLogger("pyState:functions:str")


def handle(state,call,obj):
    """
    Simulate str funcion
    """
    # Resolve the object
    obj = state.resolveObject(obj)
    
    if type(obj) not in [Int, Real, BitVec]:
        # Only know how to do str on numbers for now
        err = "handle: Don't know how to handle type {0}".format(type(obj))
        logger.error(err)
        raise Exception(err)

    # Only dealing with concrete values for now.
    if obj.isStatic():
        val = obj.getValue()
        ret = state.getVar("tmpStrVal",ctx=1,varType=String)
        ret.increment()
        ret.setTo(str(val))

    # TODO: Deal with symbolic values (returning list of possibilities)
    else:
        err = "handle: Don't know how to handle symbolic ints for now"
        logger.error(err)
        raise Exception(err)


    return ret.copy()
