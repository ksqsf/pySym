from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
import logging

logger = logging.getLogger("pyState:functions:bin")


def handle(state,call,obj):
    """
    Simulate bin funcion
    """
    # Resolve the object
    obj = state.resolveObject(obj)
    
    if type(obj) not in [Int, Real, BitVec]:
        err = "handle: This shouldn't happen. Possibly a target program bug? Got obj type {0}".format(type(obj))
        logger.error(err)
        raise Exception(err)

    # Only dealing with concrete values for now.
    if obj.isStatic():
        val = obj.getValue()
        ret = state.getVar("tmpStrVal",ctx=1,varType=String)
        ret.increment()
        ret.setTo(bin(val))

    # TODO: Deal with symbolic values (returning list of possibilities)
    else:
        err = "handle: Don't know how to handle symbolic ints for now"
        logger.error(err)
        raise Exception(err)


    return ret.copy()
