from pySym.pyObjectManager.Int import Int
from pySym.pyObjectManager.Real import Real
from pySym.pyObjectManager.BitVec import BitVec
from pySym.pyObjectManager.String import String
from pySym.pyObjectManager.List import List
import logging
from pySym import pyState

logger = logging.getLogger("pyState:functions:str")


def handle(state,call,obj,ctx=None):
    """
    Simulate str funcion
    """
    ctx = ctx if ctx is not None else state.ctx

    # Resolve the object
    objs = state.resolveObject(obj,ctx=ctx)
    
    # Normalize
    objs = [objs] if type(objs) is not list else objs

    # Resolve calls if we need to
    retObjs = [x for x in objs if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    # Loop through objects
    retList = []
    for obj in objs:

        if type(obj) not in [Int, Real, BitVec, List]:
            # Only know how to do str on numbers for now
            err = "handle: Don't know how to handle type {0}".format(type(obj))
            logger.error(err)
            raise Exception(err)

        # Only dealing with concrete values for now.
        if obj.isStatic():
            ret = state.getVar("tmpStrVal",ctx=1,varType=String)
            ret.increment()
            # Utilize pyObjectManager class methods
            ret.setTo(obj.__str__(),clear=True)

        # TODO: Deal with symbolic values (returning list of possibilities)
        else:
            err = "handle: Don't know how to handle symbolic ints for now"
            logger.error(err)
            raise Exception(err)


        retList.append(ret.copy())

    return retList
