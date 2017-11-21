import logging
from pySym.pyObjectManager.List import List
from pySym.pyObjectManager.Int import Int
from pySym.pyObjectManager.Real import Real
from pySym.pyObjectManager.BitVec import BitVec
from pySym.pyObjectManager.Char import Char
from pySym.pyObjectManager.String import String
from pySym import pyState

logger = logging.getLogger("pyState:SimFunction:List:clear")


def handle(state,call,ctx=None):
    """
    Clear list
    """
    ctx = ctx if ctx is not None else state.ctx
    
    # The "l" in "l.clear()"
    roots = state.resolveObject(call.func.value,ctx=ctx)

    # If we're waiting on a symbolic call (that'd be weird..), return
    retObjs = [x for x in roots if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    # Not sure when we'd ever have multiple...
    assert len(roots) == 1

    root = roots[0]

    root.state.path.pop(0)
    
    root.increment()
    root.variables = []

    return [root.state]



