import z3
import ast
from pyObjectManager.Real import Real

def handle(state,call,value=None,ctx=None):
    """
    Returns a z3 Real object. Use this to inform pySym that something should be Real symbolic
    (optional) value == the value to set this variable to
    """
    ctx = ctx if ctx is not None else state.ctx

    myReal = state.resolveObject(ast.Name('tempReal',0),ctx=ctx,varType=Real)
   
    ret = myReal
 
    if value is not None:
        ret = []
        for r in myReal:
            state = r.state
            value = state.resolveObject(value,ctx=ctx)
            for v in value:
                r.setTo(v)
                ret.append(r.copy())
                r.increment()

    return ret
