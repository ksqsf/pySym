import z3
import ast
from pyObjectManager.Real import Real

def handle(state,call,ctx=None):
    """
    Returns a z3 Real object. Use this to inform pySym that something should be Real symbolic
    """
    ctx = ctx if ctx is not None else state.ctx

    myReal = state.resolveObject(ast.Name('temp',0),ctx=1,varType=Real)

    return myReal
