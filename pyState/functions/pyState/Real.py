import z3
import ast
from pyObjectManager.Real import Real

def handle(state):
    """
    Returns a z3 Real object. Use this to inform pySym that something should be Real symbolic
    """

    myReal = state.resolveObject(ast.Name('temp',0),ctx=1,varType=Real)

    return myReal
