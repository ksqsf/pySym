
import z3
import ast
from pyObjectManager.Int import Int

def handle(state,call):
    """
    Returns an Int object. Use this to inform pySym that something should be Int symbolic
    """

    myInt = state.resolveObject(ast.Name('temp',0),ctx=1,varType=Int)

    return myInt
