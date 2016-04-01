import logging
import z3
import ast
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List
import pyState
import pyState.ListComp

logger = logging.getLogger("pyState:GeneratorExp")

#import astunparse


def handle(state,element,ctx=None):
    """
    For now, we're just changing GeneratorExp into a list comprehension.
    """
    assert type(element) is ast.GeneratorExp

    ctx = state.ctx if ctx is None else ctx

    # NOTE: Maybe there are cases where we don't want the GeneratorExp to be turned into ListComp?

    # Create a skelleton ListComp
    listComp = ast.parse("[x for x in []]").body[0].value

    # Pop in our generator
    listComp.generators = element.generators
    
    # Pop in our element
    listComp.elt = element.elt

    # Make the switch
    pyState.replaceObjectWithObject(state.path[0],element,listComp)

    #print(astunparse.unparse(element))
    #print(astunparse.unparse(listComp))

    # Call ListComp to handle this
    return pyState.ListComp.handle(state,listComp,ctx=ctx)


