import logging
import z3
import ast

logger = logging.getLogger("pyState:Compare")

def _handleLeftVar(state,element,left):
    """
    Input:
        state = State object to work with
        element = ast element object for the if statement (type ast.If)
        left = Left variable name (i.e.: 'x')
    Action:
        Handle compare where left side is a variable
        ex: if x > 5
    Return:
        Nothing. Modify state object in place
    """
    
    # Operators that we're comparing with
    ops = element.ops
    comp = element.comparators
    
    if len(ops) > 1 or len(comp) > 1:
        err = "Don't know how to handle multiple operations '{0}' at line {1} column {2}".format(ops,element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)
    
    ops = ops[0]
    comp = comp[0]
    
    
    


def handle(state,element):
    """
    Handle the Compare element (such as <,>,==,etc)
    """
    assert type(element) == ast.Compare
    
    # The left side of the compare
    left = element.left
    
    # Make sure we understand how to deal with this
    if type(left) == ast.Name:
        left = left.id
        _handleLeftVar(state,element,left)
    
    else:
        err = "Unknown type '{0}' at line {1} column {2}".format(type(left),left.lineno,left.col_offset)
        logger.error(err)
        raise Exception(err)
        
