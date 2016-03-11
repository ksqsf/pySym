import logging
import z3
import ast
import pyState
from . import Call

logger = logging.getLogger("pyState:Expr")

def handle(state,element):
    """
    Input:
        state = State object
        element = ast.Expr element to parse
    Action:
        Figure out what to do with this...
    Returns:
        Nothing?
    """
    
    assert type(state) == pyState.State
    assert type(element) == ast.Expr

    # What is this expression?
    value = element.value

    # Pop instruction 
    state.path.pop(0)
    
    if type(value) == ast.Call:
        Call.handle(state,value)
        return [state]

    else:
        err = "Expr: Don't know how to handle expr type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
        logger.error(err)
        raise Exception(err)
    
