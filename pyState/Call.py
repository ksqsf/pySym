import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:Call")

def handle(state,element,retID=None):
    """
    Input:
        state = State object
        element = ast.Call element to parse
        (optional) retID = Return call ID
    Action:
        Performs call
    Returns:
        Next instruction block for path object
    """
    
    assert type(state) == pyState.State
    assert type(element) == ast.Call

    return state.Call(element,retID=retID)

    """
    else:
        err = "Expr: Don't know how to handle expr type {0} at line {1} col {2}".format(type(expr),expr.lineno,expr.col_offset)
        logger.error(err)
        raise Exception(err)
    """
