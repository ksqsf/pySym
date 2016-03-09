import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:Return")

def handle(state,element):
    """
    Input:
        state = State object
        element = ast.Return element to parse
    Action:
        Sets return variable as applicable
    Returns:
        Nothing for now
    """
    
    assert type(state) == pyState.State
    assert type(element) == ast.Return

    state.Return(element)

    """
    else:
        err = "Expr: Don't know how to handle expr type {0} at line {1} col {2}".format(type(expr),expr.lineno,expr.col_offset)
        logger.error(err)
        raise Exception(err)
    """
