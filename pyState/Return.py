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

    ret = state.Return(element)
    
    logger.debug("handle: ret value = {0}".format(ret))

    # Normalize
    ret = [ret] if type(ret) is not list else ret

    # Check for return object. Return all applicable
    retObjs = [x.state for x in ret if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs


    # Good to go, pop back down
    state.popCallStack()

    return [state]
    
    """
    else:
        err = "Expr: Don't know how to handle expr type {0} at line {1} col {2}".format(type(expr),expr.lineno,expr.col_offset)
        logger.error(err)
        raise Exception(err)
    """
