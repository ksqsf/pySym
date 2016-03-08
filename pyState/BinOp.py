import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:BinOp")

def handle(state,element):
    """
    Input:
        state = State object
        element = ast.BinOp element to parse
    Action:
        Parse out the element with respect to the state
    Returns:
        Z3 constraint representing this BinOp
    """
    
    assert type(state) == pyState.State
    assert type(element) == ast.BinOp

    # Try resolving the parts
    left = state.resolveObject(element.left)
    right = state.resolveObject(element.right)
    op = element.op

    # Figure out what the op is and add constraint
    if type(op) == ast.Add:
        return left + right

    elif type(op) == ast.Sub:
        return left - right

    elif type(op) == ast.Mult:
        return left * right

    elif type(op) == ast.Div:
        return left / right

    elif type(op) == ast.Mod:
        return left % right

    else:
        err = "BinOP: Don't know how to handle op type {0} at line {1} col {2}".format(type(op),op.lineno,op.col_offset)
        logger.error(err)
        raise Exception(err)

