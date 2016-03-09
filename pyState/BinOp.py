import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:BinOp")

def handle(state,element,ctx=None):
    """
    Input:
        state = State object
        element = ast.BinOp element to parse
        (optional) ctx = context to resolve BinOp in if not current
    Action:
        Parse out the element with respect to the state
    Returns:
        Z3 constraint representing this BinOp
    """
    ctx = state.ctx if ctx is None else ctx
    
    assert type(state) == pyState.State
    assert type(element) == ast.BinOp

    # Try resolving the parts
    left = state.resolveObject(element.left,ctx=ctx)
    right = state.resolveObject(element.right,ctx=ctx)
    op = element.op
    
    # Due to Z3 qirk, we need to cast vars to Real if one var is a float
    #if type(left) == float and type(right) == z3.ArithRef and right.is_int():
    #    right = z3.ToReal(right)
    #elif type(right) == float and type(left) == z3.ArithRef and left.is_int():
    #    left = z3.ToReal(left)

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

