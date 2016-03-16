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
    left = state.resolveObject(element.left,parent=element,ctx=ctx)
    
    logger.debug("BinOp: BinOp Left = {0} Type {1}".format(left,type(left)))
    # If we need to pause to resolve something, pause
    if type(left) == pyState.ReturnObject:
        return left

    
    right = state.resolveObject(element.right,parent=element,ctx=ctx)
    
    logger.debug("BinOp: BinOp Right = {0} Type {1}".format(right,type(right)))

    if type(right) == pyState.ReturnObject:
        return right

    op = element.op

    # Match our object types
    left,right = pyState.z3Helpers.z3_matchLeftAndRight(left,right,op)
    
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

    elif type(op) == ast.BitXor:
        return left ^ right

    elif type(op) == ast.BitOr:
        return left | right

    elif type(op) == ast.BitAnd:
        return left & right

    elif type(op) == ast.LShift:
        return left << right
    
    elif type(op) == ast.RShift:
        return left >> right

    else:
        err = "BinOP: Don't know how to handle op type {0} at line {1} col {2}".format(type(op),op.lineno,op.col_offset)
        logger.error(err)
        raise Exception(err)

