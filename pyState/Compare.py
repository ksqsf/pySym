import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:Compare")

def _handleLeftVarInt(state,element,left):
    """
    Input:
        state = State object for the evaluation of the compare
        element = ast element object for the if statement (type ast.If)
        left = Left variable name or int (i.e.: 'x' or 5)
    Action:
        Handle compare where left side is a variable or int
        Note: left is treated as an object and used directly in the constraint.
              therefor it must be either an int or a z3 object type
        ex: if x > 5
    Return:
        Created constraint expressions as a (ifSide,elseSide) tuple, or (ReturnObject, None) if we're waiting on a call
    """

    # Looks like we're making a call, go ahead and return
    if type(left) == pyState.ReturnObject:
        return left, None
    
    # Operators that we're comparing with
    ops = element.ops
    comp = element.comparators
    
    if len(ops) > 1 or len(comp) > 1:
        err = "_handleLeftVar: Don't know how to handle multiple operations '{0}' at line {1} column {2}".format(ops,element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)
    
    ops = ops[0]
    comp = comp[0]
    
    right = state.resolveObject(comp)
    
    # Resolve Call first
    if type(right) == pyState.ReturnObject:
        return right, None

    # Adjust the types if needed
    left,right = pyState.z3Helpers.z3_matchLeftAndRight(left,right,ops)

    logger.debug("_handleLeftVar: Comparing {0} (type: {2}) and {1} (type: {3})".format(left,right,type(left),type(right)))

    # Assume success. Add constraints
    if type(ops) == ast.Gt:
        return left > right, left <= right 
    
    elif type(ops) == ast.GtE:
        return left >= right, left < right

    elif type(ops) == ast.Lt:
        return left < right, left >= right

    elif type(ops) == ast.LtE:
        return left <= right, left > right

    elif type(ops) == ast.Eq:
        return left == right, left != right

    elif type(ops) == ast.NotEq:
        return left != right, left == right

    else:
        err = "_handleLeftVar: Don't know how to handle type '{0}' at line {1} column {2}".format(type(ops),element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)
       
    

def handle(state,element):
    """
    Handle the Compare element (such as <,>,==,etc)
    Input:
        state = state object
    Action:
        Create constraint expression for both True and False state objects
    Return:
        The corresponding z3 constraints as a tuple (true constraints ,false constraints), or (ReturnObject, None) if waiting for a Call
    """
    assert type(element) == ast.Compare
    
    # The left side of the compare
    left = element.left
    
    # TODO: Probably need to add checks or consolidate here...
    return _handleLeftVarInt(state,element,state.resolveObject(left))
