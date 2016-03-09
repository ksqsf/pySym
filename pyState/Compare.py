import logging
import z3
import ast

logger = logging.getLogger("pyState:Compare")

def _handleLeftVarInt(stateTrue,stateFalse,element,left):
    """
    Input:
        stateTrue = State object for the True evaluation of the compare
        stateFalse = State object for the False evaluation of the compare
        element = ast element object for the if statement (type ast.If)
        left = Left variable name or int (i.e.: 'x' or 5)
    Action:
        Handle compare where left side is a variable or int
        Note: left is treated as an object and used directly in the constraint.
              therefor it must be either an int or a z3 object type
        ex: if x > 5
    Return:
        Nothing. Modify state objects in place
    """
    
    # Operators that we're comparing with
    ops = element.ops
    comp = element.comparators
    
    if len(ops) > 1 or len(comp) > 1:
        err = "_handleLeftVar: Don't know how to handle multiple operations '{0}' at line {1} column {2}".format(ops,element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)
    
    ops = ops[0]
    comp = comp[0]
    
    # Determine what's on the right hand side of the compare
    #if type(comp) == ast.Name:
    #    # Right hand side is another variable
    #    right = stateTrue.getZ3Var(comp.id)
    
    #elif type(comp) == ast.Num:
    #    # Right hand side is a number
    #    right = comp.n
    right = stateTrue.resolveObject(comp)

    #else:
    #    err = "_handleLeftVar: Don't know how to handle right-hand type '{0}' at line {1} column {2}".format(type(comp),element.lineno,element.col_offset)
    #    logger.error(err)
    #    raise Exception(err)

    # Assume success. Add constraints
    if type(ops) == ast.Gt:
        stateTrue.addConstraint(left > right )
        stateFalse.addConstraint(left <= right )
    
    elif type(ops) == ast.GtE:
        stateTrue.addConstraint(left >= right )
        stateFalse.addConstraint(left < right )

    elif type(ops) == ast.Lt:
        stateTrue.addConstraint(left < right )
        stateFalse.addConstraint(left >= right )

    elif type(ops) == ast.LtE:
        stateTrue.addConstraint(left <= right )
        stateFalse.addConstraint(left > right )

    elif type(ops) == ast.Eq:
        stateTrue.addConstraint(left == right )
        stateFalse.addConstraint(left != right )

    elif type(ops) == ast.NotEq:
        stateTrue.addConstraint(left != right )
        stateFalse.addConstraint(left == right )

    else:
        err = "_handleLeftVar: Don't know how to handle type '{0}' at line {1} column {2}".format(type(ops),element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)
       
    

def handle(stateTrue,stateFalse,element):
    """
    Handle the Compare element (such as <,>,==,etc)
    Input:
        stateTrue = state object for the True side of the compare
        stateFalse = state object for the False side of the compare
    Action:
        Add constraints to bother True and False state objects
    Return:
        Nothing
    """
    assert type(element) == ast.Compare
    
    # The left side of the compare
    left = element.left
    
    # Make sure we understand how to deal with this
    if type(left) == ast.Name:
        left = stateTrue.getZ3Var(left.id)
        _handleLeftVarInt(stateTrue,stateFalse,element,left)
    
    elif type(left) == ast.Num:
        left = left.n
        _handleLeftVarInt(stateTrue,stateFalse,element,left)
    
    else:
        err = "Unknown type '{0}' at line {1} column {2}".format(type(left),left.lineno,left.col_offset)
        logger.error(err)
        raise Exception(err)
        
