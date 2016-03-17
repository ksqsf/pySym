import logging
import z3
import ast
import pyState
import pyState.Compare

logger = logging.getLogger("pyState:BoolOp")

def handle(state, element):
    """
    Handle the Compare elements (such as <,>,==,etc)
    BoolOp is "x == 1 and y == 2" type commands
    Input:
        state = state object
    Action:
        Generate appropriate constraint objects
    Return:
        Return the constraint objects (ifSide, elseSide) or (ReturnObject, None)
    """

    assert type(element) == ast.BoolOp
    
    op = element.op

    values = element.values
    
    # Keep track of them in a list
    ifSideConstraints = []
    elseSideConstraints = []

    # Loop through our requested checks
    for value in values:
        if type(value) is ast.Compare:
            ifSide, elseSide = pyState.Compare.handle(state,value)

            # If we need to resolve a call, wait
            if type(ifSide) == pyState.ReturnObject:
                return ifSide, None
            
            # Add these to our list
            ifSideConstraints.append(ifSide)
            elseSideConstraints.append(elseSide)

        else:
            err = "handle: Don't know how to handle type '{0}' at line {1} column {2}".format(type(value),value.lineno,value.col_offset)
            logger.error(err)
            raise Exception(err)


    # Change the checks into a Z3 Expression
    if type(op) is ast.And:
        ifSide = z3.And(ifSideConstraints)
        elseSide = z3.And(elseSideConstraints)
        return ifSide, elseSide
    
    elif type(op) is ast.Or:
        ifSide = z3.Or(ifSideConstraints)
        elseSide = z3.Or(elseSideConstraints)
        return ifSide, elseSide

    else:
        err = "handle: Don't know how to handle op type '{0}' at line {1} column {2}".format(type(op),element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)

