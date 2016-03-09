import logging
import z3, z3util
import ast
from . import BinOp, hasRealComponent

logger = logging.getLogger("pyState:Assign")


def _handleAssignNum(state,target,value):
    """
    Handle assigning a number to a variable (i.e.: x = 1)
    Update local variable dict and return
    value should already be resolved via state.resolveObject (meaning it is now an expression)
    """
    # The "x" part of "x" = 1
    varName = target.id

    # Check if we have any Real vars to create the correct corresponding value (z3 doesn't mix types well)
    if hasRealComponent(value):
        x = state.getZ3Var(varName,increment=True,varType=z3.RealSort())

    else: 
        x = state.getZ3Var(varName,increment=True,varType=z3.IntSort())

    state.addConstraint(x == value)


def handle(state,element):
    """
    Attempt to handle the assign element
    """
    
    # Targets are what is being set
    targets = element.targets

    # Value is what to set them to
    value = element.value

    # Only handling single targets for now
    if len(targets) != 1:
        err = "Cannot handle multiple variable set at Line {0} Col {1}".format(element.lineno,element.col_offset)
        logger.error(err)
        raise Exception(err)

    # Clear up the naming
    target = targets[0]

    # Call appropriate handlers
    if type(value) in [ast.Num, ast.Name, ast.BinOp]:
        _handleAssignNum(state,target,state.resolveObject(value))

    else:
        err = "Don't know how to assign type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
        logger.error(err)
        raise Exception(err)

