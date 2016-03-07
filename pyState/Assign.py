import logging
import z3
import ast

logger = logging.getLogger("pyState:Assign")


def _handleAssignNum(state,target,value):
    """
    Handle assigning a number to a variable (i.e.: x = 1)
    Update local variable dict and return
    """
    # The "x" part of "x" = 1
    varName = target.id

    # Grab the actual value
    valueActual = value.n

    # Right now only know how to deal with int
    if type(valueActual) != int:
        err = "Cannot handle non-int {2} set at line {0} col {1}".format(value.lineno,value.col_offset,type(valueActual))
        logger.error(err)
        raise Exception(err)

    # Create local var if we don't have it already
    # TODO: Something in this if statement is corrupting something.. Double-linked list corruption and python crash on exit
    if varName not in state.localVars:
        state.localVars[varName] = {
            'var': z3.Int(varName),
            'expr': []
        }

    # Since this is a set of a concrete, we throw away the old
    # constraints and just set this new one
    state.localVars[varName]['expr'] = [state.localVars[varName]['var'] == valueActual]


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
    if type(value) == ast.Num:
        _handleAssignNum(state,target,value)

    else:
        err = "Don't know how to assign type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
        logger.error()
        raise Exception(err)

