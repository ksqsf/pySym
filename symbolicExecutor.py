import logging
import ast
import Colorer
import z3

logger = logging.getLogger("SymbolicExecutor")

"""
localVars and globalVars are dicts containing variables and their constraint expressions

localVars = {
    'x': {
        'var': x, # This is the actual z3.Int/z3.Array, etc object
        'expr': [
            'localVars['x']['var'] > 1',    # Actual expressions to go into solver
            'localVars['x']['var'] * 5 > 7'
        ]
    }
}
"""

def _handleAssignNum(target,value,localVars,globalVars):
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
        logger.error("Cannot handle non-int {2} set at line {0} col {1}".format(value.lineno,value.col_offset,type(valueActual)))
        exit(1)
    
    # Create local var if we don't have it already
    if varName not in localVars:
        localVars[varName] = {
            'var': z3.Int(varName),
            'expr': []
        }
    
    # Since this is a set of a concrete, we throw away the old
    # constraints and just set this new one
    localVars[varName]['expr'] = ['localVars[\'{0}\'][\'var\'] == {1}'.format(varName,valueActual)]
    
    # Return new vars. Returning both local and global since at some point we might update global from this
    return localVars, globalVars


def handleAssign(element,localVars={},globalVars={}):
    """
    Attempt to handle the assign element
    """
    
    # Targets are what is being set
    targets = element.targets
    
    # Value is what to set them to
    value = element.value
    
    # Only handling single targets for now
    if len(targets) != 1:
        logger.error("Cannot handle multiple variable set at Line {0} Col {1}".format(element.lineno,element.col_offset))
        exit(1)
    
    # Clear up the naming
    target = targets[0]
    
    # Call appropriate handlers
    if type(value) == ast.Num:
        localVars, globalVars = _handleAssignNum(target,value,localVars,globalVars)
    
    else:
        logger.error("Don't know how to assign type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset))
        exit(1)
    
    print(localVars,globalVars)
     
    return localVars, globalVars

def runBody(body):
    """
    Input:
        Body of AST model
    Action:
        Symbolically Execute body
    Return:
        Nothing for now
    """
    
    logger.debug("Parsing Body: {0}".format(body))
    
    # Loop through the elements
    for element in body:
        if type(element) == ast.Assign:
            handleAssign(element)
        else:
            logger.error("Unhandled element of type {0} at Line {1} Col {2}".format(type(element),element.lineno,element.col_offset))
            exit(1)
