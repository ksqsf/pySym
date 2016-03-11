import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:FunctionDef")

def handle(state,element):
    """
    Input:
        state = State object
        element = ast.FunctionDef element to parse
    Action:
        Sore the function delcaration
    Returns:
        Nothing
    """
    
    assert type(state) == pyState.State
    assert type(element) == ast.FunctionDef
    
    state.registerFunction(element)
    
    # Pop instruction
    state.path.pop(0)
    
    # Return state
    return [state]
