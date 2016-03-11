import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:Pass")

def handle(state,element):
    """
    Input:
        state = State object
        element = ast.Return element to parse
    Action:
        Increments instruction :-)
    Returns:
        Nothing
    """
    
    state.path.pop(0)
    
    return [state]
