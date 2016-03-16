import logging
import z3
import ast
import pyState

logger = logging.getLogger("pyState:Break")

def handle(state,element):
    """
    Input:
        state = State object
        element = ast.Break element to parse
    Action:
        Pops off CallStack, effectively Breaking out of it's current function.
    Returns:
        Nothing for now
    """
    
    assert type(state) == pyState.State
    assert type(element) == ast.Break

    # We could be in a few levels of if/else statements. Pop back up to the loop
    while state.loop == None:
        state.popCallStack()

    # Good to go, pop out of our loop
    state.popCallStack()

    return [state]
    
