import logging
import z3
import ast
import pyState.Compare

logger = logging.getLogger("pyState:If")


def handle(stateTrue,stateFalse,element):
    """
    Attempt to handle the if element
    Not handling else at the moment
    """

    # Check what type of test this is    
    if type(element.test) == ast.Compare:
        pyState.Compare.handle(stateTrue,stateFalse,element.test)

    else:
        logger.error("handle: I don't know how to handle type {0}".format(type(element.test)))
    
