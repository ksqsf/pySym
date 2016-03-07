import logging
import z3
import ast

logger = logging.getLogger("pyState:If")


def handle(state,element):
    """
    Attempt to handle the if element
    Not handling else at the moment
    """

    # Check what type of test this is    
    if type(element.test) == ast.Compare:
        # Do stuff

    else:
        logger.error("handle: I don't know how to handle type {0}".format(type(element.test)))
    
