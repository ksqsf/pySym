import logging
import z3
import ast
import pyState
from copy import deepcopy
import itertools

logger = logging.getLogger("pyState:Call")


def _resolveArgs(state,element):

    ret = []
    # Resolve the args
    for arg in element.args:
        caller_args = state.resolveObject(arg)

        # Normalize
        caller_args = [caller_args] if type(caller_args) is not list else caller_args

        # Check for return object. Return all applicable
        retObjs = [x.state for x in caller_args if type(x) is pyState.ReturnObject]
        if len(retObjs) > 0:
            return retObjs

        
        ret.append(caller_args)

    return itertools.product(*ret)

def _resolveKeywords(state,element):
    ret = []

    for keyword in element.keywords:
        kws = []
        caller_args = state.resolveObject(keyword.value)

        # Normalize
        caller_args = [caller_args] if type(caller_args) is not list else caller_args
        
        # Check for return object. Return all applicable
        retObjs = [x.state for x in caller_args if type(x) is pyState.ReturnObject]
        if len(retObjs) > 0:
            return retObjs

        # Add all of these to a list
        for arg in caller_args:
            kw = deepcopy(keyword)
            kw.value = arg.copy()
            kws.append(kw)

        ret.append(kws)

    return itertools.product(*ret)

def handle(state,element,retObj=None):
    """
    Input:
        state = State object
        element = ast.Call element to parse
        (optional) retObj = ReturnObject to have it's ID filled in
    Action:
        Performs call
    Returns:
        Next instruction block for path object
    """
    
    assert type(state) == pyState.State
    assert type(element) == ast.Call

    argElements = list(_resolveArgs(state,element))
    keywordElements = list(_resolveKeywords(state,deepcopy(element)))
    ret = [] 
    
    # For each possible combination of args
    for arg in argElements:
        
        for keyword in keywordElements:

            # Set the arg list
            elm = deepcopy(element)
            elm.args = arg

            # Set the kwlist
            elm.keywords = keyword

            # Copy state
            s = state.copy()

            # Create our return object (temporary ID to be filled in by the Call handle)
            retObj = pyState.ReturnObject(1)

            # Update state, change call to ReturnObject so we can resolve next time
            assert pyState.replaceObjectWithObject(s.path[0],element,retObj)

            # Ensure everything has a state
            [a.setState(s) for a in elm.args]
            [a.value.setState(s) for a in keyword]


            # Call
            ret += [s.Call(elm,retObj=retObj)]
    
    return ret
    
    """

    else:
        err = "Expr: Don't know how to handle expr type {0} at line {1} col {2}".format(type(expr),expr.lineno,expr.col_offset)
        logger.error(err)
        raise Exception(err)
    """
