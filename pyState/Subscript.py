import logging
import z3
import ast
import pyState
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List
from pyObjectManager.String import String
from copy import deepcopy

logger = logging.getLogger("pyState:Subscript")

def _handleIndex(state,sub_object,sub_slice):

    if type(sub_object) not in [List, String]:
        err = "handleIndex: Don't know how to subscript type {0}".format(type(sub_object))
        logger.error(err)
        raise Exception(err)

    # Resolve the index value
    sub_index = state.resolveObject(sub_slice.value)

    if sub_index.isStatic():
        index = sub_index.getValue()

    # Check if it's a variable that only has one possibility
    elif type(sub_index) in [Int, BitVec] and len(state.any_n_int(sub_index,2)) == 1:
        index = state.any_int(sub_index)

    else:
        err = "handle: Don't know how to handle symbolic slice integers at the moment"
        logger.error(err)
        raise Exception(err)

    return sub_object[index]


def _handleSlice(state,sub_object,sub_slice):

    if type(sub_object) is not List:
        err = "handleIndex: Don't know how to subscript type {0}".format(sub_object)
        logger.error(err)
        raise Exception(err)

    # Resolve our variables for this
    lower = state.resolveObject(sub_slice.lower) if sub_slice.lower is not None else None

    if type(lower) is pyState.ReturnObject:
        return [state]

    upper = state.resolveObject(sub_slice.upper) if sub_slice.upper is not None else None
    
    if type(upper) is pyState.ReturnObject:
        return [state]

    step = state.resolveObject(sub_slice.step) if sub_slice.step is not None else None
    
    if type(step) is pyState.ReturnObject:
        return [state]

    ##################
    # Lower Concrete #
    ##################
    # NOTE: Assuming these are going to be Int types. Maybe bad assumption?

    if type(lower) not in [int,type(None)]:
        if lower.isStatic():
            lower = lower.value
    
        # Check if it's a variable that only has one possibility
        elif type(lower) in [Int, BitVec] and len(state.any_n_int(lower,2)) == 1:
            lower = state.any_int(lower)
    
        else:
            err = "_handleSlice: Don't know how to handle symbolic lower slice integers at the moment"
            logger.error(err)
            raise Exception(err)

    ##################
    # Upper Concrete #
    ##################
    # NOTE: Assuming these are going to be Int types. Maybe bad assumption?

    if type(upper) not in [int,type(None)]:
        if upper.isStatic():
            upper = upper.value

        # Check if it's a variable that only has one possibility
        elif type(upper) in [Int, BitVec] and len(state.any_n_int(upper,2)) == 1:
            upper = state.any_int(upper)

        else:
            err = "_handleSlice: Don't know how to handle symbolic upper slice integers at the moment"
            logger.error(err)
            raise Exception(err)

    #################
    # Step Concrete #
    #################
    # NOTE: Assuming these are going to be Int types. Maybe bad assumption?

    if type(step) not in [int,type(None)]:
        if step.isStatic():
            step = step.value

        # Check if it's a variable that only has one possibility
        elif type(step) in [Int, BitVec] and len(state.any_n_int(step,2)) == 1:
            step = state.any_int(step)

        else:
            err = "_handleSlice: Don't know how to handle symbolic step slice integers at the moment"
            logger.error(err)
            raise Exception(err)

    # Get slice
    newList = state.recursiveCopy(sub_object[lower:upper:step])
    
    step = 1 if step is None else step
    
    if lower is None:
        if step > 0:
            lower = 0
        else:
            lower = -1

    if upper is None:
        if step > 0:
            upper = sub_object.length()
        else:
            upper = -sub_object.length() - 1

    j = 0
    for i in range(lower,upper,step):
        if type(sub_object[i]) in [Int, Real, BitVec]:
            state.addConstraint(newList[j].getZ3Object() == sub_object[i].getZ3Object())
        else:
            newList[j] = state.recursiveCopy(sub_object[i])
        j += 1


    # Return new List
    return newList


def handle(state,element,ctx=None):
    """
    Input:
        state = State object
        element = ast.Subscript element to parse
        (optional) ctx = context to resolve subscript in if not current
    Action:
        Parse out the subscript. Return element type expected. If this is an
        index, that means the element itself. If it's a range, that means a list
    Returns:
        Subscript resolved element (optionally as (element, parent))
    """
    ctx = state.ctx if ctx is None else ctx
    
    assert type(state) == pyState.State
    assert type(element) == ast.Subscript

    sub_slice = element.slice
    sub_value = element.value

    if type(sub_value) not in [ast.Name,ast.Subscript]:
        err = "handle: Don't know how to handle value type {0}".format(sub_value)
        logger.error(err)
        raise Exception(err)

    sub_object = state.resolveObject(sub_value,ctx=ctx)

    if type(sub_slice) is ast.Index:
        return _handleIndex(state,sub_object,sub_slice)

    elif type(sub_slice) is ast.Slice:
        return _handleSlice(state,sub_object,sub_slice)

    else:
        err = "handle: Don't know how to handle slice type {0}".format(sub_slice)
        logger.error(err)
        raise Exception(err)

