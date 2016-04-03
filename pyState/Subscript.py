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
import itertools

logger = logging.getLogger("pyState:Subscript")

def _handleIndex(state,sub_object,sub_slice):

    if type(sub_object) not in [List, String]:
        err = "handleIndex: Don't know how to subscript type {0}".format(type(sub_object))
        logger.error(err)
        raise Exception(err)

    # Resolve the index value
    sub_indexs = state.resolveObject(sub_slice.value)

    # Normalize
    sub_indexs = [sub_indexs] if type(sub_indexs) is not list else sub_indexs

    # Resolve calls if we need to
    retObjs = [x for x in sub_indexs if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    # Loop through all possible indedxes
    ret = []

    for sub_index in sub_indexs:

        if sub_index.isStatic():
            index = sub_index.getValue()

        # Check if it's a variable that only has one possibility
        elif type(sub_index) in [Int, BitVec] and len(state.any_n_int(sub_index,2)) == 1:
            index = state.any_int(sub_index)

        else:
            err = "handle: Don't know how to handle symbolic slice integers at the moment"
            logger.error(err)
            raise Exception(err)

        ret.append(sub_object[index])

    return ret


def _handleSlice(state,sub_object,sub_slice):

    if type(sub_object) not in [List, String]:
        err = "handleIndex: Don't know how to subscript type {0}".format(sub_object)
        logger.error(err)
        raise Exception(err)

    # Resolve our variables for this
    lowers = state.resolveObject(sub_slice.lower) if sub_slice.lower is not None else None

    lowers = [lowers] if type(lowers) is not list else lowers

    # Resolve calls if we need to
    retObjs = [x.state for x in lowers if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    uppers = state.resolveObject(sub_slice.upper) if sub_slice.upper is not None else None
    
    uppers = [uppers] if type(uppers) is not list else uppers

    # Resolve calls if we need to
    retObjs = [x.state for x in uppers if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    steps = state.resolveObject(sub_slice.step) if sub_slice.step is not None else None
    
    steps = [steps] if type(steps) is not list else steps

    # Resolve calls if we need to
    retObjs = [x.state for x in steps if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    # Loop through all possible combinations
    ret = []

    for upper,lower,step in itertools.product(uppers,lowers,steps):

        ##################
        # Lower Concrete #
        ##################
        # NOTE: Assuming these are going to be Int types. Maybe bad assumption?

        if type(lower) not in [int,type(None)]:
            if lower.isStatic():
                lower = lower.getValue()
    
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
                upper = upper.getValue()
    
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
                step = step.getValue()
    
            else:
                err = "_handleSlice: Don't know how to handle symbolic step slice integers at the moment"
                logger.error(err)
                raise Exception(err)
    
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
    
        if type(sub_object) is List:
            # Get slice
            newObject = state.recursiveCopy(sub_object[lower:upper:step])
    
            j = 0
            for i in range(lower,upper,step):
                if type(sub_object[i]) in [Int, Real, BitVec]:
                    state.addConstraint(newObject[j].getZ3Object() == sub_object[i].getZ3Object())
                else:
                    newObject[j] = state.recursiveCopy(sub_object[i])
                j += 1
    
        elif type(sub_object) is String:
            newObject = sub_object[lower:upper:step].copy()
    
    
        # Return new List
        ret.append(newObject)

    return ret


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

    if type(sub_value) not in [ast.Name,ast.Subscript, ast.Call]:
        err = "handle: Don't know how to handle value type {0}".format(sub_value)
        logger.error(err)
        raise Exception(err)

    sub_objects = state.resolveObject(sub_value,ctx=ctx)

    # Normalize
    sub_objects = [sub_objects] if type(sub_objects) is not list else sub_objects

    # Resolve calls if we need to
    retObjs = [x for x in sub_objects if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    # Gather return list for each of the subobjects

    ret = []

    for sub_object in sub_objects:

        if type(sub_slice) is ast.Index:
            ret += _handleIndex(state,sub_object,sub_slice)

        elif type(sub_slice) is ast.Slice:
            ret += _handleSlice(state,sub_object,sub_slice)

        else:
            err = "handle: Don't know how to handle slice type {0}".format(sub_slice)
            logger.error(err)
            raise Exception(err)

    return ret
