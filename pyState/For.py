import logging
import z3
import ast
import pyState.Compare
import pyState
from pyObjectManager.List import List
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
from pyObjectManager.Char import Char
from copy import deepcopy

logger = logging.getLogger("pyState:For")


def handle(state,element):
    """
    Attempt to handle the For element
    """
    assert type(element) is ast.For
 
    # The For element is an iterator that sets variables
    iterator = element.iter
    target = element.target
    
    # Resolve our iter first
    newIter = state.resolveObject(iterator)
    
    # Keep track of if we're just repeating a loop
    newLoop = True if newIter != iterator else False
    
    # If it's a new loop, work on a copy not the real thing
    if newLoop:
        newIter = state.recursiveCopy(newIter)

    # If we're making a call, we need to pause here
    if type(newIter) == pyState.ReturnObject:
        return [state]

    if type(newIter) not in [List, String]:
        err = "handle: I don't know how to handle iter type {0}".format(type(newIter))
        logger.error(err)
        raise Exception(err)

    # Moving forward
    state.path.pop(0)

    # Assuming it's a list for now

    # If we're out of things to iterate, take the else
    if newIter.length() == 0:
        cs = deepcopy(state.path)
        if len(cs) > 0:
            state.pushCallStack(path=cs)
        
        # else side should be done with the loop
        state.loop = None
        state.path = element.orelse
        return [state]
        
    # If we're here, we have something left to do
    # Pop the current iter value
    elm = newIter.pop(0)

    # Set the iter back
    element.iter = newIter

    # Setup our callstack for this loop
    cs = deepcopy(state.path)

    # Don't want to push an empth path into call stack for now
    # If this is a new loop, save the previous info
    # TODO: Kinda hackish..
    if newLoop:
        if len(cs) ==  0:
            cs.append(ast.Pass(lineno=0,col_offset=0))
        state.pushCallStack(path=cs)

    # Our new path becomes the inside of the if statement
    state.path = element.body

    # If state should get a copy of the loop we're now in
    state.loop = element # deepcopy(element)


    # Create the target var
    t, kwargs = pyState.duplicateSort(elm)
    target = state.resolveObject(target,varType=t,kwargs=kwargs)
    target.increment()

    if type(target) in [Int, Real, BitVec, Char]:
        # Copy the constraint
        state.addConstraint(target.getZ3Object() == elm.getZ3Object())
    
    else:
        err = "handle: I don't know how to handle target type {0}".format(type(target))
        logger.error(err)
        raise Exception(err)

    return [state]

