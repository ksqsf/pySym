import logging
import z3
import ast
from pyState import hasRealComponent, ReturnObject, z3Helpers
from pySym import pyState.z3Helpers
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String

logger = logging.getLogger("pyState:AugAssign")

def _handleNum(state,element,value,op):
    """
    Handle the case where we're AugAssigning numbers
    """

    # Find the parent object
    oldTargets = state.resolveObject(element.target)

    # Normalize
    oldTargets = [oldTargets] if type(oldTargets) is not list else oldTargets

    # Resolve calls if we need to
    retObjs = [x for x in oldTargets if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    ret = []

    # Loop through resolved objects
    for oldTarget in oldTargets:
        parent = state.objectManager.getParent(oldTarget)
        index = parent.index(oldTarget)
    
        # Basic sanity checks complete. For augment assigns we will always need to update the vars.
        # Grab the old var and create a new now
        #oldTargetVar = oldTarget.getZ3Object()

        # Match up the right hand side
        oldTargetVar, valueVar = z3Helpers.z3_matchLeftAndRight(oldTarget,value,op)
    
        if hasRealComponent(valueVar) or hasRealComponent(oldTargetVar):
            parent[index] = Real(oldTarget.varName,ctx=state.ctx,state=state)
            #newTargetVar = parent[index].getZ3Object(increment=True)

        elif type(valueVar) in [z3.BitVecRef,z3.BitVecNumRef]:
            parent[index] = BitVec(oldTarget.varName,ctx=state.ctx,size=valueVar.size(),state=state)
            #newTargetVar = parent[index].getZ3Object(increment=True)
    
        else:
            parent[index] = Int(oldTarget.varName,ctx=state.ctx,state=state)
            #newTargetVar = parent[index].getZ3Object(increment=True)

        newTargetObj = parent[index]
        newTargetObj.increment()
        newTargetVar = newTargetObj.getZ3Object()

        # Figure out what the op is and add constraint
        if type(op) == ast.Add:
            if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
                # Check for over and underflows
                state.solver.add(pyState.z3Helpers.bvadd_safe(oldTargetVar,valueVar))

            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() + value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar + valueVar)
    
        elif type(op) == ast.Sub:
            if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
                # Check for over and underflows
                state.solver.add(pyState.z3Helpers.bvsub_safe(oldTargetVar,valueVar))

            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() - value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar - valueVar)
    
        elif type(op) == ast.Mult:
            if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
                # Check for over and underflows
                state.solver.add(pyState.z3Helpers.bvmul_safe(oldTargetVar,valueVar))

            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() * value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar * valueVar)
    
        elif type(op) == ast.Div:
            if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
                # Check for over and underflows
                state.solver.add(pyState.z3Helpers.bvdiv_safe(oldTargetVar,valueVar))

            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() / value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar / valueVar)
    
        elif type(op) == ast.Mod:
            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() % value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar % valueVar)
    
        elif type(op) == ast.BitXor:
            logger.debug("{0} = {1} ^ {2}".format(newTargetVar,oldTargetVar,valueVar))
            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() ^ value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar ^ valueVar)
    
        elif type(op) == ast.BitOr:
            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() | value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar | valueVar)
    
        elif type(op) == ast.BitAnd:
            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() & value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar & valueVar)
    
        elif type(op) == ast.LShift:
            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() << value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar << valueVar)
    
        elif type(op) == ast.RShift:
            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() >> value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar >> valueVar)

        # TODO: This will fail with BitVec objects...
        elif type(op) == ast.Pow:
            # Keep clutter out of z3
            if oldTarget.isStatic() and value.isStatic():
                newTargetObj.setTo(oldTarget.getValue() ** value.getValue())
            else:
                state.addConstraint(newTargetVar == oldTargetVar ** valueVar)

        else:
            err = "Don't know how to handle op type {0} at line {1} col {2}".format(type(op),op.lineno,op.col_offset)
            logger.error(err)
            raise Exception(err)

        ret.append(state)

    # Pop the instruction off
    state.path.pop(0)

    # Return the state
    return ret

def _handleString(state,element,value,op):
    """
    Handle the case where we're AugAssigning Strings
    """

    # Find the parent object
    oldTargets = state.resolveObject(element.target)

    # Normalize
    oldTargets = [oldTargets] if type(oldTargets) is not list else oldTargets

    # Resolve calls if we need to
    retObjs = [x for x in oldTargets if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    ret = []

    state.path.pop(0)

    # Loop through possible old targets
    
    for oldTarget in oldTargets:

        parent = state.objectManager.getParent(oldTarget)
        index = parent.index(oldTarget)

        # Create a new string
        newString = state.getVar("AugAssignTempString",ctx=1,varType=String)
        newString.increment()
    
        # Set the new string
        newString.variables = oldTarget.variables + value.variables

        # Assign the new string
        parent[index] = newString.copy()

        ret.append(state.copy())

    # Return the state
    return ret


def handle(state,element):
    """Attempt to handle the Python AugAssign element
    
    Parameters
    ----------
    state : pyState.State
        pyState.State object to handle this element under
    element : ast.AugAssign
        element from source to be handled

    Returns
    -------
    list
        list contains state objects either generated or discovered through
        handling this ast.

    
    This function handles calls to AugAssign. It is not meant to be called
    manually via a user.


    Example
    -------
    Example of ast.Assign is: x += 1
    """

    # Value is what to set them to
    value = state.resolveObject(element.value)
    
    # Normalize the input
    values = [value] if type(value) is not list else value
    
    # Check for return object. Return all applicable
    retObjs = [x.state for x in values if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        return retObjs

    # The operations to do (Add/Mul/etc)
    op = element.op    

    ret = []

    # Loop through possible values, creating states as we go
    for value in values:

        if type(value) in [Int, BitVec, Real]:
            ret += _handleNum(state.copy(),element,value,op)

        elif type(value) is String:
            ret += _handleString(state.copy(),element,value,op)

        else:
            err = "handle: Don't know how to handle type {0}".format(type(value))
            logger.error(err)
            raise Exception(err)

    return ret
