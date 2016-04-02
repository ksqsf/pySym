import logging
import z3
import ast
from pyState import hasRealComponent, ReturnObject, z3Helpers
import pyState.z3Helpers
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
    oldTarget = state.resolveObject(element.target)
    parent = state.objectManager.getParent(oldTarget)
    index = parent.index(oldTarget)


    # Basic sanity checks complete. For augment assigns we will always need to update the vars.
    # Grab the old var and create a new now
    oldTargetVar = oldTarget.getZ3Object()

    # Match up the right hand side
    oldTargetVar, valueVar = z3Helpers.z3_matchLeftAndRight(oldTargetVar,value.getZ3Object(),op)
    
    if hasRealComponent(valueVar) or hasRealComponent(oldTargetVar):
        parent[index] = Real(oldTarget.varName,ctx=state.ctx)
        newTargetVar = parent[index].getZ3Object(increment=True)

    elif type(valueVar) in [z3.BitVecRef,z3.BitVecNumRef]:
        parent[index] = BitVec(oldTarget.varName,ctx=state.ctx,size=valueVar.size())
        newTargetVar = parent[index].getZ3Object(increment=True)

    else:
        parent[index] = Int(oldTarget.varName,ctx=state.ctx)
        newTargetVar = parent[index].getZ3Object(increment=True)

    # Figure out what the op is and add constraint
    if type(op) == ast.Add:
        if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
            # Check for over and underflows
            state.solver.add(pyState.z3Helpers.bvadd_safe(oldTargetVar,valueVar))
        state.addConstraint(newTargetVar == oldTargetVar + valueVar)

    elif type(op) == ast.Sub:
        if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
            # Check for over and underflows
            state.solver.add(pyState.z3Helpers.bvsub_safe(oldTargetVar,valueVar))
        state.addConstraint(newTargetVar == oldTargetVar - valueVar)

    elif type(op) == ast.Mult:
        if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
            # Check for over and underflows
            state.solver.add(pyState.z3Helpers.bvmul_safe(oldTargetVar,valueVar))
        state.addConstraint(newTargetVar == oldTargetVar * valueVar)

    elif type(op) == ast.Div:
        if type(newTargetVar) in [z3.BitVecRef, z3.BitVecNumRef]:
            # Check for over and underflows
            state.solver.add(pyState.z3Helpers.bvdiv_safe(oldTargetVar,valueVar))
        state.addConstraint(newTargetVar == oldTargetVar / valueVar)

    elif type(op) == ast.Mod:
        state.addConstraint(newTargetVar == oldTargetVar % valueVar)

    elif type(op) == ast.BitXor:
        logger.debug("{0} = {1} ^ {2}".format(newTargetVar,oldTargetVar,valueVar))
        state.addConstraint(newTargetVar == oldTargetVar ^ valueVar)

    elif type(op) == ast.BitOr:
        state.addConstraint(newTargetVar == oldTargetVar | valueVar)

    elif type(op) == ast.BitAnd:
        state.addConstraint(newTargetVar == oldTargetVar & valueVar)

    elif type(op) == ast.LShift:
        state.addConstraint(newTargetVar == oldTargetVar << valueVar)

    elif type(op) == ast.RShift:
        state.addConstraint(newTargetVar == oldTargetVar >> valueVar)

    # TODO: This will fail with BitVec objects...
    elif type(op) == ast.Pow:
        state.addConstraint(newTargetVar == oldTargetVar ** valueVar)

    else:
        err = "Don't know how to handle op type {0} at line {1} col {2}".format(type(op),op.lineno,op.col_offset)
        logger.error(err)
        raise Exception(err)

    # Pop the instruction off
    state.path.pop(0)

    # Return the state
    return [state]

def _handleString(state,element,value,op):
    """
    Handle the case where we're AugAssigning Strings
    """

    # Find the parent object
    oldTarget = state.resolveObject(element.target)
    parent = state.objectManager.getParent(oldTarget)
    index = parent.index(oldTarget)

    # Create a new string
    newString = state.getVar("AugAssignTempString",ctx=1,varType=String)
    newString.increment()
    
    # Set the new string
    newString.variables = oldTarget.variables + value.variables

    # Assign the new string
    parent[index] = newString.copy()

    # Pop the instruction off
    state.path.pop(0)

    # Return the state
    return [state]


def handle(state,element):
    """
    Attempt to handle the AugAssign element
    Example of this: x += 1
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
