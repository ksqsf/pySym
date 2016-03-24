import logging
import z3
import ast
from pyState import hasRealComponent, ReturnObject, z3Helpers
import pyState.z3Helpers
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec


logger = logging.getLogger("pyState:AugAssign")

def handle(state,element):
    """
    Attempt to handle the AugAssign element
    Example of this: x += 1
    """
    # Value is what to set them to
    value = state.resolveObject(element.value)
        
    # Check if we're making a call and need to wait for that to finish
    if type(value) == ReturnObject:
        return [state]

    # The operations to do (Add/Mul/etc)
    op = element.op    

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
