import logging
import z3
import ast

logger = logging.getLogger("pyState:AugAssign")

def _isRealVal(val):
    """
    Input:
        val = Value to check for real-ness
    Action:
        Determine val type (z3 object, int/float, etc).
    Returns:
        True fif val is of Real type, False otherwise
    """
    t = type(val)

    if t == int:
        return False

    elif t == float:
        return True

    elif t == z3.ArithRef:
        return val.is_real()
    
    else:
        err = "Can't determine if object '{0}' is real type or not".format(val)
        logger.error(err)
        raise Exception(err)


def handle(state,element):
    """
    Attempt to handle the AugAssign element
    Example of this: x += 1
    """
    
    # Targets are what is being set
    target = element.target

    # Value is what to set them to
    value = element.value

    # The operations to do (Add/Mul/etc)
    op = element.op    

    # Only know how to handle name types
    if type(target) == ast.Name:
        # Grab the var name
        target = target.id
    
    else:
        err = "Don't know how to handle target type {0} at line {1} col {2}".format(type(target),target.lineno,target.col_offset)
        logger.error(err)
        raise Exception(err)

    # Figure out value type
    if type(value) == ast.Num:
        value = value.n

    elif type(value) == ast.Name:
        value = state.getZ3Var(value.id)

    else:
        err = "Don't know how to handle value type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
        logger.error(err)
        raise Exception(err)
    
    # Basic sanity checks complete. For augment assigns we will always need to update the vars.
    # Grab the old var and create a new now
    oldTargetVar = state.getZ3Var(target)
    
    # Z3 gets confused if we don't change our var to Real when comparing w/ Real
    if _isRealVal(value):
        newTargetVar = state.getZ3Var(target,increment=True,varType=z3.RealSort())
    else:
        newTargetVar = state.getZ3Var(target,increment=True)
    
    # Figure out what the op is and add constraint
    if type(op) == ast.Add:
        state.addConstraint(newTargetVar == oldTargetVar + value)
    
    elif type(op) == ast.Sub:
        state.addConstraint(newTargetVar == oldTargetVar - value)

    elif type(op) == ast.Mult:
        state.addConstraint(newTargetVar == oldTargetVar * value)
    
    elif type(op) == ast.Div:
        state.addConstraint(newTargetVar == oldTargetVar / value)
    
    elif type(op) == ast.Mod:
        state.addConstraint(newTargetVar == oldTargetVar % value)

    else:
        err = "Don't know how to handle op type {0} at line {1} col {2}".format(type(op),op.lineno,op.col_offset)
        logger.error(err)
        raise Exception(err)

    # Pop the instruction off
    state.path.pop(0)
