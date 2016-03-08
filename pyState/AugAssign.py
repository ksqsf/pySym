import logging
import z3
import ast

logger = logging.getLogger("pyState:AugAssign")


def _handleAssignNum(state,target,value):
    """
    Handle assigning a number to a variable (i.e.: x = 1)
    Update local variable dict and return
    """
    # The "x" part of "x" = 1
    varName = target.id

    # Grab the actual value
    valueActual = value.n

    # Right now only know how to deal with int
    if type(valueActual) not in [int,float]:
        err = "Cannot handle non-int {2} set at line {0} col {1}".format(value.lineno,value.col_offset,type(valueActual))
        logger.error(err)
        raise Exception(err)

    # Set up temporary variable to create expression
    if type(valueActual) == int:
        #x = z3.Int(varName)
        #varType = "z3.Int('{0}')".format(varName)
        x = state.getZ3Var(varName,increment=True,varType=z3.IntSort())

    elif type(valueActual) == float:
        #x = z3.Real(varName)
        #varType = "z3.Real('{0}')".format(varName)
        x = state.getZ3Var(varName,increment=True,varType=z3.RealSort())

    else:
        err = "Unknown value type {2} set at line {0} col {1}".format(value.lineno,value.col_offset,type(valueActual))
        logger.error(err)
        raise Exception(err)

    state.addConstraint(x == valueActual) #,assign=True,varType=varType,varName=varName)


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

    # Call appropriate handlers
    if type(value) == ast.Num:
        value = value.n

    else:
        err = "Don't know how to handle value type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
        logger.error(err)
        raise Exception(err)
    
    # Basic sanity checks complete. For augment assigns we will always need to update the vars.
    # Grab the old var and create a new now
    oldTargetVar = state.getZ3Var(target)
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

