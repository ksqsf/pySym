import logging
import z3
import ast
import pyState
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String
from pyObjectManager.List import List
from copy import deepcopy

logger = logging.getLogger("pyState:BinOp")

def _handleNum(state,left,right,op):
    # Match our object types
    leftZ3Object,rightZ3Object = pyState.z3Helpers.z3_matchLeftAndRight(left,right,op)

    # Figure out what the op is and add constraint
    if type(op) == ast.Add:
        if type(left) is BitVec:
            # Check for over and underflows
            state.solver.add(pyState.z3Helpers.bvadd_safe(leftZ3Object,rightZ3Object))
        ret = leftZ3Object + rightZ3Object

    elif type(op) == ast.Sub:
        if type(left) is BitVec:
            state.solver.add(pyState.z3Helpers.bvsub_safe(leftZ3Object,rightZ3Object))
        ret = leftZ3Object - rightZ3Object

    elif type(op) == ast.Mult:
        if type(left) is BitVec:
            state.solver.add(pyState.z3Helpers.bvmul_safe(leftZ3Object,rightZ3Object))
        ret = leftZ3Object * rightZ3Object

    elif type(op) == ast.Div:
        if type(left) is BitVec:
            state.solver.add(pyState.z3Helpers.bvdiv_safe(leftZ3Object,rightZ3Object))
        ret = leftZ3Object / rightZ3Object

    elif type(op) == ast.Mod:
        ret = leftZ3Object % rightZ3Object

    elif type(op) == ast.BitXor:
        ret = leftZ3Object ^ rightZ3Object

    elif type(op) == ast.BitOr:
        ret = leftZ3Object | rightZ3Object

    elif type(op) == ast.BitAnd:
        ret = leftZ3Object & rightZ3Object

    elif type(op) == ast.LShift:
        ret = leftZ3Object << rightZ3Object

    elif type(op) == ast.RShift:
        ret = leftZ3Object >> rightZ3Object

    # TODO: This one will fail if we use BitVecs.. Maybe think about check/convert?
    elif type(op) == ast.Pow:
        ret = leftZ3Object ** rightZ3Object

    else:
        err = "BinOP: Don't know how to handle op type {0} at line {1} col {2}".format(type(op),op.lineno,op.col_offset)
        logger.error(err)
        raise Exception(err)

    # TODO: Clean up code below...
    # Duplicate the object and create a pyObjectManager object
    left_t,left_args = pyState.duplicateSort(leftZ3Object)
    right_t,right_args = pyState.duplicateSort(rightZ3Object)
    if left_t in [Int,Real,BitVec] and right_t in [Int, Real, BitVec]:
        # Not handling this case well right now
        if left_t is Real or right_t is Real:
            args = left_args if left_t is Real else right_args
            # We want variables, not constants
            args.pop("value",None) if args is not None else None
            retVar = state.getVar(varName='BinOpTemp',varType=Real,kwargs = args)

        else:
            left_args.pop("value",None) if left_args is not None else None
            retVar = state.getVar(varName='BinOpTemp',varType=left_t,kwargs = left_args)

        retVar.increment()
        # Now that we have a clean variable to return, add constraints and return it
        logger.debug("Adding constraint {0} == {1}".format(retVar.getZ3Object(),ret))
        state.addConstraint(retVar.getZ3Object() == ret)
        #print([x for x in state.solver.assertions()])
        return [retVar.copy()]

    else:
        err = "BinOP: Don't know how to handle variable type {0} at line {1} col {2}".format(t,op.lineno,op.col_offset)
        logger.error(err)
        raise Exception(err)


def _handleStr(state,left,right,op):
    """
    Handle BinOp for string types
    """
    assert type(left) in [String, Int, BitVec]
    assert type(right) in [String, Int, BitVec]
    
    # Because strings are just class abstractions, we can do this without touching Z3
    s = state.getVar("tempBinOpString",ctx=1,varType=String)
    s.increment()

    ret = []

    # Case: "A" + "B"
    if (type(left) is String and type(right) is String) and type(op) is ast.Add:
        s.variables = left.copy().variables + right.copy().variables
        ret.append(s.copy())

    elif ((set([type(left),type(right)]) == set([String,Int])) or (set([type(left),type(right)]) == set([String,BitVec]))) and type(op) is ast.Mult:
        i = left if type(left) in [Int, BitVec] else right
        oldStr = left if type(left) is String else right
        
        if not i.isStatic():
            err = "_handleStr: Don't know how to handle symbolic mult at the moment"
            logger.error(err)
            raise Exception(err)

        # Solidify it
        i = i.getValue()
        
        # Add the variables
        s.variables = oldStr.copy().variables * i
        
        # Add it to our return list
        ret.append(s.copy())

    else:
        err = "_handleStr: Don't know how to handle {0} {1} {2}".format(type(left),op,type(right))
        logger.error(err)
        raise Exception(err)


    return ret

def _handleList(state,left,right,op):
    """
    Handle BinOp for List types
    """
    assert type(left) in [List, Int, BitVec]
    assert type(right) in [List, Int, BitVec]
    
    # Because Lists are just class abstractions, we can do this without touching Z3
    s = state.getVar("tempBinOpList",ctx=1,varType=List)
    s.increment()

    if type(op) is ast.Add:
        # It's only valid to add two lists together, not list and int
        s.variables = left.copy().variables + right.copy().variables

    elif type(op) is ast.Mult:
        # It's only valid to multiply a list and a number
        assert (type(left) is List and type(right) in [Int, BitVec]) or (type(right) is List and type(left) in [Int, BitVec])

        oldList = left if type(left) is List else right
        myInt = left if type(left) in [Int, BitVec] else right
    
        # TODO: Add symbolic here    
        if not myInt.isStatic():
            err = "_handleList: Don't know how to handle symbolic list multiplication"
            logger.error(err)
            raise Exception(err)

        # Resolve the value
        myIntVal = myInt.getValue()
        
        # Populate the new variable
        s.variables = oldList.variables * myIntVal

    else:
        err = "_handleList: Don't know how to handle op type {0}".format(type(op))
        logger.error(err)
        raise Exception(err)


    return [s.copy()]


def handle(state,element,ctx=None):
    """
    Input:
        state = State object
        element = ast.BinOp element to parse
        (optional) ctx = context to resolve BinOp in if not current
    Action:
        Parse out the element with respect to the state
    Returns:
        pyObjectManager object representing this BinOp
    """
    ctx = state.ctx if ctx is None else ctx
    
    assert type(state) == pyState.State
    assert type(element) == ast.BinOp

    logger.debug("handle: Resolving left {0}".format(element.left))
    
    # Try resolving the parts
    left = state.resolveObject(element.left,parent=element,ctx=ctx)

    # Resolve calls if we need to
    retObjs = [x for x in left if type(x) is pyState.ReturnObject]
    if len(retObjs) > 0:
        logger.debug("handle: Returning retObjs {0}".format(retObjs))
        return retObjs

    # Save a copy so that we don't lose it
    left = [x.copy() for x in left]

    #logger.debug("BinOp: BinOp Left = {0}".format(type(left)))
    right = {}
    
    # Enumate all possible states
    for s in set([x.state for x in left]):
        logger.debug("handle: Resolving right {0}".format(element.right))
        right[s] = [x for x in s.resolveObject(element.right,parent=element,ctx=ctx)]

    # Resolve calls if we need to
    retObjs = [y for x in right.values() for y in x if type(y) is pyState.ReturnObject]
    if len(retObjs) > 0:
        logger.debug("handle: Returning retObjs {0}".format(retObjs))
        return retObjs
    #logger.debug("BinOp: BinOp Right = {0}".format(type(right)))

    op = element.op
    ret = []
    
    # Loop through all possible combinations
    for l in left:
        # Don't want to duplicate states. Thus the dictionary
        for r in right[l.state]:
            if type(l) is List or type(r) is List:
                ret += _handleList(r.state,l,r,op)
        
            elif type(l) is String or type(r) is String:
                ret += _handleStr(r.state,l,r,op)
        
            # TODO: Assuming like types here... Maybe check both left and right?
            elif type(l) in [Int, Real, BitVec]:
                ret += _handleNum(r.state,l,r,op)
    
            else:
                err = "BinOP: Don't know how to handle variable type {0}".format(type(l))
                logger.error(err)
                raise Exception(err)

    # Return our possibilities
    return ret
