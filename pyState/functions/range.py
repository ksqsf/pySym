from copy import deepcopy
from pyObjectManager.List import List
from pyObjectManager.Int import Int

def handle(state,call,a,b=None,c=None,ctx=None):
    """
    Simulate range funcion
    """
    ctx = ctx if ctx is not None else state.ctx

    # Resolve the vars
    a = state.resolveObject(a,ctx=ctx)
    b = state.resolveObject(b,ctx=ctx) if b is not None else None
    c = state.resolveObject(c,ctx=ctx) if c is not None else None

    ##############
    # a Concrete #
    ##############

    if type(a) not in [int,type(None)]:
        if a.isStatic():
            a = a.value

        # Check if it's a variable that only has one possibility
        elif type(a) in [Int, BitVec] and len(state.any_n_int(a,2)) == 1:
            a = state.any_int(a)

        else:
            err = "handle: Don't know how to handle symbolic integers at the moment"
            logger.error(err)
            raise Exception(err)


    ##############
    # b Concrete #
    ##############

    if type(b) not in [int,type(None)]:
        if b.isStatic():
            b = b.value

        # Check if it's a variable that only has one possibility
        elif type(b) in [Int, BitVec] and len(state.any_n_int(b,2)) == 1:
            b = state.any_int(b)

        else:
            err = "handle: Don't know how to handle symbolic integers at the moment"
            logger.error(err)
            raise Exception(err)


    ##############
    # c Concrete #
    ##############

    if type(c) not in [int,type(None)]:
        if c.isStatic():
            c = c.value

        # Check if it's a variable that only has one possibility
        elif type(c) in [Int, BitVec] and len(state.any_n_int(c,2)) == 1:
            lower = state.any_int(c)

        else:
            err = "handle: Don't know how to handle symbolic integers at the moment"
            logger.error(err)
            raise Exception(err)


    # Create the return List object
    out = state.getVar("range",ctx=1,varType=List)
    out.increment()
    
    if b == None:
        rangeOut = range(a)

    elif c == None:
        rangeOut = range(a,b)

    else:
        rangeOut = range(a,b,c)
    
    # Copy the output
    for var in rangeOut:
        out.append(Int,kwargs={'value':var})
    
    # Return a copy
    return out.copy()
        
