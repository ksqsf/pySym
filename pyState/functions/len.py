from pyObjectManager.Int import Int

def handle(state,call,obj,ctx=None):
    """
    Simulate len funcion
    """
    ctx = ctx if ctx is not None else state.ctx

    # Resolve the object
    obj = state.resolveObject(obj,ctx=ctx)
    
    # Just calling the length function on the object..
    l = obj.length()
    
    i = state.getVar("tmpLenValue",ctx=1, varType=Int)
    i.increment()
    
    # Tell Z3 about our value
    state.addConstraint(i.getZ3Object() == l)
    
    return i.copy()
