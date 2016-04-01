def handle(state,call,s,ctx=None):
    """
    Pretend to print stuff
    """
    ctx = ctx if ctx is not None else state.ctx

    
    #print(state.any_int(state.resolveObject(s)))
    print("Hit print statement")
