def handle(state,call,s):
    """
    Pretend to print stuff
    """
    
    print(state.any_int(state.resolveObject(s)))
