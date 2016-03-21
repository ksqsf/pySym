import z3
import ast

def handle(state,var):
    """
    Returns a z3 Real object. Use this to inform pySym that something should be Real symbolic
    """

    assert type(var) is ast.Name
    
    return z3.Real(var.id)
