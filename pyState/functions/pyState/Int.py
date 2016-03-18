
import z3
import ast

def handle(state,var):
    """
    Returns an Int object. Use this to inform pySym that something should be Int symbolic
    """

    assert type(var) is ast.Name
    
    return z3.Int(var.id)
