
import z3
import ast
from pyState.z3Helpers import Z3_DEFAULT_BITVEC_SIZE

def handle(state,var,size=ast.Num(Z3_DEFAULT_BITVEC_SIZE)):
    """
    Returns a BitVec object. Use this to inform pySym that something should be BitVec symbolic
    """

    assert type(var) is ast.Name
    assert type(size) is ast.Num
    
    return z3.BitVec(var.id,size.n)
