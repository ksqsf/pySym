
import z3
import ast
from pyState.z3Helpers import Z3_DEFAULT_BITVEC_SIZE

def handle(state,i,size=ast.Num(Z3_DEFAULT_BITVEC_SIZE)):
    """
    Returns a BitVecVal object. This is helpful if we want to manually state what type a variable should be.
    """

    assert type(i) is ast.Num
    assert type(size) is ast.Num
    
    return z3.BitVecVal(i.n,size.n)
