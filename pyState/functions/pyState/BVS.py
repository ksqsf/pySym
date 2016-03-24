
import z3
import ast
from pyState.z3Helpers import Z3_DEFAULT_BITVEC_SIZE

def handle(state,size=ast.Num(Z3_DEFAULT_BITVEC_SIZE)):
    """
    Returns a BitVec object. Use this to inform pySym that something should be BitVec symbolic
    """

    assert type(size) is ast.Num

    bvs = state.resolveObject(ast.Name('temp',0),ctx=1,varType=BitVec,kwargs={'size': size.n})
    
    return bvs
