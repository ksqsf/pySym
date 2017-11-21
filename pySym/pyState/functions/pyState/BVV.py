
import z3
import ast
from ...z3Helpers import Z3_DEFAULT_BITVEC_SIZE
from ....pyObjectManager.BitVec import BitVec

def handle(state,call,i,size=ast.Num(Z3_DEFAULT_BITVEC_SIZE),ctx=None):
    """
    Returns a BitVecVal object. This is helpful if we want to manually state what type a variable should be.
    """
    ctx = ctx if ctx is not None else state.ctx


    assert type(i) is ast.Num
    assert type(size) is ast.Num
    
    bvv = state.resolveObject(ast.Name('temp',0),ctx=1,varType=BitVec,kwargs={'size': size.n})
    assert len(bvv) == 1
    bvv = bvv.pop()
    state.addConstraint(bvv.getZ3Object(increment=True) == i.n)

    return bvv
