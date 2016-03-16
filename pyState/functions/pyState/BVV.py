
import z3
import ast

def handle(state,i,size=ast.Num(128)):
    """
    Returns a BitVecVal object. This is helpful if we want to manually state what type a variable should be.
    """

    assert type(i) is ast.Num
    assert type(size) is ast.Num
    
    return z3.BitVecVal(i.n,size.n)
