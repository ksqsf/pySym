"""
A file to hold my helper items directly relating to z3
"""

import z3
import ast
import pyState


def mk_var(name,vsort):
    if vsort.kind() == z3.Z3_INT_SORT:
        v = z3.Int(name)
    elif vsort.kind() == z3.Z3_REAL_SORT:
        v = z3.Real(name)
    elif vsort.kind() == z3.Z3_BOOL_SORT:
        v = z3.Bool(name)
    elif vsort.kind() == z3.Z3_DATATYPE_SORT:
        v = z3.Const(name,vsort)
    elif vsort.kind() == z3.Z3_BV_SORT:
        v = z3.BitVec(name,vsort.size())

    else:
        assert False, 'Cannot handle this sort (s: %sid: %d)'\
            %(vsort,vsort.kind())

    return v

def z3_matchLeftAndRight(left,right,op):
    """
    Input:
        left = z3 object
        right = z3 object
        op = ast operation that will be performed
    Action:
        Appropriately cast the two variables so that they can be used in an expression
        Main problem is between Int type and BitVec type
    Returns:
        (left,right) where both vars should be able to be used together
    """
    lType = type(left)
    rType = type(right)

    needBitVec = True if type(op) in [ast.BitXor, ast.BitAnd, ast.BitOr, ast.LShift, ast.RShift] else False

    # For now only handling casting of int to BV. Not other way around.
    if (lType is z3.BitVecRef and rType is z3.ArithRef) or (rType in [z3.ArithRef,z3.IntNumRef] and needBitVec):
        right = pyState.z3_int_to_bv(right)

    if (rType is z3.BitVecRef and lType is z3.ArithRef) or (lType in [z3.ArithRef,z3.IntNumRef] and needBitVec):
        left = pyState.z3_int_to_bv(left)

    return (left,right)

