"""
A file to hold my helper items directly relating to z3
"""

import z3
import ast
import pyState


def isZ3Object(obj):
    """
    Determine if the object given is a z3 type object
    """
    if type(obj) in [z3.ArithRef, z3.IntNumRef, z3.RatNumRef, z3.BitVecRef, z3.BitVecNumRef, z3.ArrayRef, z3.SeqRef]:
        return True
    return False

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
    # TODO: If the two sizes are different, we'll have problems down the road.
    bitVecSize = max([c.size() for c in [b for b in [left,right] if type(b) in [z3.BitVecRef, z3.BitVecNumRef]]],default=128)

    # For now only handling casting of int to BV. Not other way around.
    if (lType is z3.BitVecRef and rType in [z3.ArithRef,z3.IntNumRef]) or (rType in [z3.ArithRef,z3.IntNumRef] and needBitVec):
        # If we need to convert to BitVec and it is a constant, not variable, do so more directly
        if rType is z3.IntNumRef and right.is_int():
            right = z3.BitVecVal(right.as_long(),bitVecSize)
        # Otherwise cast it. Not optimal, but oh well.
        else:
            right = pyState.z3_int_to_bv(right)

    if (rType is z3.BitVecRef and lType is [z3.ArithRef,z3.IntNumRef]) or (lType in [z3.ArithRef,z3.IntNumRef] and needBitVec):
        if lType is z3.IntNumRef and left.is_int():
            left = z3.BitVecVal(left.as_long(),bitVecSize)
        else:
            left = pyState.z3_int_to_bv(left)

    return (left,right)

