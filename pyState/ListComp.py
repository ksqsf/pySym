import logging
import z3
import ast
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List
import pyState

logger = logging.getLogger("pyState:ListComp")

import astunparse

def _findAllInputVariables(haystack):
    """
    Find all input variables (ast.Name objects). Return as a list
    """
    ret = []
    print("type",type(haystack))

    if type(haystack) is ast.ListComp:
        for generator in haystack.generators:
            ret += _findAllInputVariables(generator)
        return ret

    if type(haystack) is ast.Name:
        return [haystack]

    if type(haystack) is ast.comprehension:
        return _findAllInputVariables(haystack.iter)

    if type(haystack) is ast.Call:
        if haystack.args is not None:
            for arg in haystack.args:
                ret += _findAllInputVariables(arg)
        if haystack.kwargs is not None:
            for arg in haystack.kwargs:
                ret += _findAllInputVariables(arg)
        if type(haystack.func) is not ast.Name:
            ret += _findAllInputVariables(haystack.func)
        return ret
    
    if type(haystack) is ast.Attribute:
        return [] + _findAllInputVariables(haystack.value)

    if type(haystack) is ast.Subscript:
        return [] + _findAllInputVariables(haystack.value)

    return []


def handle(state,element,ctx=None):
    """
    Treating ListComprehension as a function call. Using ast to re-write list comprehension into function, then calling it
    """
    assert type(element) is ast.ListComp    

    ctx = state.ctx if ctx is None else ctx

    col_offset = element.col_offset
    lineno = element.lineno

    # Create the function to be called
    fun = ast.parse("def tempFunction():\n\tpySymTempList = []").body[0]

    # Pointer to deepest statement
    last = fun

    # These are the "for" commands    
    for generator in element.generators:
        if type(generator.target) is not ast.Name:
            err = "handle: Don't know how to handle object '{0}'".format(type(generator.target))
            logger.error(err)
            raise Exception(err)

        # Generate the ast structure
        f = ast.parse("for x in y:\n\tpass").body[0]
        # Populate it with the generator information
        f.target = generator.target
        f.iter = generator.iter

        # Add this for loop to our nest
        last.body.append(f)

        # Our new for loop is the deepest
        last = f
        
        # TODO: Add ifs here
        for ifStmnt in generator.ifs:
            tmpIf = ast.parse("if x > y:\n\tpass").body[0]
            tmpIf.test = ifStmnt
            last.body.append(tmpIf)
            # This if is now the deepend
            last = tmpIf

    # Generate our list at the deepest level
    a = ast.parse("pySymTempList.append({0})".format(generator.target.id)).body[0]
    a.value.args = [element.elt]
    last.body.append(a)

    # Need to return the var
    fun.body.append(ast.parse("return pySymTempList").body[0])

    # Change this list comprehention into a ReturnObject
    retObj = pyState.ReturnObject(1)
    
    # Replace list comprehension with our ReturnObject
    pyState.replaceObjectWithObject(state.path[0],element,retObj)
    
    # Determine variables we need to pass in
    allInputVars = set(_findAllInputVariables(element))

    # Add these args into the function def
    for inputVar in allInputVars:
        fun.args.args.append(ast.arg(inputVar.id,0))

    print(astunparse.unparse(fun))

    # Call our new function.
    state.Call(ast.parse("blergy({0})".format(','.join([x.id for x in allInputVars]))).body[0].value,func=fun,retObj=retObj)

    return retObj


