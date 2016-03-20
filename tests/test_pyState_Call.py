import sys, os
myPath = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, myPath + '/../')

import logging
import Colorer
logging.basicConfig(level=logging.DEBUG,format='%(name)s - %(levelname)s - %(message)s', datefmt='%m/%d/%Y %I:%M:%S %p')


import ast
import z3
from pyPath import Path
import pytest

test1 = """
def test():
    x = 5

x = 1
test()
y = 3
"""

test2 = """
def test(a,b,c):
    x = 5

x = 1
test(1,2.2,3.5)
y = 1
"""

test3 = """
def test(a,b=2,c=5.5):
    x = 5

x = 1.5
test(1,c=x+1)
y = 1
"""

test4 = """
def test(a,b=2,c=5.5):
    z = 5
    return a+b
    x = 12


x = 1
test(1,c=x+1)
x = test(1,2.2)
y = 1
"""

test5 = """
x = 4
def test():
    x = 6
    return 5

x = test()
z = 1
"""

test6 = """
def test2():
    return 3

def test():
    x = test2()
    return x + 2

x = test()
z = 1
"""

test7 = """
def test2():
    return 5

def test():
    return test2() + 2

x = test()
z = 1
"""

test8 = """
def test2():
    return 5

def test():
    return test2() + test2()

x = test()
z = 1
"""

def test_pySym_functionNestingThree():
    b = ast.parse(test8).body
    p = Path(b,source=test8)
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    assert p.state.isSat()
    assert p.state.any_int('x') == 10


def test_pySym_functionNestingTwo():
    # More intense nesting
    b = ast.parse(test7).body
    p = Path(b,source=test7)
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    assert p.state.isSat()
    assert p.state.any_int('x') == 7


def test_pySym_functionNesting():
    # Test out calling functions from functions
    b = ast.parse(test6).body
    p = Path(b,source=test6)
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p.printBacktrace()
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('x') == 5


def test_pySym_returnToAssign():
    # Testing that we can return a function to a variable
    b = ast.parse(test5).body
    p = Path(b,source=test5)
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    assert p.state.any_int('x') == 5


def test_pySym_callwithKeyWordAndDefaultReturn():
    b = ast.parse(test4).body
    p = Path(b,source=test4)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]
    p = p.step()[0]
    
    assert p.state.isSat()
    with pytest.raises(Exception):
        p.state.any_int('x')
    assert p.state.any_int('a') == 1
    assert p.state.any_int('b') == 2
    assert p.state.any_real('c') == 2

    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    #assert p.state.any_int('ret',ctx=1) == 1+2
    p.state.any_int('x') == 1+2
    
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_int('a') == 1
    assert p.state.any_real('b') == 2.2
    assert p.state.any_real('c') == 5.5
    
    p = p.step()[0]
    p = p.step()[0]
    
    #???
    p = p.step()[0]
    p = p.step()[0]
    #???

    assert p.state.isSat()
    p.printBacktrace()
    assert p.state.any_real('x') == 3.2
    

def test_pySym_callwithKeyWordAndDefault():
    b = ast.parse(test3).body
    p = Path(b,source=test3)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_real('x') == 1.5
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('a') == 1
    assert p.state.any_int('b') == 2
    assert p.state.any_real('c') == 2.5
    with pytest.raises(Exception):
        p.state.any_int('x')



def test_pySym_callThreeArgs():
    b = ast.parse(test2).body
    p = Path(b,source=test2)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_int('x') == 1
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('a') == 1
    assert p.state.any_real('b') == 2.2
    assert p.state.any_real('c') == 3.5
    with pytest.raises(Exception):
        p.state.any_int('x')
    
    p = p.step()[0]
    assert p.state.isSat()
    assert p.state.any_int('x') == 5
    
    p = p.step()[0]
    p = p.step()[0]
    
    assert p.state.isSat()
    with pytest.raises(Exception):
        p.state.any_int('a')
    assert p.state.any_real('b') == None
    assert p.state.any_real('c') == None
    assert p.state.any_int('x') == 1
    assert p.state.any_int('y') == 1


def test_pySym_CallNoArgs():
    b = ast.parse(test1).body
    p = Path(b,source=test1)
    # Step through program
    p = p.step()[0]
    p = p.step()[0]

    assert p.state.isSat()
    assert p.state.any_int('x') == 1

    p = p.step()[0]
    
    assert p.state.isSat()
    with pytest.raises(Exception):
        p.state.any_int('x') # New context means there should be no more x
    
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('x') == 5
    
    p = p.step()[0]
    p = p.step()[0]
    
    assert p.state.isSat()
    assert p.state.any_int('x') == 1 # Back to original context
    assert p.state.any_int('y') == 3
