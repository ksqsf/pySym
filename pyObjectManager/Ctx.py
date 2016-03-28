import z3
import ast
import logging
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List
from pyObjectManager.String import String

logger = logging.getLogger("ObjectManager:Ctx")

class Ctx:
    """
    Define a Ctx Object
    """

    def __init__(self,ctx):
        assert type(ctx) is int
        
        self.ctx = ctx
        self.variables = {}

    def __iter__(self): return iter(self.variables)

    def items(self): return self.variables.items()

    def index(self,elm):
        """
        Returns "index" of the given element. Raises exception if it's not found
        For a pseudo dict class, this is just the key for the key,val pair
        """
        val = [k for k,v in self.variables.items() if v is elm]
        assert len(val) == 1
        return val[0]

    def __getitem__(self,index):
        """
        We want to be able to do "list[x]", so we define this.
        """
        return self.variables[index]

    def __setitem__(self,key,value):
        """
        Sets value at index key. Checks for variable type, updates counter according, similar to getVar call
        """
        # Attempt to return variable
        assert type(value) in [Int, Real, BitVec, List, String]

        # Get that index's current count
        if key in self.variables:
            count = self.variables[key].count + 1
        else:
            count = 0

        if type(value) is Int:
            logger.debug("__setitem__: setting Int")
            self.variables[key] = Int('{0}'.format(value.varName),ctx=self.ctx,count=count)

        elif type(value) is Real:
            logger.debug("__setitem__: setting Real")
            self.variables[key] = Real('{0}'.format(value.varName),ctx=self.ctx,count=count)

        elif type(value) is BitVec:
            logger.debug("__setitem__: setting BitVec")
            self.variables[key] = BitVec('{0}'.format(value.varName),ctx=self.ctx,count=count,size=value.size)

        elif type(value) in [List, String]:
            logger.debug("__setitem__: setting List")
            self.variables[key] = value
            value.count = count

        else:
            err = "__setitem__: Don't know how to set object '{0}'".format(value)
            logger.error(err)
            raise Exception(err)

