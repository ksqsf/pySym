import z3
import ast
import logging
from .Int import Int
from .Real import Real
from .BitVec import BitVec
from .List import List
from .String import String
from .Char import Char
from .. import pyState

logger = logging.getLogger("ObjectManager:Ctx")

class Ctx:
    """
    Define a Ctx Object
    """

    def __init__(self,ctx,variables=None):
        assert type(ctx) is int, "Unexpected ctx type of {}".format(type(ctx))
        
        self.ctx = ctx
        self.variables = {} if variables is None else variables

    def copy(self):
        return Ctx(
            ctx = self.ctx,
            variables = {key:self.variables[key].copy() for key in self.variables},
        )

    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State

        self.state = state
        for var in self.variables:
            self.variables[var].setState(state)


    def __iter__(self): return iter(self.variables)

    def items(self): return self.variables.items()

    def index(self,elm):
        """
        Returns "index" of the given element. Raises exception if it's not found
        For a pseudo dict class, this is just the key for the key,val pair
        """
        val = [k for k,v in self.variables.items() if v.uuid is elm.uuid]
        assert len(val) == 1, "Expected one item to be found. Found {} instead".format(len(val))
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
        assert type(value) in [Int, Real, BitVec, List, String, Char]
        
        # Things get weird if our variable names don't match up...
        #assert key == value.varName

        # Get that index's current count
        if key in self.variables:
            count = self.variables[key].count + 1
        else:
            count = 0

        #try:
        #    self.index(value)
        #    raise Exception("Trying to make duplicate variable uuid.")
        #except:
        #    pass

        # If the variable comes in with a higher count, that's the one to use
        #count = max(count,

        #print("Setting",value.getZ3Object())
        #self.variables[key] = value
        #value.count = count
        #print("Set",self.variables[key].getZ3Object())
        #return

        if type(value) is Int:
            logger.debug("__setitem__: setting Int")
            #self.variables[key] = Int('{0}'.format(key),ctx=self.ctx,count=count,state=self.state,on_increment=value.on_increment)

            self.variables[key] = value
            # Don't add a constraint if it's the same thing!
            #if self.variables[key].getZ3Object().get_id() != value.getZ3Object().get_id():
            #    #self.state.addConstraint(self.variables[key].getZ3Object() == value.getZ3Object())
            #    self.variables[key].setTo(value)

        elif type(value) is Real:
            logger.debug("__setitem__: setting Real")
            #self.variables[key] = Real('{0}'.format(key),ctx=self.ctx,count=count,state=self.state)
            self.variables[key] = value
            # Don't add a constraint if it's the same thing!
            if self.variables[key].getZ3Object().get_id() != value.getZ3Object().get_id():
                #self.state.addConstraint(self.variables[key].getZ3Object() == value.getZ3Object())
                self.variables[key].setTo(value)

        elif type(value) is BitVec:
            logger.debug("__setitem__: setting BitVec")
            #self.variables[key] = BitVec('{0}'.format(key),ctx=self.ctx,count=count,size=value.size,state=self.state)
            self.variables[key] = value
            # Don't add a constraint if it's the same thing!
            if self.variables[key].getZ3Object().get_id() != value.getZ3Object().get_id():
                #self.state.addConstraint(self.variables[key].getZ3Object() == value.getZ3Object())
                self.variables[key].setTo(value)

        elif type(value) in [List, String]:
            logger.debug("__setitem__: setting {0}".format(type(value)))
            value = value.copy()
            self.variables[key] = value
            self.variables[key].setState(self.state)
            #value.count = count
        
        elif type(value) is Char:
            logger.debug("__setitem__: setting Char")
            #self.variables[key] = Char('{0}'.format(key),ctx=self.ctx,count=count,state=self.state)
            self.variables[key] = value
            # Don't add a constraint if it's the same thing!
            #if self.variables[key].getZ3Object().get_id() != value.getZ3Object().get_id():
            #    #self.state.addConstraint(self.variables[key].getZ3Object() == value.getZ3Object())
            #    self.variables[key].setTo(value)

        else:
            err = "__setitem__: Don't know how to set object '{0}'".format(value)
            logger.error(err)
            raise Exception(err)
        
