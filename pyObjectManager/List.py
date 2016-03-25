import z3
import ast
import logging
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec

logger = logging.getLogger("ObjectManager:List")

class List:
    """
    Define a List
    """

    def __init__(self,varName,ctx,count=None):
        assert type(varName) is str
        assert type(ctx) is int

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.variables = []


    def increment(self):
        self.count += 1
        # reset variable list if we're incrementing our count
        self.variables = []
        
    def append(self,var,kwargs=None):
        """
        Input:
            var = pyObjectManager oject to append (i.e.: Int/Real/etc)
            (optional) kwargs = optional keyword args needed to instantiate type
        Action:
            Resolves object, creates variable if needed
        Returns:
            Nothing
        """
        # Variable names in list are "<verson><varName>[<index>]". This is in addition to base naming conventions 

        if var is Int or type(var) is Int:
            logger.debug("append: adding Int")
            self.variables.append(Int('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx))

        elif var is Real or type(var) is Real:
            logger.debug("append: adding Real")
            self.variables.append(Real('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx))

        elif var is BitVec or type(var) is BitVec:
            logger.debug("append: adding BitVec")
            kwargs = {'size': var.size} if kwargs is None else kwargs
            self.variables.append(BitVec('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,**kwargs if kwargs is not None else {}))

        elif type(var) is List:
            logger.debug("append: adding List")
            self.variables.append(var)

        else:
            err = "append: Don't know how to append/resolve object '{0}'".format(var)
            logger.error(err)
            raise Exception(err)


    def _isSame(self):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        return True

    def index(self,elm):
        """
        Returns index of the given element. Raises exception if it's not found
        """
        return self.variables.index(elm)

    def __getitem__(self,index):
        """
        We want to be able to do "list[x]", so we define this.
        """
        if type(index) is slice:
            # Build a new List object containing the sliced stuff
            newList = List("temp",ctx=self.ctx)
            oldList = self.variables[index]
            for var in oldList:
                newList.append(var)
            return newList
            

        return self.variables[index]

    def __setitem__(self,key,value):
        """
        Sets value at index key. Checks for variable type, updates counter according, similar to getVar call
        """
        # Attempt to return variable
        assert type(key) is int
        assert type(value) in [Int, Real, BitVec, List]

        # Get that index's current count
        count = self.variables[key].count + 1

        if type(value) is Int:
            logger.debug("__setitem__: setting Int")
            self.variables[key] = Int('{2}{0}[{1}]'.format(self.varName,key,self.count),ctx=self.ctx,count=count)

        elif type(value) is Real:
            logger.debug("__setitem__: setting Real")
            self.variables[key] = Real('{2}{0}[{1}]'.format(self.varName,key,self.count),ctx=self.ctx,count=count)

        elif type(value) is BitVec:
            logger.debug("__setitem__: setting BitVec")
            self.variables[key] = BitVec('{2}{0}[{1}]'.format(self.varName,key,self.count),ctx=self.ctx,count=count,size=value.size)

        elif type(value) is List:
            logger.debug("__setitem__: setting List")
            self.variables[key] = value
            value.count = count

        else:
            err = "__setitem__: Don't know how to set object '{0}'".format(value)
            logger.error(err)
            raise Exception(err)

    def length(self):
        return len(self.variables)

    def pop(self,i):
        return self.variables.pop(i)
