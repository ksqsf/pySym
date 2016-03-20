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

        if var is Int:
            self.variables.append(Int('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx))

        elif var is Real:
            self.variables.append(Real('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx))

        elif type(var) is List:
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

    def __getitem__(self,index):
        """
        We want to be able to do "list[x]", so we define this.
        """
        return self.variables[index]
