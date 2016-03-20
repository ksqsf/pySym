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
        
    def append(self,var):
        """
        Input:
            var = object to append
        Action:
            Resolves object, creates variable if needed
        Returns:
            Nothing
        """
        # Variable names in list are "<varName>@<index>". This is in addition to base naming conventions 

        if type(var) is ast.Num:
            if type(var.n) is int:
                self.variables.append(Int('{0}@{1}'.format(self.varName,len(self.variables)),ctx=self.ctx))

            elif type(var.n) is float:
                self.variables.append(Real('{0}@{1}'.format(self.varName,len(self.variables)),ctx=self.ctx))

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
