import z3
import ast
import logging
from pyObjectManager.BitVec import BitVec
import pyState

logger = logging.getLogger("ObjectManager:Char")

class Char:
    """
    Define a Char (Character)
    """

    def __init__(self,varName,ctx,count=None,variable=None,state=None):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(count) in [int, type(None)]

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.variable = BitVec('{1}{0}'.format(self.varName,self.count),ctx=self.ctx,size=16) if variable is None else variable

        if state is not None:
            self.setState(state)


    def copy(self):
        return Char(
            varName = self.varName,
            ctx = self.ctx,
            count = self.count,
            variable = self.variable.copy()
        )

    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State

        self.state = state

    def increment(self):
        self.count += 1
        # reset variable list if we're incrementing our count
        self.variable = BitVec('{1}{0}'.format(self.varName,self.count),ctx=self.ctx,size=16)
    
    def _isSame(self,**args):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        return True

    def getZ3Object(self):
        return self.variable.getZ3Object()
