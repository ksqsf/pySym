import z3
import logging
import pyState

logger = logging.getLogger("ObjectManager:Real")

class Real:
    """
    Define a Real
    """
    
    def __init__(self,varName,ctx,count=None,value=None,state=None):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(value) in [type(None),float,int]

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.value = value
        
        if state is not None:
            self.setState(state)

    def copy(self):
        return Real(
            varName = self.varName,
            ctx = self.ctx,
            count = self.count,
            value = self.value,
            state = self.state if hasattr(self,"state") else None
        )


    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State

        self.state = state

        
    def increment(self):
        self.count += 1

    def getZ3Object(self,increment=False):
        """
        Returns the z3 object for this variable
        """
        
        if increment:
            self.increment()
        
        if self.value is None:
            return z3.Real("{0}{1}@{2}".format(self.count,self.varName,self.ctx))

        return z3.RealVal(self.value)
    
    def _isSame(self,value=None):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        if value == self.value:
            return True
        return False

    def isStatic(self):
        """
        Returns True if this object is a static variety (i.e.: RealVal(12))
        """
        if self.value is not None:
            return True
        return False

    def getValue(self):
        """
        Resolves the value of this real. Assumes that isStatic method is called
        before this is called to ensure the value is not symbolic
        """
        if self.value is not None:
            return self.value

        return self.state.any_real(self)

