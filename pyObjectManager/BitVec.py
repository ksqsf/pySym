import z3
import pyState

class BitVec:
    """
    Define a BitVec
    """
    
    def __init__(self,varName,ctx,size,count=None,state=None):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(size) is int

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.size = size

        if state is not None:
            self.setState(state)


    def copy(self):
        return BitVec(
            varName = self.varName,
            ctx = self.ctx,
            size = self.size,
            count = self.count,
            state = self.state if hasattr(self,"state") else None
        )


    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State

        self.state = state

    def increment(self):
        """
        Increment the counter
        """
        self.count += 1
        
    def getZ3Object(self,increment=False):
        """
        Returns the z3 object for this variable
        """
        
        if increment:
            self.increment()
        
        return z3.BitVec("{0}{1}@{2}".format(self.count,self.varName,self.ctx),self.size)
    
    def _isSame(self,size):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        assert type(size) is int
        return True if size == self.size else False
