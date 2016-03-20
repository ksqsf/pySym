import z3
import logging

logger = logging.getLogger("ObjectManager:Int")

class Int:
    """
    Define an Int
    """
    
    def __init__(self,varName,ctx,count=None,value=None):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(value) in [type(None),int]

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.value = value
        
    def getZ3Object(self,increment=False):
        """
        Returns the z3 object for this variable
        """
        
        if increment:
            self.count += 1
    
        # If this is a variable type    
        if self.value is None:
            return z3.Int("{0}{1}@{2}".format(self.count,self.varName,self.ctx))

        # This must be a constant type
        return z3.IntVal(self.value)
    
    def _isSame(self,value=None):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        if self.value is value:
            return True
        return False
