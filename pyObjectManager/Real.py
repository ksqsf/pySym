import z3

class Real:
    """
    Define a Real
    """
    
    def __init__(self,varName,ctx,count=None):
        assert type(varName) is str
        assert type(ctx) is int

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        
    def getZ3Object(self,increment=False):
        """
        Returns the z3 object for this variable
        """
        
        if increment:
            self.count += 1
        
        return z3.Real("{0}{1}@{2}".format(self.count,self.varName,self.ctx))
    
    def _isSame(self):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        return True
