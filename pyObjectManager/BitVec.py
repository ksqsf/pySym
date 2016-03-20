import z3

class BitVec:
    """
    Define a BitVec
    """
    
    def __init__(self,varName,ctx,size,count=None):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(size) is int

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.size = size
        
    def getZ3Object(self,increment=False):
        """
        Returns the z3 object for this variable
        """
        
        if increment:
            self.count += 1
        
        return z3.BitVec("{0}{1}@{2}".format(self.count,self.varName,self.ctx),self.size)
    
    def _isSame(self,size):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        assert type(size) is int
        return True if size == self.size else False
