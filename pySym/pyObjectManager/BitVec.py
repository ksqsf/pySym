import z3
from pySym import pyState

class BitVec:
    """
    Define a BitVec
    """
    
    def __init__(self,varName,ctx,size,count=None,state=None,increment=False,value=None):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(size) is int

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.size = size
        self.value = value

        if state is not None:
            self.setState(state)

        if increment:
            self.increment()

    def __deepcopy__(self,_):
        return self.copy()

    def __copy__(self):
        return self.copy()

    def copy(self):
        return BitVec(
            varName = self.varName,
            ctx = self.ctx,
            size = self.size,
            count = self.count,
            state = self.state if hasattr(self,"state") else None,
            value = self.value
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
        self.value = None
        self.count += 1
        
    def getZ3Object(self,increment=False):
        """
        Returns the z3 object for this variable
        """
        
        if increment:
            self.increment()
    
        # If we're not static    
        if self.value == None:
            return z3.BitVec("{0}{1}@{2}".format(self.count,self.varName,self.ctx),self.size,ctx=self.state.solver.ctx)

        return z3.BitVecVal(self.value,self.size)
    
    def _isSame(self,size):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        assert type(size) is int
        return True if size == self.size else False


    def setTo(self,var):
        """
        Sets this BitVec object to be equal/copy of another. Type can be int, or BitVec
        """
        assert type(var) in [int, BitVec]

        # Add the constraints

        # If we're not in the solver, we can play some tricks to make things faster
        if not pyState.z3Helpers.varIsUsedInSolver(self.getZ3Object(),self.state.solver):

            # Intentionally trying to unclutter the z3 solver here.
            if type(var) is int:
                self.value = var
                return

            elif var.isStatic():
                self.value = var.getValue()
                return

        if type(var) is int:
            obj = var
        elif var.isStatic():
            obj = var.getValue()
        else:
            obj = var.getZ3Object()

        self.value = None
        self.state.addConstraint(self.getZ3Object() == obj)


    def isStatic(self):
        """
        Returns True if this object is a static variety (i.e.: BitVecVal(12)).
        Also returns True if object has only one possibility
        """
        # If this is a static BitVec
        if self.value is not None:
            return True

        # If this is a BitVec with only one possibility
        if len(self.state.any_n_int(self,2)) == 1:
            return True

        return False


    def getValue(self):
        """
        Resolves the value of this BitVec. Assumes that isStatic method is called
        before this is called to ensure the value is not symbolic
        """
        if self.value is not None:
            return self.value

        return self.state.any_int(self)

    def __str__(self):
        """
        str will change this object into a possible representation by calling state.any_int
        """
        #return str(self.state.any_int(self))
        return str(self.getValue())


    def canBe(self,var):
        """
        Test if this BitVec can be equal to the given variable
        Returns True or False
        """
        if type(var) not in [Int, BitVec,int]:
            return False

        # Ask the solver
        s = self.state.copy()

        if type(var) in [Int, BitVec]:
            s.addConstraint(self.getZ3Object() == var.getZ3Object())

        else:
            s.addConstraint(self.getZ3Object() == var)

        if s.isSat():
            return True

        return False

    def mustBe(self,var):
        """
        Test if this BitVec must be equal to another variable
        Returns True or False
        """
        if not self.canBe(var):
            return False


        # Can we be something else?
        if len(self.state.any_n_int(self,2)) == 2:
            return False

        # Ok, we can't be anything else. How about the var?
        if len(self.state.any_n_int(var,2)) == 2:
            return False

        # So we can be, now must we?
        #if len(self.state.any_n_int(self,2)) == 1:
        #    return True

        #return False
        # We CAN be the same, and neither of us can be different. We MUST be the same
        return True

        
from pySym.pyObjectManager.Int import Int
