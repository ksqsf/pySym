import z3
import logging
from pySym import pyState

logger = logging.getLogger("ObjectManager:Int")

class Int:
    """
    Define an Int
    """
    
    def __init__(self,varName,ctx,count=None,value=None,state=None,increment=False):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(value) in [type(None),int]

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
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
        return Int(
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
        self.value = None
        self.count += 1
        
    def getZ3Object(self,increment=False):
        """
        Returns the z3 object for this variable
        """
        
        if increment:
            self.increment()

        if self.value is None:
            return z3.Int("{0}{1}@{2}".format(self.count,self.varName,self.ctx),ctx=self.state.solver.ctx)
        
        return z3.IntVal(self.value)

    
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
        Returns True if this object is a static variety (i.e.: IntVal(12)).
        Also returns True if object has only one possibility
        """
        # If this is a static int
        if self.value is not None:
            return True
        
        # If this is an integer with only one possibility
        if len(self.state.any_n_int(self,2)) == 1:
            return True

        return False

    def getValue(self):
        """
        Resolves the value of this integer. Assumes that isStatic method is called
        before this is called to ensure the value is not symbolic
        """
        if self.value is not None:
            return self.value
        
        return self.state.any_int(self)

    def setTo(self,var):
        """
        Sets this Int object to be equal/copy of another. Type can be int or Int
        """
        # Floats are OK so long as they are equal to an int
        if type(var) is float:
            if int(var) == var:
                var = int(var)
            else:
                err = "Attempting to set float {0} to int {1}!".format(var,int(var))
                logger.error(err)
                raise Exception(err)

        assert type(var) in [Int, int]

        # Add the constraints
        
        # If we're not in the solver, we can play some tricks to make things faster
        if not z3Helpers.varIsUsedInSolver(self.getZ3Object(),self.state.solver):

            # If we're adding a static variety, don't clutter up the solver
            if type(var) is int:
                self.value = var            
                return

            # If var is static and not being used in any expressions
            elif var.isStatic():
                self.value = var.getValue()
                return

        ## At this point, we know that our own variable is in the solver already, need to add this to the solver        

        if type(var) is int:
            obj = var
        elif var.isStatic():
            obj = var.getValue()
        else:
            obj = var.getZ3Object()

        # If we're setting this to a variable, make sure we're not set as static
        self.value = None
        self.state.addConstraint(self.getZ3Object() == obj)

    def __str__(self):
        """
        str will change this object into a possible representation by calling state.any_int
        """
        return str(self.state.any_int(self))

    def mustBe(self,var):
        """
        Test if this Int must be equal to another variable
        Returns True or False
        """
        if not self.canBe(var):
            return False

        # Can we be something else?
        if len(self.state.any_n_int(self,2)) == 2:
            return False

        # Can the other var be something else?
        if len(self.state.any_n_int(var,2)) == 2:
            return False
        
        #return False
        return True


    def canBe(self,var):
        """
        Test if this Int can be equal to the given variable
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

from pyObjectManager.BitVec import BitVec
import pySym.pyState.z3Helpers as z3Helpers
