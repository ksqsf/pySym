import z3
import ast
import logging
import pyState

logger = logging.getLogger("ObjectManager:Char")

class Char:
    """
    Define a Char (Character)
    """

    def __init__(self,varName,ctx,count=None,variable=None,state=None,increment=False):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(count) in [int, type(None)]

        self.size = 16
        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.variable = BitVec('{1}{0}'.format(self.varName,self.count),ctx=self.ctx,size=self.size) if variable is None else variable

        if state is not None:
            self.setState(state)

        if increment:
            self.increment()

    def __deepcopy__(self,_):
        return self.copy()


    def copy(self):
        return Char(
            varName = self.varName,
            ctx = self.ctx,
            count = self.count,
            variable = self.variable.copy(),
            state = self.state if hasattr(self,"state") else None,
        )

    def __str__(self):
        return chr(self.state.any_int(self))

    def setTo(self,var):
        """
        Sets this Char to the variable. Raises exception on failure.
        """
        if type(var) not in [str, String, Char]:
            err = "setTo: Invalid argument type {0}".format(type(var))
            logger.error(err)
            raise Exception(err)

        if (type(var) is String and var.length() != 1) or (type(var) is str and len(var) != 1):
            err = "setTo: Cannot set Char element to more than 1 length"
            logger.error(err)
            raise Exception(err)

        # Go ahead and add the constraints
        if type(var) is str:
            #self.state.addConstraint(self.getZ3Object() == ord(var))
            self.variable.setTo(ord(var))
        
        else:
            if type(var) is String:
                var = var[0]
            
            #self.state.addConstraint(self.getZ3Object() == var.getZ3Object())
            self.variable.setTo(var.variable)


    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State

        self.state = state
        self.variable.setState(state)

    def increment(self):
        self.count += 1
        # reset variable list if we're incrementing our count
        self.variable = BitVec('{1}{0}'.format(self.varName,self.count),ctx=self.ctx,size=self.size,state=self.state)
    
    def _isSame(self,**args):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        return True

    def getZ3Object(self):
        return self.variable.getZ3Object()

    def isStatic(self):
        """
        Returns True if this object is a static variety (i.e.: "a").
        Also returns True if object has only one possibility
        """
        return self.variable.isStatic()
        #if len(self.state.any_n_int(self,2)) == 1:
        #    return True

        #return False

    def getValue(self):
        """
        Resolves the value of this Char. Assumes that isStatic method is called
        before this is called to ensure the value is not symbolic
        """
        #return chr(self.state.any_int(self))
        return chr(self.variable.getValue())


    def mustBe(self,var):
        """
        Return True if this Char must be equivalent to input (str/Char). False otherwise.
        """
        assert type(var) in [str, Char]
        
        # If we can't be, then mustBe is also False
        if not self.canBe(var):
            return False
        
        # Utilize the BitVec's methods here
        if type(var) is str:
            return self.variable.mustBe(ord(var))

        if type(var) is Char:
            return self.variable.mustBe(var.variable)        

        # If we can be, determine if this is the only option
        #if len(self.state.any_n_int(self,2)) == 1 and len(self.state.any_n_int(var,2)) == 1:
        #    return True
        
        # Looks like we're only one option
        return False


    def canBe(self,var):
        """
        Test if this Char can be equal to the given variable
        Returns True or False
        """

        assert type(var) in [str, Char]

        if type(var) is str and len(var) != 1:
            return False
        
        if type(var) is str:
            return self.variable.canBe(ord(var))
            #s = self.state.copy()
            #s.addConstraint(self.getZ3Object() == ord(var))
            #if s.isSat():
            #    return True
            #return False

        elif type(var) is Char:
            return self.variable.canBe(var.variable)
            #s = self.state.copy()
            #s.addConstraint(self.getZ3Object() == var.getZ3Object())
            #if s.isSat():
            #    return True
            #return False



# Circular importing problem. Don't hate :-)
from pyObjectManager.BitVec import BitVec
from pyObjectManager.String import String

