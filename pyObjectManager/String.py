import z3
import ast
import logging
import pyState

logger = logging.getLogger("ObjectManager:String")

class String:
    """
    Define a String
    """

    def __init__(self,varName,ctx,count=None,string=None,variables=None,state=None,length=None,increment=False):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(count) in [int, type(None)]

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        # Treating string as a list of BitVecs
        self.variables = [] if variables is None else variables

        if increment:
            self.increment()

        if state is not None:
            self.setState(state)


        if string is not None:
            self.setTo(string)

        # Add generic characters to this string
        if length is not None:
            for x in range(length):
                self._addChar()


    def copy(self):
        return String(
            varName = self.varName,
            ctx = self.ctx,
            count = self.count,
            variables = [x.copy() for x in self.variables],
            state = self.state if hasattr(self,"state") else None
        )

    def __deepcopy__(self, _):
        return self.copy()



        if increment:
            self.increment()
    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State

        self.state = state
        for var in self.variables:
            var.setState(state)

    def increment(self):
        self.count += 1
        length = self.length()
        # reset variable list if we're incrementing our count
        self.variables = []

        # Add generic characters to this string
        if length is not None:
            for x in range(length):
                self._addChar()

    
    def _addChar(self):
        """
        Append a generic Char item to this string.
        """
        self.variables.append(Char('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,state=self.state))

    def setTo(self,var):
        """
        Sets this String object to be equal/copy of another. Type can be str or String.
        """
        assert type(var) in [String, str]
        
        self.variables = []

        # For now, just add as many characters as there was originally
        for val in var:
            self._addChar()
            if type(val) is str:
                self.state.addConstraint(self[-1].getZ3Object() == ord(val))
            else:
                self.state.addConstraint(self[-1].getZ3Object() == val.getZ3Object())
            


    def _isSame(self,length=None,**args):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        if length is not self.length():
            return False
        return True

    def index(self,elm):
        """
        Returns index of the given element. Raises exception if it's not found
        """
        return self.variables.index(elm)

    def __getitem__(self,index):
        """
        We want to be able to do "string[x]", so we define this.
        """
        if type(index) is slice:
            # TODO: Redo this to return as string object
            # Build a new String object containing the sliced stuff
            # Create a copy
            newString = self.copy()

            # Adjust the variables down to the slice
            newString.variables = newString.variables[index]

            return newString
            

        return self.variables[index]

    def __setitem__(self,key,value):
        """
        String doesn't support setitem
        """
        err = "String type does not support item assignment"
        logger.error(err)
        raise Exception(err)


    def length(self):
        return len(self.variables)

    def pop(self,index=None):
        """
        Not exactly something you can do on a string, but helpful for our symbolic execution
        """
        if index is not None:
            return self.variables.pop(index)
        else:
            return self.variables.pop()

    def __str__(self):
        """
        str will change this object into a possible representation by calling state.any_str
        """
        return self.state.any_str(self)

    def mustBe(self,var):
        """
        Test if this string must be equal to the given variable. This means there's no other options and it's not symbolic
        """
        assert type(var) in [str, String]

        # TODO: Re-assess how i do this. Can probably make this more efficient...

        # If it's not even possible, just return no
        if not self.canBe(var):
            return False

        # If we can possible be this value, see if we MUST be this value
        # Loop through all our characters and see if they have more than one possibility
        for c in self:
            # If this has more than one option, return False
            if len(self.state.any_n_int(c,2)) == 2:
                return False

        # Looks like we've got a match...
        return True

    def canBe(self,var):
        """
        Test if this string can be equal to the given variable
        Returns True or False
        """

        # May need to add String object canBe later
        assert type(var) in [str, String]
        
        # If we're dealing with a python string
        if type(var) is str:
            # It can't be equal if it's a different length...
            if self.length() != len(var):
                return False
            
            # Ask the solver...
            s = self.state.copy()
            for (me,you) in zip(self,var):
                # Add the constraint
                s.addConstraint(me.getZ3Object() == ord(you))
                # If we're not possible, return False
                if not s.isSat():
                    return False
        
            # If we made it here, it's a possibility
            return True
    
        # if we're dealing with a String object
        if type(var) is String:
            # It can't be equal if it's a different length...
            if self.length() != var.length():
                return False

            # Ask the solver...
            s = self.state.copy()
            for (me,you) in zip(self,var):
                # Add the constraint
                s.addConstraint(me.getZ3Object() == you.getZ3Object())
                # If we're not possible, return False
                if not s.isSat():
                    return False

            # If we made it here, it's a possibility
            return True

    def isStatic(self):
        """
        Returns True if this object is a static variety (i.e.: "test").
        Also returns True if object has only one possibility
        """
        # Check every character for multiple possible values
        for c in self:
            if not c.isStatic():
                return False

        # If all of them are static, this is a static string
        return True

    def getValue(self):
        """
        Resolves the value of this String. Assumes that isStatic method is called
        before this is called to ensure the value is not symbolic
        """
        return self.state.any_str(self)

# Circular importing problem. Don't hate :-)
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.Char import Char

