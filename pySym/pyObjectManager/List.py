import z3
import ast
import logging
from .. import pyState

logger = logging.getLogger("ObjectManager:List")

class List:
    """
    Define a List
    """

    def __init__(self,varName,ctx,count=None,variables=None,state=None,increment=False):
        assert type(varName) is str
        assert type(ctx) is int

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        self.variables = [] if variables is None else variables

        if state is not None:
            self.setState(state)

        if increment:
            self.increment()


    def copy(self):
        return List(
            varName = self.varName,
            ctx = self.ctx,
            count = self.count,
            variables = [x.copy() for x in self.variables],
            state = self.state if hasattr(self,"state") else None
        )

    def __deepcopy__(self,_):
        return self.copy()

    def __copy__(self):
        return self.copy()

    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State

        self.state = state
        for var in self.variables:
            var.setState(state)

    def setTo(self,otherList,clear=False):
        """
        Sets this list to another of type List
        (optional) clear = Should we clear the current variables and set, or set the current variables in place retaining their constraints?
        """
        assert type(otherList) is List
        
        if clear:
            # Increment will also clear out the variables
            self.increment()
            
            # Just copy it over
            for elm in otherList:
                self.variables.append(elm.copy())        
        
        else:
            raise Exception("Not implemented")


    def increment(self):
        self.count += 1
        # reset variable list if we're incrementing our count
        self.variables = []

        
    def append(self,var,kwargs=None):
        """
        Input:
            var = pyObjectManager oject to append (i.e.: Int/Real/etc)
            (optional) kwargs = optional keyword args needed to instantiate type
        Action:
            Resolves object, creates variable if needed
        Returns:
            Nothing
        """
        # Variable names in list are "<verson><varName>[<index>]". This is in addition to base naming conventions 

        if type(var) is Int or var is Int:
            logger.debug("append: adding Int")
            self.variables.append(Int('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,state=self.state,**kwargs if kwargs is not None else {}))
            # We're being given an object. Let's make sure we link it to Z3 appropriately
            if type(var) is Int:
                self.variables[-1].setTo(var)

        elif type(var) is Real or var is Real:
            logger.debug("append: adding Real")
            self.variables.append(Real('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,state=self.state))
            if type(var) is Real:
                self.variables[-1].setTo(var)

        elif type(var) is BitVec or var is BitVec:
            logger.debug("append: adding BitVec")
            kwargs = {'size': var.size} if kwargs is None else kwargs
            self.variables.append(BitVec('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,state=self.state,**kwargs if kwargs is not None else {}))
            if type(var) is BitVec:
                self.variables[-1].setTo(var)
        
        elif type(var) is Char or var is Char:
            logger.debug("append: adding Char")
            self.variables.append(Char('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,state=self.state))
            if type(var) is Char:
                self.variables[-1].setTo(var)

        elif type(var) in [List, String]:
            logger.debug("append: adding {0}".format(type(var)))
            self.variables.append(var)

        else:
            err = "append: Don't know how to append/resolve object '{0}'".format(type(var))
            logger.error(err)
            raise Exception(err)


    def _isSame(self):
        """
        Checks if variables for this object are the same as those entered.
        Assumes checks of type will be done prior to calling.
        """
        return True

    def index(self,elm):
        """
        Returns index of the given element. Raises exception if it's not found
        """
        return self.variables.index(elm)

    def __getitem__(self,index):
        """
        We want to be able to do "list[x]", so we define this.
        """
        if type(index) is slice:
            # Build a new List object containing the sliced stuff
            newList = List("temp",ctx=self.ctx,state=self.state)
            oldList = self.variables[index]
            for var in oldList:
                newList.append(var)
            return newList
            

        return self.variables[index]

    def __setitem__(self,key,value):
        """
        Sets value at index key. Checks for variable type, updates counter according, similar to getVar call
        """
        # Attempt to return variable
        assert type(key) is int
        assert type(value) in [Int, Real, BitVec, List, String]

        # Get that index's current count
        count = self.variables[key].count + 1

        if type(value) is Int:
            logger.debug("__setitem__: setting Int")
            self.variables[key] = Int('{2}{0}[{1}]'.format(self.varName,key,self.count),ctx=self.ctx,count=count,state=self.state)
            self.variables[key].setTo(value)

        elif type(value) is Real:
            logger.debug("__setitem__: setting Real")
            self.variables[key] = Real('{2}{0}[{1}]'.format(self.varName,key,self.count),ctx=self.ctx,count=count,state=self.state)
            self.variables[key].setTo(value)

        elif type(value) is BitVec:
            logger.debug("__setitem__: setting BitVec")
            self.variables[key] = BitVec('{2}{0}[{1}]'.format(self.varName,key,self.count),ctx=self.ctx,count=count,size=value.size,state=self.state)
            self.variables[key].setTo(value)

        elif type(value) in [List, String]:
            logger.debug("__setitem__: setting {0}".format(type(value)))
            self.variables[key] = value
            #value.count = count

        else:
            err = "__setitem__: Don't know how to set object '{0}'".format(value)
            logger.error(err)
            raise Exception(err)

    def length(self):
        return len(self.variables)

    def pop(self,i):
        return self.variables.pop(i)

    def mustBe(self,var):
        """
        Test if this List must be equal to another
        """
        if not self.canBe(var):
            return False

        # Check each item in turn to see if it must be
        for (item,val) in zip(self,var):
            if not item.mustBe(val):
                return False
        
        return True

    def canBe(self,var):
        """
        Test if this List can be equal to another List
        Returns True or False
        """
        if type(var) is not List:
            return False
        
        # If not the same length, we can't be the same
        if self.length() != var.length():
            return False
        
        # Compare pairwise Chars
        for (me,you) in zip(self,var):
            if not me.canBe(you):
                return False

        return True

    def __str__(self):
        return str(self.state.any_list(self))

    def getValue(self):
        """
        Return a possible value. You probably want to check isStatic before calling this.
        """
        return self.state.any_list(self)

    def isStatic(self):
        """
        Checks if this list can only have one possible value overall (including all elements).
        Returns True/False
        """
        # Check each of my items for static-ness
        for var in self:
            if not var.isStatic():
                return False

        return True

# Circular importing problem. Don't hate :-)
from .Int import Int
from .Real import Real
from .BitVec import BitVec
from .Char import Char
from .String import String

