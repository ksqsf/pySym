import z3
import ast
import logging
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List

logger = logging.getLogger("ObjectManager:String")

class String:
    """
    Define a String
    """

    def __init__(self,varName,ctx,count=None,string=None):
        assert type(varName) is str
        assert type(ctx) is int
        assert type(count) in [int, type(None)]

        self.count = 0 if count is None else count
        self.varName = varName
        self.ctx = ctx
        # Treating string as a list of BitVecs
        self.variables = []

        if string is not None:
            self.setTo(string)


    def increment(self):
        self.count += 1
        # reset variable list if we're incrementing our count
        self.variables = []
    
    """ 
    def append(self,var,kwargs=None):
        Input:
            var = pyObjectManager oject to append (i.e.: Int/Real/etc)
            (optional) kwargs = optional keyword args needed to instantiate type
        Action:
            Resolves object, creates variable if needed
        Returns:
            Nothing
        # Variable names in list are "<verson><varName>[<index>]". This is in addition to base naming conventions 

        if var is Int or type(var) is Int:
            logger.debug("append: adding Int")
            self.variables.append(Int('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,**kwargs if kwargs is not None else {}))

        elif var is Real or type(var) is Real:
            logger.debug("append: adding Real")
            self.variables.append(Real('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx))

        elif var is BitVec or type(var) is BitVec:
            logger.debug("append: adding BitVec")
            kwargs = {'size': var.size} if kwargs is None else kwargs
            self.variables.append(BitVec('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,**kwargs if kwargs is not None else {}))

        elif type(var) is List:
            logger.debug("append: adding List")
            self.variables.append(var)

        else:
            err = "append: Don't know how to append/resolve object '{0}'".format(var)
            logger.error(err)
            raise Exception(err)
    """

    def setTo(self,var):
        """
        Sets this String object to be equal/copy of another. Type can be str or String.
        Remember that this doesn't set anything in Z3
        """
        assert type(var) in [String, str]
        
        # For now, just add as many characters as there was originally
        for c in var:
            # Assuming 8-bit BitVec for now
            # TODO: Figure out a better way to handle this... Characters might be of various bitlength... Some asian encodings are up to 4 bytes...
            self.variables.append(BitVec('{2}{0}[{1}]'.format(self.varName,len(self.variables),self.count),ctx=self.ctx,size=16))


    def _isSame(self,**args):
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
        We want to be able to do "string[x]", so we define this.
        """
        if type(index) is slice:
            # Build a new List object containing the sliced stuff
            newList = String("temp",ctx=self.ctx)
            oldList = self.variables[index]
            for var in oldList:
                newList.append(var)
            return newList
            

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
