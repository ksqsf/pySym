import z3
import ast
import logging
#from pyState import z3Helpers
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec
from pyObjectManager.List import List
from pyObjectManager.Ctx import Ctx
from pyObjectManager.String import String
from pyObjectManager.Char import Char
import pyState

logger = logging.getLogger("ObjectManager")

CTX_GLOBAL = 0
CTX_RETURNS = 1

class ObjectManager:
    """
    Object Manager will keep track of objects. Generally, Objects will be variables such as ints, lists, strings, etc.
    """

    def __init__(self,variables=None,returnObjects=None,state=None):
        self.variables = {CTX_GLOBAL: Ctx(CTX_GLOBAL), CTX_RETURNS: Ctx(CTX_RETURNS)} if variables is None else variables
        self.returnObjects = returnObjects if returnObjects is not None else {}

        if state is not None:
            self.setState(state)


    def setState(self,state):
        """
        This is a bit strange, but State won't copy correctly due to Z3, so I need to bypass this a bit by setting State each time I copy
        """
        assert type(state) == pyState.State
        
        self.state = state
        for ctx in self.variables:
            self.variables[ctx].setState(state)
        

    def newCtx(self,ctx):
        """
        Sets up a new context (ctx)
        """
        assert ctx is not None

        self.variables[ctx] = Ctx(ctx)
        self.variables[ctx].setState(self.state)

    def setVar(self,varName,ctx,var):
        """
        Input:
            varName = variable name (i.e.: 'x')
            ctx = Context to set for
            var = variable object of type pyObjectManager.X
        Action:
            Sets variable to the input (var) object
        Returns:
            Nothing
        """
        assert type(varName) is str
        assert type(ctx) is int
        assert type(var) in [Int, Real, BitVec, List]

        self.variables[ctx][varName] = var
        

    def getVar(self,varName,ctx,varType=None,kwargs=None):
        """
        Input:
            varName = name of variable to get
            ctx = Context for variable
            (optional) varType = Class type of variable (ex: pyObjectManager.Int)
            (optional) kwargs = args needed to instantiate variable
        Action:
            Find appropriate variable object, creating one if necessary
        Returns:
            pyObjectManager object for given variable (i.e.: pyObjectManager.Int)
        """
        
        # Attempt to return variable
        assert type(varName) is str
        assert type(ctx) is int
        assert varType in [None, Int, Real, BitVec, List, String, Char]
        
        create = False
        count = None
        
        # Check that we already have this variable defined
        if varName in self.variables[ctx]:
            
            # Check the type of the var is correct
            if varType is not None:

                # If the variable type is different or it's settings are different, we need to create a new object
                if type(self.variables[ctx][varName]) is not varType or not self.variables[ctx][varName]._isSame(**kwargs if kwargs is not None else {}):
                    create = True
                    # Re-using variable names is BAD!
                    count = self.variables[ctx][varName].count + 1
            
            # If we can just return the current one, let's do it
            if not create:
                return self.variables[ctx][varName]

        # Looks like we need to create a var
        if varType == None:
            err = "getVar: Need to create '{0}' but no type information given".format(varName)
            logger.error(err)
            raise Exception(err)
        
        # Make the var
        self.variables[ctx][varName] = varType(varName=varName,ctx=ctx,count=count,state=self.state,**kwargs if kwargs is not None else {})
        
        return self.variables[ctx][varName]

    def getParent(self,key,haystack=None):
        """
        Returns the parent object for any given object by recursively searching.
        """
        # TODO: This might get to be a long search if there are a lot of variables...

        haystack = self.variables if haystack is None else haystack

        if type(haystack) in [dict, Ctx]:
            for k,v in haystack.items():
                if v == key:
                    return haystack
                elif type(v) in [dict, List, Ctx]:
                    p = self.getParent(key,v)
                    if p:
                        return p
        elif isinstance(haystack,List):
            for v in haystack:
                if v == key:
                    return haystack
                elif type(v) in [dict,List]:
                    p = self.getParent(key,v)
                    if p:
                        return p


    def copy(self):
        """
        Return a copy of the Object Manager
        """

        return ObjectManager(
            variables = {key:self.variables[key].copy() for key in self.variables},
            returnObjects = {key:self.returnObjects[key].copy() for key in self.returnObjects}
        )

