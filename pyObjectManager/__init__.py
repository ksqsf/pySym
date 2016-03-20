import z3
import ast
import logging
from copy import deepcopy
#from pyState import z3Helpers
from pyObjectManager.Int import Int
from pyObjectManager.Real import Real
from pyObjectManager.BitVec import BitVec


logger = logging.getLogger("ObjectManager")

CTX_GLOBAL = 0
CTX_RETURNS = 1

class ObjectManager:
    """
    Object Manager will keep track of objects. Generally, Objects will be variables such as ints, lists, strings, etc.
    """

    """
    variables = {
        <ctx> : {
            <varName> : <var Class Instance>
        }
    }
    """

    def __init__(self,variables=None):
        self.variables = {CTX_GLOBAL: {}, CTX_RETURNS: {}} if variables is None else variables

    def newCtx(self,ctx):
        """
        Sets up a new context (ctx)
        """
        assert ctx is not None

        self.variables[ctx] = {}


    def resolveVariable(self,obj,ctx):
        """
        Input:
            obj = ast object to resolve
            ctx = Context for this variable
        Action: 
           Resolve it to an object z3 can work with
        Return:
            Resolved z3 object
        """
        # List of object we current understand
        assert type(obj) in [ast.Name]
        
        # Basically copying this function over for now. Will modify later.
        return self.getZ3Var(obj.id,ctx=ctx)


    def _varTypeToString(self,varType):
        """
        Input:
            varType = z3 var sort (i.e.: z3.IntSort())
        Action:
            Resolves input type back to it's string (i.e.: "z3.IntSort()")
        Returns:
            String representation of varType
        """
        assert type(varType) in [z3.ArithSortRef,z3.BoolSortRef,z3.BitVecSortRef]

        if type(varType) == z3.ArithSortRef:
            if varType.is_real():
                return "z3.RealSort()"
            elif varType.is_int():
                return "z3.IntSort()"
            else:
                raise Exception("Got unknown ArithSortRef type {0}".format(varType))

        elif type(varType) == z3.BoolSortRef:
            if varType.is_bool():
                return "z3.BoolSort()"
            else:
                raise Exception("Got unknown BoolSortRef type {0}".format(varType))

        elif type(varType) == z3.BitVecSortRef:
            return "z3.BitVecSort({0})".format(varType.size())


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
        assert varType in [None, Int, Real, BitVec]
        
        create = False
        
        # Check that we already have this variable defined
        if varName in self.variables[ctx]:
            
            # Check the type of the var is correct
            if varType is not None:

                # If the variable type is different or it's settings are different, we need to create a new object
                if type(self.variables[ctx][varName]) is not varType or not self.variables[ctx][varName]._isSame(**kwargs if kwargs is not None else {}):
                    create = True
            
            # If we can just return the current one, let's do it
            if not create:
                return self.variables[ctx][varName]

        # Looks like we need to create a var
        if varType == None:
            err = "getVar: Need to create '{0}' but no type information given".format(varName)
            logger.error(err)
            raise Exception(err)
        
        # Make the var
        self.variables[ctx][varName] = varType(varName=varName,ctx=ctx,**kwargs if kwargs is not None else {})
        
        return self.variables[ctx][varName]

    """
    def getZ3Var(self,varName,local=True,increment=False,varType=None,previous=False,ctx=None):
        Input:
            varName = Variable name to retrieve Z3 object of
            (optional) local = Boolean if we're dealing with local scope
            (optional) increment = Increment the counter. This is if we want to do
                                   something new with this variable. If variable
                                   does not exist, it will be created in the scope
                                   defined by the "local" param
            (optional) varType = Type of var to create. Used when increment=True
                                 and var cannot be found. (i.e: z3.IntSort())
            (optional) previous = Bool of do you want one that is one older
                                  i.e.: current is x_1, return x_0
            ctx = context to resolve in if not the current one
        Action:
            Look-up variable
        Returns:
            z3 object variable with given name or None if it cannot be found
        # It's important to look this up since we might not know going in
        # what the variable type is. This keeps track of that state.

        # Variable naming convention. Intentionally breaking legal python variable naming conventions
        # <Count><VarName>@<context>
        # example: 07MyVar@1

        #TODO: Optimize this

        #ctx = self.ctx if ctx is None else ctx
        assert ctx is not None

        # If we're looking up local variable
        if local:
            if varName in self.localVars[ctx]:
                # Increment the counter if asked
                if increment:
                    self.localVars[ctx][varName]['count'] += 1
                count = self.localVars[ctx][varName]['count']
                # Get previous
                if previous:
                    count -= 1

                # Set varType if asked for
                if type(varType) != type(None):
                    self.localVars[ctx][varName]['varType'] = self._varTypeToString(varType)

                return z3Helpers.mk_var("{0}{1}@{2}".format(count,varName,ctx),eval(self.localVars[ctx][varName]['varType']))

            # If we want to increment but we didn't find it, create it
            elif increment:
                assert type(varType) in [z3.ArithSortRef,z3.BoolSortRef,z3.BitVecSortRef]

                # Time to create a new var!
                self.localVars[ctx][varName] = {
                    'count': 0,
                    'varType': self._varTypeToString(varType)
                }
                return z3Helpers.mk_var("{0}{1}@{2}".format(self.localVars[ctx][varName]['count'],varName,ctx),varType)

        # Try global
        if varName in self.globalVars:
            # Increment the counter if asked
            if increment:
                self.localVars[varName]['count'] += 1
            count = self.globalVars[varName]['count']
            if previous:
                count -= 1
            
            # Set varType if asked for
            if varType != None:
                self.localVars[varName]['varType'] = self._varTypeToString(varType)
            
            return z3Helpers.mk_var("{0}{1}".format(count,varName),eval(self.globalVars[varName]['varType']))

        # We failed :-(
        return None

    """


    def copy(self):
        """
        Return a copy of the Object Manager
        """

        return ObjectManager(
            variables = deepcopy(self.variables)
        )

