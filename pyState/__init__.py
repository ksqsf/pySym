import z3, z3util
import ast
import logging
from copy import copy, deepcopy
import pyState.BinOp

logger = logging.getLogger("State")

def get_all(f,rs=[]):
    """
    >>> x,y = Ints('x y')
    >>> a,b = Bools('a b')
    >>> get_all(Implies(And(x+y==0,x*2==10),Or(a,Implies(a,b==False))))
    [x, y, a, b]
    """
    if __debug__:
        assert z3util.is_expr(f)

    if z3util.is_const(f):
        return z3util.vset(rs + [f],str)

    else:
        for f_ in f.children():
            rs = get_all(f_,rs)

        return z3util.vset(rs,str)

def hasRealComponent(expr):
    """
    Input:
        expr = expression object
    Action:
        Checks if expression contains a real/non-int value or variable
    Returns:
        True if it has real componenet, False otherwise
    """
    return max([x.is_real() for x in get_all(expr)])


class State():
    """
    Defines the state of execution at any given point.
    """

    """
    localVars and globalVars are dicts containing variables and their constraint expressions
    
    localVars = {
        'x': {
            'varType': "z3.IntSort()", # Eval string to re-create the object's type on the fly. This is because z3 kept on crashing everything :-(
            'count': 0 # This helps us keep track of Static Single Assignment forms
        }
    }
    """
    
    def __init__(self,localVars=None,globalVars=None,solver=None):
    
        self.localVars = {} if localVars is None else localVars
        self.globalVars = {} if globalVars is None else globalVars
        self.solver = z3.Solver() if solver is None else solver

    def resolveObject(self,obj):
        """
        Input:
            obj = Some ast object (i.e.: ast.Name, ast.Num, etc)
        Action:
            Resolve object into something that can be used in a constraint
        Return:
            Resolved object
                ast.Num == int (i.e.: 6)
                ast.Name == z3 Object
                ast.BinOp == z3 expression of BinOp (i.e.: x + y)
        """
        t = type(obj)
        
        if t == ast.Name:
            return self.getZ3Var(obj.id)
        
        elif t == ast.Num:
            # Return real val or int val
            return z3.RealVal(obj.n) if type(obj.n) == float else z3.IntVal(obj.n)
        
        elif t == ast.BinOp:
            return pyState.BinOp.handle(self,obj)

        else:
            err = "resolveObject: unable to resolve object '{0}'".format(obj)
            logger.error(err)
            raise Exception(err)


    def _varTypeToString(self,varType):
        """
        Input:
            varType = z3 var sort (i.e.: z3.IntSort())
        Action:
            Resolves input type back to it's string (i.e.: "z3.IntSort()")
        Returns:
            String representation of varType
        """
        assert type(varType) in [z3.ArithSortRef,z3.BoolSortRef]
        
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


    def getZ3Var(self,varName,local=True,increment=False,varType=None,previous=False):
        """
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
        Action:
            Look-up variable
        Returns:
            z3 object variable with given name or None if it cannot be found
        """
        # It's important to look this up since we might not know going in
        # what the variable type is. This keeps track of that state.
        
        #TODO: Optimize this
        
        # If we're looking up local variable
        if local and varName in self.localVars:
            # Increment the counter if asked
            if increment:
                self.localVars[varName]['count'] += 1
            count = self.localVars[varName]['count']
            # Get previous
            if previous:
                count -= 1
            
            # Set varType if asked for
            if type(varType) != type(None):
                self.localVars[varName]['varType'] = self._varTypeToString(varType)
            
            return z3util.mk_var("{0}_{1}".format(varName,count),eval(self.localVars[varName]['varType']))
        
        # If we want to increment but we didn't find it, create it
        if local and varName not in self.localVars and increment:
            assert type(varType) in [z3.ArithSortRef,z3.BoolSortRef]
            
            # Time to create a new var!
            self.localVars[varName] = {
                'count': 0,
                'varType': self._varTypeToString(varType)
            }
            return z3util.mk_var("{0}_{1}".format(varName,self.localVars[varName]['count']),varType)
        
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
            
            return z3util.mk_var("{0}_{1}".format(varName,count),eval(self.globalVars[varName]['varType']))

        
        # We failed :-(
        return None


    def addConstraint(self,constraint):
        """
        Input:
            constraint = A z3 expression to use as a constraint
        Action:
            Add constraint given
        Returns:
            Nothing
        """
        # Sanity checks
        assert "z3." in str(type(constraint))
        
        # Add our new constraint to the solver
        self.solver.add(constraint)
        
        # Using iterative engine
        self.solver.push()
        

    def isSat(self):
        """
        Input:
            Nothing
        Action:
            Checks if the current state is satisfiable
            Note, it uses the local and global vars to create the solver on the fly
        Returns:
            Boolean True or False
        """
        # Get and clear our solver
        s = self.solver

        # Changing how I manage constraints. They're all going into the solver directly now
        # Just need to ask for updated SAT
        return s.check() == z3.sat
        
    def printVars(self):
        """
        Input:
            Nothing
        Action:
            Resolves current constraints and prints viable variables
        Returns:
            Nothing
        """
        # Populate model
        if not self.isSat():
            print("State does not seem possible.")
            return
        
        # Set model
        m = self.solver.model()
        
        # Loop through model, printing out vars
        for var in m:
            print("{0} == {1}".format(var.name(),m[var]))

    def any_int(self,var):
        """
        Input:
            var == variable name. i.e.: "x"
        Action:
            Resolve possible value for this variable
        Return:
            Discovered variable or None if none found
        """
        
        # Solve model first
        if not self.isSat():
            logger.debug("any_int: No valid model found")
            # No valid ints
            return None

        # Get model
        m = self.solver.model()
        
        # Check if we have it in our localVars
        if self.getZ3Var(var) == None:
            logger.debug("any_int: var '{0}' not in known localVars".format(var))
            return None

        var = self.getZ3Var(var)
        
        # Try getting the value
        value = m.eval(var)
        
        # Check if we have a known solution
        # Assuming local for now
        if type(value) == z3.ArithRef:
            logger.debug("any_int: var '{0}' not found in solution".format(var))
            # No known solution
            return None

        # Check the type of the value
        if type(value) != z3.IntNumRef:
            err = "any_int: var '{0}' not of type int, of type '{1}'".format(var,type(value))
            logger.error(err)
            raise Exception(err)
        
        # Made it! Return it as an int
        return int(value.as_string(),10)

    """
    def any_num(self,var):
        Input:
            var == variable name. i.e.: "x"
        Action:
            Resolve possible value for this variable
        Return:
            Discovered variable or None if none found
            This will attempt to discover the correct type of variable (int/real) and return
            that type.
        
        # TODO: Do better than this... Check stuff first. Try/Catch isn't a great practice
        
        ret = None
        try:
            ret = self.any_int(var)
        except:
            pass
        
        if ret != None:
            return ret
        
        # Intentionally not catching exceptions here
        return self.any_real(var)
    """

    def any_real(self,var):
        """
        Input:
            var == variable name. i.e.: "x"
        Action:
            Resolve possible value for this variable
        Return:
            Discovered variable or None if none found
            Note: this function will cast an Int to a Real implicitly if found
        """

        # Solve model first
        if not self.isSat():
            logger.debug("any_real: No valid model found")
            # No valid ints
            return None

        # Get model
        m = self.solver.model()

        if self.getZ3Var(var) == None:
            logger.debug("any_real: var '{0}' not found".format(var))
            return None
        
        var = self.getZ3Var(var)

        # Try getting the value
        value = m.eval(var)

        # Check if we have a known solution
        # Assuming local for now
        if type(value) == z3.ArithRef:
            logger.debug("any_real: var '{0}' not found in solution".format(var))
            # No known solution
            return None

        # Check the type of the value
        if type(value) not in [z3.IntNumRef,z3.RatNumRef]:
            err = "any_real: var '{0}' not of type int or real, of type '{1}'".format(var,type(value))
            logger.error(err)
            raise Exception(err) 

        # Made it! Return it as a real/float
        return float(eval(value.as_string()))


 
    def copy(self):
        """
        Return a copy of the current state
        """

        # Copy the solver state
        solverCopy = z3.Solver()
        solverCopy.add(self.solver.assertions())
        
        return State(
            localVars=deepcopy(self.localVars),
            globalVars=deepcopy(self.globalVars),
            solver=solverCopy
            )
        
