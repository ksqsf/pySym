import z3
import ast
import logging
from copy import copy, deepcopy

logger = logging.getLogger("State")

class State():
    """
    Defines the state of execution at any given point.
    """

    """
    localVars and globalVars are dicts containing variables and their constraint expressions
    
    localVars = {
        'x': {
            'var': x, # This is the actual z3.Int/z3.Array, etc object
            'expr': [
                'localVars['x']['var'] > 1',    # Actual expressions to go into solver
                'localVars['x']['var'] * 5 > 7'
            ]
        }
    }
    """
    
    def __init__(self,localVars=None,globalVars=None,solver=None):
    
        self.localVars = {} if localVars is None else localVars
        self.globalVars = {} if globalVars is None else globalVars
        self.solver = z3.Solver() if solver is None else solver


    def addConstraint(self,varName,constraint,assign=False):
        """
        Input:
            varName = String representation of the variable name (i.e.: 'x')
            constraint = A z3 expression to use as a constraint
            (optional) assign = Is this an assignment? If so, we destroy all
                                the old constraints on it
        Action:
            Add constraint given
        Returns:
            Nothing
        """
        # Sanity checks
        assert type(varName) == str
        assert "z3." in str(type(constraint))
        
        # Create local var if we don't have it already
        # TODO: Something in this if statement is corrupting something.. Double-linked list corruption and python crash on exit
        if varName not in self.localVars:
            self.localVars[varName] = {
                'var': z3.Int(varName),
                'expr': []
            }

        # If we're assigning
        if assign:
            self.localVars[varName]['expr'] = [constraint]

        # Otherwise just add it is as an expression
        else:
            self.localVars[varName]['expr'].append(constraint)

    

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
        s.reset()
        
        localVars = self.localVars
        
        # TODO: This is a bit dangerous... If I can get the concept working using eval needs to change
        # Populate the solver
        for var in localVars:
            s.add(localVars[var]['expr'])
            # Add in every expr we know
            #for expr in localVars[var]['expr']:
            #    s.add(eval(expr))
        
        # Check sat
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
        if var not in self.localVars:
            logger.debug("any_int: var '{0}' not in known localVars".format(var))
            return None
        
        # Try getting the value
        value = m.eval(self.localVars[var]['var'])
        
        # Check if we have a known solution
        # Assuming local for now
        if type(value) == z3.ArithRef:
            logger.debug("any_int: var '{0}' not found in solution".format(var))
            # No known solution
            return None

        # Check the type of the value
        if type(value) != z3.IntNumRef:
            logger.warn("any_int: var '{0}' not of type int, of type '{1}'".format(var,type(value)))
            return None
        
        # Made it! Return it as an int
        return int(value.as_string(),10)
    
    def copy(self):
        """
        Return a copy of the current state
        """
        
        def _copyVars(var):
            """
            Need to manually do copy for now since deep copy won't work on ctype
            This copy is basically a "deep-shallow" crossover copy
            Returns new copy
            """
            cp = {}
            for v in var:
                cp[v] = {
                    'var': copy(var[v]['var']),
                    'expr': [x for x in var[v]['expr']]
                }
            return cp
        
        return State(
            localVars=_copyVars(self.localVars),
            globalVars=_copyVars(self.globalVars)
            )
        
