import z3
import ast
import logging

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

    
    def __init__(self,localVars={},globalVars={},solver=None):
    
        self.localVars = localVars
        self.globalVars = globalVars
        self.solver = z3.Solver() if solver == None else solver
    
    
    def _handleAssignNum(self,target,value):
        """
        Handle assigning a number to a variable (i.e.: x = 1)
        Update local variable dict and return
        """
        # The "x" part of "x" = 1
        varName = target.id
    
        # Grab the actual value
        valueActual = value.n
        
        # Right now only know how to deal with int
        if type(valueActual) != int:
            err = "Cannot handle non-int {2} set at line {0} col {1}".format(value.lineno,value.col_offset,type(valueActual))
            logger.error(err)
            raise Exception(err)
    
        # Create local var if we don't have it already
        if varName not in self.localVars:
            self.localVars[varName] = {
                'var': z3.Int(varName),
                'expr': []
            }
    
        # Since this is a set of a concrete, we throw away the old
        # constraints and just set this new one
        self.localVars[varName]['expr'] = ['localVars[\'{0}\'][\'var\'] == {1}'.format(varName,valueActual)]
    

    def handleAssign(self,element):
        """
        Attempt to handle the assign element
        """
    
        # Targets are what is being set
        targets = element.targets
    
        # Value is what to set them to
        value = element.value
    
        # Only handling single targets for now
        if len(targets) != 1:
            err = "Cannot handle multiple variable set at Line {0} Col {1}".format(element.lineno,element.col_offset)
            logger.error(err)
            raise Exception(err)
    
        # Clear up the naming
        target = targets[0]

        # Call appropriate handlers
        if type(value) == ast.Num:
            self._handleAssignNum(target,value)
    
        else:
            err = "Don't know how to assign type {0} at line {1} col {2}".format(type(value),value.lineno,value.col_offset)
            logger.error()
            raise Exception(err)
    
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
            # Add in every expr we know
            for expr in localVars[var]['expr']:
                s.add(eval(expr))
        
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
