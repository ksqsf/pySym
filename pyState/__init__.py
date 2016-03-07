import z3
import ast
import logging
from copy import copy, deepcopy
import z3util

logger = logging.getLogger("State")

class State():
    """
    Defines the state of execution at any given point.
    """

    """
    localVars and globalVars are dicts containing variables and their constraint expressions
    
    localVars = {
        'x': {
            'eval': "z3.Int('x')", # Eval string to re-create the object on the fly. This is because z3 kept on crashing everything :-(
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


    def getZ3Var(self,varName,local=True):
        """
        Input:
            varName = Variable name to retrieve Z3 object of
            (optional) local = Boolean if we're dealing with local scope
        Action:
            Look-up variable
        Returns:
            z3 object variable with given name or None if it cannot be found
        """
        # It's important to look this up since we might not know going in
        # what the variable type is. This keeps track of that state.
        
        # If we're looking up local variable
        if local and varName in self.localVars:
            return eval(self.localVars[varName]['eval'])
        
        # Try global
        if varName in self.globalVars:
            return eval(self.globalVars[varName]['eval'])
        
        # We failed :-(
        return None


    def addConstraint(self,constraint,assign=False,varType=None,varName=None):
        """
        Input:
            constraint = A z3 expression to use as a constraint
            (optional) assign = Is this an assignment? If so, we destroy all
                                the old constraints on it
            (optional) varType = String to eval to get this var (i.e.: "z3.Int('x')")
            (optional) varName = String representation of the variable name (i.e.: 'x')
                                 needed only if assign is True
        Action:
            Add constraint given
        Returns:
            Nothing
        """
        
        # Sanity checks
        assert type(varName) in [str,type(None)]
        assert "z3." in str(type(constraint))
        assert type(assign) == bool
        assert type(varType) in [type(None),str]
        
        if assign:
            assert type(varType) == str
        
            # Since we're assigning, create the var
            self.localVars[varName] = {
                'eval': varType,
            }
        
        # TODO: This is hackish... Re-work to be better 
        # If we're assigning
        if assign:
            # Get a copy of the var
            var = eval(varType)
            # Create a new solver too
            newSolver = z3.Solver()
            
            # Clear matching constraints here..
            for asrt in self.solver.assertions():
                shouldAdd = True
                # Only copy over constraints that do not constrain the new variable
                for x in z3util.get_vars(asrt):
                    # If this is our var
                    if x.eq(var):
                        shouldAdd = False
                        break

                if shouldAdd:
                    newSolver.add(asrt)
            
            # Change our solver to the new one
            self.solver = newSolver
            

        # Add our new constraint to the solver
        self.solver.add(constraint)
        

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
        if var not in self.localVars:
            logger.debug("any_int: var '{0}' not in known localVars".format(var))
            return None
        
        # Try getting the value
        value = m.eval(self.getZ3Var(var))
        
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

        # Copy the solver state
        solverCopy = z3.Solver()
        solverCopy.add(self.solver.assertions())
        
        return State(
            localVars=deepcopy(self.localVars),
            globalVars=deepcopy(self.globalVars),
            solver=solverCopy
            )
        
