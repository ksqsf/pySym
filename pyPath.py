import z3
import ast
import logging
from pyState import State
from prettytable import PrettyTable
import sys
from copy import deepcopy
import pyState.Assign

logger = logging.getLogger("Path")

class Path():
    """
    Defines a path of execution.
    """
    
    def __init__(self,path=None,backtrace=None,state=None,source=None,callStack=None):
        """
        (optional) path = list of sequential actions. Derived by ast.parse
        (optional) backtrace = list of asts that happened before the current one
        (optional) state = State object for current path
        (optional) source = source code that we're looking at. This can make things prettier
        (optional) callStack = list of lists containing previous instruction list. This gets
                               pushed and popd when we call functions or go through if statements
        """
        
        self.path = [] if path is None else path
        self.backtrace = [] if backtrace is None else backtrace
        self.state = State() if state is None else state
        self.source = source
        self.callStack = [] if callStack is None else callStack

    def step(self):
        """
        Move the current path forward by one step
        Note, this actually makes a copy/s and returns them. The initial path isn't modified.
        Returns: A list of paths
        """
        # Get the current instruction
        inst = self.path.pop(0)
        
        # Return paths
        ret_paths = []

        if type(inst) == ast.Assign:
            path = self.copy()
            ret_paths = [path]
            pyState.Assign.handle(path.state,inst)
        
        elif type(inst) == ast.If:
            # On If statements we want to take both options
            path = self.copy()
            path2 = self.copy()
            ret_paths = [path,path2]
            
        
        else:
            err = "step: Unhandled element of type {0} at Line {1} Col {2}".format(type(inst),inst.lineno,inst.col_offset)
            logger.error(err)
            raise Exception(err)

        for path in ret_paths:
            # Once we're done, push this instruction to the done column
            path.backtrace.insert(0,inst)
        
        # Return the paths
        return ret_paths
    
    def printBacktrace(self):
        """
        Convinence function to print out what we've executed so far
        """
        source = self.source
        source = source.split("\n") if source != None else None
        
        table = PrettyTable(header=False,border=False,field_names=["lineno","line","element"])
        
        for inst in self.backtrace[::-1]:
            table.add_row([
                "Line {0}".format(inst.lineno),
                source[inst.lineno-1] if source != None else " ",
                inst])
        
        print(table)
    
    def copy(self):
        """
        Input:
            Nothing
        Action:
            Create a copy of the current Path object
        Returns:
            Copy of the path
        """
        return Path(
                path=deepcopy(self.path),
                backtrace=deepcopy(self.backtrace),
                state=self.state.copy(),
                source=deepcopy(self.source),
                callStack=deepcopy(self.callStack)
                )
