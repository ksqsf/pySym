import z3
import ast
import logging
from pyState import State
from prettytable import PrettyTable
import sys
from copy import copy
import pyState.Assign, pyState.If, pyState.AugAssign, pyState.FunctionDef, pyState.Expr, pyState.Return
from random import random

logger = logging.getLogger("Path")

class Path():
    """
    Defines a path of execution.
    """
    
    def __init__(self,path=None,backtrace=None,state=None,source=None):
        """
        (optional) path = list of sequential actions. Derived by ast.parse. Passed to state.
        (optional) backtrace = list of asts that happened before the current one
        (optional) state = State object for current path
        (optional) source = source code that we're looking at. This can make things prettier
        """
        
        path = [] if path is None else path
        self.backtrace = [] if backtrace is None else backtrace
        self.state = State(path=path) if state is None else state
        self.source = source

    def step(self):
        """
        Move the current path forward by one step
        Note, this actually makes a copy/s and returns them. The initial path isn't modified.
        Returns: A list of paths or empty list if the path is done 
        """
        
        # Step-it
        stateList = self.state.step()
        
        pathList = []

        for state in stateList:
            # New path
            path = self.copy()

            # New state
            path.state = state

            pathList.append(path)

        return pathList
    
    def printBacktrace(self):
        """
        Convinence function to print out what we've executed so far
        """
        source = self.source
        source = source.split("\n") if source != None else None
        
        table = PrettyTable(header=False,border=False,field_names=["lineno","line","element"])
        table.align = 'l'
        
        for inst in self.state.backtrace[::-1]:
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
        # TODO: Don't think i need to copy state in this...
        return Path(
                backtrace=copy(self.backtrace),
                state=self.state.copy(),
                source=copy(self.source),
                )
