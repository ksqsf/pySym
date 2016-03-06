import z3
import ast
import logging
from pyState import State
from prettytable import PrettyTable

logger = logging.getLogger("Path")

class Path():
    """
    Defines a path of execution.
    """
    
    def __init__(self,path=[],backtrace=[],state=State(),source=None):
        """
        (optional) path = list of sequential actions. Derived by ast.parse
        (optional) backtrace = list of asts that happened before the current one
        (optional) state = State object for current path
        (optional) source = source code that we're looking at. This can make things prettier
        """
        
        self.path = path
        self.backtrace = backtrace
        self.state = state
        self.source = source

    def step(self):
        """
        Move the current path forward by one step
        """
        # Get the current instruction
        inst = self.path.pop(0)

        if type(inst) == ast.Assign:
            self.state.handleAssign(inst)
        else:
            logger.error("step: Unhandled element of type {0} at Line {1} Col {2}".format(type(inst),inst.lineno,inst.col_offset))
            exit(1)

        # Once we're done, push this instruction to the done column
        self.backtrace.insert(0,inst)
    
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
