import z3
import ast
import logging

logger = logging.getLogger("State")


class ObjectManager:
    """
    Object Manager will keep track of objects. Generally, Objects will be variables such as ints, lists, strings, etc.
    """

    def __init__(self):
        # Not sure what needs to go here yet
        pass


    def copy(self):
        """
        Return a copy of the Object Manager
        """

        return ObjectManager()

