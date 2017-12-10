import logging
logger = logging.getLogger("Project")
from . import Colorer

import enforce
import os

#@enforce.runtime_validation
class Project:

    def __init__(self, file, debug=False):
    
        if debug:
            logging.basicConfig(level=logging.DEBUG)

        self.file_name = file
        self.factory = Factory(self)

    ##############
    # Properties #
    ##############

    @property
    def factory(self):
        return self.__factory

    @factory.setter
    def factory(self, factory) -> None:
        self.__factory = factory

    @property
    def file_name(self) -> str:
        """str: Name of the file that's being symbolically executed."""
        return self.__file_name

    @file_name.setter
    def file_name(self, file_name: str) -> None:
        file_name = os.path.abspath(file_name)

        # Make sure this is a real file.
        if not os.path.isfile(file_name):
            raise Exception("Not a valid file: {file_name:s}".format(file_name=file_name))
        
        self.__file_name = file_name

from .Factory import Factory
