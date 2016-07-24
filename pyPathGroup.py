from pyPath import Path

class PathGroup:

    def __init__(self,path=None,discardFailures=None,discardCompleted=None):
        """
        (optional) path = starting path object for path group
        (optional) discardFailure = Should we throw away bad paths to save on memory?
        (optional) discardCompleted = Should we discard completed paths to save on memory?
        """

        # Init the groups
        self.active = [path] if path is not None else []
        self.deadended = []
        self.completed = []
        self.errored = []
        self.found = []
        self.discardFailures = False if discardFailures is None else discardFailures
        self.discardCompleted = False if discardCompleted is None else discardCompleted


    def __str__(self):
        """
        Pretty print status
        """
        s = "<PathGroup with {0}>"

        # Figure out the attributes
        attr = []
        if len(self.active) > 0:
            attr.append("{0} active".format(len(self.active)))
        if len(self.deadended) > 0:
            attr.append("{0} deadended".format(len(self.deadended)))
        if len(self.completed) > 0:
            attr.append("{0} completed".format(len(self.completed)))
        if len(self.errored) > 0:
            attr.append("{0} errored".format(len(self.errored)))
        if len(self.found) > 0:
            attr.append("{0} found".format(len(self.found)))
        
        return s.format(', '.join(attr))

    def __repr__(self):
        return self.__str__()

    def explore(self,find=None):
        """
        Input:
            (optional) find = input line number to explore to
        Action:
            Step through script until line is found
        Returns:
            True if found, False if not
        """
        assert type(find) in [int,type(None)]
        
        while len(self.active) > 0:
            # Step the things
            self.step()

            # Blow away failed paths to save on memory
            if self.discardFailures:
                self.deadended = []
                self.errored = []

            # If we're really looking for something, throw away completed too
            if self.discardCompleted:
                self.completed = []
            
            if find:
                # Check for any path that has made it here
                for path in self.active:
                    if path.state.lineno() == find:
                        self.unstash(path,from_stash="active",to_stash="found")
                        return True


    def unstash(self,path=None,from_stash=None,to_stash=None):
        """
        Simply moving around paths for book keeping.
        """
        assert type(path) == Path
        assert type(from_stash) in [str, type(None)]
        assert type(to_stash) in [str, type(None)]

        if to_stash is not None:
            to_stash = getattr(self,to_stash)
            to_stash.append(path)

        if from_stash is not None:
            from_stash = getattr(self,from_stash)
            from_stash.remove(path)


    def step(self):
        """
        Step all active paths one step.
        """
        
        for currentPath in self.active:
            # It's possible this throws an exception on us
            try:
                paths_ret = currentPath.step()
                # Pop it off the block
                self.unstash(path=currentPath,from_stash="active")

            except Exception as e:
                currentPath.error = str(e)
                self.unstash(path=currentPath,from_stash="active",to_stash="errored")
                continue

            # If an empty list is returned, this path must be done
            if len(paths_ret) == 0:
                self.unstash(path=currentPath,to_stash="completed")
                continue
            
            # We have some return path
            else:
                for returnedPath in paths_ret:
                    # Make sure the returned path is possible
                    if not returnedPath.state.isSat():
                        self.unstash(path=returnedPath,to_stash="deadended")
                    else:
                        # We found our next step in the path
                        self.unstash(path=returnedPath,to_stash="active")
