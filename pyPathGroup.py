from pyPath import Path

class PathGroup:

    def __init__(self,path=None):
        """
        (optional) path = starting path object for path group
        """

        # Init the groups
        self.active = [path] if path is not None else []
        self.deadended = []
        self.completed = []
        self.errored = []

    def __str__(self):
        """
        Pretty print status
        """
        s = "<PathGroup with "
        if len(self.active) > 0:
            s += "{0} active".format(len(self.active))
        if len(self.deadended) > 0:
            s += "{0} deadended".format(len(self.deadended))
        if len(self.completed) > 0:
            s += "{0} completed".format(len(self.completed))
        if len(self.errored) > 0:
            s += "{0} errored".format(len(self.errored))
        s += ">"
        
        return s

    def __repr__(self):
        return self.__str__()


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
                        self.unstash(path=returnedPath,from_stash="active",to_stash="deadended")
                    else:
                        # We found our next step in the path
                        self.unstash(path=returnedPath,to_stash="active")
