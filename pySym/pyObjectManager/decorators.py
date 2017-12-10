def as_clone(orig_func):
    def run_from_clone(self, *args, **kwargs):
        # Transparently run from clone object if we have one
        if self._clone is not None:
            return getattr(self._clone,orig_func.__name__)(*args, **kwargs)

        # We're not a clone, run the original
        else:
            return orig_func(self, *args, **kwargs)

    return run_from_clone
