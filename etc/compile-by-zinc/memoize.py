
# from http://code.activestate.com/recipes/578231-probably-the-fastest-memoization-decorator-in-the-/

__all__ = ["memoize"]

def memoize(f):
    """ Memoization decorator for a function taking one or more arguments. """
    class memodict(dict):
        def __getitem__(self, *key, **kwkey):
            return dict.__getitem__(self, (tuple(key), tuple((k, kwkey[k]) for k in sorted(kwkey.keys()))))

        def __missing__(self, key):
            args, kwargs = key
            self[key] = ret = f(*args, **dict(kwargs))
            return ret

    return memodict().__getitem__
