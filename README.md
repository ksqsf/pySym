# pySym
Python Symbolic Execution

[ ![Codeship Status for Owlz/pySym](https://codeship.com/projects/691a2930-c591-0133-c81b-4e8753dd3f97/status?branch=master)](https://codeship.com/projects/138556)
[![Coverage Status](https://coveralls.io/repos/github/Owlz/pySym/badge.svg?branch=HEAD)](https://coveralls.io/github/Owlz/pySym?branch=HEAD)

# Disclaimer
This is just for me to mess around with symbolic execution of python scripts. Likely not going to work/be broken so probably not something you care to play with.

# Install
Basic installation requires installing z3 with python bindings. It's recommended to install this into a python virtualenv to keep things a bit more clean.

I created a setup script. It works on Ubuntu 15.04. It is untested on other releases.

```bash
$ ./setup.sh
```

# Tests
Tests need to be done from somewhere that has z3 access. For my env, this means the virtual environment.

```bash
$ workon pySym
(pySym)$ py.test --cov=. --cov-config=.coveragerc
```

# Basic Example
A lot of the layout for pySym is shamelessly stolen from the angr project. If you're familiar with their calls, this will make sense to you.

As an example of what is currently working, take the following script:

```python
x = 1.5
y = 1
if x == 1:
    y = 2
else:
    y += x
```

While basic, it can show how stepping through a program works. The following python script excersizes this functionality:

```python
from pyPath import Path
import ast
import logging
import Colorer
logging.basicConfig(level=logging.DEBUG,format='%(name)s - %(levelname)s - %(message)s', datefmt='%m/%d/%Y %I:%M:%S %p')

source = """
x = 1.5
y = 1
if x == 1:
    y = 2
else:
    y += x
"""
b = ast.parse(source).body
p = Path(b,source=source)
p = p.step()[0]
p = p.step()[0]
ifSide,elseSide = p.step()
elseSide = elseSide.step()[0]
```

Note that I put the source inline. It doens't have to be. You could read it from a file or really anywhere else that gives you a string. What happens in this script is the following:

b = ast.parse(source).body -- This call parses out the mini script into functional blocks that we use.

p = Path(b,source=source) -- This sets up our initial path variable. For now, this starts at the top of the script and works its way down.

p = p.step()[0] -- These are stepping through the program. The path itself does not get modified. However, a copy of the path returns. Note on the third step we encounter an if statement that causes the path to branch into two (taking both).

elseSide = elseSide.step()[0] -- Perform our final step, executing "y += x"

We can see if our given path is viable by checking path.state.isSat()

```python
In [2]: ifSide.state.isSat()
Out[2]: False

In [3]: elseSide.state.isSat()
Out[3]: True
```

As expected, the else is the only viable path through here. We can also ask what the variable should be at this point:

```python
In [4]: elseSide.state.any_real('y')
Out[4]: 2.5
```

Again, nothing fancy but it does give us the value we would expect from this path. If we wanted to discover what this elsePath looked like from start to finish, we can ask that as well:

```python
In [5]: elseSide.printBacktrace()
 Line 2  x = 1.5     <_ast.Assign object at 0x7f9263f8a438>    
 Line 3  y = 1       <_ast.Assign object at 0x7f9263f8d080>    
 Line 4  if x == 1:  <_ast.If object at 0x7f926985b550>        
 Line 7      y += x  <_ast.AugAssign object at 0x7f9263f8d400> 
```

Much work left to do as I have only implimented a limited set of operations. However, this is pretty neat!

# To-Do
Here's a list of things I have left to implement. This is really just a subset of things, but these are high on my list.

* ifelse inline (x = 1 if 1 > 2 else 2)
* list comprehensions
* function calls (mostly completed)
 * kwargs
 * starargs
* imports
* "global" keyword
* symbolic strings
* symbolic ints
* symbolic arrays
* function annotations
* path groups
* while loop
* for loop
* built-in calls
 * print
