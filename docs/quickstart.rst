========================
pySym Quick-Start
========================

Running Your First Program
==========================

Assuming that you have already `installed <installation.html>`_ pySym, actiate
your virtual environment and load up a source::

   $ workon pySym
   (pySym)$ ipython

For the moment, loading is done through a string mechanism. You can either copy
and paste the script you want to execute or load it using file:

.. code-block:: python

   In [1]: from pyPath import Path

   In [2]: import ast

   In [3]: import Colorer

   In [4]: from pyPathGroup import PathGroup

   In [5]: with open("test","r") as f:
      ...:         b = ast.parse(source).body
      ...:         p = Path(b,source=source)
      ...:         pg = PathGroup(p)

You can now run it by simply executing:

.. code-block:: python
    
    In [6]: pg.explore()

See the `examples <examples.html>`_ page for example programs.
