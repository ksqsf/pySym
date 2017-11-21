"""A setuptools based setup module.

See:
https://packaging.python.org/en/latest/distributing.html
https://github.com/pypa/sampleproject
"""

# Always prefer setuptools over distutils
from setuptools import setup, find_packages
# To use a consistent encoding
from codecs import open
from os import path

here = path.abspath(path.dirname(__file__))

#with open(path.join(here, 'README.md'), encoding='utf-8') as f:
#    long_description = f.read()
long_description = "See website for more info."

setup(
    name='pySym',
    version='0.0.1',
    description='Symbolic execution of python source.',
    long_description=long_description,
    # The project's main homepage.
    url='https://github.com/bannsec/pySym',
    author='Michael Bann',
    author_email='self@bannsecurity.com',
    license='MIT',
    classifiers=[
        # Pick your license as you wish (should match "license" above)
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python :: 3',
        'Operating System :: POSIX :: Linux',
        'Environment :: Console'
    ],
    keywords='symbolic execution python',
    packages=find_packages(exclude=['contrib', 'docs', 'tests', 'longer_tests']),
    install_requires=['z3-solver','prettytable'],
    extras_require={
        'dev': ['pytest','python-coveralls','coverage','pytest-cov','pytest-xdist','ipython'],
    },

    #entry_points={
    #    'console_scripts': [
    #        'pySym = pySym.pySym:main',
    #    ],
    #},

)

