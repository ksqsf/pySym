#!/usr/bin/env bash

# Figure out where we are
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

PYSYM_VENV="${HOME}/.virtualenvs/pySym"
Z3_DIR="${HOME}/opt/pySymZ3"

# Setup the venv
mkdir -p $PYSYM_VENV 2>/dev/null
mkdir -p $Z3_DIR 2>/dev/null

# Setup new virtual environment
virtualenv -p $(which python3) "$PYSYM_VENV"

# Activate it
source "${PYSYM_VENV}/bin/activate"

# Install requirements
pip install -r ${DIR}/requirements.txt

# These aren't strictly necessary, but they are if you want to test
pip3 install -U pytest
pip3 install python-coveralls
pip3 install coverage
pip3 install pytest-cov

pushd .
cd ~/opt

# Install Z3... This will be slow as f*
git clone https://github.com/Z3Prover/z3.git
cd z3

# Make the makefile
python scripts/mk_make.py --python

cd build
# Make it
make
make install

popd 2>/dev/null

echo "Install complete."
echo "Remember to activate the pySym virtualenv before using '$ source ${PYSYM_VENV}/bin/activate)'"
