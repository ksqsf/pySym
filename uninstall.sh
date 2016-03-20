#!/bin/bash

# Simple uninstall

PYSYM_VENV="${HOME}/.virtualenvs/pySym"
Z3_DIR="${HOME}/opt/pySymZ3"
Z3_BASENAME=`basename $Z3_DIR`

rm -rf $PYSYM_VENV
rm -rf $Z3_DIR

echo "Uninstalled"
