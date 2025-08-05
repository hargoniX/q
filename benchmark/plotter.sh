#!/bin/bash
set -xe
REPO_ROOT=`git rev-parse --show-toplevel`

pushd $REPO_ROOT"/benchmark" > /dev/null
python plotter.py --mode time --duration 10 --variant custom -f pelletier.toml
python plotter.py --mode time --duration 10 --variant casc24
python plotter.py --mode time --duration 10 --variant casc29
python plotter.py --mode time --duration 1 --variant custom -f theorems.toml
python plotter.py --mode time --duration 1 --variant custom -f contradictory.toml
python plotter.py --mode time --duration 1 --variant custom -f counter_satisfiable.toml
python plotter.py --mode time --duration 1 --variant custom -f satisfiable.toml
python plotter.py --mode time --duration 1 --variant custom -f unsat.toml
python plotter.py --mode comp --duration 10 --variant casc24
python plotter.py --mode comp --duration 10 --variant casc29
python plotter.py --mode comp --duration 1 --variant custom -f theorems.toml
python plotter.py --mode comp --duration 1 --variant custom -f counter_satisfiable.toml
popd > /dev/null
