#!/bin/bash
set -xe
REPO_ROOT=`git rev-parse --show-toplevel`

pushd $REPO_ROOT"/benchmark" > /dev/null
python plotter.py --mode time --duration 10 --variant pelletier -f pelletier.toml
python plotter.py --mode time --duration 10 --variant casc24
python plotter.py --mode time --duration 10 --variant casc29
python plotter.py --mode time --duration 1 --variant pelletier -f theorems.toml
python plotter.py --mode time --duration 1 --variant pelletier -f contradictory.toml
python plotter.py --mode time --duration 1 --variant pelletier -f counter_satisfiable.toml
python plotter.py --mode time --duration 1 --variant pelletier -f satisfiable.toml
python plotter.py --mode time --duration 1 --variant pelletier -f unsat.toml
python plotter.py --mode comp --duration 10 --variant casc24
python plotter.py --mode comp --duration 10 --variant casc29
python plotter.py --mode comp --duration 1 --variant pelletier -f theorems.toml
python plotter.py --mode comp --duration 1 --variant pelletier -f counter_satisfiable.toml
popd > /dev/null
