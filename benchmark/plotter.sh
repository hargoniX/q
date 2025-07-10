#!/bin/bash
set -xe
python plotter.py --mode time --duration 3 --variant pelletier
python plotter.py --mode time --duration 10 --variant casc24
python plotter.py --mode time --duration 10 --variant casc29
