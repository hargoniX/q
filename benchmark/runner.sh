#!/bin/bash
variant=$1
duration=${2:-"1"}
REPO_ROOT=`git rev-parse --show-toplevel`

pushd $REPO_ROOT > /dev/null
if [ "${variant}" == "pelletier" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/pelletier.toml
elif [ "${variant}" == "theorems-easy" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/theorems-easy.toml
elif [ "${variant}" == "theorems" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/theorems.toml
elif [ "${variant}" == "casc29" ]; then
  python benchmark/runner.py -d $duration -m casc29 -c fof
  python benchmark/runner.py -d $duration -m casc29 -c fnt
elif [ "${variant}" == "casc24" ]; then
  python benchmark/runner.py -d $duration -m casc24 -c fof
  python benchmark/runner.py -d $duration -m casc24 -c fnt
else
  echo "${variant} has no controlflow! Existing Variants: 'pelletier', 'casc29', 'casc24', 'theorems-easy', 'theorems'"
fi
popd > /dev/null
