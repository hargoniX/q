#!/bin/bash
variant=$1
REPO_ROOT=`git rev-parse --show-toplevel`

pushd $REPO_ROOT > /dev/null
if [ "${variant}" == "pelletier" ]; then
  python benchmark/runner.py -d 3 -m pelletier -f benchmark/config.toml
elif [ "${variant}" == "casc29" ]; then
  python benchmark/runner.py -d 1 -m casc29 -c fof
  python benchmark/runner.py -d 1 -m casc29 -c fnt
elif [ "${variant}" == "casc24" ]; then
  python benchmark/runner.py -d 1 -m casc24 -c fof
  python benchmark/runner.py -d 1 -m casc24 -c fnt
else
  echo "${variant} has no controlflow! Existing Variants: 'pelletier', 'casc29', 'casc24'"
fi
popd > /dev/null
