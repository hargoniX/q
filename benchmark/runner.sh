#!/bin/bash
variant=$1
duration=${2:-"1"}
REPO_ROOT=`git rev-parse --show-toplevel`

pushd $REPO_ROOT > /dev/null
if [ "${variant}" == "pelletier" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/pelletier.toml
elif [ "${variant}" == "casc29" ]; then
  python benchmark/runner.py -d $duration -m casc29 -c fof
  python benchmark/runner.py -d $duration -m casc29 -c fnt
elif [ "${variant}" == "casc24" ]; then
  python benchmark/runner.py -d $duration -m casc24 -c fof
  python benchmark/runner.py -d $duration -m casc24 -c fnt
elif [ "${variant}" == "contra" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/contradictory.toml
elif [ "${variant}" == "countersat" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/counter_satisfiable.toml
elif [ "${variant}" == "sat" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/satisfiable.toml
elif [ "${variant}" == "theorems" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/theorems.toml
elif [ "${variant}" == "theorems-easy" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/theorems-easy.toml
elif [ "${variant}" == "unsat" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/unsat.toml
else
  echo "Usage: runner.sh <variant> <max_duration_in_s:1>"
  echo ""
  echo "Given variant '${variant}' has no controlflow!"
  echo "Existing Variants:"
  echo "- Pelletier Problems: 'pelletier'"
  echo "- CASC24 FOF/FNT: 'casc24'"
  echo "- CASC29 FOF/FNT: 'casc29'"
  echo "- Full TPTP FOF: 'contra', 'countersat', 'sat', 'theorems', 'unsat'"
  echo "- Easy TPTP FOF Theorems subset: 'theorems-easy'"
fi
popd > /dev/null
