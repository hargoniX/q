#!/bin/bash
variant=$1
duration=${2:-"1"}
SELECTION_STRATEGY=${3:-"zipper-sel"}
REPO_ROOT=`git rev-parse --show-toplevel`

pushd $REPO_ROOT > /dev/null
if [ "${variant}" == "pelletier" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/pelletier.toml -s $SELECTION_STRATEGY
elif [ "${variant}" == "casc29" ]; then
  python benchmark/runner.py -d $duration -m casc29 -c fof -s $SELECTION_STRATEGY
  python benchmark/runner.py -d $duration -m casc29 -c fnt -s $SELECTION_STRATEGY
elif [ "${variant}" == "casc29-ueq" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/casc29_ueq.toml -s $SELECTION_STRATEGY
elif [ "${variant}" == "casc24" ]; then
  python benchmark/runner.py -d $duration -m casc24 -c fof -s $SELECTION_STRATEGY
  python benchmark/runner.py -d $duration -m casc24 -c fnt -s $SELECTION_STRATEGY
elif [ "${variant}" == "contra" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/contradictory.toml -s $SELECTION_STRATEGY
elif [ "${variant}" == "countersat" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/counter_satisfiable.toml -s $SELECTION_STRATEGY
elif [ "${variant}" == "sat" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/satisfiable.toml -s $SELECTION_STRATEGY
elif [ "${variant}" == "theorems" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/theorems.toml -s $SELECTION_STRATEGY
elif [ "${variant}" == "unsat" ]; then
  python benchmark/runner.py -d $duration -m pelletier -f benchmark/unsat.toml -s $SELECTION_STRATEGY
else
  echo "Usage: runner.sh <variant> <max_duration_in_s:1>"
  echo ""
  echo "Given variant '${variant}' has no controlflow!"
  echo "Existing Variants:"
  echo "- Pelletier Problems: 'pelletier'"
  echo "- CASC24 FOF/FNT: 'casc24'"
  echo "- CASC29 FOF/FNT: 'casc29'"
  echo "- CASC29 UEQ: 'casc29-ueq'"
  echo "- Full TPTP FOF: 'contra', 'countersat', 'sat', 'theorems', 'unsat'"
fi
popd > /dev/null
