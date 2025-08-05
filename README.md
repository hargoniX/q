# q
The Q superposition prover.

## Usage
For general purpose usage, see: `cargo run --release -- --help`.

To benchmark against specific problem sets, there are wrapper scripts:
```bash
bash benchmark/runner.sh <problemset_variant> <max_duration:1> <literal_selection_strategy:first-neg>
# Runs the problems stated in benchmark/pelletier.toml with
# - max_duration=1s
# - literal_selection_strategy=first-neg
# and compares them against the expected result
bash benchmark/runner.sh pelletier
bash benchmark/runner.sh pelletier 3 no-sel
# Plots simple time and comparison plots for the results of all the problem sets
bash benchmark/plotter.sh
```

## Problem Sets
### Simple TPTP Examples
Copied from the Test Problems section of <https://tptp.org/UserDocs/QuickGuide/>:
- Most Features to test parser: SYN000+1
- FOF Theorem: SYN075+1
- FOF CounterSatisfiable: MGT019+2
- FOF Unsatisfiable: KRS063+1
- FOF Satisfiable: KRS018+1

### Pelletier Problems
Credit goes to the [zipperposition repository](https://github.com/sneeuwballen/zipperposition/tree/master/examples/pelletier_problems):
cleaned up and maintained versions of the original pelletier problems.

### CASC
Two categories are interesting for us:
- FOF: First-Order Form theorems (axioms with a provable conjecture)
  - FNE: FOF with No Equality
  - FEQ: FOF with EQuality
- FNT: FOF Non-Theorems (axioms with a countersatisfiable conjecture, and satisfiable axioms without a conjecture)
  - FNN: FNT with No equality
  - FNQ: FNT with eQuality

Since the problems require a lot of storage, it is not sensible to check them into git.
For convenience there is an installer script to setup the problems locally.
It requires a pre-downloaded `Problems.tgz` from e.g. <https://tptp.org/CASC/29/Problems.tgz>,
and then you can run `bash benchmark/setup_casc29.sh`.

Note: there are currently two setup scripts `setup_casc29.sh` and `setup_casc24.sh`.
The casc24 `Problem.tgz` seemingly doesn't include all the required axiom files of its problems,
so we instead symlink to the casc29 ones.

### TPTP
To benchmark against the full TPTP problem set, there also exists a setup script: `setup_all.sh`.
Since the problems require a lot of storage, it is not sensible to check them into git.
It requires a pre-downloaded `TPTP-v9.0.0.tgz` from e.g. <https://tptp.org/TPTP/>.
