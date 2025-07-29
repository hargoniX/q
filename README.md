# q
The Q superposition prover

## Example Problems

Copied from the Test Problems section of <https://tptp.org/UserDocs/QuickGuide/>:
- Most Features to test parser: SYN000+1
- FOF Theorem: SYN075+1
- FOF CounterSatisfiable: MGT019+2
- FOF Unsatisfiable: KRS063+1
- FOF Satisfiable: KRS018+1

## CASC
Two categories are interesting for us:
- FOF: First-Order Form theorems (axioms with a provable conjecture).
  - FNE – FOF with No Equality, e.g., COM003+1.
  - FEQ – FOF with EQuality, e.g., SEU147+3.
- FNT: FOF Non-Theorems (axioms with a countersatisfiable conjecture, and satisfiable axioms without a conjecture).
  - FNN – FNT with No equality, e.g., KRS173+1.
  - FNQ – FNT with eQuality, e.g., MGT033+2.

Since the problems require a lot of storage, it is not sensible to check them into git.
For convenience there is an installer script to setup the problems locally.
It requires a pre-downloaded `Problems.tgz` from e.g. <https://tptp.org/CASC/29/Problems.tgz>, and then one can run `bash benchmark/setup_casc29.sh`.

Note: there are currently two setup scripts `setup_casc29.sh` and `setup_casc24.sh`.
The casc24 `Problem.tgz` seemingly doesn't include all the required axiom files of its problems,
so we instead symlink to the casc29 ones.

## TPTP
To benchmark against the full TPTP problem set, there exists the setup script `setup_all.sh`.
Since the problems require a lot of storage, it is not sensible to check them into git.
It requires a pre-downloaded `TPTP-v9.0.0.tgz` from e.g. <https://tptp.org/TPTP/>.
