//! ## Clause SImplifier
//! This module contains the implementation of the cheap and the regular simplification algorithm
//! described in:
//! ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf)

use std::collections::HashSet;

use crate::clause::{Clause, Literal};

pub fn cheap_simplify(clause: Clause) -> Clause {
    // TODO: RN, RP, ACS (likely only RN and RP), note that these require access to more clauses

    let new_lits = clause
        .iter()
        .map(|(_, lit)| lit)
        // Rule DR, remove x != x
        .filter(|lit| !(lit.is_ne() && lit.get_lhs() == lit.get_rhs()))
        // Rule DD, remove duplicate literals, note that literals both hash and eq up to symmetry
        // so we can use a HashSet for this
        .collect::<HashSet<&Literal>>();

    if new_lits.len() != clause.len() {
        Clause::new(new_lits.into_iter().cloned().collect())
    } else {
        clause
    }
}

pub fn simplify(clause: Clause) -> Clause {
    // TODO: more simplification
    cheap_simplify(clause)
}
