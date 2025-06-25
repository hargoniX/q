//! ## Trivial Clause Detection
//! This module contains the implementation of a trivial clause detection algorithm based on
//! ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf)

use crate::clause::Clause;

// TODO: ACD check if we want to support AC theories
pub fn is_trivial(clause: &Clause) -> bool {
    for (l1_id, l1) in clause.iter() {
        // Rule TD1, literals with reflexive literals are tautologies
        if l1.is_eq() && l1.get_lhs() == l1.get_rhs() {
            return true;
        }

        for (_, l2) in clause.iter_after(l1_id) {
            // Rule TD2, clauses with a literal and the negation of that literal are tautologies.
            if l1.is_negation_of(l2) {
                return true;
            }
        }
    }
    false
}
