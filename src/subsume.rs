//! # Subsumption
//! This module implements the Algorithm of Stillman for clause-to-clause subsumption.
//! In the future adding improvements from [Towards Efficient Subsumption](https://link.springer.com/chapter/10.1007/BFb0054276)
//! as well as a feature vector based index from [Simple and Efficient Clause Subsumption with Feature Vector Indexing](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz2013-FVI.pdf)
//! are going to be integrated as well. The concrete implementation of the algorithms is based on
//! the implementation in [Zipperposition](https://github.com/sneeuwballen/zipperposition/blob/050072e01d8539f9126993482b595e09f921f66a/src/prover_calculi/superposition.ml#L2737).

use crate::{
    clause::{Clause, Literal},
    subst::Substitution,
};

impl Clause {
    fn subsumes_aux(subsuming: &[Literal], target: &[Literal], unused: Vec<bool>, subst: Substitution) -> bool {
        if subsuming.len() == 0 {
            return true;
        }

        for (t_idx, t_lit) in unused.iter().enumerate().filter(|(_, b)| **b).map(|(idx, _)| (idx, &target[idx])).filter(|(_, t_lit)| t_lit.get_pol() == subsuming[0].get_pol()) {
            let t_lhs = t_lit.get_lhs();
            let t_rhs = t_lit.get_rhs();
            for (s_lhs, s_rhs) in subsuming[0].symm_term_iter() {
                let subst = subst.clone();
                if let Some(subst) = s_lhs.matching_partial(&t_lhs, Some(subst)) {
                    if let Some(subst) = s_rhs.matching_partial(&t_rhs, Some(subst)) {
                        let mut unused = unused.clone();
                        unused[t_idx] = false;
                        if Clause::subsumes_aux(&subsuming[1..], target, unused, subst) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    pub fn subsumes(&self, other: &Self) -> bool {
        if self.len() > other.len() {
            return false;
        }
        Clause::subsumes_aux(&self.literals, &other.literals, vec![true; other.len()], Substitution::new())
    }
}
