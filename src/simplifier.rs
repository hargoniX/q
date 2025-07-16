//! ## Clause SImplifier
//! This module contains the implementation of the cheap and the regular simplification algorithm
//! described in:
//! ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf)

use std::cmp::Ordering;

use log::info;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    clause::{Clause, ClauseSet, Literal, Polarity},
    discr_tree::DiscriminationTree,
    kbo::KboOrd,
    position::ClauseSetLiteralPosition,
    pretty_print::pretty_print,
    subst::Substitutable,
    term_bank::{Term, TermBank},
};

struct RuleResult {
    modified: bool,
    clause: Clause,
}

/// Apply the DR and DD rules to `clause` if possible.
fn rule_dr_dd(clause: Clause, term_bank: &TermBank) -> RuleResult {
    info!(
        "Applying DR DD to clause: {}",
        pretty_print(&clause, term_bank)
    );
    let new_lits = clause
        .iter()
        .map(|(_, lit)| lit)
        // Rule DR, remove x != x
        .filter(|lit| !(lit.is_ne() && lit.get_lhs() == lit.get_rhs()))
        // Rule DD, remove duplicate literals, note that literals both hash and eq up to symmetry
        // so we can use a HashSet for this
        .collect::<FxHashSet<&Literal>>();

    if new_lits.len() != clause.len() {
        let clause = Clause::new(new_lits.into_iter().cloned().collect());
        info!("DR DD result: {}", pretty_print(&clause, term_bank));
        RuleResult {
            modified: true,
            clause,
        }
    } else {
        info!("DR DD: no change");
        RuleResult {
            modified: false,
            clause,
        }
    }
}

struct ForwardRewriter<'a> {
    /// An index of all equational unit clauses from `active`.
    rewriting_index: &'a DiscriminationTree<ClauseSetLiteralPosition>,
    /// The current active clause set.
    active: &'a ClauseSet,
    term_bank: &'a TermBank,
    /// The clause we are performing rewriting on
    literals: Vec<Literal>,
    /// A rewriting cache, if a term `t` is mapped to:
    /// - Some(r) we know we can rewrite `t` to `r`
    /// - None we know `t` cannot be rewritten with any clause from `active`.
    cache: FxHashMap<Term, Option<Term>>,
}

impl ForwardRewriter<'_> {
    fn forward_rewrite(
        clause: Clause,
        rewriting_index: &DiscriminationTree<ClauseSetLiteralPosition>,
        active: &ClauseSet,
        term_bank: &TermBank,
    ) -> RuleResult {
        info!("Rewriting clause: {}", pretty_print(&clause, term_bank));
        let rewriter = ForwardRewriter {
            literals: clause.to_vec(),
            rewriting_index,
            active,
            term_bank,
            cache: FxHashMap::default(),
        };

        rewriter.fixpoint_rewrite()
    }

    fn step(&mut self) -> bool {
        let mut modified = false;
        for lit in self.literals.iter_mut() {
            'lit_loop: for (lit_lhs, lit_rhs) in lit.clone().symm_term_iter() {
                for (subterm, subterm_pos) in lit_lhs.subterm_iter() {
                    if let Some(result) = self.cache.get(&subterm) {
                        match result {
                            Some(res) => {
                                let new_lhs = subterm_pos.replace_term_at(
                                    &lit_lhs,
                                    res.clone(),
                                    self.term_bank,
                                );
                                let new_lit = Literal::new(new_lhs, lit_rhs, lit.get_pol());
                                *lit = new_lit;
                                modified = true;
                                info!("Rewritten using cache");
                                break 'lit_loop;
                            }
                            // We already know we are going to fail
                            None => break,
                        }
                    }

                    for candidate_pos in
                        self.rewriting_index.get_generalisation_candidates(&subterm)
                    {
                        let candidate_clause =
                            self.active.get_by_id(candidate_pos.clause_id).unwrap();
                        let candidate_literal =
                            candidate_clause.get_literal(candidate_pos.literal_id);
                        let candidate_lhs = candidate_pos.literal_side.get_side(candidate_literal);
                        let candidate_rhs = candidate_pos
                            .literal_side
                            .swap()
                            .get_side(candidate_literal);
                        // Shared side condition one: u|p = sigma(s)
                        if let Some(matching) = candidate_lhs.matching(&subterm) {
                            let subst_lhs =
                                candidate_lhs.clone().subst_with(&matching, self.term_bank);
                            let subst_rhs =
                                candidate_rhs.clone().subst_with(&matching, self.term_bank);
                            // Shared side condition two: sigma(s) > sigma(t)
                            if subst_lhs.kbo(&subst_rhs, self.term_bank) == Some(Ordering::Greater)
                            {
                                let valid = match lit.get_pol() {
                                    // Positive literals need at least one of these conditions:
                                    // - p is not a root position (funnily enough the paper doesn't
                                    //   actually say what lambda is)
                                    // - !(u > v)
                                    // - the literal `u = v` is not maximal in its original clause
                                    Polarity::Eq => {
                                        !subterm_pos.is_root()
                                            || candidate_lhs.kbo(candidate_rhs, self.term_bank)
                                                != Some(Ordering::Greater)
                                            || !candidate_clause.is_kbo_maximal(
                                                candidate_pos.literal_id,
                                                self.term_bank,
                                            )
                                    }
                                    // negative literals have no more side conditions
                                    Polarity::Ne => true,
                                };

                                if valid {
                                    let new_lhs = subterm_pos.replace_term_at(
                                        &lit_lhs,
                                        subst_rhs.clone(),
                                        self.term_bank,
                                    );
                                    let new_lit = Literal::new(new_lhs, lit_rhs, lit.get_pol());
                                    *lit = new_lit;
                                    modified = true;
                                    self.cache.insert(subterm, Some(subst_rhs));
                                    info!(
                                        "Rewritten using: {}",
                                        pretty_print(candidate_clause, self.term_bank)
                                    );
                                    break 'lit_loop;
                                }
                            }
                        }
                    }

                    // If we make it after this loop we know all candiates failed so we can cache
                    // failure:
                    self.cache.insert(subterm, None);
                }
            }
        }
        modified
    }

    fn fixpoint_rewrite(mut self) -> RuleResult {
        let mut modified = false;
        loop {
            let res = self.step();
            if !res {
                break;
            }
            modified = true;
        }

        let clause = Clause::new(self.literals);
        if modified {
            info!(
                "Rewriting resulting clause: {}",
                pretty_print(&clause, self.term_bank)
            );
        } else {
            info!("No rewrites found");
        }

        RuleResult { clause, modified }
    }
}

pub fn cheap_simplify(clause: Clause, term_bank: &TermBank) -> Clause {
    rule_dr_dd(clause, term_bank).clause
}

pub fn forward_simplify(
    clause: Clause,
    rewriting_index: &DiscriminationTree<ClauseSetLiteralPosition>,
    active: &ClauseSet,
    term_bank: &TermBank,
) -> Clause {
    let mut clause = clause;

    // We could do a round of DR DD here but we already know that clauses from passive are in DR/DD
    // normal form due to cheap_simplify so we can skip it.
    let res = ForwardRewriter::forward_rewrite(clause, rewriting_index, active, term_bank);
    clause = res.clause;

    // Maybe we got more useless clauses to remove from rewriting
    if res.modified {
        let res = rule_dr_dd(clause, term_bank);
        clause = res.clause;
    }

    clause
}
