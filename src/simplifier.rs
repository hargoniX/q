//! ## Clause SImplifier
//! This module contains the implementation of the cheap and the regular simplification algorithm
//! described in:
//! ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf)

use std::cmp::Ordering;

use log::info;
use rustc_hash::FxHashSet;

use crate::{
    clause::{Clause, ClauseSet, Literal, Polarity},
    discr_tree::DiscriminationTree,
    kbo::KboOrd,
    position::ClauseSetLiteralPosition,
    pretty_print::pretty_print,
    subst::Substitutable,
    term_bank::TermBank,
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

/// This function performs at most one rewrite for every literal in `literals` using equational
/// unit clauses clauses from `active` indexed in `rewriting_index`. If it found at least one
/// rewrite `true` is returned in order to enable applying this in a fixpoint loop.
fn forward_rewrite_step(
    literals: &mut [Literal],
    rewriting_index: &DiscriminationTree<ClauseSetLiteralPosition>,
    active: &ClauseSet,
    term_bank: &TermBank,
) -> bool {
    let mut modified = false;
    for lit in literals.iter_mut() {
        'lit_loop: for (lit_lhs, lit_rhs) in lit.clone().symm_term_iter() {
            for (subterm, subterm_pos) in lit_lhs.subterm_iter() {
                for candidate_pos in rewriting_index.get_generalisation_candidates(&subterm) {
                    let candidate_clause = active.get_by_id(candidate_pos.clause_id).unwrap();
                    let candidate_literal = candidate_clause.get_literal(candidate_pos.literal_id);
                    let candidate_lhs = candidate_pos.literal_side.get_side(candidate_literal);
                    let candidate_rhs = candidate_pos
                        .literal_side
                        .swap()
                        .get_side(candidate_literal);
                    // Shared side condition one: u|p = sigma(s)
                    if let Some(matching) = candidate_lhs.matching(&subterm) {
                        let subst_lhs = candidate_lhs.clone().subst_with(&matching, term_bank);
                        let subst_rhs = candidate_rhs.clone().subst_with(&matching, term_bank);
                        // Shared side condition two: sigma(s) > sigma(t)
                        if subst_lhs.kbo(&subst_rhs, term_bank) == Some(Ordering::Greater) {
                            let valid = match lit.get_pol() {
                                // Positive literals need at least one of these conditions:
                                // - p is not a root position (funnily enough the paper doesn't
                                //   actually say what lambda is)
                                // - !(u > v)
                                // - the literal `u = v` is not maximal in its original clause
                                Polarity::Eq => {
                                    if !subterm_pos.is_root()
                                        || candidate_lhs.kbo(candidate_rhs, term_bank)
                                            != Some(Ordering::Greater)
                                    {
                                        true
                                    } else {
                                        !candidate_clause
                                            .is_kbo_maximal(candidate_pos.literal_id, term_bank)
                                    }
                                }
                                // negative literals have no more side conditions
                                Polarity::Ne => true,
                            };

                            if valid {
                                let new_lhs =
                                    subterm_pos.replace_term_at(&lit_lhs, subst_rhs, term_bank);
                                let new_lit = Literal::new(new_lhs, lit_rhs, lit.get_pol());
                                info!(
                                    "Rewritten using: {}",
                                    pretty_print(candidate_clause, term_bank)
                                );
                                *lit = new_lit;
                                modified = true;
                                break 'lit_loop;
                            }
                        }
                    }
                }
            }
        }
    }

    modified
}

/// Rewrite `clause` using equational unit clauses clauses from `active` indexed in `rewriting_index`
/// until fixpoint.
fn forward_rewrite(
    clause: Clause,
    rewriting_index: &DiscriminationTree<ClauseSetLiteralPosition>,
    active: &ClauseSet,
    term_bank: &TermBank,
) -> RuleResult {
    info!("Rewriting clause: {}", pretty_print(&clause, term_bank));

    let mut modified = false;
    let mut literals = clause.to_vec();
    loop {
        let res = forward_rewrite_step(&mut literals, rewriting_index, active, term_bank);
        if !res {
            break;
        }
        modified = true;
    }

    let clause = Clause::new(literals);
    if modified {
        info!(
            "Rewriting resulting clause: {}",
            pretty_print(&clause, term_bank)
        );
    } else {
        info!("No rewrites found");
    }

    RuleResult { clause, modified }
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
    let res = forward_rewrite(clause, rewriting_index, active, term_bank);
    clause = res.clause;

    // Maybe we got more useless clauses to remove from rewriting
    if res.modified {
        let res = rule_dr_dd(clause, term_bank);
        clause = res.clause;
    }

    clause
}
