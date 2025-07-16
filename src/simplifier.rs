//! ## Clause SImplifier
//! This module contains the implementation of the cheap and the regular simplification algorithm
//! described in:
//! ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf)

use std::cmp::Ordering;

use log::info;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    clause::{Clause, ClauseId, ClauseSet, Literal, Polarity},
    discr_tree::DiscriminationTree,
    kbo::KboOrd,
    position::{Position, UnitClauseSetPosition},
    pretty_print::pretty_print,
    subst::Substitutable,
    superposition::SuperpositionState,
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
    rewriting_index: &'a DiscriminationTree<UnitClauseSetPosition>,
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

// TODO: we could do this in one term traversal instead of like this but let's stick with a naive
// impl for now
impl ForwardRewriter<'_> {
    fn forward_rewrite(
        clause: Clause,
        rewriting_index: &DiscriminationTree<UnitClauseSetPosition>,
        active: &ClauseSet,
        term_bank: &TermBank,
    ) -> RuleResult {
        info!(
            "Forward rewriting clause: {}",
            pretty_print(&clause, term_bank)
        );
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
        for tgt_lit_idx in 0..self.literals.len() {
            let tgt_lit = &self.literals[tgt_lit_idx];
            'tgt_loop: for (tgt_lit_lhs, tgt_lit_rhs) in tgt_lit.clone().symm_term_iter() {
                for (tgt_subterm, tgt_subterm_pos) in tgt_lit_lhs.subterm_iter() {
                    if let Some(result) = self.cache.get(&tgt_subterm) {
                        match result {
                            Some(res) => {
                                let new_lhs = tgt_subterm_pos.replace_term_at(
                                    &tgt_lit_lhs,
                                    res.clone(),
                                    self.term_bank,
                                );
                                let new_lit = Literal::new(new_lhs, tgt_lit_rhs, tgt_lit.get_pol());
                                self.literals[tgt_lit_idx] = new_lit;
                                modified = true;
                                info!("Forward rewritten using cache");
                                break 'tgt_loop;
                            }
                            // We already know we are going to fail
                            None => break,
                        }
                    }

                    for rw_rule_pos in self
                        .rewriting_index
                        .get_generalisation_candidates(&tgt_subterm)
                    {
                        let rw_rule_literal = self
                            .active
                            .get_by_id(rw_rule_pos.clause_id)
                            .unwrap()
                            .first_lit();
                        let rw_rule_lhs = rw_rule_pos.literal_side.get_side(rw_rule_literal);
                        let rw_rule_rhs = rw_rule_pos.literal_side.swap().get_side(rw_rule_literal);
                        // Shared side condition one: u|p = sigma(s)
                        if let Some(matching) = rw_rule_lhs.matching(&tgt_subterm) {
                            let subst_lhs =
                                rw_rule_lhs.clone().subst_with(&matching, self.term_bank);
                            let subst_rhs =
                                rw_rule_rhs.clone().subst_with(&matching, self.term_bank);
                            // Shared side condition two: sigma(s) > sigma(t)
                            if subst_lhs.kbo(&subst_rhs, self.term_bank) == Some(Ordering::Greater)
                            {
                                let valid = match tgt_lit.get_pol() {
                                    // Positive literals need at least one of these conditions:
                                    // - p is not a root position (funnily enough the paper doesn't
                                    //   actually say what lambda is)
                                    // - !(u > v)
                                    // - the literal `u = v` is not maximal in its original clause
                                    Polarity::Eq => {
                                        if !tgt_subterm_pos.is_root()
                                            || tgt_lit_lhs.kbo(&tgt_lit_rhs, self.term_bank)
                                                != Some(Ordering::Greater)
                                        {
                                            true
                                        } else {
                                            !(0..self.literals.len())
                                                .filter(|other_idx| *other_idx != tgt_lit_idx)
                                                .all(|other_idx| {
                                                    let other_lit = &self.literals[other_idx];
                                                    let ord =
                                                        tgt_lit.kbo(other_lit, self.term_bank);
                                                    ord != Some(Ordering::Less)
                                                })
                                        }
                                    }
                                    // negative literals have no more side conditions
                                    Polarity::Ne => true,
                                };

                                if valid {
                                    let new_lhs = tgt_subterm_pos.replace_term_at(
                                        &tgt_lit_lhs,
                                        subst_rhs.clone(),
                                        self.term_bank,
                                    );
                                    let new_lit =
                                        Literal::new(new_lhs, tgt_lit_rhs, tgt_lit.get_pol());
                                    self.literals[tgt_lit_idx] = new_lit;
                                    modified = true;
                                    self.cache.insert(tgt_subterm, Some(subst_rhs));
                                    info!(
                                        "Forward rewritten using: {}",
                                        pretty_print(rw_rule_literal, self.term_bank)
                                    );
                                    break 'tgt_loop;
                                }
                            }
                        }
                    }

                    // If we make it after this loop we know all candiates failed so we can cache
                    // failure:
                    self.cache.insert(tgt_subterm, None);
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
                "Forward rewriting resulting clause: {}",
                pretty_print(&clause, self.term_bank)
            );
        } else {
            info!("No forward rewrites found");
        }

        RuleResult { clause, modified }
    }
}

struct BackwardRewriter<'a, 'b> {
    state: &'a mut SuperpositionState<'b>,
    equation: &'a Literal,
    new_clauses: FxHashMap<ClauseId, Clause>,
    cache: FxHashMap<Term, Term>,
}

impl<'a, 'b> BackwardRewriter<'a, 'b> {
    fn backward_rewrite(clause: &Clause, state: &mut SuperpositionState<'_>) -> Vec<Clause> {
        if clause.is_unit() {
            let lit = clause.first_lit();
            if lit.is_eq() {
                info!(
                    "Backward rewriting using: {}",
                    pretty_print(lit, state.term_bank)
                );
                let mut rewriter = BackwardRewriter {
                    state,
                    equation: lit,
                    new_clauses: FxHashMap::default(),
                    cache: FxHashMap::default(),
                };
                rewriter.find_candidates();
                return rewriter.new_clauses.into_values().collect();
            }
        }
        vec![]
    }

    fn find_candidates(&mut self) {
        for (rw_rule_lhs, rw_rule_rhs) in self.equation.symm_term_iter() {
            // if we have lhs = rhs and know lhs < rhs we know we will never rewrite in this
            // orientation already
            if rw_rule_lhs.kbo(&rw_rule_rhs, self.state.term_bank) == Some(Ordering::Less) {
                continue;
            }

            for tgt_pos in self
                .state
                .subterm_index
                .get_instance_candidates(&rw_rule_lhs)
            {
                if self.new_clauses.contains_key(&tgt_pos.clause_id) {
                    // We already performed backward rewriting on this one, let's wait for
                    // cheap_simplify to handle further business.
                    continue;
                }

                let tgt_clause_pos = &tgt_pos.clause_pos;
                let tgt_lit_pos = &tgt_clause_pos.literal_pos;
                let tgt_subterm_pos = &tgt_lit_pos.term_pos;
                let tgt_lit_id = tgt_clause_pos.literal_id;
                let tgt_clause = self
                    .state
                    .active
                    .get_by_id(tgt_pos.clause_id)
                    .unwrap()
                    .clone();
                let tgt_lit = tgt_clause.get_literal(tgt_lit_id);
                let tgt_lit_lhs = tgt_lit_pos.literal_side.get_side(tgt_lit);
                let tgt_lit_rhs = tgt_lit_pos.literal_side.swap().get_side(tgt_lit);
                let tgt_subterm = tgt_subterm_pos.term_at(tgt_lit_lhs);

                if let Some(res) = self.cache.get(tgt_subterm) {
                    info!(
                        "Found backward rewriting opportunity for: {}",
                        pretty_print(&tgt_clause, self.state.term_bank)
                    );
                    let new_lhs = tgt_subterm_pos.replace_term_at(
                        tgt_lit_lhs,
                        res.clone(),
                        self.state.term_bank,
                    );
                    let new_lit = Literal::new(new_lhs, tgt_lit_rhs.clone(), tgt_lit.get_pol());

                    let id = tgt_clause.get_id();
                    let mut lits = tgt_clause.to_vec();
                    lits[tgt_lit_id.0] = new_lit;
                    let new_clause = Clause::new(lits);

                    info!(
                        "Backward rewritten using cache to: {}",
                        pretty_print(&new_clause, self.state.term_bank)
                    );

                    self.new_clauses.insert(id, new_clause);
                    continue;
                }

                if let Some(matching) = rw_rule_lhs.matching(tgt_subterm) {
                    let subst_lhs = rw_rule_lhs
                        .clone()
                        .subst_with(&matching, self.state.term_bank);
                    let subst_rhs = rw_rule_rhs
                        .clone()
                        .subst_with(&matching, self.state.term_bank);
                    if subst_lhs.kbo(&subst_rhs, self.state.term_bank) == Some(Ordering::Greater) {
                        let valid = match tgt_lit.get_pol() {
                            // Positive literals need at least one of these conditions:
                            // - p is not a root position (funnily enough the paper doesn't
                            //   actually say what lambda is)
                            // - !(u > v)
                            // - the literal `u = v` is not maximal in its original clause
                            Polarity::Eq => {
                                if !tgt_subterm_pos.is_root()
                                    || tgt_lit_lhs.kbo(tgt_lit_rhs, self.state.term_bank)
                                        != Some(Ordering::Greater)
                                {
                                    true
                                } else {
                                    !tgt_clause
                                        .iter()
                                        .filter(|(other_id, _)| *other_id != tgt_lit_id)
                                        .all(|(_, other_lit)| {
                                            let ord = tgt_lit.kbo(other_lit, self.state.term_bank);
                                            ord != Some(Ordering::Less)
                                        })
                                }
                            }
                            // negative literals have no more side conditions
                            Polarity::Ne => true,
                        };

                        if valid {
                            info!(
                                "Found backward rewriting opportunity for: {}",
                                pretty_print(&tgt_clause, self.state.term_bank)
                            );
                            let new_lhs = tgt_subterm_pos.replace_term_at(
                                tgt_lit_lhs,
                                subst_rhs.clone(),
                                self.state.term_bank,
                            );
                            self.cache.insert(tgt_subterm.clone(), subst_rhs);

                            // Ordering here is actually crucial to maintain subterm indexing
                            // consistency.
                            let new_lit =
                                Literal::new(new_lhs, tgt_lit_rhs.clone(), tgt_lit.get_pol());

                            let id = tgt_clause.get_id();
                            let mut lits = tgt_clause.to_vec();
                            lits[tgt_lit_id.0] = new_lit;
                            let new_clause = Clause::new(lits);

                            info!(
                                "Backward rewritten to: {}",
                                pretty_print(&new_clause, self.state.term_bank)
                            );

                            self.new_clauses.insert(id, new_clause);
                        }
                    }
                }
            }
        }
        self.new_clauses.iter().for_each(|(old_id, _)| {
            let old_clause = self.state.active.get_by_id(*old_id).unwrap().clone();
            self.state.erase_active(&old_clause);
        });
    }
}

/// Simplify `clause` with respect to all active clauses in `state`, returnin the modified version.
pub(crate) fn forward_simplify(clause: Clause, state: &SuperpositionState) -> Clause {
    let mut clause = clause;

    // We could do a round of DR DD here but we already know that clauses from passive are in DR/DD
    // normal form due to cheap_simplify so we can skip it.
    let res = ForwardRewriter::forward_rewrite(
        clause,
        &state.rewriting_index,
        &state.active,
        state.term_bank,
    );
    clause = res.clause;

    // Maybe we got more useless clauses to remove from rewriting
    if res.modified {
        let res = rule_dr_dd(clause, state.term_bank);
        clause = res.clause;
    }

    // Finally we give the clause a little sort according to `(weight, is_neg)` in order to
    // increase the likelihood of finding maximal clauses earlier:
    let mut vec = clause.to_vec();
    vec.sort_by(|lhs, rhs| {
        lhs.weight()
            .cmp(&rhs.weight())
            .reverse()
            .then(lhs.is_ne().cmp(&rhs.is_ne()))
    });

    clause = Clause::new(vec);

    clause
}

/// Simplify the active clause set from `state` with respect to `clause`, this includes deleting
/// them from active if they are found to be simplifiable. Return the simplified versions of
/// clauses if they were found.
pub(crate) fn backward_simplify(clause: &Clause, state: &mut SuperpositionState) -> Vec<Clause> {
    BackwardRewriter::backward_rewrite(clause, state)
}

pub(crate) fn cheap_simplify(clause: Clause, state: &SuperpositionState) -> Clause {
    // We implement no "non cheap" simplifications for now
    //forward_simplify(clause, state)
    rule_dr_dd(clause, state.term_bank).clause
}
