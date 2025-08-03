//! This module implements the core reasoning engine of Q, designed similarly to
//! ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf)
//! with:
//! - the DISCOUNT loop
//! - a subsumption index
//! - term indices for rewriting and paramodulation
//! - a couple but not all of the simplification rules
//!
//! The key entry point of this module is [search_proof].

use std::{
    cmp::Ordering,
    fs::File,
    io::Write,
    time::{Duration, Instant},
};

use log::info;

use crate::{
    clause::{Clause, ClauseId, ClauseSet, Literal, LiteralId, Orientation, Polarity},
    clause_queue::ClauseQueue,
    discr_tree::DiscriminationTree,
    feature_vector::FeatureVectorIndex,
    kbo::KboOrd,
    position::{
        ClausePosition, ClauseSetLiteralPosition, ClauseSetTermPosition, LiteralPosition,
        LiteralSide, Position, TermPosition, UnitClauseSetPosition,
    },
    pretty_print::pretty_print,
    proofs::{GraphvizMode, ProofLog, ProofRule},
    selection::SelectionStrategy,
    simplifier::{backward_simplify, cheap_simplify, forward_simplify},
    subst::{Substitutable, Substitution},
    term_bank::{Term, TermBank},
    trivial::is_trivial,
};

use memory_stats::memory_stats;

/// The resource limits that should cause the saturation loop to abort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ResourceLimitConfig {
    /// The maximum duration for which the saturation should run.
    pub duration: Option<Duration>,
    /// The maximum memory the saturation process is allowed to consume.
    pub memory_limit: Option<usize>,
}

impl Default for ResourceLimitConfig {
    fn default() -> Self {
        ResourceLimitConfig {
            duration: None,
            memory_limit: None,
        }
    }
}

struct ResourceLimits {
    time_limit: Option<Instant>,
    memory_limit: Option<usize>,
}

impl ResourceLimits {
    fn of_config(config: &ResourceLimitConfig) -> Self {
        let time_limit = config.duration.map(|dur| Instant::now() + dur);
        let memory_limit = config.memory_limit;
        ResourceLimits {
            time_limit,
            memory_limit,
        }
    }
}

pub(crate) struct SuperpositionState<'a> {
    /// The passive/unprocessed set.
    pub(crate) passive: ClauseQueue,
    /// The active/processed set.
    pub(crate) active: ClauseSet,
    /// The term bank for allocating our hashconsed terms.
    pub(crate) term_bank: &'a mut TermBank,
    /// Term index containing all subterms from `active`, used when superposing using the given
    /// clause as the one providing the equality.
    pub(crate) subterm_index: DiscriminationTree<ClauseSetTermPosition>,
    /// Term index containing all equational literals from `active`, used when superposing while
    /// rewriting inside of the given clause.
    pub(crate) eq_literal_index: DiscriminationTree<ClauseSetLiteralPosition>,
    /// Subsumption index containing all clauses from `active`.
    pub(crate) subsumption_index: FeatureVectorIndex,
    /// Term index containing all equational unit clauses from `active`.
    pub(crate) rewriting_index: DiscriminationTree<UnitClauseSetPosition>,
    /// The log of all proof steps done so far
    pub(crate) proof_log: ProofLog,
    /// The resource limit configuration for aborting if they are exceeded.
    resource_limits: ResourceLimits,
    /// The Literal Selection Algorithm
    selection_strategy: SelectionStrategy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnknownReason {
    Timeout,
    OutOfMemory,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SuperpositionResult {
    ProofFound,
    StatementFalse,
    Unknown(UnknownReason),
}

fn ordering_check(
    clause: &Clause,
    check_lit_id: LiteralId,
    subst: &Substitution,
    f: impl Fn(Option<Ordering>) -> bool,
    term_bank: &TermBank,
) -> Option<Vec<Literal>> {
    let mut new_literals = Vec::with_capacity(clause.len());
    let check_lit = clause
        .get_literal(check_lit_id)
        .clone()
        .subst_with(subst, term_bank);
    let ok = clause
        .iter()
        .filter(|(other_lit_id, _)| check_lit_id != *other_lit_id)
        .all(|(_, other_lit)| {
            let other_lit = other_lit.clone().subst_with(subst, term_bank);
            if f(check_lit.kbo(&other_lit, term_bank)) {
                new_literals.push(other_lit);
                true
            } else {
                // abort: we are not maximal
                false
            }
        });
    if ok { Some(new_literals) } else { None }
}

/// Takes a `clause` and an index `check_lit_id` to some literal `check_lit` in `clause` together
/// with a substitution `subst`. Then checks whether `subst(check_lit)` is maximal in `subst(clause)`.
/// Returns `None` if maximality check fails, otherwise `Some(subst(clause) \ subst(check_lit))`
fn maximality_check(
    clause: &Clause,
    check_lit_id: LiteralId,
    subst: &Substitution,
    term_bank: &TermBank,
) -> Option<Vec<Literal>> {
    ordering_check(
        clause,
        check_lit_id,
        subst,
        |ord| ord != Some(Ordering::Less),
        term_bank,
    )
}

/// Eligiblity for Resolution Check given a non-empty selection:
/// Returns the substituted and filtered literals,
/// if the given literal is maximal in the intersection of the selection
/// with either the positive or negative literalset of the clause with the mgu applied
fn eligible_resolution_with_selection(
    clause: &Clause,
    check_lit_id: LiteralId,
    subst: &Substitution,
    selection_strategy: SelectionStrategy,
    term_bank: &TermBank,
) -> Option<Vec<Literal>> {
    let mut new_literals = Vec::with_capacity(clause.len());
    let check_lit = clause
        .get_literal(check_lit_id)
        .clone()
        .subst_with(subst, term_bank);
    let mut is_pos_max = true;
    let mut is_neg_max = true;
    // Iterate through the selection and keep track if there is a positive
    // or negative literal which is greater than check_lit
    for (_, other_lit) in clause
        .eligible_iter(selection_strategy, term_bank)
        .filter(|(other_lit_id, _)| check_lit_id != *other_lit_id)
    {
        let other_lit = other_lit.clone().subst_with(subst, term_bank);
        // Only compute the KBO if the polarity can make the maximality check fail
        if (is_pos_max && other_lit.get_pol() == Polarity::Eq)
            || (is_neg_max && other_lit.get_pol() == Polarity::Ne)
        {
            if let Some(Ordering::Greater) = check_lit.kbo(&other_lit, term_bank) {
                // Abort: we are not maximal for the intersection of that polarity
                match other_lit.get_pol() {
                    Polarity::Eq => is_pos_max = false,
                    Polarity::Ne => is_neg_max = false,
                }
                if !is_pos_max && !is_neg_max {
                    return None;
                }
            }
        }
        new_literals.push(other_lit);
    }
    // On success add the remaining literals, which were not part of the selection
    for (_, other_lit) in clause.non_eligible_iter(selection_strategy, term_bank) {
        let other_lit = other_lit.clone().subst_with(subst, term_bank);
        new_literals.push(other_lit);
    }
    Some(new_literals)
}

impl SuperpositionState<'_> {
    fn insert_subterms(
        &mut self,
        root_term: &Term,
        clause_id: ClauseId,
        literal_id: LiteralId,
        literal_side: LiteralSide,
    ) {
        for (term, term_pos) in root_term.subterm_iter() {
            let pos = ClauseSetTermPosition::new(
                ClausePosition::new(LiteralPosition::new(term_pos, literal_side), literal_id),
                clause_id,
            );
            self.subterm_index.insert(&term, pos);
        }
    }

    /// Insert `clause` into the `active` set, updating all of the term indices to account for it.
    fn insert_active(&mut self, clause: Clause) {
        let clause_id = clause.get_id();
        info!(
            "Inserting active: {}",
            pretty_print(&clause, self.term_bank)
        );

        // Insert all sub terms with their position into the term index for superposition
        for (literal_id, literal) in clause.iter() {
            let lhs = literal.get_lhs();
            let rhs = literal.get_rhs();

            // If the literal is already orientable at this point there is no need to insert
            // both symmetries.
            match literal.get_orientation(self.term_bank) {
                Some(Orientation::Impossible) => {}
                Some(Orientation::Flipped) => {
                    self.insert_subterms(rhs, clause_id, literal_id, LiteralSide::Right);
                }
                Some(Orientation::Natural) => {
                    self.insert_subterms(lhs, clause_id, literal_id, LiteralSide::Left);
                }
                // not orientable -> both orderings could be valid
                None => {
                    self.insert_subterms(lhs, clause_id, literal_id, LiteralSide::Left);
                    self.insert_subterms(rhs, clause_id, literal_id, LiteralSide::Right);
                }
            }
        }

        // Insert all equational literals into the term index for superposition
        for (lit_id, lit) in clause.iter() {
            if lit.is_ne() {
                continue;
            }
            let lhs = lit.get_lhs();
            let rhs = lit.get_rhs();
            // If the literal is already orientable at this point there is no need to insert
            // both symmetries.
            match lit.get_orientation(self.term_bank) {
                Some(Orientation::Impossible) => {}
                Some(Orientation::Flipped) => {
                    self.eq_literal_index.insert(
                        rhs,
                        ClauseSetLiteralPosition::new(clause.get_id(), lit_id, LiteralSide::Right),
                    );
                }
                Some(Orientation::Natural) => {
                    self.eq_literal_index.insert(
                        lhs,
                        ClauseSetLiteralPosition::new(clause.get_id(), lit_id, LiteralSide::Left),
                    );
                }
                // not orientable -> both orderings could be valid
                None => {
                    self.eq_literal_index.insert(
                        lhs,
                        ClauseSetLiteralPosition::new(clause.get_id(), lit_id, LiteralSide::Left),
                    );
                    self.eq_literal_index.insert(
                        rhs,
                        ClauseSetLiteralPosition::new(clause.get_id(), lit_id, LiteralSide::Right),
                    );
                }
            }
        }

        // TODO: merge this with the above
        if let Some(lit) = clause.is_rewrite_rule() {
            // If the literal is already orientable at this point there is no need to insert
            // both symmetries.
            let lhs = lit.get_lhs();
            let rhs = lit.get_rhs();
            match lit.get_orientation(self.term_bank) {
                Some(Orientation::Impossible) => {}
                Some(Orientation::Flipped) => {
                    self.rewriting_index.insert(
                        rhs,
                        UnitClauseSetPosition::new(clause.get_id(), LiteralSide::Right),
                    );
                }
                Some(Orientation::Natural) => {
                    self.rewriting_index.insert(
                        lhs,
                        UnitClauseSetPosition::new(clause.get_id(), LiteralSide::Left),
                    );
                }
                // not orientable -> both orderings could be valid
                None => {
                    self.rewriting_index.insert(
                        lhs,
                        UnitClauseSetPosition::new(clause.get_id(), LiteralSide::Left),
                    );
                    self.rewriting_index.insert(
                        rhs,
                        UnitClauseSetPosition::new(clause.get_id(), LiteralSide::Right),
                    );
                }
            }
        }

        // Update the feature vector index for subsumption
        self.subsumption_index.insert(&clause, self.term_bank);

        self.active.insert(clause);
    }

    /// Remove `clause` from the `active` set, updating all of the term indices to account for it.
    pub(crate) fn erase_active(&mut self, clause: &Clause) {
        let clause_id = clause.get_id();
        info!("Erasing active: {}", pretty_print(clause, self.term_bank));

        // Erase all sub terms with their position in the term index for superposition
        for (literal_id, literal) in clause.iter() {
            for literal_side in [LiteralSide::Left, LiteralSide::Right] {
                let root_term = literal_side.get_side(literal);
                for (term, term_pos) in root_term.subterm_iter() {
                    let pos = ClauseSetTermPosition::new(
                        ClausePosition::new(
                            LiteralPosition::new(term_pos, literal_side),
                            literal_id,
                        ),
                        clause_id,
                    );
                    self.subterm_index.remove(&term, pos);
                }
            }
        }

        // Erase all equational literals in the term index for superposition
        for (literal_id, literal) in clause.iter() {
            if literal.is_ne() {
                continue;
            }
            for literal_side in [LiteralSide::Left, LiteralSide::Right] {
                let lhs = literal_side.get_side(literal);
                let pos = ClauseSetLiteralPosition::new(clause.get_id(), literal_id, literal_side);
                self.eq_literal_index.remove(lhs, pos);
            }
        }

        if let Some(lit) = clause.is_rewrite_rule() {
            self.rewriting_index.remove(
                lit.get_lhs(),
                UnitClauseSetPosition::new(clause.get_id(), LiteralSide::Left),
            );
            self.rewriting_index.remove(
                lit.get_rhs(),
                UnitClauseSetPosition::new(clause.get_id(), LiteralSide::Right),
            );
        }

        self.subsumption_index.remove(clause, self.term_bank);
        self.active.remove(clause);
    }

    /// Insert `clause` into the passive set, this is a very cheap operation.
    fn insert_passive(&mut self, clause: Clause) {
        info!(
            "Inserting passive: {}",
            pretty_print(&clause, self.term_bank)
        );
        self.passive.push(clause);
    }

    fn equality_resolution(&mut self, clause: &Clause, acc: &mut Vec<Clause>) {
        info!(
            "ERes working clause: {}",
            pretty_print(clause, self.term_bank)
        );
        for (literal_id, literal) in clause.eligible_iter(self.selection_strategy, self.term_bank) {
            // Condition: the literal must be an inequality
            if literal.is_eq() {
                continue;
            }

            // Condition 1: the lhs and rhs of the literal must unify
            if let Some(subst) = literal.get_lhs().unify(literal.get_rhs(), self.term_bank) {
                if clause.has_selection(self.selection_strategy, self.term_bank) {
                    // Condition 2: non-empty selection: has to be maximal in the
                    // mgu applied intersection of the selection with either C- or C+
                    if let Some(new_literals) = eligible_resolution_with_selection(
                        clause,
                        literal_id,
                        &subst,
                        self.selection_strategy,
                        self.term_bank,
                    ) {
                        let new_clause = Clause::new(new_literals);
                        info!(
                            "ERes derived clause: {}",
                            pretty_print(&new_clause, self.term_bank)
                        );
                        self.proof_log.log_clause(
                            &new_clause,
                            ProofRule::EqualityResolution,
                            &[clause.get_id()],
                            self.term_bank,
                        );
                        acc.push(new_clause);
                    }
                } else {
                    // Condition 2: The literal must be maximal in the clause with the mgu applied
                    if let Some(new_literals) =
                        maximality_check(clause, literal_id, &subst, self.term_bank)
                    {
                        let new_clause = Clause::new(new_literals);
                        info!(
                            "ERes derived clause: {}",
                            pretty_print(&new_clause, self.term_bank)
                        );
                        self.proof_log.log_clause(
                            &new_clause,
                            ProofRule::EqualityResolution,
                            &[clause.get_id()],
                            self.term_bank,
                        );
                        acc.push(new_clause);
                    }
                }
            }
        }
    }

    fn equality_factoring(&mut self, clause: &Clause, acc: &mut Vec<Clause>) {
        if clause.has_selection(self.selection_strategy, self.term_bank) {
            info!(
                "EFact working clause skipped due to selection: {}",
                pretty_print(clause, self.term_bank)
            );
            return;
        }
        info!(
            "EFact working clause: {}",
            pretty_print(clause, self.term_bank)
        );
        for (literal1_id, lit1) in clause.iter() {
            // Condition: Literal 1 must be an equality
            if lit1.is_ne() {
                continue;
            }
            for (literal2_id, lit2) in clause.iter() {
                // Condition: Literal 2 must be an equality
                if lit2.is_ne() || literal2_id == literal1_id {
                    continue;
                }
                for (l1_lhs, l1_rhs) in lit1.symm_term_iter() {
                    for (l2_lhs, l2_rhs) in lit2.symm_term_iter() {
                        // Condition 1: the lhs of both literals must unify
                        if let Some(subst) = l1_lhs.unify(&l2_lhs, self.term_bank) {
                            let l1_rhs_subst = l1_rhs.clone().subst_with(&subst, self.term_bank);
                            let ord = l1_lhs
                                .clone()
                                .subst_with(&subst, self.term_bank)
                                .kbo(&l1_rhs_subst, self.term_bank);
                            // Condition 2: after applying the mgu we must have ~(lhs < rhs)
                            if ord == Some(Ordering::Less) {
                                continue;
                            }

                            // Condition 3: The literal must be maximal in the clause with the mgu
                            // appplied
                            if let Some(mut new_literals) =
                                maximality_check(clause, literal1_id, &subst, self.term_bank)
                            {
                                let final_lit = Literal::mk_ne(
                                    l1_rhs_subst,
                                    l2_rhs.clone().subst_with(&subst, self.term_bank),
                                );
                                new_literals.push(final_lit);
                                let new_clause = Clause::new(new_literals);
                                info!(
                                    "EFact derived clause: {}",
                                    pretty_print(&new_clause, self.term_bank)
                                );
                                self.proof_log.log_clause(
                                    &new_clause,
                                    ProofRule::EqualityFactoring,
                                    &[clause.get_id()],
                                    self.term_bank,
                                );
                                acc.push(new_clause);
                            }
                        }
                    }
                }
            }
        }
    }

    /// The core part of superposition, assuming that:
    /// - lit1_id points into a literal in clause1 that is an equality
    /// - lit2_id points into a literal in clause2
    /// - lit2_pol is the polarity of literal 2
    /// - lit(1|2)_(lhs|rhs) are the respective sides of the literals (recall that literals are
    ///   considered up to symmetry)
    /// - subterm_pos is a term position within lit2_lhs that is not a variable (Condition 2)
    /// - subst is the mgu of the term at subterm_pos and lit1_lhs (Condition 1)
    ///
    /// This function will check:
    /// - ~(subst(lit1_lhs) < subst(lit1_rhs))
    /// - ~(subst(lit2_lhs) < subst(lit2_rhs))
    /// - subst(lit1_lhs = lit1_rhs) is eligible for paramodulation
    /// - subst(lit2_lhs =/!= lit2_rhs) is eligible for resolution
    ///
    /// and add a new clause to acc on success.
    fn superposition_core(
        &self,
        clause1: &Clause,
        clause2: &Clause,
        lit1_id: LiteralId,
        lit2_id: LiteralId,
        lit2_pol: Polarity,
        lit1_lhs: &Term,
        lit1_rhs: &Term,
        lit2_lhs: &Term,
        lit2_rhs: &Term,
        subterm_pos: &TermPosition,
        subst: &Substitution,
        acc: &mut Vec<Clause>,
    ) {
        let l1_ord = lit1_lhs.clone().subst_with(subst, self.term_bank).kbo(
            &lit1_rhs.clone().subst_with(subst, self.term_bank),
            self.term_bank,
        );
        if l1_ord == Some(Ordering::Less) {
            return;
        }

        let l2_rhs_subst = lit2_rhs.clone().subst_with(subst, self.term_bank);
        let l2_ord = lit2_lhs
            .clone()
            .subst_with(subst, self.term_bank)
            .kbo(&l2_rhs_subst, self.term_bank);
        if l2_ord == Some(Ordering::Less) {
            return;
        }

        if let Some(mut new_literals1) = maximality_check(clause1, lit1_id, subst, self.term_bank) {
            if clause2.has_selection(self.selection_strategy, self.term_bank) {
                // Non-empty selection: has to be maximal in the mgu applied intersection of the
                // selection with either C- or C+
                if let Some(mut new_literals2) = eligible_resolution_with_selection(
                    clause2,
                    lit2_id,
                    subst,
                    self.selection_strategy,
                    self.term_bank,
                ) {
                    new_literals1.append(&mut new_literals2);
                    let new_rhs = l2_rhs_subst;
                    let new_lhs = subterm_pos
                        .replace_term_at(lit2_lhs, lit1_rhs.clone(), self.term_bank)
                        .subst_with(subst, self.term_bank);
                    let new_lit = Literal::new(new_lhs, new_rhs, lit2_pol);
                    new_literals1.push(new_lit);
                    let new_clause = Clause::new(new_literals1);
                    self.proof_log.log_clause(
                        &new_clause,
                        ProofRule::Superposition,
                        &[clause1.get_id(), clause2.get_id()],
                        self.term_bank,
                    );
                    acc.push(new_clause);
                }
            } else {
                // Empty selection: literal has to be maximal in the full clause
                if let Some(mut new_literals2) =
                    maximality_check(clause2, lit2_id, subst, self.term_bank)
                {
                    new_literals1.append(&mut new_literals2);
                    let new_rhs = l2_rhs_subst;
                    let new_lhs = subterm_pos
                        .replace_term_at(lit2_lhs, lit1_rhs.clone(), self.term_bank)
                        .subst_with(subst, self.term_bank);
                    let new_lit = Literal::new(new_lhs, new_rhs, lit2_pol);
                    new_literals1.push(new_lit);
                    let new_clause = Clause::new(new_literals1);
                    info!(
                        "SP derived clause: {} by superposing {} with {}",
                        pretty_print(&new_clause, self.term_bank),
                        pretty_print(clause1, self.term_bank),
                        pretty_print(clause2, self.term_bank)
                    );
                    self.proof_log.log_clause(
                        &new_clause,
                        ProofRule::Superposition,
                        &[clause1.get_id(), clause2.get_id()],
                        self.term_bank,
                    );
                    acc.push(new_clause);
                }
            }
        }
    }

    fn superposition(&mut self, given_clause: &Clause, acc: &mut Vec<Clause>) {
        info!(
            "SP working clause: {}",
            pretty_print(given_clause, self.term_bank)
        );

        let clause1 = given_clause;
        // Part 1: given_clause is the one being used for rewriting.
        if !clause1.has_selection(self.selection_strategy, self.term_bank) {
            for (lit1_id, lit1) in clause1.iter() {
                // Condition: The one being used for rewriting must be an equality
                if lit1.is_ne() {
                    continue;
                }
                // Try to orient the equation using stability under substitution
                for (lit1_lhs, lit1_rhs) in lit1.oriented_symm_term_iter(self.term_bank) {
                    // Iterate over all possible unifying subpositions in the active set
                    for candidate_pos in self.subterm_index.get_unification_candidates(&lit1_lhs) {
                        let lit2_lhs_p = candidate_pos.term_at(&self.active);
                        // The term at the subposition must not be a variable
                        if lit2_lhs_p.is_variable() {
                            continue;
                        }

                        // The lhs of the rewriting literal and the subposition must unify
                        if let Some(subst) = lit1_lhs.unify(lit2_lhs_p, self.term_bank) {
                            let clause_pos = &candidate_pos.clause_pos;
                            let literal_pos = &clause_pos.literal_pos;
                            let subterm_pos = &literal_pos.term_pos;
                            let clause2 = self.active.get_by_id(candidate_pos.clause_id).unwrap();
                            let lit2_id = clause_pos.literal_id;
                            let lit2 = clause2.get_literal(lit2_id);
                            let lit2_lhs = literal_pos.literal_side.get_side(lit2);
                            let lit2_rhs = literal_pos.literal_side.swap().get_side(lit2);
                            let lit2_pol = lit2.get_pol();

                            self.superposition_core(
                                clause1,
                                clause2,
                                lit1_id,
                                lit2_id,
                                lit2_pol,
                                &lit1_lhs,
                                &lit1_rhs,
                                lit2_lhs,
                                lit2_rhs,
                                subterm_pos,
                                &subst,
                                acc,
                            );
                        }
                    }
                }
            }
        }

        // Part 2: the given clause is the one being rewritten
        let clause2 = given_clause;
        for (lit2_id, lit2) in clause2.iter() {
            let lit2_pol = lit2.get_pol();
            // Try to orient the equation using stability under substitution
            for (lit2_lhs, lit2_rhs) in lit2.oriented_symm_term_iter(self.term_bank) {
                // Iterate over all subterms to look for unifying partners in the active set
                for (subterm, subterm_pos) in lit2_lhs.subterm_iter() {
                    // The term at the subposition must not be a variable
                    if subterm.is_variable() {
                        continue;
                    }

                    // Iterate over all equational literals that potentially unify with our subterm
                    for candidate_pos in self.eq_literal_index.get_unification_candidates(&subterm)
                    {
                        let clause_id = candidate_pos.clause_id;
                        let clause1 = self.active.get_by_id(clause_id).unwrap();
                        if clause1.has_selection(self.selection_strategy, self.term_bank) {
                            continue;
                        }
                        let lit1_id = candidate_pos.literal_id;
                        let lit1 = clause1.get_literal(lit1_id);
                        debug_assert!(lit1.is_eq());
                        let literal_side = &candidate_pos.literal_side;
                        let lit1_lhs = literal_side.get_side(lit1);
                        let lit1_rhs = literal_side.swap().get_side(lit1);

                        // The lhs of the rewriting literal and the subposition must unify
                        if let Some(subst) = subterm.unify(lit1_lhs, self.term_bank) {
                            self.superposition_core(
                                clause1,
                                clause2,
                                lit1_id,
                                lit2_id,
                                lit2_pol,
                                lit1_lhs,
                                lit1_rhs,
                                &lit2_lhs,
                                &lit2_rhs,
                                &subterm_pos,
                                &subst,
                                acc,
                            );
                        }
                    }
                }
            }
        }
    }

    /// Run all generating inferences, this is the core of the reasoning engine.
    fn generate(&mut self, clause: Clause) -> Vec<Clause> {
        let mut acc = Vec::new();
        self.equality_resolution(&clause, &mut acc);
        self.equality_factoring(&clause, &mut acc);
        self.superposition(&clause, &mut acc);
        acc
    }

    /// Check if one of the resource exhaustion conditions is met. May cause garbage collection on
    /// the term bank if the memory limit is almost exhausted.
    fn resources_exhausted(&self) -> Option<UnknownReason> {
        if let Some(time_limit) = self.resource_limits.time_limit {
            let now = Instant::now();
            if now > time_limit {
                return Some(UnknownReason::Timeout);
            }
        }

        if let Some(memory_limit) = self.resource_limits.memory_limit {
            if let Some(stats) = memory_stats() {
                // We only start to try and GC one we are about to explode to go fast in the normal
                // case
                if memory_limit as f64 * 0.98 < stats.physical_mem as f64 {
                    self.term_bank.gc();
                    if let Some(stats) = memory_stats() {
                        if memory_limit < stats.physical_mem {
                            return Some(UnknownReason::OutOfMemory);
                        }
                    }
                }
            }
        }

        None
    }

    /// Check whether `g` is redundant with respect to the active set via subsumption.
    fn redundant(&self, g: &Clause) -> bool {
        for active_clause_id in self.subsumption_index.forward_candidates(g, self.term_bank) {
            let active_clause = self.active.get_by_id(active_clause_id).unwrap();
            if active_clause.subsumes(g, self.term_bank) {
                info!(
                    "Forward Subsumption: {} subsumes {}",
                    pretty_print(active_clause, self.term_bank),
                    pretty_print(g, self.term_bank)
                );
                return true;
            }
        }
        false
    }

    /// Remove all clauses in the active subsumed by `g` from the active set
    fn backward_subsumption(&mut self, g: &Clause) {
        let mut redundant_active = Vec::new();
        for active_clause_id in self
            .subsumption_index
            .backward_candidates(g, self.term_bank)
        {
            let active_clause = self.active.get_by_id(active_clause_id).unwrap();
            if g.subsumes(active_clause, self.term_bank) {
                info!(
                    "Backward Subsumption: {} subsumes {}",
                    pretty_print(g, self.term_bank),
                    pretty_print(active_clause, self.term_bank),
                );
                redundant_active.push(active_clause.clone());
            }
        }
        redundant_active.iter().for_each(|c| self.erase_active(c));
    }

    fn run(&mut self) -> SuperpositionResult {
        while let Some(g_queue) = self.passive.pop() {
            let mut g = g_queue.fresh_variable_clone(self.term_bank);
            info!("Next given clause: {}", pretty_print(&g, self.term_bank));
            self.proof_log
                .log_clause(&g, ProofRule::Renaming, &[g_queue.get_id()], self.term_bank);

            g = forward_simplify(g, self);

            if is_trivial(&g, self.term_bank) {
                continue;
            }

            if g.is_empty() {
                log::warn!("Active Set size: {}", self.active.len());
                return SuperpositionResult::ProofFound;
            }

            if self.redundant(&g) {
                continue;
            }

            self.backward_subsumption(&g);

            let backward_simplified = backward_simplify(&g, self);

            // For situations where we superpose a clause with itself it is crucial, that we submit
            // a fresh variable copy in order to make sure that the two clauses are considered
            // distinct.
            let active_g = g.fresh_variable_clone(self.term_bank);
            self.insert_active(active_g);

            let new_clauses = self.generate(g);
            for mut clause in backward_simplified
                .into_iter()
                .chain(new_clauses.into_iter())
            {
                clause = cheap_simplify(clause, self);
                if is_trivial(&clause, self.term_bank) {
                    continue;
                }
                self.insert_passive(clause);
            }

            if let Some(reason) = self.resources_exhausted() {
                log::warn!(
                    "Active Set size: {} | Passive Set size {}",
                    self.active.len(),
                    self.passive.len()
                );
                return SuperpositionResult::Unknown(reason);
            }
        }

        log::warn!("Active Set size: {}", self.active.len(),);

        SuperpositionResult::StatementFalse
    }
}

pub fn search_proof(
    initial_clauses: Vec<Clause>,
    term_bank: &mut TermBank,
    resource_config: &ResourceLimitConfig,
    selection_strategy: SelectionStrategy,
    gcfg: Option<(GraphvizMode, String)>,
) -> SuperpositionResult {
    let mut passive = ClauseQueue::new();
    let proof_log = ProofLog::new(gcfg.is_some());
    initial_clauses.into_iter().for_each(|clause| {
        proof_log.log_clause(&clause, ProofRule::Original, &[], term_bank);
        passive.push(clause);
    });
    let active = ClauseSet::new();
    let subterm_index = DiscriminationTree::new();
    let resource_limits = ResourceLimits::of_config(resource_config);
    let subsumption_index = FeatureVectorIndex::new();
    let rewriting_index = DiscriminationTree::new();
    let eq_literal_index = DiscriminationTree::new();

    let mut state = SuperpositionState {
        passive,
        active,
        term_bank,
        subterm_index,
        resource_limits,
        subsumption_index,
        rewriting_index,
        eq_literal_index,
        selection_strategy,
        proof_log,
    };
    let ret = state.run();
    if let Some((gmode, gfile)) = gcfg {
        let mut file = File::create(gfile).unwrap();
        file.write_all(&state.proof_log.to_graphviz(gmode).into_bytes())
            .unwrap();
    }
    ret
}

#[cfg(test)]
mod test {
    use crate::{
        clause::{Clause, Literal, Polarity},
        selection::SelectionStrategy,
        superposition::SuperpositionResult,
        term_bank::{FunctionInformation, Sort, TermBank, VariableInformation},
    };

    use super::search_proof;

    #[test]
    fn basic_equality_resolution() {
        let mut term_bank = TermBank::new();
        let top = term_bank.add_function(FunctionInformation {
            name: "top".to_string(),
            arity: 0,
            sort: Sort::Individual,
        });
        let bot = term_bank.add_function(FunctionInformation {
            name: "bot".to_string(),
            arity: 0,
            sort: Sort::Individual,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
            sort: Sort::Individual,
        });
        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });

        let top = term_bank.mk_const(top);
        let bot = term_bank.mk_const(bot);

        let fx = term_bank.mk_app(f, vec![x.clone()]);
        let ft = term_bank.mk_app(f, vec![top.clone()]);

        let lit1 = Literal::new(top.clone(), top.clone(), Polarity::Ne);
        let lit2 = Literal::new(bot.clone(), bot.clone(), Polarity::Ne);
        let lit3 = Literal::new(fx, ft, Polarity::Ne);
        let clause = Clause::new(vec![lit1, lit2, lit3]);
        assert_eq!(
            search_proof(
                vec![clause],
                &mut term_bank,
                &Default::default(),
                SelectionStrategy::ZipperSel,
                None,
            ),
            SuperpositionResult::ProofFound
        );
    }

    #[test]
    fn basic_transitivity() {
        let mut term_bank = TermBank::new();
        let a = term_bank.add_function(FunctionInformation {
            name: "a".to_string(),
            arity: 0,
            sort: Sort::Individual,
        });
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
            sort: Sort::Individual,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
            sort: Sort::Individual,
        });

        let a = term_bank.mk_const(a);
        let b = term_bank.mk_const(b);
        let c = term_bank.mk_const(c);

        let clause1 = Clause::new(vec![Literal::new(a.clone(), b.clone(), Polarity::Eq)]);
        let clause2 = Clause::new(vec![Literal::new(b.clone(), c.clone(), Polarity::Eq)]);
        let clause3 = Clause::new(vec![Literal::new(a.clone(), c.clone(), Polarity::Ne)]);

        assert_eq!(
            search_proof(
                vec![clause1, clause2, clause3],
                &mut term_bank,
                &Default::default(),
                SelectionStrategy::ZipperSel,
                None,
            ),
            SuperpositionResult::ProofFound
        );
    }
}
