use std::{
    cmp::Ordering,
    time::{Duration, Instant},
};

use log::info;

use crate::{
    clause::{Clause, ClauseSet, Literal, LiteralId, Polarity},
    clause_queue::ClauseQueue,
    discr_tree::DiscriminationTree,
    feature_vector::FeatureVectorIndex,
    kbo::KboOrd,
    position::{
        ClausePosition, ClauseSetPosition, LiteralPosition, LiteralSide, Position, TermPosition,
    },
    pretty_print::pretty_print,
    simplifier::{cheap_simplify, simplify},
    subst::{Substitutable, Substitution},
    term_bank::{Term, TermBank},
    trivial::is_trivial,
};

use memory_stats::memory_stats;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ResourceLimitConfig {
    pub duration: Option<Duration>,
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

struct SuperpositionState<'a> {
    passive: ClauseQueue,
    active: ClauseSet,
    term_bank: &'a mut TermBank,
    subterm_index: DiscriminationTree<ClauseSetPosition>,
    subsumption_index: FeatureVectorIndex,
    resource_limits: ResourceLimits,
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
        .subst_with(&subst, term_bank);
    let ok = clause
        .iter()
        .filter(|(other_lit_id, _)| check_lit_id != *other_lit_id)
        .all(|(_, other_lit)| {
            let other_lit = other_lit.clone().subst_with(&subst, term_bank);
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

/*
Takes a `clause` and an index `check_lit_id` to some literal `check_lit` in `clause` together
with a substitution `subst`. Then checks whether `subst(check_lit)` is maximal in `subst(clause)`.

Returns `None` if maximality check fails, otherwise `Some(subst(clause) \ subst(check_lit))`
*/
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

/*
Takes a `clause` and an index `check_lit_id` to some literal `check_lit` in `clause` together
with a substitution `subst`. Then checks whether `subst(check_lit)` is strictly maximal in
`subst(clause)`.

Returns `None` if maximality check fails, otherwise `Some(subst(clause) \ subst(check_lit))`
*/
fn strict_maximality_check(
    clause: &Clause,
    check_lit_id: LiteralId,
    subst: &Substitution,
    term_bank: &TermBank,
) -> Option<Vec<Literal>> {
    ordering_check(
        clause,
        check_lit_id,
        subst,
        |ord| ord != Some(Ordering::Less) && ord != Some(Ordering::Equal),
        term_bank,
    )
}

fn equality_resolution(clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
    info!("ERes working clause: {}", pretty_print(clause, term_bank));
    for (literal_id, literal) in clause.iter() {
        // Condition: the literal must be an inequality
        if literal.is_eq() {
            continue;
        }

        // Condition 1: the lhs and rhs of the literal must unify
        if let Some(subst) = literal.get_lhs().unify(literal.get_rhs(), term_bank) {
            // Condition 2: The literal must be maximal in the clause with the mgu applied
            if let Some(new_literals) = maximality_check(clause, literal_id, &subst, term_bank) {
                let new_clause = Clause::new(new_literals);
                info!(
                    "ERes derived clause: {}",
                    pretty_print(&new_clause, term_bank)
                );
                acc.push(new_clause);
            }
        }
    }
}

fn equality_factoring(clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
    info!("EFact working clause: {}", pretty_print(clause, term_bank));
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
                    if let Some(subst) = l1_lhs.unify(&l2_lhs, term_bank) {
                        let ord = l1_rhs
                            .clone()
                            .subst_with(&subst, term_bank)
                            .kbo(&l1_lhs.clone().subst_with(&subst, term_bank), term_bank);
                        // Condition 2: after applying the mgu the rhs must not be <= than the lhs
                        if ord == Some(Ordering::Equal) || ord == Some(Ordering::Less) {
                            continue;
                        }

                        // Condition 3: The literal must be maximal in the clause with the mgu
                        // appplied
                        if let Some(mut new_literals) =
                            maximality_check(clause, literal1_id, &subst, term_bank)
                        {
                            let final_lit = Literal::mk_ne(
                                l1_rhs.clone().subst_with(&subst, term_bank),
                                l2_rhs.clone().subst_with(&subst, term_bank),
                            );
                            new_literals.push(final_lit);
                            let new_clause = Clause::new(new_literals);
                            info!(
                                "EFact derived clause: {}",
                                pretty_print(&new_clause, term_bank)
                            );
                            acc.push(new_clause);
                        }
                    }
                }
            }
        }
    }
}

impl<'a> SuperpositionState<'a> {
    fn insert_active(&mut self, clause: Clause) {
        let clause_id = clause.get_id();
        info!(
            "Inserting active: {}",
            pretty_print(&clause, self.term_bank)
        );

        // Insert all sub terms with their position into the term index for superposition

        // TODO: There is a potential optimization here where we keep a second index that contains
        // just the root terms of all literals. This is useful for superposing when the given
        // clause is the one being substituted in.
        for (literal_id, literal) in clause.iter() {
            for literal_side in [LiteralSide::Left, LiteralSide::Right] {
                let root_term = literal_side.get_side(literal);
                for (term, term_pos) in root_term.subterm_iter() {
                    if term.variable_id().is_none() {
                        let pos = ClauseSetPosition::new(
                            ClausePosition::new(
                                LiteralPosition::new(term_pos, literal_side),
                                literal_id,
                            ),
                            clause_id,
                        );
                        self.subterm_index.insert(&term, pos);
                    }
                }
            }
        }

        // Update the feature vector index for subsumption
        self.subsumption_index.insert(&clause);

        self.active.insert(clause);
    }

    fn insert_passive(&mut self, clause: Clause) {
        info!(
            "Inserting passive: {}",
            pretty_print(&clause, self.term_bank)
        );
        self.passive.push(clause);
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
    /// This function will check condition 3 through 6 for both positive and negative superposition
    /// and add a new clause to acc if applicable.
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
        term_bank: &TermBank,
    ) {
        let l1_ord = lit1_lhs
            .clone()
            .subst_with(&subst, term_bank)
            .kbo(&lit1_rhs.clone().subst_with(&subst, term_bank), term_bank);
        // Condition 3: The lhs of the rewriting literal must not be <= the rhs after
        // applying the substitution.
        if l1_ord == Some(Ordering::Equal) || l1_ord == Some(Ordering::Less) {
            return;
        }

        // Condition 5: The lhs of the literal being rewritten must not be <= the
        // rhs after applying the substitution.
        let l2_ord = lit2_lhs
            .clone()
            .subst_with(&subst, term_bank)
            .kbo(&lit2_rhs.clone().subst_with(&subst, term_bank), term_bank);
        if l2_ord == Some(Ordering::Equal) || l2_ord == Some(Ordering::Less) {
            return;
        }

        // Condition 4: The literal being used for rewriting must be maximal after
        // applying the mgu to its clause.
        if let Some(mut new_literals1) =
            strict_maximality_check(clause1, lit1_id, &subst, term_bank)
        {
            // Condition 6: The literal being rewritten must be maximal or strictly
            // maximal after applying the mgu to its clause.
            let checker = match lit2_pol {
                Polarity::Eq => strict_maximality_check,
                Polarity::Ne => maximality_check,
            };
            if let Some(mut new_literals2) = checker(clause2, lit2_id, &subst, term_bank) {
                new_literals1.append(&mut new_literals2);
                let new_rhs = lit2_rhs.clone().subst_with(&subst, term_bank);
                let new_lhs = subterm_pos
                    .replace_term_at(lit2_lhs, lit1_rhs.clone(), term_bank)
                    .subst_with(&subst, term_bank);
                let new_lit = Literal::new(new_lhs, new_rhs, lit2_pol);
                new_literals1.push(new_lit);
                let new_clause = Clause::new(new_literals1);
                info!(
                    "SP derived clause: {}",
                    pretty_print(&new_clause, term_bank)
                );
                acc.push(new_clause);
            }
        }
    }

    fn superposition(&self, given_clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
        info!(
            "SP working clause: {}",
            pretty_print(given_clause, term_bank)
        );

        let clause1 = given_clause;
        // Part 1: given_clause is the one being used for rewriting.
        for (lit1_id, lit1) in clause1.iter() {
            // Condition: The one being used for rewriting must be an equality
            if lit1.is_ne() {
                continue;
            }
            for (lit1_lhs, lit1_rhs) in lit1.symm_term_iter() {
                // Iterate over all possible unifying subpositions in the active set
                for candidate_pos in self.subterm_index.get_unification_candidates(&lit1_lhs) {
                    let lit2_lhs_p = candidate_pos.term_at(&self.active);
                    // Condition 2: The term at the subposition must not be a variable
                    if lit2_lhs_p.is_variable() {
                        continue;
                    }

                    // Condition 1: the lhs of the rewriting literal and the subposition must unify
                    if let Some(subst) = lit1_lhs.unify(lit2_lhs_p, &term_bank) {
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
                            term_bank,
                        );
                    }
                }
            }
        }

        // Part 2: the given clause is the one being rewritten
        let clause2 = given_clause;
        for (lit2_id, lit2) in clause2.iter() {
            let lit2_pol = lit2.get_pol();
            for (lit2_lhs, lit2_rhs) in lit2.symm_term_iter() {
                // Iterate over all subterms to look for unifying partners in the active set
                for (subterm, subterm_pos) in lit2_lhs.subterm_iter() {
                    if subterm.is_variable() {
                        continue;
                    }

                    // Iterate over all top level terms that potentially unify with our subterm
                    let candidates = self.subterm_index.get_unification_candidates(&subterm);
                    for candidate_pos in candidates
                        .into_iter()
                        .filter(|p| p.clause_pos.literal_pos.term_pos.is_root())
                    {
                        let clause_pos = &candidate_pos.clause_pos;
                        let clause1 = self.active.get_by_id(candidate_pos.clause_id).unwrap();
                        let lit1_id = clause_pos.literal_id;
                        let lit1 = clause1.get_literal(lit1_id);
                        // Condition: The one being used for rewriting must be an equality
                        if lit1.get_pol() != Polarity::Eq {
                            continue;
                        }
                        let literal_pos = &clause_pos.literal_pos;
                        let lit1_lhs = literal_pos.literal_side.get_side(lit1);
                        let lit1_rhs = literal_pos.literal_side.swap().get_side(lit1);

                        // Condition 1: The lhs of the rewriting literal and the subposition must
                        // unify
                        if let Some(subst) = subterm.unify(lit1_lhs, term_bank) {
                            self.superposition_core(
                                clause1,
                                clause2,
                                lit1_id,
                                lit2_id,
                                lit2_pol,
                                &lit1_lhs,
                                &lit1_rhs,
                                &lit2_lhs,
                                &lit2_rhs,
                                &subterm_pos,
                                &subst,
                                acc,
                                term_bank,
                            );
                        }
                    }
                }
            }
        }
    }

    fn generate(&self, clause: Clause) -> Vec<Clause> {
        let mut acc = Vec::new();
        equality_resolution(&clause, &mut acc, &self.term_bank);
        equality_factoring(&clause, &mut acc, &self.term_bank);
        self.superposition(&clause, &mut acc, &self.term_bank);
        acc
    }

    fn resources_exhausted(&self) -> Option<UnknownReason> {
        if let Some(time_limit) = self.resource_limits.time_limit {
            let now = Instant::now();
            if now > time_limit {
                return Some(UnknownReason::Timeout);
            }
        }

        if let Some(memory_limit) = self.resource_limits.memory_limit {
            if let Some(stats) = memory_stats() {
                if memory_limit < stats.physical_mem {
                    return Some(UnknownReason::OutOfMemory);
                }
            }
        }

        None
    }

    fn redundant(&self, g: &Clause) -> bool {
        for active_clause_id in self.subsumption_index.get_subsumer_candidates(g) {
            let active_clause = self.active.get_by_id(active_clause_id).unwrap();
            if active_clause.subsumes(g) {
                info!(
                    "Subsumption: {} subsumes {}",
                    pretty_print(active_clause, &self.term_bank),
                    pretty_print(active_clause, &self.term_bank)
                );
                return true;
            }
        }
        false
    }

    // TODO: full given-clause loop
    fn run(mut self) -> SuperpositionResult {
        while let Some(mut g) = self.passive.pop() {
            g = g.fresh_variable_clone(&mut self.term_bank);
            g = simplify(g);
            if g.is_empty() {
                return SuperpositionResult::ProofFound;
            }
            if self.redundant(&g) {
                continue;
            }
            self.insert_active(g.clone());
            let new_clauses = self.generate(g);
            new_clauses
                .into_iter()
                .map(|c| cheap_simplify(c))
                .filter(|c| !is_trivial(c))
                .for_each(|clause| self.insert_passive(clause));

            if let Some(reason) = self.resources_exhausted() {
                return SuperpositionResult::Unknown(reason);
            }
            self.term_bank.gc();
        }
        SuperpositionResult::StatementFalse
    }
}

pub fn search_proof(
    clauses: Vec<Clause>,
    term_bank: &mut TermBank,
    resource_config: &ResourceLimitConfig,
) -> SuperpositionResult {
    let mut passive = ClauseQueue::new();
    clauses.into_iter().for_each(|clause| passive.push(clause));
    let active = ClauseSet::new();
    let subterm_index = DiscriminationTree::new();
    let resource_limits = ResourceLimits::of_config(resource_config);
    let subsumption_index = FeatureVectorIndex::new();

    let state = SuperpositionState {
        passive,
        active,
        term_bank,
        subterm_index,
        resource_limits,
        subsumption_index,
    };
    state.run()
}

#[cfg(test)]
mod test {
    use crate::{
        clause::{Clause, Literal, Polarity},
        superposition::SuperpositionResult,
        term_bank::{FunctionInformation, TermBank, VariableInformation},
    };

    use super::search_proof;

    #[test]
    fn basic_equality_resolution() {
        let mut term_bank = TermBank::new();
        let top = term_bank.add_function(FunctionInformation {
            name: "top".to_string(),
            arity: 0,
        });
        let bot = term_bank.add_function(FunctionInformation {
            name: "bot".to_string(),
            arity: 0,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
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
            search_proof(vec![clause], &mut term_bank, &Default::default()),
            SuperpositionResult::ProofFound
        );
    }

    #[test]
    fn basic_transitivity() {
        let mut term_bank = TermBank::new();
        let a = term_bank.add_function(FunctionInformation {
            name: "a".to_string(),
            arity: 0,
        });
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
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
                &Default::default()
            ),
            SuperpositionResult::ProofFound
        );
    }
}
