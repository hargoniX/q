use std::cmp::Ordering;

use log::info;

use crate::{
    clause::{Clause, ClauseSet, Literal, Polarity},
    clause_queue::ClauseQueue,
    discr_tree::DiscriminationTree,
    kbo::KboOrd,
    position::{
        ClausePosition, ClauseSetPosition, LiteralPosition, LiteralSide, Position,
        TermPositionIterator,
    },
    pretty_print::pretty_print,
    subst::{Substitutable, Substitution},
    term_bank::TermBank,
};

struct SuperpositonState<'a> {
    passive: ClauseQueue,
    active: ClauseSet,
    term_bank: &'a mut TermBank,
    subterm_index: DiscriminationTree<ClauseSetPosition>,
}

// TODO: timeout
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SuperpositionResult {
    ProofFound,
    StatementFalse,
    Unknown,
}

fn ordering_check(
    clause: &Clause,
    check_lit_idx: usize,
    subst: &Substitution,
    f: impl Fn(Option<Ordering>) -> bool,
    term_bank: &TermBank,
) -> Option<Vec<Literal>> {
    let mut new_literals = Vec::with_capacity(clause.len());
    let check_lit = clause
        .get_literal(check_lit_idx)
        .clone()
        .subst_with(&subst, term_bank);
    let ok = (0..clause.len())
        .filter(|other_lit_idx| check_lit_idx != *other_lit_idx)
        .all(|other_lit_idx| {
            let other_lit = clause
                .get_literal(other_lit_idx)
                .clone()
                .subst_with(&subst, term_bank);
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
Takes a `clause` and an index `check_lit_idx` to some literal `check_lit` in `clause` together
with a substitution `subst`. Then checks whether `subst(check_lit)` is maximal in `subst(clause)`.

Returns `None` if maximality check fails, otherwise `Some(subst(clause) \ subst(check_lit))`
*/
fn maximality_check(
    clause: &Clause,
    check_lit_idx: usize,
    subst: &Substitution,
    term_bank: &TermBank,
) -> Option<Vec<Literal>> {
    ordering_check(
        clause,
        check_lit_idx,
        subst,
        |ord| ord != Some(Ordering::Greater),
        term_bank,
    )
}

/*
Takes a `clause` and an index `check_lit_idx` to some literal `check_lit` in `clause` together
with a substitution `subst`. Then checks whether `subst(check_lit)` is strictly maximal in
`subst(clause)`.

Returns `None` if maximality check fails, otherwise `Some(subst(clause) \ subst(check_lit))`
*/
fn strict_maximality_check(
    clause: &Clause,
    check_lit_idx: usize,
    subst: &Substitution,
    term_bank: &TermBank,
) -> Option<Vec<Literal>> {
    ordering_check(
        clause,
        check_lit_idx,
        subst,
        |ord| ord != Some(Ordering::Greater) && ord != Some(Ordering::Equal),
        term_bank,
    )
}

fn equality_resolution(clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
    info!("ERes working clause: {}", pretty_print(clause, term_bank));
    for literal_idx in 0..clause.len() {
        let literal = clause.get_literal(literal_idx);
        if literal.is_eq() {
            continue;
        }
        if let Some(subst) = literal.get_lhs().unify(literal.get_rhs(), term_bank) {
            if let Some(new_literals) = maximality_check(clause, literal_idx, &subst, term_bank) {
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
    for literal1_idx in 0..clause.len() {
        let lit1 = clause.get_literal(literal1_idx);
        if lit1.is_ne() {
            continue;
        }
        let lit1_terms = [lit1.get_lhs(), lit1.get_rhs()];

        for literal2_idx in 0..clause.len() {
            let lit2 = clause.get_literal(literal2_idx);
            if lit2.is_ne() || literal2_idx == literal1_idx {
                continue;
            }
            let lit2_terms = [lit2.get_lhs(), lit2.get_rhs()];
            for t1_idx in 0..2 {
                for t2_idx in 0..2 {
                    let l1_lhs = lit1_terms[t1_idx];
                    let l1_rhs = lit1_terms[1 - t1_idx];
                    let l2_lhs = lit2_terms[t2_idx];
                    let l2_rhs = lit2_terms[1 - t2_idx];

                    if let Some(subst) = l1_lhs.unify(l2_lhs, term_bank) {
                        let ord = l1_rhs
                            .clone()
                            .subst_with(&subst, term_bank)
                            .kbo(&l1_lhs.clone().subst_with(&subst, term_bank), term_bank);
                        if ord != Some(Ordering::Equal) && ord != Some(Ordering::Less) {
                            if let Some(mut new_literals) =
                                maximality_check(clause, literal1_idx, &subst, term_bank)
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
}

impl<'a> SuperpositonState<'a> {
    fn insert_active(&mut self, clause: Clause) {
        let clause_id = clause.get_id();
        for literal_idx in 0..clause.len() {
            let literal = clause.get_literal(literal_idx);
            for literal_side in [LiteralSide::Left, LiteralSide::Right] {
                let root_term = literal_side.get_side(literal);
                for (term, term_pos) in TermPositionIterator::new(root_term) {
                    if term.variable_id().is_none() {
                        let pos = ClauseSetPosition::new(
                            ClausePosition::new(
                                LiteralPosition::new(term_pos, literal_side),
                                literal_idx,
                            ),
                            clause_id,
                        );
                        self.subterm_index.insert(&term, pos);
                    }
                }
            }
        }

        info!(
            "Inserting active: {}",
            pretty_print(&clause, self.term_bank)
        );
        self.active.insert(clause);
    }

    fn insert_passive(&mut self, clause: Clause) {
        info!(
            "Inserting passive: {}",
            pretty_print(&clause, self.term_bank)
        );
        self.passive.push(clause);
    }

    fn superposition(&self, given_clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
        //info!("SP working clause: {}", pretty_print(clause1, term_bank));

        let clause1 = given_clause;
        // Part 1: given_clause is the one being used for rewriting.
        for lit1_idx in 0..clause1.len() {
            let lit1 = clause1.get_literal(lit1_idx);
            if lit1.is_ne() {
                continue;
            }
            let lit1_terms = [lit1.get_lhs(), lit1.get_rhs()];
            for t1_idx in 0..2 {
                let lit1_lhs = lit1_terms[t1_idx];
                let lit1_rhs = lit1_terms[1 - t1_idx];
                for candidate_pos in self.subterm_index.get_unification_candidates(lit1_lhs) {
                    let lit2_lhs_p = candidate_pos.term_at(&self.active);
                    if lit2_lhs_p.variable_id().is_some() {
                        continue;
                    }
                    if let Some(subst) = lit1_lhs.unify(lit2_lhs_p, &term_bank) {
                        let l1_ord = lit1_lhs
                            .clone()
                            .subst_with(&subst, term_bank)
                            .kbo(&lit1_rhs.clone().subst_with(&subst, term_bank), term_bank);
                        if l1_ord != Some(Ordering::Equal) && l1_ord != Some(Ordering::Less) {
                            let clause_pos = &candidate_pos.clause_pos;
                            let literal_pos = &clause_pos.literal_pos;
                            let term_pos = &literal_pos.term_pos;
                            let clause2 = self.active.get_by_id(candidate_pos.clause_id).unwrap();
                            info!(
                                "SP working {} together with: {}",
                                pretty_print(clause1, term_bank),
                                pretty_print(clause2, term_bank)
                            );
                            let lit2_idx = clause_pos.literal_idx;
                            let lit2 = clause2.get_literal(lit2_idx);
                            let lit2_lhs = literal_pos.literal_side.get_side(lit2);
                            let lit2_rhs = literal_pos.literal_side.swap().get_side(lit2);
                            let lit2_pol = lit2.get_pol();
                            let l2_ord = lit2_lhs
                                .clone()
                                .subst_with(&subst, term_bank)
                                .kbo(&lit2_rhs.clone().subst_with(&subst, term_bank), term_bank);
                            if l2_ord != Some(Ordering::Equal) && l2_ord != Some(Ordering::Less) {
                                if let Some(mut new_literals1) =
                                    strict_maximality_check(clause1, lit1_idx, &subst, term_bank)
                                {
                                    let checker = match lit2_pol {
                                        Polarity::Eq => strict_maximality_check,
                                        Polarity::Ne => maximality_check,
                                    };
                                    if let Some(mut new_literals2) =
                                        checker(clause2, lit2_idx, &subst, term_bank)
                                    {
                                        new_literals1.append(&mut new_literals2);
                                        let new_rhs =
                                            lit2_rhs.clone().subst_with(&subst, term_bank);
                                        let new_lhs = term_pos
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
                        }
                    }
                }
            }
        }

        // Part 2: the given clause is the one being rewritten
        let clause2 = given_clause;
        for lit2_idx in 0..clause2.len() {
            let lit2 = clause2.get_literal(lit2_idx);
            let lit2_terms = [lit2.get_lhs(), lit2.get_rhs()];
            for t2_idx in 0..2 {
                let lit2_lhs = lit2_terms[t2_idx];
                let lit2_rhs = lit2_terms[1 - t2_idx];
                let lit2_pol = lit2.get_pol();
                for (subterm, subterm_pos) in TermPositionIterator::new(lit2_lhs) {
                    if subterm.variable_id().is_some() {
                        continue;
                    }
                    let candidates = self.subterm_index.get_unification_candidates(&subterm);
                    for candidate_pos in candidates
                        .into_iter()
                        .filter(|p| p.clause_pos.literal_pos.term_pos.is_root())
                    {
                        let clause_pos = &candidate_pos.clause_pos;
                        let clause1 = self.active.get_by_id(candidate_pos.clause_id).unwrap();
                        let lit1_idx = clause_pos.literal_idx;
                        let lit1 = clause1.get_literal(lit1_idx);
                        if lit1.get_pol() != Polarity::Eq {
                            continue;
                        }
                        let literal_pos = &clause_pos.literal_pos;
                        let lit1_lhs = literal_pos.literal_side.get_side(lit1);
                        let lit1_rhs = literal_pos.literal_side.swap().get_side(lit1);

                        if let Some(subst) = subterm.unify(lit1_lhs, term_bank) {
                            let l1_ord = lit1_lhs
                                .clone()
                                .subst_with(&subst, term_bank)
                                .kbo(&lit1_rhs.clone().subst_with(&subst, term_bank), term_bank);
                            if l1_ord != Some(Ordering::Equal) && l1_ord != Some(Ordering::Less) {
                                let l2_ord = lit2_lhs.clone().subst_with(&subst, term_bank).kbo(
                                    &lit2_rhs.clone().subst_with(&subst, term_bank),
                                    term_bank,
                                );
                                if l2_ord != Some(Ordering::Equal) && l2_ord != Some(Ordering::Less)
                                {
                                    if let Some(mut new_literals1) = strict_maximality_check(
                                        clause1, lit1_idx, &subst, term_bank,
                                    ) {
                                        let checker = match lit2_pol {
                                            Polarity::Eq => strict_maximality_check,
                                            Polarity::Ne => maximality_check,
                                        };
                                        if let Some(mut new_literals2) =
                                            checker(clause2, lit2_idx, &subst, term_bank)
                                        {
                                            new_literals1.append(&mut new_literals2);
                                            let new_rhs =
                                                lit2_rhs.clone().subst_with(&subst, term_bank);
                                            let new_lhs = subterm_pos
                                                .replace_term_at(
                                                    lit2_lhs,
                                                    lit1_rhs.clone(),
                                                    term_bank,
                                                )
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
                            }
                        }
                    }
                }
            }
        }
    }

    fn generate(&self, clause: Clause) -> Vec<Clause> {
        let mut acc = Vec::new();
        equality_resolution(&clause, &mut acc, &self.term_bank);
        //equality_factoring(&clause, &mut acc, &self.term_bank);
        self.superposition(&clause, &mut acc, &self.term_bank);
        acc
    }

    // TODO: full given-clause loop
    fn run(mut self) -> SuperpositionResult {
        let mut count = 10;
        while let Some(mut g) = self.passive.pop() {
            if count == 0 {
                return SuperpositionResult::Unknown;
            }
            g = g.fresh_variable_clone(&mut self.term_bank);
            if g.is_empty() {
                return SuperpositionResult::ProofFound;
            }
            self.insert_active(g.clone());
            let new_clauses = self.generate(g);
            new_clauses
                .into_iter()
                .for_each(|clause| self.insert_passive(clause));
            count -= 1;
        }
        SuperpositionResult::StatementFalse
    }
}

pub fn search_proof(clauses: Vec<Clause>, term_bank: &mut TermBank) -> SuperpositionResult {
    let mut passive = ClauseQueue::new();
    clauses.into_iter().for_each(|clause| passive.push(clause));
    let active = ClauseSet::new();
    let subterm_index = DiscriminationTree::new();

    let state = SuperpositonState {
        passive,
        active,
        term_bank,
        subterm_index,
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
            search_proof(vec![clause], &mut term_bank),
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
            search_proof(vec![clause1, clause2, clause3], &mut term_bank),
            SuperpositionResult::ProofFound
        );
    }
}
