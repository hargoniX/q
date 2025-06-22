use std::cmp::Ordering;

use log::info;

use crate::{
    clause::{Clause, ClauseSet, Literal},
    clause_queue::ClauseQueue,
    kbo::{literal_kbo, term_kbo},
    pretty_print::pretty_print,
    subst::{Substitutable, Substitution},
    term_bank::TermBank,
};

struct SuperpositonState<'a> {
    passive: ClauseQueue,
    active: ClauseSet,
    term_bank: &'a mut TermBank,
}

// TODO: timeout
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SuperpositionResult {
    ProofFound,
    StatementFalse,
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
    let mut new_literals = Vec::with_capacity(clause.len());
    let check_lit = clause.get_literal(check_lit_idx).clone().subst_with(&subst, term_bank);
    let ok = (0..clause.len())
        .filter(|other_lit_idx| check_lit_idx != *other_lit_idx)
        .all(|other_lit_idx| {
            let other_lit = clause
                .get_literal(other_lit_idx)
                .clone()
                .subst_with(&subst, term_bank);
            if literal_kbo(&check_lit, &other_lit, term_bank) != Some(Ordering::Greater) {
                new_literals.push(other_lit);
                true
            } else {
                // abort: we are not maximal
                false
            }
        });
    if ok {
        Some(new_literals)
    } else {
        None
    }
}

fn equality_resolution(clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
    info!("ERes working clause: {}", pretty_print(clause, term_bank));
    for literal_idx in 0..clause.len() {
        let literal = clause.get_literal(literal_idx);
        if literal.is_negative() {
            if let Some(subst) = literal.get_lhs().unify(literal.get_rhs(), term_bank) {
                if let Some(new_literals) =
                    maximality_check(clause, literal_idx, &subst, term_bank)
                {
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
}

fn equality_factoring(clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
    info!("EFact working clause: {}", pretty_print(clause, term_bank));
    for literal1_idx in 0..clause.len() {
        let lit1 = clause.get_literal(literal1_idx);
        if lit1.is_negative() {
            continue;
        }
        let lit1_terms = [lit1.get_lhs(), lit1.get_rhs()];

        for literal2_idx in 0..clause.len() {
            let lit2 = clause.get_literal(literal2_idx);
            if lit2.is_negative() || literal2_idx == literal1_idx {
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
                        if term_kbo(
                            &l1_lhs.clone().subst_with(&subst, term_bank),
                            &l1_rhs.clone().subst_with(&subst, term_bank),
                            term_bank,
                        ) != Some(Ordering::Less)
                        {
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
        self.active.insert(clause);
    }

    fn insert_passive(&mut self, clause: Clause) {
        self.passive.push(clause);
    }

    fn superposition(&self, clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
        //todo!()
    }

    fn generate(&self, clause: Clause) -> Vec<Clause> {
        let mut acc = Vec::new();
        equality_resolution(&clause, &mut acc, &self.term_bank);
        equality_factoring(&clause, &mut acc, &self.term_bank);
        self.superposition(&clause, &mut acc, &self.term_bank);
        acc
    }

    // TODO: full given-clause loop
    fn run(mut self) -> SuperpositionResult {
        while let Some(mut g) = self.passive.pop() {
            g = g.fresh_variable_clone(&mut self.term_bank);
            if g.is_empty() {
                return SuperpositionResult::ProofFound;
            }
            self.insert_active(g.clone());
            let new_clauses = self.generate(g);
            new_clauses
                .into_iter()
                .for_each(|clause| self.insert_passive(clause));
        }
        SuperpositionResult::StatementFalse
    }
}

pub fn search_proof(clauses: Vec<Clause>, term_bank: &mut TermBank) -> SuperpositionResult {
    let mut passive = ClauseQueue::new();
    clauses.into_iter().for_each(|clause| passive.push(clause));
    let active = ClauseSet::new();
    let state = SuperpositonState {
        passive,
        active,
        term_bank,
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
}
