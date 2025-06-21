use std::cmp::Ordering;

use log::info;

use crate::{
    clause::{Clause, ClauseSet},
    clause_queue::ClauseQueue,
    kbo::literal_kbo,
    pretty_print::pretty_print,
    subst::Substitutable,
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

fn equality_resolution(clause: &Clause, acc: &mut Vec<Clause>, term_bank: &TermBank) {
    info!("ERes working clause: {}", pretty_print(clause, term_bank));
    for literal_idx in 0..clause.len() {
        let literal = clause.get_literal(literal_idx);
        if literal.is_negative() {
            if let Some(subst) = literal.get_lhs().unify(literal.get_rhs(), term_bank) {
                let mut new_literals = Vec::with_capacity(clause.len());
                let new_lit = literal.clone().subst_with(&subst, term_bank);
                let larger_idx = (0..clause.len())
                    .filter(|new_literal_idx| literal_idx != *new_literal_idx)
                    .find(|new_literal_idx| {
                        let check_lit = clause
                            .get_literal(*new_literal_idx)
                            .clone()
                            .subst_with(&subst, term_bank);
                        if literal_kbo(&check_lit, &new_lit, term_bank) != Some(Ordering::Greater) {
                            new_literals.push(check_lit);
                            false
                        } else {
                            // abort: we are not maximal
                            true
                        }
                    });
                if larger_idx.is_none() {
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
    //todo!()
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
