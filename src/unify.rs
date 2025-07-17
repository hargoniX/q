//! ## First Order Unification
//! This module implements the naive rule based first order unification as taught in
//! [LMU's ATP course](https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp/slides06-general-resolution.pdf).
//! The key function is [Term::unify].

use log::debug;

use crate::{
    pretty_print::pretty_print,
    subst::{HashSubstitution, Substitutable, Substitution},
    term_bank::{Term, TermBank},
};

struct UnificationProblem {
    equations: Vec<(Term, Term)>,
    substitution: HashSubstitution,
}

enum UnificationState {
    Success,
    Failure,
    Next,
}

// TODO: Polynomial Unification or better
impl UnificationProblem {
    fn new(lhs: Term, rhs: Term) -> Self {
        let equations = vec![(lhs, rhs)];
        let substitution = HashSubstitution::new();
        Self {
            equations,
            substitution,
        }
    }

    fn step(&mut self, term_bank: &TermBank) -> UnificationState {
        match self.equations.pop() {
            Some((lhs, rhs)) => {
                if lhs == rhs {
                    // t = t, E => E
                    UnificationState::Next
                } else {
                    match (lhs.function_id(), rhs.function_id()) {
                        (Some(f), Some(g)) => {
                            if f == g {
                                // f(s_1, ..., s_n) = f(t_1, ..., t_n), E =>
                                // s_1 = t_1, ..., s_n = t_n, E
                                lhs.function_args()
                                    .unwrap()
                                    .iter()
                                    .zip(rhs.function_args().unwrap())
                                    .for_each(|(s, n)| self.equations.push((s.clone(), n.clone())));
                                UnificationState::Next
                            } else {
                                // f(...) = g(...), E => bot if f != g
                                UnificationState::Failure
                            }
                        }
                        (None, _) => {
                            let var_id = lhs.variable_id().unwrap();
                            if var_id.occurs_in(&rhs) {
                                // x = t, E => bot if x != t and x in var(t)
                                UnificationState::Failure
                            } else {
                                // x = t, E => x = t, E {x |-> t} if x in var(E) and x not in var(t)
                                let mut new_subst = HashSubstitution::new();
                                new_subst.insert(var_id, rhs.clone());
                                self.equations = self
                                    .equations
                                    .iter()
                                    .map(|(lhs, rhs)| {
                                        (
                                            lhs.clone().subst_with(&new_subst, term_bank),
                                            rhs.clone().subst_with(&new_subst, term_bank),
                                        )
                                    })
                                    .collect();
                                // TODO: consider general compose method
                                self.substitution.compose_binding(var_id, rhs, term_bank);
                                UnificationState::Next
                            }
                        }
                        (Some(_), None) => {
                            self.equations.push((rhs, lhs));
                            UnificationState::Next
                        }
                    }
                }
            }
            None => UnificationState::Success,
        }
    }

    fn run(mut self, term_bank: &TermBank) -> Option<HashSubstitution> {
        loop {
            match self.step(term_bank) {
                UnificationState::Success => return Some(self.substitution),
                UnificationState::Failure => return None,
                UnificationState::Next => continue,
            }
        }
    }
}

impl Term {
    /// Try to unify `self` and `other`, returning `Some(subst)` on success and `None` otherwise.
    /// If both `self` and `other` are ground this operation is `O(1)` otherwise potentially
    /// expensive.
    pub fn unify(&self, other: &Self, term_bank: &TermBank) -> Option<HashSubstitution> {
        debug!(
            "Unifying, {} with {}",
            pretty_print(self, term_bank),
            pretty_print(other, term_bank),
        );

        let res = if self.is_ground() && other.is_ground() {
            if self == other {
                Some(HashSubstitution::new())
            } else {
                None
            }
        } else {
            let problem = UnificationProblem::new(self.clone(), other.clone());
            problem.run(term_bank)
        };
        debug!("Unification success? {}", res.is_some());
        res
    }
}

#[cfg(test)]
mod test {
    use crate::{
        subst::Substitutable,
        term_bank::{FunctionInformation, TermBank, VariableInformation},
    };

    #[test]
    fn ex_3_10_6() {
        let mut term_bank = TermBank::new();
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });
        let g = term_bank.add_function(FunctionInformation {
            name: "g".to_string(),
            arity: 2,
        });
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });

        let lhs = term_bank.mk_app(g, vec![x.clone(), term_bank.mk_app(f, vec![x.clone()])]);
        let rhs = term_bank.mk_app(g, vec![term_bank.mk_const(b), y.clone()]);
        let subst = lhs.unify(&rhs, &term_bank);
        assert!(subst.is_some());
        let subst = subst.unwrap();
        assert_eq!(
            lhs.subst_with(&subst, &term_bank),
            rhs.subst_with(&subst, &term_bank)
        );
    }

    #[test]
    fn ex_3_10_7() {
        let mut term_bank = TermBank::new();
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 2,
        });
        let g = term_bank.add_function(FunctionInformation {
            name: "g".to_string(),
            arity: 3,
        });
        let a = term_bank.add_function(FunctionInformation {
            name: "a".to_string(),
            arity: 0,
        });
        let a = term_bank.mk_const(a);
        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });
        let z = term_bank.mk_fresh_variable(VariableInformation {
            name: "z".to_string(),
        });

        let lhs = term_bank.mk_app(g, vec![x.clone(), y.clone(), z.clone()]);
        let rhs = term_bank.mk_app(
            g,
            vec![
                term_bank.mk_app(f, vec![y.clone(), y.clone()]),
                term_bank.mk_app(f, vec![z.clone(), z.clone()]),
                term_bank.mk_app(f, vec![a.clone(), a.clone()]),
            ],
        );
        let subst = lhs.unify(&rhs, &term_bank);
        assert!(subst.is_some());
        let subst = subst.unwrap();
        assert_eq!(
            lhs.subst_with(&subst, &term_bank),
            rhs.subst_with(&subst, &term_bank)
        );
    }
}
