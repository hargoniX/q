//! # Matching
//! This module contains an implementation of a naive matching algorithm to determine a
//! substitution `sigma` s.t. `sigma(s) = t`. The implementation is based on [PyRes](https://github.com/eprover/PyRes/blob/master/matching.py).

use crate::{
    subst::{HashSubstitution, Substitution},
    term_bank::{RawTerm, Term},
};

impl Term {
    /// Attempt to compute a subsitution `sigma` s.t. `sigma(self) = other` where `sigma` strictly
    /// extends the already provided `subst` (if it was provided).
    pub fn matching_partial<S: Substitution>(
        &self,
        other: &Self,
        subst: Option<S>,
    ) -> Option<S> {
        let mut subst = subst.unwrap_or_else(S::new);
        let mut matcher_list = vec![self];
        let mut target_list = vec![other];
        while let Some(matcher) = matcher_list.pop() {
            let target = target_list.pop().unwrap();

            match (&**matcher, &**target) {
                (RawTerm::Var { id, .. }, _) => match subst.get(*id) {
                    Some(matcher_value) => {
                        if &matcher_value != target {
                            return None;
                        }
                    }
                    None => {
                        subst.insert(*id, target.clone());
                    }
                },
                (RawTerm::App { .. }, RawTerm::Var { .. }) => {
                    return None;
                }
                (
                    RawTerm::App {
                        id: m_id,
                        args: m_args,
                        ..
                    },
                    RawTerm::App {
                        id: t_id,
                        args: t_args,
                        ..
                    },
                ) => {
                    if t_id != m_id {
                        return None;
                    }

                    matcher_list.extend(m_args.iter());
                    target_list.extend(t_args.iter());
                }
            }
        }
        Some(subst)
    }

    /// Attempt to compute a substitution `sigma` s.t. `sigma(self) = other`.
    pub fn matching(&self, other: &Self) -> Option<HashSubstitution> {
        self.matching_partial(other, None)
    }
}

#[cfg(test)]
mod test {
    use crate::term_bank::{FunctionInformation, TermBank, VariableInformation};

    #[test]
    fn basic_matching_test() {
        let mut term_bank = TermBank::new();
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });
        let b = term_bank.add_function(FunctionInformation {
            name: "b".to_string(),
            arity: 0,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
        });
        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });

        let f_x = term_bank.mk_app(f, vec![x.clone()]);
        let f_y = term_bank.mk_app(f, vec![y.clone()]);
        let f_b = term_bank.mk_app(f, vec![term_bank.mk_const(b)]);
        let f_c = term_bank.mk_app(f, vec![term_bank.mk_const(c)]);

        assert!(f_x.matching(&f_b).is_some());
        assert!(f_b.matching(&f_b).is_some());
        assert!(f_b.matching(&f_x).is_none());
        assert!(f_b.matching(&f_c).is_none());
        assert!(f_x.matching(&f_y).is_some());
    }
}
