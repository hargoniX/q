//! # Matching
//! This module contains an implementation of a naive matching algorithm to determine a
//! substitution `sigma` s.t. `sigma(s) = t`. The implementation is based on [PyRes](https://github.com/eprover/PyRes/blob/master/matching.py).

use crate::{
    subst::Substitution,
    term_bank::{RawTerm, Sort, Term, TermBank},
};

impl Term {
    /// Attempt to compute a subsitution `sigma` s.t. `sigma(self) = other` where `sigma` strictly
    /// extends the already provided `subst` (if it was provided).
    pub fn matching_partial(
        &self,
        other: &Self,
        subst: Option<Substitution>,
        term_bank: &TermBank,
    ) -> Option<Substitution> {
        let mut subst = subst.unwrap_or_else(Substitution::new);
        let mut matcher_list = vec![self];
        let mut target_list = vec![other];
        while let Some(matcher) = matcher_list.pop() {
            let target = target_list.pop().unwrap();

            match (&**matcher, &**target) {
                (RawTerm::Var { id, .. }, _) => {
                    // We cannot match propositions with variables! This is one of the crucial
                    // points where we make use of our 2-sortedness to avoid inconsistencies.
                    if term_bank.infer_sort(target) != Sort::Individual {
                        return None;
                    }

                    match subst.get(*id) {
                        Some(matcher_value) => {
                            if &matcher_value != target {
                                return None;
                            }
                        }
                        None => {
                            subst.insert(*id, target.clone());
                        }
                    }
                }
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
    pub fn matching(&self, other: &Self, term_bank: &TermBank) -> Option<Substitution> {
        self.matching_partial(other, None, term_bank)
    }
}

#[cfg(test)]
mod test {
    use crate::term_bank::{FunctionInformation, Sort, TermBank, VariableInformation};

    #[test]
    fn basic_matching_test() {
        let mut term_bank = TermBank::new();
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
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

        assert!(f_x.matching(&f_b, &term_bank).is_some());
        assert!(f_b.matching(&f_b, &term_bank).is_some());
        assert!(f_b.matching(&f_x, &term_bank).is_none());
        assert!(f_b.matching(&f_c, &term_bank).is_none());
        assert!(f_x.matching(&f_y, &term_bank).is_some());
    }
}
