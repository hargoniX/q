//! ## Knuth Bendix Order
//! This module contains the naive implementation of Knuth Bendix Order (KBO) from
//! ["Things to Know When Implementing KBO"](https://link.springer.com/content/pdf/10.1007/s10817-006-9031-4.pdf).
//! It is additionally informed by ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf),
//! in particular we draw:
//! - `mu = 1`
//! - the precedence between function symbols which works in two steps:
//!   1. If a function has higher arity than another one it wins
//!   2. If the functions have same arity choose arbitrarily, here we choose to compare by the index
//!      in the term bank.
//!
//! The key type exposed is [KboOrd] together with its implementation for terms and literals.

use std::{cmp::Ordering, collections::HashMap};

use crate::{
    clause::{Literal, Polarity},
    term_bank::{FunctionIdentifier, RawTerm, Term, TermBank},
};

// TODO: implement the optimized version.

const MU: usize = 1;

fn phi(term: &Term) -> usize {
    match &**term {
        RawTerm::Var { .. } => MU,
        RawTerm::App { args, .. } => MU + args.iter().map(phi).sum::<usize>(),
    }
}

struct KboComparator<'a> {
    term_bank: &'a TermBank,
}

impl<'a> KboComparator<'a> {
    fn xlen(&self, term: &Term, i: usize) -> usize {
        match &**term {
            RawTerm::Var { id, .. } => {
                if self.term_bank.get_variable_index(*id) as usize == i {
                    1
                } else {
                    0
                }
            }
            RawTerm::App { args, .. } => args.iter().map(|arg| self.xlen(arg, i)).sum::<usize>(),
        }
    }

    fn var_check(&self, lhs: &Term, rhs: &Term) -> bool {
        let k = self.term_bank.get_variable_count();
        for i in 0..k {
            if !(self.xlen(lhs, i) >= self.xlen(rhs, i)) {
                return false;
            }
        }
        true
    }

    // Return true iff lhs has precedence over rhs
    fn function_precedence(&self, lhs: FunctionIdentifier, rhs: FunctionIdentifier) -> bool {
        let lhs_info = self.term_bank.get_function_info(lhs);
        let rhs_info = self.term_bank.get_function_info(rhs);
        match lhs_info.arity.cmp(&rhs_info.arity) {
            Ordering::Greater => true,
            Ordering::Less => false,
            Ordering::Equal => {
                self.term_bank.get_function_index(lhs) > self.term_bank.get_function_index(rhs)
            }
        }
    }

    fn kbolex(&self, ss: &[Term], ts: &[Term]) -> bool {
        debug_assert_eq!(ss.len(), ts.len());
        for (s, t) in ss.iter().zip(ts.iter()) {
            if s != t {
                return self.kbo_aux(s, t);
            }
        }
        false
    }

    fn kbo_aux(&self, lhs: &Term, rhs: &Term) -> bool {
        match (&**lhs, &**rhs) {
            (
                RawTerm::App {
                    id: f, args: ss, ..
                },
                RawTerm::App {
                    id: g, args: ts, ..
                },
            ) => {
                if self.var_check(lhs, rhs) {
                    let lphi = phi(lhs);
                    let rphi = phi(rhs);
                    match lphi.cmp(&rphi) {
                        Ordering::Greater => true,
                        Ordering::Equal => {
                            self.function_precedence(*f, *g) || (f == g && self.kbolex(ss, ts))
                        }
                        Ordering::Less => false,
                    }
                } else {
                    false
                }
            }
            (RawTerm::App { .. }, RawTerm::Var { id: var_id, .. }) => var_id.occurs_in(lhs),
            (RawTerm::Var { .. }, _) => false,
        }
    }

    fn kbo(lhs: &Term, rhs: &Term, term_bank: &'a TermBank) -> bool {
        let cmp = Self { term_bank };
        cmp.kbo_aux(lhs, rhs)
    }
}

pub trait KboOrd {
    fn kbo(&self, other: &Self, term_bank: &TermBank) -> Option<Ordering>;
}

impl KboOrd for Term {
    fn kbo(&self, other: &Self, term_bank: &TermBank) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if KboComparator::kbo(self, other, term_bank) {
            Some(Ordering::Greater)
        } else if KboComparator::kbo(other, self, term_bank) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

fn literal_to_multiset(lit: &Literal) -> HashMap<&Term, usize> {
    match lit.get_pol() {
        // l = r becomes {l, r}
        Polarity::Eq => HashMap::from([(lit.get_lhs(), 1), (lit.get_rhs(), 1)]),
        // l != r becomes {l, l, r, r}
        Polarity::Ne => HashMap::from([(lit.get_lhs(), 2), (lit.get_rhs(), 2)]),
    }
}

// precondition lhs != rhs
fn multiset_gt(
    lhs: &HashMap<&Term, usize>,
    rhs: &HashMap<&Term, usize>,
    term_bank: &TermBank,
) -> bool {
    // ∀ m ∈ M, rhs(m) > lhs(m)
    let iter = rhs
        .iter()
        .filter(|(elem, count_r)| **count_r > *lhs.get(*elem).unwrap_or(&0));
    for (m, _) in iter {
        // ∃ m_alt ∈ M, lhs(m_alt) > rhs(m_alt) ∧ m_alt > m
        let larger = lhs.iter().find(|(m_alt, count_l)| {
            **count_l > *rhs.get(*m_alt).unwrap_or(&0)
                && m_alt.kbo(m, term_bank) == Some(Ordering::Greater)
        });
        if larger.is_none() {
            return false;
        }
    }
    true
}

impl KboOrd for Literal {
    fn kbo(&self, other: &Self, term_bank: &TermBank) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else {
            let lhs_set = literal_to_multiset(self);
            let rhs_set = literal_to_multiset(other);
            if multiset_gt(&lhs_set, &rhs_set, term_bank) {
                Some(Ordering::Greater)
            } else if multiset_gt(&rhs_set, &lhs_set, term_bank) {
                Some(Ordering::Less)
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use std::{cmp::Ordering, vec};

    use crate::{
        kbo::KboOrd,
        term_bank::{FunctionInformation, TermBank, VariableInformation},
    };

    #[test]
    fn basic_kbo_test() {
        let mut term_bank = TermBank::new();
        let b = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
        });
        let g = term_bank.add_function(FunctionInformation {
            name: "g".to_string(),
            arity: 2,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
        });
        let h = term_bank.add_function(FunctionInformation {
            name: "h".to_string(),
            arity: 1,
        });
        // this creation order ensures: g > h > f > b > c as function precedence

        let x = term_bank.mk_fresh_variable(VariableInformation {
            name: "x".to_string(),
        });
        let y = term_bank.mk_fresh_variable(VariableInformation {
            name: "y".to_string(),
        });

        let t1 = term_bank.mk_app(
            g,
            vec![
                term_bank.mk_app(h, vec![x.clone()]),
                term_bank.mk_app(h, vec![term_bank.mk_const(c)]),
            ],
        );
        let t2 = term_bank.mk_app(g, vec![x.clone(), x.clone()]);
        let t3 = term_bank.mk_app(
            g,
            vec![term_bank.mk_const(b), term_bank.mk_app(f, vec![x.clone()])],
        );
        let t4 = term_bank.mk_app(f, vec![term_bank.mk_app(g, vec![x.clone(), y.clone()])]);
        let t5 = term_bank.mk_app(
            h,
            vec![term_bank.mk_app(g, vec![x.clone(), term_bank.mk_const(c)])],
        );

        assert_eq!(t1.kbo(&t1, &term_bank), Some(Ordering::Equal));
        assert_eq!(t1.kbo(&t2, &term_bank), None);
        assert_eq!(t1.kbo(&t3, &term_bank), Some(Ordering::Greater));
        assert_eq!(t1.kbo(&t4, &term_bank), None);
        assert_eq!(t1.kbo(&t5, &term_bank), Some(Ordering::Greater));

        assert_eq!(t2.kbo(&t1, &term_bank), None);
        assert_eq!(t2.kbo(&t2, &term_bank), Some(Ordering::Equal));
        assert_eq!(t2.kbo(&t3, &term_bank), None);
        assert_eq!(t2.kbo(&t4, &term_bank), None);
        assert_eq!(t2.kbo(&t5, &term_bank), None);

        assert_eq!(t3.kbo(&t1, &term_bank), Some(Ordering::Less));
        assert_eq!(t3.kbo(&t2, &term_bank), None);
        assert_eq!(t3.kbo(&t3, &term_bank), Some(Ordering::Equal));
        assert_eq!(t3.kbo(&t4, &term_bank), None);
        assert_eq!(t3.kbo(&t5, &term_bank), Some(Ordering::Greater));

        assert_eq!(t4.kbo(&t1, &term_bank), None);
        assert_eq!(t4.kbo(&t2, &term_bank), None);
        assert_eq!(t4.kbo(&t3, &term_bank), None);
        assert_eq!(t4.kbo(&t4, &term_bank), Some(Ordering::Equal));
        assert_eq!(t4.kbo(&t5, &term_bank), None);

        assert_eq!(t5.kbo(&t1, &term_bank), Some(Ordering::Less));
        assert_eq!(t5.kbo(&t2, &term_bank), None);
        assert_eq!(t5.kbo(&t3, &term_bank), Some(Ordering::Less));
        assert_eq!(t5.kbo(&t4, &term_bank), None);
        assert_eq!(t5.kbo(&t5, &term_bank), Some(Ordering::Equal));

        assert_eq!(x.kbo(&y, &term_bank), None);
        assert_eq!(t1.kbo(&y, &term_bank), None);
        assert_eq!(t1.kbo(&x, &term_bank), Some(Ordering::Greater));
        assert_eq!(x.kbo(&t1, &term_bank), Some(Ordering::Less));
        assert_eq!(y.kbo(&t1, &term_bank), None);
    }
}
