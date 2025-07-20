//! ## Knuth Bendix Order
//! This module contains an imperative adaption of the efficient implementation of Knuth Bendix Order (KBO) from
//! ["Things to Know When Implementing KBO"](https://link.springer.com/content/pdf/10.1007/s10817-006-9031-4.pdf).
//! Most notably we don't rely on a fixed size array to store the variable balance, but instead rely on a HashMap.
//! It is additionally informed by ["E – A Brainiac Theorem Prover"](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf),
//! in particular we draw:
//! - `mu = 1`
//! - the precedence between function symbols which works in two steps:
//!   1. If a function has higher arity than another one it wins
//!   2. If the functions have same arity choose arbitrarily, here we choose to compare by the index
//!      in the term bank.
//!
//! The key type exposed is [KboOrd] together with its implementation for terms and literals.
//!
//! The general idea is that we traverse the two terms only once, but maintain a balance counter
//! for the weight and each of the met variables.
//!
//! Mapping function names to paper names:
//! Paper      | Code
//! -----------|--------------
//! inc        | inc_var
//! dec        | dec_var
//! tckbolex   | kbo_lex
//! tckbo      | kbo_aux
//! tckbo'     | kbo_functions
//! mfyVWBc    | modify_balances_contains
//! mfyVWBc_tl | modify_balances_list_contains
//! mfyVWB_tl  | modify_balances_list

use std::{cmp::Ordering, collections::hash_map::Entry};

use rustc_hash::FxHashMap;

use crate::{
    clause::{Literal, Polarity},
    position::LiteralSide,
    term_bank::{FunctionIdentifier, RawTerm, Term, TermBank, VariableIdentifier},
};

// TODO: evaluate kbo_6 pacman lemma

// Since the weight is calculated on the fly, there is no explicit phi(t):
// - each variable and function symbol weights MU
// - each function weights MU+phi(args)
const MU: i32 = 1;

struct KboComparator<'a> {
    term_bank: &'a TermBank,
    var_balance: FxHashMap<VariableIdentifier, i32>,
    weight_balance: i32,
    num_neg: usize,
    num_pos: usize,
}

impl<'a> KboComparator<'a> {
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

    fn inc_var(&mut self, id: VariableIdentifier) {
        match self.var_balance.entry(id) {
            Entry::Occupied(mut entry) => {
                let num = *entry.get();
                if num == 0 {
                    self.num_pos += 1;
                } else if num == -1 {
                    self.num_neg -= 1;
                }
                entry.insert(num + 1);
            }
            Entry::Vacant(entry) => {
                self.num_pos += 1;
                entry.insert(1);
            }
        }
    }

    fn dec_var(&mut self, id: VariableIdentifier) {
        match self.var_balance.entry(id) {
            Entry::Occupied(mut entry) => {
                let num = *entry.get();
                if num == 0 {
                    self.num_neg += 1;
                } else if num == 1 {
                    self.num_pos -= 1;
                }
                entry.insert(num - 1);
            }
            Entry::Vacant(entry) => {
                self.num_neg += 1;
                entry.insert(-1);
            }
        }
    }

    fn modify_balances_list(&mut self, ss: &[Term], pos: LiteralSide) {
        for s in ss.iter() {
            match &**s {
                RawTerm::Var { id: x, .. } => match pos {
                    LiteralSide::Left => {
                        self.inc_var(*x);
                        self.weight_balance += MU;
                    }
                    LiteralSide::Right => {
                        self.dec_var(*x);
                        self.weight_balance -= MU;
                    }
                },
                RawTerm::App { args: ss, .. } => {
                    self.modify_balances_list(ss, pos);
                    match pos {
                        LiteralSide::Left => self.weight_balance += MU,
                        LiteralSide::Right => self.weight_balance -= MU,
                    }
                }
            }
        }
    }

    fn modify_balances_list_contains(
        &mut self,
        ss: &[Term],
        y: &VariableIdentifier,
        pos: LiteralSide,
    ) -> bool {
        for (idx, s) in ss.iter().enumerate() {
            if self.modify_balances_contains(s, y, pos) {
                // Simply modify the balances for the remaining terms
                // since y already occurs in s
                self.modify_balances_list(&ss[idx + 1..], pos);
                return true;
            }
        }
        false
    }

    fn modify_balances_contains(
        &mut self,
        t: &Term,
        y: &VariableIdentifier,
        pos: LiteralSide,
    ) -> bool {
        match &**t {
            RawTerm::Var { id: x, .. } => match pos {
                LiteralSide::Left => {
                    self.inc_var(*x);
                    self.weight_balance += MU;
                    x == y
                }
                LiteralSide::Right => {
                    self.dec_var(*x);
                    self.weight_balance -= MU;
                    x == y
                }
            },
            RawTerm::App { args: ss, .. } => {
                let result = self.modify_balances_list_contains(ss, y, pos);
                match pos {
                    LiteralSide::Left => self.weight_balance += MU,
                    LiteralSide::Right => self.weight_balance -= MU,
                }
                result
            }
        }
    }

    // Only called if f = g, which implies identical arity
    fn kbo_lex(&mut self, ss: &[Term], ts: &[Term]) -> Option<Ordering> {
        debug_assert_eq!(ss.len(), ts.len());
        for (idx, (s, t)) in ss.iter().zip(ts.iter()).enumerate() {
            let result = self.kbo_aux(s, t);
            // Lexicographic iteration: skip until we find unequal terms
            if let Some(Ordering::Equal) = result {
                continue;
            } else {
                // Fix balances of the rest, then return
                self.modify_balances_list(&ss[idx + 1..], LiteralSide::Left);
                self.modify_balances_list(&ts[idx + 1..], LiteralSide::Right);
                return result;
            }
        }
        Some(Ordering::Equal)
    }

    fn kbo_functions(
        &mut self,
        f: &FunctionIdentifier,
        g: &FunctionIdentifier,
        ss: &[Term],
        ts: &[Term],
    ) -> Option<Ordering> {
        // Weight cancels out, so we only have to focus on the args
        if f == g {
            self.kbo_lex(ss, ts)
        } else {
            self.modify_balances_list(ss, LiteralSide::Left);
            self.modify_balances_list(ts, LiteralSide::Right);
            None
        }
    }

    fn kbo_aux(&mut self, lhs: &Term, rhs: &Term) -> Option<Ordering> {
        match (&**lhs, &**rhs) {
            (RawTerm::Var { id: x, .. }, RawTerm::Var { id: y, .. }) => {
                // Weight cancels out, so we only have to modify the variable balance
                self.inc_var(*x);
                self.dec_var(*y);
                if x == y { Some(Ordering::Equal) } else { None }
            }
            (RawTerm::Var { id: x, .. }, RawTerm::App { .. }) => {
                let contained = self.modify_balances_contains(rhs, x, LiteralSide::Right);
                // Update variable and weight balance only for the variable part
                self.inc_var(*x);
                self.weight_balance += MU;
                if contained {
                    Some(Ordering::Less)
                } else {
                    None
                }
            }
            (RawTerm::App { .. }, RawTerm::Var { id: y, .. }) => {
                let contained = self.modify_balances_contains(lhs, y, LiteralSide::Left);
                // Update variable and weight balance only for the variable part
                self.dec_var(*y);
                self.weight_balance -= MU;
                if contained {
                    Some(Ordering::Greater)
                } else {
                    None
                }
            }
            (
                RawTerm::App {
                    id: f, args: ss, ..
                },
                RawTerm::App {
                    id: g, args: ts, ..
                },
            ) => {
                // We assign each function symbol the same weight, so they cancel out
                let lex_ord = self.kbo_functions(f, g, ss, ts);
                let g_or_n = if self.num_neg == 0 {
                    Some(Ordering::Greater)
                } else {
                    None
                };
                let l_or_n = if self.num_pos == 0 {
                    Some(Ordering::Less)
                } else {
                    None
                };
                if self.weight_balance > 0 {
                    g_or_n
                } else if self.weight_balance < 0 {
                    l_or_n
                } else if self.function_precedence(*f, *g) {
                    g_or_n
                } else if self.function_precedence(*g, *f) {
                    l_or_n
                } else if f != g {
                    None
                } else if lex_ord == Some(Ordering::Equal) {
                    Some(Ordering::Equal)
                } else if lex_ord == Some(Ordering::Greater) {
                    g_or_n
                } else if lex_ord == Some(Ordering::Less) {
                    l_or_n
                } else {
                    None
                }
            }
        }
    }

    fn kbo(lhs: &Term, rhs: &Term, term_bank: &'a TermBank) -> Option<Ordering> {
        let mut cmp = Self {
            term_bank,
            var_balance: FxHashMap::default(),
            weight_balance: 0,
            num_neg: 0,
            num_pos: 0,
        };
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
        } else {
            KboComparator::kbo(self, other, term_bank)
        }
    }
}

impl KboOrd for Literal {
    // Taken from dupers interpretation of the multiset formalism
    fn kbo(&self, other: &Self, term_bank: &TermBank) -> Option<Ordering> {
        let cll = self.get_lhs().kbo(other.get_lhs(), term_bank)?;
        let clr = self.get_lhs().kbo(other.get_rhs(), term_bank)?;
        let crl = self.get_rhs().kbo(other.get_lhs(), term_bank)?;
        let crr = self.get_rhs().kbo(other.get_rhs(), term_bank)?;

        match (cll, clr, crl, crr) {
            (Ordering::Greater, Ordering::Greater, _, _) => Some(Ordering::Greater),
            (_, _, Ordering::Greater, Ordering::Greater) => Some(Ordering::Greater),
            (Ordering::Less, _, Ordering::Less, _) => Some(Ordering::Less),
            (_, Ordering::Less, _, Ordering::Less) => Some(Ordering::Less),

            (Ordering::Greater, _, _, Ordering::Greater) => Some(Ordering::Greater),
            (Ordering::Less, _, _, Ordering::Less) => Some(Ordering::Less),
            (_, Ordering::Greater, Ordering::Greater, _) => Some(Ordering::Greater),
            (_, Ordering::Less, Ordering::Less, _) => Some(Ordering::Less),
            (_, _, _, _) => {
                let csign = match (self.get_pol(), other.get_pol()) {
                    (Polarity::Eq, Polarity::Eq) => Ordering::Equal,
                    (Polarity::Ne, Polarity::Eq) => Ordering::Greater,
                    (Polarity::Eq, Polarity::Ne) => Ordering::Less,
                    (Polarity::Ne, Polarity::Ne) => Ordering::Equal,
                };

                match (cll, clr, crl, crr, csign) {
                    (Ordering::Equal, _, _, c, Ordering::Equal) => Some(c),
                    (_, Ordering::Equal, c, _, Ordering::Equal) => Some(c),
                    (_, c, Ordering::Equal, _, Ordering::Equal) => Some(c),
                    (c, _, _, Ordering::Equal, Ordering::Equal) => Some(c),

                    (Ordering::Equal, _, _, Ordering::Equal, _) => Some(Ordering::Equal),
                    (_, Ordering::Equal, Ordering::Equal, _, _) => Some(Ordering::Equal),

                    (Ordering::Equal, _, _, _, c) => Some(c),
                    (_, Ordering::Equal, _, _, c) => Some(c),
                    (_, _, Ordering::Equal, _, c) => Some(c),
                    (_, _, _, Ordering::Equal, c) => Some(c),

                    (_, _, _, _, _) => {
                        panic!("unexpected comparisons : {cll:?} {clr:?} {crl:?} {crr:?} {csign:?}")
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use std::{cmp::Ordering, vec};

    use crate::{
        kbo::KboOrd,
        term_bank::{FunctionInformation, Sort, TermBank, VariableInformation},
    };

    #[test]
    fn basic_kbo_test() {
        let mut term_bank = TermBank::new();
        let b = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
            sort: Sort::Individual,
        });
        let c = term_bank.add_function(FunctionInformation {
            name: "c".to_string(),
            arity: 0,
            sort: Sort::Individual,
        });
        let g = term_bank.add_function(FunctionInformation {
            name: "g".to_string(),
            arity: 2,
            sort: Sort::Individual,
        });
        let f = term_bank.add_function(FunctionInformation {
            name: "f".to_string(),
            arity: 1,
            sort: Sort::Individual,
        });
        let h = term_bank.add_function(FunctionInformation {
            name: "h".to_string(),
            arity: 1,
            sort: Sort::Individual,
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
