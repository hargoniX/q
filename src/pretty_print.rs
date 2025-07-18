//! ## Pretty Printing
//! This module contains the [BankPrettyPrint] trait which can be implemented for types that may
//! be pretty printed given some information from a term bank.

use crate::{
    clause::{Literal, Polarity},
    term_bank::{RawTerm, Term, TermBank},
};

/// Types that can be pretty printed using information from a [TermBank]
pub trait BankPrettyPrint {
    /// Print the representation of `self` into `acc` using information from `term_bank`.
    fn print_into(&self, term_bank: &TermBank, acc: &mut String);
}

/// Pretty print some value that implements [BankPrettyPrint] to a string using information from
/// `term_bank`.
pub fn pretty_print<T: BankPrettyPrint>(t: &T, term_bank: &TermBank) -> String {
    let mut acc = String::new();
    t.print_into(term_bank, &mut acc);
    acc
}

fn print_term_into_aux(term: &Term, term_bank: &TermBank, acc: &mut String) {
    match &**term {
        RawTerm::Var { id, .. } => {
            let name = &term_bank.get_variable_info(*id).name;
            if name.ends_with("rep") {
                let prefix = name.rsplit_once("_").unwrap().0;
                acc.push_str(prefix);
            } else {
                acc.push_str(name);
            }
        }
        RawTerm::App { id, args, .. } => {
            let info = term_bank.get_function_info(*id);
            acc.push_str(&info.name);
            if info.arity > 0 {
                acc.push('(');
                for arg in args.iter().take(args.len() - 1) {
                    print_term_into_aux(arg, term_bank, acc);
                    acc.push_str(", ");
                }
                print_term_into_aux(&args[args.len() - 1], term_bank, acc);
                acc.push(')');
            } else {
                acc.push_str("()");
            }
        }
    }
}

impl BankPrettyPrint for Term {
    fn print_into(&self, term_bank: &TermBank, acc: &mut String) {
        print_term_into_aux(self, term_bank, acc);
    }
}

impl BankPrettyPrint for Polarity {
    fn print_into(&self, _term_bank: &TermBank, acc: &mut String) {
        match self {
            Polarity::Eq => acc.push('='),
            Polarity::Ne => acc.push('≠'),
        }
    }
}

impl BankPrettyPrint for Literal {
    fn print_into(&self, term_bank: &TermBank, acc: &mut String) {
        self.get_lhs().print_into(term_bank, acc);
        acc.push(' ');
        self.get_pol().print_into(term_bank, acc);
        acc.push(' ');
        self.get_rhs().print_into(term_bank, acc);
    }
}
