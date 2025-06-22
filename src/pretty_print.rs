//! ## Pretty Printing
//! This module contains the [BankPrettyPrint] trait which can be implemented for types that may
//! be pretty printed given some information from a term bank.

use crate::{
    clause::{Clause, Literal, Polarity},
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
        RawTerm::Var { id, .. } => acc.push_str(&term_bank.get_variable_info(*id).name),
        RawTerm::App { id, args, .. } => {
            let info = term_bank.get_function_info(*id);
            acc.push_str(&info.name);
            if info.arity > 0 {
                acc.push_str("(");
                for arg_idx in 0..(args.len() - 1) {
                    let arg = &args[arg_idx];
                    print_term_into_aux(arg, term_bank, acc);
                    acc.push_str(", ");
                }
                print_term_into_aux(&args[args.len() - 1], term_bank, acc);
                acc.push_str(")");
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
            Polarity::Eq => acc.push_str("="),
            Polarity::Ne => acc.push_str("≠"),
        }
    }
}

impl BankPrettyPrint for Literal {
    fn print_into(&self, term_bank: &TermBank, acc: &mut String) {
        self.get_lhs().print_into(term_bank, acc);
        acc.push_str(" ");
        self.get_pol().print_into(term_bank, acc);
        acc.push_str(" ");
        self.get_rhs().print_into(term_bank, acc);
    }
}

impl BankPrettyPrint for Clause {
    fn print_into(&self, term_bank: &TermBank, acc: &mut String) {
        if self.is_empty() {
            acc.push_str("⊥");
        } else {
            for lit_idx in 0..(self.len() - 1) {
                let lit = self.get_literal(lit_idx);
                acc.push_str("(");
                lit.print_into(term_bank, acc);
                acc.push_str(") ∨ ");
            }
            let lit = self.get_literal(self.len() - 1);
            acc.push_str("(");
            lit.print_into(term_bank, acc);
            acc.push_str(")");
        }
    }
}
