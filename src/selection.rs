use bitvec::bitvec;
use std::cmp::Ordering;

use bitvec::vec::BitVec;

use crate::{
    clause::{Clause, Literal, LiteralId, Polarity},
    kbo::KboOrd,
    term_bank::{Sort, TermBank},
};

const FILTER_PROPS: bool = false;

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum SelectionStrategy {
    /// Never select a literal
    NoSel,
    /// Select the first negative literal
    FirstNeg,
    /// Based on Zipperposition's max_goal selection function with strict set to false:
    /// Select the first maximal negative literal and all positive literals
    ZipperSel,
}

fn is_propositional(lit: &Literal, term_bank: &TermBank) -> bool {
    if let Some(id) = lit.get_rhs().function_id() {
        if term_bank.get_function_info(id).sort == Sort::Individual {
            return true;
        }
    } else {
        return true;
    }
    false
}

fn select_first_neg_lit(clause: &Clause, term_bank: &TermBank) -> BitVec {
    let mut result = bitvec![0; clause.len()];
    for (lit_id, lit) in clause.iter() {
        if lit.get_pol() == Polarity::Ne && (!FILTER_PROPS || is_propositional(lit, term_bank)) {
            result.set(lit_id.0, true);
        }
    }
    result
}

fn select_first_max_neg_lit_and_all_pos_lits(clause: &Clause, term_bank: &TermBank) -> BitVec {
    let mut result = bitvec![0; clause.len()];
    let mut max_neg_lit: Option<(LiteralId, &Literal)> = None;
    for (lit_id, lit) in clause.iter() {
        if !FILTER_PROPS || is_propositional(lit, term_bank) {
            if lit.get_pol() == Polarity::Eq {
                if !FILTER_PROPS {
                    result.set(lit_id.0, true);
                }
            } else if let Some((_, max_lit)) = max_neg_lit {
                if lit.kbo(max_lit, term_bank) == Some(Ordering::Greater) {
                    max_neg_lit = Some((lit_id, lit));
                }
            } else {
                max_neg_lit = Some((lit_id, lit));
            }
        }
    }
    if let Some((neg_lit_id, _)) = max_neg_lit {
        result.set(neg_lit_id.0, true);
        result
    } else {
        bitvec![0; clause.len()]
    }
}

pub fn select_literals(
    clause: &Clause,
    strategy: &SelectionStrategy,
    term_bank: &TermBank,
) -> BitVec {
    match strategy {
        SelectionStrategy::NoSel => bitvec![0; clause.len()],
        SelectionStrategy::FirstNeg => select_first_neg_lit(clause, term_bank),
        SelectionStrategy::ZipperSel => {
            select_first_max_neg_lit_and_all_pos_lits(clause, term_bank)
        }
    }
}
