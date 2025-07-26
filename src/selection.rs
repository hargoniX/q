use bitvec::bitvec;
use std::cmp::Ordering;

use bitvec::vec::BitVec;

use crate::{
    clause::{Clause, Literal, LiteralId, Polarity},
    kbo::KboOrd,
    term_bank::TermBank,
};

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

fn select_first_neg_lit(clause: &Clause) -> BitVec {
    let mut result = bitvec![0; clause.len()];
    for (lit_id, lit) in clause.iter() {
        if lit.get_pol() == Polarity::Ne {
            result.set(lit_id.0, true);
            return result;
        }
    }
    result
}

fn select_first_max_neg_lit_and_all_pos_lits(clause: &Clause, term_bank: &TermBank) -> BitVec {
    let mut result = bitvec![0; clause.len()];
    let mut max_neg_lit: Option<(LiteralId, &Literal)> = None;
    for (lit_id, lit) in clause.iter() {
        if lit.get_pol() == Polarity::Eq {
            result.set(lit_id.0, true);
        } else if let Some((_, max_lit)) = max_neg_lit {
            if lit.kbo(max_lit, term_bank) == Some(Ordering::Greater) {
                max_neg_lit = Some((lit_id, lit));
            }
        } else {
            max_neg_lit = Some((lit_id, lit));
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
        SelectionStrategy::FirstNeg => select_first_neg_lit(clause),
        SelectionStrategy::ZipperSel => {
            select_first_max_neg_lit_and_all_pos_lits(clause, term_bank)
        }
    }
}
