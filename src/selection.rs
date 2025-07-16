use std::cmp::Ordering;

use crate::{
    clause::{Clause, Literal, LiteralId, Polarity},
    kbo::KboOrd,
    term_bank::{Sort, TermBank},
};
pub type Selection<'a> = Vec<(LiteralId, &'a Literal)>;

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum SelectionStrategy {
    /// Never select a literal
    NoSelection,
    /// Select the first negative literal
    SelectFirstNegLit,
    /// Based on Zipperposition's max_goal selection function with strict set to false:
    /// Select the first maximal negative literal and all positive literals
    SelectFirstMaximalNegLitAndAllPosLits,
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

fn select_first_neg_lit<'a>(
    clause: &'a Clause,
    term_bank: &TermBank,
    filter_props: bool,
) -> Option<Selection<'a>> {
    for (lit_id, lit) in clause.iter() {
        if lit.get_pol() == Polarity::Ne && (!filter_props || is_propositional(lit, term_bank)) {
            return Some(vec![(lit_id, clause.get_literal(lit_id))]);
        }
    }
    None
}

fn select_first_max_neg_lit_and_all_pos_lits<'a>(
    clause: &'a Clause,
    term_bank: &TermBank,
    filter_props: bool,
) -> Option<Selection<'a>> {
    let mut results = Vec::new();
    let mut max_neg_lit: Option<(LiteralId, &Literal)> = None;
    for (lit_id, lit) in clause.iter() {
        if !filter_props || is_propositional(lit, term_bank) {
            if lit.get_pol() == Polarity::Eq {
                if !filter_props {
                    results.push((lit_id, lit));
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
    if let Some(neg_lit) = max_neg_lit {
        results.push(neg_lit);
        Some(results)
    } else {
        None
    }
}

pub fn select_literals<'a>(
    clause: &'a Clause,
    strategy: &SelectionStrategy,
    term_bank: &TermBank,
    filter_props: bool,
) -> Option<Selection<'a>> {
    match strategy {
        SelectionStrategy::NoSelection => None,
        SelectionStrategy::SelectFirstNegLit => {
            select_first_neg_lit(clause, term_bank, filter_props)
        }
        SelectionStrategy::SelectFirstMaximalNegLitAndAllPosLits => {
            select_first_max_neg_lit_and_all_pos_lits(clause, term_bank, filter_props)
        }
    }
}
