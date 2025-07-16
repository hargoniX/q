use crate::clause::{Clause, Literal, LiteralId, Polarity};
pub type Selection<'a> = Vec<(LiteralId, &'a Literal)>;

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum SelectionStrategy {
    /// Never select a literal
    NoSelection,
    /// Select the first negative literal
    SelectFirstNegLit,
    /// Select the negative literal in which both terms have the largest size difference
    SelectDiffNegLit,
    /// Select first negative literal which is maximal in ?X
    SelectFirstMaximalNegLit,
}

fn select_first_neg_lit(clause: &Clause) -> Option<Selection> {
    for (lit_id, lit) in clause.iter() {
        if lit.get_pol() == Polarity::Ne {
            return Some(vec![(lit_id, clause.get_literal(lit_id))]);
        }
    }
    None
}

pub fn select_literals<'a>(
    clause: &'a Clause,
    strategy: &SelectionStrategy,
) -> Option<Selection<'a>> {
    match strategy {
        SelectionStrategy::NoSelection => None,
        SelectionStrategy::SelectFirstNegLit => select_first_neg_lit(clause),
        SelectionStrategy::SelectDiffNegLit => todo!(),
        SelectionStrategy::SelectFirstMaximalNegLit => todo!(),
    }
}
