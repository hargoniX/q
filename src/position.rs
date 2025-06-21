use crate::{
    clause::{Clause, ClauseId, ClauseSet, Literal},
    term_bank::{RawTerm, Term},
};

pub trait Position {
    type T;
    fn term_at<'a>(&self, t: &'a Self::T) -> &'a Term;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TermPosition {
    path: Vec<usize>,
}

impl TermPosition {
    pub fn new() -> Self {
        Self { path: Vec::new() }
    }

    pub fn of_vec(path: Vec<usize>) -> Self {
        Self { path }
    }

    pub fn add(&mut self, next: usize) {
        self.path.push(next);
    }
}

impl Position for TermPosition {
    type T = Term;

    fn term_at<'a>(&self, term: &'a Self::T) -> &'a Term {
        let mut term = term;
        for step in self.path.iter() {
            match &**term {
                RawTerm::Var { .. } => panic!("Position step to take but arrived at variable"),
                RawTerm::App { args, .. } => term = &args[*step],
            }
        }
        term
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LiteralSide {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiteralPosition {
    term_pos: TermPosition,
    literal_side: LiteralSide,
}

impl LiteralPosition {
    pub fn new(term_pos: TermPosition, literal_side: LiteralSide) -> Self {
        Self {
            term_pos,
            literal_side,
        }
    }
}

impl Position for LiteralPosition {
    type T = Literal;

    fn term_at<'a>(&self, t: &'a Self::T) -> &'a Term {
        let side_term = match self.literal_side {
            LiteralSide::Left => t.get_lhs(),
            LiteralSide::Right => t.get_rhs(),
        };
        self.term_pos.term_at(side_term)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClausePosition {
    literal_pos: LiteralPosition,
    literal_idx: usize,
}

impl ClausePosition {
    pub fn new(literal_pos: LiteralPosition, literal_idx: usize) -> Self {
        Self {
            literal_pos,
            literal_idx,
        }
    }
}

impl Position for ClausePosition {
    type T = Clause;

    fn term_at<'a>(&self, t: &'a Self::T) -> &'a Term {
        self.literal_pos.term_at(t.get_literal(self.literal_idx))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClauseSetPosition {
    clause_pos: ClausePosition,
    clause_id: ClauseId,
}

impl ClauseSetPosition {
    pub fn new(clause_pos: ClausePosition, clause_id: ClauseId) -> Self {
        Self {
            clause_pos,
            clause_id,
        }
    }
}

impl Position for ClauseSetPosition {
    type T = ClauseSet;

    fn term_at<'a>(&self, t: &'a Self::T) -> &'a Term {
        let clause = t
            .get_by_id(self.clause_id)
            .expect("Clause id not found in clause set");
        self.clause_pos.term_at(clause)
    }
}
