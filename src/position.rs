use crate::{
    clause::{Clause, ClauseId, ClauseSet, Literal, LiteralId},
    term_bank::{RawTerm, Term, TermBank},
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

    fn replace_term_at_aux(
        &self,
        term: &Term,
        new_term: Term,
        term_bank: &TermBank,
        idx: usize,
    ) -> Term {
        debug_assert!(idx <= self.path.len());
        if idx == self.path.len() {
            new_term
        } else {
            let arg_idx = self.path[idx];
            let mut args = term.function_args().unwrap().clone();
            let new = self.replace_term_at_aux(&args[arg_idx], new_term, term_bank, idx + 1);
            args[arg_idx] = new;
            term_bank.mk_app(term.function_id().unwrap(), args)
        }
    }

    pub fn replace_term_at(&self, term: &Term, new_term: Term, term_bank: &TermBank) -> Term {
        self.replace_term_at_aux(term, new_term, term_bank, 0)
    }

    pub fn is_root(&self) -> bool {
        self.path.is_empty()
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

pub struct TermPositionIterator<'a> {
    front: Vec<(&'a Term, TermPosition)>,
}

impl<'a> TermPositionIterator<'a> {
    fn new(term: &'a Term) -> Self {
        Self {
            front: vec![(term, TermPosition::new())],
        }
    }
}

impl Term {
    pub fn subterm_iter(&self) -> TermPositionIterator<'_> {
        TermPositionIterator::new(self)
    }
}

impl Iterator for TermPositionIterator<'_> {
    type Item = (Term, TermPosition);

    fn next(&mut self) -> Option<Self::Item> {
        let (curr_term, curr_pos) = self.front.pop()?;

        if let Some(args) = curr_term.function_args() {
            for (idx, arg) in args.iter().enumerate() {
                let mut new_pos = curr_pos.clone();
                new_pos.add(idx);
                self.front.push((arg, new_pos));
            }
        }

        Some((curr_term.clone(), curr_pos))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LiteralSide {
    Left,
    Right,
}

impl LiteralSide {
    pub fn get_side<'a>(&self, literal: &'a Literal) -> &'a Term {
        match self {
            LiteralSide::Left => literal.get_lhs(),
            LiteralSide::Right => literal.get_rhs(),
        }
    }

    pub fn swap(&self) -> Self {
        match self {
            LiteralSide::Left => LiteralSide::Right,
            LiteralSide::Right => LiteralSide::Left,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiteralPosition {
    pub term_pos: TermPosition,
    pub literal_side: LiteralSide,
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
    pub literal_pos: LiteralPosition,
    pub literal_id: LiteralId,
}

impl ClausePosition {
    pub fn new(literal_pos: LiteralPosition, literal_id: LiteralId) -> Self {
        Self {
            literal_pos,
            literal_id,
        }
    }
}

impl Position for ClausePosition {
    type T = Clause;

    fn term_at<'a>(&self, t: &'a Self::T) -> &'a Term {
        self.literal_pos.term_at(t.get_literal(self.literal_id))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClauseSetPosition {
    pub clause_pos: ClausePosition,
    pub clause_id: ClauseId,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClauseSetLiteralPosition {
    pub literal_side: LiteralSide,
    pub literal_id: LiteralId,
    pub clause_id: ClauseId,
}

impl ClauseSetLiteralPosition {
    pub fn new(clause_id: ClauseId, literal_id: LiteralId, literal_side: LiteralSide) -> Self {
        Self {
            literal_side,
            literal_id,
            clause_id,
        }
    }
}

impl Position for ClauseSetLiteralPosition {
    type T = ClauseSet;

    fn term_at<'a>(&self, t: &'a Self::T) -> &'a Term {
        let clause = t
            .get_by_id(self.clause_id)
            .expect("Clause id not found in clause set");
        let literal = clause.get_literal(self.literal_id);
        self.literal_side.get_side(literal)
    }
}
