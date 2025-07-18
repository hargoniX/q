use std::{cell::RefCell, collections::BTreeMap, fmt::Display};

use crate::{
    clause::{Clause, ClauseId},
    pretty_print::pretty_print,
    term_bank::TermBank,
};

use rustc_hash::FxHashSet;

/// What kind of graph to print
#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum GraphvizMode {
    /// All clauses leading to the last generated one.
    Last,
    /// All clauses
    All,
}

#[derive(Debug, Clone, Copy)]
pub enum ProofRule {
    EqualityResolution,
    EqualityFactoring,
    Superposition,
    Rewriting,
    DRDD,
    Original,
    Renaming,
    Sorting,
}

impl ProofRule {
    fn as_str(&self) -> &'static str {
        match self {
            ProofRule::EqualityResolution => "eqres",
            ProofRule::EqualityFactoring => "eqfact",
            ProofRule::Superposition => "superpos",
            ProofRule::Rewriting => "rw",
            ProofRule::DRDD => "drdd",
            ProofRule::Original => "orig",
            ProofRule::Renaming => "rename",
            ProofRule::Sorting => "sort",
        }
    }
}

impl Display for ProofRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone)]
struct ProofStep {
    id: ClauseId,
    new_clause_str: String,
    rule: ProofRule,
    participating: Vec<ClauseId>,
}

impl ProofStep {
    fn to_graphiz(&self, buf: &mut String) {
        let description = format!("{}\\ninference: {} ({})", self.new_clause_str, self.rule, self.id.0);
        buf.push_str(&format!(
            "{:?} [shape=box,label=\"{}\"]\n",
            self.id.0, &description
        ));
        for participant in self.participating.iter() {
            buf.push_str(&format!("{:?} -> {:?}\n", participant.0, self.id.0));
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProofLog {
    graph: RefCell<BTreeMap<ClauseId, ProofStep>>,
    active: bool,
}

impl ProofLog {
    pub fn new(active: bool) -> ProofLog {
        ProofLog {
            graph: RefCell::new(BTreeMap::default()),
            active,
        }
    }

    pub fn log_clause(
        &self,
        new_clause: &Clause,
        rule: ProofRule,
        participating: &[ClauseId],
        term_bank: &TermBank,
    ) {
        if self.active {
            let new_clause_str = pretty_print(new_clause, term_bank);
            debug_assert!(!self.graph.borrow().contains_key(&new_clause.get_id()));
            debug_assert!(
                participating
                    .iter()
                    .all(|c| self.graph.borrow().contains_key(c))
            );
            self.graph.borrow_mut().insert(
                new_clause.get_id(),
                ProofStep {
                    id: new_clause.get_id(),
                    new_clause_str,
                    rule,
                    participating: participating.to_owned(),
                },
            );
        }
    }

    fn to_graphviz_prefix(&self, buf: &mut String) {
        buf.push_str("digraph proof {\n");
        buf.push_str("rankdir = TB\n");
        buf.push_str("graph [splines=true overlap=false];\n");
    }

    fn to_graphviz_all(&self) -> String {
        let mut buf = String::new();
        self.to_graphviz_prefix(&mut buf);
        let graph = self.graph.borrow();
        for (_, step) in graph.iter() {
            step.to_graphiz(&mut buf);
        }

        buf.push('}');

        buf
    }

    fn to_graphiz_last(&self) -> String {
        let mut buf = String::new();
        self.to_graphviz_prefix(&mut buf);
        let graph = self.graph.borrow();
        let mut visited = FxHashSet::default();
        let mut worklist = vec![*graph.last_key_value().unwrap().0];
        while let Some(id) = worklist.pop() {
            if visited.contains(&id) {
                continue;
            }
            let step = graph.get(&id).unwrap();
            step.to_graphiz(&mut buf);
            visited.insert(id);
            step.participating
                .iter()
                .filter(|id| !visited.contains(*id))
                .for_each(|id| worklist.push(*id));
        }

        buf.push('}');

        buf
    }

    pub fn to_graphviz(&self, mode: GraphvizMode) -> String {
        match mode {
            GraphvizMode::Last => self.to_graphiz_last(),
            GraphvizMode::All => self.to_graphviz_all(),
        }
    }
}
