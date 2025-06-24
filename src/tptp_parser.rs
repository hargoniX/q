use std::collections::HashMap;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use tptp::TPTPIterator;
use tptp::common::NonassocConnective;
use tptp::fof;
use tptp::top::{AnnotatedFormula, FormulaSelection, TPTPInput};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Name {
    Builtin(String),
    Parsed(String),
    Skolem(String),
}

impl Name {
    pub fn get_name(&self) -> &str {
        match self {
            Name::Builtin(name) => name,
            Name::Parsed(name) => name,
            Name::Skolem(name) => name,
        }
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Name::Builtin(name) => write!(f, "${}", name),
            Name::Parsed(name) => write!(f, "P_{}", name),
            Name::Skolem(name) => write!(f, "S_{}", name),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term {
    Variable(Name),
    Function(Name, Vec<Term>),
}

type Substitution<'a> = HashMap<Name, Term>;

impl Term {
    fn substitute(&self, s: &mut Substitution) -> Term {
        match self {
            Term::Variable(name) => {
                if let Some(t2) = s.get(&name) {
                    t2.clone()
                } else {
                    self.clone()
                }
            }
            Term::Function(name, ts) => Term::Function(
                name.clone(),
                ts.into_iter().map(|t| t.substitute(s)).collect(),
            ),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Variable(name) => write!(f, "{}", name),
            Term::Function(name, ts) => write!(
                f,
                "{}({})",
                name,
                ts.into_iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(",")
            ),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Literal {
    Eq(Term, Term),
    NotEq(Term, Term),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Eq(t1, t2) => write!(f, "{} = {}", t1, t2),
            Literal::NotEq(t1, t2) => write!(f, "{} != {}", t1, t2),
        }
    }
}

// We chose to keep the n-ary Quantifiers since they can be handled quite easily when skolemizing,
// but distributing n-ary Operators seems to result in a worse result when computing naively
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum FOLTerm {
    Literal(Literal),
    And(Box<FOLTerm>, Box<FOLTerm>),
    Or(Box<FOLTerm>, Box<FOLTerm>),
    Exist(Vec<Name>, Box<FOLTerm>),
    Forall(Vec<Name>, Box<FOLTerm>),
}

impl fmt::Display for FOLTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FOLTerm::Literal(l) => write!(f, "{}", l),
            FOLTerm::And(t1, t2) => write!(f, "({}&{})", t1, t2),
            FOLTerm::Or(t1, t2) => write!(f, "({}|{})", t1, t2),
            FOLTerm::Exist(vars, ts) => {
                write!(
                    f,
                    "?[{}]:{}",
                    vars.into_iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<String>>()
                        .join(","),
                    ts.to_string()
                )
            }
            FOLTerm::Forall(vars, ts) => {
                write!(
                    f,
                    "![{}]:{}",
                    vars.into_iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<String>>()
                        .join(","),
                    ts.to_string()
                )
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SkolemTerm {
    Literal(Literal),
    And(Box<SkolemTerm>, Box<SkolemTerm>),
    Or(Box<SkolemTerm>, Box<SkolemTerm>),
}

struct SkolemState {
    counter: usize,
}

impl SkolemState {
    pub fn get_fresh_var(&mut self) -> Name {
        self.counter += 1;
        Name::Skolem(self.counter.to_string())
    }
}

// Modelling scopes through a stack:
// the currently active renaming is the last element of the vec
type ScopedRenameMap<'a> = HashMap<Name, Vec<Name>>;

fn rename_term(t: &Term, s: &mut ScopedRenameMap) -> Term {
    match t {
        Term::Variable(name) => {
            if let Some(rename_list) = s.get_mut(name) {
                if let Some(t2) = rename_list.get(rename_list.len() - 1) {
                    return Term::Variable(t2.clone());
                }
            }
            t.clone()
        }
        Term::Function(name, ts) => Term::Function(
            name.clone(),
            ts.into_iter().map(|t| rename_term(t, s)).collect(),
        ),
    }
}

enum Op {
    And,
    Or,
}

enum Binder {
    Forall(Vec<Name>),
    Exist(Vec<Name>),
}

impl FOLTerm {
    // Distribute a negation over the whole term
    fn negate(self) -> FOLTerm {
        match self {
            FOLTerm::Literal(Literal::Eq(t1, t2)) => FOLTerm::Literal(Literal::NotEq(t1, t2)),
            FOLTerm::Literal(Literal::NotEq(t1, t2)) => FOLTerm::Literal(Literal::Eq(t1, t2)),
            FOLTerm::And(t1, t2) => FOLTerm::Or(Box::new(t1.negate()), Box::new(t2.negate())),
            FOLTerm::Or(t1, t2) => FOLTerm::And(Box::new(t1.negate()), Box::new(t2.negate())),
            FOLTerm::Exist(n, t) => FOLTerm::Forall(n, Box::new(t.negate())),
            FOLTerm::Forall(n, t) => FOLTerm::Exist(n, t),
        }
    }

    // There is a caveat to using a single mutable subst in that we need to know the previous
    // value of the mapping and restore it after the binder gets out of scope.
    // Example:
    //      ∀x.(∀x.p(x)) ∧ p(x)
    // should result in
    //      ∀1.(∀2.p(2)) ∧ p(1)
    fn rename_quantifier(
        binder_names: Vec<Name>,
        term: Box<FOLTerm>,
        state: &mut SkolemState,
        sub: &mut ScopedRenameMap,
    ) -> (Vec<Name>, Box<FOLTerm>) {
        let mut new_binder_names = Vec::new();
        for name in binder_names.clone() {
            let fresh_var = state.get_fresh_var();
            new_binder_names.push(fresh_var.clone());
            log::debug!("Renaming {} to {}", name, fresh_var);

            if let Some(binders) = sub.get_mut(&name) {
                binders.push(fresh_var);
            } else {
                sub.insert(name, vec![fresh_var]);
            }
        }
        let renamed_fol_term = term.rename_quants(state, sub);
        // Pop the changes after leaving the scope
        for name in binder_names {
            sub.get_mut(&name).unwrap().pop();
        }
        (new_binder_names, Box::new(renamed_fol_term))
    }

    fn rename_quants(self, state: &mut SkolemState, sub: &mut ScopedRenameMap) -> FOLTerm {
        match self {
            FOLTerm::Literal(Literal::Eq(t1, t2)) => {
                FOLTerm::Literal(Literal::Eq(rename_term(&t1, sub), rename_term(&t2, sub)))
            }
            FOLTerm::Literal(Literal::NotEq(t1, t2)) => {
                FOLTerm::Literal(Literal::NotEq(rename_term(&t1, sub), rename_term(&t2, sub)))
            }
            FOLTerm::And(t1, t2) => FOLTerm::And(
                Box::new(t1.rename_quants(state, sub)),
                Box::new(t2.rename_quants(state, sub)),
            ),
            FOLTerm::Or(t1, t2) => FOLTerm::Or(
                Box::new(t1.rename_quants(state, sub)),
                Box::new(t2.rename_quants(state, sub)),
            ),
            FOLTerm::Exist(n, t) => {
                let (new_binder_names, renamed_fol_term) =
                    FOLTerm::rename_quantifier(n, t, state, sub);
                FOLTerm::Exist(new_binder_names, renamed_fol_term)
            }
            FOLTerm::Forall(n, t) => {
                let (new_binder_names, renamed_fol_term) =
                    FOLTerm::rename_quantifier(n, t, state, sub);
                FOLTerm::Forall(new_binder_names, renamed_fol_term)
            }
        }
    }

    // Cuts away quantifiers recursively and pushes them into the vec
    // until there is another type of term
    fn separate_binders(self, quants: &mut Vec<Binder>) -> FOLTerm {
        match self {
            FOLTerm::And(t1, t2) => FOLTerm::And(
                Box::new(t1.separate_binders(quants)),
                Box::new(t2.separate_binders(quants)),
            ),
            FOLTerm::Or(t1, t2) => FOLTerm::Or(
                Box::new(t1.separate_binders(quants)),
                Box::new(t2.separate_binders(quants)),
            ),
            FOLTerm::Exist(n, t) => {
                quants.push(Binder::Exist(n));
                t.separate_binders(quants)
            }
            FOLTerm::Forall(n, t) => {
                quants.push(Binder::Forall(n));
                t.separate_binders(quants)
            }
            _ => self,
        }
    }

    // The order of the pulled up quantifiers is important for Skolemnization.
    // TODO: If there are multiple equisatisfiable versions, picking Exist first is preferable.
    // It will result in Skolem Functions with less arguments.
    fn pull_quants(self) -> FOLTerm {
        let mut quants = Vec::new();
        let mut result = self.separate_binders(&mut quants);

        // Reverse the order of the quantifiers to build the terms more easily
        quants.reverse();
        for quant in quants {
            match quant {
                Binder::Exist(names) => {
                    result = FOLTerm::Exist(names, Box::new(result));
                }
                Binder::Forall(names) => {
                    result = FOLTerm::Forall(names, Box::new(result));
                }
            }
        }
        result
    }

    // Prenex Normal Form
    //
    // The following equivalence/possible transformation is not valid:
    //     P(x) ∧ (∃x. Q(x)) ⇔ ∃x. P(x) ∧ Q(x).
    // We can always avoid such problems by renaming the bound variable, if
    // necessary, to some y that is not free in either p or q:
    //     p ∧ (∃x. q) ⇔ ∃y. p ∧ (subst (x |⇒ y) q).
    //
    // This is done as naively as possible:
    // 1. Renaming all the quantifier variables to fresh Skolem Ones
    //    If there are multiple quantifiers over the same Variable, e.g.
    //      ∀x.∀x.p(x)
    //    then we would expect the result to be
    //      ∀1.∀2.p(2)
    //    where the substitution gets overwritten by the second occurence of x
    // 2. Pulling up the quantifiers
    fn pnf(self, state: &mut SkolemState) -> FOLTerm {
        let renamed_term = self.rename_quants(state, &mut ScopedRenameMap::new());
        log::debug!("Renamed Binders: {}", renamed_term);
        renamed_term.pull_quants()
    }

    // TODO: I think it is fine to remove forall on the traversal already?
    // this should probably take a &mut subst and subst on the traversal with the skolemized
    // function symbol
    fn skolemize(self, s: &mut Substitution, binders: &mut Vec<Name>) -> SkolemTerm {
        match self {
            FOLTerm::Literal(t) => match t {
                Literal::Eq(t1, t2) => {
                    SkolemTerm::Literal(Literal::Eq(t1.substitute(s), t2.substitute(s)))
                }
                Literal::NotEq(t1, t2) => {
                    SkolemTerm::Literal(Literal::NotEq(t1.substitute(s), t2.substitute(s)))
                }
            },
            FOLTerm::And(t1, t2) => SkolemTerm::And(
                Box::new(t1.skolemize(s, binders)),
                Box::new(t2.skolemize(s, binders)),
            ),
            FOLTerm::Or(t1, t2) => SkolemTerm::Or(
                Box::new(t1.skolemize(s, binders)),
                Box::new(t2.skolemize(s, binders)),
            ),
            // Due to the pulling out of the quantifiers, the scopes become linear and
            // thus we can just append to the state of binder variables
            FOLTerm::Forall(names, t) => {
                for name in names {
                    binders.push(name);
                }
                t.skolemize(s, binders)
            }
            FOLTerm::Exist(names, t) => {
                // It is fine for the function to keep its variable name
                // since it's unique after renaming
                for name in names {
                    s.insert(
                        name.clone(),
                        Term::Function(
                            name.clone(),
                            binders
                                .into_iter()
                                .map(|n| Term::Variable(n.clone()))
                                .collect(),
                        ),
                    );
                }
                t.skolemize(s, binders)
            }
        }
    }
}

// This function gets rid of all the quantifiers:
// - pull the quantifiers outside (Prenex Normal Form).
//   We first rename ALL of the binder variables to get out of the edge cases
// - replace Existential with a Skolem function symbol
// - remove the Forall Quantifiers
//
// It is more complex since our Quantifiers are n-ary.
// Since this is supposed to just naively parse the problem at the current time,
// there are no optimizations like removing quantifiers
// which variables don't occur in the formula
impl From<FOLTerm> for SkolemTerm {
    fn from(f: FOLTerm) -> Self {
        let mut state = SkolemState { counter: 0 };
        let pnf_term = f.pnf(&mut state);
        log::info!("PNF Term: {}", pnf_term);
        pnf_term.skolemize(&mut Substitution::new(), &mut Vec::new())
    }
}

impl fmt::Display for SkolemTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SkolemTerm::Literal(l) => write!(f, "{}", l),
            SkolemTerm::And(t1, t2) => write!(f, "({}&{})", t1, t2),
            SkolemTerm::Or(t1, t2) => write!(f, "({}|{})", t1, t2),
        }
    }
}

// This function requires the subterms of the `Or` to already be in CNF
// and just recursively pushes possibly multiple `And`s inwards
fn push_or_inwards(t: SkolemTerm) -> SkolemTerm {
    match t {
        SkolemTerm::Or(s, t) => match (*s, *t) {
            (SkolemTerm::And(s1, s2), t) => {
                let cnf_s = push_or_inwards(SkolemTerm::Or(s1, Box::new(t.clone())));
                let cnf_t = push_or_inwards(SkolemTerm::Or(s2, Box::new(t)));
                SkolemTerm::And(Box::new(cnf_s), Box::new(cnf_t))
            }
            (s, SkolemTerm::And(t1, t2)) => {
                let cnf_s = push_or_inwards(SkolemTerm::Or(Box::new(s.clone()), t1));
                let cnf_t = push_or_inwards(SkolemTerm::Or(Box::new(s), t2));
                SkolemTerm::And(Box::new(cnf_s), Box::new(cnf_t))
            }
            (s, t) => SkolemTerm::Or(Box::new(s), Box::new(t)),
        },
        _ => t,
    }
}

// Distribute Or inwards over And naively:
//      Or(s, Or(t, And(v, And(u, w))))
//   Should result in the following steps
// ->   Or(s, And(Or(t,v), Or(t, And(u,w))))
// ->   Or(s, And(Or(t,v), And(Or(t,u), Or(t,w))))
// ->   And(Or(s, Or(t,v)), Or(s, And(Or(t,u), Or(t,w))))
// ->   And(Or(s, Or(t,v)), And(Or(s, Or(t,u)), Or(s, Or(t,w))))
fn cnf(f: SkolemTerm) -> SkolemTerm {
    match f {
        SkolemTerm::And(s, t) => SkolemTerm::And(Box::new(cnf(*s)), Box::new(cnf(*t))),
        SkolemTerm::Or(s, t) => {
            let cnf_s = cnf(*s);
            let cnf_t = cnf(*t);
            match (cnf_s, cnf_t) {
                (SkolemTerm::And(s1, s2), t) => {
                    let cnf_s = push_or_inwards(SkolemTerm::Or(s1, Box::new(t.clone())));
                    let cnf_t = push_or_inwards(SkolemTerm::Or(s2, Box::new(t)));
                    SkolemTerm::And(Box::new(cnf_s), Box::new(cnf_t))
                }
                (s, SkolemTerm::And(t1, t2)) => {
                    let cnf_s = push_or_inwards(SkolemTerm::Or(Box::new(s.clone()), t1));
                    let cnf_t = push_or_inwards(SkolemTerm::Or(Box::new(s), t2));
                    SkolemTerm::And(Box::new(cnf_s), Box::new(cnf_t))
                }
                (s, t) => SkolemTerm::Or(Box::new(s), Box::new(t)),
            }
        }
        _ => f,
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TPTPProblem {
    pub axioms: Vec<FOLTerm>,
    pub conjectures: Vec<FOLTerm>,
}

// Parse into structure consisting of two lists: one with assumptions, one with goals (still FoF)
// FIXME: we don't have any sanity checks for include stuff with conflicting names
pub fn parse_file<'a>(file: PathBuf) -> TPTPProblem {
    log::info!("Opening {:?}", file);
    let mut f = File::open(&file).expect("Unable to open file");
    let mut vec = Vec::new();
    f.read_to_end(&mut vec).expect("Unable to read file");
    let mut parser = TPTPIterator::<()>::new(&vec);
    let mut axioms = Vec::new();
    let mut conjectures = Vec::new();
    for result in &mut parser {
        let input = result.expect("Syntax error");
        match input {
            TPTPInput::Include(include) => {
                let include_file = include.file_name;
                if let FormulaSelection(Some(a)) = include.selection {
                    log::error!("Selection: '{}'", a);
                    assert!(false, "Parsing doesn't handle a selection of input yet!");
                }
                let mut include_path = file.clone();
                assert!(
                    include_path.pop(),
                    "Couldn't fetch the directory of the tptp input: '{:?}'",
                    file
                );
                // The path is singlely-quoted, which does make this funny.
                // But who would put single quotes in their filenames right.. right
                let problem_path = include_file.0.to_string().replace("'", "");
                include_path.push(problem_path);
                log::info!("Include {:?}", include_path);

                let mut tptp_problem = parse_file(include_path);
                axioms.append(&mut tptp_problem.axioms);
                conjectures.append(&mut tptp_problem.conjectures);
            }
            TPTPInput::Annotated(annotated_formula) => {
                match *annotated_formula {
                    AnnotatedFormula::Fof(fof) => {
                        // We disregard any names of the formula or special annotations
                        let annotated_fof = (*fof).0;
                        // This will be a very naive way to interpret TPTP,
                        // where every role but conjectures will be handled like an axiom
                        // <https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html#formula_role>
                        // > "assumption"s can be used like axioms, but must be discharged before a derivation is complete.
                        let role = annotated_fof.role.0.0;
                        // > "negated_conjecture"s are formed from negation of a "conjecture"
                        // > (usually in a FOF to CNF conversion).
                        // This should always be empty for our use-case but let's keep it just in case for now.
                        assert!(
                            role != "negated_conjecture",
                            "The 'negated_conjecture'-role doesn't seem to be intended for this provers use-case."
                        );
                        let formula = *annotated_fof.formula;
                        log::info!("Parse FOF: {}", formula);
                        let fol_term = FOLTerm::from(formula.0);
                        log::info!("Parsed FOLTerm: {}", fol_term);
                        if role == "conjecture" {
                            conjectures.push(fol_term);
                        } else {
                            axioms.push(fol_term);
                        }
                    }
                    AnnotatedFormula::Tfx(_) => assert!(false, "Parsing doesn't handle Tfx!"),
                    AnnotatedFormula::Cnf(_) => assert!(false, "Parsing doesn't handle Cnf!"),
                }
            }
        }
    }
    assert!(
        parser.remaining.is_empty(),
        "Parser wasn't finished somehow!"
    );
    TPTPProblem {
        axioms: axioms,
        conjectures: conjectures,
    }
}

// Transform the TPTPProblem into the problem in CNF for our saturation prover:
// - we conjunct the assumption formulas
// - we conject those with the negated goals
// - we transform it into CNF
// - we show False
pub fn transform_problem(problem: TPTPProblem) -> SkolemTerm {
    let mut acc;
    if problem.conjectures.len() != 0 {
        let neg_goals: Vec<FOLTerm> = problem
            .conjectures
            .into_iter()
            .map(FOLTerm::negate)
            .collect();
        log::info!("Neg. Goals: {:?}", neg_goals);
        acc = FOLTerm::from(neg_goals[0].clone());
        for t in neg_goals[1..].into_iter() {
            acc = FOLTerm::And(Box::new(acc), Box::new(t.clone()));
        }
        for t in problem.axioms {
            acc = FOLTerm::And(Box::new(acc), Box::new(t.clone()));
        }
    } else {
        log::warn!("No Goals!");
        acc = FOLTerm::from(problem.axioms[0].clone());
        for t in problem.axioms[1..].into_iter() {
            acc = FOLTerm::And(Box::new(acc), Box::new(t.clone()));
        }
    }
    let skolem_term = SkolemTerm::from(acc);
    log::info!("SkolemTerm: {}", skolem_term);
    let cnf_term = cnf(skolem_term.clone());
    log::info!("CNF Term: {}", skolem_term);
    cnf_term
}

// This function has to:
// - convert Implications/Equivalences
// - get rid of the unary operator 'neg' on formulas
impl From<fof::LogicFormula<'_>> for FOLTerm {
    fn from(f: fof::LogicFormula) -> Self {
        match f {
            fof::LogicFormula::Binary(b) => Self::from(b),
            fof::LogicFormula::Unary(u) => Self::from(u),
            fof::LogicFormula::Unitary(u) => Self::from(u),
        }
    }
}

impl From<fof::BinaryFormula<'_>> for FOLTerm {
    fn from(f: fof::BinaryFormula) -> Self {
        match f {
            fof::BinaryFormula::Nonassoc(fbna) => Self::from(fbna),
            fof::BinaryFormula::Assoc(fba) => Self::from(fba),
        }
    }
}

impl From<fof::UnaryFormula<'_>> for FOLTerm {
    fn from(f: fof::UnaryFormula) -> Self {
        match f {
            fof::UnaryFormula::Unary(_neg, fuf) => Self::from(*fuf).negate(),
            fof::UnaryFormula::InfixUnary(i) => Self::from(i),
        }
    }
}

impl From<fof::UnitaryFormula<'_>> for FOLTerm {
    fn from(f: fof::UnitaryFormula) -> Self {
        match f {
            fof::UnitaryFormula::Parenthesised(flf) => Self::from(*flf),
            fof::UnitaryFormula::Quantified(fqf) => Self::from(fqf),
            fof::UnitaryFormula::Atomic(a) => Self::from(*a),
        }
    }
}

impl From<fof::BinaryNonassoc<'_>> for FOLTerm {
    fn from(f: fof::BinaryNonassoc) -> Self {
        let l = Self::from(*f.left);
        let r = Self::from(*f.right);
        match f.op {
            NonassocConnective::LRImplies => Self::Or(Box::new(l.negate()), Box::new(r)),
            NonassocConnective::RLImplies => Self::Or(Box::new(r.negate()), Box::new(l)),
            NonassocConnective::Equivalent => Self::And(
                Box::new(Self::Or(Box::new(l.clone().negate()), Box::new(r.clone()))),
                Box::new(Self::Or(Box::new(r.negate()), Box::new(l))),
            ),
            NonassocConnective::NotEquivalent => Self::Or(
                Box::new(Self::And(Box::new(l.clone()), Box::new(r.clone().negate()))),
                Box::new(Self::And(Box::new(r), Box::new(l.negate()))),
            ),
            NonassocConnective::NotOr => Self::And(Box::new(l.negate()), Box::new(r.negate())),
            NonassocConnective::NotAnd => Self::Or(Box::new(l.negate()), Box::new(r.negate())),
        }
    }
}

// The BNF makes sure that there are atleast two elems in the initial vec
// the formula vectors `f_or`|`f_and`
fn convert_op_into_binary(fs: &[fof::UnitFormula<'_>], op: &Op) -> FOLTerm {
    let mut acc = FOLTerm::from(fs[0].clone());
    let op_fn = match op {
        Op::And => FOLTerm::And,
        Op::Or => FOLTerm::Or,
    };
    for f in fs[1..].into_iter() {
        let t = FOLTerm::from(f.clone());
        acc = op_fn(Box::new(acc), Box::new(t));
    }
    acc
}

impl From<fof::BinaryAssoc<'_>> for FOLTerm {
    fn from(f: fof::BinaryAssoc) -> Self {
        match f {
            fof::BinaryAssoc::And(f_and) => convert_op_into_binary(&f_and.0[..], &Op::And),
            fof::BinaryAssoc::Or(f_or) => convert_op_into_binary(&f_or.0[..], &Op::Or),
        }
    }
}

impl From<fof::UnitFormula<'_>> for FOLTerm {
    fn from(f: fof::UnitFormula) -> Self {
        match f {
            fof::UnitFormula::Unitary(u) => Self::from(u),
            fof::UnitFormula::Unary(u) => Self::from(u),
        }
    }
}

impl From<fof::InfixUnary<'_>> for FOLTerm {
    fn from(f: fof::InfixUnary) -> Self {
        Self::Literal(Literal::NotEq(Term::from(*f.left), Term::from(*f.right)))
    }
}

impl From<fof::Term<'_>> for Term {
    fn from(t: fof::Term) -> Self {
        match t {
            fof::Term::Variable(v) => Self::Variable(Name::Parsed(v.to_string())),
            fof::Term::Function(f) => Self::from(*f),
        }
    }
}

//%----System terms have system specific interpretations
//%----<fof_system_atomic_formula>s are used for evaluable predicates that are
//%----available in particular tools. The predicate names are not controlled by
//%----the TPTP syntax, so use with due care. Same for <fof_system_term>s.
// FIXME: unclear if we want to support System Terms and what would be the correct interpretation
impl From<fof::FunctionTerm<'_>> for Term {
    fn from(t: fof::FunctionTerm) -> Self {
        match t {
            fof::FunctionTerm::Plain(p) => Self::from(p),
            fof::FunctionTerm::Defined(d) => Self::from(d),
            fof::FunctionTerm::System(_) => unimplemented!(),
        }
    }
}

impl From<fof::PlainTerm<'_>> for Term {
    fn from(t: fof::PlainTerm) -> Self {
        match t {
            fof::PlainTerm::Constant(c) => Self::Function(Name::Parsed(c.to_string()), Vec::new()),
            fof::PlainTerm::Function(f, args) => Self::Function(
                Name::Parsed(f.to_string()),
                args.0.into_iter().map(Self::from).collect(),
            ),
        }
    }
}

//%----Defined terms have TPTP specific interpretations
impl From<fof::DefinedTerm<'_>> for Term {
    fn from(t: fof::DefinedTerm) -> Self {
        match t {
            fof::DefinedTerm::Defined(d) => Self::from(d),
            fof::DefinedTerm::Atomic(_) => todo!(),
        }
    }
}

//%----Defined terms have TPTP specific interpretations"
//%----<distinct_object>s are different from (but may be equal to) other tokens,
//%----e.g., "cat" is different from 'cat' and cat. Distinct objects are always interpreted as
//%----themselves, so if they are different they are unequal, e.g., "Apple" != "Microsoft" is %----implicit.
// FIXME: unclear if we even want to support those and if this is the right interpretation
impl From<tptp::common::DefinedTerm<'_>> for Term {
    fn from(t: tptp::common::DefinedTerm) -> Self {
        match t {
            tptp::common::DefinedTerm::Number(n) => {
                Self::Function(Name::Parsed(n.to_string()), Vec::new())
            }
            // These are double-quoted tokens.
            tptp::common::DefinedTerm::Distinct(n) => {
                Self::Function(Name::Parsed(n.to_string()), Vec::new())
            }
        }
    }
}

impl From<fof::QuantifiedFormula<'_>> for FOLTerm {
    fn from(f: fof::QuantifiedFormula) -> Self {
        match f.quantifier {
            // FIXME: the reference implementation reversed the order, but I dont understand why
            fof::Quantifier::Forall => {
                let vars = f
                    .bound
                    .0
                    .iter()
                    .map(|v| Name::Parsed(v.to_string()))
                    .collect();
                Self::Forall(vars, Box::new(Self::from(*f.formula)))
            }
            fof::Quantifier::Exists => {
                let vars = f
                    .bound
                    .0
                    .iter()
                    .map(|v| Name::Parsed(v.to_string()))
                    .collect();
                Self::Exist(vars, Box::new(Self::from(*f.formula)))
            }
        }
    }
}

impl From<fof::DefinedAtomicFormula<'_>> for FOLTerm {
    fn from(f: fof::DefinedAtomicFormula) -> Self {
        match f {
            fof::DefinedAtomicFormula::Plain(p) => Self::from(p),
            fof::DefinedAtomicFormula::Infix(i) => {
                Self::Literal(Literal::Eq(Term::from(*i.left), Term::from(*i.right)))
            }
        }
    }
}

// `defined_proposition` aka `$true | $false` only occurs in `fof_defined_plain_formula`
// Thus there are no other ways to create the builtin truth values
// We refrain from integrating $false into our model because we would then
// also need to automaticly include some term `$true != $false`
impl From<fof::DefinedPlainFormula<'_>> for FOLTerm {
    fn from(f: fof::DefinedPlainFormula) -> Self {
        match f.0 {
            fof::DefinedPlainTerm::Constant(c) if c.0.0.0.0.0 == "true" => {
                FOLTerm::Literal(Literal::Eq(
                    Term::Function(Name::Builtin(String::from("true")), Vec::new()),
                    Term::Function(Name::Builtin(String::from("true")), Vec::new()),
                ))
            }
            fof::DefinedPlainTerm::Constant(c) if c.0.0.0.0.0 == "false" => {
                FOLTerm::Literal(Literal::NotEq(
                    Term::Function(Name::Builtin(String::from("true")), Vec::new()),
                    Term::Function(Name::Builtin(String::from("true")), Vec::new()),
                ))
            }
            _ => unimplemented!("No other theory is implemented"),
        }
    }
}

impl From<fof::AtomicFormula<'_>> for FOLTerm {
    fn from(f: fof::AtomicFormula) -> Self {
        match f {
            fof::AtomicFormula::Plain(p) => Self::from(p),
            fof::AtomicFormula::Defined(d) => Self::from(d),
            fof::AtomicFormula::System(_) => todo!(),
        }
    }
}

impl From<fof::PlainAtomicFormula<'_>> for FOLTerm {
    fn from(f: fof::PlainAtomicFormula) -> Self {
        match f.0 {
            fof::PlainTerm::Constant(c) => FOLTerm::Literal(Literal::Eq(
                Term::Function(Name::Parsed(c.to_string()), Vec::new()),
                Term::Function(Name::Builtin(String::from("true")), Vec::new()),
            )),
            fof::PlainTerm::Function(f, args) => FOLTerm::Literal(Literal::Eq(
                Term::Function(
                    Name::Parsed(f.to_string()),
                    args.0.into_iter().map(Term::from).collect(),
                ),
                Term::Function(Name::Builtin(String::from("true")), Vec::new()),
            )),
        }
    }
}
