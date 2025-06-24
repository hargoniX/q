use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use tptp::TPTPIterator;
use tptp::common::NonassocConnective;
use tptp::fof;
use tptp::top::{AnnotatedFormula, FormulaSelection, TPTPInput};

// These will be converted to an actual problem in CNF form to be proven by saturation:
// - we conjunct the assumption formulas
// - we conject those with the negated goals
// - we show False
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TPTPProblem {
    pub axioms: Vec<FOLTerm>,
    pub conjectures: Vec<FOLTerm>,
    // > "negated_conjecture"s are formed from negation of a "conjecture"
    // > (usually in a FOF to CNF conversion).
    // This should always be empty for our use-case but let's keep it just in case for now.
    pub negated_conjectures: Vec<FOLTerm>,
}

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

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum FOLTerm {
    Literal(Literal),
    And(Vec<FOLTerm>),
    Or(Vec<FOLTerm>),
    Exist(Vec<Name>, Box<FOLTerm>),
    Forall(Vec<Name>, Box<FOLTerm>),
}

impl fmt::Display for FOLTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FOLTerm::Literal(l) => write!(f, "{}", l),
            FOLTerm::And(ts) => write!(
                f,
                "({})",
                ts.into_iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join("&")
            ),
            FOLTerm::Or(ts) => write!(
                f,
                "({})",
                ts.into_iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join("|")
            ),
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

// Distribute a negation over the whole term
fn negate(fol: FOLTerm) -> FOLTerm {
    match fol {
        FOLTerm::Literal(Literal::Eq(t1, t2)) => FOLTerm::Literal(Literal::NotEq(t1, t2)),
        FOLTerm::Literal(Literal::NotEq(t1, t2)) => FOLTerm::Literal(Literal::Eq(t1, t2)),
        FOLTerm::And(ts) => FOLTerm::Or(ts.into_iter().map(negate).collect()),
        FOLTerm::Or(ts) => FOLTerm::And(ts.into_iter().map(negate).collect()),
        FOLTerm::Exist(n, t) => FOLTerm::Forall(n, Box::new(negate(*t))),
        FOLTerm::Forall(n, t) => FOLTerm::Forall(n, t),
    }
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
    let mut negated_conjectures = Vec::new();
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
                negated_conjectures.append(&mut tptp_problem.negated_conjectures);
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
                        let formula = *annotated_fof.formula;
                        log::info!("Parse FOF: {}", formula);
                        let fol_term = FOLTerm::from(formula.0);
                        log::info!("Parsed FOLTerm: {}", fol_term);
                        if role == "conjecture" {
                            conjectures.push(fol_term);
                        } else if role == "negated_conjecture" {
                            negated_conjectures.push(fol_term);
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
        negated_conjectures: negated_conjectures,
    }
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
            fof::UnaryFormula::Unary(_neg, fuf) => negate(Self::from(*fuf)),
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
            NonassocConnective::LRImplies => Self::Or(vec![negate(l), r]),
            NonassocConnective::RLImplies => Self::Or(vec![negate(r), l]),
            NonassocConnective::Equivalent => Self::And(vec![
                Self::Or(vec![negate(l.clone()), r.clone()]),
                Self::Or(vec![negate(r), l]),
            ]),
            NonassocConnective::NotEquivalent => Self::Or(vec![
                Self::And(vec![l.clone(), negate(r.clone())]),
                Self::And(vec![r, negate(l)]),
            ]),
            NonassocConnective::NotOr => Self::And(vec![negate(l), negate(r)]),
            NonassocConnective::NotAnd => Self::And(vec![negate(l), negate(r)]),
        }
    }
}

impl From<fof::BinaryAssoc<'_>> for FOLTerm {
    fn from(f: fof::BinaryAssoc) -> Self {
        match f {
            fof::BinaryAssoc::Or(f_or) => Self::Or(f_or.0.into_iter().map(Self::from).collect()),
            fof::BinaryAssoc::And(f_and) => {
                Self::And(f_and.0.into_iter().map(Self::from).collect())
            }
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
