use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use tptp::TPTPIterator;
use tptp::top::{AnnotatedFormula, FormulaSelection, TPTPInput};

struct TPTPProblem<'a> {
    assumptions: Vec<tptp::fof::LogicFormula<'a>>,
    goals: Vec<tptp::fof::LogicFormula<'a>>,
}

// parse into structure consisting of two lists: one with assumptions, one with goals (still FoF)
// then combine these into a big conjunction with the correct negations
// Include make it such that it is actually unique?
pub fn parse_file<'a>(file: PathBuf) -> TPTPProblem<'a> {
    log::info!("Opening '{:?}'", file);
    let mut f = File::open(&file).expect("Unable to open file");
    let mut vec = Vec::new();
    f.read_to_end(&mut vec).expect("Unable to read file");
    let mut parser = TPTPIterator::<()>::new(&vec);
    let mut assumptions = Vec::new();
    let mut goals = Vec::new();
    for result in &mut parser {
        let input = result.expect("Syntax error");
        match input {
            TPTPInput::Include(include) => {
                let include_file = include.file_name;
                if let FormulaSelection(Some(a)) = include.selection {
                    log::error!("Selection: '{}'", a);
                    assert!(false, "Parsing doesn't handle a selection of input yet!");
                }
                log::info!("Include '{}'", include_file);
                let mut include_path = file.clone();
                assert!(
                    include_path.pop(),
                    "Couldn't fetch the directory of the tptp input: '{:?}'",
                    file
                );
                include_path.push(include_file.to_string());
                let mut tptp_problem = parse_file(include_path);
                assumptions.append(&mut tptp_problem.assumptions);
                goals.append(&mut tptp_problem.goals);
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
                        if role == "conjecture" {
                            goals.push(formula.0.to_owned());
                        } else {
                            assumptions.push(formula.0.to_owned());
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
        assumptions: assumptions,
        goals: goals,
    }
}
