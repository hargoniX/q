use chrono::Local;
use clap::Parser;
use env_logger::Env;
use qlib::pretty_print::pretty_print;
use qlib::superposition::{ResourceLimitConfig, search_proof};
use qlib::term_bank::TermBank;
use qlib::tptp_parser::{TermBankConversionState, to_clauses};
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::time::Duration;

/// Prove some TPTP Problem
#[derive(Parser)]
struct Cli {
    /// Path to a tptp problem file
    file: PathBuf,
    /// Duration limit
    duration: Option<u64>,
}

fn main() {
    let args = Cli::parse();
    env_logger::Builder::from_env(Env::default().default_filter_or("info"))
        .format(|buf, record| {
            let level_style = buf.default_level_style(record.level()).bold();
            writeln!(
                buf,
                "{}|{level_style}{:7}{level_style:#}|{:10}| {}",
                Local::now().format("%H:%M:%S"),
                record.level(),
                record.target(),
                record.args()
            )
        })
        .init();
    let resource_limit;
    if let Some(duration) = args.duration {
        resource_limit = ResourceLimitConfig {
            duration: Some(Duration::from_secs(duration)),
            memory_limit: None,
        };
    } else {
        resource_limit = Default::default();
    }
    log::info!("Path to TPTP problem: '{:?}'", args.file);

    let tptp_problem = qlib::tptp_parser::parse_file(args.file);
    for assumption in &tptp_problem.axioms {
        log::info!("Axioms: {}", assumption);
    }
    for goal in &tptp_problem.conjectures {
        log::info!("Conjectures: {}", goal);
    }
    // This should be hidden away within `fn solve` or sth
    let problem_cnf = qlib::tptp_parser::transform_problem(tptp_problem);
    log::info!("Problem Statement: {}", problem_cnf);

    let mut term_bank = TermBank::new();
    let clauses = to_clauses(
        problem_cnf,
        &mut TermBankConversionState {
            term_bank: &mut term_bank,
            var_map: HashMap::new(),
            func_map: HashMap::new(),
        },
    );
    for clause in &clauses {
        log::info!("Clause: {}", pretty_print(clause, &term_bank));
    }
    let result = search_proof(clauses, &mut term_bank, &resource_limit);
    log::warn!("Result superposition: '{:?}'", result);
}
