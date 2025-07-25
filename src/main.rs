use chrono::Local;
use clap::Parser;
use env_logger::Env;
use qlib::pretty_print::pretty_print;
use qlib::proofs::GraphvizMode;
use qlib::selection::SelectionStrategy;
use qlib::superposition::{ResourceLimitConfig, search_proof};
use std::io::Write;
use std::path::PathBuf;
use std::time::Duration;

/// Prove some TPTP Problem
#[derive(Parser)]
struct Cli {
    /// Path to a tptp problem file
    file: PathBuf,
    /// Literal Selection Algorithm
    selection_strategy: Option<SelectionStrategy>,
    /// Duration limit in seconds
    duration: Option<u64>,
    /// Memory limit in MB,
    mem: Option<usize>,
    /// Path to graphviz output file
    #[arg(long)]
    graphviz: Option<String>,
    /// Graphviz output mode, if not set defaults to last
    #[arg(long)]
    gmode: Option<GraphvizMode>,
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
    let duration = args.duration.map(Duration::from_secs);
    let memory_limit = args.mem.map(|val| val * 1_000_000);
    let resource_limit = ResourceLimitConfig {
        duration,
        memory_limit,
    };
    log::info!("Path to TPTP problem: '{:?}'", args.file);

    let tptp_problem = qlib::tptp_parser::parse_file(args.file);
    for assumption in &tptp_problem.axioms {
        log::info!("Axioms: {assumption}");
    }
    for goal in &tptp_problem.conjectures {
        log::info!("Conjectures: {goal}");
    }
    // This should be hidden away within `fn solve` or sth
    let problem_cnf = qlib::tptp_parser::transform_problem(tptp_problem);
    log::info!("Problem Statement: {problem_cnf}");

    let (clauses, mut term_bank) = problem_cnf.to_clauses();
    term_bank.assert_names_unique();
    for clause in &clauses {
        log::info!("Clause: {}", pretty_print(clause, &term_bank));
        clause.assert_well_typed(&term_bank);
    }
    let gcfg = args
        .graphviz
        .map(|file| (args.gmode.unwrap_or(GraphvizMode::Last), file));
    let result = search_proof(
        clauses,
        &mut term_bank,
        &resource_limit,
        args.selection_strategy
            .unwrap_or(SelectionStrategy::FirstNeg),
        gcfg,
    );
    log::warn!("Result superposition: '{result:?}'");
}
