use chrono::Local;
use clap::Parser;
use env_logger::Env;
use std::io::Write;
use std::path::PathBuf;

/// Prove some TPTP Problem
#[derive(Parser)]
struct Cli {
    /// Path to a tptp problem file
    file: PathBuf,
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
    log::info!("Path to TPTP problem: '{:?}'", args.file);
    let tptp_problem = qlib::tptp_parser::parse_file(args.file);
    for assumption in &tptp_problem.axioms {
        log::info!("Axioms: '{}'", assumption);
    }
    for goal in &tptp_problem.conjectures {
        log::info!("Conjectures: '{}'", goal);
    }
    let problem_cnf = qlib::tptp_parser::transform_problem(tptp_problem);
    log::info!("Problem Statement: '{}'", problem_cnf);
}
