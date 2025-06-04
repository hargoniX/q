use chrono::Local;
use clap::Parser;
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
    env_logger::builder()
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
    log::info!("Parse file: {:?}", args.file);
    log::info!("Hello, World! {}", qlib::test());
}
