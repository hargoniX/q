use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use tptp::visitor::Visitor;
use tptp::TPTPIterator;

fn read_file(file: PathBuf) -> Vec<u8> {
    log::info!("Opening '{:?}'", file);
    let mut f = File::open(file).expect("Unable to open file");
    let mut vec = Vec::new();
    f.read_to_end(&mut vec).expect("Unable to read file");
    vec
}

// Splitting this to use it for the include directive as well
pub fn parse_file(file: PathBuf) {
    let vec = read_file(file);
    parse(vec.as_slice())
}

struct FoFVisitor;
impl<'a> Visitor<'a> for FoFVisitor {}

pub fn parse(bytes: &[u8]) {
    let mut visitor = FoFVisitor;
    let mut parser = TPTPIterator::<()>::new(bytes);
    for result in &mut parser {
        let input = result.expect("Syntax error");
        log::info!("{}", &input);
        visitor.visit_tptp_input(&input);
    }
    assert!(parser.remaining.is_empty());
}
