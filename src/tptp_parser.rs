use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use tptp::top::TPTPInput;
use tptp::TPTPIterator;

pub fn parse_file(file: PathBuf) {
    let bytes = read_file(file);
    parse(&bytes)
}

fn read_file(file: PathBuf) -> Box<[u8]> {
    log::info!("Opening '{:?}'", file);
    let mut f = File::open(file).expect("Unable to open file");
    let mut vec = Vec::new();
    f.read_to_end(&mut vec).expect("Unable to read file");
    vec.into_boxed_slice()
}



// parse into structure consisting of two lists: one with assumptions, one with goals (still FoF)
// then combine these into a big conjunction with the correct negations
pub fn parse(bytes: &[u8]) {
    let mut parser = TPTPIterator::<()>::new(bytes);
    for result in &mut parser {
        let input = result.expect("Syntax error");
        if let TPTPInput::Include(f) = input {
            log::info!("File to include: '{}'", f);
        } else if let TPTPInput::Annotated(annotated_formula) = input {
            let file = annotated_formula.file_name;
            log::info!("Annotated FoF: '{}'", file);
        }
    }
    assert!(parser.remaining.is_empty());
}
