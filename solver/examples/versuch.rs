use anyhow::Result;
use clap::Parser;
use log::{debug, error, info, warn};
use solver::convert::Builder;
use std::fs;
use std::io;
use std::path::PathBuf;

/// Solver
#[derive(Parser, Debug)]
#[clap(name = "solver")]
#[clap(version, author)]
struct Opt {
    /// Input file in aspif format
    #[clap(name = "FILE", parse(from_os_str))]
    file: Option<PathBuf>,
    /// Verbose mode (-v, -vv, -vvv, etc)
    #[clap(short = 'v', long = "verbose", parse(from_occurrences))]
    verbose: usize,
}

pub enum Reader<'a> {
    File(io::BufReader<fs::File>),
    Stdin(io::StdinLock<'a>),
}

impl<'a> io::Read for Reader<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::File(reader) => reader.read(buf),
            Self::Stdin(guard) => guard.read(buf),
        }
    }
}

impl<'a> io::BufRead for Reader<'a> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        match self {
            Self::File(reader) => reader.fill_buf(),
            Self::Stdin(guard) => guard.fill_buf(),
        }
    }
    fn consume(&mut self, amt: usize) {
        match self {
            Self::File(reader) => reader.consume(amt),
            Self::Stdin(guard) => guard.consume(amt),
        }
    }
}
fn main() {
    let opt = Opt::parse();

    stderrlog::new()
        .module(module_path!())
        .verbosity(opt.verbose * 4)
        .module("solver")
        .init()
        .unwrap();
    if let Err(err) = run(opt) {
        error!("{:?}", err);
        std::process::exit(1);
    }
}
fn run(opt: Opt) -> Result<()> {
    let stdin = io::stdin();
    let input = match opt.file {
        Some(path) => {
            let file = fs::File::open(path)?;
            Reader::File(io::BufReader::new(file))
        }
        None => {
            let guard = stdin.lock();
            Reader::Stdin(guard)
        }
    };

    // let mut out = std::io::stdout();

    info!("Reading input ...");
    let parse_result = match input {
        Reader::File(buf_reader) => aspif::read_aspif(buf_reader)?,
        Reader::Stdin(buf_reader) => aspif::read_aspif(buf_reader)?,
    };

    let (builder, symbol_mapper, interner) = match parse_result {
        aspif::ParseResult::Complete(aspif_program) => Builder::from_aspif(&aspif_program),
        aspif::ParseResult::Incomplete(_) => {
            warn!("Could not read complete aspif program.");
            panic!("Could not read complete aspif program.");
        }
    };

    // let builder = Builder {
    //     nogoods: vec![
    //         vec![
    //             Literal { id: 0, sign: true },
    //             Literal { id: 1, sign: false },
    //         ],
    //         vec![
    //             Literal { id: 1, sign: true },
    //             Literal { id: 2, sign: false },
    //         ],
    //         vec![Literal { id: 2, sign: true }, Literal { id: 1, sign: true }],
    //     ],
    // };

    let mut solver = builder.build();
    use solver::solver::SolveResult;
    let mut solutions = solver.solve().enumerate();

    loop {
        if let Some((c, res)) = solutions.next() {
            match res {
                SolveResult::Sat(assignments) => {
                    print!("Solution {}: ", c + 1);
                    for (condition, symbol) in &symbol_mapper {
                        let mut satisfied = true;
                        for literal in condition {
                            match assignments[literal.id] {
                                Some(sign) => satisfied = sign == literal.sign,
                                None => panic!("Partial assignment!"),
                            }
                            if !satisfied {
                                break;
                            };
                        }
                        if satisfied {
                            print!("{} ", interner.resolve(*symbol).unwrap());
                        }
                    }
                    let mut string = String::new();
                    for (id, e) in assignments.iter().enumerate() {
                        match e {
                            Some(true) => string = format!("{} {}", string, id),
                            Some(false) => string = format!("{} ~{}", string, id),
                            None => {}
                        }
                    }
                    debug!("solution: {string}");
                    println!();
                }
                SolveResult::UnSat => {
                    println!("UNSAT");
                }
            }
        } else {
            println!("EXHAUSTED");
            break;
        }
    }
    Ok(())
}