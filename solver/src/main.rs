mod solver;
use solver::*;

pub fn main() {
    let builder = Builder {
        nogoods: vec![
            vec![
                Literal { id: 0, sign: true },
                Literal { id: 1, sign: false },
            ],
            vec![
                Literal { id: 1, sign: true },
                Literal { id: 2, sign: false },
            ],
            vec![Literal { id: 2, sign: true }, Literal { id: 1, sign: true }],
        ],
    };
    let mut solver = builder.build();

    let mut solutions = solver.solve().enumerate();

    loop {
        if let Some((c, res)) = solutions.next() {
            match res {
                SolveResult::Sat(assignments) => {
                    print!("Solution {}: ", c + 1);
                    for (id, e) in assignments.iter().enumerate() {
                        match e {
                            Some(true) => print!("{} ", id),
                            Some(false) => print!("~{} ", id),
                            None => {}
                        }
                    }
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
}
