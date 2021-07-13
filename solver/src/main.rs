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
                    println!("Solution {}: {:?}", c + 1, assignments);
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
