mod solver;
use solver::*;

pub fn main() {
    let builder = Builder {
        nogoods: vec![
            vec![Literal(1), Literal(-2)],
            vec![Literal(2), Literal(-3)],
            vec![Literal(3), Literal(2)],
        ],
    };
    let mut solver = builder.build();

    let mut solutions = solver.solve().enumerate();

    loop {
        if let Some((c, res)) = solutions.next() {
            match res {
                SolveResult::Sat(assignments) => {
                    println!("Solution {}: {:?}", c, assignments);
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
