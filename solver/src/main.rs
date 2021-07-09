mod solver;
use solver::*;

pub fn main() {
    let mut solver = Solver {
        tight: true,
        number_of_variables: 3,
        assignments: vec![],
        decisions: vec![],
        watch_lists: vec![],
        nogoods: vec![
            vec![Literal(1), Literal(-2)],
            vec![Literal(2), Literal(-3)],
            vec![Literal(3), Literal(2)],
        ],
        decision_level: 0,
        chronological_backtracking_level: 0,
        derivations: Map::default(),
    };

    let solutions = solver.solve();

    for solution in solutions {
        println!("{:?}", solution);
    }
}