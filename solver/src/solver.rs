use std::collections::VecDeque;
use std::usize;
// solve() uses a SolveResult generator as iterator.
use genawaiter::sync::Gen;

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Literal(pub(crate) i32);

impl Literal {
    // fn id(&self) -> usize {
    //     self.0.unsigned_abs() as usize
    // }
    pub fn negate(&self) -> Literal {
        Literal(-self.0)
    }
}

// #[test]
// fn test_id() {
//     let lit = Literal(-2);
//     assert_eq!(lit.id(), 2);
// }

// TODO: Nogoods from a program

#[derive(Clone, Debug)]
pub(crate) struct WatchList {
    left_watch: usize,
    right_watch: usize,
    nogood: Vec<Literal>,
}
type Clause = Vec<Literal>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveResult {
    UnSat,
    Sat(Assignments),
}
// pub enum SolveResult<'a> {
//     UnSat,
//     Sat(&'a Assignments),
// }

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum PropagationResult {
    Ok,
    Conflict(Clause),
}
/// Map implementation used by the library.
pub type Map<K, V> = rustc_hash::FxHashMap<K, V>;
pub type Assignments = Vec<Literal>;

#[derive(Clone, Debug)]
pub struct Solver {
    pub(crate) tight: bool,
    pub(crate) number_of_variables: u32,
    pub(crate) assignments: Assignments,
    pub(crate) decisions: Vec<Literal>,
    pub(crate) watch_lists: Vec<WatchList>,
    pub(crate) nogoods: Vec<Clause>,
    pub(crate) decision_level: usize,
    pub(crate) chronological_backtracking_level: usize,
    pub(crate) derivations: Map<Literal, (Option<usize>, usize)>,
}
impl Solver {
    pub fn solve<'a, 'b>(&mut self) -> impl Iterator<Item = SolveResult> + '_ {
        Gen::new(|co| async move {
            self.create_watch_lists();
            let mut sat = true;

            while sat {
                if let PropagationResult::Conflict(nogood) = self.propagate() {
                    if self.is_top_level_conflict(&nogood) {
                        sat = false;
                        co.yield_(SolveResult::UnSat).await;
                    } else {
                        if self.chronological_backtracking_level < self.decision_level {
                            let (uip, sigma, k) = self.conflict_resolution(&nogood);
                            eprintln!("uip: {:?}", &uip);
                            if self.chronological_backtracking_level > k {
                                self.decision_level = self.chronological_backtracking_level;
                            } else {
                                self.decision_level = k;
                            }
                            eprintln!("new_decision_level: {}", self.decision_level);
                            self.backjump();

                            // add complement
                            let negated_sigma = sigma.negate();
                            self.assignments.push(negated_sigma);
                            self.derivations.insert(negated_sigma, (None, k));

                            self.nogoods.push(uip); // TODO: book keeping about learned nogoods
                            self.create_watch_lists();
                        } else {
                            //get decision literal from this decision_level
                            let decision_literal = self.decisions[self.decision_level - 1];
                            self.decision_level -= 1;
                            self.chronological_backtracking_level = self.decision_level;

                            self.backjump();

                            // add complement
                            let negated_decision_literal = decision_literal.negate();
                            self.assignments.push(negated_decision_literal);
                            self.derivations
                                .insert(negated_decision_literal, (None, self.decision_level));
                        }
                    }
                } else if self.assignment_complete() {
                    co.yield_(SolveResult::Sat(self.assignments.clone())).await;

                    //TODO: decrease number of solutions count down s
                    if self.decision_level == 0 {
                        return;
                    } else {
                        //get decision literal from this decision_level
                        let decision_literal = self.decisions[self.decision_level - 1];
                        eprintln!("backtrack decision literal {:?}", decision_literal);
                        self.decision_level -= 1;
                        eprintln!("decision_level: {}", self.decision_level);
                        self.chronological_backtracking_level = self.decision_level;
                        eprintln!(
                            "chronological_backtracking_level: {}",
                            self.chronological_backtracking_level
                        );
                        self.backjump();

                        // add complement
                        let negated_decision_literal = decision_literal.negate();
                        self.assignments.push(negated_decision_literal);
                        self.derivations
                            .insert(negated_decision_literal, (None, self.decision_level));
                    }
                    // TODO cleanup learnt nogoods
                } else {
                    self.decide()
                }
            }
        })
        .into_iter()
    }

    pub(crate) fn create_watch_lists(&mut self) {
        self.watch_lists.clear();
        for nogood in &self.nogoods {
            //  TODO: special handling for nogoods of size 1
            self.watch_lists.push(WatchList {
                left_watch: 1,
                right_watch: nogood.len(),
                nogood: nogood.clone(),
            })
        }
    }

    /// analyze conflict and learn UIP nogood
    pub(crate) fn conflict_resolution(&self, nogood: &[Literal]) -> (Clause, Literal, usize) {
        let mut nogood = nogood.to_owned();
        let sigma = loop {
            // eprintln!("delta:{:?}", nogood);
            let sigma = nogood[0];
            let (nogood_index, decision_level_sigma) = self.derivations.get(&sigma).unwrap();

            if {
                // a nogood is a unique implication point if there is no other literal
                // from the same decision level as sigma
                let mut iter = nogood.iter();
                let unique = loop {
                    if let Some(literal) = iter.next() {
                        if *literal != sigma {
                            let (_, decision_level) = self.derivations.get(literal).unwrap();
                            if decision_level == decision_level_sigma {
                                break false;
                            }
                        }
                    } else {
                        break true;
                    }
                };
                unique
            } {
                break sigma;
            }

            if let Some(index) = nogood_index {
                let reason = &self.nogoods[*index];
                let res = resolve(&nogood, &sigma, reason);
                // eprintln!("res: {:?}", &res);
                nogood = res;
            } else {
                // There is always a reason
                // TODO: double check this
                unreachable!();
            }
        };
        let mut k = 0;
        for lit in &nogood {
            if *lit != sigma {
                let (_id, decision_level) = self.derivations.get(lit).unwrap();
                if *decision_level > k {
                    k = *decision_level
                }
            }
        }
        eprintln!("k: {}", k);
        eprintln!("sigma: {:?}", sigma);
        (nogood, sigma, k)
    }
    /// increase decision level assign truth value to a previously unassigned variable
    pub(crate) fn decide(&mut self) {
        self.decision_level += 1;
        eprintln!("decision_level: {:?}", self.decision_level);
        let decision_literal = self.choose();
        eprintln!("decision_literal: {:?}", decision_literal);
        self.assignments.push(decision_literal);
        self.decisions.push(decision_literal);
        self.derivations
            .insert(decision_literal, (None, self.decision_level));
    }

    fn choose(&self) -> Literal {
        for index in 1..self.number_of_variables + 1 {
            if self.assignments.contains(&Literal(index as i32)) {
                continue;
            }
            if self.assignments.contains(&Literal(-(index as i32))) {
                continue;
            }
            return Literal(index as i32);
        }
        panic!("Logic error: calling choose on complete assignment-");
    }

    /// return true if all variables have a truth value assignment
    pub(crate) fn assignment_complete(&self) -> bool {
        for index in 1..self.number_of_variables + 1 {
            if self.assignments.contains(&Literal(index as i32)) {
                continue;
            }
            if self.assignments.contains(&Literal(-(index as i32))) {
                continue;
            }
            return false;
        }
        true
    }
    /// return true if there is a conflich on decision level 0
    pub fn is_top_level_conflict(&self, nogood: &[Literal]) -> bool {
        for literal in nogood {
            let (_id, decision_level) = self.derivations.get(literal).unwrap();
            if *decision_level > 0 {
                return false;
            }
        }
        true
    }
    /// backjump to decision level x and rewind assignment
    pub fn backjump(&mut self) {
        eprintln!("backjump");
        eprintln!("decision_level {}", self.decision_level);

        // let mut assignment_iter = self.assignments.iter();
        // let mut new_assignments = vec![];
        // while let Some(lit) = assignment_iter.next() {
        //     let (_id, decision_level) = self.derivations.get(lit).unwrap();
        //     if *decision_level < self.decision_level {
        //         new_assignments.push(*lit);
        //     } else {
        //         eprintln!("pop:{:?}", lit);
        //         self.derivations.remove(lit);
        //     }
        // }
        // self.assignments = new_assignments;

        if self.assignments.len() > 0 {
            let mut index = self.assignments.len();

            while index > 0 {
                index -= 1;
                let lit = &self.assignments[index];
                let (_id, decision_level) = self.derivations.get(lit).unwrap();
                if *decision_level >= self.decision_level {
                    eprintln!("pop:{:?}", lit);
                    self.derivations.remove(lit);
                    self.assignments.remove(index);
                }
            }
        }

        // backtrack decisions
        while self.decisions.len() > self.decision_level {
            self.decisions.pop();
        }
    }
    /// run unit propagation and unfounded set check
    pub(crate) fn propagate(&mut self) -> PropagationResult {
        eprintln!("propagate");
        if let PropagationResult::Conflict(nogood) = self.unit_propagation() {
            return PropagationResult::Conflict(nogood);
        }
        if !self.tight {
            self.unfounded_loop_learning();
        }
        PropagationResult::Ok
    }
    /// learn a nogood for an unfounded loop
    pub fn unfounded_loop_learning(&mut self) {
        todo!()
    }

    pub(crate) fn unit_propagation(&mut self) -> PropagationResult {
        let mut propagation_queue: VecDeque<Literal> = self.assignments.iter().cloned().collect();

        loop {
            if let Some(p) = propagation_queue.pop_front() {
                for (index, current_watch_list) in self.watch_lists.iter_mut().enumerate() {
                    if current_watch_list.nogood[current_watch_list.left_watch - 1] == p {
                        current_watch_list.left_watch += 1;
                    }
                    if current_watch_list.nogood[current_watch_list.right_watch - 1] == p {
                        current_watch_list.right_watch -= 1;
                    }

                    if current_watch_list.left_watch > current_watch_list.right_watch {
                        eprintln!("conflicting nogood: {:?}", current_watch_list.nogood);
                        return PropagationResult::Conflict(current_watch_list.nogood.clone());
                    }
                    if current_watch_list.left_watch == current_watch_list.right_watch {
                        let res = current_watch_list.nogood[current_watch_list.right_watch - 1];
                        if self.assignments.contains(&res) {
                            eprintln!("conflicting nogood: {:?}", current_watch_list.nogood);
                            return PropagationResult::Conflict(current_watch_list.nogood.clone());
                        }
                        let res = res.negate();
                        if !self.assignments.contains(&res) {
                            eprintln!("infer: {:?}", res);
                            self.assignments.push(res);
                            propagation_queue.push_back(res);
                            self.derivations
                                .insert(res, (Some(index), self.decision_level));
                            break;
                        }
                    }
                }
            } else {
                for (wl_index, current_watch_list) in self.watch_lists.iter().enumerate() {
                    if current_watch_list.left_watch == current_watch_list.right_watch {
                        let res = current_watch_list.nogood[current_watch_list.right_watch - 1];
                        if self.assignments.contains(&res) {
                            eprintln!("conflicting nogood: {:?}", current_watch_list.nogood);
                            return PropagationResult::Conflict(current_watch_list.nogood.clone());
                        }
                        let res = res.negate();
                        if !self.assignments.contains(&res) {
                            eprintln!("infer: {:?}", res);
                            self.assignments.push(res);
                            propagation_queue.push_back(res);
                            self.derivations
                                .insert(res, (Some(wl_index), self.decision_level));

                            break;
                        }
                    }
                }
            }
            if propagation_queue.is_empty() {
                return PropagationResult::Ok;
            }
        }
    }
}

fn resolve(nogood: &[Literal], sigma: &Literal, reason: &[Literal]) -> Clause {
    // assert sigma in nogood and reason
    let mut res = vec![];
    for lit in nogood {
        if *lit != *sigma {
            res.push(*lit)
        }
    }
    let neg_sigma = sigma.negate();
    for lit in reason {
        if *lit != neg_sigma {
            res.push(*lit)
        }
    }
    res.sort();
    res.dedup();
    res
}

#[test]
fn test_unit_propagation() {
    let mut solver = Solver {
        tight: true,
        number_of_variables: 3,
        assignments: vec![Literal(1)],
        decisions: vec![Literal(1)],
        watch_lists: vec![],
        nogoods: vec![vec![Literal(1), Literal(-2)]],
        decision_level: 0,
        chronological_backtracking_level: 0,
        derivations: Map::default(),
    };
    solver.create_watch_lists();
    solver.unit_propagation();
    let res = &solver.assignments;
    assert_eq!(*res, vec![Literal(1), Literal(2)]);
}

/// only for testing
fn mock_decide(solver: &mut Solver) {
    solver.decision_level += 1;
    let decision_literal = Literal(1);
    solver.assignments.push(decision_literal);
    solver
        .derivations
        .insert(decision_literal, (None, solver.decision_level));
}

/// only for testing
fn mock_decide2(solver: &mut Solver) {
    solver.decision_level += 1;
    let decision_literal = Literal(3);
    solver.assignments.push(decision_literal);
    solver
        .derivations
        .insert(decision_literal, (None, solver.decision_level));
}

#[test]
fn test_unit_propagation_conflict() {
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
    mock_decide(&mut solver); // assign Literal(1)
    solver.create_watch_lists();
    let prop_result = solver.unit_propagation();
    if let PropagationResult::Conflict(nogood) = prop_result {
        assert_eq!(nogood, vec![Literal(3), Literal(2)]);
        let top_level_conflict = solver.is_top_level_conflict(&nogood);
        assert_eq!(top_level_conflict, false);
        let (uip, sigma, k) = solver.conflict_resolution(&nogood);
        assert_eq!(uip, vec![Literal(2)]);
        assert_eq!(sigma, Literal(2));
        if solver.chronological_backtracking_level > k {
            solver.decision_level = solver.chronological_backtracking_level;
        } else {
            solver.decision_level = k;
        }
        eprintln!("new_decision_level: {}", solver.decision_level);
        solver.backjump();

        // add complement
        let negated_sigma = sigma.negate();
        solver.assignments.push(negated_sigma);
        solver.derivations.insert(negated_sigma, (None, k));

        solver.nogoods.push(uip);
        solver.create_watch_lists();

        let res = solver.unit_propagation();
        assert_eq!(res, PropagationResult::Ok);
        assert_eq!(solver.assignments, vec![Literal(-2), Literal(-1)]);

        mock_decide2(&mut solver); // assign Literal(3)

        let res = solver.unit_propagation();
        assert_eq!(res, PropagationResult::Ok);
        assert_eq!(
            solver.assignments,
            vec![Literal(-2), Literal(-1), Literal(3)]
        );

        assert_eq!(solver.assignment_complete(), true);
    }
}

#[test]
pub fn test_solve1() {
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

    let mut solutions = solver.solve();
    let res = solutions.next();
    assert_eq!(
        res,
        Some(SolveResult::Sat(vec![Literal(-2), Literal(-1), Literal(3)]))
    );
    let res = solutions.next();
    assert_eq!(
        res,
        Some(SolveResult::Sat(vec![
            Literal(-3),
            Literal(-1),
            Literal(-2)
        ]))
    );
    let res = solutions.next();
    assert_eq!(res, None);
}
#[test]
pub fn test_solve_unsat() {
    let mut solver = Solver {
        tight: true,
        number_of_variables: 1,
        assignments: vec![],
        decisions: vec![],
        watch_lists: vec![],
        nogoods: vec![vec![Literal(1)], vec![Literal(-1)]],
        decision_level: 0,
        chronological_backtracking_level: 0,
        derivations: Map::default(),
    };

    let mut solutions = solver.solve();
    let res = solutions.next();
    assert_eq!(res, Some(SolveResult::UnSat));
    let res = solutions.next();
    assert_eq!(res, None);
}
