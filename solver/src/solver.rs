use std::collections::VecDeque;
use std::usize;
// solve() uses a SolveResult generator as iterator.
use genawaiter::sync::Gen;

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Literal {
    pub(crate) id: usize,
    pub(crate) sign: bool,
}
impl Literal {
    fn id(&self) -> usize {
        self.id
    }
    pub fn sign(&self) -> bool {
        self.sign
    }
    pub fn negate(&self) -> Literal {
        Literal {
            id: self.id,
            sign: !self.sign,
        }
    }
}

#[test]
fn test_id() {
    let lit = Literal { id: 2, sign: false };
    assert_eq!(lit.id(), 2);
}

// TODO: Nogoods from a program

#[derive(Copy, Clone, Debug)]
pub(crate) struct WatchList {
    first_watch: usize,
    second_watch: usize,
}
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Watch {
    First,
    Second,
}
/// Solver internal representation of nogoods and assignments
type Nogood = Vec<Option<bool>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveResult {
    UnSat,
    Sat(Vec<Option<bool>>),
}
//type Assignments = Vec<Option<bool>>
// pub enum SolveResult<'a> {
//     UnSat,
//     Sat(&'a Assignments),
// }

#[derive(Clone, Debug, PartialEq)]
enum PropagationResult {
    Ok,
    Conflict(Nogood),
}
/// Map implementation used by the library.
pub type Map<K, V> = rustc_hash::FxHashMap<K, V>;

pub struct Builder {
    pub(crate) nogoods: Vec<Vec<Literal>>,
}
impl Builder {
    pub fn build(self) -> Solver {
        let mut number_of_variables = 0;
        for nogood in &self.nogoods {
            for lit in nogood {
                if lit.id() + 1 > number_of_variables {
                    number_of_variables = lit.id() + 1;
                }
            }
        }
        let mut solver_nogoods = vec![];
        for nogood in self.nogoods {
            let mut solver_nogood = vec![None; number_of_variables];
            for id in 0..number_of_variables {
                if nogood.contains(&Literal { id, sign: true }) {
                    solver_nogood[id] = Some(true);
                } else if nogood.contains(&Literal { id, sign: false }) {
                    solver_nogood[id] = Some(false);
                }
            }
            solver_nogoods.push(solver_nogood);
        }

        let mut watch_lists = vec![];
        for nogood in &solver_nogoods {
            eprintln!("nogood: {:?}", nogood);
            //  TODO: special handling for nogoods of size 1
            let mut left_watch = 0;
            while nogood[left_watch] == None {
                left_watch += 1;
            }
            let mut right_watch = nogood.len() - 1;
            while nogood[right_watch] == None {
                right_watch -= 1;
            }
            watch_lists.push(WatchList {
                first_watch: left_watch,
                second_watch: right_watch,
            })
        }

        let mut var_to_nogoods: Vec<Map<usize, bool>> = vec![Map::default(); number_of_variables];
        let mut nogoods_to_var: Vec<Map<usize, bool>> = vec![Map::default(); solver_nogoods.len()];
        for nogood_id in 0..solver_nogoods.len() {
            for variable_id in 0..number_of_variables {
                if let Some(sign) = solver_nogoods[nogood_id][variable_id] {
                    var_to_nogoods[variable_id].insert(nogood_id, sign);
                    nogoods_to_var[nogood_id].insert(variable_id, sign);
                }
            }
        }

        Solver {
            tight: true,
            number_of_variables,
            assignments: vec![None; number_of_variables],
            decisions: vec![],
            watch_lists,
            nogoods: solver_nogoods,
            var_to_nogoods,
            nogoods_to_var,
            decision_level: 0,
            assignments_log: vec![(None, None, 0); number_of_variables],
            chronological_backtracking_level: 0,
        }
    }
}
#[derive(Clone, Debug)]
pub struct Solver {
    tight: bool,
    number_of_variables: usize,
    assignments: Vec<Option<bool>>,
    decisions: Vec<Literal>,
    watch_lists: Vec<WatchList>,
    nogoods: Vec<Nogood>,
    var_to_nogoods: Vec<Map<usize, bool>>,
    nogoods_to_var: Vec<Map<usize, bool>>,
    decision_level: usize,
    assignments_log: Vec<(Option<bool>, Option<usize>, usize)>,
    chronological_backtracking_level: usize,
}
impl Solver {
    pub fn solve(&mut self) -> impl Iterator<Item = SolveResult> + '_ {
        Gen::new(|co| async move {
            let mut sat = true;

            while sat {
                if let PropagationResult::Conflict(nogood) = self.propagate() {
                    if self.is_top_level_conflict(&nogood) {
                        sat = false;
                        co.yield_(SolveResult::UnSat).await;
                    } else if self.chronological_backtracking_level < self.decision_level {
                        let (uip, sigma, k) = self.conflict_resolution(&nogood);
                        eprintln!("uip: {:?}", &uip);
                        if self.chronological_backtracking_level > k {
                            self.decision_level = self.chronological_backtracking_level;
                        } else {
                            self.decision_level = k;
                        }
                        eprintln!("new_decision_level: {}", self.decision_level);
                        self.backjump();

                        // add complement of sigma
                        self.assignments[sigma.id] = Some(!sigma.sign);
                        self.assignments_log[sigma.id] = (Some(!sigma.sign), None, k);
                        self.record_nogood(uip);
                    } else {
                        //get decision literal from this decision_level
                        let decision_literal = self.decisions[self.decision_level - 1];
                        self.decision_level -= 1;
                        self.chronological_backtracking_level = self.decision_level;

                        self.backjump();

                        // add complement of the decision literal
                        self.assignments[decision_literal.id] = Some(!decision_literal.sign);
                        self.assignments_log[decision_literal.id] =
                            (Some(!decision_literal.sign), None, self.decision_level);
                    }
                } else if self.assignment_complete() {
                    co.yield_(SolveResult::Sat(self.assignments.clone())).await;

                    if self.decision_level == 0 {
                        return;
                    } else {
                        // get decision literal from this decision_level
                        let decision_literal = self.decisions[self.decision_level - 1];
                        // eprintln!("flip decision literal {:?}", decision_literal);
                        self.decision_level -= 1;
                        eprintln!("decision_level: {}", self.decision_level);
                        self.chronological_backtracking_level = self.decision_level;
                        eprintln!(
                            "chronological_backtracking_level: {}",
                            self.chronological_backtracking_level
                        );
                        self.backjump();

                        // add complement of the decision literal
                        self.assignments[decision_literal.id] = Some(!decision_literal.sign);
                        self.assignments_log[decision_literal.id] =
                            (Some(!decision_literal.sign), None, self.decision_level);
                    }
                    // TODO cleanup learnt nogoods
                } else {
                    self.decide()
                }
            }
        })
        .into_iter()
    }

    fn record_nogood(&mut self, nogood: Nogood) {
        self.watch_lists.push(nogood_to_watch_list(&nogood));
        self.nogoods.push(nogood);
        let nogood_id = self.nogoods.len() - 1;
        for variable_id in 0..self.number_of_variables {
            if let Some(sign) = self.nogoods[nogood_id][variable_id] {
                self.var_to_nogoods[variable_id].insert(nogood_id, sign);
                self.nogoods_to_var.push(Map::default());
                self.nogoods_to_var[nogood_id].insert(variable_id, sign);
            }
        }
    }

    /// analyze conflict and learn UIP nogood
    fn conflict_resolution(&self, nogood: &[Option<bool>]) -> (Nogood, Literal, usize) {
        let mut nogood = nogood.to_owned();
        let sigma = loop {
            // eprintln!("delta: {:?}", nogood);
            let iter = nogood.iter().enumerate();

            // initialie sigma, nogood_index, decision_levl_sigma
            let mut sigma = Literal { id: 0, sign: true };
            let mut nogood_index = None;
            let mut decision_level_sigma = 0;
            for (id, assignment) in iter {
                if let Some(sign) = *assignment {
                    let literal = Literal { id, sign };
                    let (_, ng_index, decision_level) = self.assignments_log[literal.id];
                    if let Some(index) = ng_index {
                        sigma = literal;
                        nogood_index = Some(index);
                        decision_level_sigma = decision_level;
                        break;
                    }
                    sigma = literal;
                    nogood_index = None;
                    decision_level_sigma = decision_level;
                }
            }
            // eprintln!("sigma: {:?}", sigma);

            // a nogood is a unique implication point if there is no other literal
            // from the same decision level as sigma
            let mut iter = nogood.iter().enumerate();
            let unique = loop {
                match iter.next() {
                    Some((id, &Some(sign))) => {
                        let literal = Literal { id, sign };
                        if sigma != literal {
                            // eprintln!("literal: {:?}", literal);
                            let (_, _, decision_level) = self.assignments_log[literal.id];
                            if decision_level == decision_level_sigma {
                                break false;
                            }
                        }
                    }
                    Some((_, &None)) => {}
                    None => break true,
                }
            };
            if unique {
                break sigma;
            }
            // eprintln!("not unique");
            if let Some(nogood_index) = nogood_index {
                let reason = &self.nogoods[nogood_index];
                // eprintln!("reason: {:?}", reason);
                let res = resolve(&nogood, &sigma, reason);
                nogood = res;
            } else {
                // sigma is a decision_literals
                // the reason is empty
                let reason: Vec<Option<bool>> = vec![None; self.number_of_variables];
                // eprintln!("reason: {:?}", reason);
                let res = resolve(&nogood, &sigma, &reason);
                nogood = res;
            }
        };
        let mut k = 0;
        for (id, assignment) in nogood.iter().enumerate() {
            if let Some(sign) = *assignment {
                let literal = Literal { id, sign };
                if literal != sigma {
                    let (_, _, decision_level) = self.assignments_log[literal.id];
                    if decision_level > k {
                        k = decision_level
                    }
                }
            }
        }
        // eprintln!("k: {}", k);
        // eprintln!("sigma: {:?}", sigma);
        (nogood, sigma, k)
    }
    /// increase decision level assign truth value to a previously unassigned variable
    fn decide(&mut self) {
        self.decision_level += 1;
        eprintln!("decision_level: {:?}", self.decision_level);
        let decision_literal = self.choose();
        eprintln!("decision_literal: {:?}", decision_literal);
        self.assignments[decision_literal.id()] = Some(decision_literal.sign);
        self.decisions.push(decision_literal);
        self.assignments_log[decision_literal.id] =
            (Some(decision_literal.sign), None, self.decision_level);
    }

    fn choose(&self) -> Literal {
        for id in 0..self.number_of_variables {
            if self.assignments[id] == Some(true) {
                continue;
            }
            if self.assignments[id] == Some(false) {
                continue;
            }
            return Literal { id, sign: true };
        }
        panic!("Logic error: calling choose on complete assignment-");
    }

    /// return true if all variables have a truth value assignment
    fn assignment_complete(&self) -> bool {
        for id in 0..self.number_of_variables {
            if self.assignments[id] == Some(true) {
                continue;
            }
            if self.assignments[id] == Some(false) {
                continue;
            }
            return false;
        }
        true
    }
    /// return true if there is a conflict on decision level 0
    fn is_top_level_conflict(&self, nogood: &[Option<bool>]) -> bool {
        for (id, assignment) in nogood.iter().enumerate() {
            if assignment.is_some() {
                let (_, _, decision_level) = self.assignments_log[id];
                if decision_level > 0 {
                    return false;
                }
            }
        }
        true
    }
    /// backjump to decision level x and rewind assignment
    fn backjump(&mut self) {
        // eprintln!("backjump to decision_level {}", self.decision_level);
        for (id, assignment) in self.assignments.iter_mut().enumerate() {
            if let Some(sign) = *assignment {
                let lit = Literal { id, sign };
                let (_, _, decision_level) = self.assignments_log[lit.id];

                if decision_level > self.decision_level {
                    self.assignments_log[lit.id] = (None, None, 0);
                    *assignment = None;
                }
            }
        }

        // backtrack decisions
        while self.decisions.len() > self.decision_level {
            self.decisions.pop();
        }
    }

    /// run unit propagation and unfounded set check
    fn propagate(&mut self) -> PropagationResult {
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
    fn unfounded_loop_learning(&mut self) {
        todo!()
    }

    fn unit_propagation(&mut self) -> PropagationResult {
        let mut propagation_queue: VecDeque<Literal> = VecDeque::new();
        for (id, assignment) in self.assignments.iter().enumerate() {
            if let Some(sign) = *assignment {
                propagation_queue.push_back(Literal { id, sign });
            }
        }

        loop {
            if let Some(p) = propagation_queue.pop_front() {
                // eprintln!("prp: {:?}", p);

                for (index, sign) in &self.var_to_nogoods[p.id] {
                    let watch_list = &mut self.watch_lists[*index];
                    // eprintln!(
                    //     "wl.0: {} wl.1: {} nogood: {:?}",
                    //     watch_list.first_watch, watch_list.second_watch, self.nogoods[*index]
                    // );
                    if watch_list.first_watch == p.id || watch_list.second_watch == p.id {
                        let dirty_watch = if watch_list.first_watch == p.id {
                            Watch::First
                        } else {
                            Watch::Second
                        };

                        if *sign == p.sign {
                            // propagated literal and nogood literal have the same sign
                            // try to update watch
                            if let Some(new_watch) = update_watches(
                                &self.nogoods_to_var[*index],
                                &self.assignments,
                                p,
                                watch_list.first_watch,
                                watch_list.second_watch,
                            ) {
                                if dirty_watch == Watch::First {
                                    watch_list.first_watch = new_watch;
                                } else {
                                    watch_list.second_watch = new_watch;
                                }
                                continue;
                            } else {
                                // eprintln!("one watch could not be updated. it's a conflict or an implication.");
                                let other_watch = if dirty_watch == Watch::First {
                                    &mut watch_list.second_watch
                                } else {
                                    &mut watch_list.first_watch
                                };

                                // eprintln!("check the other watch");
                                let sign = self.nogoods_to_var[*index][other_watch];
                                match self.assignments[*other_watch] {
                                    Some(x) => {
                                        if sign == x {
                                            // also the other watched literal is in the assignment. it's a conflict
                                            return PropagationResult::Conflict(
                                                self.nogoods[*index].clone(),
                                            );
                                        }
                                    }
                                    None => {
                                        // the other watch is unassigned. we can imply the complement
                                        let complement = !sign;
                                        self.assignments[*other_watch] = Some(complement);
                                        let lit = Literal {
                                            id: *other_watch,
                                            sign: complement,
                                        };
                                        eprintln!("infer: {:?}", lit);
                                        propagation_queue.push_back(lit);
                                        self.assignments_log[*other_watch] =
                                            (Some(complement), Some(*index), self.decision_level);
                                    }
                                }
                            }
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

fn update_watches(
    nogood_vars: &Map<usize, bool>,
    assignments: &[Option<bool>],
    p: Literal,
    first_watch: usize,
    second_watch: usize,
) -> Option<usize> {
    for (id, sign) in nogood_vars {
        if *id != p.id
            && *id != first_watch
            && *id != second_watch
            && assignments[*id] != Some(*sign)
        {
            return Some(*id);
        }
    }
    None
}

fn resolve(nogood: &[Option<bool>], sigma: &Literal, reason: &[Option<bool>]) -> Nogood {
    // assert sigma in nogood and reason
    let mut res = vec![];
    for (id, assignment) in nogood.iter().enumerate() {
        match *assignment {
            Some(sign) => {
                let literal = Literal { id, sign };
                if literal != *sigma {
                    res.push(Some(sign))
                } else {
                    res.push(None)
                }
            }
            None => res.push(None),
        }
    }
    let neg_sigma = sigma.negate();
    for (id, assignment) in reason.iter().enumerate() {
        if let Some(sign) = *assignment {
            let literal = Literal { id, sign };
            if literal != neg_sigma {
                res[id] = Some(sign);
            }
        }
    }
    res
}

fn nogood_to_watch_list(nogood: &[Option<bool>]) -> WatchList {
    //  TODO: special handling for nogoods of size 1
    let mut first_watch = 0;
    while nogood[first_watch] == None {
        first_watch += 1;
    }
    let mut second_watch = nogood.len() - 1;
    while nogood[second_watch] == None {
        second_watch -= 1;
    }
    WatchList {
        first_watch,
        second_watch,
    }
}
// only for tests
fn create_watch_lists(nogoods: &[Vec<Option<bool>>]) -> Vec<WatchList> {
    let mut watch_lists = vec![];
    for nogood in nogoods {
        //  TODO: special handling for nogoods of size 1
        watch_lists.push(nogood_to_watch_list(nogood))
    }
    watch_lists
}
/// only for testing
fn mock_decide(solver: &mut Solver) {
    solver.decision_level += 1;
    solver.assignments[0] = Some(true);
    solver.assignments_log[0] = (Some(true), None, solver.decision_level);
}

/// only for testing
fn mock_decide2(solver: &mut Solver) {
    solver.decision_level += 1;
    solver.assignments[2] = Some(true);
    solver.assignments_log[2] = (Some(true), None, solver.decision_level);
}
#[test]
fn test_unit_propagation() {
    let solver_nogoods = vec![vec![None, Some(true), Some(false)]];
    let number_of_variables = 3;
    let mut var_to_nogoods: Vec<Map<usize, bool>> = vec![Map::default(); number_of_variables];
    let mut nogoods_to_var: Vec<Map<usize, bool>> = vec![Map::default(); solver_nogoods.len()];
    for nogood_id in 0..solver_nogoods.len() {
        for variable_id in 0..number_of_variables {
            if let Some(sign) = solver_nogoods[nogood_id][variable_id] {
                var_to_nogoods[variable_id].insert(nogood_id, sign);
                nogoods_to_var[nogood_id].insert(variable_id, sign);
            }
        }
    }

    let mut solver = Solver {
        tight: true,
        number_of_variables,
        assignments: vec![None, Some(true), None],
        decisions: vec![Literal { id: 1, sign: true }],
        watch_lists: vec![],
        nogoods: solver_nogoods,
        var_to_nogoods,
        nogoods_to_var,
        decision_level: 0,
        assignments_log: vec![(None, None, 0); number_of_variables],
        chronological_backtracking_level: 0,
    };
    solver.watch_lists = create_watch_lists(&solver.nogoods);
    solver.unit_propagation();
    let res = &solver.assignments;
    assert_eq!(*res, vec![None, Some(true), Some(true)]);
}

#[test]
fn test_unit_propagation_conflict() {
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
            vec![Literal { id: 1, sign: true }, Literal { id: 2, sign: true }],
        ],
    };
    let mut solver = builder.build();

    mock_decide(&mut solver); // assign Literal(0)
    let prop_result = solver.unit_propagation();
    if let PropagationResult::Conflict(nogood) = prop_result {
        assert_eq!(nogood, vec![None, Some(true), Some(true)]);
        let top_level_conflict = solver.is_top_level_conflict(&nogood);
        assert_eq!(top_level_conflict, false);
        let (uip, sigma, k) = solver.conflict_resolution(&nogood);
        assert_eq!(uip, vec![Some(true), None, None]);
        assert_eq!(sigma, Literal { id: 0, sign: true });
        if solver.chronological_backtracking_level > k {
            solver.decision_level = solver.chronological_backtracking_level;
        } else {
            solver.decision_level = k;
        }
        eprintln!("new_decision_level: {}", solver.decision_level);
        solver.backjump();

        // add complement of sigma
        solver.assignments[sigma.id] = Some(!sigma.sign);
        solver.assignments_log[sigma.id] = (Some(!sigma.sign), None, k);
        solver.record_nogood(uip);
        let res = solver.unit_propagation();
        assert_eq!(res, PropagationResult::Ok);
        assert_eq!(solver.assignments, vec![Some(false), None, None]);

        mock_decide2(&mut solver); // assign Literal(2)

        let res = solver.unit_propagation();
        assert_eq!(res, PropagationResult::Ok);
        assert_eq!(
            solver.assignments,
            vec![Some(false), Some(false), Some(true)]
        );

        assert_eq!(solver.assignment_complete(), true);
    }
}

#[test]
pub fn test_solve_1() {
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
            vec![Literal { id: 1, sign: true }, Literal { id: 2, sign: true }],
        ],
    };
    let mut solver = builder.build();

    let mut solutions = solver.solve();
    let res = solutions.next();
    assert_eq!(
        res,
        Some(SolveResult::Sat(vec![Some(false), Some(false), Some(true)]))
    );
    let res = solutions.next();
    assert_eq!(
        res,
        Some(SolveResult::Sat(vec![
            Some(false),
            Some(false),
            Some(false)
        ]))
    );
    let res = solutions.next();
    assert_eq!(res, None);
}
#[test]
pub fn test_solve_unsat_1() {
    let builder = Builder {
        nogoods: vec![
            vec![Literal { id: 0, sign: true }],
            vec![Literal { id: 0, sign: false }],
        ],
    };
    let mut solver = builder.build();

    let mut solutions = solver.solve();
    let res = solutions.next();
    assert_eq!(res, Some(SolveResult::UnSat));
    let res = solutions.next();
    assert_eq!(res, None);
}
#[test]
pub fn test_solve_unsat_2() {
    let builder = Builder {
        nogoods: vec![
            vec![Literal { id: 1, sign: true }],
            vec![Literal { id: 1, sign: false }],
        ],
    };
    let mut solver = builder.build();

    let mut solutions = solver.solve();
    let res = solutions.next();
    assert_eq!(res, Some(SolveResult::UnSat));
    let res = solutions.next();
    assert_eq!(res, None);
}
