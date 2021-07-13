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

#[derive(Clone, Debug)]
pub(crate) struct WatchList {
    left_watch: usize,
    right_watch: usize,
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Bla {
    True,
    False,
    Nothing,
}
// type Clause = Vec<Literal>;
type Clause = Vec<Bla>;

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
enum PropagationResult {
    Ok,
    Conflict(Clause),
}
/// Map implementation used by the library.
pub type Map<K, V> = rustc_hash::FxHashMap<K, V>;
pub type Assignments = Vec<Literal>;

pub struct Builder {
    pub(crate) nogoods: Vec<Vec<Literal>>,
}
impl Builder {
    pub fn build(self) -> Solver {
        let mut number_of_variables = 0;
        for clause in &self.nogoods {
            for lit in clause {
                if lit.id() + 1 > number_of_variables {
                    number_of_variables = lit.id() + 1;
                }
            }
        }
        let mut solver_nogoods = vec![];
        for clause in self.nogoods {
            let mut solver_clause = vec![Bla::Nothing; number_of_variables];
            for id in 0..number_of_variables {
                if clause.contains(&Literal { id, sign: true }) {
                    solver_clause[id] = Bla::True;
                } else if clause.contains(&Literal { id, sign: false }) {
                    solver_clause[id] = Bla::False;
                }
            }
            solver_nogoods.push(solver_clause);
        }
        Solver {
            tight: true,
            number_of_variables,
            assignments: vec![],
            decisions: vec![],
            watch_lists: vec![],
            nogoods: solver_nogoods,
            decision_level: 0,
            chronological_backtracking_level: 0,
            derivations: Map::default(),
        }
    }
}
#[derive(Clone, Debug)]
pub struct Solver {
    tight: bool,
    number_of_variables: usize,
    assignments: Assignments,
    decisions: Vec<Literal>,
    watch_lists: Vec<WatchList>,
    nogoods: Vec<Clause>,
    decision_level: usize,
    chronological_backtracking_level: usize,
    derivations: Map<Literal, (Option<usize>, usize)>,
}
impl Solver {
    pub fn solve(&mut self) -> impl Iterator<Item = SolveResult> + '_ {
        Gen::new(|co| async move {
            self.create_watch_lists();
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
                } else if self.assignment_complete() {
                    co.yield_(SolveResult::Sat(self.assignments.clone())).await;

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

    fn create_watch_lists(&mut self) {
        self.watch_lists.clear();
        for nogood in &self.nogoods {
            eprintln!("nogood: {:?}", nogood);
            //  TODO: special handling for nogoods of size 1
            let mut left_watch = 0;
            while nogood[left_watch] == Bla::Nothing {
                left_watch += 1;
            }
            let mut right_watch = nogood.len() - 1;
            while nogood[right_watch] == Bla::Nothing {
                right_watch -= 1;
            }
            self.watch_lists.push(WatchList {
                left_watch,
                right_watch,
            })
        }
    }

    /// analyze conflict and learn UIP nogood
    fn conflict_resolution(&self, nogood: &[Bla]) -> (Clause, Literal, usize) {
        let mut nogood = nogood.to_owned();
        let sigma = loop {
            eprintln!("delta:{:?}", nogood);
            let mut iter = nogood.iter().enumerate();
            let (sigma, nogood_index, decision_level_sigma) = loop {
                // let mut last: Literal;
                match iter.next() {
                    Some((id, &Bla::True)) => {
                        let literal = Literal { id, sign: true };
                        if let (Some(index), decision_level) =
                            self.derivations.get(&literal).unwrap()
                        {
                            break (literal, Some(index), decision_level);
                        }
                    }
                    Some((id, &Bla::False)) => {
                        let literal = Literal { id, sign: false };
                        if let (Some(index), decision_level) =
                            self.derivations.get(&literal).unwrap()
                        {
                            break (literal, Some(index), decision_level);
                        }
                    }
                    Some((_, &Bla::Nothing)) => {}
                    None => {
                        //no good contains only decision literals
                        iter = nogood.iter().enumerate();
                        let res: (Literal, Option<&usize>, &usize) = loop {
                            match iter.next() {
                                Some((id, &Bla::True)) => {
                                    let literal = Literal { id, sign: true };
                                    if let (None, decision_level) =
                                        self.derivations.get(&literal).unwrap()
                                    {
                                        break (literal, None, decision_level);
                                    }
                                }
                                Some((id, &Bla::False)) => {
                                    let literal = Literal { id, sign: false };
                                    if let (None, decision_level) =
                                        self.derivations.get(&literal).unwrap()
                                    {
                                        break (literal, None, decision_level);
                                    }
                                }
                                Some((_, &Bla::Nothing)) => {}
                                None => {
                                    unreachable!()
                                }
                            }
                        };
                        break res;
                    }
                }
            };
            eprintln!("sigma: {:?}", sigma);

            if let None = nogood_index {
                // sigma is a decision_literal all other literals are also decision lit
                eprintln!("should be uip")
            }

            // a nogood is a unique implication point if there is no other literal
            // from the same decision level as sigma
            let mut iter = nogood.iter().enumerate();
            let unique = loop {
                match iter.next() {
                    Some((id, &Bla::True)) => {
                        let literal = Literal { id, sign: true };
                        if sigma != literal {
                            eprintln!("literal: {:?}", literal);
                            let (_, decision_level) = self.derivations.get(&literal).unwrap();
                            if decision_level == decision_level_sigma {
                                break false;
                            }
                        }
                    }
                    Some((id, &Bla::False)) => {
                        let literal = Literal { id, sign: false };
                        if sigma != literal {
                            let (_, decision_level) = self.derivations.get(&literal).unwrap();
                            if decision_level == decision_level_sigma {
                                break false;
                            }
                        }
                    }
                    Some((_, &Bla::Nothing)) => {}
                    None => break true,
                }
            };
            if unique {
                break sigma;
            }
            eprintln!("not unique");
            if let Some(nogood_index) = nogood_index {
                let reason = &self.nogoods[*nogood_index];
                eprintln!("reason: {:?}", reason);
                let res = resolve(&nogood, &sigma, reason);
                nogood = res;
            } else {
                // sigma is a decision_literals
                // the reason is empty
                let reason = vec![Bla::Nothing; self.number_of_variables];
                eprintln!("reason: {:?}", reason);
                let res = resolve(&nogood, &sigma, &reason);
                nogood = res;
            }
        };
        let mut k = 0;
        for (id, bla) in nogood.iter().enumerate() {
            match bla {
                Bla::True => {
                    let literal = Literal { id, sign: true };
                    if literal != sigma {
                        let (_, decision_level) = self.derivations.get(&literal).unwrap();
                        if *decision_level > k {
                            k = *decision_level
                        }
                    }
                }
                Bla::False => {
                    let literal = Literal { id, sign: false };
                    if literal != sigma {
                        let (_, decision_level) = self.derivations.get(&literal).unwrap();
                        if *decision_level > k {
                            k = *decision_level
                        }
                    }
                }
                Bla::Nothing => {}
            }
        }
        eprintln!("k: {}", k);
        eprintln!("sigma: {:?}", sigma);
        (nogood, sigma, k)
    }
    /// increase decision level assign truth value to a previously unassigned variable
    fn decide(&mut self) {
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
        for id in 0..self.number_of_variables {
            if self.assignments.contains(&Literal { id, sign: true }) {
                continue;
            }
            if self.assignments.contains(&Literal { id, sign: false }) {
                continue;
            }
            return Literal { id, sign: true };
        }
        panic!("Logic error: calling choose on complete assignment-");
    }

    /// return true if all variables have a truth value assignment
    fn assignment_complete(&self) -> bool {
        for id in 0..self.number_of_variables {
            if self.assignments.contains(&Literal { id, sign: true }) {
                continue;
            }
            if self.assignments.contains(&Literal { id, sign: false }) {
                continue;
            }
            return false;
        }
        true
    }
    /// return true if there is a conflich on decision level 0
    fn is_top_level_conflict(&self, nogood: &[Bla]) -> bool {
        for (id, assignment) in nogood.iter().enumerate() {
            match assignment {
                Bla::True => {
                    let literal = Literal { id, sign: true };
                    let (_id, decision_level) = self.derivations.get(&literal).unwrap();
                    if *decision_level > 0 {
                        return false;
                    }
                }
                Bla::False => {
                    let literal = Literal { id, sign: false };
                    let (_id, decision_level) = self.derivations.get(&literal).unwrap();
                    if *decision_level > 0 {
                        return false;
                    }
                }
                Bla::Nothing => {}
            }
        }
        true
    }
    /// backjump to decision level x and rewind assignment
    fn backjump(&mut self) {
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

        if !self.assignments.is_empty() {
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
        let mut propagation_queue: VecDeque<Literal> = self.assignments.iter().cloned().collect();

        loop {
            if let Some(p) = propagation_queue.pop_front() {
                eprintln!("prp: {:?}", p);
                for (index, watch_list) in self.watch_lists.iter_mut().enumerate() {
                    // eprintln!("index:{}",index);
                    eprintln!(
                        "ng: {} {} {:?}",
                        watch_list.left_watch, watch_list.right_watch, self.nogoods[index]
                    );
                    if watch_list.left_watch == p.id() {
                        if p.sign() == true
                            && self.nogoods[index][watch_list.left_watch] == Bla::True
                        {
                            watch_list.left_watch += 1;
                        }
                        if p.sign() == false
                            && self.nogoods[index][watch_list.left_watch] == Bla::False
                        {
                            watch_list.left_watch += 1;
                        }
                    }
                    if watch_list.right_watch == p.id() {
                        if p.sign() == true
                            && self.nogoods[index][watch_list.right_watch] == Bla::True
                        {
                            watch_list.right_watch -= 1;
                        }
                        if p.sign() == false
                            && self.nogoods[index][watch_list.right_watch] == Bla::False
                        {
                            watch_list.right_watch -= 1;
                        }
                    }

                    if watch_list.left_watch > watch_list.right_watch {
                        eprintln!("conflicting nogood: {:?}", self.nogoods[index]);
                        return PropagationResult::Conflict(self.nogoods[index].clone());
                    }
                    if watch_list.left_watch == watch_list.right_watch {
                        let res = match self.nogoods[index][watch_list.right_watch] {
                            Bla::True => Literal {
                                id: watch_list.right_watch,
                                sign: true,
                            },
                            Bla::False => Literal {
                                id: watch_list.right_watch,
                                sign: false,
                            },
                            _ => unreachable!(),
                        };
                        if self.assignments.contains(&res) {
                            eprintln!("conflicting nogood: {:?}", self.nogoods[index]);
                            return PropagationResult::Conflict(self.nogoods[index].clone());
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
                for (index, watch_list) in self.watch_lists.iter().enumerate() {
                    // eprintln!("index:{}",index);
                    if watch_list.left_watch == watch_list.right_watch {
                        let res = match self.nogoods[index][watch_list.right_watch] {
                            Bla::True => Literal {
                                id: watch_list.right_watch,
                                sign: true,
                            },
                            Bla::False => Literal {
                                id: watch_list.right_watch,
                                sign: false,
                            },
                            _ => unreachable!(),
                        };
                        if self.assignments.contains(&res) {
                            eprintln!("conflicting nogood: {:?}", self.nogoods[index]);
                            return PropagationResult::Conflict(self.nogoods[index].clone());
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
            }
            if propagation_queue.is_empty() {
                return PropagationResult::Ok;
            }
        }
    }
}

fn resolve(nogood: &[Bla], sigma: &Literal, reason: &[Bla]) -> Clause {
    // assert sigma in nogood and reason
    let mut res = vec![];
    for (id, bla) in nogood.iter().enumerate() {
        match bla {
            Bla::True => {
                let literal = Literal { id, sign: true };
                if literal != *sigma {
                    res.push(Bla::True)
                } else {
                    res.push(Bla::Nothing)
                }
            }
            Bla::False => {
                let literal = Literal { id, sign: false };
                if literal != *sigma {
                    res.push(Bla::False)
                } else {
                    res.push(Bla::Nothing)
                }
            }
            Bla::Nothing => res.push(Bla::Nothing),
        }
    }
    let neg_sigma = sigma.negate();
    for (id, bla) in reason.iter().enumerate() {
        match bla {
            Bla::True => {
                let literal = Literal { id, sign: true };
                if literal != neg_sigma {
                    res[id] = Bla::True;
                }
            }
            Bla::False => {
                let literal = Literal { id, sign: false };
                if literal != neg_sigma {
                    res[id] = Bla::False;
                }
            }
            Bla::Nothing => {}
        }
    }
    res
}

#[test]
fn test_unit_propagation() {
    let mut solver = Solver {
        tight: true,
        number_of_variables: 3,
        assignments: vec![Literal { id: 1, sign: true }],
        decisions: vec![Literal { id: 1, sign: true }],
        watch_lists: vec![],
        nogoods: vec![vec![Bla::Nothing, Bla::True, Bla::False]],
        decision_level: 0,
        chronological_backtracking_level: 0,
        derivations: Map::default(),
    };
    solver.create_watch_lists();
    solver.unit_propagation();
    let res = &solver.assignments;
    assert_eq!(
        *res,
        vec![Literal { id: 1, sign: true }, Literal { id: 2, sign: true }]
    );
}

/// only for testing
fn mock_decide(solver: &mut Solver) {
    solver.decision_level += 1;
    let decision_literal = Literal { id: 0, sign: true };
    solver.assignments.push(decision_literal);
    solver
        .derivations
        .insert(decision_literal, (None, solver.decision_level));
}

/// only for testing
fn mock_decide2(solver: &mut Solver) {
    solver.decision_level += 1;
    let decision_literal = Literal { id: 2, sign: true };
    solver.assignments.push(decision_literal);
    solver
        .derivations
        .insert(decision_literal, (None, solver.decision_level));
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
    solver.create_watch_lists();
    let prop_result = solver.unit_propagation();
    if let PropagationResult::Conflict(nogood) = prop_result {
        assert_eq!(nogood, vec![Bla::Nothing, Bla::True, Bla::True]);
        let top_level_conflict = solver.is_top_level_conflict(&nogood);
        assert_eq!(top_level_conflict, false);
        let (uip, sigma, k) = solver.conflict_resolution(&nogood);
        assert_eq!(uip, vec![Bla::True, Bla::Nothing, Bla::Nothing]);
        assert_eq!(sigma, Literal { id: 0, sign: true });
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
        assert_eq!(solver.assignments, vec![Literal { id: 0, sign: false }]);

        mock_decide2(&mut solver); // assign Literal(2)

        let res = solver.unit_propagation();
        assert_eq!(res, PropagationResult::Ok);
        assert_eq!(
            solver.assignments,
            vec![
                Literal { id: 0, sign: false },
                Literal { id: 2, sign: true },
                Literal { id: 1, sign: false }
            ]
        );

        assert_eq!(solver.assignment_complete(), true);
    }
}

#[test]
pub fn test_solve1() {
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
        Some(SolveResult::Sat(vec![
            Literal { id: 1, sign: false },
            Literal { id: 0, sign: false },
            Literal { id: 2, sign: true }
        ]))
    );
    let res = solutions.next();
    assert_eq!(
        res,
        Some(SolveResult::Sat(vec![
            Literal { id: 2, sign: false },
            Literal { id: 0, sign: false },
            Literal { id: 1, sign: false }
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
