use crate::solver::{Literal, Map, Solver, WatchList};
use aspif::AspifProgram;
use log::debug;
use string_interner::symbol::SymbolU32;
use string_interner::StringInterner;

#[derive(Default)]
pub struct LiteralMapper {
    aspif_literals: Map<u64, usize>,
    bodies: Map<Vec<Literal>, usize>,
    literal_count: usize,
}
impl LiteralMapper {
    pub fn u64_to_solver_literal(&mut self, a: &u64) -> Literal {
        if let Some((_key, value)) = self.aspif_literals.get_key_value(a) {
            Literal {
                id: *value,
                sign: true,
            }
        } else {
            self.aspif_literals.insert(*a, self.literal_count);
            let literal = Literal {
                id: self.literal_count,
                sign: true,
            };
            self.literal_count += 1;
            literal
        }
    }
    pub fn i64_to_solver_literal(&mut self, a: &i64) -> Literal {
        if *a > 0 {
            let b = *a as u64;
            if let Some((_key, value)) = self.aspif_literals.get_key_value(&b) {
                Literal {
                    id: *value,
                    sign: true,
                }
            } else {
                self.literal_count += 1;
                self.aspif_literals.insert(b as u64, self.literal_count);
                Literal {
                    id: self.literal_count,
                    sign: true,
                }
            }
        } else {
            let b = -a as u64;
            if let Some((_key, value)) = self.aspif_literals.get_key_value(&b) {
                Literal {
                    id: *value,
                    sign: false,
                }
            } else {
                self.aspif_literals.insert(b as u64, self.literal_count);
                let literal = Literal {
                    id: self.literal_count,
                    sign: false,
                };
                self.literal_count += 1;
                literal
            }
        }
    }
    pub fn body2solver_literal(&mut self, a: &[Literal]) -> Literal {
        if let Some((_key, value)) = self.bodies.get_key_value(a) {
            Literal {
                id: *value,
                sign: true,
            }
        } else {
            self.literal_count += 1;
            self.bodies.insert(a.to_owned(), self.literal_count);
            Literal {
                id: self.literal_count,
                sign: true,
            }
        }
    }
}

pub type SymbolMapper = Map<Vec<Literal>, SymbolU32>;

pub fn insert_into_symbol_mapper(
    symbol_mapper: &mut SymbolMapper,
    literal_mapper: &mut LiteralMapper,
    symbol: SymbolU32,
    condition: &[i64],
) {
    let mut new_condition = vec![];
    for e in condition {
        new_condition.push(literal_mapper.i64_to_solver_literal(e));
    }
    // TODO: This is buggy if there could be multiple symbols with the same condition
    // q :- not p.
    // p :- not q.
    // #show t:p.
    symbol_mapper.insert(new_condition, symbol);
}

pub struct Builder {
    pub(crate) nogoods: Vec<Vec<Literal>>,
}
impl Builder {
    pub fn from_aspif(aspif_program: &AspifProgram) -> (Self, SymbolMapper, StringInterner) {
        let mut interner = StringInterner::default();
        let mut literal_mapper = LiteralMapper::default();
        let mut symbol_mapper = SymbolMapper::default();

        let mut nogoods = vec![];

        for statement in &aspif_program.statements {
            match statement {
                aspif::Statement::Rule(rule) => {
                    // create rule nogood
                    let body_clause = match &rule.body {
                        aspif::Body::NormalBody { elements } => {
                            // create clause that makes the body true
                            let mut body_clause = vec![];
                            for e in elements {
                                body_clause.push(literal_mapper.i64_to_solver_literal(e));
                            }
                            body_clause.sort();
                            body_clause
                        }
                        aspif::Body::WeightBody {
                            lowerbound: _,
                            elements: _,
                        } => {
                            panic!("Unsupported Body")
                        }
                    };
                    match &rule.head {
                        aspif::Head::Disjunction { elements } => {
                            // create rule nogood
                            let mut nogood = vec![];
                            for e in elements {
                                nogood.push(literal_mapper.u64_to_solver_literal(e))
                            }
                            nogood.push(literal_mapper.body2solver_literal(&body_clause));
                            debug!("Nogood: {nogood:?}");
                            nogoods.push(nogood)
                        }
                        aspif::Head::Choice { elements } => {
                            panic!("Unsupported Head : Choice")
                        }
                    }
                }
                // aspif::Statement::Minimize(_) => todo!(),
                // aspif::Statement::Projection(_) => todo!(),
                aspif::Statement::Output(output) => {
                    let sym = interner.get_or_intern(&output.string);
                    insert_into_symbol_mapper(
                        &mut symbol_mapper,
                        &mut literal_mapper,
                        sym,
                        &output.condition,
                    )
                }
                // aspif::Statement::External { atom, init } => todo!(),
                // aspif::Statement::Assumption(_) => todo!(),
                // aspif::Statement::Heuristic {
                //     modifier,
                //     atom,
                //     k,
                //     priority,
                //     condition,
                // } => todo!(),
                // aspif::Statement::Edge { u, v, condition } => todo!(),
                // aspif::Statement::NumericTheoryTerm { id, w } => todo!(),
                // aspif::Statement::SymbolicTheoryTerm { id, string } => todo!(),
                // aspif::Statement::CompoundTheoryTerm { id, t, terms } => todo!(),
                // aspif::Statement::TheoryAtomElements {
                //     id,
                //     theory_terms,
                //     literals,
                // } => todo!(),
                // aspif::Statement::TheoryAtom {
                //     atom,
                //     symbolic_term,
                //     theory_atom_elements,
                //     theory_operation,
                // } => todo!(),
                // aspif::Statement::TheoryDirective {
                //     symbolic_term,
                //     theory_atom_elements,
                //     theory_operation,
                // } => todo!(),
                // aspif::Statement::Comment => todo!(),
                _ => {
                    panic!("Unsupported Statement");
                }
            }
        }
        (Builder { nogoods }, symbol_mapper, interner)
    }
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
            debug!("Solver nogood: {:?}", solver_nogood);
            solver_nogoods.push(solver_nogood);
        }

        let mut watch_lists = vec![];
        for nogood in &solver_nogoods {
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

// pub struct GroundDisjunctiveRule {
//     head: Vec<u32>,
//     body: Body,
// }
// impl GroundDisjunctiveRule {
//     fn new(head: &[u32], pbody: &[u32], nbody: &[u32]) -> Self {
//         let mut head_atoms = Vec::from(head);
//         head_atoms.dedup();
//         let body = Body::new(pbody, nbody);
//         GroundDisjunctiveRule {
//             head: head_atoms,
//             body,
//         }
//     }
// }
// #[derive(PartialEq, Clone, Debug)]
// pub enum Body {
//     // Body contains a Contradiction and can never be satisfied
//     Contradiction,
//     Conditions {
//         positive_body: Vec<u32>,
//         negative_body: Vec<u32>,
//     },
// }
// impl Body {
//     fn new(pbody: &[u32], nbody: &[u32]) -> Self {
//         let mut positive_body = Vec::from(pbody);
//         positive_body.dedup();
//         let mut negative_body = Vec::from(nbody);
//         negative_body.dedup();
//         for a1 in &negative_body {
//             for a2 in &positive_body {
//                 if a1 == a2 {
//                     return Body::Contradiction;
//                 }
//             }
//         }
//         Body::Conditions {
//             positive_body,
//             negative_body,
//         }
//     }
// }
// type SolversAtoms = u32;
// fn atoms(program: &[GroundDisjunctiveRule]) -> Vec<SolversAtoms> {
//     Vec::default()
// }
// fn bodies(program: &[GroundDisjunctiveRule]) -> Vec<SolversAtoms> {
//     Vec::default()
// }
