use crate::solver::{Literal, Map, Solver, WatchList};
use aspif::AspifProgram;
use log::{debug, info};
use string_interner::symbol::SymbolU32;
use string_interner::StringInterner;

#[derive(Default)]
pub struct LiteralMapper {
    aspif_literals: Map<u64, usize>,
    pub bodies: Map<Vec<Literal>, usize>,
    literal_count: usize,
    supports: Map<usize, Vec<Literal>>,
}
impl LiteralMapper {
    fn u64_to_solver_literal(&mut self, a: &u64) -> Literal {
        if let Some((_key, value)) = self.aspif_literals.get_key_value(a) {
            Literal::new(*value, true)
        } else {
            self.aspif_literals.insert(*a, self.literal_count);
            let literal = Literal::new(self.literal_count, true);
            self.literal_count += 1;
            literal
        }
    }
    fn i64_to_solver_literal(&mut self, a: &i64) -> Literal {
        if *a >= 0 {
            let b = *a as u64;
            if let Some((_key, value)) = self.aspif_literals.get_key_value(&b) {
                Literal::new(*value, true)
            } else {
                self.aspif_literals.insert(b, self.literal_count);
                let literal = Literal::new(self.literal_count, true);
                self.literal_count += 1;
                literal
            }
        } else {
            let b = -a as u64;
            if let Some((_key, value)) = self.aspif_literals.get_key_value(&b) {
                Literal::new(*value, false)
            } else {
                self.aspif_literals.insert(b, self.literal_count);
                let literal = Literal::new(self.literal_count, false);
                self.literal_count += 1;
                literal
            }
        }
    }
    fn body2solver_literal(&mut self, body: &[Literal]) -> Literal {
        if let Some((_key, value)) = self.bodies.get_key_value(body) {
            Literal::new(*value, true)
        } else {
            self.bodies.insert(body.to_owned(), self.literal_count);
            let literal = Literal::new(self.literal_count, true);
            self.literal_count += 1;
            literal
        }
    }
    /// Returns corresponding solver literal if the body already exist in the LiteralMap
    fn get_body_literal(&mut self, body: &[Literal]) -> Option<Literal> {
        self.bodies
            .get(body)
            .map(|value| Literal::new(*value, true))
    }

    /// This function creates rule nogoods as in Definition 1 in *Advanced Conflict-Driven Disjunctive Answer Set Solving*
    /// It also collects support body clauses for atom wise shifted rules as in *Advanced Conflict-Driven Disjunctive Answer Set Solving*
    fn write_rule_nogood(&mut self, rule: &aspif::Rule, nogoods: &mut Vec<Vec<Literal>>) {
        let body_clause = match &rule.body {
            aspif::Body::NormalBody { elements } => {
                // Create clause that makes the body true
                let mut body_clause = vec![];
                for e in elements {
                    body_clause.push(self.i64_to_solver_literal(e));
                }
                // TODO: is sort and dedup necessary
                body_clause.sort();
                body_clause.dedup();
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
                let ori_body_lit = self.body2solver_literal(&body_clause);
                // Create rule nogood
                let mut rule_nogood = vec![];
                for e in elements {
                    let head_lit = self.u64_to_solver_literal(e);
                    let neg_head_lit = head_lit.negate();
                    rule_nogood.push(neg_head_lit)
                }
                rule_nogood.push(ori_body_lit);

                debug!("Rule nogood: {rule_nogood:?}");
                nogoods.push(rule_nogood);

                // Shift head atoms to the new body
                for (idx, e) in elements.iter().enumerate() {
                    let new_head_lit = self.u64_to_solver_literal(e);
                    let mut new_body = body_clause.clone();
                    let mut new_body2 = vec![];
                    for (idx2, _e) in elements.iter().enumerate() {
                        if idx2 != idx {
                            let lit2 = self.u64_to_solver_literal(e);
                            let neg_lit = lit2.negate();
                            new_body.push(neg_lit);
                            new_body2.push(neg_lit);
                        }
                    }
                    let new_body_lit = if let Some(lit) = self.get_body_literal(&new_body) {
                        lit
                    } else {
                        self.body2solver_literal(&new_body2)
                    };
                    self.supports
                        .entry(new_head_lit.id())
                        .and_modify(|e| e.push(new_body_lit))
                        .or_insert(vec![new_body_lit]);
                    debug!("Support for {new_head_lit:?}: {new_body_lit:?}");
                }
            }
            aspif::Head::Choice { elements } => {
                panic!("Unsupported Head : Choice")
            }
        };
    }

    /// This function creates support nogoods as in Definition 2 in *Advanced Conflict-Driven Disjunctive Answer Set Solving*
    fn write_support_nogoods(&self, nogoods: &mut Vec<Vec<Literal>>) {
        for (k, support) in &self.supports {
            let mut support_nogood = vec![];
            // Create support nogoods
            support_nogood.push(Literal::new(*k, true));
            for lit in support {
                let neg_lit = lit.negate();
                support_nogood.push(neg_lit);
            }
            debug!("Support nogood: {:?}", support_nogood);
            nogoods.push(support_nogood);
        }
    }

    /// This function creates conjunction nogoods as in Definition 3 in *Advanced Conflict-Driven Disjunctive Answer Set Solving*
    fn write_conjuction_nogoods(&self, nogoods: &mut Vec<Vec<Literal>>) {
        for (body, lit_id) in &self.bodies {
            let mut conjunction_nogood1 = vec![];
            let lit = Literal::new(*lit_id, true);
            let neg_lit = Literal::new(*lit_id, false);
            conjunction_nogood1.push(neg_lit);
            for l in body.iter() {
                conjunction_nogood1.push(*l);
                let mut conjunction_nogoodn = vec![];
                conjunction_nogoodn.push(lit);
                for l2 in body.iter() {
                    if *l == *l2 {
                        conjunction_nogoodn.push(l.negate())
                    } else {
                        conjunction_nogoodn.push(*l2)
                    }
                }
                nogoods.push(conjunction_nogoodn);
            }
            nogoods.push(conjunction_nogood1);
        }
    }
}

#[test]
fn test_aspif_i64_to_solver_literal() {
    let mut lm = LiteralMapper::default();
    let l0 = Literal::new(0, true);
    let l1 = Literal::new(1, false);
    let l2 = Literal::new(0, false);
    let l3 = Literal::new(1, true);
    let sl0 = lm.i64_to_solver_literal(&12);
    let sl1 = lm.i64_to_solver_literal(&-2);
    let sl2 = lm.i64_to_solver_literal(&-12);
    let sl3 = lm.i64_to_solver_literal(&-2);
    let sl4 = lm.i64_to_solver_literal(&2);
    assert_eq!(l0, sl0);
    assert_eq!(l1, sl1);
    assert_eq!(l2, sl2);
    assert_eq!(l1, sl3);
    assert_eq!(l3, sl4);
}
#[test]
fn test_aspif_u64_to_solver_literal() {
    let mut lm = LiteralMapper::default();
    let l0 = Literal::new(0, true);
    let l1 = Literal::new(1, false);
    let l2 = Literal::new(0, false);
    let l3 = Literal::new(1, true);
    let sl0 = lm.u64_to_solver_literal(&12);
    let sl1 = lm.i64_to_solver_literal(&-2);
    let sl2 = lm.i64_to_solver_literal(&-12);
    let sl3 = lm.u64_to_solver_literal(&2);

    assert_eq!(l0, sl0);
    assert_eq!(l1, sl1);
    assert_eq!(l2, sl2);
    assert_eq!(l3, sl3);
}
#[test]
fn test_body_to_solver_literal() {
    // TODO
    // let mut lm = LiteralMapper::default();
    // let la = Literal::new(0, true);
    // let lb = Literal::new(1, false);
    // let lc = Literal::new(0, false);
    // let ld = Literal::new(1, true);
    // let sl0 = lm.body2solver_literal(&[la,lb]);
    // let sl1 = lm.body2solver_literal(&[lb,lc]);
    // let sl2 = lm.body2solver_literal(&[lc,ld]);
    // let sl3 = lm.body2solver_literal(&[lb,ld]);

    // let l0 = Literal::new(2, true);
    // let l1 = Literal::new(3, true);
    // let l2 = Literal::new(4, true);
    // let l3 = Literal::new(5, true);

    // assert_eq!(l0, sl0);
    // assert_eq!(l1, sl1);
    // assert_eq!(l2, sl2);
    // assert_eq!(l3, sl3);
}

pub type SymbolMapper = Map<Vec<Literal>, SymbolU32>;

fn insert_into_symbol_mapper(
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

use petgraph::algo::tarjan_scc;
use petgraph::graph::{DiGraph, NodeIndex};

/// Create a (directed) positive atom dependency graph
/// The graph will be used to compute scc's which correspond to loops of the program
pub fn graph_from_aspif(aspif_program: &AspifProgram) {
    let mut literal_mapper = LiteralMapper::default();
    let mut positive_atom_dependency_graph: DiGraph<u32, ()> = DiGraph::default();

    for statement in &aspif_program.statements {
        match statement {
            aspif::Statement::Rule(rule) => {
                let body_clause = match &rule.body {
                    aspif::Body::NormalBody { elements } => {
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
                        for body_lit in &body_clause {
                            if body_lit.sign() {
                                for head_atom_id in elements {
                                    while positive_atom_dependency_graph.node_count()
                                        <= *head_atom_id as usize
                                    {
                                        let _a = positive_atom_dependency_graph.add_node(0);
                                    }
                                    let a = NodeIndex::from(*head_atom_id as u32);
                                    while positive_atom_dependency_graph.node_count()
                                        <= body_lit.id()
                                    {
                                        let _a = positive_atom_dependency_graph.add_node(0);
                                    }
                                    let b = NodeIndex::from(body_lit.id() as u32);
                                    positive_atom_dependency_graph.add_edge(a, b, ());
                                }
                            }
                        }
                    }
                    aspif::Head::Choice { elements } => {
                        panic!("Unsupported Head : Choice")
                    }
                }
            }
            // aspif::Statement::Minimize(_) => todo!(),
            // aspif::Statement::Projection(_) => todo!(),
            aspif::Statement::Output(_) => {}
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

    debug!("positive_atom_dependency_graph: {positive_atom_dependency_graph:?}");
    info!("Strongly connected components ...");
    let components = tarjan_scc(&positive_atom_dependency_graph);

    for scc in components {
        debug!("{scc:?}");
    }
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
                    literal_mapper.write_rule_nogood(rule, &mut nogoods);
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
        literal_mapper.write_support_nogoods(&mut nogoods);
        literal_mapper.write_conjuction_nogoods(&mut nogoods);

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
            for (id, item) in solver_nogood.iter_mut().enumerate() {
                if nogood.contains(&Literal::new(id, true)) {
                    *item = Some(true);
                } else if nogood.contains(&Literal::new(id, false)) {
                    *item = Some(false);
                }
            }
            debug!("Solver nogood: {:?}", solver_nogood);
            solver_nogoods.push(solver_nogood);
        }

        let mut watch_lists = vec![];
        for nogood in &solver_nogoods {
            //  TODO: special handling for nogoods of size 1
            let mut left_watch = 0;
            while nogood[left_watch].is_none() {
                left_watch += 1;
            }
            let mut right_watch = nogood.len() - 1;
            while nogood[right_watch].is_none() {
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
            for (variable_id, map) in var_to_nogoods
                .iter_mut()
                .enumerate()
                .take(number_of_variables)
            {
                if let Some(sign) = solver_nogoods[nogood_id][variable_id] {
                    map.insert(nogood_id, sign);
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

#[test]
fn test_create_rule_nogood() {
    let mut lm = LiteralMapper::default();
    let l0 = Literal::new(0, true);
    let l1 = Literal::new(1, false);
    let l2 = Literal::new(2, true);
    let l3 = Literal::new(3, false);

    let mut nogoods = vec![];
    // Rule with empty body and empty head `:-.` the corresponding rule nogood should contain only the literal corresponding to the empty body
    if let aspif::Statement::Rule(rule) = aspif::read_statement_line("1 0 0 0 0").unwrap() {
        lm.write_rule_nogood(&rule, &mut nogoods);
        assert_eq!(nogoods[0], vec![l0])
    }
    // Rule with one head and empty body `a.`
    if let aspif::Statement::Rule(rule) = aspif::read_statement_line("1 0 1 1 0 0").unwrap() {
        lm.write_rule_nogood(&rule, &mut nogoods);
        assert_eq!(nogoods[1], vec![l1, l0])
    }

    // :- not a.
    if let aspif::Statement::Rule(rule) = aspif::read_statement_line("1 0 0 0 1 -1").unwrap() {
        lm.write_rule_nogood(&rule, &mut nogoods);
        assert_eq!(nogoods[2], vec![l2])
    }

    // a :- not a.
    if let aspif::Statement::Rule(rule) = aspif::read_statement_line("1 0 1 1 0 1 -1").unwrap() {
        lm.write_rule_nogood(&rule, &mut nogoods);
        assert_eq!(nogoods[3], vec![l1, l2])
    }

    // b :- not a.
    if let aspif::Statement::Rule(rule) = aspif::read_statement_line("1 0 1 2 0 1 -1").unwrap() {
        lm.write_rule_nogood(&rule, &mut nogoods);
        assert_eq!(nogoods[4], vec![l3, l2])
    }
    // a;b :- not a.
    if let aspif::Statement::Rule(rule) = aspif::read_statement_line("1 0 2 1 2 0 1 -1").unwrap() {
        lm.write_rule_nogood(&rule, &mut nogoods);
        assert_eq!(nogoods[5], vec![l1, l3, l2])
    }
}

#[test]
fn test_collect_atom_support() {
    //TODO
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
