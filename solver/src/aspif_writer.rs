use std::io::Write;

use aspif::{AspifProgram, Statement};
pub fn write_aspif_program(mut out: impl Write, program: &AspifProgram) -> std::io::Result<()> {
    write!(
        out,
        "asp {} {} {}",
        program.header.major, program.header.minor, program.header.revision
    )?;
    if program.header.incremental {
        write!(out, " incremental")?;
    }
    writeln!(out)?;
    for statement in &program.statements {
        write_aspif_statement(&mut out, &statement)?;
    }
    Ok(())
}
fn write_aspif_statement(mut out: impl Write, statement: &Statement) -> std::io::Result<()> {
    match statement {
        Statement::Rule(rule) => write_aspif_rule(&mut out, rule)?,
        Statement::Minimize(m) => todo!(),
        Statement::Projection(_) => todo!(),
        Statement::Output(_) => todo!(),
        Statement::External { atom, init } => todo!(),
        Statement::Assumption(_) => todo!(),
        Statement::Heuristic {
            modifier,
            atom,
            k,
            priority,
            condition,
        } => todo!(),
        Statement::Edge { u, v, condition } => todo!(),
        Statement::NumericTheoryTerm { id, w } => todo!(),
        Statement::SymbolicTheoryTerm { id, string } => todo!(),
        Statement::CompoundTheoryTerm { id, t, terms } => todo!(),
        Statement::TheoryAtomElements {
            id,
            theory_terms,
            literals,
        } => todo!(),
        Statement::TheoryAtom {
            atom,
            symbolic_term,
            theory_atom_elements,
            theory_operation,
        } => todo!(),
        Statement::TheoryDirective {
            symbolic_term,
            theory_atom_elements,
            theory_operation,
        } => todo!(),
        Statement::Comment => todo!(),
    }
    writeln!(out)?;
    Ok(())
}

fn write_aspif_rule(mut out: impl Write, rule: &aspif::Rule) -> std::io::Result<()> {
    match &rule.head {
        aspif::Head::Disjunction { elements } => {
            write!(&mut out, "1 0 {}", elements.len())?;
            for e in elements {
                write!(&mut out, " {}", e)?;
            }
        }
        aspif::Head::Choice { elements } => todo!(),
    }
    match &rule.body {
        aspif::Body::NormalBody { elements } => {
            write!(&mut out, " 0 {}", elements.len())?;
            for e in elements {
                write!(&mut out, " {e}")?;
            }
        }
        aspif::Body::WeightBody {
            lowerbound,
            elements,
        } => todo!(),
    };
    Ok(())
}
