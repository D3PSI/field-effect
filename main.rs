use std::{cell::RefCell, error::Error, path::PathBuf, rc::Rc};

use clap::Parser;

use field_effect::{simulate_circuit, LogicFunction, LogicGate, LogicLevel, Wire};

#[derive(Parser)]
struct FieldEffectArgs {}

fn main() -> Result<(), Box<dyn Error>> {
    let _args = FieldEffectArgs::parse();

    let mut and_gate = LogicGate::new(LogicFunction::AND);
    let input_one = Wire::new(LogicLevel::One);
    let input_two = Wire::new(LogicLevel::One);
    let output = Wire::new(LogicLevel::Zero);
    and_gate.add_input(Rc::downgrade(&input_one));
    and_gate.add_input(Rc::downgrade(&input_two));
    and_gate.add_output(output.clone());

    simulate_circuit(Box::new(and_gate))?;

    println!("{}", output.borrow().read());

    Ok(())
}
