use std::error::Error;

use clap::Parser;

use field_effect::{simulate, LogicFunction, LogicGate, LogicLevel, Wire};

#[derive(Parser)]
struct FieldEffectArgs {}

fn main() -> Result<(), Box<dyn Error>> {
    let _args = FieldEffectArgs::parse();

    let mut and_gate = LogicGate::new(LogicFunction::AND);
    let input_one = Wire::new(LogicLevel::One);
    let input_two = Wire::new(LogicLevel::One);
    let output = Wire::new(LogicLevel::Zero);
    and_gate.add_input(&input_one);
    and_gate.add_input(&input_two);
    and_gate.add_output(output.clone());

    simulate(and_gate)?;

    println!("{}", output.borrow().read());

    Ok(())
}
