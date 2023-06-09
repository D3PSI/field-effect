use std::{error::Error, fs::remove_file, path::PathBuf};

use clap::Parser;

use field_effect::{
    load_circuit, store_circuit, Circuit, CircuitElement, LogicFunction, LogicGate, LogicLevel,
    Wire,
};

#[derive(Parser)]
struct FieldEffectArgs {}

fn main() -> Result<(), Box<dyn Error>> {
    let _args = FieldEffectArgs::parse();

    let mut circuit = Circuit::new();

    let mut first_and_gate = LogicGate::new(LogicFunction::AND);
    let mut second_and_gate = LogicGate::new(LogicFunction::AND);
    let mut not_gate = LogicGate::new(LogicFunction::NOT);
    let input_one = Wire::new(LogicLevel::One);
    let input_two = Wire::new(LogicLevel::One);
    let output_one = Wire::new(LogicLevel::Zero);
    let output_two = Wire::new(LogicLevel::Zero);
    let output_three = Wire::new(LogicLevel::Zero);
    first_and_gate.add_input(input_one.clone());
    first_and_gate.add_output(output_one.clone());
    second_and_gate.add_input(input_two.clone());
    second_and_gate.add_input(output_one.clone());
    second_and_gate.add_output(output_two.clone());
    not_gate.add_input(output_two.clone());
    not_gate.add_output(output_three.clone());
    first_and_gate.add_input(output_three.clone());

    circuit.add_input(input_one.clone());
    circuit.add_input(input_two.clone());
    circuit.add_output(output_two.clone());
    circuit.add_element(first_and_gate);
    circuit.add_element(second_and_gate);
    circuit.add_element(not_gate);

    let path = &PathBuf::from("./serde.json");
    store_circuit(path, *Box::new(circuit))?;
    let circuit = load_circuit(path)?;
    dbg!(&circuit);

    remove_file(path)?;

    Ok(())
}
