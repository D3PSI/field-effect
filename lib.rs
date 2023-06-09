//! This library root file contains basic definitions of working with logical circuits

use num::Integer;
use serde::{Deserialize, Serialize};
use std::{
    cell::RefCell,
    collections::HashMap,
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::{BufReader, BufWriter, Read, Write},
    ops::{BitAnd, BitOr, BitXor, Neg},
    path::PathBuf,
    rc::Rc,
};
use uuid::Uuid;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub enum LogicLevel {
    Zero = 0,
    One = 1,
}

impl<T: Integer> From<T> for LogicLevel {
    fn from(val: T) -> Self {
        if val == T::zero() {
            return LogicLevel::Zero;
        }
        LogicLevel::One
    }
}

impl Display for LogicLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Zero => 0,
                Self::One => 1,
            }
        )
    }
}

impl BitAnd for LogicLevel {
    type Output = LogicLevel;

    fn bitand(self, rhs: Self) -> Self::Output {
        if rhs == LogicLevel::One && self == LogicLevel::One {
            return LogicLevel::One;
        }
        LogicLevel::Zero
    }
}

impl BitOr for LogicLevel {
    type Output = LogicLevel;

    fn bitor(self, rhs: Self) -> Self::Output {
        if rhs == LogicLevel::One || self == LogicLevel::One {
            return LogicLevel::One;
        }
        LogicLevel::Zero
    }
}

impl BitXor for LogicLevel {
    type Output = LogicLevel;

    fn bitxor(self, rhs: Self) -> Self::Output {
        if rhs == self {
            return LogicLevel::Zero;
        }
        LogicLevel::One
    }
}

impl Neg for LogicLevel {
    type Output = LogicLevel;

    fn neg(self) -> Self::Output {
        if self == LogicLevel::One {
            return LogicLevel::Zero;
        }
        LogicLevel::One
    }
}

#[typetag::serde(tag = "type")]
pub trait CircuitElement: std::fmt::Debug {
    /// returns true if there have not been state updates (the element has settled on a state)
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>>;

    fn elements(&mut self) -> &mut Vec<Box<dyn CircuitElement>>;

    fn add_element(&mut self, element: Box<dyn CircuitElement>);

    fn inputs(&mut self) -> &mut Vec<WireLink>;

    fn outputs(&mut self) -> &mut Vec<WireLink>;

    fn add_input(&mut self, input: WireLink);

    fn add_output(&mut self, output: WireLink);

    fn deduplicate(&mut self, map: &mut HashMap<Uuid, WireLink>) {
        for element in self.elements() {
            element.deduplicate(map);
        }
        let outputs = self.outputs().clone();
        self.outputs().clear();
        for output in outputs {
            let uuid = (*output).borrow().uuid();
            if map.contains_key(&uuid) {
                self.add_output(map.get(&uuid).unwrap().clone());
            } else {
                map.insert(uuid, output.clone());
                self.add_output(output);
            }
        }
        let inputs = self.inputs().clone();
        self.inputs().clear();
        for input in inputs {
            let uuid = (*input).borrow().uuid();
            if map.contains_key(&uuid) {
                self.add_input(map.get(&uuid).unwrap().clone());
            } else {
                map.insert(uuid, input.clone());
                self.add_input(input);
            }
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Wire {
    uuid: Uuid,
    number: Option<usize>,
    value: LogicLevel,
}

impl Wire {
    pub fn new(value: LogicLevel) -> Rc<RefCell<Wire>> {
        let uuid = Uuid::new_v4();
        let number = None;
        Rc::new(RefCell::new(Wire {
            uuid,
            number,
            value,
        }))
    }

    pub fn uuid(&self) -> Uuid {
        self.uuid
    }

    pub fn number(&mut self, number: usize) {
        self.number = Some(number)
    }

    pub fn write(&mut self, value: LogicLevel) {
        self.value = value;
    }

    pub fn read(&self) -> LogicLevel {
        self.value
    }
}

/// Wraps a `Wire` in a `RefCell` for interior mutability
pub type WireRef = RefCell<Wire>;

/// Wraps a `WireRef` in an `Rc` - represents a mutable reference to a wire
pub type WireLink = Rc<WireRef>;

#[derive(Debug, Serialize, Deserialize)]
pub struct Circuit {
    // a circuit owns all of its constituent circuits
    elements: Vec<Box<dyn CircuitElement>>,
    // inputs and outputs are modeled using a wire (which itself is a circuit element that is owned
    // by the circuit)
    inputs: Vec<WireLink>,
    outputs: Vec<WireLink>,
}

impl Default for Circuit {
    fn default() -> Self {
        Circuit {
            elements: vec![],
            inputs: vec![],
            outputs: vec![],
        }
    }
}

impl Circuit {
    pub fn new() -> Box<Circuit> {
        Box::new(Circuit::default())
    }
}

#[typetag::serde]
impl CircuitElement for Circuit {
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>> {
        let mut settled = true;
        for element in self.elements.iter_mut() {
            if !element.propagate()? {
                settled = false;
            }
        }

        Ok(settled)
    }

    fn elements(&mut self) -> &mut Vec<Box<dyn CircuitElement>> {
        &mut self.elements
    }

    fn add_element(&mut self, element: Box<dyn CircuitElement>) {
        self.elements.push(element)
    }

    fn inputs(&mut self) -> &mut Vec<WireLink> {
        &mut self.inputs
    }

    fn outputs(&mut self) -> &mut Vec<WireLink> {
        &mut self.outputs
    }

    fn add_input(&mut self, input: WireLink) {
        (*input).borrow_mut().number(self.inputs().len());
        self.inputs.push(input);
    }

    fn add_output(&mut self, output: WireLink) {
        (*output).borrow_mut().number(self.inputs().len());
        self.outputs.push(output);
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub enum LogicFunction {
    AND,
    OR,
    NOT,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct LogicGate {
    function: LogicFunction,
    elements: Vec<Box<dyn CircuitElement>>,
    inputs: Vec<WireLink>,
    outputs: Vec<WireLink>,
}

impl Default for LogicGate {
    fn default() -> Self {
        LogicGate {
            function: LogicFunction::AND,
            elements: vec![],
            inputs: vec![],
            outputs: vec![],
        }
    }
}

impl LogicGate {
    pub fn new(function: LogicFunction) -> Box<LogicGate> {
        let mut gate = LogicGate::default();
        gate.function = function;
        Box::new(gate)
    }
}

#[typetag::serde]
impl CircuitElement for LogicGate {
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>> {
        let inputs: Vec<LogicLevel> = self
            .inputs
            .iter()
            .map(|i| RefCell::borrow(&*i).read())
            .collect();
        let value = match self.function {
            LogicFunction::AND => inputs.into_iter().reduce(|l, r| l & r),
            LogicFunction::OR => inputs.into_iter().reduce(|l, r| l | r),
            LogicFunction::NOT => inputs.into_iter().reduce(|l, r| l | r).map(LogicLevel::neg),
        };
        let value = value.unwrap_or(LogicLevel::Zero);
        let mut old_value = LogicLevel::Zero;
        for output in self.outputs.iter() {
            let v = RefCell::borrow(&*output);
            old_value = old_value | v.read();
        }
        for output in self.outputs.iter_mut() {
            let mut output = RefCell::borrow_mut(&*output);
            output.write(value);
        }

        Ok(old_value == value)
    }

    fn elements(&mut self) -> &mut Vec<Box<dyn CircuitElement>> {
        &mut self.elements
    }

    fn add_element(&mut self, _element: Box<dyn CircuitElement>) {}

    fn inputs(&mut self) -> &mut Vec<WireLink> {
        &mut self.inputs
    }

    fn outputs(&mut self) -> &mut Vec<WireLink> {
        &mut self.outputs
    }

    fn add_input(&mut self, input: WireLink) {
        (*input).borrow_mut().number(self.inputs().len());
        self.inputs.push(input);
    }

    fn add_output(&mut self, output: WireLink) {
        (*output).borrow_mut().number(self.inputs().len());
        self.outputs.push(output);
    }
}

#[allow(dead_code)]
pub fn load_circuit(path: &PathBuf) -> Result<Box<dyn CircuitElement>, Box<dyn Error>> {
    let mut buf = String::new();
    BufReader::new(File::open(path)?).read_to_string(&mut buf)?;

    let mut circuit: Circuit = serde_json::from_slice(buf.as_bytes())?;
    let mut map = HashMap::new();
    circuit.deduplicate(&mut map);

    Ok(Box::new(circuit))
}

#[allow(dead_code)]
pub fn store_circuit(
    path: &PathBuf,
    circuit: Box<dyn CircuitElement>,
) -> Result<(), Box<dyn Error>> {
    let mut file = BufWriter::new(File::create(path)?);
    write!(file, "{}", serde_json::to_string(&circuit)?)?;

    Ok(())
}

pub fn simulate(mut circuit: Box<dyn CircuitElement>) -> Result<(), Box<dyn Error>> {
    loop {
        if circuit.propagate()? {
            break;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{error::Error, fs::remove_file, path::PathBuf};

    use crate::{
        load_circuit, simulate, store_circuit, Circuit, CircuitElement, LogicFunction, LogicGate,
        LogicLevel, Wire,
    };

    fn test_input(
        gate: LogicFunction,
        input_one: usize,
        output_value: usize,
    ) -> Result<(), Box<dyn Error>> {
        let mut gate = LogicGate::new(gate);
        let input_one = Wire::new(input_one.into());
        let output = Wire::new(LogicLevel::Zero);
        gate.add_input(input_one);
        gate.add_output(output.clone());

        assert_eq!((*output).borrow().read(), LogicLevel::Zero);

        simulate(gate)?;

        assert_eq!((*output).borrow().read(), output_value.into());

        Ok(())
    }

    fn test_inputs(
        gate: LogicFunction,
        input_one: usize,
        input_two: usize,
        output_value: usize,
    ) -> Result<(), Box<dyn Error>> {
        let mut gate = LogicGate::new(gate);
        let input_one = Wire::new(input_one.into());
        let input_two = Wire::new(input_two.into());
        let output = Wire::new(LogicLevel::Zero);
        gate.add_input(input_one);
        gate.add_input(input_two);
        gate.add_output(output.clone());

        assert_eq!((*output).borrow().read(), LogicLevel::Zero);

        simulate(gate)?;

        assert_eq!((*output).borrow().read(), output_value.into());

        Ok(())
    }

    #[test]
    fn and_gate() -> Result<(), Box<dyn Error>> {
        test_inputs(LogicFunction::AND, 0, 0, 0)?;
        test_inputs(LogicFunction::AND, 0, 1, 0)?;
        test_inputs(LogicFunction::AND, 1, 0, 0)?;
        test_inputs(LogicFunction::AND, 1, 1, 1)?;

        Ok(())
    }

    #[test]
    fn or_gate() -> Result<(), Box<dyn Error>> {
        test_inputs(LogicFunction::OR, 0, 0, 0)?;
        test_inputs(LogicFunction::OR, 0, 1, 1)?;
        test_inputs(LogicFunction::OR, 1, 0, 1)?;
        test_inputs(LogicFunction::OR, 1, 1, 1)?;

        Ok(())
    }

    #[test]
    fn not_gate() -> Result<(), Box<dyn Error>> {
        test_input(LogicFunction::NOT, 0, 1)?;
        test_input(LogicFunction::NOT, 1, 0)?;

        Ok(())
    }

    #[test]
    fn clock_test() -> Result<(), Box<dyn Error>> {
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

        assert_eq!((*input_one).borrow().read(), LogicLevel::One);
        assert_eq!((*input_two).borrow().read(), LogicLevel::One);
        assert_eq!((*output_one).borrow().read(), LogicLevel::Zero);
        assert_eq!((*output_two).borrow().read(), LogicLevel::Zero);
        assert_eq!((*output_three).borrow().read(), LogicLevel::Zero);
        circuit.propagate()?;
        assert_eq!((*input_one).borrow().read(), LogicLevel::One);
        assert_eq!((*input_two).borrow().read(), LogicLevel::One);
        assert_eq!((*output_one).borrow().read(), LogicLevel::Zero);
        assert_eq!((*output_two).borrow().read(), LogicLevel::Zero);
        assert_eq!((*output_three).borrow().read(), LogicLevel::One);
        for _i in 0..1000 {
            circuit.propagate()?;
            assert_eq!((*input_one).borrow().read(), LogicLevel::One);
            assert_eq!((*input_two).borrow().read(), LogicLevel::One);
            assert_eq!((*output_one).borrow().read(), LogicLevel::One);
            assert_eq!((*output_two).borrow().read(), LogicLevel::One);
            assert_eq!((*output_three).borrow().read(), LogicLevel::Zero);
            circuit.propagate()?;
            assert_eq!((*input_one).borrow().read(), LogicLevel::One);
            assert_eq!((*input_two).borrow().read(), LogicLevel::One);
            assert_eq!((*output_one).borrow().read(), LogicLevel::Zero);
            assert_eq!((*output_two).borrow().read(), LogicLevel::Zero);
            assert_eq!((*output_three).borrow().read(), LogicLevel::One);
        }

        let path = &PathBuf::from("./serde.json");
        store_circuit(path, *Box::new(circuit))?;
        let mut circuit = load_circuit(path)?;
        for _i in 0..1000 {
            circuit.propagate()?;
        }

        remove_file(path)?;

        Ok(())
    }
}
