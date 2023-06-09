//! This library root file contains basic definitions of working with logical circuits

use std::{
    cell::RefCell,
    error::Error,
    fmt::Display,
    ops::{BitAnd, BitOr, BitXor, Neg},
    path::PathBuf,
    rc::{Rc, Weak},
};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LogicLevel {
    Zero = 0,
    One = 1,
}

impl From<usize> for LogicLevel {
    fn from(val: usize) -> Self {
        if val == 0 {
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

pub trait CircuitElement {
    /// returns true if there have not been state updates (the element has settled on a state)
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>>;
}

pub struct Wire {
    value: LogicLevel,
}

impl CircuitElement for Wire {
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>> {
        Ok(true)
    }
}

impl Wire {
    pub fn new(value: LogicLevel) -> Rc<RefCell<Wire>> {
        Rc::new(RefCell::new(Wire { value }))
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

/// Wraps a `WireRef` in a `Weak` - represent an immutable reference to a wire
pub type WireWeak = Weak<WireRef>;

pub struct Circuit {
    // a circuit owns all of its constituent circuits
    elements: Vec<Box<dyn CircuitElement>>,
    // inputs and outputs are modeled using a wire (which itself is a circuit element that is owned
    // by the circuit)
    inputs: Vec<WireWeak>,
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
    pub fn add_element(&mut self, element: Box<dyn CircuitElement>) {
        self.elements.push(element);
    }

    pub fn add_input(&mut self, input: WireWeak) {
        self.inputs.push(input);
    }

    pub fn add_output(&mut self, output: WireLink) {
        self.outputs.push(output);
    }
}

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
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum LogicFunction {
    AND,
    OR,
    NOT,
}

pub struct LogicGate {
    function: LogicFunction,
    inputs: Vec<WireWeak>,
    outputs: Vec<WireLink>,
}

impl LogicGate {
    pub fn new(function: LogicFunction) -> LogicGate {
        LogicGate {
            function,
            inputs: vec![],
            outputs: vec![],
        }
    }

    pub fn add_input(&mut self, input: WireWeak) {
        self.inputs.push(input);
    }

    pub fn add_output(&mut self, output: WireLink) {
        self.outputs.push(output);
    }
}

impl CircuitElement for LogicGate {
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>> {
        let inputs: Vec<LogicLevel> = self
            .inputs
            .iter()
            .map(|i| i.upgrade())
            .map(|i| {
                if let Some(wire) = i {
                    return (*wire).borrow().read();
                } else {
                    return LogicLevel::Zero;
                }
            })
            .collect();
        let value = match self.function {
            LogicFunction::AND => inputs.into_iter().reduce(|l, r| l & r),
            LogicFunction::OR => inputs.into_iter().reduce(|l, r| l | r),
            LogicFunction::NOT => inputs.into_iter().reduce(|l, r| l | r).map(LogicLevel::neg),
        };
        let value = value.unwrap_or(LogicLevel::Zero);
        let old_value = self
            .outputs
            .iter_mut()
            .map(|o| o.borrow().read())
            .reduce(|l, r| l | r)
            .unwrap_or(LogicLevel::Zero);
        for output in self.outputs.iter_mut() {
            let mut output = RefCell::borrow_mut(&*output);
            output.write(value);
        }

        Ok(old_value == value)
    }
}

pub fn load_circuit(circuit_file: &PathBuf) -> Result<Circuit, Box<dyn Error>> {
    todo!();
}

pub fn store_circuit(circuit: &Circuit) -> Result<(), Box<dyn Error>> {
    todo!();
}

pub fn simulate_circuit(mut circuit: Box<dyn CircuitElement>) -> Result<(), Box<dyn Error>> {
    loop {
        if circuit.propagate()? {
            break;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{error::Error, rc::Rc};

    use crate::{simulate_circuit, LogicFunction, LogicGate, LogicLevel, Wire};

    fn test_gate_input(
        gate: LogicFunction,
        input_one: usize,
        output_value: usize,
    ) -> Result<(), Box<dyn Error>> {
        let mut gate = LogicGate::new(gate);
        let input_one = Wire::new(input_one.into());
        let output = Wire::new(LogicLevel::Zero);
        gate.add_input(Rc::downgrade(&input_one));
        gate.add_output(output.clone());

        assert_eq!(output.borrow().read(), LogicLevel::Zero);

        simulate_circuit(Box::new(gate))?;

        assert_eq!(output.borrow().read(), output_value.into());

        Ok(())
    }

    fn test_gate_inputs(
        gate: LogicFunction,
        input_one: usize,
        input_two: usize,
        output_value: usize,
    ) -> Result<(), Box<dyn Error>> {
        let mut gate = LogicGate::new(gate);
        let input_one = Wire::new(input_one.into());
        let input_two = Wire::new(input_two.into());
        let output = Wire::new(LogicLevel::Zero);
        gate.add_input(Rc::downgrade(&input_one));
        gate.add_input(Rc::downgrade(&input_two));
        gate.add_output(output.clone());

        assert_eq!(output.borrow().read(), LogicLevel::Zero);

        simulate_circuit(Box::new(gate))?;

        assert_eq!(output.borrow().read(), output_value.into());

        Ok(())
    }

    #[test]
    fn and_gate() -> Result<(), Box<dyn Error>> {
        test_gate_inputs(LogicFunction::AND, 0, 0, 0)?;
        test_gate_inputs(LogicFunction::AND, 0, 1, 0)?;
        test_gate_inputs(LogicFunction::AND, 1, 0, 0)?;
        test_gate_inputs(LogicFunction::AND, 1, 1, 1)?;

        Ok(())
    }

    #[test]
    fn or_gate() -> Result<(), Box<dyn Error>> {
        test_gate_inputs(LogicFunction::OR, 0, 0, 0)?;
        test_gate_inputs(LogicFunction::OR, 0, 1, 1)?;
        test_gate_inputs(LogicFunction::OR, 1, 0, 1)?;
        test_gate_inputs(LogicFunction::OR, 1, 1, 1)?;

        Ok(())
    }

    #[test]
    fn not_gate() -> Result<(), Box<dyn Error>> {
        test_gate_input(LogicFunction::NOT, 0, 1)?;
        test_gate_input(LogicFunction::NOT, 1, 0)?;

        Ok(())
    }
}
