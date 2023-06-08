//! This library root file contains basic definitions of working with logical circuits

use std::{
    cell::RefCell,
    error::Error,
    ops::{BitAnd, BitOr, BitXor, Neg},
    path::PathBuf,
    rc::{Rc, Weak},
};

#[derive(PartialEq, Eq, Clone, Copy)]
enum LogicLevel {
    Zero = 0,
    One = 1,
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

trait CircuitElement {
    /// returns true if there have not been state updates (the element has settled on a state)
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>>;
}

pub struct Wire {
    value: LogicLevel,
    input: LogicLevel,
}

impl CircuitElement for Wire {
    fn propagate(&mut self) -> Result<bool, Box<dyn Error>> {
        let settled = self.value == self.input;
        self.value = self.input;

        Ok(settled)
    }
}

impl Wire {
    fn write(&mut self, value: LogicLevel) {
        self.input = value;
    }

    fn read(&self) -> LogicLevel {
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
enum LogicFunction {
    AND,
    OR,
    NOT,
}

pub struct LogicGate {
    function: LogicFunction,
    inputs: Vec<WireWeak>,
    outputs: Vec<WireLink>,
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
        self.outputs
            .iter_mut()
            .for_each(|o| o.borrow_mut().write(value));

        Ok(old_value == value)
    }
}

pub fn load_circuit(circuit_file: &PathBuf) -> Result<Circuit, Box<dyn Error>> {
    todo!();
}

pub fn store_circuit(circuit: &Circuit) -> Result<(), Box<dyn Error>> {
    todo!();
}

pub fn simulate_circuit(circuit: &mut Circuit) -> Result<(), Box<dyn Error>> {
    loop {
        if circuit.propagate()? {
            break;
        }
    }

    Ok(())
}
