use crossbeam::channel::{Receiver, Sender};
use rayon::{self, Scope};
use std::{error::Error, ops::Neg, sync::mpsc};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum LogicLevel {
    ZERO = 0,
    ONE = 1,
}

impl Neg for LogicLevel {
    type Output = Self;
    fn neg(self) -> Self::Output {
        if self == Self::ZERO {
            return Self::ONE;
        }

        Self::ZERO
    }
}

pub type InWire = Receiver<LogicLevel>;
pub type OutWire = Sender<LogicLevel>;
pub type Wire = (OutWire, InWire);

/// A circuit component intended to represent only a simple logic gate function with one output,
/// however this implementation would also allow for more complex logic functions with multiple outputs.
pub struct LogicGate {
    inputs: Vec<InWire>,
    outputs: Vec<OutWire>,
    logic: Box<dyn Fn(Vec<LogicLevel>) -> Vec<LogicLevel> + Send + Sync>,
}

impl LogicGate {
    /// Constructs a new AND gate with the given inputs
    pub fn and(inputs: Vec<InWire>, outputs: Vec<OutWire>) -> LogicGate {
        let num_outputs = outputs.len();
        let logic = Box::new(move |inp| {
            for i in inp {
                if i != LogicLevel::ONE {
                    return vec![LogicLevel::ZERO; num_outputs];
                }
            }
            return vec![LogicLevel::ONE; num_outputs];
        });
        LogicGate {
            inputs,
            outputs,
            logic,
        }
    }

    /// Constructs a new OR gate with the given inputs
    pub fn or(inputs: Vec<InWire>, outputs: Vec<OutWire>) -> LogicGate {
        let num_outputs = outputs.len();
        let logic = Box::new(move |inp| {
            for i in inp {
                if i == LogicLevel::ONE {
                    return vec![LogicLevel::ONE; num_outputs];
                }
            }
            return vec![LogicLevel::ZERO; num_outputs];
        });
        LogicGate {
            inputs,
            outputs,
            logic,
        }
    }

    /// Constructs a new NOT gate with the given inputs
    pub fn not(inputs: Vec<InWire>, outputs: Vec<OutWire>) -> LogicGate {
        let logic = Box::new(move |inp| {
            let mut out = vec![];
            for i in inp {
                let mut negated: LogicLevel = LogicLevel::ONE;
                if i == LogicLevel::ONE {
                    negated = LogicLevel::ZERO;
                }

                out.push(negated);
            }
            out
        });
        LogicGate {
            inputs,
            outputs,
            logic,
        }
    }
}

/// A recursive type to represent a combinational and/or a sequential circuit element.
/// Inputs and outputs are dangling in their respective directions until they are reconciled. A
/// protocol will be defined for that. In said protocol for each input/output, since every output
/// is linked to another Circuit's input, one whole channel will be dropped per connection.
pub struct CircuitElement<T: Propagatable + Send + Sync> {
    inputs: Vec<InWire>,
    outputs: Vec<OutWire>,
    circuits: Vec<Box<T>>,
    cutoff: bool,
}

/// Top level circuit object
pub struct Circuit<T: Propagatable + Send + Sync> {
    circuits: Vec<Box<T>>,
}

impl<T: Propagatable + Send + Sync> Circuit<T> {
    /// Computes the next state from the current state. May utilize multiple CPUs to do so using
    /// task parallelism.
    pub fn compute(&self) -> Result<(), Box<dyn Error + Send + Sync>> {
        rayon::scope(|s| -> Result<(), Box<dyn Error + Send + Sync>> {
            let mut changed = false;
            while !changed {
                changed = false;
                for circuit in self.circuits.iter() {
                    if circuit.propagate(s)? {
                        changed = true;
                    }
                }
            }

            Ok(())
        })?;

        Ok(())
    }
}

/// A trait to propagate state computation through circuits. This computation is broken up into
/// multiple tasks and implemented using task parallelism.
pub trait Propagatable {
    fn propagate<'a>(&'a self, s: &Scope<'a>) -> Result<bool, Box<dyn Error + Send + Sync>>;
}

impl Propagatable for LogicGate {
    fn propagate<'a>(&'a self, _: &Scope<'a>) -> Result<bool, Box<dyn Error + Send + Sync>> {
        let mut inp = vec![];
        for input in &self.inputs {
            inp.push(input.try_recv().unwrap_or(LogicLevel::ZERO));
        }

        let prev = inp.clone();
        let out = (self.logic)(inp);

        for (i, output) in self.outputs.iter().enumerate() {
            output.send(out[i])?;
        }

        Ok(out != prev)
    }
}

impl<T: Propagatable + Send + Sync> Propagatable for CircuitElement<T> {
    fn propagate<'a>(&'a self, s: &Scope<'a>) -> Result<bool, Box<dyn Error + Send + Sync>> {
        if self.cutoff {
            let mut changed = false;
            for circuit in self.circuits.iter() {
                if circuit.propagate(s)? {
                    changed = true;
                }
            }

            return Ok(changed);
        }
        let (tx, rx) = mpsc::channel();
        for circuit in self.circuits.iter() {
            let tx_closure = tx.clone();
            s.spawn(move |s| {
                tx_closure.send(circuit.propagate(s).unwrap()).unwrap();
            });
        }
        drop(tx);
        let mut changed = false;
        for _i in 0..self.circuits.len() {
            changed &= rx.recv()?;
        }

        Ok(changed)
    }
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use crossbeam::channel::bounded;

    use crate::{Circuit, CircuitElement, LogicLevel, Wire};

    use super::LogicGate;

    #[test]
    fn combinational_and_gates() -> Result<(), Box<dyn Error>> {
        let input_one_one: Wire = bounded(1);
        let input_one_two: Wire = bounded(1);
        let mut inputs_one = Vec::new();
        inputs_one.push(input_one_one.1);
        inputs_one.push(input_one_two.1);
        let output_one: Wire = bounded(1);
        let mut outputs_one = Vec::new();
        outputs_one.push(output_one.0);
        let logic_gate_one = Box::new(LogicGate::and(inputs_one, outputs_one));
        let input_two_one: Wire = bounded(1);
        let input_two_two: Wire = bounded(1);
        let mut inputs_two = Vec::new();
        inputs_two.push(input_two_one.1);
        inputs_two.push(input_two_two.1);
        let output_two: Wire = bounded(1);
        let mut outputs_two = Vec::new();
        outputs_two.push(output_two.0);
        let logic_gate_two = Box::new(LogicGate::and(inputs_two, outputs_two));
        let inputs_three = vec![output_one.1, output_two.1];
        let output_three: Wire = bounded(1);
        let mut outputs_three = Vec::new();
        outputs_three.push(output_three.0);
        let logic_gate_three = Box::new(LogicGate::and(inputs_three, outputs_three));
        let element = Box::new(CircuitElement {
            inputs: vec![],
            outputs: vec![],
            circuits: vec![logic_gate_one, logic_gate_two, logic_gate_three],
            cutoff: true,
        });
        let circuit = Circuit {
            circuits: vec![element],
        };
        // send all inputs first
        input_one_one.0.send(LogicLevel::ONE).unwrap();
        input_one_two.0.send(LogicLevel::ONE).unwrap();
        input_two_one.0.send(LogicLevel::ONE).unwrap();
        input_two_two.0.send(LogicLevel::ONE).unwrap();
        // dataflow should sort out the rest of the propagation
        circuit.compute().unwrap();

        assert_eq!(output_three.1.recv(), Ok(LogicLevel::ONE));

        Ok(())
    }

    #[test]
    fn logic_level_negation() {
        assert_eq!(-LogicLevel::ZERO, LogicLevel::ONE);
        assert_eq!(-LogicLevel::ONE, LogicLevel::ZERO);
    }
}
