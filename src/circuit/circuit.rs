use crossbeam::channel::{bounded, Receiver, Sender};
use rayon::{self, Scope};
use std::{error::Error, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum LogicLevel {
    ZERO = 0,
    ONE = 1,
}

pub type InWire = Receiver<LogicLevel>;
pub type OutWire = Sender<LogicLevel>;
pub type Wire = (OutWire, InWire);

/// A circuit component intended to represent only a simple logic gate function with one output,
/// however this implementation would also allow for more complex logic functions with multiple outputs.
struct LogicGate<F>
where
    F: Fn(Vec<LogicLevel>) -> Vec<LogicLevel>,
{
    inputs: Vec<InWire>,
    outputs: Vec<OutWire>,
    logic: F,
}

/// A recursive type to represent a combinational and/or a sequential circuit element.
/// Inputs and outputs are dangling in their respective directions until they are reconciled. A
/// protocol will be defined for that. In said protocol for each input/output, since every output
/// is linked to another Circuit's input, one whole channel will be dropped per connection.
pub struct CircuitElement<T: Propagatable + Send + Sync> {
    inputs: Vec<Wire>,
    outputs: Vec<Wire>,
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
    pub fn compute(&mut self) -> Result<(), Box<dyn Error>> {
        rayon::scope(|s| {
            for circuit in self.circuits.iter_mut() {
                // TODO: figure out how to gracefully handle Result types
                circuit.propagate(s).unwrap();
            }
        });

        Ok(())
    }
}

/// A trait to propagate state computation through circuits. This computation is broken up into
/// multiple tasks and implemented using task parallelism.
pub trait Propagatable {
    fn propagate<'a>(&'a mut self, s: &Scope<'a>) -> Result<(), Box<dyn Error>>;
}

impl<F> Propagatable for LogicGate<F>
where
    F: Fn(Vec<LogicLevel>) -> Vec<LogicLevel>,
{
    fn propagate<'a>(&'a mut self, _: &Scope<'a>) -> Result<(), Box<dyn Error>> {
        let mut inp = vec![];
        for input in &self.inputs {
            inp.push(input.try_recv()?);
        }

        let out = (self.logic)(inp);

        for (i, output) in self.outputs.iter().enumerate() {
            output.send(out[i])?;
        }

        Ok(())
    }
}

impl<T: Propagatable + Send + Sync> Propagatable for CircuitElement<T> {
    fn propagate<'a>(&'a mut self, s: &Scope<'a>) -> Result<(), Box<dyn Error>> {
        if self.cutoff {
            for circuit in self.circuits.iter_mut() {
                circuit.propagate(s)?;
            }
        } else {
            for circuit in self.circuits.iter_mut() {
                s.spawn(|s| {
                    // TODO: figure out how to gracefully handle Result types
                    circuit.propagate(s).unwrap();
                });
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use crossbeam::channel::bounded;

    use crate::{LogicLevel, Wire};

    use super::{LogicGate, Propagatable};

    #[test]
    fn test_and_gate() -> Result<(), Box<dyn Error>> {
        let input_one: Wire = bounded(1);
        let input_two: Wire = bounded(1);
        let mut inputs = Vec::new();
        inputs.push(input_one.1);
        inputs.push(input_two.1);
        let output_one: Wire = bounded(1);
        let mut outputs = Vec::new();
        outputs.push(output_one.0);
        let mut logic_gate = LogicGate {
            inputs,
            outputs,
            logic: |inp| {
                for i in inp {
                    if i != LogicLevel::ONE {
                        return vec![LogicLevel::ZERO];
                    }
                }
                return vec![LogicLevel::ONE];
            },
        };
        input_one.0.send(LogicLevel::ONE).unwrap();
        input_two.0.send(LogicLevel::ONE).unwrap();
        rayon::scope(|s| {
            logic_gate.propagate(s).unwrap();
        });
        assert_eq!(output_one.1.recv(), Ok(LogicLevel::ONE));
        Ok(())
    }
}
