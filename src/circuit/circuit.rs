use crossbeam::channel::{bounded, Receiver, Sender};
use rayon::{self, Scope};
use std::error::Error;

#[derive(Clone, Copy)]
pub enum LogicLevel {
    ZERO = 0,
    ONE = 1,
}

pub type InWire = Receiver<LogicLevel>;
pub type OutWire = Sender<LogicLevel>;
pub type Wire = (OutWire, InWire);

/// A circuit component intended to represent only a simple logic gate function with one output,
/// however this implementation would also allow for more complex logic functions with multiple outputs.
struct LogicGate {
    inputs: Vec<InWire>,
    outputs: Vec<OutWire>,
    logic: Box<dyn Fn(Vec<LogicLevel>) -> Vec<LogicLevel>>,
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

impl Propagatable for LogicGate {
    fn propagate<'a>(&'a mut self, _: &Scope<'a>) -> Result<(), Box<dyn Error>> {
        let mut inp = vec![];
        for input in &self.inputs {
            inp.push(input.recv()?);
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
