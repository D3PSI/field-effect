use crossbeam::channel::{Receiver, Sender};
use rayon::Scope;
use std::error::Error;

enum LogicLevel {
    ZERO = 0,
    ONE = 1,
}

type InWire = Receiver<LogicLevel>;
type OutWire = Sender<LogicLevel>;

struct LogicGate {
    inputs: Vec<InWire>,
    outputs: Vec<OutWire>,
    // TODO: Logic function to perform, which computes outputs from inputs in a dataflow manner
}

struct Circuit<T: Propagatable + Send + Sync> {
    inputs: Vec<InWire>,
    outputs: Vec<OutWire>,
    circuits: Vec<Box<T>>,
    cutoff: bool,
}

trait Propagatable {
    fn propagate<'a>(&'a mut self, s: &Scope<'a>) -> Result<(), Box<dyn Error>>;
}

impl Propagatable for LogicGate {
    fn propagate<'a>(&'a mut self, _: &Scope<'a>) -> Result<(), Box<dyn Error>> {
        let mut inp = vec![];
        for input in &self.inputs {
            inp.push(input.recv()?);
        }

        Ok(())
    }
}

impl<T: Propagatable + Send + Sync> Propagatable for Circuit<T> {
    fn propagate<'a>(&'a mut self, s: &Scope<'a>) -> Result<(), Box<dyn Error>> {
        if self.cutoff {
        } else {
            for circuit in self.circuits.iter_mut() {
                s.spawn(|s| {
                    circuit.propagate(s);
                });
            }
        }

        Ok(())
    }
}
