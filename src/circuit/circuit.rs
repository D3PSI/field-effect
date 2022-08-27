use crossbeam::channel::{Receiver, Sender};
use rayon::join;
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

struct Circuit<T: Propagatable> {
    inputs: Vec<InWire>,
    outputs: Vec<OutWire>,
    circuits: Vec<Box<T>>,
}

trait Propagatable {
    fn propagate(&mut self) -> Result<(), Box<dyn Error>>;
}

impl Propagatable for LogicGate {
    fn propagate(&mut self) -> Result<(), Box<dyn Error>> {
        let mut inp = vec![];
        for input in &self.inputs {
            inp.push(input.recv()?);
        }

        Ok(())
    }
}

impl<T: Propagatable> Propagatable for Circuit<T> {
    fn propagate(&mut self) -> Result<(), Box<dyn Error>> {
        // TODO: use rayon::join for task parallelism, somehow add sequential cutoff above level of
        // logic gates because that would be too fine grained. maybe introduce a gate counter for
        // each circuit and have sequential cutoff at circuits with fewer than 1000 gates (calls
        // for experimentation)
        Ok(())
    }
}
