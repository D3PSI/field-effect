use std::{error::Error, path::PathBuf};

use clap::Parser;

use field_effect::{load_circuit, simulate_circuit};

#[derive(Parser)]
struct FieldEffectArgs {
    circuit_file: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = FieldEffectArgs::parse();
    let mut circuit = load_circuit(&args.circuit_file)?;
    simulate_circuit(&mut circuit)?;

    Ok(())
}
