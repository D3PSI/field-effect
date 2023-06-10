use std::{error::Error, path::PathBuf};

use clap::Parser;

use field_effect::load_circuit;

#[derive(Parser)]
struct FieldEffectArgs {
    circuit_file: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = FieldEffectArgs::parse();
    let circuit = load_circuit(&args.circuit_file)?;
    dbg!(&circuit);

    Ok(())
}
