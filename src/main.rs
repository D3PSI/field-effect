use clap::{App, Arg, ArgMatches};
use field_effect::{circuit::circuit::Circuit, FieldEffectOptions};
use std::error::Error;

const ARG_FILE: &str = "file";

fn args() -> ArgMatches {
    App::new("field effect")
        .version("0.1.0")
        .author("Cedric Schwyter <cedricschwyter@bluewin.ch>")
        .about("an intuitive, high-performance logic simulator/puzzle game")
        .arg(
            Arg::with_name(ARG_FILE)
                .short('f')
                .takes_value(true)
                .required(false)
                .help("load circuit from file"),
        )
        .get_matches()
}

fn config() -> FieldEffectOptions {
    let mut options = FieldEffectOptions::defaults();
    let args = args();
    if let Some(file) = args.value_of(ARG_FILE) {
        options.file(file.to_string());
    }
    options
}

fn main() -> Result<(), Box<dyn Error>> {
    let options = config();

    Ok(())
}
