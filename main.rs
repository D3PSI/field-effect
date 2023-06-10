use std::{error::Error, path::PathBuf};

use clap::Parser;

use eframe::egui;
use field_effect::{load_circuit, simulate};

#[derive(Parser)]
struct FieldEffectArgs {
    circuit_file: PathBuf,
}

struct FieldEffect {
    args: FieldEffectArgs,
}

impl FieldEffect {
    fn new(_cc: &eframe::CreationContext<'_>, args: FieldEffectArgs) -> Self {
        FieldEffect { args }
    }
}

impl eframe::App for FieldEffect {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("Hello World!");
        });
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = FieldEffectArgs::parse();
    let native_options = eframe::NativeOptions::default();
    eframe::run_native(
        "Field Effect",
        native_options,
        Box::new(|cc| Box::new(FieldEffect::new(cc, args))),
    )?;

    Ok(())
}
