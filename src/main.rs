mod render;

use clap::{App, Arg, ArgMatches};
use field_effect::{circuit::circuit::Circuit, FieldEffectOptions};
use render::State;
use std::error::Error;

use pollster;
use winit::{
    event::*,
    event_loop::{ControlFlow, EventLoop},
    window::WindowBuilder,
};

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

async fn run() {
    env_logger::init();
    let event_loop = EventLoop::new();
    let window = WindowBuilder::new().build(&event_loop).unwrap();

    let mut state = State::new(&window).await;

    event_loop.run(move |event, _, control_flow| {
        match event {
            Event::RedrawRequested(window_id) if window_id == window.id() => {
                state.update();
                match state.render() {
                    Ok(_) => {}
                    // Reconfigure the surface if lost
                    Err(wgpu::SurfaceError::Lost) => state.resize(state.size),
                    // The system is out of memory, we should probably quit
                    Err(wgpu::SurfaceError::OutOfMemory) => *control_flow = ControlFlow::Exit,
                    // All other errors (Outdated, Timeout) should be resolved by the next frame
                    Err(e) => eprintln!("{:?}", e),
                }
            }
            Event::MainEventsCleared => {
                // RedrawRequested will only trigger once, unless we manually
                // request it.
                window.request_redraw();
            }
            Event::WindowEvent {
                ref event,
                window_id,
            } if window_id == window.id() => {
                if !state.input(event) {
                    match event {
                        WindowEvent::CloseRequested
                        | WindowEvent::KeyboardInput {
                            input:
                                KeyboardInput {
                                    state: ElementState::Pressed,
                                    virtual_keycode: Some(VirtualKeyCode::Escape),
                                    ..
                                },
                            ..
                        } => *control_flow = ControlFlow::Exit,
                        WindowEvent::Resized(physical_size) => {
                            state.resize(*physical_size);
                        }
                        WindowEvent::ScaleFactorChanged { new_inner_size, .. } => {
                            state.resize(**new_inner_size);
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    });
}

fn main() -> Result<(), Box<dyn Error>> {
    let options = config();

    pollster::block_on(run());

    Ok(())
}
