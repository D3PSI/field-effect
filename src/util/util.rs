/// Library configuration options
#[derive(Debug)]
pub struct FieldEffectOptions {
    file: Option<String>,
}

impl FieldEffectOptions {
    /// Returns the default configuration options for the library
    pub fn defaults() -> Self {
        FieldEffectOptions { file: None }
    }

    /// Setter for the file configuration option
    pub fn file(&mut self, f: String) -> &mut Self {
        self.file = Some(f);
        self
    }
}
