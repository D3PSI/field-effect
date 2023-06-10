#[macro_export]
macro_rules! read {
    ($v:expr) => {
        (*$v).borrow().read()
    };
}
