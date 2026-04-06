#[macro_export]
macro_rules! printerr {
    ($($arg:tt)*) => {
        ::std::eprintln!("\x1b[31m[Error] {}\x1b[0m", format!($($arg)*));
    };
}

#[macro_export]
macro_rules! printwarn {
    ($($arg:tt)*) => {
        ::std::eprintln!("\x1b[33m[Warning] {}\x1b[0m", format!($($arg)*));
    };
}
