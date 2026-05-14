use std::fmt::{self, Display};

use resolvo::utils::{Pool, VersionSet};

/// A set of digits 1-9 represented as a bitmask.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct DigitSet(u16);

impl DigitSet {
    fn all() -> Self {
        DigitSet(0b1111111110) // bits 1-9 set
    }

    fn singleton(digit: u8) -> Self {
        DigitSet(1 << digit)
    }

    fn contains(&self, digit: u8) -> bool {
        self.0 & (1 << digit) != 0
    }
}

impl Display for DigitSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let digits: Vec<u8> = (1..=9).filter(|&d| self.contains(d)).collect();
        write!(
            f,
            "{{{}}}",
            digits
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl VersionSet for DigitSet {
    type V = u8;
}

fn main() {
    println!("sudoku example placeholder");
}
