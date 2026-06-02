//! Defines several helper functions and structs that make it easier to
//! implement a custom dependency provider.

mod indexed_set;
mod mapping;
mod pool;

pub use indexed_set::IndexedSet;
pub use mapping::{Mapping, MappingIter};
pub use pool::{IntoPackageName, PackageName, Pool, Solvable, VersionSet};
