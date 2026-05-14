//! Solves sudoku puzzles using resolvo's CDCL SAT solver.
//!
//! This example demonstrates that resolvo — a package dependency resolver — can solve
//! constraint satisfaction problems beyond package resolution. It maps sudoku concepts
//! to resolvo's domain model:
//!
//! | Sudoku              | Resolvo              | Example             |
//! |---------------------|----------------------|---------------------|
//! | Cell (81 total)     | Package (`NameId`)   | `r0c0`, `r4c7`      |
//! | Digit 1-9 for cell  | Version (`SolvableId`)| `r0c0=5`           |
//! | "Cell needs a digit"| Requirement          | "install r0c0"      |
//! | Row/col/box rules   | Constraint           | "r0c0 excludes 5 from peers" |
//! | Pre-filled cell     | Locked candidate     | "r0c0 must be 5"    |
//!
//! Usage: `cargo run --example sudoku -- "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79"`

use std::fmt::{self, Display};
use std::process;

use resolvo::utils::{Pool, VersionSet};
use resolvo::{
    Candidates, Condition, ConditionId, ConditionalRequirement, Dependencies, DependencyProvider,
    HintDependenciesAvailable, Interner, KnownDependencies, NameId, Problem, SolvableId, Solver,
    SolverCache, StringId, VersionSetId, VersionSetUnionId,
};

// -- VersionSet implementation ------------------------------------------------
//
// Resolvo is generic over what "versions" mean. In package management, a version
// set might be a semver range like ">=1.2, <2.0". For sudoku, our "versions" are
// digits 1-9, and a "version set" is a subset of those digits. We represent this
// compactly as a bitmask.

/// A set of digits 1-9 represented as a bitmask. Bit N set means digit N is in
/// the set. This serves as resolvo's `VersionSet` — the analog of a semver range,
/// but for sudoku digits.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct DigitSet(u16);

impl DigitSet {
    /// All digits 1-9. Used as the "any version" requirement for each cell.
    fn all() -> Self {
        DigitSet(0b1111111110) // bits 1-9 set
    }

    /// A single digit. Used to build exclusion constraints between peer cells.
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

// -- SudokuProvider -----------------------------------------------------------
//
// The provider is the bridge between the problem domain (sudoku) and the solver.
// It tells resolvo what "packages" exist (cells), what "versions" are available
// (digits 1-9), and what constraints apply (no duplicate digits in any row,
// column, or 3x3 box).

/// Implements resolvo's `DependencyProvider` and `Interner` traits to present a
/// sudoku puzzle as a package resolution problem.
struct SudokuProvider {
    pool: Pool<DigitSet>,
    /// Pre-filled digits. `givens[row * 9 + col] = Some(d)` means the cell is fixed.
    givens: [Option<u8>; 81],
    /// Flat lookup: `solvables[cell * 9 + (digit - 1)]` gives the SolvableId for
    /// "cell X takes digit D".
    solvables: Vec<SolvableId>,
    /// One NameId per cell, indexed by `row * 9 + col`.
    names: Vec<NameId>,
}

impl SudokuProvider {
    fn new(givens: [Option<u8>; 81]) -> Self {
        let pool = Pool::new();
        let mut names = Vec::with_capacity(81);
        let mut solvables = Vec::with_capacity(81 * 9);

        // Register 81 "packages" (cells) with 9 "versions" (digits) each.
        for cell in 0..81 {
            let row = cell / 9;
            let col = cell % 9;
            let name = pool.intern_package_name(format!("r{}c{}", row, col));
            names.push(name);

            for digit in 1..=9u8 {
                let solvable = pool.intern_solvable(name, digit);
                solvables.push(solvable);
            }
        }

        Self {
            pool,
            givens,
            solvables,
            names,
        }
    }

    fn solvable_id(&self, cell: usize, digit: u8) -> SolvableId {
        self.solvables[cell * 9 + (digit as usize - 1)]
    }

    /// Reverse lookup: given a solvable, return which cell and digit it represents.
    fn cell_and_digit(&self, solvable: SolvableId) -> (usize, u8) {
        let record = self.pool.resolve_solvable(solvable);
        let cell = self.names.iter().position(|&n| n == record.name).unwrap();
        (cell, record.record)
    }
}

// -- Interner impl ------------------------------------------------------------
//
// The Interner trait provides human-readable display for solver objects. This is
// used in error messages when a puzzle is unsolvable.

impl Interner for SudokuProvider {
    fn display_solvable(&self, solvable: SolvableId) -> impl Display + '_ {
        let record = self.pool.resolve_solvable(solvable);
        let cell = self.names.iter().position(|&n| n == record.name).unwrap();
        let row = cell / 9;
        let col = cell % 9;
        format!("r{}c{}={}", row, col, record.record)
    }

    fn display_merged_solvables(&self, solvables: &[SolvableId]) -> impl Display + '_ {
        solvables
            .iter()
            .map(|&id| self.display_solvable(id).to_string())
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn display_name(&self, name: NameId) -> impl Display + '_ {
        self.pool.resolve_package_name(name).clone()
    }

    fn display_version_set(&self, version_set: VersionSetId) -> impl Display + '_ {
        self.pool.resolve_version_set(version_set).to_string()
    }

    fn display_string(&self, string_id: StringId) -> impl Display + '_ {
        self.pool.resolve_string(string_id).to_owned()
    }

    fn version_set_name(&self, version_set: VersionSetId) -> NameId {
        self.pool.resolve_version_set_package_name(version_set)
    }

    fn solvable_name(&self, solvable: SolvableId) -> NameId {
        self.pool.resolve_solvable(solvable).name
    }

    fn version_sets_in_union(
        &self,
        version_set_union: VersionSetUnionId,
    ) -> impl Iterator<Item = VersionSetId> {
        self.pool.resolve_version_set_union(version_set_union)
    }

    fn resolve_condition(&self, condition: ConditionId) -> Condition {
        self.pool.resolve_condition(condition).clone()
    }
}

// -- DependencyProvider impl --------------------------------------------------
//
// This is where the sudoku rules are encoded. The key insight:
//
// - `get_candidates` tells the solver what digits are possible for each cell.
//   Pre-filled cells have a single `locked` candidate.
//
// - `get_dependencies` encodes the sudoku constraint: when a cell is assigned
//   digit D, every peer cell (same row, column, or 3x3 box) is constrained to
//   NOT contain digit D. This is expressed via `constrains` — resolvo's mechanism
//   for saying "if package X is in the solution, it must satisfy this version set."
//
// - `filter_candidates` applies a DigitSet constraint to narrow candidates.

impl SudokuProvider {
    /// Returns the 20 peer cell indices for a given cell — all cells that share
    /// the same row, column, or 3x3 box (excluding the cell itself).
    fn peers(cell: usize) -> impl Iterator<Item = usize> {
        let row = cell / 9;
        let col = cell % 9;
        let box_row = (row / 3) * 3;
        let box_col = (col / 3) * 3;

        let row_peers = (0..9).map(move |c| row * 9 + c);
        let col_peers = (0..9).map(move |r| r * 9 + col);
        let box_peers =
            (0..3).flat_map(move |r| (0..3).map(move |c| (box_row + r) * 9 + box_col + c));

        row_peers
            .chain(col_peers)
            .chain(box_peers)
            .filter(move |&peer| peer != cell)
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
    }
}

impl DependencyProvider for SudokuProvider {
    async fn filter_candidates(
        &self,
        candidates: &[SolvableId],
        version_set: VersionSetId,
        inverse: bool,
    ) -> Vec<SolvableId> {
        let digit_set = self.pool.resolve_version_set(version_set);
        candidates
            .iter()
            .copied()
            .filter(|&solvable| {
                let record = self.pool.resolve_solvable(solvable);
                let matches = digit_set.contains(record.record);
                if inverse { !matches } else { matches }
            })
            .collect()
    }

    async fn get_candidates(&self, name: NameId) -> Option<Candidates> {
        let cell = self.names.iter().position(|&n| n == name)?;

        let candidates: Vec<SolvableId> = (1..=9u8)
            .map(|digit| self.solvable_id(cell, digit))
            .collect();

        // If this cell has a pre-filled digit, lock the solver to that single candidate.
        let locked = self.givens[cell].map(|digit| self.solvable_id(cell, digit));

        Some(Candidates {
            candidates,
            locked,
            favored: None,
            hint_dependencies_available: HintDependenciesAvailable::All,
            excluded: Vec::new(),
        })
    }

    async fn sort_candidates(&self, _solver: &SolverCache<Self>, solvables: &mut [SolvableId]) {
        solvables.sort_by_key(|&solvable| self.pool.resolve_solvable(solvable).record);
    }

    async fn get_dependencies(&self, solvable: SolvableId) -> Dependencies {
        let (cell, digit) = self.cell_and_digit(solvable);

        // For each peer cell, add a constraint: "peer must NOT be this digit."
        // In resolvo terms, `constrains` means "the peer's version must match this set",
        // so we use the complement — all digits except the current one.
        let mut constrains = Vec::new();
        for peer in Self::peers(cell) {
            let peer_name = self.names[peer];
            let allowed = DigitSet(DigitSet::all().0 & !DigitSet::singleton(digit).0);
            let vs_id = self.pool.intern_version_set(peer_name, allowed);
            constrains.push(vs_id);
        }

        Dependencies::Known(KnownDependencies {
            requirements: Vec::new(),
            constrains,
        })
    }
}

// -- Puzzle I/O ---------------------------------------------------------------

/// Parses an 81-character string into a grid of givens. '.' or '0' means empty.
fn parse_puzzle(input: &str) -> Result<[Option<u8>; 81], String> {
    if input.len() != 81 {
        return Err(format!("Expected 81 characters, got {}", input.len()));
    }

    let mut givens = [None; 81];
    for (i, ch) in input.chars().enumerate() {
        match ch {
            '.' | '0' => {}
            '1'..='9' => givens[i] = Some(ch as u8 - b'0'),
            _ => return Err(format!("Invalid character '{}' at position {}", ch, i)),
        }
    }
    Ok(givens)
}

fn print_grid(grid: &[u8; 81]) {
    println!("┌───────┬───────┬───────┐");
    for row in 0..9 {
        if row == 3 || row == 6 {
            println!("├───────┼───────┼───────┤");
        }
        for col in 0..9 {
            if col % 3 == 0 {
                print!("│ ");
            }
            if grid[row * 9 + col] == 0 {
                print!(". ");
            } else {
                print!("{} ", grid[row * 9 + col]);
            }
        }
        println!("│");
    }
    println!("└───────┴───────┴───────┘");
}

// -- Main ---------------------------------------------------------------------

fn main() {
    let input = match std::env::args().nth(1) {
        Some(arg) => arg,
        None => {
            eprintln!("Usage: sudoku <81-character puzzle string>");
            eprintln!("  Use '.' or '0' for empty cells, '1'-'9' for givens.");
            eprintln!();
            eprintln!("Example:");
            eprintln!(
                "  cargo run --example sudoku -- \"53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79\""
            );
            process::exit(1);
        }
    };

    let givens = match parse_puzzle(&input) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    };

    // Print the unsolved puzzle.
    let mut puzzle_grid = [0u8; 81];
    for (i, g) in givens.iter().enumerate() {
        puzzle_grid[i] = g.unwrap_or(0);
    }
    print_grid(&puzzle_grid);
    println!();

    let provider = SudokuProvider::new(givens);

    // Each cell must be assigned exactly one digit. We express this as a
    // requirement per cell: "pick some version (digit) from DigitSet::all()."
    let requirements: Vec<ConditionalRequirement> = provider
        .names
        .iter()
        .map(|&name| {
            let version_set = provider.pool.intern_version_set(name, DigitSet::all());
            version_set.into()
        })
        .collect();

    let problem = Problem::new().requirements(requirements);

    // Solve using resolvo's CDCL SAT solver.
    let mut solver = Solver::new(provider);
    match solver.solve(problem) {
        Ok(solution) => {
            let mut grid = [0u8; 81];
            for solvable_id in solution {
                let (cell, digit) = solver.provider().cell_and_digit(solvable_id);
                grid[cell] = digit;
            }
            print_grid(&grid);
        }
        Err(_) => {
            eprintln!("No solution exists.");
            process::exit(1);
        }
    }
}
