use std::fmt::{self, Display};
use std::process;

use resolvo::utils::{Pool, VersionSet};
use resolvo::{
    Candidates, Condition, ConditionId, ConditionalRequirement, Dependencies, DependencyProvider,
    HintDependenciesAvailable, Interner, KnownDependencies, NameId, Problem, SolvableId, Solver,
    SolverCache, StringId, VersionSetId, VersionSetUnionId,
};

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

struct SudokuProvider {
    pool: Pool<DigitSet>,
    givens: [Option<u8>; 81],
    solvables: Vec<SolvableId>,
    names: Vec<NameId>,
}

impl SudokuProvider {
    fn new(givens: [Option<u8>; 81]) -> Self {
        let pool = Pool::new();
        let mut names = Vec::with_capacity(81);
        let mut solvables = Vec::with_capacity(81 * 9);

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

    fn cell_and_digit(&self, solvable: SolvableId) -> (usize, u8) {
        let record = self.pool.resolve_solvable(solvable);
        let cell = self.names.iter().position(|&n| n == record.name).unwrap();
        (cell, record.record)
    }
}

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

impl SudokuProvider {
    /// Returns the indices of the 20 peer cells (same row, column, or box) for a given cell.
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
            print!("{} ", grid[row * 9 + col]);
        }
        println!("│");
    }
    println!("└───────┴───────┴───────┘");
}

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

    let provider = SudokuProvider::new(givens);

    let requirements: Vec<ConditionalRequirement> = provider
        .names
        .iter()
        .map(|&name| {
            let version_set = provider.pool.intern_version_set(name, DigitSet::all());
            version_set.into()
        })
        .collect();

    let problem = Problem::new().requirements(requirements);

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
