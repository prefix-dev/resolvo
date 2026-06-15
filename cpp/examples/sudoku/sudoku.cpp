/**
 * Solves sudoku puzzles using resolvo's CDCL SAT solver.
 *
 * This is a C++ port of the Rust `sudoku` example (`examples/sudoku.rs`). It
 * demonstrates that resolvo, a package dependency resolver, can solve
 * constraint satisfaction problems beyond package resolution. It maps sudoku
 * concepts onto resolvo's domain model:
 *
 *   | Sudoku               | Resolvo                | Example                       |
 *   |----------------------|------------------------|-------------------------------|
 *   | Cell (81 total)      | Package (`NameId`)     | `r0c0`, `r4c7`                |
 *   | Digit 1-9 for cell   | Version (`SolvableId`) | `r0c0=5`                      |
 *   | "Cell needs a digit" | Requirement            | "install r0c0"                |
 *   | Row/col/box rules    | Constraint             | "r0c0 excludes 5 from peers"  |
 *   | Pre-filled cell      | Locked candidate       | "r0c0 must be 5"              |
 *
 * Usage:
 *   sudoku "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79"
 *
 * Note on ids: resolvo requires dense (contiguous, zero-based) ids. This example
 * gets them by construction: cells are numbered `0..81` and used as `NameId`s,
 * the solvable for "cell C takes digit D" is at index `C * 9 + (D - 1)`, and
 * version sets come from a `resolvo::Pool`.
 */

#include <resolvo.h>
#include <resolvo_pool.h>

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

namespace {

/// The number of cells along one side of the grid, and the number of digits.
constexpr int N = 9;
/// The total number of cells in the grid.
constexpr int CELLS = N * N;

// -- DigitSet -----------------------------------------------------------------
//
// Resolvo's "versions" are sudoku digits 1-9; a "version set" is a subset of
// them, stored as a bitmask (bit N set means digit N is in the set).
struct DigitSet {
    /// All digits 1-9 (bits 1..=9 set). Used as the "any version" requirement.
    static constexpr uint16_t all() { return 0b1111111110; }

    /// A single digit. Used to build exclusion constraints between peer cells.
    static constexpr uint16_t singleton(uint8_t digit) {
        return static_cast<uint16_t>(1u << digit);
    }

    static bool contains(uint16_t set, uint8_t digit) { return (set & (1u << digit)) != 0; }

    /// Renders a set as `{1, 2, 3}` for error messages.
    static std::string to_string(uint16_t set) {
        std::stringstream ss;
        ss << "{";
        bool first = true;
        for (uint8_t digit = 1; digit <= 9; ++digit) {
            if (!contains(set, digit)) {
                continue;
            }
            if (!first) {
                ss << ", ";
            }
            first = false;
            ss << static_cast<int>(digit);
        }
        ss << "}";
        return ss.str();
    }
};

/// A set of digits tied to a cell (package). Interned via `resolvo::Pool` so
/// equal version sets share a dense id.
struct VersionSet {
    resolvo::NameId name;
    uint16_t digits;

    friend bool operator==(const VersionSet& a, const VersionSet& b) {
        return a.name == b.name && a.digits == b.digits;
    }
};

}  // namespace

namespace std {
template <>
struct hash<VersionSet> {
    std::size_t operator()(const VersionSet& vs) const {
        return std::hash<uint64_t>()((static_cast<uint64_t>(vs.name.id) << 16) | vs.digits);
    }
};
}  // namespace std

namespace {

/// Returns the 20 peer cell indices for a given cell: every cell sharing the
/// same row, column, or 3x3 box (excluding the cell itself).
std::vector<int> peers(int cell) {
    int row = cell / N;
    int col = cell % N;
    int box_row = (row / 3) * 3;
    int box_col = (col / 3) * 3;

    std::set<int> result;
    for (int c = 0; c < N; ++c) {
        result.insert(row * N + c);
    }
    for (int r = 0; r < N; ++r) {
        result.insert(r * N + col);
    }
    for (int r = 0; r < 3; ++r) {
        for (int c = 0; c < 3; ++c) {
            result.insert((box_row + r) * N + (box_col + c));
        }
    }
    result.erase(cell);
    return {result.begin(), result.end()};
}

// -- SudokuProvider -----------------------------------------------------------
//
// Bridges sudoku to the solver: which packages exist (cells), which versions
// are available (digits), and which constraints apply (the sudoku rules).
struct SudokuProvider : public resolvo::DependencyProvider {
    /// Pre-filled digits. `givens[cell]` is 0 for an empty cell, 1-9 otherwise.
    std::array<uint8_t, CELLS> givens;
    /// Stable backing for the `locked` pointer returned by `get_candidates`.
    std::array<resolvo::SolvableId, CELLS> locked_storage{};
    /// Interns version sets, handing out dense `VersionSetId`s.
    resolvo::Pool<resolvo::VersionSetId, VersionSet> version_sets;

    explicit SudokuProvider(const std::array<uint8_t, CELLS>& givens) : givens(givens) {}

    /// The dense `SolvableId` for "cell C takes digit D".
    static resolvo::SolvableId solvable_id(int cell, uint8_t digit) {
        return resolvo::SolvableId{static_cast<uint32_t>(cell * N + (digit - 1))};
    }

    /// Reverse lookup: which cell and digit a solvable represents.
    static std::pair<int, uint8_t> cell_and_digit(resolvo::SolvableId solvable) {
        int cell = static_cast<int>(solvable.id) / N;
        uint8_t digit = static_cast<uint8_t>(solvable.id % N + 1);
        return {cell, digit};
    }

    /// Interns a version set for the given cell, returning its dense id.
    resolvo::VersionSetId intern_version_set(resolvo::NameId name, uint16_t digits) {
        return version_sets.alloc(VersionSet{name, digits});
    }

    // -- Interner / display methods -------------------------------------------
    // Human-readable output for error messages when a puzzle is unsolvable.

    resolvo::String display_solvable(resolvo::SolvableId solvable) override {
        auto [cell, digit] = cell_and_digit(solvable);
        std::stringstream ss;
        ss << "r" << (cell / N) << "c" << (cell % N) << "=" << static_cast<int>(digit);
        return resolvo::String(ss.str());
    }

    resolvo::String display_merged_solvables(
        resolvo::Slice<resolvo::SolvableId> solvables) override {
        std::stringstream ss;
        bool first = true;
        for (auto solvable : solvables) {
            if (!first) {
                ss << ", ";
            }
            first = false;
            ss << std::string_view(display_solvable(solvable));
        }
        return resolvo::String(ss.str());
    }

    resolvo::String display_name(resolvo::NameId name) override {
        int cell = static_cast<int>(name.id);
        std::stringstream ss;
        ss << "r" << (cell / N) << "c" << (cell % N);
        return resolvo::String(ss.str());
    }

    resolvo::String display_version_set(resolvo::VersionSetId version_set) override {
        return resolvo::String(DigitSet::to_string(version_sets[version_set].digits));
    }

    resolvo::String display_string(resolvo::StringId) override { return resolvo::String(); }

    resolvo::NameId version_set_name(resolvo::VersionSetId version_set_id) override {
        return version_sets[version_set_id].name;
    }

    resolvo::NameId solvable_name(resolvo::SolvableId solvable_id) override {
        return resolvo::NameId{solvable_id.id / N};
    }

    resolvo::Slice<resolvo::VersionSetId> version_sets_in_union(
        resolvo::VersionSetUnionId) override {
        // Sudoku never uses version set unions.
        return resolvo::Slice<resolvo::VersionSetId>(nullptr, 0);
    }

    resolvo::Condition resolve_condition(resolvo::ConditionId) override {
        // Sudoku never uses conditions.
        return resolvo::Condition(resolvo::VersionSetId{0});
    }

    // -- DependencyProvider methods -------------------------------------------
    // Where the sudoku rules are encoded.

    resolvo::Candidates get_candidates(resolvo::NameId package) override {
        int cell = static_cast<int>(package.id);

        resolvo::Candidates result;
        for (uint8_t digit = 1; digit <= 9; ++digit) {
            result.candidates.push_back(solvable_id(cell, digit));
        }

        result.favored = nullptr;

        // If this cell is pre-filled, lock the solver to that single candidate.
        if (givens[cell] != 0) {
            locked_storage[cell] = solvable_id(cell, givens[cell]);
            result.locked = &locked_storage[cell];
        } else {
            result.locked = nullptr;
        }

        return result;
    }

    void sort_candidates(resolvo::Slice<resolvo::SolvableId> solvables) override {
        std::sort(
            solvables.begin(), solvables.end(),
            [](resolvo::SolvableId a, resolvo::SolvableId b) { return (a.id % N) < (b.id % N); });
    }

    resolvo::Vector<resolvo::SolvableId> filter_candidates(
        resolvo::Slice<resolvo::SolvableId> solvables, resolvo::VersionSetId version_set_id,
        bool inverse) override {
        resolvo::Vector<resolvo::SolvableId> result;
        const auto& version_set = version_sets[version_set_id];
        for (auto solvable : solvables) {
            uint8_t digit = static_cast<uint8_t>(solvable.id % N + 1);
            bool matches = DigitSet::contains(version_set.digits, digit);
            if (matches != inverse) {
                result.push_back(solvable);
            }
        }
        return result;
    }

    resolvo::Dependencies get_dependencies(resolvo::SolvableId solvable) override {
        auto [cell, digit] = cell_and_digit(solvable);

        // Constrain every peer to "not this digit". `constrains` matches a
        // version set, so we pass the complement: all digits except this one.
        resolvo::Dependencies result;
        uint16_t allowed = static_cast<uint16_t>(DigitSet::all() & ~DigitSet::singleton(digit));
        for (int peer : peers(cell)) {
            auto peer_name = resolvo::NameId{static_cast<uint32_t>(peer)};
            result.constrains.push_back(intern_version_set(peer_name, allowed));
        }
        return result;
    }
};

// -- Puzzle I/O ---------------------------------------------------------------

/// Parses an 81-character string into a grid of givens. '.' or '0' means empty.
bool parse_puzzle(std::string_view input, std::array<uint8_t, CELLS>& givens, std::string& error) {
    if (input.size() != CELLS) {
        std::stringstream ss;
        ss << "Expected " << CELLS << " characters, got " << input.size();
        error = ss.str();
        return false;
    }

    givens.fill(0);
    for (std::size_t i = 0; i < input.size(); ++i) {
        char ch = input[i];
        if (ch == '.' || ch == '0') {
            continue;
        }
        if (ch >= '1' && ch <= '9') {
            givens[i] = static_cast<uint8_t>(ch - '0');
            continue;
        }
        std::stringstream ss;
        ss << "Invalid character '" << ch << "' at position " << i;
        error = ss.str();
        return false;
    }
    return true;
}

void print_grid(const std::array<uint8_t, CELLS>& grid) {
    std::cout << "┌───────┬───────┬───────┐\n";
    for (int row = 0; row < N; ++row) {
        if (row == 3 || row == 6) {
            std::cout << "├───────┼───────┼───────┤\n";
        }
        for (int col = 0; col < N; ++col) {
            if (col % 3 == 0) {
                std::cout << "│ ";
            }
            uint8_t value = grid[row * N + col];
            if (value == 0) {
                std::cout << ". ";
            } else {
                std::cout << static_cast<int>(value) << " ";
            }
        }
        std::cout << "│\n";
    }
    std::cout << "└───────┴───────┴───────┘\n";
}

}  // namespace

int main(int argc, char** argv) {
    std::string input;
    if (argc >= 2) {
        input = argv[1];
    } else {
        std::cerr << "No puzzle provided, using the built-in example.\n";
        std::cerr << "Usage: sudoku <81-character puzzle string>\n";
        std::cerr << "  Use '.' or '0' for empty cells, '1'-'9' for givens.\n\n";
        input = "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79";
    }

    std::array<uint8_t, CELLS> givens{};
    std::string error;
    if (!parse_puzzle(input, givens, error)) {
        std::cerr << "Error: " << error << "\n";
        return 1;
    }

    // Print the unsolved puzzle.
    print_grid(givens);
    std::cout << "\n";

    SudokuProvider provider(givens);

    // Each cell needs one digit: a requirement per cell over DigitSet::all().
    resolvo::Vector<resolvo::ConditionalRequirement> requirements;
    for (uint32_t cell = 0; cell < CELLS; ++cell) {
        auto name = resolvo::NameId{cell};
        auto version_set = provider.intern_version_set(name, DigitSet::all());
        requirements.push_back(resolvo::ConditionalRequirement(resolvo::Requirement(version_set)));
    }

    resolvo::Problem problem = {requirements, {}, {}};

    // Solve using resolvo's CDCL SAT solver, timing how long it takes.
    resolvo::Vector<resolvo::SolvableId> result;
    auto start = std::chrono::steady_clock::now();
    resolvo::String solve_error = resolvo::solve(provider, problem, result);
    auto elapsed = std::chrono::steady_clock::now() - start;
    auto elapsed_ms = std::chrono::duration<double, std::milli>(elapsed).count();

    if (!std::string_view(solve_error).empty()) {
        std::cerr << "No solution exists. The solver found these conflicts:\n\n";
        std::cerr << std::string_view(solve_error) << "\n";
        std::cerr << "\nSolver ran for " << elapsed_ms << " ms.\n";
        return 1;
    }

    std::array<uint8_t, CELLS> grid{};
    for (auto solvable : result) {
        auto [cell, digit] = SudokuProvider::cell_and_digit(solvable);
        grid[cell] = digit;
    }
    print_grid(grid);
    std::cout << "\nSolved in " << elapsed_ms << " ms.\n";

    return 0;
}
