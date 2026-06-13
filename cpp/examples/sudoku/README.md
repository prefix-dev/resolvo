# Resolvo C++ sudoku example

A small, runnable example that solves sudoku puzzles using resolvo's CDCL SAT solver. It is a C++ port of the Rust [`sudoku` example](../../../examples/sudoku.rs) and demonstrates that resolvo, a package dependency resolver, can solve constraint satisfaction problems beyond package resolution.

## The idea

The example models a sudoku puzzle as a package resolution problem by mapping sudoku concepts onto resolvo's domain model:

| Sudoku               | Resolvo                | Example                       |
|----------------------|------------------------|-------------------------------|
| Cell (81 total)      | Package (`NameId`)     | `r0c0`, `r4c7`                |
| Digit 1-9 for cell   | Version (`SolvableId`) | `r0c0=5`                      |
| "Cell needs a digit" | Requirement            | "install r0c0"                |
| Row/col/box rules    | Constraint             | "r0c0 excludes 5 from peers"  |
| Pre-filled cell      | Locked candidate       | "r0c0 must be 5"              |

Each cell becomes a package that must be "installed", and each digit a version of that package. The sudoku rule "no digit repeats in a row, column or box" is encoded with resolvo's `constrains` mechanism: assigning a digit to a cell constrains all 20 of its peer cells to not take that digit. Pre-filled cells are expressed as a single `locked` candidate.

See the doc comment at the top of [`sudoku.cpp`](./sudoku.cpp) for a full walkthrough of the implementation.

## Running it

### With Pixi (recommended)

From the repository root, run the example as a Pixi package. This builds the `resolvo-cpp` bindings and the `resolvo-cpp-sudoku` package (which depends on them) and runs the solver:

```shell
# Solve the built-in example puzzle.
pixi run cpp-example-sudoku

# Solve your own puzzle: an 81-character string, '.' or '0' for empty cells.
pixi run cpp-example-sudoku "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79"
```

The example prints the unsolved grid, the solved grid, and how long the solve took:

```
┌───────┬───────┬───────┐
│ 5 3 4 │ 6 7 8 │ 9 1 2 │
│ 6 7 2 │ 1 9 5 │ 3 4 8 │
│ 1 9 8 │ 3 4 2 │ 5 6 7 │
├───────┼───────┼───────┤
│ 8 5 9 │ 7 6 1 │ 4 2 3 │
│ 4 2 6 │ 8 5 3 │ 7 9 1 │
│ 7 1 3 │ 9 2 4 │ 8 5 6 │
├───────┼───────┼───────┤
│ 9 6 1 │ 5 3 7 │ 2 8 4 │
│ 2 8 7 │ 4 1 9 │ 6 3 5 │
│ 3 4 5 │ 2 8 6 │ 1 7 9 │
└───────┴───────┴───────┘

Solved in 18.5 ms.
```

If the puzzle has no solution, resolvo's human-readable conflict report is printed instead.

### With CMake (in-tree)

The example is also built as part of the top-level CMake build when `RESOLVO_BUILD_EXAMPLES` is enabled:

```shell
cmake -GNinja -S . -B build -DRESOLVO_BUILD_EXAMPLES=ON
cmake --build build
./build/cpp/examples/sudoku/sudoku "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79"
```
