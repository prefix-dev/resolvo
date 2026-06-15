# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.4.0](https://github.com/prefix-dev/resolvo/releases/tag/resolvo_cpp-v0.4.0) - 2026-06-15

This release bundles the `resolvo` solver up to `0.11.0`, bringing a number of
solver performance and correctness improvements to the C++ bindings.

### Added
- A runnable `sudoku` example under `cpp/examples`, porting the Rust sudoku example to C++ ([#241](https://github.com/prefix-dev/resolvo/pull/241)).
- `pixi build` packaging: the bindings (`resolvo-cpp`, `cpp/pixi.toml`) and the sudoku example (`resolvo-cpp-sudoku`, `cpp/examples/sudoku/pixi.toml`) are now defined as Pixi packages, with the example depending on the bindings via a path dependency. Run it from the workspace root with `pixi run cpp-example-sudoku` ([#241](https://github.com/prefix-dev/resolvo/pull/241)).
- Solver: `Pool::iter_solvables()` for iterating over interned solvables ([#229](https://github.com/prefix-dev/resolvo/pull/229)).

### Changed
- Document that provider-supplied ids (`SolvableId`, `NameId`, `VersionSetId`, ...) must be *dense* (contiguous and zero-based). This invariant cannot be validated at the FFI boundary, so it is now spelled out on each id type, on the `DependencyProvider` interface, and on the `Pool` helper ([#241](https://github.com/prefix-dev/resolvo/pull/241)).
- Raise the toolchain to Rust 1.89.0 and set a minimum supported Rust version (MSRV) of 1.85.1 ([#167](https://github.com/prefix-dev/resolvo/pull/167)).

### Fixed
- Don't merge conflict nodes with distinct requirements ([#233](https://github.com/prefix-dev/resolvo/pull/233)).
- Fix a panic in `add_pending_forbid_clauses` during conflict detection ([#231](https://github.com/prefix-dev/resolvo/pull/231)).
- Make all public solver types nameable ([#193](https://github.com/prefix-dev/resolvo/pull/193)).
- Strip trailing whitespace when a version set is empty ([#164](https://github.com/prefix-dev/resolvo/pull/164)).

### Performance
- (**breaking**) Use an explicit memory layout for externally provided ids (`SolvableId`, `NameId`) by converting them through `into_raw`/`from_raw` and pinning the `Interner` associated id types ([#224](https://github.com/prefix-dev/resolvo/pull/224)).
- Defer candidate loading for conditional requirements ([#237](https://github.com/prefix-dev/resolvo/pull/237)).
- Use an incremental work queue in `decide()` ([#238](https://github.com/prefix-dev/resolvo/pull/238)).
- Encode shared constraints with an auxiliary variable per version set ([#236](https://github.com/prefix-dev/resolvo/pull/236)).
- Encoding optimizations ([#221](https://github.com/prefix-dev/resolvo/pull/221)) and further minor performance optimizations ([#223](https://github.com/prefix-dev/resolvo/pull/223)).

## [0.3.0](https://github.com/prefix-dev/resolvo/releases/tag/resolvo_cpp-v0.3.0) - 2025-07-30

This release bundles the `resolvo` solver up to `0.10.0`, on top of the C++ changes below.

### Added
- (**breaking**) Support for conditional dependencies ([#136](https://github.com/prefix-dev/resolvo/pull/136)).
- A `HintDependenciesAvailable` type ([#123](https://github.com/prefix-dev/resolvo/pull/123)).
- Solver: diagnostics ([#85](https://github.com/prefix-dev/resolvo/pull/85)).
- Solver: expose conflict-graph internals for external consumption — the graph structs are now public, `ConflictGraph::simplify` is public, and `ConflictGraph` is `Clone` ([#152](https://github.com/prefix-dev/resolvo/pull/152), [#147](https://github.com/prefix-dev/resolvo/pull/147), [#145](https://github.com/prefix-dev/resolvo/pull/145)).

### Changed
- Bump to Rust edition 2024 ([#132](https://github.com/prefix-dev/resolvo/pull/132)).
- Update all dependencies ([#154](https://github.com/prefix-dev/resolvo/pull/154)).

### Fixed
- Use the correct import library name on Windows ([#163](https://github.com/prefix-dev/resolvo/pull/163)).
- Use the correct `libdir` on Unix.
- A constraint at the root can conflict ([#79](https://github.com/prefix-dev/resolvo/pull/79)).
- Handle a union clause that has no candidates ([#93](https://github.com/prefix-dev/resolvo/pull/93)).
- Avoid a panic in `Itertools::format_with` ([#108](https://github.com/prefix-dev/resolvo/pull/108)).
- Make the versions printed for merged solvables unique ([#106](https://github.com/prefix-dev/resolvo/pull/106)).
- Constraint formatting ([#80](https://github.com/prefix-dev/resolvo/pull/80)).
- Add the missing `Ord` trait for `NameId` ([#73](https://github.com/prefix-dev/resolvo/pull/73)).

### Performance
- Improve the encoding of clauses ([#131](https://github.com/prefix-dev/resolvo/pull/131)).
- Reintroduce the binary encoding of forbid-multiple clauses ([#91](https://github.com/prefix-dev/resolvo/pull/91)).
- Reduce the watch map memory size ([#92](https://github.com/prefix-dev/resolvo/pull/92)) and simplify watch map traversal ([#98](https://github.com/prefix-dev/resolvo/pull/98)).

## [0.2.1](https://github.com/prefix-dev/resolvo/releases/tag/resolvo_cpp-v0.2.1) - 2024-10-01

### Fixed
- Use `GNUInstallDirs` for installation locations ([#72](https://github.com/prefix-dev/resolvo/pull/72)).

## [0.2.0](https://github.com/prefix-dev/resolvo/releases/tag/resolvo_cpp-v0.2.0) - 2024-06-11

### Added
- More tracing ([#55](https://github.com/prefix-dev/resolvo/pull/55))
- (**breaking**) Version set unions as solvable requirements ([#56](https://github.com/prefix-dev/resolvo/pull/56))
- (**breaking**) Solve for optional solvables in addition to the root solvable ([#54](https://github.com/prefix-dev/resolvo/pull/54))
- (**breaking**) Add `Problem` struct ([#62](https://github.com/prefix-dev/resolvo/pull/62))
- (**breaking**) Decide on explicit requirements first ([#61](https://github.com/prefix-dev/resolvo/pull/61))

### Fixed
- Display_merged_solvables to display merged solvables correctly ([#48](https://github.com/prefix-dev/resolvo/pull/48))
- Add a virtual destructor to `DependencyProvider` ([#50](https://github.com/prefix-dev/resolvo/pull/50))
- Fix off-by-one error in `Mapping::serialize` ([#58](https://github.com/prefix-dev/resolvo/pull/58))

### Performance
* Visit less clauses during propagation ([#66](https://github.com/prefix-dev/resolvo/pull/66))
* Implement a form of VSIDS ([#67](https://github.com/prefix-dev/resolvo/pull/67))

## [0.1.0](https://github.com/prefix-dev/resolvo/releases/tag/resolvo_cpp-v0.1.0) - 2024-06-11

### Added
- c++ bindings ([#41](https://github.com/prefix-dev/resolvo/pull/41))
