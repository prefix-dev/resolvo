# Resolvo C++ examples

Each example lives in its own subdirectory and is a self-contained `pixi build` package that depends on the `resolvo-cpp` bindings.

| Example | Package | Run from the repo root |
|---|---|---|
| [`sudoku`](./sudoku) | `resolvo-cpp-sudoku` | `pixi run cpp-example-sudoku` |

They can also be built in-tree with the rest of the C++ sources:

```shell
cmake -GNinja -S . -B build -DRESOLVO_BUILD_EXAMPLES=ON
cmake --build build
```
