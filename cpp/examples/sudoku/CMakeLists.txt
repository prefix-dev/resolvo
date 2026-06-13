cmake_minimum_required(VERSION 3.21)

project(ResolvoExampleSudoku LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# This file is used in two ways:
#
#  * As part of the top-level Resolvo build (via `add_subdirectory`), where the
#    `Resolvo::Resolvo` target already exists.
#  * Standalone, as the `resolvo-cpp-sudoku` Pixi package, where the bindings
#    are provided by the installed `resolvo-cpp` package and located through
#    `find_package`.
if(NOT TARGET Resolvo::Resolvo)
  find_package(Resolvo REQUIRED)
endif()

include(GNUInstallDirs)

add_executable(sudoku sudoku.cpp)
target_link_libraries(sudoku PRIVATE Resolvo::Resolvo)

set(gcc_like_cxx "$<COMPILE_LANG_AND_ID:CXX,ARMClang,AppleClang,Clang,GNU>")
set(msvc_cxx "$<COMPILE_LANG_AND_ID:CXX,MSVC>")
target_compile_options(
  sudoku PRIVATE "$<${gcc_like_cxx}:-Wall;-Wextra>" "$<${msvc_cxx}:/W3>")

install(TARGETS sudoku RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
