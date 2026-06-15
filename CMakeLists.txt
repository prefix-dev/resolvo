cmake_minimum_required(VERSION 3.21)

project(resolvo LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include(FeatureSummary)

option(RESOLVO_BUILD_TESTING "Build tests" OFF)
add_feature_info(RESOLVO_BUILD_TESTING RESOLVO_BUILD_TESTING
                 "configure whether to build the test suite")
include(CTest)

option(RESOLVO_BUILD_EXAMPLES "Build examples" OFF)
add_feature_info(RESOLVO_BUILD_EXAMPLES RESOLVO_BUILD_EXAMPLES
                 "configure whether to build the examples")

set(RESOLVO_IS_TOPLEVEL_BUILD TRUE)

# Place all compiled examples into the same bin directory on Windows, where
# we'll also put the dll
if(WIN32)
  set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY_DEBUG ${CMAKE_BINARY_DIR}/bin/debug)
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY_RELEASE ${CMAKE_BINARY_DIR}/bin/release)
elseif(APPLE)
  # On macOS, the resolvo_cpp.dylib's install_name uses @rpath. CMake doesn't
  # set BUILD_RPATH for imported targets though, so include the directory here
  # by hand in the rpath used to build binaries in the build tree (such as our
  # examples or tests).
  set(CMAKE_BUILD_RPATH ${CMAKE_BINARY_DIR}/cpp)
endif()

add_subdirectory(cpp/)

feature_summary(WHAT ENABLED_FEATURES DESCRIPTION "Enabled features:")
feature_summary(WHAT DISABLED_FEATURES DESCRIPTION "Disabled features:")
