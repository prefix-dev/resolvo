cmake_minimum_required(VERSION 3.21)

# Select C++ and C as languages, as Corrosion needs ${CMAKE_C_COMPILER} for
# linking
project(Resolvo LANGUAGES C CXX)

# Add the Corrosion dependency (used to build Rust code)
include(FetchContent)
FetchContent_Declare(
  Corrosion
  GIT_REPOSITORY https://github.com/corrosion-rs/corrosion.git
  GIT_TAG v0.5.1)
FetchContent_MakeAvailable(Corrosion)

# Extract the version from the rust crate
corrosion_parse_package_version("${CMAKE_CURRENT_SOURCE_DIR}/Cargo.toml"
                                resolvo_cpp_version)
string(REPLACE "." ";" VERSION_LIST ${resolvo_cpp_version})
list(GET VERSION_LIST 0 resolvo_cpp_version_major)
list(GET VERSION_LIST 1 resolvo_cpp_version_minor)
list(GET VERSION_LIST 2 resolvo_cpp_version_patch)

# Add the Corrosion CMake module path to the list of paths to search for modules
list(PREPEND CMAKE_MODULE_PATH ${Corrosion_SOURCE_DIR}/cmake)
find_package(Rust 1.86 REQUIRED MODULE)

option(BUILD_SHARED_LIBS "Build Resolvo as shared library" ON)

set(RESOLVO_LIBRARY_CARGO_FLAGS
    ""
    CACHE STRING
          "Flags to pass to cargo when building the Resolvo runtime library")

if(BUILD_SHARED_LIBS)
  set(rustc_lib_type "cdylib")
  set(resolvo_cpp_impl "resolvo_cpp-shared")
  set(cmake_lib_type "SHARED")
else()
  set(rustc_lib_type "staticlib")
  set(resolvo_cpp_impl "resolvo_cpp-static")
  set(cmake_lib_type "STATIC")
endif()

corrosion_import_crate(
  MANIFEST_PATH
  "${CMAKE_CURRENT_SOURCE_DIR}/Cargo.toml"
  CRATES
  resolvo_cpp
  CRATE_TYPES
  bin
  ${rustc_lib_type})

# See
# https://corrosion-rs.github.io/corrosion/common_issues.html#missing-install_name-on-macos-for-ccdylibs--hardcoded-references-to-the-build-directory
if(APPLE
   AND RESOLVO_IS_TOPLEVEL_BUILD
   AND BUILD_SHARED_LIBS)
  corrosion_add_target_local_rustflags(
    resolvo_cpp
    -Clink-arg=-Wl,-install_name,@rpath/libresolvo_cpp.dylib,-current_version,${resolvo_cpp_version_major}.${resolvo_cpp_version_minor}.${resolvo_cpp_version_patch},-compatibility_version,${resolvo_cpp_version_major}.${resolvo_cpp_version_minor}.0
  )
  set_target_properties(resolvo_cpp-shared PROPERTIES IMPORTED_NO_SONAME 0)
  set_target_properties(resolvo_cpp-shared PROPERTIES IMPORTED_SONAME
                                                      libresolvo_cpp.dylib)
endif()

add_library(Resolvo INTERFACE)
add_library(Resolvo::Resolvo ALIAS Resolvo)
target_link_libraries(Resolvo INTERFACE resolvo_cpp)

set_property(
  TARGET resolvo_cpp
  APPEND
  PROPERTY
    CORROSION_ENVIRONMENT_VARIABLES
    "RESOLVO_GENERATED_INCLUDE_DIR=${CMAKE_CURRENT_BINARY_DIR}/generated_include/"
)

file(
  GLOB api_headers
  RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  "${CMAKE_CURRENT_SOURCE_DIR}/include/*.h")

foreach(header IN LISTS api_headers)
  set_property(
    TARGET Resolvo
    APPEND
    PROPERTY PUBLIC_HEADER include/${header})
endforeach()

set(generated_headers
    ${CMAKE_CURRENT_BINARY_DIR}/generated_include/resolvo_vector_internal.h
    ${CMAKE_CURRENT_BINARY_DIR}/generated_include/resolvo_string_internal.h
    ${CMAKE_CURRENT_BINARY_DIR}/generated_include/resolvo_internal.h)

foreach(header IN LISTS generated_headers)
  set_property(
    TARGET Resolvo
    APPEND
    PROPERTY PUBLIC_HEADER ${header})
endforeach()

target_include_directories(
  Resolvo
  INTERFACE $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/generated_include>
            $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
            $<INSTALL_INTERFACE:include/resolvo>)

include(GNUInstallDirs)

export(
  TARGETS Resolvo resolvo_cpp
  NAMESPACE Resolvo::
  FILE "${CMAKE_BINARY_DIR}/lib/cmake/Resolvo/ResolvoTargets.cmake")
install(
  EXPORT ResolvoTargets
  NAMESPACE Resolvo::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Resolvo)

install(
  TARGETS Resolvo resolvo_cpp
  EXPORT ResolvoTargets
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
  PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/resolvo)

if(BUILD_SHARED_LIBS)
  install(FILES $<TARGET_FILE:${resolvo_cpp_impl}> TYPE BIN)
  if(WIN32)
    install(FILES $<TARGET_LINKER_FILE:${resolvo_cpp_impl}> 
            TYPE LIB 
            RENAME resolvo_cpp.lib)
  endif()
else()
    install(FILES $<TARGET_FILE:${resolvo_cpp_impl}> TYPE LIB)
endif()

include(CMakePackageConfigHelpers)

function(_resolvo_write_configure_file)
  foreach(
    prop
    IMPORTED_LOCATION
    IMPORTED_LOCATION_DEBUG
    IMPORTED_LOCATION_RELEASE
    IMPORTED_LOCATION_RELWITHDEBINFO
    IMPORTED_LOCATION_MINSIZEREL
    IMPORTED_IMPLIB
    IMPORTED_IMPLIB_DEBUG
    IMPORTED_IMPLIB_RELEASE
    IMPORTED_IMPLIB_RELWITHDEBINFO
    IMPORTED_IMPLIB_MINSIZEREL)
    get_target_property(value ${resolvo_cpp_impl} ${prop})

    if(value)
      get_filename_component(value ${value} NAME)
      list(APPEND RESOLVO_LIB_PROPERTIES ${prop}
           "\${_IMPORT_PREFIX}/${CMAKE_INSTALL_LIBDIR}/${value}")
    endif()
  endforeach()

  foreach(prop IMPORTED_NO_SONAME IMPORTED_SONAME)
    get_target_property(value ${resolvo_cpp_impl} ${prop})
    if(value)
      list(APPEND RESOLVO_LIB_PROPERTIES ${prop} ${value})
    endif()
  endforeach()

  configure_package_config_file(
    "cmake/ResolvoConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfig.cmake"
    INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Resolvo)
endfunction()

cmake_language(DEFER CALL _resolvo_write_configure_file)

write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfigVersion.cmake
  VERSION
    ${resolvo_cpp_version_major}.${resolvo_cpp_version_minor}.${resolvo_cpp_version_patch}
  COMPATIBILITY SameMinorVersion)

install(
  FILES
    "${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/lib/cmake/Resolvo/ResolvoConfigVersion.cmake"
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Resolvo)

if(RESOLVO_BUILD_TESTING)
  add_subdirectory(tests)
endif()
