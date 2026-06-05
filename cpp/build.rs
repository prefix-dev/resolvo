use std::path::{Path, PathBuf};

use anyhow::Context;

fn main() -> anyhow::Result<()> {
    let manifest_dir = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap());

    println!("cargo:rerun-if-env-changed=RESOLVO_GENERATED_INCLUDE_DIR");
    let output_dir = std::env::var_os("RESOLVO_GENERATED_INCLUDE_DIR").unwrap_or_else(|| {
        Path::new(&std::env::var_os("OUT_DIR").unwrap())
            .join("generated_include")
            .into()
    });
    let output_dir = Path::new(&output_dir);

    println!("cargo:GENERATED_INCLUDE_DIR={}", output_dir.display());

    std::fs::create_dir_all(output_dir).context("Could not create the include directory")?;

    let mut default_config = cbindgen::Config::default();
    default_config.macro_expansion.bitflags = true;
    default_config.pragma_once = true;
    default_config.include_version = true;
    default_config.namespaces = Some(vec!["resolvo".into(), "cbindgen_private".into()]);
    default_config.line_length = 100;
    default_config.tab_width = 4;
    default_config.language = cbindgen::Language::Cxx;
    default_config.cpp_compat = true;
    default_config.documentation = true;
    default_config.documentation_style = cbindgen::DocumentationStyle::Doxy;
    default_config.structure.associated_constants_in_body = true;
    default_config.constant.allow_constexpr = true;
    default_config.export.exclude = vec!["Slice".into()];

    cbindgen::Builder::new()
        .with_config(default_config.clone())
        .with_src(manifest_dir.join("src/vector.rs"))
        .generate()
        .context("Unable to generate bindings for resolvo_vector_internal.h")?
        .write_to_file(output_dir.join("resolvo_vector_internal.h"));

    let mut string_config = default_config.clone();
    string_config.export.exclude = vec!["String".into()];

    cbindgen::Builder::new()
        .with_config(string_config.clone())
        .with_src(manifest_dir.join("src/string.rs"))
        .with_after_include("namespace resolvo { struct String; }")
        .generate()
        .context("Unable to generate bindings for resolvo_string_internal.h")?
        .write_to_file(output_dir.join("resolvo_string_internal.h"));

    let mut config = default_config.clone();
    config.export.exclude.extend(vec![
        "Vector".into(),
        "resolvo_vector_free".into(),
        "resolvo_vector_allocate".into(),
        "resolvo_vector_empty".into(),
        "String".into(),
        "resolvo_string_bytes".into(),
        "resolvo_string_drop".into(),
        "resolvo_string_clone".into(),
        "resolvo_string_from_bytes".into(),
    ]);
    config.export.body.insert(
        "Candidates".to_owned(),
        r"
    Candidates() : candidates{}, favored(nullptr), locked(nullptr), hint_dependencies_available{}, excluded{}, allow_multiple(false) {}
        "
        .to_owned(),
    );
    config.export.body.insert(
        "Slice".to_owned(),
        r"
    const T &operator[](int i) const { return ptr[i]; }
    /// Note: this doesn't initialize Slice properly, but we need to keep the struct as compatible with C
    constexpr Slice() = default;
    /// Rust uses a NonNull, so even empty slices shouldn't use nullptr
    constexpr Slice(const T *ptr, uintptr_t len) : ptr(ptr ? const_cast<T*>(ptr) : reinterpret_cast<T*>(sizeof(T))), len(len) {}"
            .to_owned(),
    );
    config.export.body.insert(
        "ConditionalRequirement".to_owned(),
        r"
    /**
     * Constructs a new conditional requirement with the specified condition
     * and requirement.
     */
    constexpr ConditionalRequirement(const ConditionId *condition, Requirement &&requirement) : condition(condition), requirement(std::forward<Requirement>(requirement)) {};
    /**
     * Constructs a new conditional requirement without a condition.
     */
    constexpr ConditionalRequirement(Requirement &&requirement) : condition(nullptr), requirement(std::forward<Requirement>(requirement)) {};
        ".to_owned());
    config.export.body.insert(
        "Requirement".to_owned(),
        r"
    constexpr Requirement(VersionSetId id) : tag(Tag::Single), single({id}) {};
    constexpr Requirement(VersionSetUnionId id) : tag(Tag::Union), union_({id}) {};

    constexpr bool is_union() const { return tag == Tag::Union; }
    constexpr bool is_single() const { return tag == Tag::Single; }
        "
        .to_owned(),
    );

    config.export.body.insert(
        "Condition".to_owned(),
        r"
    constexpr Condition(VersionSetId id) : tag(Tag::Requirement), requirement({id}) {};
    constexpr Condition(LogicalOperator op, ConditionId lhs, ConditionId rhs) : tag(Tag::Binary), binary({op, lhs, rhs}) {};

    constexpr bool is_binary() const { return tag == Tag::Requirement; }
    constexpr bool is_requirement() const { return tag == Tag::Binary; }
        ".to_owned());

    cbindgen::Builder::new()
        .with_config(config.clone())
        .with_src(manifest_dir.join("src/lib.rs"))
        .with_include("resolvo_slice.h")
        .with_include("resolvo_vector.h")
        .with_include("resolvo_string.h")
        .generate()
        .context("Unable to generate bindings for resolvo_internal.h")?
        .write_to_file(output_dir.join("resolvo_internal.h"));

    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=src/slice.rs");
    println!("cargo:rerun-if-changed=src/string.rs");
    println!("cargo:rerun-if-changed=src/vector.rs");

    Ok(())
}
