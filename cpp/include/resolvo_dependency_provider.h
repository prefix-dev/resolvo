#pragma once

#include "resolvo_internal.h"
#include "resolvo_slice.h"
#include "resolvo_string.h"
#include "resolvo_vector.h"

namespace resolvo {
using cbindgen_private::Candidates;
using cbindgen_private::Condition;
using cbindgen_private::ConditionalRequirement;
using cbindgen_private::ConditionId;
using cbindgen_private::Dependencies;
using cbindgen_private::ExcludedSolvable;
using cbindgen_private::NameId;
using cbindgen_private::SolvableId;
using cbindgen_private::StringId;
using cbindgen_private::VersionSetId;
using cbindgen_private::VersionSetUnionId;

/**
 * An interface that implements ecosystem specific logic.
 *
 * Every id handed to resolvo through this interface (`NameId`, `SolvableId`,
 * `VersionSetId`, `VersionSetUnionId`, `StringId` and `ConditionId`) must be
 * *dense*: allocated as a contiguous, zero-based sequence (`0, 1, 2, ...`)
 * without gaps. Resolvo uses these ids directly to index vector-backed
 * storage, so gaps waste memory and the largest id you hand out determines the
 * size of several internal allocations. This invariant cannot be validated at
 * the FFI boundary, so upholding it is the responsibility of the
 * implementation. The `resolvo::Pool` helper hands out dense ids for you. See
 * the documentation on `SolvableId` for the full rationale.
 */
struct DependencyProvider {
    virtual ~DependencyProvider() = default;

    /**
     * Returns a user-friendly string representation of the specified solvable.
     *
     * When formatting the solvable, it should it include both the name of
     * the package and any other identifying properties.
     */
    virtual String display_solvable(SolvableId solvable) = 0;

    /**
     * Returns a user-friendly string representation of the name of the
     * specified solvable.
     */
    virtual String display_solvable_name(SolvableId solvable) {
        return display_name(solvable_name(solvable));
    }

    /**
     * Returns a string representation of multiple solvables merged together.
     *
     * When formatting the solvables, both the name of the packages and any
     * other identifying properties should be included.
     */
    virtual String display_merged_solvables(Slice<SolvableId> solvable) = 0;

    /**
     * Returns an object that can be used to display the given name in a
     * user-friendly way.
     */
    virtual String display_name(NameId name) = 0;

    /**
     * Returns a user-friendly string representation of the specified version
     * set.
     *
     * The name of the package should *not* be included in the display. Where
     * appropriate, this information is added.
     */
    virtual String display_version_set(VersionSetId version_set) = 0;

    /**
     * Returns the string representation of the specified string.
     */
    virtual String display_string(StringId string) = 0;

    /**
     * Returns the name of the package that the specified version set is
     * associated with.
     */
    virtual NameId version_set_name(VersionSetId version_set_id) = 0;

    /**
     * Returns the name of the package for the given solvable.
     */
    virtual NameId solvable_name(SolvableId solvable_id) = 0;

    /**
     * Returns the version sets comprising the given union.
     */
    virtual Slice<VersionSetId> version_sets_in_union(VersionSetUnionId version_set_union_id) = 0;

    /**
     * Returns the condition that the given condition id describes
     */
    virtual Condition resolve_condition(ConditionId condition) = 0;

    /**
     * Obtains a list of solvables that should be considered when a package
     * with the given name is requested.
     */
    virtual Candidates get_candidates(NameId package) = 0;

    /**
     * Sort the specified solvables based on which solvable to try first. The
     * solver will iteratively try to select the highest version. If a
     * conflict is found with the highest version the next version is
     * tried. This continues until a solution is found.
     */
    virtual void sort_candidates(Slice<SolvableId> solvables) = 0;

    /**
     * Given a set of solvables, return the candidates that match the given
     * version set or if `inverse` is true, the candidates that do *not* match
     * the version set.
     */
    virtual Vector<SolvableId> filter_candidates(Slice<SolvableId> candidates,
                                                 VersionSetId version_set_id, bool inverse) = 0;

    /**
     * Returns the dependencies for the specified solvable.
     */
    virtual Dependencies get_dependencies(SolvableId solvable) = 0;
};

namespace private_api {
extern "C" inline void bridge_display_solvable(void *data, SolvableId solvable, String *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->display_solvable(solvable);
}
extern "C" inline void bridge_display_solvable_name(void *data, SolvableId solvable,
                                                    String *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->display_solvable_name(solvable);
}
extern "C" inline void bridge_display_merged_solvables(void *data, Slice<SolvableId> solvable,
                                                       String *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->display_merged_solvables(solvable);
}
extern "C" inline void bridge_display_name(void *data, NameId name, String *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->display_name(name);
}
extern "C" inline void bridge_display_version_set(void *data, VersionSetId version_set,
                                                  String *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->display_version_set(version_set);
}
extern "C" inline void bridge_display_string(void *data, StringId string, String *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->display_string(string);
}

extern "C" inline NameId bridge_version_set_name(void *data, VersionSetId version_set_id) {
    return reinterpret_cast<DependencyProvider *>(data)->version_set_name(version_set_id);
}
extern "C" inline NameId bridge_solvable_name(void *data, SolvableId solvable_id) {
    return reinterpret_cast<DependencyProvider *>(data)->solvable_name(solvable_id);
}
extern "C" inline void bridge_resolve_condition(void *data, ConditionId solvable_id,
                                                Condition *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->resolve_condition(solvable_id);
}

// HACK(clang): For some reason, clang needs this to know that the return type is complete
static_assert(sizeof(Slice<VersionSetId>));

extern "C" inline void bridge_version_sets_in_union(void *data,
                                                    VersionSetUnionId version_set_union_id,
                                                    Slice<VersionSetId> *result) {
    *result =
        reinterpret_cast<DependencyProvider *>(data)->version_sets_in_union(version_set_union_id);
}

extern "C" inline void bridge_get_candidates(void *data, NameId package, Candidates *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->get_candidates(package);
}
extern "C" inline void bridge_sort_candidates(void *data, Slice<SolvableId> solvables) {
    return reinterpret_cast<DependencyProvider *>(data)->sort_candidates(solvables);
}
extern "C" inline void bridge_filter_candidates(void *data, Slice<SolvableId> candidates,
                                                VersionSetId version_set_id, bool inverse,
                                                Vector<SolvableId> *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->filter_candidates(
        candidates, version_set_id, inverse);
}
extern "C" inline void bridge_get_dependencies(void *data, SolvableId solvable,
                                               Dependencies *result) {
    *result = reinterpret_cast<DependencyProvider *>(data)->get_dependencies(solvable);
}

}  // namespace private_api
}  // namespace resolvo
