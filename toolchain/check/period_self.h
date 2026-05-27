// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#ifndef CARBON_TOOLCHAIN_CHECK_PERIOD_SELF_H_
#define CARBON_TOOLCHAIN_CHECK_PERIOD_SELF_H_

#include "toolchain/check/context.h"
#include "toolchain/check/subst.h"
#include "toolchain/sem_ir/ids.h"

namespace Carbon::Check {

// Introduce `.Self` as a symbolic binding into the current scope, and return
// the `SymbolicBinding` instruction.
//
// The type of `.Self` must be a `FacetType`, so that it gets wrapped in
// `FacetAccessType` when used in a type position, such as in `U:! I(.Self)`.
// This allows substitution with other facet values without requiring an
// additional `FacetAccessType` to be inserted.
auto MakePeriodSelfFacetValue(Context& context, SemIR::LocId loc_id,
                              SemIR::TypeId self_type_id,
                              SemIR::ElementIndex depth,
                              bool insert_name = true) -> SemIR::InstId;

// Get the depth of a `.Self` facet, which represents the number of `where`
// clauses it is nested within.
auto GetPeriodSelfDepth(Context& context, SemIR::SymbolicBinding bind)
    -> SemIR::ElementIndex;

auto GetPeriodSelfAbstract(Context& context, SemIR::InstId inst_id) -> bool;

enum class SubstPeriodSelfBehaviour {
  ImplicitOnly,
  ExplicitOnly,
  All,
};

using SubstPeriodSelfRebuildInst =
    llvm::function_ref<auto(SemIR::Inst)->SemIR::InstId>;

// Replace `.Self` references in `const_id` with `period_self_replacement_id`.
//
// The `behaviour` specifies if all `.Self` are replaced or just implicit use in
// designators. The `rebuild` callback can optionally be specified to override
// how an instruction is re-constructed to form an InstId after replacement. It
// can return None to fall back to the default of evaluating the inst.
auto SubstPeriodSelf(
    Context& context, SemIR::LocId loc_id, SemIR::ConstantId const_id,
    SemIR::ElementIndex abstract_depth,
    SemIR::ConstantId period_self_replacement_id,
    SubstPeriodSelfBehaviour behaviour = SubstPeriodSelfBehaviour::All,
    SubstPeriodSelfRebuildInst rebuild = nullptr) -> SemIR::ConstantId;

// FIXME: Docs. Mention matching_depth.
auto SubstPeriodSelf(
    Context& context, SemIR::LocId loc_id, SemIR::InstId inst_id,
    SemIR::ElementIndex abstract_depth,
    SemIR::InstId period_self_replacement_id,
    SubstPeriodSelfBehaviour behaviour = SubstPeriodSelfBehaviour::All,
    SubstPeriodSelfRebuildInst rebuild = nullptr) -> SemIR::InstId;

// Replace `.Self` references in the specific of the interface or named
// constraint with `period_self_replacement_id`.
//
// The `behaviour` specifies if all `.Self` are replaced or just implicit use in
// designators. The `rebuild` callback can optionally be specified to override
// how an instruction is re-constructed to form an InstId after replacement. It
// can return None to fall back to the default of evaluating the inst.
auto SubstPeriodSelf(
    Context& context, SemIR::LocId loc_id, SemIR::SpecificInterface interface,
    SemIR::ElementIndex abstract_depth,
    SemIR::ConstantId period_self_replacement_id,
    SubstPeriodSelfBehaviour behaviour = SubstPeriodSelfBehaviour::All,
    SubstPeriodSelfRebuildInst rebuild = nullptr) -> SemIR::SpecificInterface;
auto SubstPeriodSelf(
    Context& context, SemIR::LocId loc_id,
    SemIR::SpecificNamedConstraint constraint,
    SemIR::ElementIndex abstract_depth,
    SemIR::ConstantId period_self_replacement_id,
    SubstPeriodSelfBehaviour behaviour = SubstPeriodSelfBehaviour::All,
    SubstPeriodSelfRebuildInst rebuild = nullptr)
    -> SemIR::SpecificNamedConstraint;

// Replace `.Self` references with the self-type. The `facet_type_inst_id` must
// be a `FacetType` instruction (or error).
//
// The implicit `.Self` in designators is not replaced in rewrite constraints,
// to allow for rewrite constraint resolution to recognise the designators.
// Later use of rewrite constraints requires further `.Self` replacement.
//
// Unlike SubstPeriodSelf, which works with constant values and thus canonical
// instructions, this operation can be done for non-canonical facet types. A new
// instruction is added for the output FacetType if anything does get replaced,
// and the original instruction id is preserved otherwise.
auto SubstPeriodSelfInFacetType(Context& context, SemIR::LocId loc_id,
                                SemIR::TypeInstId self_type_inst_id,
                                SemIR::TypeInstId facet_type_inst_id)
    -> SemIR::TypeInstId;

auto SubstPeriodSelfRemoveDepth(Context& context, SemIR::InstId inst_id,
                                SemIR::InstId period_self_to_be_replaced)
    -> SemIR::InstId;
auto SubstPeriodSelfRemoveDepth(Context& context, SemIR::TypeInstId inst_id,
                                SemIR::InstId period_self_to_be_replaced)
    -> SemIR::TypeInstId;

// Returns whether the `inst_id` is a reference to `.Self`.
//
// If `canonicalize` is true, look at the constant value of `inst_id` and get
// the canonicalized facet or type to look through FacetAccessType.
auto IsPeriodSelf(Context& context, SemIR::InstId inst_id,
                  bool canonicalize = true) -> bool;

// If `inst_id` is a reference to `.Self`, return it.
//
// If `canonicalize` is true, look at the constant value of `inst_id` and get
// the canonicalized facet or type to look through FacetAccessType.
auto TryGetAsPeriodSelf(Context& context, SemIR::InstId inst_id,
                        bool canonicalize = true)
    -> std::optional<SemIR::SymbolicBinding>;

// Look for ambiguous `.Self` in a `T impls X where ...` statement. The given
// inst ids are the non-canonical insts for the LHS and RHS of the `impls`
// inside a `where` expression.
//
// If the LHS is not `.Self` and RHS contains a nested `where` expression, the
// value of `.Self` becomes ambiguous on the RHS of the `where` (it could mean
// either the original value or new value given by the LHS of the `impls`). Note
// that implicit `.Self` references are never ambiguous, they always refer to
// the innermost value that `.Self` could refer to.
//
// Returns true if an error was diagnosed.
auto FindAndDiagnoseAmbiguousPeriodSelf(Context& context,
                                        SemIR::InstId impls_lhs_id,
                                        SemIR::InstId impls_rhs_id) -> bool;

}  // namespace Carbon::Check

#endif  // CARBON_TOOLCHAIN_CHECK_PERIOD_SELF_H_
