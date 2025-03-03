// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include "toolchain/check/impl_lookup.h"

#include "toolchain/check/deduce.h"
#include "toolchain/check/diagnostic_helpers.h"
#include "toolchain/check/generic.h"
#include "toolchain/check/import_ref.h"
#include "toolchain/check/type_completion.h"
#include "toolchain/sem_ir/ids.h"
#include "toolchain/sem_ir/impl.h"
#include "toolchain/sem_ir/inst.h"
#include "toolchain/sem_ir/typed_insts.h"

namespace Carbon::Check {

static auto FindAssociatedImportIRs(Context& context,
                                    SemIR::ConstantId type_const_id,
                                    SemIR::ConstantId interface_const_id)
    -> llvm::SmallVector<SemIR::ImportIRId> {
  llvm::SmallVector<SemIR::ImportIRId> result;

  // Add an entity to our result.
  auto add_entity = [&](const SemIR::EntityWithParamsBase& entity) {
    // We will look for impls in the import IR associated with the first owning
    // declaration.
    auto decl_id = entity.first_owning_decl_id;
    if (!decl_id.has_value()) {
      return;
    }
    if (auto ir_id = GetCanonicalImportIRInst(context, decl_id).ir_id;
        ir_id.has_value()) {
      result.push_back(ir_id);
    }
  };

  llvm::SmallVector<SemIR::InstId> worklist;
  worklist.push_back(context.constant_values().GetInstId(type_const_id));
  worklist.push_back(context.constant_values().GetInstId(interface_const_id));

  // Push the contents of an instruction block onto our worklist.
  auto push_block = [&](SemIR::InstBlockId block_id) {
    if (block_id.has_value()) {
      llvm::append_range(worklist, context.inst_blocks().Get(block_id));
    }
  };

  // Add the arguments of a specific to the worklist.
  auto push_args = [&](SemIR::SpecificId specific_id) {
    if (specific_id.has_value()) {
      push_block(context.specifics().Get(specific_id).args_id);
    }
  };

  while (!worklist.empty()) {
    auto inst_id = worklist.pop_back_val();

    // Visit the operands of the constant.
    auto inst = context.insts().Get(inst_id);
    auto [arg0_kind, arg1_kind] = inst.ArgKinds();
    for (auto [arg, kind] :
         {std::pair{inst.arg0(), arg0_kind}, {inst.arg1(), arg1_kind}}) {
      switch (kind) {
        case SemIR::IdKind::For<SemIR::InstId>: {
          if (auto id = SemIR::InstId(arg); id.has_value()) {
            worklist.push_back(id);
          }
          break;
        }
        case SemIR::IdKind::For<SemIR::InstBlockId>: {
          push_block(SemIR::InstBlockId(arg));
          break;
        }
        case SemIR::IdKind::For<SemIR::ClassId>: {
          add_entity(context.classes().Get(SemIR::ClassId(arg)));
          break;
        }
        case SemIR::IdKind::For<SemIR::InterfaceId>: {
          add_entity(context.interfaces().Get(SemIR::InterfaceId(arg)));
          break;
        }
        case SemIR::IdKind::For<SemIR::FacetTypeId>: {
          const auto& facet_type_info =
              context.facet_types().Get(SemIR::FacetTypeId(arg));
          for (const auto& impl : facet_type_info.impls_constraints) {
            add_entity(context.interfaces().Get(impl.interface_id));
            push_args(impl.specific_id);
          }
          break;
        }
        case SemIR::IdKind::For<SemIR::FunctionId>: {
          add_entity(context.functions().Get(SemIR::FunctionId(arg)));
          break;
        }
        case SemIR::IdKind::For<SemIR::SpecificId>: {
          push_args(SemIR::SpecificId(arg));
          break;
        }
        default: {
          break;
        }
      }
    }
  }

  // Deduplicate.
  llvm::sort(result, [](SemIR::ImportIRId a, SemIR::ImportIRId b) {
    return a.index < b.index;
  });
  result.erase(llvm::unique(result), result.end());

  return result;
}

// Returns true if a cycle was found and diagnosed.
static auto FindAndDiagnoseImplLookupCycle(
    Context& context,
    const llvm::SmallVector<Context::ImplLookupStackEntry>& stack,
    SemIR::LocId loc_id, SemIR::ConstantId type_const_id,
    SemIR::ConstantId interface_const_id) -> bool {
  // Deduction of the interface parameters can do further impl lookups, and we
  // need to ensure we terminate.
  //
  // https://docs.carbon-lang.dev/docs/design/generics/details.html#acyclic-rule
  // - We look for violations of the acyclic rule by seeing if a previous lookup
  //   had all the same type inputs.
  // - The `interface_const_id` encodes the entire facet type being looked up,
  //   including any specific parameters for a generic interface.
  //
  // TODO: Implement the termination rule, which requires looking at the
  // complexity of the types on the top of (or throughout?) the stack:
  // https://docs.carbon-lang.dev/docs/design/generics/details.html#termination-rule
  for (auto [i, entry] : llvm::enumerate(stack)) {
    if (entry.type_const_id == type_const_id &&
        entry.interface_const_id == interface_const_id) {
      auto facet_type_type_id =
          context.types().GetTypeIdForTypeConstantId(interface_const_id);
      CARBON_DIAGNOSTIC(ImplLookupCycle, Error,
                        "cycle found in search for impl of {0} for type {1}",
                        SemIR::TypeId, SemIR::TypeId);
      auto builder = context.emitter().Build(
          loc_id, ImplLookupCycle, facet_type_type_id,
          context.types().GetTypeIdForTypeConstantId(type_const_id));
      for (const auto& active_entry : llvm::drop_begin(stack, i)) {
        if (active_entry.impl_loc.has_value()) {
          CARBON_DIAGNOSTIC(ImplLookupCycleNote, Note,
                            "determining if this impl clause matches", );
          builder.Note(active_entry.impl_loc, ImplLookupCycleNote);
        }
      }
      builder.Emit();
      return true;
    }
  }
  return false;
}

// Gets the set of `SpecificInterface`s that are required by a facet type
// (as a constant value).
static auto GetInterfacesFromConstantId(Context& context, SemIR::LocId loc_id,
                                        SemIR::ConstantId interface_const_id)
    -> llvm::SmallVector<
        std::pair<SemIR::CompleteFacetType::RequiredInterface, bool>, 16> {
  // The `interface_const_id` is a constant value for some facet type. We do
  // this long chain of steps to go from that constant value to the
  // `FacetTypeId` found on the `FacetType` instruction of this constant value,
  // and finally to the `CompleteFacetType`.
  auto facet_type_inst_id =
      context.constant_values().GetInstId(interface_const_id);
  auto facet_type_inst =
      context.insts().GetAs<SemIR::FacetType>(facet_type_inst_id);
  auto facet_type_id = facet_type_inst.facet_type_id;
  auto complete_facet_type_id =
      context.complete_facet_types().TryGetId(facet_type_id);
  // The facet type will already be completed before coming here. If we're
  // converting from a concrete type to a facet type, the conversion step
  // requires everything to be complete before doing impl lookup.
  CARBON_CHECK(complete_facet_type_id.has_value());
  const auto& complete_facet_type =
      context.complete_facet_types().Get(complete_facet_type_id);

  llvm::SmallVector<
      std::pair<SemIR::CompleteFacetType::RequiredInterface, bool>, 16>
      interface_ids;

  if (complete_facet_type.required_interfaces.empty()) {
    // This should never happen - a FacetType either requires or is bounded by
    // some `.Self impls` clause. Otherwise you would just have `type` (aka
    // `TypeType` in the toolchain implementation) which is not a facet type.
    context.TODO(loc_id,
                 "impl lookup for a FacetType with no interface (using "
                 "`where .Self impls ...` instead?)");
    return interface_ids;
  }
  for (auto required : complete_facet_type.required_interfaces) {
    interface_ids.push_back(
        {required,
         context.facet_types().Get(facet_type_id).other_requirements});
  }
  return interface_ids;
}

static auto GetWitnessIdForImpl(
    Context& context, SemIR::LocId loc_id, SemIR::ConstantId type_const_id,
    SemIR::ConstantId interface_const_id,
    const SemIR::CompleteFacetType::RequiredInterface& interface,
    bool interface_has_other_requirements, const SemIR::Impl& impl)
    -> SemIR::InstId {
  // If the impl's interface_id differs from the query, then this impl can not
  // possibly provide the queried interface, and we don't need to proceed.
  if (impl.interface.interface_id != interface.interface_id) {
    return SemIR::InstId::None;
  }

  // When the impl's interface_id matches, but the interface is generic, the
  // impl may or may not match based on restrictions in the generic parameters
  // of the impl.
  //
  // As a shortcut, if the impl's constraint is not symbolic (does not depend on
  // any generic parameters), then we can determine that we match if the specific
  // ids match exactly.
  auto impl_interface_const_id =
      context.constant_values().Get(impl.constraint_id);
  if (!impl_interface_const_id.is_symbolic()) {
    if (impl.interface.specific_id != interface.specific_id) {
      return SemIR::InstId::None;
    }
  }

  // This check comes first to avoid deduction with an invalid impl. We use an
  // error value to indicate an error during creation of the impl, such as a
  // recursive impl which will cause deduction to recurse infinitely.
  if (impl.witness_id == SemIR::ErrorInst::SingletonInstId) {
    return SemIR::InstId::None;
  }
  if (!impl.witness_id.has_value()) {
    // TODO: Diagnose if the impl isn't defined yet?
    return SemIR::InstId::None;
  }

  // The impl may have generic arguments, in which case we need to deduce them
  // to find what they are given the specific interface query. We use that
  // specific to map values in the impl to the deduced values.
  auto specific_id = SemIR::SpecificId::None;
  if (impl.generic_id.has_value()) {
    specific_id = DeduceImplArguments(context, loc_id, impl, type_const_id,
                                      interface.specific_id);
    if (!specific_id.has_value()) {
      return SemIR::InstId::None;
    }
  }

  // The self type of the impl must match the type in the query, or this is an
  // `impl T as ...` for some other type `T` and should not be considered.
  auto deduced_self_const_id = SemIR::GetConstantValueInSpecific(
      context.sem_ir(), specific_id, impl.self_id);
  if (type_const_id != deduced_self_const_id) {
    return SemIR::InstId::None;
  }

  // The impl's constraint is a facet type which it is implementing for the self
  // type: the `I` in `impl ... as I`. The deduction step may be unable to be
  // fully applied to the types in the constraint and result in an error here,
  // in which case it does not match the query.
  auto deduced_constraint_id =
      context.constant_values().GetInstId(SemIR::GetConstantValueInSpecific(
          context.sem_ir(), specific_id, impl.constraint_id));
  if (deduced_constraint_id == SemIR::ErrorInst::SingletonInstId) {
    return SemIR::InstId::None;
  }

  auto deduced_constaint_facet_type_id =
      context.insts()
          .GetAs<SemIR::FacetType>(deduced_constraint_id)
          .facet_type_id;
  bool constraint_has_other_requirements =
      context.facet_types()
          .Get(deduced_constaint_facet_type_id)
          .other_requirements;

  // If there are requirements on the impl's constraint facet type, or on the
  // query facet type, that are not modelled yet in the FacetTypeInfo and
  // CompleteFacetType, then we can't tell if we have a match for this specific
  // query interface.
  //
  // In this case we just do the wrong thing if the either the constraint or
  // query facet type had more than one interface in it, and compare the
  // constant value of the entire query facet type against the entire impl's
  // constraint facet type. The latter will include those other requirements
  // (correctly), but the former may include more things unrelated to this one
  // interface being looked for here and thus fail incorrectly.
  //
  // TODO: Stop using `other_requirements` and look at `where .Self impls`
  // clauses with further impl lookups as needed. These should become part of
  // the set of interfaces for which this function is called on, and this
  // function shouldn't have to think about them.
  if (constraint_has_other_requirements || interface_has_other_requirements) {
    if (context.constant_values().Get(deduced_constraint_id) !=
        interface_const_id) {
      return SemIR::InstId::None;
    }
  }

  LoadImportRef(context, impl.witness_id);
  if (specific_id.has_value()) {
    // We need a definition of the specific `impl` so we can access its
    // witness.
    ResolveSpecificDefinition(context, loc_id, specific_id);
  }
  return context.constant_values().GetInstId(SemIR::GetConstantValueInSpecific(
      context.sem_ir(), specific_id, impl.witness_id));
}

auto LookupImplWitness(Context& context, SemIR::LocId loc_id,
                       SemIR::ConstantId type_const_id,
                       SemIR::ConstantId interface_const_id) -> SemIR::InstId {
  if (type_const_id == SemIR::ErrorInst::SingletonConstantId ||
      interface_const_id == SemIR::ErrorInst::SingletonConstantId) {
    return SemIR::ErrorInst::SingletonInstId;
  }
  auto import_irs =
      FindAssociatedImportIRs(context, type_const_id, interface_const_id);
  for (auto import_ir : import_irs) {
    // TODO: Instead of importing all impls, only import ones that are in some
    // way connected to this query.
    for (auto impl_index : llvm::seq(
             context.import_irs().Get(import_ir).sem_ir->impls().size())) {
      // TODO: Track the relevant impls and only consider those ones and any
      // local impls, rather than looping over all impls below.
      ImportImpl(context, import_ir, SemIR::ImplId(impl_index));
    }
  }

  if (FindAndDiagnoseImplLookupCycle(context, context.impl_lookup_stack(),
                                     loc_id, type_const_id,
                                     interface_const_id)) {
    return SemIR::ErrorInst::SingletonInstId;
  }

  auto interfaces =
      GetInterfacesFromConstantId(context, loc_id, interface_const_id);
  if (interfaces.empty()) {
    // TODO: Remove this when the context.TODO() is removed in
    // GetInterfaceIdsFromConstantId.
    return SemIR::InstId::None;
  }

  llvm::SmallVector<SemIR::InstId> result_witness_ids;

  auto& stack = context.impl_lookup_stack();
  stack.push_back({
      .type_const_id = type_const_id,
      .interface_const_id = interface_const_id,
  });
  // We need to find a witness for each interface in `interfaces`. We return
  // them in the same order as they are found in the `CompleteFacetType`, which
  // is the same order as in `interfaces` here.
  for (const auto& [interface, interface_has_other_requirements] : interfaces) {
    bool found_witness = false;
    for (const auto& impl : context.impls().array_ref()) {
      stack.back().impl_loc = impl.definition_id;
      auto result_witness_id = GetWitnessIdForImpl(
          context, loc_id, type_const_id, interface_const_id, interface,
          interface_has_other_requirements, impl);
      if (result_witness_id.has_value()) {
        result_witness_ids.push_back(result_witness_id);
        // We found a matching impl; don't keep looking for this `interface_id`,
        // move onto the next.
        found_witness = true;
        break;
      }
    }
    if (!found_witness) {
      // At least one queried interface in the facet type has no witness for the
      // given type, we can stop looking for more.
      break;
    }
  }
  stack.pop_back();

  // All interfaces in the query facet type must have been found to be available
  // through some impl (TODO: or directly on the type itself if `type_const_id`
  // is a facet type).
  if (result_witness_ids.size() != interfaces.size()) {
    return SemIR::InstId::None;
  }

  // TODO: Return the whole set as a (newly introduced) FacetTypeWitness
  // instruction. For now we just return a single witness instruction which
  // doesn't matter because it essentially goes unused anyway. So far this
  // method is just used as a boolean test in cases where there can be more than
  // one interface in the query facet type:
  // - Concrete facet values (`({} as C) as (C as (A & B))`) are looked through
  //   to the implementing type (typically a ClassType) to access members, and
  //   thus don't use the witnesses in the facet value.
  // - Compound member lookup (`G.(A & B).F()`) uses name lookup to find the
  //   interface first, then does impl lookup for a witness with a single
  //   interface query. It's also only possible on concrete facet values so far
  //   (see below).
  // - Qualified name lookup on symbolic facet values (`T:! A & B`) doesn't work
  //   at all, so never gets to looking for a witness.
  return result_witness_ids[0];
}

}  // namespace Carbon::Check
