// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include "toolchain/sem_ir/generated_function.h"

#include "toolchain/base/canonical_value_store_impl.h"
#include "toolchain/base/value_store_impl.h"

namespace Carbon::SemIR {

auto GeneratedFunctionDeclArgsStorage::FromArgs(
    const GeneratedFunctionDeclArgs& args, SemIR::InstId decl_id,
    SemIR::FunctionId function_id) -> GeneratedFunctionDeclArgsStorage {
  return {
      .parent_scope_id = args.parent_scope_id,
      .name_id = args.name_id,
      .self_type_id = args.self_type_id,
      .self_kind = args.self_kind,
      .param_type_ids = llvm::SmallVector<SemIR::TypeId>(args.param_type_ids),
      .param_kinds =
          llvm::SmallVector<SemIR::ParamPatternKind>(args.param_kinds),
      .return_form = args.return_form,
      .decl_id = decl_id,
      .function_id = function_id};
}

auto GeneratedFunctionDeclArgsStorage::GetAsKey() const
    -> GeneratedFunctionDeclArgs {
  return {.parent_scope_id = parent_scope_id,
          .name_id = name_id,
          .self_type_id = self_type_id,
          .self_kind = self_kind,
          .param_type_ids = param_type_ids,
          .param_kinds = param_kinds,
          .return_form = return_form};
}

}  // namespace Carbon::SemIR

namespace Carbon {
template class CanonicalValueStore<
    SemIR::GeneratedFunctionDeclArgsId, SemIR::GeneratedFunctionDeclArgs,
    Tag<SemIR::CheckIRId>, SemIR::GeneratedFunctionDeclArgsStorage>;
}
