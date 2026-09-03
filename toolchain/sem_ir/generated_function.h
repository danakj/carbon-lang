// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#ifndef CARBON_TOOLCHAIN_SEM_IR_GENERATED_FUNCTION_H_
#define CARBON_TOOLCHAIN_SEM_IR_GENERATED_FUNCTION_H_

#include "common/hashing.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "toolchain/base/canonical_value_store.h"
#include "toolchain/sem_ir/form.h"
#include "toolchain/sem_ir/ids.h"
#include "toolchain/sem_ir/pattern.h"

namespace Carbon::SemIR {

// Arguments for generating a function declaration.
struct GeneratedFunctionDeclArgs {
  SemIR::NameScopeId parent_scope_id;
  SemIR::NameId name_id;
  // The type of the leading `self` parameter, or `None` if there is none.
  SemIR::TypeId self_type_id = SemIR::TypeId::None;
  // The kind of the `self` parameter.
  SemIR::ParamPatternKind self_kind = SemIR::ParamPatternKind::Ref;
  // The types of the explicit parameters.
  llvm::ArrayRef<SemIR::TypeId> param_type_ids = {};
  // The kinds of the parameters described by `param_type_ids`.
  llvm::ArrayRef<SemIR::ParamPatternKind> param_kinds = {};
  // The return form, or `None` if the function doesn't declare a return form.
  SemIR::FormExpr return_form = SemIR::FormExpr::None;

  friend auto operator==(const GeneratedFunctionDeclArgs& lhs,
                         const GeneratedFunctionDeclArgs& rhs)
      -> bool = default;
};

inline auto CarbonHashValue(const GeneratedFunctionDeclArgs& value,
                            uint64_t seed) -> HashCode {
  Hasher hasher(seed);
  hasher.Hash(value.parent_scope_id);
  hasher.Hash(value.name_id);
  hasher.Hash(value.self_type_id);
  hasher.Hash(value.self_kind);
  hasher.HashArray(value.param_type_ids);
  hasher.HashArray(value.param_kinds);
  hasher.Hash(value.return_form);
  return static_cast<HashCode>(hasher);
}

// A copy of GeneratedFunctionDeclArgs but with durable storage of its values,
// and the generated FunctionId from those arguments.
struct GeneratedFunctionDeclArgsStorage {
  SemIR::NameScopeId parent_scope_id;
  SemIR::NameId name_id;
  SemIR::TypeId self_type_id;
  SemIR::ParamPatternKind self_kind;
  llvm::SmallVector<SemIR::TypeId> param_type_ids;
  llvm::SmallVector<SemIR::ParamPatternKind> param_kinds;
  SemIR::FormExpr return_form;

  SemIR::InstId decl_id;
  SemIR::FunctionId function_id;

  static auto FromArgs(const GeneratedFunctionDeclArgs& args,
                       SemIR::InstId decl_id, SemIR::FunctionId function_id)
      -> GeneratedFunctionDeclArgsStorage;

  auto GetAsKey() const -> GeneratedFunctionDeclArgs;
};

using GeneratedFunctionDeclArgsStore =
    CanonicalValueStore<GeneratedFunctionDeclArgsId, GeneratedFunctionDeclArgs,
                        Tag<CheckIRId>, GeneratedFunctionDeclArgsStorage>;

}  // namespace Carbon::SemIR

#endif  // CARBON_TOOLCHAIN_SEM_IR_GENERATED_FUNCTION_H_
