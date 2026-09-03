// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#ifndef CARBON_TOOLCHAIN_SEM_IR_GENERATED_FUNCTION_H_
#define CARBON_TOOLCHAIN_SEM_IR_GENERATED_FUNCTION_H_

#include "llvm/ADT/SmallVector.h"
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
};

}  // namespace Carbon::SemIR

#endif  // CARBON_TOOLCHAIN_SEM_IR_GENERATED_FUNCTION_H_
