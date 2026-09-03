// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#ifndef CARBON_TOOLCHAIN_SEM_IR_FORM_H_
#define CARBON_TOOLCHAIN_SEM_IR_FORM_H_

#include "toolchain/sem_ir/ids.h"
#include "toolchain/sem_ir/typed_insts.h"

namespace Carbon::SemIR {

// Data about a form expression.
struct FormExpr {
  static const FormExpr Error;
  static const FormExpr None;

  // The inst ID of the form expression itself. This is always an inst in the
  // AnyPrimitiveForm category.
  InstId form_inst_id;
  // The inst ID of the form expression's type component.
  TypeInstId type_component_inst_id;
  // The type ID corresponding to type_component_id.
  TypeId type_component_id;
};

inline constexpr FormExpr FormExpr::Error = {
    .form_inst_id = ErrorInst::InstId,
    .type_component_inst_id = ErrorInst::TypeInstId,
    .type_component_id = ErrorInst::TypeId};

inline constexpr FormExpr FormExpr::None = {
    .form_inst_id = SemIR::InstId::None,
    .type_component_inst_id = SemIR::TypeInstId::None,
    .type_component_id = SemIR::TypeId::None};

}  // namespace Carbon::SemIR

#endif  // CARBON_TOOLCHAIN_SEM_IR_FORM_H_
