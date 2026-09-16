// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include "toolchain/sem_ir/singleton_insts.h"

#include "toolchain/sem_ir/ids.h"
#include "toolchain/sem_ir/inst.h"
#include "toolchain/sem_ir/inst_kind.h"
#include "toolchain/sem_ir/typed_insts.h"

namespace Carbon::SemIR {

auto IsSingletonInst(Inst inst) -> bool {
  if (inst.kind() == InstKind::FacetType) {
    return inst.As<FacetType>().declared_facet_type_id ==
           DeclaredFacetTypeId::Empty;
  }
  return IsSingletonInstKind(inst.kind());
}

}  // namespace Carbon::SemIR
