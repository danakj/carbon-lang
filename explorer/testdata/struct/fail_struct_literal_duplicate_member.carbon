// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// NOAUTOUPDATE

package ExplorerTest api;

fn Main() -> i32 {
  // CHECK:STDERR: COMPILATION ERROR: fail_struct_literal_duplicate_member.carbon:[[@LINE+1]]: Duplicate name `x` in struct literal
  var x: auto = {.x = 0, .x = 0};
  return 0;
}
