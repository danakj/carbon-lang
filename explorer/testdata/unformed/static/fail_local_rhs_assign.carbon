// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// NOAUTOUPDATE

package ExplorerTest api;

fn Main() -> i32 {
  var x: i32;
  var y: i32;
  // CHECK:STDERR: COMPILATION ERROR: fail_local_rhs_assign.carbon:[[@LINE+1]]: use of uninitialized variable x
  y = x;
  return y;
}
