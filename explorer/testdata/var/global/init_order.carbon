// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// NOAUTOUPDATE

package ExplorerTest api;

// Test a global variable depending on another global.

var x: i32 = 0;

var y: i32 = x;

fn Main() -> i32 {
  return y;
}

// CHECK:STDOUT: result: 0
