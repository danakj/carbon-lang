// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// NOAUTOUPDATE

package ExplorerTest api;

fn CompareBools(a: bool, b: bool) -> bool {
  // CHECK:STDERR: SYNTAX ERROR: fail_compare_precedence.carbon:[[@LINE+1]]: syntax error, unexpected EQUAL_EQUAL, expecting SEMICOLON
  return not a == b;
}
