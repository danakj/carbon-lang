// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// NOAUTOUPDATE

package ExplorerTest api;

fn Main() -> i32 {
  // CHECK:STDERR: COMPILATION ERROR: fail_intrinsic_convert_no_args.carbon:[[@LINE+1]]: __intrinsic_implicit_as_convert takes 2 arguments
  __intrinsic_implicit_as_convert();
  return 0;
}
