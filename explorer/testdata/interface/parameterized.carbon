// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// NOAUTOUPDATE

package ExplorerTest api;

interface Vector(Scalar:! type) {
  fn Zero() -> Self;
  fn Add[self: Self](b: Self) -> Self;
  fn Scale[self: Self](v: Scalar) -> Self;
}

class Point {
  var x: i32;
  var y: i32;
  extend impl as Vector(i32) {
    fn Zero() -> Point {
      return {.x = 0, .y = 0};
    }
    fn Add[self: Point](b: Point) -> Point {
      return {.x = self.x + b.x, .y = self.y + b.y};
    }
    fn Scale[self: Point](v: i32) -> Point {
      return {.x = self.x * v, .y = self.y * v};
    }
  }
}

fn AddAndScaleGeneric[T:! type, U:! Vector(T)](a: U, s: T) -> U {
  return a.Add(U.Zero()).Scale(s);
}

fn Main() -> i32 {
  var a: Point = {.x = 2, .y = 1};
  var p: Point = AddAndScaleGeneric(a, 5);
  return p.x - 10;
}

// CHECK:STDOUT: result: 0
