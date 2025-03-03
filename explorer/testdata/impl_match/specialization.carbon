// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// NOAUTOUPDATE

package ExplorerTest api;

interface Vector(T:! type) {
  fn Add[self: Self](b: Self) -> Self;
  fn Scale[self: Self](v: T) -> Self;
}

class Point(T:! type) {
  var x: T;
  var y: T;
}

impl Point(i32) as Vector(i32) {
  fn Add[self: Self](b: Self) -> Self {
    return {.x = self.x + b.x, .y = self.y + b.y};
  }
  fn Scale[self: Self](v: i32) -> Self {
    return {.x = self.x * v, .y = self.y * v};
  }
}

impl forall [T:! type] Point(T) as Vector(T) {
  fn Add[self: Self](b: Self) -> Self {
    return self;
  }
  fn Scale[self: Self](v: T) -> Self {
    return self;
  }
}

fn AddAndScaleGeneric[T:! Vector(i32)](a: T, b: T, s: i32) -> T {
  return a.Add(b).Scale(s);
}

fn Main() -> i32 {
  var a: Point(i32) = {.x = 1, .y = 1};
  var b: Point(i32) = {.x = 2, .y = 3};
  // TODO: This shouldn't be considered ambiguous.
  var p: Point(i32) = AddAndScaleGeneric(a, b, 5);
  return p.x - 15;
}

// CHECK:STDOUT: result: 0
