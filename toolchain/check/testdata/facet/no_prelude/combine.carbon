// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// EXTRA-ARGS: --no-dump-sem-ir
//
// AUTOUPDATE
// TIP: To test this file alone, run:
// TIP:   bazel test //toolchain/testing:file_test --test_arg=--file_tests=toolchain/check/testdata/facet/no_prelude/combine.carbon
// TIP: To dump output, run:
// TIP:   bazel run //toolchain/testing:file_test -- --dump_output --file_tests=toolchain/check/testdata/facet/no_prelude/combine.carbon

// --- core.carbon
package Core;

interface As(Dest:! type) {
  fn Convert[self: Self]() -> Dest;
}

interface ImplicitAs(Dest:! type) {
  fn Convert[self: Self]() -> Dest;
}

interface BitAnd {
  fn Op[self: Self](other: Self) -> Self;
}

impl forall [T:! type] T as BitAnd {
  fn Op[self: Self](other: Self) -> Self = "type.and";
}

// --- fail_combine_with_non_facet_type.carbon
library "[[@TEST_NAME]]";

import Core;

interface A {}
class C {}

fn F() {
  // CHECK:STDERR: fail_combine_with_non_facet_type.carbon:[[@LINE+4]]:23: error: non-facet type `C` combined with `&` operator [FacetTypeRequiredForTypeAndOperator]
  // CHECK:STDERR:   ({} as C) as (C as (A & C));
  // CHECK:STDERR:                       ^~~~~
  // CHECK:STDERR:
  ({} as C) as (C as (A & C));
  // CHECK:STDERR: fail_combine_with_non_facet_type.carbon:[[@LINE+4]]:23: error: non-facet type `C` combined with `&` operator [FacetTypeRequiredForTypeAndOperator]
  // CHECK:STDERR:   ({} as C) as (C as (C & A));
  // CHECK:STDERR:                       ^~~~~
  // CHECK:STDERR:
  ({} as C) as (C as (C & A));
  // CHECK:STDERR: fail_combine_with_non_facet_type.carbon:[[@LINE+8]]:23: error: non-facet type `C` combined with `&` operator [FacetTypeRequiredForTypeAndOperator]
  // CHECK:STDERR:   ({} as C) as (C as (C & C));
  // CHECK:STDERR:                       ^~~~~
  // CHECK:STDERR:
  // CHECK:STDERR: fail_combine_with_non_facet_type.carbon:[[@LINE+4]]:23: error: non-facet type `C` combined with `&` operator [FacetTypeRequiredForTypeAndOperator]
  // CHECK:STDERR:   ({} as C) as (C as (C & C));
  // CHECK:STDERR:                       ^~~~~
  // CHECK:STDERR:
  ({} as C) as (C as (C & C));
}

// --- same.carbon
library "[[@TEST_NAME]]";

import Core;

interface A {
  fn G();
}

class C {}
impl C as A {
  fn G() {}
}

fn F() {
  ({} as C).((A & A).G)();
  (({} as C) as (C as (A & A))).((A & A).G)();
  (({} as C) as (C as (A & A))).(A.G)();
}

// --- fail_name_collision.carbon
library "[[@TEST_NAME]]";

import Core;

interface A {
  fn G();
}
interface B {
  fn G();
}

class C {}
impl C as A {
  fn G();
}
impl C as B {
  fn G() {}
}

fn F() {
  // TODO: This error message is wrong here, we are not using `extend`.

  // CHECK:STDERR: fail_name_collision.carbon:[[@LINE+4]]:14: error: ambiguous use of name `G` found in multiple extended scopes [NameAmbiguousDueToExtend]
  // CHECK:STDERR:   ({} as C).((A & B).G)();
  // CHECK:STDERR:              ^~~~~~~~~
  // CHECK:STDERR:
  ({} as C).((A & B).G)();
}

// --- combine.carbon
library "[[@TEST_NAME]]";

import Core;

interface A {}
interface B {
  fn G();
}

class C {}
impl C as A {}
impl C as B {
  fn G() {}
}

fn F() {
  ({} as C).((A & B).G)();

  (({} as C) as (C as (A & B))).((A & B).G)();

  (({} as C) as (C as (A & B))).((B).G)();
}

// --- fail_todo_generic_param_is_combined.carbon

library "[[@TEST_NAME]]";

import Core;

interface A {
  fn G();
}
interface B {
  fn H();
}

fn G[T:! A & B](t: T) {
  // CHECK:STDERR: fail_todo_generic_param_is_combined.carbon:[[@LINE+4]]:3: error: type `T` does not support qualified expressions [QualifiedExprUnsupported]
  // CHECK:STDERR:   t.G();
  // CHECK:STDERR:   ^~~
  // CHECK:STDERR:
  t.G();
  // CHECK:STDERR: fail_todo_generic_param_is_combined.carbon:[[@LINE+4]]:3: error: type `T` does not support qualified expressions [QualifiedExprUnsupported]
  // CHECK:STDERR:   t.H();
  // CHECK:STDERR:   ^~~
  // CHECK:STDERR:
  t.H();
}

class C {}
impl C as A {
  fn G() {}
}
impl C as B {
  fn H() {}
}

fn F() {
  G({} as C);
}

// --- todo_generic_interface.carbon
library "[[@TEST_NAME]]";

import Core;

interface A(T:! type) {}
interface B {
  fn G();
}

class P1 {}
class P2 {}

class C {}
impl C as A(P1) {}
impl C as B {
  fn G() {}
}

fn F() {
  // TODO: Qualified lookup of `G` should not be needed here.
  (({} as C) as (C as (A(P1) & B))).(B.G)();
}

// --- fail_wrong_generic_interface.carbon
library "[[@TEST_NAME]]";

import Core;

interface A(T:! type) {}
interface B {
  fn G();
}

class P1 {}
class P2 {}

class C {}
impl C as A(P1) {}
impl C as B {
  fn G() {}
}

fn F() {
  // CHECK:STDERR: fail_wrong_generic_interface.carbon:[[@LINE+7]]:18: error: cannot convert from `type` to `A(P2) & B` with `as` [ExplicitAsConversionFailure]
  // CHECK:STDERR:   (({} as C) as (C as (A(P2) & B))).(B.G)();
  // CHECK:STDERR:                  ^~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_wrong_generic_interface.carbon:[[@LINE+4]]:18: note: type `type` does not implement interface `Core.As(A(P2) & B)` [MissingImplInMemberAccessNote]
  // CHECK:STDERR:   (({} as C) as (C as (A(P2) & B))).(B.G)();
  // CHECK:STDERR:                  ^~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  (({} as C) as (C as (A(P2) & B))).(B.G)();
}

// --- todo_generic_interface_parameter.carbon
library "[[@TEST_NAME]]";

import Core;

interface A {
  fn AA();
}
interface B {
  fn BB();
}

class C {}
impl C as A {
  fn AA() {}
}
impl C as B {
  fn BB() {}
}

fn G[T:! A & B](t: T) {
  // TODO: Lookup of `AA` and `BB` should be possible here, using the witnesses
  // found in type deduction.

  // CHECK:STDERR: todo_generic_interface_parameter.carbon:[[@LINE+4]]:3: error: type `T` does not support qualified expressions [QualifiedExprUnsupported]
  // CHECK:STDERR:   t.AA();
  // CHECK:STDERR:   ^~~~
  // CHECK:STDERR:
  t.AA();
  // CHECK:STDERR: todo_generic_interface_parameter.carbon:[[@LINE+4]]:3: error: type `T` does not support qualified expressions [QualifiedExprUnsupported]
  // CHECK:STDERR:   t.BB();
  // CHECK:STDERR:   ^~~~
  // CHECK:STDERR:
  t.BB();

  // TODO: Qualified lookup of `AA` and `BB` should also be possible here, using
  // the witnesses found in type deduction.

  // CHECK:STDERR: todo_generic_interface_parameter.carbon:[[@LINE+4]]:3: error: cannot access member of interface `A` in type `T` that does not implement that interface [MissingImplInMemberAccess]
  // CHECK:STDERR:   t.(A.AA)();
  // CHECK:STDERR:   ^~~~~~~~
  // CHECK:STDERR:
  t.(A.AA)();
  // CHECK:STDERR: todo_generic_interface_parameter.carbon:[[@LINE+4]]:3: error: cannot access member of interface `B` in type `T` that does not implement that interface [MissingImplInMemberAccess]
  // CHECK:STDERR:   t.(B.BB)();
  // CHECK:STDERR:   ^~~~~~~~
  // CHECK:STDERR:
  t.(B.BB)();
}

fn F() {
  G({} as C);
}


// --- todo_generic_forall_impl.carbon
library "[[@TEST_NAME]]";

import Core;

interface Iface { fn Q(); }
interface GenericIface(T:! type) { fn R(); }

class GenericClass(T:! type) {}

class C {}
impl C as Iface { fn Q() {} }

impl forall [IfaceType:! Iface] C as GenericIface(GenericClass(IfaceType)) {
  fn R() {}
}

class ImplIface {}
impl ImplIface as Iface { fn Q() {} }

fn F() {
  ({} as C) as (C as Iface);
  ({} as C) as (C as GenericIface(GenericClass(ImplIface)));

  ({} as C) as (C as (Iface & GenericIface(GenericClass(ImplIface))));

  // TODO: Qualified lookup of `Q` and `R` should not be needed here.
  (({} as C) as (C as (Iface & GenericIface(GenericClass(ImplIface))))).(Iface.Q)();
  (({} as C) as (C as (Iface & GenericIface(GenericClass(ImplIface))))).(GenericIface(GenericClass(ImplIface)).R)();
}
