// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// AUTOUPDATE
// TIP: To test this file alone, run:
// TIP:   bazel test //toolchain/testing:file_test --test_arg=--file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/fail_todo_convert_facet_value_to_specialization.carbon
// TIP: To dump output, run:
// TIP:   bazel run //toolchain/testing:file_test -- --dump_output --file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/fail_todo_convert_facet_value_to_specialization.carbon

// --- core.carbon

package Core;

interface ImplicitAs(T:! type) {
  fn Convert[self: Self]() -> T;
}

// --- fail_todo_convert_facet_to_specialization.carbon

library "[[@TEST_NAME]]";

import Core;

interface Eats {
  fn Nom[self: Self]();
}
interface Goat {}

impl forall [G:! Goat] G as Eats {
  fn Nom[self: Self]() {}
}

fn FeedGoat[T:! Eats](e: T) {
  // TODO: `e` should be the specialization of `Ginger as Eats` in the `Ginger`
  // specialization of `FeedGoat`. To help make that obvious, we could look for
  // an associated type on the Eats interface once those are working.

  // CHECK:STDERR: fail_todo_convert_facet_to_specialization.carbon:[[@LINE+14]]:3: error: cannot implicitly convert from `type` to `Goat` [ImplicitAsConversionFailure]
  // CHECK:STDERR:   e.(Eats.Nom)();
  // CHECK:STDERR:   ^~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_convert_facet_to_specialization.carbon:[[@LINE+11]]:3: note: type `type` does not implement interface `Core.ImplicitAs(Goat)` [MissingImplInMemberAccessNote]
  // CHECK:STDERR:   e.(Eats.Nom)();
  // CHECK:STDERR:   ^~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_convert_facet_to_specialization.carbon:[[@LINE-15]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: impl forall [G:! Goat] G as Eats {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  // CHECK:STDERR: fail_todo_convert_facet_to_specialization.carbon:[[@LINE+4]]:3: error: cannot access member of interface `Eats` in type `T` that does not implement that interface [MissingImplInMemberAccess]
  // CHECK:STDERR:   e.(Eats.Nom)();
  // CHECK:STDERR:   ^~~~~~~~~~~~
  // CHECK:STDERR:
  e.(Eats.Nom)();
}

fn HandleHoat[T:! Goat](g: T) {
  FeedGoat(g);
}

class Ginger {}
impl Ginger as Goat {}

impl Ginger as Eats {
  fn Nom[self: Self]() {}
}

fn F() {
  FeedGoat({} as Ginger);
}

// CHECK:STDOUT: --- core.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %T: type = bind_symbolic_name T, 0 [symbolic]
// CHECK:STDOUT:   %T.patt: type = symbolic_binding_pattern T, 0 [symbolic]
// CHECK:STDOUT:   %ImplicitAs.type.96f: type = generic_interface_type @ImplicitAs [template]
// CHECK:STDOUT:   %ImplicitAs.generic: %ImplicitAs.type.96f = struct_value () [template]
// CHECK:STDOUT:   %ImplicitAs.type.07f: type = facet_type <@ImplicitAs, @ImplicitAs(%T)> [symbolic]
// CHECK:STDOUT:   %Self: %ImplicitAs.type.07f = bind_symbolic_name Self, 1 [symbolic]
// CHECK:STDOUT:   %Self.as_type: type = facet_access_type %Self [symbolic]
// CHECK:STDOUT:   %Convert.type: type = fn_type @Convert, @ImplicitAs(%T) [symbolic]
// CHECK:STDOUT:   %Convert: %Convert.type = struct_value () [symbolic]
// CHECK:STDOUT:   %ImplicitAs.assoc_type: type = assoc_entity_type %ImplicitAs.type.07f [symbolic]
// CHECK:STDOUT:   %assoc0: %ImplicitAs.assoc_type = assoc_entity element0, @ImplicitAs.%Convert.decl [symbolic]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: file {
// CHECK:STDOUT:   package: <namespace> = namespace [template] {
// CHECK:STDOUT:     .ImplicitAs = %ImplicitAs.decl
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %ImplicitAs.decl: %ImplicitAs.type.96f = interface_decl @ImplicitAs [template = constants.%ImplicitAs.generic] {
// CHECK:STDOUT:     %T.patt.loc4_22.1: type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc4_22.2 (constants.%T.patt)]
// CHECK:STDOUT:     %T.param_patt: type = value_param_pattern %T.patt.loc4_22.1, runtime_param<none> [symbolic = %T.patt.loc4_22.2 (constants.%T.patt)]
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %T.param: type = value_param runtime_param<none>
// CHECK:STDOUT:     %T.loc4_22.1: type = bind_symbolic_name T, 0, %T.param [symbolic = %T.loc4_22.2 (constants.%T)]
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic interface @ImplicitAs(%T.loc4_22.1: type) {
// CHECK:STDOUT:   %T.loc4_22.2: type = bind_symbolic_name T, 0 [symbolic = %T.loc4_22.2 (constants.%T)]
// CHECK:STDOUT:   %T.patt.loc4_22.2: type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc4_22.2 (constants.%T.patt)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %ImplicitAs.type: type = facet_type <@ImplicitAs, @ImplicitAs(%T.loc4_22.2)> [symbolic = %ImplicitAs.type (constants.%ImplicitAs.type.07f)]
// CHECK:STDOUT:   %Self.2: %ImplicitAs.type.07f = bind_symbolic_name Self, 1 [symbolic = %Self.2 (constants.%Self)]
// CHECK:STDOUT:   %Convert.type: type = fn_type @Convert, @ImplicitAs(%T.loc4_22.2) [symbolic = %Convert.type (constants.%Convert.type)]
// CHECK:STDOUT:   %Convert: @ImplicitAs.%Convert.type (%Convert.type) = struct_value () [symbolic = %Convert (constants.%Convert)]
// CHECK:STDOUT:   %ImplicitAs.assoc_type: type = assoc_entity_type @ImplicitAs.%ImplicitAs.type (%ImplicitAs.type.07f) [symbolic = %ImplicitAs.assoc_type (constants.%ImplicitAs.assoc_type)]
// CHECK:STDOUT:   %assoc0.loc5_32.2: @ImplicitAs.%ImplicitAs.assoc_type (%ImplicitAs.assoc_type) = assoc_entity element0, %Convert.decl [symbolic = %assoc0.loc5_32.2 (constants.%assoc0)]
// CHECK:STDOUT:
// CHECK:STDOUT:   interface {
// CHECK:STDOUT:     %Self.1: @ImplicitAs.%ImplicitAs.type (%ImplicitAs.type.07f) = bind_symbolic_name Self, 1 [symbolic = %Self.2 (constants.%Self)]
// CHECK:STDOUT:     %Convert.decl: @ImplicitAs.%Convert.type (%Convert.type) = fn_decl @Convert [symbolic = @ImplicitAs.%Convert (constants.%Convert)] {
// CHECK:STDOUT:       %self.patt: @Convert.%Self.as_type.loc5_20.1 (%Self.as_type) = binding_pattern self
// CHECK:STDOUT:       %self.param_patt: @Convert.%Self.as_type.loc5_20.1 (%Self.as_type) = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:       %return.patt: @Convert.%T (%T) = return_slot_pattern
// CHECK:STDOUT:       %return.param_patt: @Convert.%T (%T) = out_param_pattern %return.patt, runtime_param1
// CHECK:STDOUT:     } {
// CHECK:STDOUT:       %T.ref: type = name_ref T, @ImplicitAs.%T.loc4_22.1 [symbolic = %T (constants.%T)]
// CHECK:STDOUT:       %self.param: @Convert.%Self.as_type.loc5_20.1 (%Self.as_type) = value_param runtime_param0
// CHECK:STDOUT:       %.loc5_20.1: type = splice_block %.loc5_20.3 [symbolic = %Self.as_type.loc5_20.1 (constants.%Self.as_type)] {
// CHECK:STDOUT:         %.loc5_20.2: @Convert.%ImplicitAs.type (%ImplicitAs.type.07f) = specific_constant @ImplicitAs.%Self.1, @ImplicitAs(constants.%T) [symbolic = %Self (constants.%Self)]
// CHECK:STDOUT:         %Self.ref: @Convert.%ImplicitAs.type (%ImplicitAs.type.07f) = name_ref Self, %.loc5_20.2 [symbolic = %Self (constants.%Self)]
// CHECK:STDOUT:         %Self.as_type.loc5_20.2: type = facet_access_type %Self.ref [symbolic = %Self.as_type.loc5_20.1 (constants.%Self.as_type)]
// CHECK:STDOUT:         %.loc5_20.3: type = converted %Self.ref, %Self.as_type.loc5_20.2 [symbolic = %Self.as_type.loc5_20.1 (constants.%Self.as_type)]
// CHECK:STDOUT:       }
// CHECK:STDOUT:       %self: @Convert.%Self.as_type.loc5_20.1 (%Self.as_type) = bind_name self, %self.param
// CHECK:STDOUT:       %return.param: ref @Convert.%T (%T) = out_param runtime_param1
// CHECK:STDOUT:       %return: ref @Convert.%T (%T) = return_slot %return.param
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %assoc0.loc5_32.1: @ImplicitAs.%ImplicitAs.assoc_type (%ImplicitAs.assoc_type) = assoc_entity element0, %Convert.decl [symbolic = %assoc0.loc5_32.2 (constants.%assoc0)]
// CHECK:STDOUT:
// CHECK:STDOUT:   !members:
// CHECK:STDOUT:     .Self = %Self.1
// CHECK:STDOUT:     .Convert = %assoc0.loc5_32.1
// CHECK:STDOUT:     witness = (%Convert.decl)
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Convert(@ImplicitAs.%T.loc4_22.1: type, @ImplicitAs.%Self.1: @ImplicitAs.%ImplicitAs.type (%ImplicitAs.type.07f)) {
// CHECK:STDOUT:   %T: type = bind_symbolic_name T, 0 [symbolic = %T (constants.%T)]
// CHECK:STDOUT:   %ImplicitAs.type: type = facet_type <@ImplicitAs, @ImplicitAs(%T)> [symbolic = %ImplicitAs.type (constants.%ImplicitAs.type.07f)]
// CHECK:STDOUT:   %Self: %ImplicitAs.type.07f = bind_symbolic_name Self, 1 [symbolic = %Self (constants.%Self)]
// CHECK:STDOUT:   %Self.as_type.loc5_20.1: type = facet_access_type %Self [symbolic = %Self.as_type.loc5_20.1 (constants.%Self.as_type)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%self.param_patt: @Convert.%Self.as_type.loc5_20.1 (%Self.as_type)]() -> @Convert.%T (%T);
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @ImplicitAs(constants.%T) {
// CHECK:STDOUT:   %T.loc4_22.2 => constants.%T
// CHECK:STDOUT:   %T.patt.loc4_22.2 => constants.%T
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Convert(constants.%T, constants.%Self) {
// CHECK:STDOUT:   %T => constants.%T
// CHECK:STDOUT:   %ImplicitAs.type => constants.%ImplicitAs.type.07f
// CHECK:STDOUT:   %Self => constants.%Self
// CHECK:STDOUT:   %Self.as_type.loc5_20.1 => constants.%Self.as_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @ImplicitAs(@Convert.%T) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @ImplicitAs(%T.loc4_22.2) {}
// CHECK:STDOUT:
// CHECK:STDOUT: --- fail_todo_convert_facet_to_specialization.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Eats.type: type = facet_type <@Eats> [template]
// CHECK:STDOUT:   %Self.1b5: %Eats.type = bind_symbolic_name Self, 0 [symbolic]
// CHECK:STDOUT:   %Self.as_type.27d: type = facet_access_type %Self.1b5 [symbolic]
// CHECK:STDOUT:   %Nom.type.a33: type = fn_type @Nom.1 [template]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [template]
// CHECK:STDOUT:   %Nom.f11: %Nom.type.a33 = struct_value () [template]
// CHECK:STDOUT:   %Eats.assoc_type: type = assoc_entity_type %Eats.type [template]
// CHECK:STDOUT:   %assoc0.457: %Eats.assoc_type = assoc_entity element0, @Eats.%Nom.decl [template]
// CHECK:STDOUT:   %Goat.type: type = facet_type <@Goat> [template]
// CHECK:STDOUT:   %Self.092: %Goat.type = bind_symbolic_name Self, 0 [symbolic]
// CHECK:STDOUT:   %G: %Goat.type = bind_symbolic_name G, 0 [symbolic]
// CHECK:STDOUT:   %G.patt: %Goat.type = symbolic_binding_pattern G, 0 [symbolic]
// CHECK:STDOUT:   %G.as_type: type = facet_access_type %G [symbolic]
// CHECK:STDOUT:   %impl_witness.b2f71e.1: <witness> = impl_witness (@impl.1.%Nom.decl), @impl.1(%G) [symbolic]
// CHECK:STDOUT:   %Nom.type.c957c6.1: type = fn_type @Nom.2, @impl.1(%G) [symbolic]
// CHECK:STDOUT:   %Nom.5b3b79.1: %Nom.type.c957c6.1 = struct_value () [symbolic]
// CHECK:STDOUT:   %Eats.facet.54805c.1: %Eats.type = facet_value %G.as_type, %impl_witness.b2f71e.1 [symbolic]
// CHECK:STDOUT:   %require_complete.e217cd.1: <witness> = require_complete_type %G.as_type [symbolic]
// CHECK:STDOUT:   %T.1b5: %Eats.type = bind_symbolic_name T, 0 [symbolic]
// CHECK:STDOUT:   %T.patt.6be: %Eats.type = symbolic_binding_pattern T, 0 [symbolic]
// CHECK:STDOUT:   %T.as_type.27d: type = facet_access_type %T.1b5 [symbolic]
// CHECK:STDOUT:   %FeedGoat.type: type = fn_type @FeedGoat [template]
// CHECK:STDOUT:   %FeedGoat: %FeedGoat.type = struct_value () [template]
// CHECK:STDOUT:   %require_complete.c75: <witness> = require_complete_type %T.as_type.27d [symbolic]
// CHECK:STDOUT:   %T.8b3: type = bind_symbolic_name T, 0 [symbolic]
// CHECK:STDOUT:   %ImplicitAs.type.d62: type = facet_type <@ImplicitAs, @ImplicitAs(%T.8b3)> [symbolic]
// CHECK:STDOUT:   %Self.519: %ImplicitAs.type.d62 = bind_symbolic_name Self, 1 [symbolic]
// CHECK:STDOUT:   %T.patt.e01: type = symbolic_binding_pattern T, 0 [symbolic]
// CHECK:STDOUT:   %Convert.type.275: type = fn_type @Convert, @ImplicitAs(%T.8b3) [symbolic]
// CHECK:STDOUT:   %Convert.42e: %Convert.type.275 = struct_value () [symbolic]
// CHECK:STDOUT:   %Self.as_type.40a: type = facet_access_type %Self.519 [symbolic]
// CHECK:STDOUT:   %ImplicitAs.assoc_type.837: type = assoc_entity_type %ImplicitAs.type.d62 [symbolic]
// CHECK:STDOUT:   %assoc0.43db8b.1: %ImplicitAs.assoc_type.837 = assoc_entity element0, imports.%Core.import_ref.207961.1 [symbolic]
// CHECK:STDOUT:   %ImplicitAs.type.64f: type = facet_type <@ImplicitAs, @ImplicitAs(%Goat.type)> [template]
// CHECK:STDOUT:   %Convert.type.f88: type = fn_type @Convert, @ImplicitAs(%Goat.type) [template]
// CHECK:STDOUT:   %Convert.137: %Convert.type.f88 = struct_value () [template]
// CHECK:STDOUT:   %ImplicitAs.assoc_type.769: type = assoc_entity_type %ImplicitAs.type.64f [template]
// CHECK:STDOUT:   %assoc0.579: %ImplicitAs.assoc_type.769 = assoc_entity element0, imports.%Core.import_ref.207961.1 [template]
// CHECK:STDOUT:   %assoc0.43db8b.2: %ImplicitAs.assoc_type.837 = assoc_entity element0, imports.%Core.import_ref.207961.2 [symbolic]
// CHECK:STDOUT:   %T.092: %Goat.type = bind_symbolic_name T, 0 [symbolic]
// CHECK:STDOUT:   %T.patt.615: %Goat.type = symbolic_binding_pattern T, 0 [symbolic]
// CHECK:STDOUT:   %T.as_type.c35: type = facet_access_type %T.092 [symbolic]
// CHECK:STDOUT:   %HandleHoat.type: type = fn_type @HandleHoat [template]
// CHECK:STDOUT:   %HandleHoat: %HandleHoat.type = struct_value () [template]
// CHECK:STDOUT:   %require_complete.e217cd.2: <witness> = require_complete_type %T.as_type.c35 [symbolic]
// CHECK:STDOUT:   %impl_witness.b2f71e.2: <witness> = impl_witness (@impl.1.%Nom.decl), @impl.1(%T.092) [symbolic]
// CHECK:STDOUT:   %Nom.type.c957c6.2: type = fn_type @Nom.2, @impl.1(%T.092) [symbolic]
// CHECK:STDOUT:   %Nom.5b3b79.2: %Nom.type.c957c6.2 = struct_value () [symbolic]
// CHECK:STDOUT:   %Eats.facet.54805c.2: %Eats.type = facet_value %T.as_type.c35, %impl_witness.b2f71e.2 [symbolic]
// CHECK:STDOUT:   %FeedGoat.specific_fn.48f: <specific function> = specific_function %FeedGoat, @FeedGoat(%Eats.facet.54805c.2) [symbolic]
// CHECK:STDOUT:   %Ginger: type = class_type @Ginger [template]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [template]
// CHECK:STDOUT:   %complete_type: <witness> = complete_type_witness %empty_struct_type [template]
// CHECK:STDOUT:   %impl_witness.1bc: <witness> = impl_witness () [template]
// CHECK:STDOUT:   %impl_witness.e95: <witness> = impl_witness (@impl.3.%Nom.decl) [template]
// CHECK:STDOUT:   %Nom.type.b13: type = fn_type @Nom.3 [template]
// CHECK:STDOUT:   %Nom.826: %Nom.type.b13 = struct_value () [template]
// CHECK:STDOUT:   %Eats.facet.930: %Eats.type = facet_value %Ginger, %impl_witness.e95 [template]
// CHECK:STDOUT:   %F.type: type = fn_type @F [template]
// CHECK:STDOUT:   %F: %F.type = struct_value () [template]
// CHECK:STDOUT:   %Ginger.val: %Ginger = struct_value () [template]
// CHECK:STDOUT:   %Goat.facet: %Goat.type = facet_value %Ginger, %impl_witness.1bc [template]
// CHECK:STDOUT:   %impl_witness.71e: <witness> = impl_witness (@impl.1.%Nom.decl), @impl.1(%Goat.facet) [template]
// CHECK:STDOUT:   %Nom.type.0af: type = fn_type @Nom.2, @impl.1(%Goat.facet) [template]
// CHECK:STDOUT:   %Nom.f15: %Nom.type.0af = struct_value () [template]
// CHECK:STDOUT:   %Eats.facet.a28: %Eats.type = facet_value %Ginger, %impl_witness.71e [template]
// CHECK:STDOUT:   %FeedGoat.specific_fn.4d2: <specific function> = specific_function %FeedGoat, @FeedGoat(%Eats.facet.a28) [template]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Core: <namespace> = namespace file.%Core.import, [template] {
// CHECK:STDOUT:     .ImplicitAs = %Core.ImplicitAs
// CHECK:STDOUT:     import Core//default
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.ff5 = import_ref Core//default, inst26 [no loc], unloaded
// CHECK:STDOUT:   %Core.import_ref.630: @ImplicitAs.%ImplicitAs.assoc_type (%ImplicitAs.assoc_type.837) = import_ref Core//default, loc5_32, loaded [symbolic = @ImplicitAs.%assoc0 (constants.%assoc0.43db8b.2)]
// CHECK:STDOUT:   %Core.Convert = import_ref Core//default, Convert, unloaded
// CHECK:STDOUT:   %Core.import_ref.207961.1 = import_ref Core//default, loc5_32, unloaded
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: file {
// CHECK:STDOUT:   package: <namespace> = namespace [template] {
// CHECK:STDOUT:     .Core = imports.%Core
// CHECK:STDOUT:     .Eats = %Eats.decl
// CHECK:STDOUT:     .Goat = %Goat.decl
// CHECK:STDOUT:     .FeedGoat = %FeedGoat.decl
// CHECK:STDOUT:     .HandleHoat = %HandleHoat.decl
// CHECK:STDOUT:     .Ginger = %Ginger.decl
// CHECK:STDOUT:     .F = %F.decl
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import = import Core
// CHECK:STDOUT:   %Eats.decl: type = interface_decl @Eats [template = constants.%Eats.type] {} {}
// CHECK:STDOUT:   %Goat.decl: type = interface_decl @Goat [template = constants.%Goat.type] {} {}
// CHECK:STDOUT:   impl_decl @impl.1 [template] {
// CHECK:STDOUT:     %G.patt.loc11_14.1: %Goat.type = symbolic_binding_pattern G, 0 [symbolic = %G.patt.loc11_14.2 (constants.%G.patt)]
// CHECK:STDOUT:     %G.param_patt: %Goat.type = value_param_pattern %G.patt.loc11_14.1, runtime_param<none> [symbolic = %G.patt.loc11_14.2 (constants.%G.patt)]
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %G.ref: %Goat.type = name_ref G, %G.loc11_14.1 [symbolic = %G.loc11_14.2 (constants.%G)]
// CHECK:STDOUT:     %G.as_type.loc11_24.1: type = facet_access_type %G.ref [symbolic = %G.as_type.loc11_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:     %.loc11: type = converted %G.ref, %G.as_type.loc11_24.1 [symbolic = %G.as_type.loc11_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:     %Eats.ref: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:     %G.param: %Goat.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:     %G.loc11_14.1: %Goat.type = bind_symbolic_name G, 0, %G.param [symbolic = %G.loc11_14.2 (constants.%G)]
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %impl_witness.loc11: <witness> = impl_witness (@impl.1.%Nom.decl), @impl.1(constants.%G) [symbolic = @impl.1.%impl_witness (constants.%impl_witness.b2f71e.1)]
// CHECK:STDOUT:   %FeedGoat.decl: %FeedGoat.type = fn_decl @FeedGoat [template = constants.%FeedGoat] {
// CHECK:STDOUT:     %T.patt.loc15_13.1: %Eats.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc15_13.2 (constants.%T.patt.6be)]
// CHECK:STDOUT:     %T.param_patt: %Eats.type = value_param_pattern %T.patt.loc15_13.1, runtime_param<none> [symbolic = %T.patt.loc15_13.2 (constants.%T.patt.6be)]
// CHECK:STDOUT:     %e.patt: @FeedGoat.%T.as_type.loc15_26.2 (%T.as_type.27d) = binding_pattern e
// CHECK:STDOUT:     %e.param_patt: @FeedGoat.%T.as_type.loc15_26.2 (%T.as_type.27d) = value_param_pattern %e.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %T.param: %Eats.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Eats.ref.loc15: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:     %T.loc15_13.1: %Eats.type = bind_symbolic_name T, 0, %T.param [symbolic = %T.loc15_13.2 (constants.%T.1b5)]
// CHECK:STDOUT:     %e.param: @FeedGoat.%T.as_type.loc15_26.2 (%T.as_type.27d) = value_param runtime_param0
// CHECK:STDOUT:     %.loc15_26.1: type = splice_block %.loc15_26.2 [symbolic = %T.as_type.loc15_26.2 (constants.%T.as_type.27d)] {
// CHECK:STDOUT:       %T.ref: %Eats.type = name_ref T, %T.loc15_13.1 [symbolic = %T.loc15_13.2 (constants.%T.1b5)]
// CHECK:STDOUT:       %T.as_type.loc15_26.1: type = facet_access_type %T.ref [symbolic = %T.as_type.loc15_26.2 (constants.%T.as_type.27d)]
// CHECK:STDOUT:       %.loc15_26.2: type = converted %T.ref, %T.as_type.loc15_26.1 [symbolic = %T.as_type.loc15_26.2 (constants.%T.as_type.27d)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %e: @FeedGoat.%T.as_type.loc15_26.2 (%T.as_type.27d) = bind_name e, %e.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %HandleHoat.decl: %HandleHoat.type = fn_decl @HandleHoat [template = constants.%HandleHoat] {
// CHECK:STDOUT:     %T.patt.loc37_15.1: %Goat.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc37_15.2 (constants.%T.patt.615)]
// CHECK:STDOUT:     %T.param_patt: %Goat.type = value_param_pattern %T.patt.loc37_15.1, runtime_param<none> [symbolic = %T.patt.loc37_15.2 (constants.%T.patt.615)]
// CHECK:STDOUT:     %g.patt: @HandleHoat.%T.as_type.loc37_28.2 (%T.as_type.c35) = binding_pattern g
// CHECK:STDOUT:     %g.param_patt: @HandleHoat.%T.as_type.loc37_28.2 (%T.as_type.c35) = value_param_pattern %g.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %T.param: %Goat.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:     %T.loc37_15.1: %Goat.type = bind_symbolic_name T, 0, %T.param [symbolic = %T.loc37_15.2 (constants.%T.092)]
// CHECK:STDOUT:     %g.param: @HandleHoat.%T.as_type.loc37_28.2 (%T.as_type.c35) = value_param runtime_param0
// CHECK:STDOUT:     %.loc37_28.1: type = splice_block %.loc37_28.2 [symbolic = %T.as_type.loc37_28.2 (constants.%T.as_type.c35)] {
// CHECK:STDOUT:       %T.ref: %Goat.type = name_ref T, %T.loc37_15.1 [symbolic = %T.loc37_15.2 (constants.%T.092)]
// CHECK:STDOUT:       %T.as_type.loc37_28.1: type = facet_access_type %T.ref [symbolic = %T.as_type.loc37_28.2 (constants.%T.as_type.c35)]
// CHECK:STDOUT:       %.loc37_28.2: type = converted %T.ref, %T.as_type.loc37_28.1 [symbolic = %T.as_type.loc37_28.2 (constants.%T.as_type.c35)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %g: @HandleHoat.%T.as_type.loc37_28.2 (%T.as_type.c35) = bind_name g, %g.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Ginger.decl: type = class_decl @Ginger [template = constants.%Ginger] {} {}
// CHECK:STDOUT:   impl_decl @impl.2 [template] {} {
// CHECK:STDOUT:     %Ginger.ref: type = name_ref Ginger, file.%Ginger.decl [template = constants.%Ginger]
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %impl_witness.loc42: <witness> = impl_witness () [template = constants.%impl_witness.1bc]
// CHECK:STDOUT:   impl_decl @impl.3 [template] {} {
// CHECK:STDOUT:     %Ginger.ref: type = name_ref Ginger, file.%Ginger.decl [template = constants.%Ginger]
// CHECK:STDOUT:     %Eats.ref: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %impl_witness.loc44: <witness> = impl_witness (@impl.3.%Nom.decl) [template = constants.%impl_witness.e95]
// CHECK:STDOUT:   %F.decl: %F.type = fn_decl @F [template = constants.%F] {} {}
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: interface @Eats {
// CHECK:STDOUT:   %Self: %Eats.type = bind_symbolic_name Self, 0 [symbolic = constants.%Self.1b5]
// CHECK:STDOUT:   %Nom.decl: %Nom.type.a33 = fn_decl @Nom.1 [template = constants.%Nom.f11] {
// CHECK:STDOUT:     %self.patt: @Nom.1.%Self.as_type.loc7_16.1 (%Self.as_type.27d) = binding_pattern self
// CHECK:STDOUT:     %self.param_patt: @Nom.1.%Self.as_type.loc7_16.1 (%Self.as_type.27d) = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %self.param: @Nom.1.%Self.as_type.loc7_16.1 (%Self.as_type.27d) = value_param runtime_param0
// CHECK:STDOUT:     %.loc7_16.1: type = splice_block %.loc7_16.2 [symbolic = %Self.as_type.loc7_16.1 (constants.%Self.as_type.27d)] {
// CHECK:STDOUT:       %Self.ref: %Eats.type = name_ref Self, @Eats.%Self [symbolic = %Self (constants.%Self.1b5)]
// CHECK:STDOUT:       %Self.as_type.loc7_16.2: type = facet_access_type %Self.ref [symbolic = %Self.as_type.loc7_16.1 (constants.%Self.as_type.27d)]
// CHECK:STDOUT:       %.loc7_16.2: type = converted %Self.ref, %Self.as_type.loc7_16.2 [symbolic = %Self.as_type.loc7_16.1 (constants.%Self.as_type.27d)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %self: @Nom.1.%Self.as_type.loc7_16.1 (%Self.as_type.27d) = bind_name self, %self.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %assoc0: %Eats.assoc_type = assoc_entity element0, %Nom.decl [template = constants.%assoc0.457]
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Self = %Self
// CHECK:STDOUT:   .Nom = %assoc0
// CHECK:STDOUT:   witness = (%Nom.decl)
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: interface @Goat {
// CHECK:STDOUT:   %Self: %Goat.type = bind_symbolic_name Self, 0 [symbolic = constants.%Self.092]
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Self = %Self
// CHECK:STDOUT:   witness = ()
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic interface @ImplicitAs(constants.%T.8b3: type) [from "core.carbon"] {
// CHECK:STDOUT:   %T: type = bind_symbolic_name T, 0 [symbolic = %T (constants.%T.8b3)]
// CHECK:STDOUT:   %T.patt: type = symbolic_binding_pattern T, 0 [symbolic = %T.patt (constants.%T.patt.e01)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %ImplicitAs.type: type = facet_type <@ImplicitAs, @ImplicitAs(%T)> [symbolic = %ImplicitAs.type (constants.%ImplicitAs.type.d62)]
// CHECK:STDOUT:   %Self: %ImplicitAs.type.d62 = bind_symbolic_name Self, 1 [symbolic = %Self (constants.%Self.519)]
// CHECK:STDOUT:   %Convert.type: type = fn_type @Convert, @ImplicitAs(%T) [symbolic = %Convert.type (constants.%Convert.type.275)]
// CHECK:STDOUT:   %Convert: @ImplicitAs.%Convert.type (%Convert.type.275) = struct_value () [symbolic = %Convert (constants.%Convert.42e)]
// CHECK:STDOUT:   %ImplicitAs.assoc_type: type = assoc_entity_type @ImplicitAs.%ImplicitAs.type (%ImplicitAs.type.d62) [symbolic = %ImplicitAs.assoc_type (constants.%ImplicitAs.assoc_type.837)]
// CHECK:STDOUT:   %assoc0: @ImplicitAs.%ImplicitAs.assoc_type (%ImplicitAs.assoc_type.837) = assoc_entity element0, imports.%Core.import_ref.207961.1 [symbolic = %assoc0 (constants.%assoc0.43db8b.1)]
// CHECK:STDOUT:
// CHECK:STDOUT:   interface {
// CHECK:STDOUT:   !members:
// CHECK:STDOUT:     .Self = imports.%Core.import_ref.ff5
// CHECK:STDOUT:     .Convert = imports.%Core.import_ref.630
// CHECK:STDOUT:     witness = (imports.%Core.Convert)
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic impl @impl.1(%G.loc11_14.1: %Goat.type) {
// CHECK:STDOUT:   %G.loc11_14.2: %Goat.type = bind_symbolic_name G, 0 [symbolic = %G.loc11_14.2 (constants.%G)]
// CHECK:STDOUT:   %G.patt.loc11_14.2: %Goat.type = symbolic_binding_pattern G, 0 [symbolic = %G.patt.loc11_14.2 (constants.%G.patt)]
// CHECK:STDOUT:   %G.as_type.loc11_24.2: type = facet_access_type %G.loc11_14.2 [symbolic = %G.as_type.loc11_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness (%Nom.decl), @impl.1(%G.loc11_14.2) [symbolic = %impl_witness (constants.%impl_witness.b2f71e.1)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %Nom.type: type = fn_type @Nom.2, @impl.1(%G.loc11_14.2) [symbolic = %Nom.type (constants.%Nom.type.c957c6.1)]
// CHECK:STDOUT:   %Nom: @impl.1.%Nom.type (%Nom.type.c957c6.1) = struct_value () [symbolic = %Nom (constants.%Nom.5b3b79.1)]
// CHECK:STDOUT:
// CHECK:STDOUT:   impl: %.loc11 as %Eats.ref {
// CHECK:STDOUT:     %Nom.decl: @impl.1.%Nom.type (%Nom.type.c957c6.1) = fn_decl @Nom.2 [symbolic = @impl.1.%Nom (constants.%Nom.5b3b79.1)] {
// CHECK:STDOUT:       %self.patt: @Nom.2.%G.as_type (%G.as_type) = binding_pattern self
// CHECK:STDOUT:       %self.param_patt: @Nom.2.%G.as_type (%G.as_type) = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:     } {
// CHECK:STDOUT:       %self.param: @Nom.2.%G.as_type (%G.as_type) = value_param runtime_param0
// CHECK:STDOUT:       %Self.ref: type = name_ref Self, @impl.1.%.loc11 [symbolic = %G.as_type (constants.%G.as_type)]
// CHECK:STDOUT:       %self: @Nom.2.%G.as_type (%G.as_type) = bind_name self, %self.param
// CHECK:STDOUT:     }
// CHECK:STDOUT:
// CHECK:STDOUT:   !members:
// CHECK:STDOUT:     .Nom = %Nom.decl
// CHECK:STDOUT:     witness = file.%impl_witness.loc11
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: impl @impl.2: %Ginger.ref as %Goat.ref {
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   witness = file.%impl_witness.loc42
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: impl @impl.3: %Ginger.ref as %Eats.ref {
// CHECK:STDOUT:   %Nom.decl: %Nom.type.b13 = fn_decl @Nom.3 [template = constants.%Nom.826] {
// CHECK:STDOUT:     %self.patt: %Ginger = binding_pattern self
// CHECK:STDOUT:     %self.param_patt: %Ginger = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %self.param: %Ginger = value_param runtime_param0
// CHECK:STDOUT:     %Self.ref: type = name_ref Self, @impl.3.%Ginger.ref [template = constants.%Ginger]
// CHECK:STDOUT:     %self: %Ginger = bind_name self, %self.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Nom = %Nom.decl
// CHECK:STDOUT:   witness = file.%impl_witness.loc44
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: class @Ginger {
// CHECK:STDOUT:   %complete_type: <witness> = complete_type_witness %empty_struct_type [template = constants.%complete_type]
// CHECK:STDOUT:   complete_type_witness = %complete_type
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Self = constants.%Ginger
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Nom.1(@Eats.%Self: %Eats.type) {
// CHECK:STDOUT:   %Self: %Eats.type = bind_symbolic_name Self, 0 [symbolic = %Self (constants.%Self.1b5)]
// CHECK:STDOUT:   %Self.as_type.loc7_16.1: type = facet_access_type %Self [symbolic = %Self.as_type.loc7_16.1 (constants.%Self.as_type.27d)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%self.param_patt: @Nom.1.%Self.as_type.loc7_16.1 (%Self.as_type.27d)]();
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Nom.2(@impl.1.%G.loc11_14.1: %Goat.type) {
// CHECK:STDOUT:   %G: %Goat.type = bind_symbolic_name G, 0 [symbolic = %G (constants.%G)]
// CHECK:STDOUT:   %G.as_type: type = facet_access_type %G [symbolic = %G.as_type (constants.%G.as_type)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type @Nom.2.%G.as_type (%G.as_type) [symbolic = %require_complete (constants.%require_complete.e217cd.1)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%self.param_patt: @Nom.2.%G.as_type (%G.as_type)]() {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @FeedGoat(%T.loc15_13.1: %Eats.type) {
// CHECK:STDOUT:   %T.loc15_13.2: %Eats.type = bind_symbolic_name T, 0 [symbolic = %T.loc15_13.2 (constants.%T.1b5)]
// CHECK:STDOUT:   %T.patt.loc15_13.2: %Eats.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc15_13.2 (constants.%T.patt.6be)]
// CHECK:STDOUT:   %T.as_type.loc15_26.2: type = facet_access_type %T.loc15_13.2 [symbolic = %T.as_type.loc15_26.2 (constants.%T.as_type.27d)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type @FeedGoat.%T.as_type.loc15_26.2 (%T.as_type.27d) [symbolic = %require_complete (constants.%require_complete.c75)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%T.param_patt: %Eats.type](%e.param_patt: @FeedGoat.%T.as_type.loc15_26.2 (%T.as_type.27d)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     %e.ref: @FeedGoat.%T.as_type.loc15_26.2 (%T.as_type.27d) = name_ref e, %e
// CHECK:STDOUT:     %Eats.ref.loc34: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:     %Nom.ref: %Eats.assoc_type = name_ref Nom, @Eats.%assoc0 [template = constants.%assoc0.457]
// CHECK:STDOUT:     %.loc34: %Goat.type = converted constants.%T.as_type.27d, <error> [template = <error>]
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Convert(constants.%T.8b3: type, constants.%Self.519: %ImplicitAs.type.d62) [from "core.carbon"] {
// CHECK:STDOUT:   %T: type = bind_symbolic_name T, 0 [symbolic = %T (constants.%T.8b3)]
// CHECK:STDOUT:   %ImplicitAs.type: type = facet_type <@ImplicitAs, @ImplicitAs(%T)> [symbolic = %ImplicitAs.type (constants.%ImplicitAs.type.d62)]
// CHECK:STDOUT:   %Self: %ImplicitAs.type.d62 = bind_symbolic_name Self, 1 [symbolic = %Self (constants.%Self.519)]
// CHECK:STDOUT:   %Self.as_type: type = facet_access_type %Self [symbolic = %Self.as_type (constants.%Self.as_type.40a)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%self.param_patt: @Convert.%Self.as_type (%Self.as_type.40a)]() -> @Convert.%T (%T.8b3);
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @HandleHoat(%T.loc37_15.1: %Goat.type) {
// CHECK:STDOUT:   %T.loc37_15.2: %Goat.type = bind_symbolic_name T, 0 [symbolic = %T.loc37_15.2 (constants.%T.092)]
// CHECK:STDOUT:   %T.patt.loc37_15.2: %Goat.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc37_15.2 (constants.%T.patt.615)]
// CHECK:STDOUT:   %T.as_type.loc37_28.2: type = facet_access_type %T.loc37_15.2 [symbolic = %T.as_type.loc37_28.2 (constants.%T.as_type.c35)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type @HandleHoat.%T.as_type.loc37_28.2 (%T.as_type.c35) [symbolic = %require_complete (constants.%require_complete.e217cd.2)]
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness (@impl.1.%Nom.decl), @impl.1(%T.loc37_15.2) [symbolic = %impl_witness (constants.%impl_witness.b2f71e.2)]
// CHECK:STDOUT:   %Eats.facet.loc38_13.3: %Eats.type = facet_value %T.as_type.loc37_28.2, %impl_witness [symbolic = %Eats.facet.loc38_13.3 (constants.%Eats.facet.54805c.2)]
// CHECK:STDOUT:   %FeedGoat.specific_fn.loc38_3.2: <specific function> = specific_function constants.%FeedGoat, @FeedGoat(%Eats.facet.loc38_13.3) [symbolic = %FeedGoat.specific_fn.loc38_3.2 (constants.%FeedGoat.specific_fn.48f)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%T.param_patt: %Goat.type](%g.param_patt: @HandleHoat.%T.as_type.loc37_28.2 (%T.as_type.c35)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     %FeedGoat.ref: %FeedGoat.type = name_ref FeedGoat, file.%FeedGoat.decl [template = constants.%FeedGoat]
// CHECK:STDOUT:     %g.ref: @HandleHoat.%T.as_type.loc37_28.2 (%T.as_type.c35) = name_ref g, %g
// CHECK:STDOUT:     %.loc38_13.1: %Goat.type = converted constants.%T.as_type.c35, constants.%T.092 [symbolic = %T.loc37_15.2 (constants.%T.092)]
// CHECK:STDOUT:     %Eats.facet.loc38_13.1: %Eats.type = facet_value constants.%T.as_type.c35, constants.%impl_witness.b2f71e.2 [symbolic = %Eats.facet.loc38_13.3 (constants.%Eats.facet.54805c.2)]
// CHECK:STDOUT:     %.loc38_13.2: %Eats.type = converted constants.%T.as_type.c35, %Eats.facet.loc38_13.1 [symbolic = %Eats.facet.loc38_13.3 (constants.%Eats.facet.54805c.2)]
// CHECK:STDOUT:     %.loc38_13.3: %Goat.type = converted constants.%T.as_type.c35, constants.%T.092 [symbolic = %T.loc37_15.2 (constants.%T.092)]
// CHECK:STDOUT:     %Eats.facet.loc38_13.2: %Eats.type = facet_value constants.%T.as_type.c35, constants.%impl_witness.b2f71e.2 [symbolic = %Eats.facet.loc38_13.3 (constants.%Eats.facet.54805c.2)]
// CHECK:STDOUT:     %.loc38_13.4: %Eats.type = converted constants.%T.as_type.c35, %Eats.facet.loc38_13.2 [symbolic = %Eats.facet.loc38_13.3 (constants.%Eats.facet.54805c.2)]
// CHECK:STDOUT:     %FeedGoat.specific_fn.loc38_3.1: <specific function> = specific_function %FeedGoat.ref, @FeedGoat(constants.%Eats.facet.54805c.2) [symbolic = %FeedGoat.specific_fn.loc38_3.2 (constants.%FeedGoat.specific_fn.48f)]
// CHECK:STDOUT:     %FeedGoat.call: init %empty_tuple.type = call %FeedGoat.specific_fn.loc38_3.1(%g.ref)
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Nom.3[%self.param_patt: %Ginger]() {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @F() {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   %FeedGoat.ref: %FeedGoat.type = name_ref FeedGoat, file.%FeedGoat.decl [template = constants.%FeedGoat]
// CHECK:STDOUT:   %.loc49_13.1: %empty_struct_type = struct_literal ()
// CHECK:STDOUT:   %Ginger.ref: type = name_ref Ginger, file.%Ginger.decl [template = constants.%Ginger]
// CHECK:STDOUT:   %.loc49_13.2: ref %Ginger = temporary_storage
// CHECK:STDOUT:   %.loc49_13.3: init %Ginger = class_init (), %.loc49_13.2 [template = constants.%Ginger.val]
// CHECK:STDOUT:   %.loc49_13.4: ref %Ginger = temporary %.loc49_13.2, %.loc49_13.3
// CHECK:STDOUT:   %.loc49_15.1: ref %Ginger = converted %.loc49_13.1, %.loc49_13.4
// CHECK:STDOUT:   %Goat.facet.loc49_24.1: %Goat.type = facet_value constants.%Ginger, constants.%impl_witness.1bc [template = constants.%Goat.facet]
// CHECK:STDOUT:   %.loc49_24.1: %Goat.type = converted constants.%Ginger, %Goat.facet.loc49_24.1 [template = constants.%Goat.facet]
// CHECK:STDOUT:   %Eats.facet.loc49_24.1: %Eats.type = facet_value constants.%Ginger, constants.%impl_witness.71e [template = constants.%Eats.facet.a28]
// CHECK:STDOUT:   %.loc49_24.2: %Eats.type = converted constants.%Ginger, %Eats.facet.loc49_24.1 [template = constants.%Eats.facet.a28]
// CHECK:STDOUT:   %Goat.facet.loc49_24.2: %Goat.type = facet_value constants.%Ginger, constants.%impl_witness.1bc [template = constants.%Goat.facet]
// CHECK:STDOUT:   %.loc49_24.3: %Goat.type = converted constants.%Ginger, %Goat.facet.loc49_24.2 [template = constants.%Goat.facet]
// CHECK:STDOUT:   %Eats.facet.loc49_24.2: %Eats.type = facet_value constants.%Ginger, constants.%impl_witness.71e [template = constants.%Eats.facet.a28]
// CHECK:STDOUT:   %.loc49_24.4: %Eats.type = converted constants.%Ginger, %Eats.facet.loc49_24.2 [template = constants.%Eats.facet.a28]
// CHECK:STDOUT:   %FeedGoat.specific_fn: <specific function> = specific_function %FeedGoat.ref, @FeedGoat(constants.%Eats.facet.a28) [template = constants.%FeedGoat.specific_fn.4d2]
// CHECK:STDOUT:   %.loc49_15.2: %Ginger = bind_value %.loc49_15.1
// CHECK:STDOUT:   %FeedGoat.call: init %empty_tuple.type = call %FeedGoat.specific_fn(%.loc49_15.2)
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Nom.1(constants.%Self.1b5) {
// CHECK:STDOUT:   %Self => constants.%Self.1b5
// CHECK:STDOUT:   %Self.as_type.loc7_16.1 => constants.%Self.as_type.27d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(constants.%G) {
// CHECK:STDOUT:   %G.loc11_14.2 => constants.%G
// CHECK:STDOUT:   %G.patt.loc11_14.2 => constants.%G
// CHECK:STDOUT:   %G.as_type.loc11_24.2 => constants.%G.as_type
// CHECK:STDOUT:   %impl_witness => constants.%impl_witness.b2f71e.1
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %Nom.type => constants.%Nom.type.c957c6.1
// CHECK:STDOUT:   %Nom => constants.%Nom.5b3b79.1
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(%G.loc11_14.2) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Nom.2(constants.%G) {
// CHECK:STDOUT:   %G => constants.%G
// CHECK:STDOUT:   %G.as_type => constants.%G.as_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Nom.1(constants.%Eats.facet.54805c.1) {
// CHECK:STDOUT:   %Self => constants.%Eats.facet.54805c.1
// CHECK:STDOUT:   %Self.as_type.loc7_16.1 => constants.%G.as_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @FeedGoat(constants.%T.1b5) {
// CHECK:STDOUT:   %T.loc15_13.2 => constants.%T.1b5
// CHECK:STDOUT:   %T.patt.loc15_13.2 => constants.%T.1b5
// CHECK:STDOUT:   %T.as_type.loc15_26.2 => constants.%T.as_type.27d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @ImplicitAs(constants.%T.8b3) {
// CHECK:STDOUT:   %T => constants.%T.8b3
// CHECK:STDOUT:   %T.patt => constants.%T.8b3
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @ImplicitAs(%T) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @ImplicitAs(@Convert.%T) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Convert(constants.%T.8b3, constants.%Self.519) {
// CHECK:STDOUT:   %T => constants.%T.8b3
// CHECK:STDOUT:   %ImplicitAs.type => constants.%ImplicitAs.type.d62
// CHECK:STDOUT:   %Self => constants.%Self.519
// CHECK:STDOUT:   %Self.as_type => constants.%Self.as_type.40a
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @ImplicitAs(constants.%Goat.type) {
// CHECK:STDOUT:   %T => constants.%Goat.type
// CHECK:STDOUT:   %T.patt => constants.%Goat.type
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %ImplicitAs.type => constants.%ImplicitAs.type.64f
// CHECK:STDOUT:   %Self => constants.%Self.519
// CHECK:STDOUT:   %Convert.type => constants.%Convert.type.f88
// CHECK:STDOUT:   %Convert => constants.%Convert.137
// CHECK:STDOUT:   %ImplicitAs.assoc_type => constants.%ImplicitAs.assoc_type.769
// CHECK:STDOUT:   %assoc0 => constants.%assoc0.579
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @HandleHoat(constants.%T.092) {
// CHECK:STDOUT:   %T.loc37_15.2 => constants.%T.092
// CHECK:STDOUT:   %T.patt.loc37_15.2 => constants.%T.092
// CHECK:STDOUT:   %T.as_type.loc37_28.2 => constants.%T.as_type.c35
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(constants.%T.092) {
// CHECK:STDOUT:   %G.loc11_14.2 => constants.%T.092
// CHECK:STDOUT:   %G.patt.loc11_14.2 => constants.%T.092
// CHECK:STDOUT:   %G.as_type.loc11_24.2 => constants.%T.as_type.c35
// CHECK:STDOUT:   %impl_witness => constants.%impl_witness.b2f71e.2
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %Nom.type => constants.%Nom.type.c957c6.2
// CHECK:STDOUT:   %Nom => constants.%Nom.5b3b79.2
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @FeedGoat(constants.%Eats.facet.54805c.2) {
// CHECK:STDOUT:   %T.loc15_13.2 => constants.%Eats.facet.54805c.2
// CHECK:STDOUT:   %T.patt.loc15_13.2 => constants.%Eats.facet.54805c.2
// CHECK:STDOUT:   %T.as_type.loc15_26.2 => constants.%T.as_type.c35
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete => constants.%require_complete.e217cd.2
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(@HandleHoat.%T.loc37_15.2) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @FeedGoat(@HandleHoat.%Eats.facet.loc38_13.3) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Nom.1(constants.%Eats.facet.930) {
// CHECK:STDOUT:   %Self => constants.%Eats.facet.930
// CHECK:STDOUT:   %Self.as_type.loc7_16.1 => constants.%Ginger
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(constants.%Goat.facet) {
// CHECK:STDOUT:   %G.loc11_14.2 => constants.%Goat.facet
// CHECK:STDOUT:   %G.patt.loc11_14.2 => constants.%Goat.facet
// CHECK:STDOUT:   %G.as_type.loc11_24.2 => constants.%Ginger
// CHECK:STDOUT:   %impl_witness => constants.%impl_witness.71e
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %Nom.type => constants.%Nom.type.0af
// CHECK:STDOUT:   %Nom => constants.%Nom.f15
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @FeedGoat(constants.%Eats.facet.a28) {
// CHECK:STDOUT:   %T.loc15_13.2 => constants.%Eats.facet.a28
// CHECK:STDOUT:   %T.patt.loc15_13.2 => constants.%Eats.facet.a28
// CHECK:STDOUT:   %T.as_type.loc15_26.2 => constants.%Ginger
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete => constants.%complete_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
