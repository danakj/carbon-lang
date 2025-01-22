// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// AUTOUPDATE
// TIP: To test this file alone, run:
// TIP:   bazel test //toolchain/testing:file_test --test_arg=--file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/convert_self_to_blanket_impl.carbon
// TIP: To dump output, run:
// TIP:   bazel run //toolchain/testing:file_test -- --dump_output --file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/convert_self_to_blanket_impl.carbon

interface Eats {
  fn Eat[self: Self]();
}
interface Goat {
  fn Wander[self: Self]();
}

impl forall [G:! Goat] G as Eats {
  fn Eat[self: Self]() {}
}

class Ginger {}
impl Ginger as Goat {
  fn Wander[self: Self]() {
    self.(Eats.Eat)();
  }
}

// CHECK:STDOUT: --- convert_self_to_blanket_impl.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Eats.type: type = facet_type <@Eats> [template]
// CHECK:STDOUT:   %Self.1b5: %Eats.type = bind_symbolic_name Self, 0 [symbolic]
// CHECK:STDOUT:   %Self.as_type.27d: type = facet_access_type %Self.1b5 [symbolic]
// CHECK:STDOUT:   %Eat.type.e5d: type = fn_type @Eat.1 [template]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [template]
// CHECK:STDOUT:   %Eat.7cd: %Eat.type.e5d = struct_value () [template]
// CHECK:STDOUT:   %Eats.assoc_type: type = assoc_entity_type %Eats.type [template]
// CHECK:STDOUT:   %assoc0.303: %Eats.assoc_type = assoc_entity element0, @Eats.%Eat.decl [template]
// CHECK:STDOUT:   %Goat.type: type = facet_type <@Goat> [template]
// CHECK:STDOUT:   %Self.092: %Goat.type = bind_symbolic_name Self, 0 [symbolic]
// CHECK:STDOUT:   %Self.as_type.c35: type = facet_access_type %Self.092 [symbolic]
// CHECK:STDOUT:   %Wander.type.046: type = fn_type @Wander.1 [template]
// CHECK:STDOUT:   %Wander.826: %Wander.type.046 = struct_value () [template]
// CHECK:STDOUT:   %Goat.assoc_type: type = assoc_entity_type %Goat.type [template]
// CHECK:STDOUT:   %assoc0.4fc: %Goat.assoc_type = assoc_entity element0, @Goat.%Wander.decl [template]
// CHECK:STDOUT:   %G: %Goat.type = bind_symbolic_name G, 0 [symbolic]
// CHECK:STDOUT:   %G.patt: %Goat.type = symbolic_binding_pattern G, 0 [symbolic]
// CHECK:STDOUT:   %G.as_type: type = facet_access_type %G [symbolic]
// CHECK:STDOUT:   %impl_witness.214: <witness> = impl_witness (@impl.1.%Eat.decl), @impl.1(%G) [symbolic]
// CHECK:STDOUT:   %Eat.type.f3a: type = fn_type @Eat.2, @impl.1(%G) [symbolic]
// CHECK:STDOUT:   %Eat.ccf: %Eat.type.f3a = struct_value () [symbolic]
// CHECK:STDOUT:   %Eats.facet: %Eats.type = facet_value %G.as_type, %impl_witness.214 [symbolic]
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type %G.as_type [symbolic]
// CHECK:STDOUT:   %Ginger: type = class_type @Ginger [template]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [template]
// CHECK:STDOUT:   %complete_type: <witness> = complete_type_witness %empty_struct_type [template]
// CHECK:STDOUT:   %impl_witness.605: <witness> = impl_witness (@impl.2.%Wander.decl) [template]
// CHECK:STDOUT:   %Wander.type.4ea: type = fn_type @Wander.2 [template]
// CHECK:STDOUT:   %Wander.450: %Wander.type.4ea = struct_value () [template]
// CHECK:STDOUT:   %Goat.facet: %Goat.type = facet_value %Ginger, %impl_witness.605 [template]
// CHECK:STDOUT:   %impl_witness.e6c: <witness> = impl_witness (@impl.1.%Eat.decl), @impl.1(%Goat.facet) [template]
// CHECK:STDOUT:   %Eat.type.209: type = fn_type @Eat.2, @impl.1(%Goat.facet) [template]
// CHECK:STDOUT:   %Eat.424: %Eat.type.209 = struct_value () [template]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: file {
// CHECK:STDOUT:   package: <namespace> = namespace [template] {
// CHECK:STDOUT:     .Eats = %Eats.decl
// CHECK:STDOUT:     .Goat = %Goat.decl
// CHECK:STDOUT:     .Ginger = %Ginger.decl
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Eats.decl: type = interface_decl @Eats [template = constants.%Eats.type] {} {}
// CHECK:STDOUT:   %Goat.decl: type = interface_decl @Goat [template = constants.%Goat.type] {} {}
// CHECK:STDOUT:   impl_decl @impl.1 [template] {
// CHECK:STDOUT:     %G.patt.loc18_14.1: %Goat.type = symbolic_binding_pattern G, 0 [symbolic = %G.patt.loc18_14.2 (constants.%G.patt)]
// CHECK:STDOUT:     %G.param_patt: %Goat.type = value_param_pattern %G.patt.loc18_14.1, runtime_param<none> [symbolic = %G.patt.loc18_14.2 (constants.%G.patt)]
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %G.ref: %Goat.type = name_ref G, %G.loc18_14.1 [symbolic = %G.loc18_14.2 (constants.%G)]
// CHECK:STDOUT:     %G.as_type.loc18_24.1: type = facet_access_type %G.ref [symbolic = %G.as_type.loc18_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:     %.loc18: type = converted %G.ref, %G.as_type.loc18_24.1 [symbolic = %G.as_type.loc18_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:     %Eats.ref: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:     %G.param: %Goat.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:     %G.loc18_14.1: %Goat.type = bind_symbolic_name G, 0, %G.param [symbolic = %G.loc18_14.2 (constants.%G)]
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %impl_witness.loc18: <witness> = impl_witness (@impl.1.%Eat.decl), @impl.1(constants.%G) [symbolic = @impl.1.%impl_witness (constants.%impl_witness.214)]
// CHECK:STDOUT:   %Ginger.decl: type = class_decl @Ginger [template = constants.%Ginger] {} {}
// CHECK:STDOUT:   impl_decl @impl.2 [template] {} {
// CHECK:STDOUT:     %Ginger.ref: type = name_ref Ginger, file.%Ginger.decl [template = constants.%Ginger]
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %impl_witness.loc23: <witness> = impl_witness (@impl.2.%Wander.decl) [template = constants.%impl_witness.605]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: interface @Eats {
// CHECK:STDOUT:   %Self: %Eats.type = bind_symbolic_name Self, 0 [symbolic = constants.%Self.1b5]
// CHECK:STDOUT:   %Eat.decl: %Eat.type.e5d = fn_decl @Eat.1 [template = constants.%Eat.7cd] {
// CHECK:STDOUT:     %self.patt: @Eat.1.%Self.as_type.loc12_16.1 (%Self.as_type.27d) = binding_pattern self
// CHECK:STDOUT:     %self.param_patt: @Eat.1.%Self.as_type.loc12_16.1 (%Self.as_type.27d) = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %self.param: @Eat.1.%Self.as_type.loc12_16.1 (%Self.as_type.27d) = value_param runtime_param0
// CHECK:STDOUT:     %.loc12_16.1: type = splice_block %.loc12_16.2 [symbolic = %Self.as_type.loc12_16.1 (constants.%Self.as_type.27d)] {
// CHECK:STDOUT:       %Self.ref: %Eats.type = name_ref Self, @Eats.%Self [symbolic = %Self (constants.%Self.1b5)]
// CHECK:STDOUT:       %Self.as_type.loc12_16.2: type = facet_access_type %Self.ref [symbolic = %Self.as_type.loc12_16.1 (constants.%Self.as_type.27d)]
// CHECK:STDOUT:       %.loc12_16.2: type = converted %Self.ref, %Self.as_type.loc12_16.2 [symbolic = %Self.as_type.loc12_16.1 (constants.%Self.as_type.27d)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %self: @Eat.1.%Self.as_type.loc12_16.1 (%Self.as_type.27d) = bind_name self, %self.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %assoc0: %Eats.assoc_type = assoc_entity element0, %Eat.decl [template = constants.%assoc0.303]
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Self = %Self
// CHECK:STDOUT:   .Eat = %assoc0
// CHECK:STDOUT:   witness = (%Eat.decl)
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: interface @Goat {
// CHECK:STDOUT:   %Self: %Goat.type = bind_symbolic_name Self, 0 [symbolic = constants.%Self.092]
// CHECK:STDOUT:   %Wander.decl: %Wander.type.046 = fn_decl @Wander.1 [template = constants.%Wander.826] {
// CHECK:STDOUT:     %self.patt: @Wander.1.%Self.as_type.loc15_19.1 (%Self.as_type.c35) = binding_pattern self
// CHECK:STDOUT:     %self.param_patt: @Wander.1.%Self.as_type.loc15_19.1 (%Self.as_type.c35) = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %self.param: @Wander.1.%Self.as_type.loc15_19.1 (%Self.as_type.c35) = value_param runtime_param0
// CHECK:STDOUT:     %.loc15_19.1: type = splice_block %.loc15_19.2 [symbolic = %Self.as_type.loc15_19.1 (constants.%Self.as_type.c35)] {
// CHECK:STDOUT:       %Self.ref: %Goat.type = name_ref Self, @Goat.%Self [symbolic = %Self (constants.%Self.092)]
// CHECK:STDOUT:       %Self.as_type.loc15_19.2: type = facet_access_type %Self.ref [symbolic = %Self.as_type.loc15_19.1 (constants.%Self.as_type.c35)]
// CHECK:STDOUT:       %.loc15_19.2: type = converted %Self.ref, %Self.as_type.loc15_19.2 [symbolic = %Self.as_type.loc15_19.1 (constants.%Self.as_type.c35)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %self: @Wander.1.%Self.as_type.loc15_19.1 (%Self.as_type.c35) = bind_name self, %self.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %assoc0: %Goat.assoc_type = assoc_entity element0, %Wander.decl [template = constants.%assoc0.4fc]
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Self = %Self
// CHECK:STDOUT:   .Wander = %assoc0
// CHECK:STDOUT:   witness = (%Wander.decl)
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic impl @impl.1(%G.loc18_14.1: %Goat.type) {
// CHECK:STDOUT:   %G.loc18_14.2: %Goat.type = bind_symbolic_name G, 0 [symbolic = %G.loc18_14.2 (constants.%G)]
// CHECK:STDOUT:   %G.patt.loc18_14.2: %Goat.type = symbolic_binding_pattern G, 0 [symbolic = %G.patt.loc18_14.2 (constants.%G.patt)]
// CHECK:STDOUT:   %G.as_type.loc18_24.2: type = facet_access_type %G.loc18_14.2 [symbolic = %G.as_type.loc18_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness (%Eat.decl), @impl.1(%G.loc18_14.2) [symbolic = %impl_witness (constants.%impl_witness.214)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %Eat.type: type = fn_type @Eat.2, @impl.1(%G.loc18_14.2) [symbolic = %Eat.type (constants.%Eat.type.f3a)]
// CHECK:STDOUT:   %Eat: @impl.1.%Eat.type (%Eat.type.f3a) = struct_value () [symbolic = %Eat (constants.%Eat.ccf)]
// CHECK:STDOUT:
// CHECK:STDOUT:   impl: %.loc18 as %Eats.ref {
// CHECK:STDOUT:     %Eat.decl: @impl.1.%Eat.type (%Eat.type.f3a) = fn_decl @Eat.2 [symbolic = @impl.1.%Eat (constants.%Eat.ccf)] {
// CHECK:STDOUT:       %self.patt: @Eat.2.%G.as_type (%G.as_type) = binding_pattern self
// CHECK:STDOUT:       %self.param_patt: @Eat.2.%G.as_type (%G.as_type) = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:     } {
// CHECK:STDOUT:       %self.param: @Eat.2.%G.as_type (%G.as_type) = value_param runtime_param0
// CHECK:STDOUT:       %Self.ref: type = name_ref Self, @impl.1.%.loc18 [symbolic = %G.as_type (constants.%G.as_type)]
// CHECK:STDOUT:       %self: @Eat.2.%G.as_type (%G.as_type) = bind_name self, %self.param
// CHECK:STDOUT:     }
// CHECK:STDOUT:
// CHECK:STDOUT:   !members:
// CHECK:STDOUT:     .Eat = %Eat.decl
// CHECK:STDOUT:     witness = file.%impl_witness.loc18
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: impl @impl.2: %Ginger.ref as %Goat.ref {
// CHECK:STDOUT:   %Wander.decl: %Wander.type.4ea = fn_decl @Wander.2 [template = constants.%Wander.450] {
// CHECK:STDOUT:     %self.patt: %Ginger = binding_pattern self
// CHECK:STDOUT:     %self.param_patt: %Ginger = value_param_pattern %self.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %self.param: %Ginger = value_param runtime_param0
// CHECK:STDOUT:     %Self.ref: type = name_ref Self, @impl.2.%Ginger.ref [template = constants.%Ginger]
// CHECK:STDOUT:     %self: %Ginger = bind_name self, %self.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Wander = %Wander.decl
// CHECK:STDOUT:   witness = file.%impl_witness.loc23
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
// CHECK:STDOUT: generic fn @Eat.1(@Eats.%Self: %Eats.type) {
// CHECK:STDOUT:   %Self: %Eats.type = bind_symbolic_name Self, 0 [symbolic = %Self (constants.%Self.1b5)]
// CHECK:STDOUT:   %Self.as_type.loc12_16.1: type = facet_access_type %Self [symbolic = %Self.as_type.loc12_16.1 (constants.%Self.as_type.27d)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%self.param_patt: @Eat.1.%Self.as_type.loc12_16.1 (%Self.as_type.27d)]();
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Wander.1(@Goat.%Self: %Goat.type) {
// CHECK:STDOUT:   %Self: %Goat.type = bind_symbolic_name Self, 0 [symbolic = %Self (constants.%Self.092)]
// CHECK:STDOUT:   %Self.as_type.loc15_19.1: type = facet_access_type %Self [symbolic = %Self.as_type.loc15_19.1 (constants.%Self.as_type.c35)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%self.param_patt: @Wander.1.%Self.as_type.loc15_19.1 (%Self.as_type.c35)]();
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Eat.2(@impl.1.%G.loc18_14.1: %Goat.type) {
// CHECK:STDOUT:   %G: %Goat.type = bind_symbolic_name G, 0 [symbolic = %G (constants.%G)]
// CHECK:STDOUT:   %G.as_type: type = facet_access_type %G [symbolic = %G.as_type (constants.%G.as_type)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type @Eat.2.%G.as_type (%G.as_type) [symbolic = %require_complete (constants.%require_complete)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%self.param_patt: @Eat.2.%G.as_type (%G.as_type)]() {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Wander.2[%self.param_patt: %Ginger]() {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   %self.ref: %Ginger = name_ref self, %self
// CHECK:STDOUT:   %Eats.ref: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:   %Eat.ref: %Eats.assoc_type = name_ref Eat, @Eats.%assoc0 [template = constants.%assoc0.303]
// CHECK:STDOUT:   %Goat.facet: %Goat.type = facet_value constants.%Ginger, constants.%impl_witness.605 [template = constants.%Goat.facet]
// CHECK:STDOUT:   %.loc25: %Goat.type = converted constants.%Ginger, %Goat.facet [template = constants.%Goat.facet]
// CHECK:STDOUT:   %impl.elem0: %Eat.type.e5d = impl_witness_access constants.%impl_witness.e6c, element0 [template = constants.%Eat.424]
// CHECK:STDOUT:   %Eat.bound: <bound method> = bound_method %self.ref, %impl.elem0
// CHECK:STDOUT:   %Eat.specific_fn: <specific function> = specific_function %Eat.bound, @Eat.2(constants.%Goat.facet)
// CHECK:STDOUT:   %Eat.call: init %empty_tuple.type = call %Eat.specific_fn(%self.ref)
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Eat.1(constants.%Self.1b5) {
// CHECK:STDOUT:   %Self => constants.%Self.1b5
// CHECK:STDOUT:   %Self.as_type.loc12_16.1 => constants.%Self.as_type.27d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Wander.1(constants.%Self.092) {
// CHECK:STDOUT:   %Self => constants.%Self.092
// CHECK:STDOUT:   %Self.as_type.loc15_19.1 => constants.%Self.as_type.c35
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(constants.%G) {
// CHECK:STDOUT:   %G.loc18_14.2 => constants.%G
// CHECK:STDOUT:   %G.patt.loc18_14.2 => constants.%G
// CHECK:STDOUT:   %G.as_type.loc18_24.2 => constants.%G.as_type
// CHECK:STDOUT:   %impl_witness => constants.%impl_witness.214
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %Eat.type => constants.%Eat.type.f3a
// CHECK:STDOUT:   %Eat => constants.%Eat.ccf
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(%G.loc18_14.2) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Eat.2(constants.%G) {
// CHECK:STDOUT:   %G => constants.%G
// CHECK:STDOUT:   %G.as_type => constants.%G.as_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Eat.1(constants.%Eats.facet) {
// CHECK:STDOUT:   %Self => constants.%Eats.facet
// CHECK:STDOUT:   %Self.as_type.loc12_16.1 => constants.%G.as_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Wander.1(constants.%Goat.facet) {
// CHECK:STDOUT:   %Self => constants.%Goat.facet
// CHECK:STDOUT:   %Self.as_type.loc15_19.1 => constants.%Ginger
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl.1(constants.%Goat.facet) {
// CHECK:STDOUT:   %G.loc18_14.2 => constants.%Goat.facet
// CHECK:STDOUT:   %G.patt.loc18_14.2 => constants.%Goat.facet
// CHECK:STDOUT:   %G.as_type.loc18_24.2 => constants.%Ginger
// CHECK:STDOUT:   %impl_witness => constants.%impl_witness.e6c
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %Eat.type => constants.%Eat.type.209
// CHECK:STDOUT:   %Eat => constants.%Eat.424
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Eat.2(constants.%Goat.facet) {
// CHECK:STDOUT:   %G => constants.%Goat.facet
// CHECK:STDOUT:   %G.as_type => constants.%Ginger
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete => constants.%complete_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
