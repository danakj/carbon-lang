// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// AUTOUPDATE
// TIP: To test this file alone, run:
// TIP:   bazel test //toolchain/testing:file_test --test_arg=--file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/convert_class_value_to_facet_value.carbon
// TIP: To dump output, run:
// TIP:   bazel run //toolchain/testing:file_test -- --dump_output --file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/convert_class_value_to_facet_value.carbon

interface Goat {}

class Ginger {}
impl Ginger as Goat {}

fn WalkGoat[T:! Goat](g: T) {}

fn F() {
  WalkGoat({} as Ginger);
}

// CHECK:STDOUT: --- convert_class_value_to_facet_value.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Goat.type: type = facet_type <@Goat> [template]
// CHECK:STDOUT:   %Self: %Goat.type = bind_symbolic_name Self, 0 [symbolic]
// CHECK:STDOUT:   %Ginger: type = class_type @Ginger [template]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [template]
// CHECK:STDOUT:   %complete_type: <witness> = complete_type_witness %empty_struct_type [template]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [template]
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness () [template]
// CHECK:STDOUT:   %T: %Goat.type = bind_symbolic_name T, 0 [symbolic]
// CHECK:STDOUT:   %T.patt: %Goat.type = symbolic_binding_pattern T, 0 [symbolic]
// CHECK:STDOUT:   %T.as_type: type = facet_access_type %T [symbolic]
// CHECK:STDOUT:   %WalkGoat.type: type = fn_type @WalkGoat [template]
// CHECK:STDOUT:   %WalkGoat: %WalkGoat.type = struct_value () [template]
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type %T.as_type [symbolic]
// CHECK:STDOUT:   %F.type: type = fn_type @F [template]
// CHECK:STDOUT:   %F: %F.type = struct_value () [template]
// CHECK:STDOUT:   %Ginger.val: %Ginger = struct_value () [template]
// CHECK:STDOUT:   %Goat.facet: %Goat.type = facet_value %Ginger, %impl_witness [template]
// CHECK:STDOUT:   %WalkGoat.specific_fn: <specific function> = specific_function %WalkGoat, @WalkGoat(%Goat.facet) [template]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: file {
// CHECK:STDOUT:   package: <namespace> = namespace [template] {
// CHECK:STDOUT:     .Goat = %Goat.decl
// CHECK:STDOUT:     .Ginger = %Ginger.decl
// CHECK:STDOUT:     .WalkGoat = %WalkGoat.decl
// CHECK:STDOUT:     .F = %F.decl
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Goat.decl: type = interface_decl @Goat [template = constants.%Goat.type] {} {}
// CHECK:STDOUT:   %Ginger.decl: type = class_decl @Ginger [template = constants.%Ginger] {} {}
// CHECK:STDOUT:   impl_decl @impl [template] {} {
// CHECK:STDOUT:     %Ginger.ref: type = name_ref Ginger, file.%Ginger.decl [template = constants.%Ginger]
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness () [template = constants.%impl_witness]
// CHECK:STDOUT:   %WalkGoat.decl: %WalkGoat.type = fn_decl @WalkGoat [template = constants.%WalkGoat] {
// CHECK:STDOUT:     %T.patt.loc16_13.1: %Goat.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc16_13.2 (constants.%T.patt)]
// CHECK:STDOUT:     %T.param_patt: %Goat.type = value_param_pattern %T.patt.loc16_13.1, runtime_param<none> [symbolic = %T.patt.loc16_13.2 (constants.%T.patt)]
// CHECK:STDOUT:     %g.patt: @WalkGoat.%T.as_type.loc16_26.2 (%T.as_type) = binding_pattern g
// CHECK:STDOUT:     %g.param_patt: @WalkGoat.%T.as_type.loc16_26.2 (%T.as_type) = value_param_pattern %g.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %T.param: %Goat.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:     %T.loc16_13.1: %Goat.type = bind_symbolic_name T, 0, %T.param [symbolic = %T.loc16_13.2 (constants.%T)]
// CHECK:STDOUT:     %g.param: @WalkGoat.%T.as_type.loc16_26.2 (%T.as_type) = value_param runtime_param0
// CHECK:STDOUT:     %.loc16_26.1: type = splice_block %.loc16_26.2 [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type)] {
// CHECK:STDOUT:       %T.ref: %Goat.type = name_ref T, %T.loc16_13.1 [symbolic = %T.loc16_13.2 (constants.%T)]
// CHECK:STDOUT:       %T.as_type.loc16_26.1: type = facet_access_type %T.ref [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type)]
// CHECK:STDOUT:       %.loc16_26.2: type = converted %T.ref, %T.as_type.loc16_26.1 [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %g: @WalkGoat.%T.as_type.loc16_26.2 (%T.as_type) = bind_name g, %g.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %F.decl: %F.type = fn_decl @F [template = constants.%F] {} {}
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: interface @Goat {
// CHECK:STDOUT:   %Self: %Goat.type = bind_symbolic_name Self, 0 [symbolic = constants.%Self]
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Self = %Self
// CHECK:STDOUT:   witness = ()
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: impl @impl: %Ginger.ref as %Goat.ref {
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   witness = file.%impl_witness
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
// CHECK:STDOUT: generic fn @WalkGoat(%T.loc16_13.1: %Goat.type) {
// CHECK:STDOUT:   %T.loc16_13.2: %Goat.type = bind_symbolic_name T, 0 [symbolic = %T.loc16_13.2 (constants.%T)]
// CHECK:STDOUT:   %T.patt.loc16_13.2: %Goat.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc16_13.2 (constants.%T.patt)]
// CHECK:STDOUT:   %T.as_type.loc16_26.2: type = facet_access_type %T.loc16_13.2 [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type @WalkGoat.%T.as_type.loc16_26.2 (%T.as_type) [symbolic = %require_complete (constants.%require_complete)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%T.param_patt: %Goat.type](%g.param_patt: @WalkGoat.%T.as_type.loc16_26.2 (%T.as_type)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @F() {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   %WalkGoat.ref: %WalkGoat.type = name_ref WalkGoat, file.%WalkGoat.decl [template = constants.%WalkGoat]
// CHECK:STDOUT:   %.loc19_13.1: %empty_struct_type = struct_literal ()
// CHECK:STDOUT:   %Ginger.ref: type = name_ref Ginger, file.%Ginger.decl [template = constants.%Ginger]
// CHECK:STDOUT:   %.loc19_13.2: ref %Ginger = temporary_storage
// CHECK:STDOUT:   %.loc19_13.3: init %Ginger = class_init (), %.loc19_13.2 [template = constants.%Ginger.val]
// CHECK:STDOUT:   %.loc19_13.4: ref %Ginger = temporary %.loc19_13.2, %.loc19_13.3
// CHECK:STDOUT:   %.loc19_15.1: ref %Ginger = converted %.loc19_13.1, %.loc19_13.4
// CHECK:STDOUT:   %Goat.facet.loc19_24.1: %Goat.type = facet_value constants.%Ginger, constants.%impl_witness [template = constants.%Goat.facet]
// CHECK:STDOUT:   %.loc19_24.1: %Goat.type = converted constants.%Ginger, %Goat.facet.loc19_24.1 [template = constants.%Goat.facet]
// CHECK:STDOUT:   %Goat.facet.loc19_24.2: %Goat.type = facet_value constants.%Ginger, constants.%impl_witness [template = constants.%Goat.facet]
// CHECK:STDOUT:   %.loc19_24.2: %Goat.type = converted constants.%Ginger, %Goat.facet.loc19_24.2 [template = constants.%Goat.facet]
// CHECK:STDOUT:   %WalkGoat.specific_fn: <specific function> = specific_function %WalkGoat.ref, @WalkGoat(constants.%Goat.facet) [template = constants.%WalkGoat.specific_fn]
// CHECK:STDOUT:   %.loc19_15.2: %Ginger = bind_value %.loc19_15.1
// CHECK:STDOUT:   %WalkGoat.call: init %empty_tuple.type = call %WalkGoat.specific_fn(%.loc19_15.2)
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @WalkGoat(constants.%T) {
// CHECK:STDOUT:   %T.loc16_13.2 => constants.%T
// CHECK:STDOUT:   %T.patt.loc16_13.2 => constants.%T
// CHECK:STDOUT:   %T.as_type.loc16_26.2 => constants.%T.as_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @WalkGoat(constants.%Goat.facet) {
// CHECK:STDOUT:   %T.loc16_13.2 => constants.%Goat.facet
// CHECK:STDOUT:   %T.patt.loc16_13.2 => constants.%Goat.facet
// CHECK:STDOUT:   %T.as_type.loc16_26.2 => constants.%Ginger
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete => constants.%complete_type
// CHECK:STDOUT: }
// CHECK:STDOUT:
