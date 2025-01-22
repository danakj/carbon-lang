// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// AUTOUPDATE
// TIP: To test this file alone, run:
// TIP:   bazel test //toolchain/testing:file_test --test_arg=--file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/convert_facet_value_to_blanket_impl.carbon
// TIP: To dump output, run:
// TIP:   bazel run //toolchain/testing:file_test -- --dump_output --file_tests=toolchain/check/testdata/builtin_conversions/no_prelude/convert_facet_value_to_blanket_impl.carbon

interface Eats {}
interface Goat {}

impl forall [G:! Goat] G as Eats {}

fn FeedGoat[T:! Eats](e: T) {}

fn HandleGoat[T:! Goat](g: T) { FeedGoat(g); }

// CHECK:STDOUT: --- convert_facet_value_to_blanket_impl.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Eats.type: type = facet_type <@Eats> [template]
// CHECK:STDOUT:   %Self.1b5: %Eats.type = bind_symbolic_name Self, 0 [symbolic]
// CHECK:STDOUT:   %Goat.type: type = facet_type <@Goat> [template]
// CHECK:STDOUT:   %Self.092: %Goat.type = bind_symbolic_name Self, 0 [symbolic]
// CHECK:STDOUT:   %G: %Goat.type = bind_symbolic_name G, 0 [symbolic]
// CHECK:STDOUT:   %G.patt: %Goat.type = symbolic_binding_pattern G, 0 [symbolic]
// CHECK:STDOUT:   %G.as_type: type = facet_access_type %G [symbolic]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [template]
// CHECK:STDOUT:   %impl_witness.f2ee9f.1: <witness> = impl_witness (), @impl(%G) [symbolic]
// CHECK:STDOUT:   %T.1b5: %Eats.type = bind_symbolic_name T, 0 [symbolic]
// CHECK:STDOUT:   %T.patt.6be: %Eats.type = symbolic_binding_pattern T, 0 [symbolic]
// CHECK:STDOUT:   %T.as_type.27d: type = facet_access_type %T.1b5 [symbolic]
// CHECK:STDOUT:   %FeedGoat.type: type = fn_type @FeedGoat [template]
// CHECK:STDOUT:   %FeedGoat: %FeedGoat.type = struct_value () [template]
// CHECK:STDOUT:   %require_complete.c75: <witness> = require_complete_type %T.as_type.27d [symbolic]
// CHECK:STDOUT:   %T.092: %Goat.type = bind_symbolic_name T, 0 [symbolic]
// CHECK:STDOUT:   %T.patt.615: %Goat.type = symbolic_binding_pattern T, 0 [symbolic]
// CHECK:STDOUT:   %T.as_type.c35: type = facet_access_type %T.092 [symbolic]
// CHECK:STDOUT:   %HandleGoat.type: type = fn_type @HandleGoat [template]
// CHECK:STDOUT:   %HandleGoat: %HandleGoat.type = struct_value () [template]
// CHECK:STDOUT:   %require_complete.e21: <witness> = require_complete_type %T.as_type.c35 [symbolic]
// CHECK:STDOUT:   %impl_witness.f2ee9f.2: <witness> = impl_witness (), @impl(%T.092) [symbolic]
// CHECK:STDOUT:   %Eats.facet: %Eats.type = facet_value %T.as_type.c35, %impl_witness.f2ee9f.2 [symbolic]
// CHECK:STDOUT:   %FeedGoat.specific_fn: <specific function> = specific_function %FeedGoat, @FeedGoat(%Eats.facet) [symbolic]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: file {
// CHECK:STDOUT:   package: <namespace> = namespace [template] {
// CHECK:STDOUT:     .Eats = %Eats.decl
// CHECK:STDOUT:     .Goat = %Goat.decl
// CHECK:STDOUT:     .FeedGoat = %FeedGoat.decl
// CHECK:STDOUT:     .HandleGoat = %HandleGoat.decl
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Eats.decl: type = interface_decl @Eats [template = constants.%Eats.type] {} {}
// CHECK:STDOUT:   %Goat.decl: type = interface_decl @Goat [template = constants.%Goat.type] {} {}
// CHECK:STDOUT:   impl_decl @impl [template] {
// CHECK:STDOUT:     %G.patt.loc14_14.1: %Goat.type = symbolic_binding_pattern G, 0 [symbolic = %G.patt.loc14_14.2 (constants.%G.patt)]
// CHECK:STDOUT:     %G.param_patt: %Goat.type = value_param_pattern %G.patt.loc14_14.1, runtime_param<none> [symbolic = %G.patt.loc14_14.2 (constants.%G.patt)]
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %G.ref: %Goat.type = name_ref G, %G.loc14_14.1 [symbolic = %G.loc14_14.2 (constants.%G)]
// CHECK:STDOUT:     %G.as_type.loc14_24.1: type = facet_access_type %G.ref [symbolic = %G.as_type.loc14_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:     %.loc14: type = converted %G.ref, %G.as_type.loc14_24.1 [symbolic = %G.as_type.loc14_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:     %Eats.ref: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:     %G.param: %Goat.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:     %G.loc14_14.1: %Goat.type = bind_symbolic_name G, 0, %G.param [symbolic = %G.loc14_14.2 (constants.%G)]
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness (), @impl(constants.%G) [symbolic = @impl.%impl_witness (constants.%impl_witness.f2ee9f.1)]
// CHECK:STDOUT:   %FeedGoat.decl: %FeedGoat.type = fn_decl @FeedGoat [template = constants.%FeedGoat] {
// CHECK:STDOUT:     %T.patt.loc16_13.1: %Eats.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc16_13.2 (constants.%T.patt.6be)]
// CHECK:STDOUT:     %T.param_patt: %Eats.type = value_param_pattern %T.patt.loc16_13.1, runtime_param<none> [symbolic = %T.patt.loc16_13.2 (constants.%T.patt.6be)]
// CHECK:STDOUT:     %e.patt: @FeedGoat.%T.as_type.loc16_26.2 (%T.as_type.27d) = binding_pattern e
// CHECK:STDOUT:     %e.param_patt: @FeedGoat.%T.as_type.loc16_26.2 (%T.as_type.27d) = value_param_pattern %e.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %T.param: %Eats.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Eats.ref: type = name_ref Eats, file.%Eats.decl [template = constants.%Eats.type]
// CHECK:STDOUT:     %T.loc16_13.1: %Eats.type = bind_symbolic_name T, 0, %T.param [symbolic = %T.loc16_13.2 (constants.%T.1b5)]
// CHECK:STDOUT:     %e.param: @FeedGoat.%T.as_type.loc16_26.2 (%T.as_type.27d) = value_param runtime_param0
// CHECK:STDOUT:     %.loc16_26.1: type = splice_block %.loc16_26.2 [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type.27d)] {
// CHECK:STDOUT:       %T.ref: %Eats.type = name_ref T, %T.loc16_13.1 [symbolic = %T.loc16_13.2 (constants.%T.1b5)]
// CHECK:STDOUT:       %T.as_type.loc16_26.1: type = facet_access_type %T.ref [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type.27d)]
// CHECK:STDOUT:       %.loc16_26.2: type = converted %T.ref, %T.as_type.loc16_26.1 [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type.27d)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %e: @FeedGoat.%T.as_type.loc16_26.2 (%T.as_type.27d) = bind_name e, %e.param
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %HandleGoat.decl: %HandleGoat.type = fn_decl @HandleGoat [template = constants.%HandleGoat] {
// CHECK:STDOUT:     %T.patt.loc18_15.1: %Goat.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc18_15.2 (constants.%T.patt.615)]
// CHECK:STDOUT:     %T.param_patt: %Goat.type = value_param_pattern %T.patt.loc18_15.1, runtime_param<none> [symbolic = %T.patt.loc18_15.2 (constants.%T.patt.615)]
// CHECK:STDOUT:     %g.patt: @HandleGoat.%T.as_type.loc18_28.2 (%T.as_type.c35) = binding_pattern g
// CHECK:STDOUT:     %g.param_patt: @HandleGoat.%T.as_type.loc18_28.2 (%T.as_type.c35) = value_param_pattern %g.patt, runtime_param0
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %T.param: %Goat.type = value_param runtime_param<none>
// CHECK:STDOUT:     %Goat.ref: type = name_ref Goat, file.%Goat.decl [template = constants.%Goat.type]
// CHECK:STDOUT:     %T.loc18_15.1: %Goat.type = bind_symbolic_name T, 0, %T.param [symbolic = %T.loc18_15.2 (constants.%T.092)]
// CHECK:STDOUT:     %g.param: @HandleGoat.%T.as_type.loc18_28.2 (%T.as_type.c35) = value_param runtime_param0
// CHECK:STDOUT:     %.loc18_28.1: type = splice_block %.loc18_28.2 [symbolic = %T.as_type.loc18_28.2 (constants.%T.as_type.c35)] {
// CHECK:STDOUT:       %T.ref: %Goat.type = name_ref T, %T.loc18_15.1 [symbolic = %T.loc18_15.2 (constants.%T.092)]
// CHECK:STDOUT:       %T.as_type.loc18_28.1: type = facet_access_type %T.ref [symbolic = %T.as_type.loc18_28.2 (constants.%T.as_type.c35)]
// CHECK:STDOUT:       %.loc18_28.2: type = converted %T.ref, %T.as_type.loc18_28.1 [symbolic = %T.as_type.loc18_28.2 (constants.%T.as_type.c35)]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %g: @HandleGoat.%T.as_type.loc18_28.2 (%T.as_type.c35) = bind_name g, %g.param
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: interface @Eats {
// CHECK:STDOUT:   %Self: %Eats.type = bind_symbolic_name Self, 0 [symbolic = constants.%Self.1b5]
// CHECK:STDOUT:
// CHECK:STDOUT: !members:
// CHECK:STDOUT:   .Self = %Self
// CHECK:STDOUT:   witness = ()
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
// CHECK:STDOUT: generic impl @impl(%G.loc14_14.1: %Goat.type) {
// CHECK:STDOUT:   %G.loc14_14.2: %Goat.type = bind_symbolic_name G, 0 [symbolic = %G.loc14_14.2 (constants.%G)]
// CHECK:STDOUT:   %G.patt.loc14_14.2: %Goat.type = symbolic_binding_pattern G, 0 [symbolic = %G.patt.loc14_14.2 (constants.%G.patt)]
// CHECK:STDOUT:   %G.as_type.loc14_24.2: type = facet_access_type %G.loc14_14.2 [symbolic = %G.as_type.loc14_24.2 (constants.%G.as_type)]
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness (), @impl(%G.loc14_14.2) [symbolic = %impl_witness (constants.%impl_witness.f2ee9f.1)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:
// CHECK:STDOUT:   impl: %.loc14 as %Eats.ref {
// CHECK:STDOUT:   !members:
// CHECK:STDOUT:     witness = file.%impl_witness
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @FeedGoat(%T.loc16_13.1: %Eats.type) {
// CHECK:STDOUT:   %T.loc16_13.2: %Eats.type = bind_symbolic_name T, 0 [symbolic = %T.loc16_13.2 (constants.%T.1b5)]
// CHECK:STDOUT:   %T.patt.loc16_13.2: %Eats.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc16_13.2 (constants.%T.patt.6be)]
// CHECK:STDOUT:   %T.as_type.loc16_26.2: type = facet_access_type %T.loc16_13.2 [symbolic = %T.as_type.loc16_26.2 (constants.%T.as_type.27d)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type @FeedGoat.%T.as_type.loc16_26.2 (%T.as_type.27d) [symbolic = %require_complete (constants.%require_complete.c75)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%T.param_patt: %Eats.type](%e.param_patt: @FeedGoat.%T.as_type.loc16_26.2 (%T.as_type.27d)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @HandleGoat(%T.loc18_15.1: %Goat.type) {
// CHECK:STDOUT:   %T.loc18_15.2: %Goat.type = bind_symbolic_name T, 0 [symbolic = %T.loc18_15.2 (constants.%T.092)]
// CHECK:STDOUT:   %T.patt.loc18_15.2: %Goat.type = symbolic_binding_pattern T, 0 [symbolic = %T.patt.loc18_15.2 (constants.%T.patt.615)]
// CHECK:STDOUT:   %T.as_type.loc18_28.2: type = facet_access_type %T.loc18_15.2 [symbolic = %T.as_type.loc18_28.2 (constants.%T.as_type.c35)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete: <witness> = require_complete_type @HandleGoat.%T.as_type.loc18_28.2 (%T.as_type.c35) [symbolic = %require_complete (constants.%require_complete.e21)]
// CHECK:STDOUT:   %impl_witness: <witness> = impl_witness (), @impl(%T.loc18_15.2) [symbolic = %impl_witness (constants.%impl_witness.f2ee9f.2)]
// CHECK:STDOUT:   %Eats.facet.loc18_43.3: %Eats.type = facet_value %T.as_type.loc18_28.2, %impl_witness [symbolic = %Eats.facet.loc18_43.3 (constants.%Eats.facet)]
// CHECK:STDOUT:   %FeedGoat.specific_fn.loc18_33.2: <specific function> = specific_function constants.%FeedGoat, @FeedGoat(%Eats.facet.loc18_43.3) [symbolic = %FeedGoat.specific_fn.loc18_33.2 (constants.%FeedGoat.specific_fn)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn[%T.param_patt: %Goat.type](%g.param_patt: @HandleGoat.%T.as_type.loc18_28.2 (%T.as_type.c35)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     %FeedGoat.ref: %FeedGoat.type = name_ref FeedGoat, file.%FeedGoat.decl [template = constants.%FeedGoat]
// CHECK:STDOUT:     %g.ref: @HandleGoat.%T.as_type.loc18_28.2 (%T.as_type.c35) = name_ref g, %g
// CHECK:STDOUT:     %.loc18_43.1: %Goat.type = converted constants.%T.as_type.c35, constants.%T.092 [symbolic = %T.loc18_15.2 (constants.%T.092)]
// CHECK:STDOUT:     %Eats.facet.loc18_43.1: %Eats.type = facet_value constants.%T.as_type.c35, constants.%impl_witness.f2ee9f.2 [symbolic = %Eats.facet.loc18_43.3 (constants.%Eats.facet)]
// CHECK:STDOUT:     %.loc18_43.2: %Eats.type = converted constants.%T.as_type.c35, %Eats.facet.loc18_43.1 [symbolic = %Eats.facet.loc18_43.3 (constants.%Eats.facet)]
// CHECK:STDOUT:     %.loc18_43.3: %Goat.type = converted constants.%T.as_type.c35, constants.%T.092 [symbolic = %T.loc18_15.2 (constants.%T.092)]
// CHECK:STDOUT:     %Eats.facet.loc18_43.2: %Eats.type = facet_value constants.%T.as_type.c35, constants.%impl_witness.f2ee9f.2 [symbolic = %Eats.facet.loc18_43.3 (constants.%Eats.facet)]
// CHECK:STDOUT:     %.loc18_43.4: %Eats.type = converted constants.%T.as_type.c35, %Eats.facet.loc18_43.2 [symbolic = %Eats.facet.loc18_43.3 (constants.%Eats.facet)]
// CHECK:STDOUT:     %FeedGoat.specific_fn.loc18_33.1: <specific function> = specific_function %FeedGoat.ref, @FeedGoat(constants.%Eats.facet) [symbolic = %FeedGoat.specific_fn.loc18_33.2 (constants.%FeedGoat.specific_fn)]
// CHECK:STDOUT:     %FeedGoat.call: init %empty_tuple.type = call %FeedGoat.specific_fn.loc18_33.1(%g.ref)
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl(constants.%G) {
// CHECK:STDOUT:   %G.loc14_14.2 => constants.%G
// CHECK:STDOUT:   %G.patt.loc14_14.2 => constants.%G
// CHECK:STDOUT:   %G.as_type.loc14_24.2 => constants.%G.as_type
// CHECK:STDOUT:   %impl_witness => constants.%impl_witness.f2ee9f.1
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl(%G.loc14_14.2) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @FeedGoat(constants.%T.1b5) {
// CHECK:STDOUT:   %T.loc16_13.2 => constants.%T.1b5
// CHECK:STDOUT:   %T.patt.loc16_13.2 => constants.%T.1b5
// CHECK:STDOUT:   %T.as_type.loc16_26.2 => constants.%T.as_type.27d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @HandleGoat(constants.%T.092) {
// CHECK:STDOUT:   %T.loc18_15.2 => constants.%T.092
// CHECK:STDOUT:   %T.patt.loc18_15.2 => constants.%T.092
// CHECK:STDOUT:   %T.as_type.loc18_28.2 => constants.%T.as_type.c35
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl(constants.%T.092) {
// CHECK:STDOUT:   %G.loc14_14.2 => constants.%T.092
// CHECK:STDOUT:   %G.patt.loc14_14.2 => constants.%T.092
// CHECK:STDOUT:   %G.as_type.loc14_24.2 => constants.%T.as_type.c35
// CHECK:STDOUT:   %impl_witness => constants.%impl_witness.f2ee9f.2
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @FeedGoat(constants.%Eats.facet) {
// CHECK:STDOUT:   %T.loc16_13.2 => constants.%Eats.facet
// CHECK:STDOUT:   %T.patt.loc16_13.2 => constants.%Eats.facet
// CHECK:STDOUT:   %T.as_type.loc16_26.2 => constants.%T.as_type.c35
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete => constants.%require_complete.e21
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @impl(@HandleGoat.%T.loc18_15.2) {}
// CHECK:STDOUT:
// CHECK:STDOUT: specific @FeedGoat(@HandleGoat.%Eats.facet.loc18_43.3) {}
// CHECK:STDOUT:
