// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// INCLUDE-FILE: toolchain/testing/testdata/min_prelude/primitives.carbon
//
// AUTOUPDATE
// TIP: To test this file alone, run:
// TIP:   bazel test //toolchain/testing:file_test --test_arg=--file_tests=toolchain/check/testdata/where_expr/dot_self_index.carbon
// TIP: To dump output, run:
// TIP:   bazel run //toolchain/testing:file_test -- --dump_output --file_tests=toolchain/check/testdata/where_expr/dot_self_index.carbon

interface Empty(W:! type) {
  let A:! type;
}

// T has index 0
// .Self has index invalid, not 1
// V has index 1, does not match .Self
//@dump-sem-ir-begin
fn H(T:! type, unused U: Empty(T) where .A = T*, unused V:! type) {}
//@dump-sem-ir-end

fn G(U: Empty(i32) where .A = i32*) {
  H(i32, U, bool);
}

// CHECK:STDOUT: --- dot_self_index.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %type: type = facet_type <type> [concrete]
// CHECK:STDOUT:   %.Self.0.e0b: %type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %pattern_type.98f: type = pattern_type type [concrete]
// CHECK:STDOUT:   %Empty.type.c52: type = generic_interface_type @Empty [concrete]
// CHECK:STDOUT:   %Empty.generic: %Empty.type.c52 = struct_value () [concrete]
// CHECK:STDOUT:   %T: type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Empty.type.95d624.2: type = facet_type <@Empty, @Empty(%T)> [symbolic]
// CHECK:STDOUT:   %.Self.0.913: %Empty.type.95d624.2 = symbolic_binding .Self.0 [symbolic]
// CHECK:STDOUT:   %Empty.assoc_type.c44b55.2: type = assoc_entity_type @Empty, @Empty(%T) [symbolic]
// CHECK:STDOUT:   %assoc0.3a7cb1.2: %Empty.assoc_type.c44b55.2 = assoc_entity element0, @Empty.WithSelf.%A [symbolic]
// CHECK:STDOUT:   %require_complete.a43: <witness> = require_complete_type %Empty.type.95d624.2 [symbolic]
// CHECK:STDOUT:   %.Self.0.as_type.a95: type = facet_access_type %.Self.0.913 [symbolic]
// CHECK:STDOUT:   %Empty.lookup_impl_witness.67b: <witness> = lookup_impl_witness %.Self.0.913, @Empty, @Empty(%T) [symbolic]
// CHECK:STDOUT:   %impl.elem0.d8a: type = impl_witness_access %Empty.lookup_impl_witness.67b, element0 [symbolic]
// CHECK:STDOUT:   %ptr.e8f: type = ptr_type %T [symbolic]
// CHECK:STDOUT:   %Empty_where.type.696: type = facet_type <@Empty, @Empty(%T) where %impl.elem0.d8a = %ptr.e8f> [symbolic]
// CHECK:STDOUT:   %pattern_type.a0f: type = pattern_type %Empty_where.type.696 [symbolic]
// CHECK:STDOUT:   %V: type = symbolic_binding V, 1 [symbolic]
// CHECK:STDOUT:   %H.type: type = fn_type @H [concrete]
// CHECK:STDOUT:   %H: %H.type = struct_value () [concrete]
// CHECK:STDOUT:   %require_complete.e98: <witness> = require_complete_type %Empty_where.type.696 [symbolic]
// CHECK:STDOUT:   %int_32: Core.IntLiteral = int_value 32 [concrete]
// CHECK:STDOUT:   %i32: type = class_type @Int, @Int(%int_32) [concrete]
// CHECK:STDOUT:   %Empty.type.39c: type = facet_type <@Empty, @Empty(%i32)> [concrete]
// CHECK:STDOUT:   %.Self.0.98b: %Empty.type.39c = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Empty.assoc_type.22b: type = assoc_entity_type @Empty, @Empty(%i32) [concrete]
// CHECK:STDOUT:   %assoc0.023: %Empty.assoc_type.22b = assoc_entity element0, @Empty.WithSelf.%A [concrete]
// CHECK:STDOUT:   %.Self.0.as_type.15e: type = facet_access_type %.Self.0.98b [symbolic_self]
// CHECK:STDOUT:   %Empty.lookup_impl_witness.4f6: <witness> = lookup_impl_witness %.Self.0.98b, @Empty, @Empty(%i32) [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.f25: type = impl_witness_access %Empty.lookup_impl_witness.4f6, element0 [symbolic_self]
// CHECK:STDOUT:   %ptr.d08: type = ptr_type %i32 [concrete]
// CHECK:STDOUT:   %Empty_where.type.944: type = facet_type <@Empty, @Empty(%i32) where %impl.elem0.f25 = %ptr.d08> [concrete]
// CHECK:STDOUT:   %pattern_type.12c: type = pattern_type %Empty_where.type.944 [concrete]
// CHECK:STDOUT:   %complete_type.c56: <witness> = complete_type_witness %Empty.type.39c [concrete]
// CHECK:STDOUT:   %complete_type.c21: <witness> = complete_type_witness %Empty_where.type.944 [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: file {
// CHECK:STDOUT:   %H.decl: %H.type = fn_decl @H [concrete = constants.%H] {
// CHECK:STDOUT:     %T.patt: %pattern_type.98f = symbolic_binding_pattern T, 0 [concrete]
// CHECK:STDOUT:     %U.param_patt: @H.%pattern_type (%pattern_type.a0f) = value_param_pattern [concrete]
// CHECK:STDOUT:     %U.patt: @H.%pattern_type (%pattern_type.a0f) = at_binding_pattern U, %U.param_patt [concrete]
// CHECK:STDOUT:     %V.patt: %pattern_type.98f = symbolic_binding_pattern V, 1 [concrete]
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     %.loc21_10.1: type = splice_block %.loc21_10.2 [concrete = type] {
// CHECK:STDOUT:       %.Self.0.loc21_7: %type = symbolic_binding .Self.0 [symbolic_self = constants.%.Self.0.e0b]
// CHECK:STDOUT:       %.loc21_10.2: type = type_literal type [concrete = type]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %T.loc21_7.2: type = symbolic_binding T, 0 [symbolic = %T.loc21_7.1 (constants.%T)]
// CHECK:STDOUT:     %U.param: @H.%Empty_where.type (%Empty_where.type.696) = value_param call_param0
// CHECK:STDOUT:     %.loc21_35.1: type = splice_block %.loc21_35.2 [symbolic = %Empty_where.type (constants.%Empty_where.type.696)] {
// CHECK:STDOUT:       %Empty.ref: %Empty.type.c52 = name_ref Empty, file.%Empty.decl [concrete = constants.%Empty.generic]
// CHECK:STDOUT:       %T.ref.loc21_32: type = name_ref T, %T.loc21_7.2 [symbolic = %T.loc21_7.1 (constants.%T)]
// CHECK:STDOUT:       %Empty.type.loc21_33.2: type = facet_type <@Empty, @Empty(constants.%T)> [symbolic = %Empty.type.loc21_33.1 (constants.%Empty.type.95d624.2)]
// CHECK:STDOUT:       %.Self.0.loc21_35.2: @H.%Empty.type.loc21_33.1 (%Empty.type.95d624.2) = symbolic_binding .Self.0 [symbolic = %.Self.0.loc21_35.1 (constants.%.Self.0.913)]
// CHECK:STDOUT:       %.Self.ref: @H.%Empty.type.loc21_33.1 (%Empty.type.95d624.2) = name_ref .Self, %.Self.0.loc21_35.2 [symbolic = %.Self.0.loc21_35.1 (constants.%.Self.0.913)]
// CHECK:STDOUT:       %.Self.as_type: type = facet_access_type %.Self.ref [symbolic = %.Self.0.as_type (constants.%.Self.0.as_type.a95)]
// CHECK:STDOUT:       %.loc21_41.1: type = converted %.Self.ref, %.Self.as_type [symbolic = %.Self.0.as_type (constants.%.Self.0.as_type.a95)]
// CHECK:STDOUT:       %.loc21_41.2: @H.%Empty.assoc_type (%Empty.assoc_type.c44b55.2) = specific_constant @A.%assoc0, @Empty.WithSelf(constants.%T, constants.%.Self.0.913) [symbolic = %assoc0 (constants.%assoc0.3a7cb1.2)]
// CHECK:STDOUT:       %A.ref: @H.%Empty.assoc_type (%Empty.assoc_type.c44b55.2) = name_ref A, %.loc21_41.2 [symbolic = %assoc0 (constants.%assoc0.3a7cb1.2)]
// CHECK:STDOUT:       %impl.elem0.loc21_41.2: type = impl_witness_access constants.%Empty.lookup_impl_witness.67b, element0 [symbolic = %impl.elem0.loc21_41.1 (constants.%impl.elem0.d8a)]
// CHECK:STDOUT:       %T.ref.loc21_46: type = name_ref T, %T.loc21_7.2 [symbolic = %T.loc21_7.1 (constants.%T)]
// CHECK:STDOUT:       %ptr.loc21_47.2: type = ptr_type %T.ref.loc21_46 [symbolic = %ptr.loc21_47.1 (constants.%ptr.e8f)]
// CHECK:STDOUT:       %.loc21_35.2: type = where_expr [symbolic = %Empty_where.type (constants.%Empty_where.type.696)] {
// CHECK:STDOUT:         requirement_base_facet_type %Empty.type.loc21_33.2
// CHECK:STDOUT:         requirement_rewrite %impl.elem0.loc21_41.2, %ptr.loc21_47.2
// CHECK:STDOUT:       }
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %U: @H.%Empty_where.type (%Empty_where.type.696) = value_binding U, %U.param
// CHECK:STDOUT:     %.loc21_61.1: type = splice_block %.loc21_61.2 [concrete = type] {
// CHECK:STDOUT:       %.Self.0.loc21_58: %type = symbolic_binding .Self.0 [symbolic_self = constants.%.Self.0.e0b]
// CHECK:STDOUT:       %.loc21_61.2: type = type_literal type [concrete = type]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %V.loc21_58.2: type = symbolic_binding V, 1 [symbolic = %V.loc21_58.1 (constants.%V)]
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @H(%T.loc21_7.2: type, %V.loc21_58.2: type) {
// CHECK:STDOUT:   %T.loc21_7.1: type = symbolic_binding T, 0 [symbolic = %T.loc21_7.1 (constants.%T)]
// CHECK:STDOUT:   %Empty.type.loc21_33.1: type = facet_type <@Empty, @Empty(%T.loc21_7.1)> [symbolic = %Empty.type.loc21_33.1 (constants.%Empty.type.95d624.2)]
// CHECK:STDOUT:   %.Self.0.loc21_35.1: @H.%Empty.type.loc21_33.1 (%Empty.type.95d624.2) = symbolic_binding .Self.0 [symbolic = %.Self.0.loc21_35.1 (constants.%.Self.0.913)]
// CHECK:STDOUT:   %require_complete.loc21_41: <witness> = require_complete_type %Empty.type.loc21_33.1 [symbolic = %require_complete.loc21_41 (constants.%require_complete.a43)]
// CHECK:STDOUT:   %.Self.0.as_type: type = facet_access_type %.Self.0.loc21_35.1 [symbolic = %.Self.0.as_type (constants.%.Self.0.as_type.a95)]
// CHECK:STDOUT:   %Empty.assoc_type: type = assoc_entity_type @Empty, @Empty(%T.loc21_7.1) [symbolic = %Empty.assoc_type (constants.%Empty.assoc_type.c44b55.2)]
// CHECK:STDOUT:   %assoc0: @H.%Empty.assoc_type (%Empty.assoc_type.c44b55.2) = assoc_entity element0, @Empty.WithSelf.%A [symbolic = %assoc0 (constants.%assoc0.3a7cb1.2)]
// CHECK:STDOUT:   %Empty.lookup_impl_witness: <witness> = lookup_impl_witness %.Self.0.loc21_35.1, @Empty, @Empty(%T.loc21_7.1) [symbolic = %Empty.lookup_impl_witness (constants.%Empty.lookup_impl_witness.67b)]
// CHECK:STDOUT:   %impl.elem0.loc21_41.1: type = impl_witness_access %Empty.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc21_41.1 (constants.%impl.elem0.d8a)]
// CHECK:STDOUT:   %ptr.loc21_47.1: type = ptr_type %T.loc21_7.1 [symbolic = %ptr.loc21_47.1 (constants.%ptr.e8f)]
// CHECK:STDOUT:   %Empty_where.type: type = facet_type <@Empty, @Empty(%T.loc21_7.1) where %impl.elem0.loc21_41.1 = %ptr.loc21_47.1> [symbolic = %Empty_where.type (constants.%Empty_where.type.696)]
// CHECK:STDOUT:   %pattern_type: type = pattern_type %Empty_where.type [symbolic = %pattern_type (constants.%pattern_type.a0f)]
// CHECK:STDOUT:   %V.loc21_58.1: type = symbolic_binding V, 1 [symbolic = %V.loc21_58.1 (constants.%V)]
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc21_24: <witness> = require_complete_type %Empty_where.type [symbolic = %require_complete.loc21_24 (constants.%require_complete.e98)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%U.param: @H.%Empty_where.type (%Empty_where.type.696)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     return
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @H(constants.%T, constants.%V) {
// CHECK:STDOUT:   %T.loc21_7.1 => constants.%T
// CHECK:STDOUT:   %Empty.type.loc21_33.1 => constants.%Empty.type.95d624.2
// CHECK:STDOUT:   %.Self.0.loc21_35.1 => constants.%.Self.0.913
// CHECK:STDOUT:   %require_complete.loc21_41 => constants.%require_complete.a43
// CHECK:STDOUT:   %.Self.0.as_type => constants.%.Self.0.as_type.a95
// CHECK:STDOUT:   %Empty.assoc_type => constants.%Empty.assoc_type.c44b55.2
// CHECK:STDOUT:   %assoc0 => constants.%assoc0.3a7cb1.2
// CHECK:STDOUT:   %Empty.lookup_impl_witness => constants.%Empty.lookup_impl_witness.67b
// CHECK:STDOUT:   %impl.elem0.loc21_41.1 => constants.%impl.elem0.d8a
// CHECK:STDOUT:   %ptr.loc21_47.1 => constants.%ptr.e8f
// CHECK:STDOUT:   %Empty_where.type => constants.%Empty_where.type.696
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.a0f
// CHECK:STDOUT:   %V.loc21_58.1 => constants.%V
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @H(constants.%i32, bool) {
// CHECK:STDOUT:   %T.loc21_7.1 => constants.%i32
// CHECK:STDOUT:   %Empty.type.loc21_33.1 => constants.%Empty.type.39c
// CHECK:STDOUT:   %.Self.0.loc21_35.1 => constants.%.Self.0.98b
// CHECK:STDOUT:   %require_complete.loc21_41 => constants.%complete_type.c56
// CHECK:STDOUT:   %.Self.0.as_type => constants.%.Self.0.as_type.15e
// CHECK:STDOUT:   %Empty.assoc_type => constants.%Empty.assoc_type.22b
// CHECK:STDOUT:   %assoc0 => constants.%assoc0.023
// CHECK:STDOUT:   %Empty.lookup_impl_witness => constants.%Empty.lookup_impl_witness.4f6
// CHECK:STDOUT:   %impl.elem0.loc21_41.1 => constants.%impl.elem0.f25
// CHECK:STDOUT:   %ptr.loc21_47.1 => constants.%ptr.d08
// CHECK:STDOUT:   %Empty_where.type => constants.%Empty_where.type.944
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.12c
// CHECK:STDOUT:   %V.loc21_58.1 => bool
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc21_24 => constants.%complete_type.c21
// CHECK:STDOUT: }
// CHECK:STDOUT:
