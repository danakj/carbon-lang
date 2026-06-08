// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// INCLUDE-FILE: toolchain/testing/testdata/min_prelude/full.carbon
//
// EXTRA-ARGS: --clang-arg=-std=c++20
//
// AUTOUPDATE
// TIP: To test this file alone, run:
// TIP:   bazel test //toolchain/testing:file_test --test_arg=--file_tests=toolchain/check/testdata/interop/cpp/range_for.carbon
// TIP: To dump output, run:
// TIP:   bazel run //toolchain/testing:file_test -- --dump_output --file_tests=toolchain/check/testdata/interop/cpp/range_for.carbon

// --- methods_return_same_type.carbon

library "[[@TEST_NAME]]";

import Cpp inline '''c++
class MutableRange {
  struct Iterator {
    auto operator*() const -> int&;
    auto operator++() -> Iterator&;
    friend auto operator==(Iterator, Iterator) -> bool;
    friend auto operator!=(Iterator, Iterator) -> bool;
  };
public:
  auto begin() -> Iterator;
  auto end() -> Iterator;
};

class ConstRange {
  struct Iterator {
    auto operator*() const -> const int&;
    auto operator++() -> Iterator&;
    friend auto operator==(Iterator, Iterator) -> bool;
    friend auto operator!=(Iterator, Iterator) -> bool;
  };
public:
  auto begin() const -> Iterator;
  auto end() const -> Iterator;
};
''';

fn Test[R:! Core.Iterate where .ElementType = i32](r: R) {
  var sum: i32 = 0;

  //@dump-sem-ir-begin
  for (i: i32 in r) {
    sum += i;
  }
  //@dump-sem-ir-end
}

fn TestDriver(var m: Cpp.MutableRange, c: Cpp.ConstRange) {
  Test(m);
  Test(c);
}

// --- methods_return_different_types.carbon

library "[[@TEST_NAME]]";

import Cpp inline '''c++
struct ValueType {
  auto operator+=(const ValueType&) -> ValueType&;
};

class MutableRange {
  struct Iterator {
    auto operator*() const -> ValueType&;
    auto operator++() -> Iterator&;
  };

  struct Sentinel {
    friend auto operator==(Iterator, Sentinel) -> bool;
    friend auto operator!=(Iterator, Sentinel) -> bool;
  };
public:
  auto begin() -> Iterator;
  auto end() -> Sentinel;
};

class ConstRange {
  struct Iterator {
    auto operator*() const -> ValueType;
    auto operator++() -> Iterator&;
  };

  struct Sentinel {
    friend auto operator==(Iterator, Sentinel) -> bool;
    friend auto operator!=(Iterator, Sentinel) -> bool;
  };
public:
  auto begin() const -> Iterator;
  auto end() const -> Sentinel;
};
''';

fn Test[R:! Core.Iterate where .ElementType = Cpp.ValueType](var r: R) {
  var sum: Cpp.ValueType = Cpp.ValueType.ValueType();

  //@dump-sem-ir-begin
  for (i: Cpp.ValueType in r) {
    sum += i;
  }
  //@dump-sem-ir-end
}

fn TestDriver(var m: Cpp.MutableRange, c: Cpp.ConstRange) {
  Test(m);
  Test(c);
}

// --- adl_return_same_types.carbon

library "[[@TEST_NAME]]";

import Cpp inline '''c++
namespace N {
class ConstRange {
  struct Iterator {
    auto operator*() const -> const double&;
    auto operator++() -> Iterator&;
    friend auto operator==(Iterator, Iterator) -> bool;
    friend auto operator!=(Iterator, Iterator) -> bool;
  };
public:
  friend auto begin(const ConstRange&) -> Iterator;
  friend auto end(const ConstRange&) -> Iterator;
};
} // namespace N
''';

fn Test[R:! Core.Iterate where .ElementType = f64](r: R) {
  var sum: f64 = 0.0;

  //@dump-sem-ir-begin
  for (i: f64 in r) {
    sum += i;
  }
  //@dump-sem-ir-end
}

fn TestDriver(c: Cpp.N.ConstRange) {
  Test(c);
}

// --- fail_todo_adl_returns_same_types_mutable.carbon

// TODO: merge with adl_returns_same_types.carbon when passing.

library "[[@TEST_NAME]]";

import Cpp inline '''c++
namespace N {
class MutableRange {
  struct Iterator {
    auto operator*() const -> double&;
    auto operator++() -> Iterator&;
    friend auto operator==(Iterator, Iterator) -> bool;
    friend auto operator!=(Iterator, Iterator) -> bool;
  };
public:
  friend auto begin(MutableRange&) -> Iterator;
  friend auto end(MutableRange&) -> Iterator;
};
} // namespace N
''';

fn Test[R:! Core.Iterate where .ElementType = f64](r: R) {
  var sum: f64 = 0.0;

  //@dump-sem-ir-begin
  for (i: f64 in r) {
    sum += i;
  }
  //@dump-sem-ir-end
}

fn TestDriver(var m: Cpp.N.MutableRange) {
  // CHECK:STDERR: fail_todo_adl_returns_same_types_mutable.carbon:[[@LINE+32]]:3: error: facet type `Core.CppRangeForIterate where .(Core.CppRangeForIterate.Iterator) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator) impls Core.Copy and .(Core.CppRangeForIterate.Iterator) impls Core.CppUnsafeDeref and .(Core.CppRangeForIterate.Iterator) impls Core.EqWith(.(Core.CppRangeForIterate.Sentinel)) and .(Core.CppRangeForIterate.Iterator) impls Core.Inc and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Copy and .(Core.CppRangeForIterate.Sentinel) impls Core.Destroy and .(Core.CppRangeForIterate.Sentinel) impls Core.Copy` can not be identified [ImplLookupInUnidentifiedFacetType]
  // CHECK:STDERR:   Test(m);
  // CHECK:STDERR:   ^~~~~~~
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:39:12: note: value expression passed to reference parameter [ValueForRefParam]
  // CHECK:STDERR:   fn Begin[self: Self]() -> Iterator;
  // CHECK:STDERR:            ^~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_same_types_mutable.carbon:[[@LINE-23]]:34: note: initializing function parameter [InCallToFunctionParam]
  // CHECK:STDERR:   friend auto begin(MutableRange&) -> Iterator;
  // CHECK:STDERR:                                  ^
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:39:3: note: while building thunk to match the signature of this function [ThunkSignature]
  // CHECK:STDERR:   fn Begin[self: Self]() -> Iterator;
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_same_types_mutable.carbon:[[@LINE-23]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = f64](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  // CHECK:STDERR: fail_todo_adl_returns_same_types_mutable.carbon:[[@LINE+16]]:3: error: facet type `Core.CppRangeForIterate where .(Core.CppRangeForIterate.Iterator) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator) impls Core.Copy and .(Core.CppRangeForIterate.Iterator) impls Core.CppUnsafeDeref and .(Core.CppRangeForIterate.Iterator) impls Core.EqWith(.(Core.CppRangeForIterate.Sentinel)) and .(Core.CppRangeForIterate.Iterator) impls Core.Inc and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Copy and .(Core.CppRangeForIterate.Sentinel) impls Core.Destroy and .(Core.CppRangeForIterate.Sentinel) impls Core.Copy` can not be identified [ImplLookupInUnidentifiedFacetType]
  // CHECK:STDERR:   Test(m);
  // CHECK:STDERR:   ^~~~~~~
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:40:10: note: value expression passed to reference parameter [ValueForRefParam]
  // CHECK:STDERR:   fn End[self: Self]() -> Sentinel;
  // CHECK:STDERR:          ^~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_same_types_mutable.carbon:[[@LINE-38]]:32: note: initializing function parameter [InCallToFunctionParam]
  // CHECK:STDERR:   friend auto end(MutableRange&) -> Iterator;
  // CHECK:STDERR:                                ^
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:40:3: note: while building thunk to match the signature of this function [ThunkSignature]
  // CHECK:STDERR:   fn End[self: Self]() -> Sentinel;
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_same_types_mutable.carbon:[[@LINE-39]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = f64](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(m);
}

// --- adl_returns_different_types.carbon

library "[[@TEST_NAME]]";

import Cpp inline '''c++
namespace N {
struct ValueType {
  auto operator+=(const ValueType& other) -> ValueType&;
};

class ConstRange {
  struct Iterator {
    auto operator*() const -> ValueType;
    auto operator++() -> Iterator&;
  };

  struct Sentinel {
    friend auto operator==(Iterator, Sentinel) -> bool;
    friend auto operator!=(Iterator, Sentinel) -> bool;
  };
public:
  friend auto begin(const ConstRange&) -> Iterator;
  friend auto end(const ConstRange&) -> Sentinel;
};
} // namespace N
''';

fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  var sum: Cpp.N.ValueType = Cpp.N.ValueType.ValueType();

  //@dump-sem-ir-begin
  for (i: Cpp.N.ValueType in r) {
    sum += i;
  }
  //@dump-sem-ir-end
}

fn TestDriver(c: Cpp.N.ConstRange) {
  Test(c);
}

// --- fail_todo_adl_returns_different_types_mutable.carbon

library "[[@TEST_NAME]]";

import Cpp inline '''c++
namespace N {
struct ValueType {
  auto operator+=(const ValueType& other) -> ValueType&;
};

class MutableRange {

  struct Iterator {
    auto operator*() const -> ValueType&;
    auto operator++() -> Iterator&;
  };

  struct Sentinel {
    friend auto operator==(Sentinel, Iterator) -> bool;
    friend auto operator!=(Sentinel, Iterator) -> bool;
  };
public:
  friend auto begin(MutableRange&) -> Iterator;
  friend auto end(MutableRange&) -> Sentinel;
};
}
''';

fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  var sum: Cpp.N.ValueType = Cpp.N.ValueType.ValueType();

  //@dump-sem-ir-begin
  for (i: Cpp.N.ValueType in r) {
    sum += i;
  }
  //@dump-sem-ir-end
}

fn TestDriver(var m: Cpp.N.MutableRange) {
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE+46]]:3: error: facet type `Core.CppRangeForIterate where .(Core.CppRangeForIterate.Iterator) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator) impls Core.Copy and .(Core.CppRangeForIterate.Iterator) impls Core.CppUnsafeDeref and .(Core.CppRangeForIterate.Iterator) impls Core.EqWith(.(Core.CppRangeForIterate.Sentinel)) and .(Core.CppRangeForIterate.Iterator) impls Core.Inc and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Copy and .(Core.CppRangeForIterate.Sentinel) impls Core.Destroy and .(Core.CppRangeForIterate.Sentinel) impls Core.Copy` can not be identified [ImplLookupInUnidentifiedFacetType]
  // CHECK:STDERR:   Test(m);
  // CHECK:STDERR:   ^~~~~~~
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:39:12: note: value expression passed to reference parameter [ValueForRefParam]
  // CHECK:STDERR:   fn Begin[self: Self]() -> Iterator;
  // CHECK:STDERR:            ^~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE-23]]:34: note: initializing function parameter [InCallToFunctionParam]
  // CHECK:STDERR:   friend auto begin(MutableRange&) -> Iterator;
  // CHECK:STDERR:                                  ^
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:39:3: note: while building thunk to match the signature of this function [ThunkSignature]
  // CHECK:STDERR:   fn Begin[self: Self]() -> Iterator;
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE-23]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE+30]]:3: error: facet type `Core.CppRangeForIterate where .(Core.CppRangeForIterate.Iterator) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator) impls Core.Copy and .(Core.CppRangeForIterate.Iterator) impls Core.CppUnsafeDeref and .(Core.CppRangeForIterate.Iterator) impls Core.EqWith(.(Core.CppRangeForIterate.Sentinel)) and .(Core.CppRangeForIterate.Iterator) impls Core.Inc and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Copy and .(Core.CppRangeForIterate.Sentinel) impls Core.Destroy and .(Core.CppRangeForIterate.Sentinel) impls Core.Copy` can not be identified [ImplLookupInUnidentifiedFacetType]
  // CHECK:STDERR:   Test(m);
  // CHECK:STDERR:   ^~~~~~~
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:40:10: note: value expression passed to reference parameter [ValueForRefParam]
  // CHECK:STDERR:   fn End[self: Self]() -> Sentinel;
  // CHECK:STDERR:          ^~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE-38]]:32: note: initializing function parameter [InCallToFunctionParam]
  // CHECK:STDERR:   friend auto end(MutableRange&) -> Sentinel;
  // CHECK:STDERR:                                ^
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:40:3: note: while building thunk to match the signature of this function [ThunkSignature]
  // CHECK:STDERR:   fn End[self: Self]() -> Sentinel;
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE-39]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE+14]]:3: error: semantics TODO: `Rewriting operator== using operator== is not supported` [SemanticsTodo]
  // CHECK:STDERR:   Test(m);
  // CHECK:STDERR:   ^~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE-46]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.N.MutableRange` into type implementing `Core.Iterate where .(Core.Iterate.ElementType) = Cpp.N.ValueType as Core.Destroy & Core.Copy` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(m);
  // CHECK:STDERR:   ^~~~~~~
  // CHECK:STDERR: fail_todo_adl_returns_different_types_mutable.carbon:[[@LINE-53]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(m);
}

// --- fail_todo_adl_overloads.carbon

import Cpp inline '''c++
namespace N {
struct ValueType {
  auto operator+=(const ValueType&) -> ValueType&;
};

class MutableAndConstRange {

  struct Iterator {
    auto operator*() const -> ValueType&;
    auto operator++() -> Iterator&;

    friend auto operator==(Iterator, Iterator) -> bool;
    friend auto operator!=(Iterator, Iterator) -> bool;
  };

  struct ConstIterator {
    auto operator*() const -> ValueType&;
    auto operator++() -> Iterator&;

    friend auto operator==(ConstIterator, ConstIterator) -> bool;
    friend auto operator!=(ConstIterator, ConstIterator) -> bool;
  };
  public:
    friend auto begin(MutableAndConstRange&) -> Iterator;
    friend auto end(MutableAndConstRange&) -> Iterator;

    friend auto begin(const MutableAndConstRange&) -> ConstIterator;
    friend auto end(const MutableAndConstRange&) -> ConstIterator;
};
}
''';

fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  var sum: Cpp.N.ValueType = Cpp.N.ValueType.ValueType();

  //@dump-sem-ir-begin
  for (i: Cpp.N.ValueType in r) {
    sum += i;
  }
  //@dump-sem-ir-end
}

fn TestDriver(var mc: Cpp.N.MutableAndConstRange) {
  // CHECK:STDERR: fail_todo_adl_overloads.carbon:[[@LINE+32]]:3: error: facet type `Core.CppRangeForIterate where .(Core.CppRangeForIterate.Iterator) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator) impls Core.Copy and .(Core.CppRangeForIterate.Iterator) impls Core.CppUnsafeDeref and .(Core.CppRangeForIterate.Iterator) impls Core.EqWith(.(Core.CppRangeForIterate.Sentinel)) and .(Core.CppRangeForIterate.Iterator) impls Core.Inc and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Copy and .(Core.CppRangeForIterate.Sentinel) impls Core.Destroy and .(Core.CppRangeForIterate.Sentinel) impls Core.Copy` can not be identified [ImplLookupInUnidentifiedFacetType]
  // CHECK:STDERR:   Test(mc);
  // CHECK:STDERR:   ^~~~~~~~
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:39:12: note: value expression passed to reference parameter [ValueForRefParam]
  // CHECK:STDERR:   fn Begin[self: Self]() -> Iterator;
  // CHECK:STDERR:            ^~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_overloads.carbon:[[@LINE-26]]:44: note: initializing function parameter [InCallToFunctionParam]
  // CHECK:STDERR:     friend auto begin(MutableAndConstRange&) -> Iterator;
  // CHECK:STDERR:                                            ^
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:39:3: note: while building thunk to match the signature of this function [ThunkSignature]
  // CHECK:STDERR:   fn Begin[self: Self]() -> Iterator;
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_overloads.carbon:[[@LINE-23]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  // CHECK:STDERR: fail_todo_adl_overloads.carbon:[[@LINE+16]]:3: error: facet type `Core.CppRangeForIterate where .(Core.CppRangeForIterate.Iterator) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator) impls Core.Copy and .(Core.CppRangeForIterate.Iterator) impls Core.CppUnsafeDeref and .(Core.CppRangeForIterate.Iterator) impls Core.EqWith(.(Core.CppRangeForIterate.Sentinel)) and .(Core.CppRangeForIterate.Iterator) impls Core.Inc and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Destroy and .(Core.CppRangeForIterate.Iterator).(Core.CppUnsafeDeref.Result) impls Core.Copy and .(Core.CppRangeForIterate.Sentinel) impls Core.Destroy and .(Core.CppRangeForIterate.Sentinel) impls Core.Copy` can not be identified [ImplLookupInUnidentifiedFacetType]
  // CHECK:STDERR:   Test(mc);
  // CHECK:STDERR:   ^~~~~~~~
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:40:10: note: value expression passed to reference parameter [ValueForRefParam]
  // CHECK:STDERR:   fn End[self: Self]() -> Sentinel;
  // CHECK:STDERR:          ^~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_overloads.carbon:[[@LINE-41]]:42: note: initializing function parameter [InCallToFunctionParam]
  // CHECK:STDERR:     friend auto end(MutableAndConstRange&) -> Iterator;
  // CHECK:STDERR:                                          ^
  // CHECK:STDERR: {{.*}}/prelude/iterate.carbon:40:3: note: while building thunk to match the signature of this function [ThunkSignature]
  // CHECK:STDERR:   fn End[self: Self]() -> Sentinel;
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_todo_adl_overloads.carbon:[[@LINE-39]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.Iterate where .ElementType = Cpp.N.ValueType](r: R) {
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(mc);
}

// --- fail_never_valid.carbon

library "[[@TEST_NAME]]";

import Cpp inline '''c++
class NoBeginEnd {};

struct NoBeginMethod {
  auto end() -> int;
};

struct NoEndMethod {
  auto begin() -> int;
};

struct NoBeginADL {
  friend auto end(NoBeginADL) -> int;
};

struct NoEndADL {
  friend auto begin(NoEndADL) -> int;
};

struct BeginMethodEndADL {
  auto begin() -> int;
  friend auto end(BeginMethodEndADL) -> int;
};

struct BeginADLEndMethod {
  friend auto begin(BeginADLEndMethod) -> int;
  auto end() -> int;
};

struct BeginFieldEndMethod {
  int begin;
  auto end() -> int;
};

struct BeginMethodEndField {
  auto begin() -> int;
  int end;
};

struct BeginMethodDeleted {
  auto begin() = delete;
  auto end() -> int;
};

struct EndMethodDeleted {
  auto begin() -> int;
  auto end() = delete;
};

struct BeginFunctionDeleted {
  friend auto begin(const BeginFunctionDeleted&) = delete;
  friend auto end(const BeginFunctionDeleted&) -> int;
};

struct EndFunctionDeleted {
  friend auto begin(const EndFunctionDeleted&) -> int;
  friend auto end(const EndFunctionDeleted&) = delete;
};
''';

// We deliberately use `Core.CppRangeForIterate` here, since we want to confirm
// that types don't implement this interface.
fn Test[R:! Core.CppRangeForIterate](unused r: R) {}

fn TestDriver(var no_begin_end: Cpp.NoBeginEnd,
              var no_begin_method: Cpp.NoBeginMethod,
              var no_end_method: Cpp.NoEndMethod,
              var no_begin_adl: Cpp.NoBeginADL,
              var no_end_adl: Cpp.NoEndADL,
              var begin_method_end_adl: Cpp.BeginMethodEndADL,
              var begin_adl_end_method: Cpp.BeginADLEndMethod,
              var begin_field_end_method: Cpp.BeginFieldEndMethod,
              var begin_method_end_field: Cpp.BeginMethodEndField,
              var begin_method_deleted: Cpp.BeginMethodDeleted,
              var end_method_deleted: Cpp.EndMethodDeleted,
              var begin_function_deleted: Cpp.BeginFunctionDeleted,
              var end_function_deleted: Cpp.EndFunctionDeleted)
{
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.NoBeginEnd` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(no_begin_end);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-19]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(no_begin_end);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.NoBeginMethod` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(no_begin_method);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-28]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(no_begin_method);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.NoEndMethod` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(no_end_method);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-37]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(no_end_method);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.NoBeginADL` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(no_begin_adl);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-46]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(no_begin_adl);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.NoEndADL` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(no_end_adl);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-55]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(no_end_adl);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.BeginMethodEndADL` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(begin_method_end_adl);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-64]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(begin_method_end_adl);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.BeginADLEndMethod` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(begin_adl_end_method);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-73]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(begin_adl_end_method);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.BeginFieldEndMethod` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(begin_field_end_method);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-82]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(begin_field_end_method);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+7]]:3: error: cannot convert type `Cpp.BeginMethodEndField` into type implementing `Core.CppRangeForIterate` [ConversionFailureTypeToFacet]
  // CHECK:STDERR:   Test(begin_method_end_field);
  // CHECK:STDERR:   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-91]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(begin_method_end_field);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+10]]:28: error: attempt to use a deleted function [CppInteropParseError]
  // CHECK:STDERR:   173 |   Test(begin_method_deleted);
  // CHECK:STDERR:       |                            ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-122]]:8: note: 'begin' has been explicitly marked deleted here [CppInteropParseNote]
  // CHECK:STDERR:    44 |   auto begin() = delete;
  // CHECK:STDERR:       |        ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-103]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(begin_method_deleted);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+10]]:26: error: attempt to use a deleted function [CppInteropParseError]
  // CHECK:STDERR:   185 |   Test(end_method_deleted);
  // CHECK:STDERR:       |                          ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-128]]:8: note: 'end' has been explicitly marked deleted here [CppInteropParseNote]
  // CHECK:STDERR:    50 |   auto end() = delete;
  // CHECK:STDERR:       |        ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-115]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(end_method_deleted);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+10]]:30: error: call to deleted function 'begin' [CppInteropParseError]
  // CHECK:STDERR:   197 |   Test(begin_function_deleted);
  // CHECK:STDERR:       |                              ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-136]]:15: note: candidate function has been explicitly deleted [CppInteropParseNote]
  // CHECK:STDERR:    54 |   friend auto begin(const BeginFunctionDeleted&) = delete;
  // CHECK:STDERR:       |               ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-127]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(begin_function_deleted);

  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE+10]]:28: error: call to deleted function 'end' [CppInteropParseError]
  // CHECK:STDERR:   209 |   Test(end_function_deleted);
  // CHECK:STDERR:       |                            ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-142]]:15: note: candidate function has been explicitly deleted [CppInteropParseNote]
  // CHECK:STDERR:    60 |   friend auto end(const EndFunctionDeleted&) = delete;
  // CHECK:STDERR:       |               ^
  // CHECK:STDERR: fail_never_valid.carbon:[[@LINE-139]]:1: note: while deducing parameters of generic declared here [DeductionGenericHere]
  // CHECK:STDERR: fn Test[R:! Core.CppRangeForIterate](unused r: R) {}
  // CHECK:STDERR: ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // CHECK:STDERR:
  Test(end_function_deleted);
}

// CHECK:STDOUT: --- methods_return_same_type.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Iterate.type: type = facet_type <@Iterate> [concrete]
// CHECK:STDOUT:   %OptionalStorage.type: type = facet_type <@OptionalStorage> [concrete]
// CHECK:STDOUT:   %Destroy.type: type = facet_type <@Destroy> [concrete]
// CHECK:STDOUT:   %facet_type.f48: type = facet_type <@Destroy & @Copy> [concrete]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [concrete]
// CHECK:STDOUT:   %T.220: %OptionalStorage.type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Optional.Get.type.bb9: type = fn_type @Optional.Get, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.Get.fa1: %Optional.Get.type.bb9 = struct_value () [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.e9e: type = fn_type @Optional.HasValue, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.6cd: %Optional.HasValue.type.e9e = struct_value () [symbolic]
// CHECK:STDOUT:   %T.283: %facet_type.f48 = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.d50: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.type.671: type = fn_type @T.as_type.as.OptionalStorage.impl.Get, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.a54: %T.as_type.as.OptionalStorage.impl.Get.type.671 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.type.d76: type = fn_type @T.as_type.as.OptionalStorage.impl.Has, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.aa4: %T.as_type.as.OptionalStorage.impl.Has.type.d76 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.type.973: type = fn_type @T.as_type.as.OptionalStorage.impl.Some, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.c3a: %T.as_type.as.OptionalStorage.impl.Some.type.973 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.type.f62: type = fn_type @T.as_type.as.OptionalStorage.impl.None, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.faf: %T.as_type.as.OptionalStorage.impl.None.type.f62 = struct_value () [symbolic]
// CHECK:STDOUT:   %.Self.0.500: %Iterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.1d8: <witness> = lookup_impl_witness %.Self.0.500, @Iterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.294: %facet_type.f48 = impl_witness_access %Iterate.lookup_impl_witness.1d8, element0 [symbolic_self]
// CHECK:STDOUT:   %int_32: Core.IntLiteral = int_value 32 [concrete]
// CHECK:STDOUT:   %N.fe9: Core.IntLiteral = symbolic_binding N, 0 [symbolic]
// CHECK:STDOUT:   %Int.67af24.1: type = class_type @Int, @Int(%N.fe9) [symbolic]
// CHECK:STDOUT:   %i32: type = class_type @Int, @Int(%int_32) [concrete]
// CHECK:STDOUT:   %pattern_type.6b6: type = pattern_type %i32 [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.2: type = fn_type @Destroy.Op.loc30_47.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.2: %Destroy.Op.type.1d8f74.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.2: <witness> = custom_witness (%Destroy.Op.1a2547.2), @Destroy [concrete]
// CHECK:STDOUT:   %Int.as.Copy.impl.Op.type.ac8: type = fn_type @Int.as.Copy.impl.Op, @Int.as.Copy.impl(%N.fe9) [symbolic]
// CHECK:STDOUT:   %Int.as.Copy.impl.Op.5e0: %Int.as.Copy.impl.Op.type.ac8 = struct_value () [symbolic]
// CHECK:STDOUT:   %Copy.impl_witness.0e0: <witness> = impl_witness imports.%Copy.impl_witness_table.367, @Int.as.Copy.impl(%int_32) [concrete]
// CHECK:STDOUT:   %facet_value.ba2: %facet_type.f48 = facet_value %i32, (%custom_witness.df9cc1.2, %Copy.impl_witness.0e0) [concrete]
// CHECK:STDOUT:   %Iterate_where.type.ec1: type = facet_type <@Iterate where %impl.elem0.294 = %facet_value.ba2> [concrete]
// CHECK:STDOUT:   %R.869: %Iterate_where.type.ec1 = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %R.as_type.a02: type = facet_access_type %R.869 [symbolic]
// CHECK:STDOUT:   %pattern_type.b2da: type = pattern_type %R.as_type.a02 [symbolic]
// CHECK:STDOUT:   %ImplicitAs.type.914: type = facet_type <@ImplicitAs, @ImplicitAs(%i32)> [concrete]
// CHECK:STDOUT:   %To: Core.IntLiteral = symbolic_binding To, 0 [symbolic]
// CHECK:STDOUT:   %Int.67af24.2: type = class_type @Int, @Int(%To) [symbolic]
// CHECK:STDOUT:   %facet_type.037: type = facet_type <@IntFitsIn, @IntFitsIn(%Int.67af24.2) & @AnyInt> [symbolic]
// CHECK:STDOUT:   %From.6a4: %facet_type.037 = symbolic_binding From, 1 [symbolic]
// CHECK:STDOUT:   %From.as_type.as.ImplicitAs.impl.Convert.type.7fa: type = fn_type @From.as_type.as.ImplicitAs.impl.Convert, @From.as_type.as.ImplicitAs.impl(%To, %From.6a4) [symbolic]
// CHECK:STDOUT:   %From.as_type.as.ImplicitAs.impl.Convert.643: %From.as_type.as.ImplicitAs.impl.Convert.type.7fa = struct_value () [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.type: type = facet_type <@CppRangeForIterate> [concrete]
// CHECK:STDOUT:   %.Self.0.aed: %CppRangeForIterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.f6b: <witness> = lookup_impl_witness %.Self.0.aed, @CppRangeForIterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.b73: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element0 [symbolic_self]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.595: <witness> = lookup_impl_witness %impl.elem0.b73, @CppUnsafeDeref [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.a2f: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.595, element0 [symbolic_self]
// CHECK:STDOUT:   %impl.elem1.228: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element1 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate_where.type: type = facet_type <@CppRangeForIterate where %impl.elem0.b73 impls @Destroy and %impl.elem0.b73 impls @Copy and %impl.elem0.b73 impls @CppUnsafeDeref and %impl.elem0.b73 impls @EqWith, @EqWith(%impl.elem1.228) and %impl.elem0.b73 impls @Inc and %impl.elem0.a2f impls @Destroy and %impl.elem0.a2f impls @Copy and %impl.elem1.228 impls @Destroy and %impl.elem1.228 impls @Copy> [concrete]
// CHECK:STDOUT:   %R.39b: %CppRangeForIterate_where.type = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.7e2712.2: <witness> = lookup_impl_witness %R.39b, @CppRangeForIterate [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a0bff.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element1 [symbolic]
// CHECK:STDOUT:   %impl.elem0.73eb7f.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element0 [symbolic]
// CHECK:STDOUT:   %tuple.type.3cf: type = tuple_type (%impl.elem0.73eb7f.2, %impl.elem1.7a0bff.2) [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.69f: <witness> = lookup_impl_witness %tuple.type.3cf, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.facet.593: %Destroy.type = facet_value %tuple.type.3cf, (%Destroy.lookup_impl_witness.69f) [symbolic]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.aa7: <witness> = lookup_impl_witness %impl.elem0.73eb7f.2, @CppUnsafeDeref [symbolic]
// CHECK:STDOUT:   %impl.elem0.af7: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.aa7, element0 [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.ec3: <witness> = lookup_impl_witness %impl.elem0.af7, @Destroy [symbolic]
// CHECK:STDOUT:   %Copy.lookup_impl_witness.a7a: <witness> = lookup_impl_witness %impl.elem0.af7, @Copy [symbolic]
// CHECK:STDOUT:   %facet_value.194: %facet_type.f48 = facet_value %impl.elem0.af7, (%Destroy.lookup_impl_witness.ec3, %Copy.lookup_impl_witness.a7a) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.d8f: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c6d: %R.as_type.as.Iterate.impl.Next.type.d8f = struct_value () [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.127: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.627: %R.as_type.as.Iterate.impl.NewCursor.type.127 = struct_value () [symbolic]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.18b: <witness> = lookup_impl_witness %R.869, @Iterate [symbolic]
// CHECK:STDOUT:   %Iterate.facet.353: %Iterate.type = facet_value %R.as_type.a02, (%Iterate.lookup_impl_witness.18b) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.8fb: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.353) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.830: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.353) [symbolic]
// CHECK:STDOUT:   %.985: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.8fb, %Iterate.facet.353 [symbolic]
// CHECK:STDOUT:   %impl.elem2.8ec: %.985 = impl_witness_access %Iterate.lookup_impl_witness.18b, element2 [symbolic]
// CHECK:STDOUT:   %impl.elem1.295: %Destroy.type = impl_witness_access %Iterate.lookup_impl_witness.18b, element1 [symbolic]
// CHECK:STDOUT:   %as_type.c8a: type = facet_access_type %impl.elem1.295 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.9ca: <specific function> = specific_impl_function %impl.elem2.8ec, @Iterate.WithSelf.NewCursor(%Iterate.facet.353) [symbolic]
// CHECK:STDOUT:   %ptr.2ef: type = ptr_type %as_type.c8a [symbolic]
// CHECK:STDOUT:   %.f86: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.830, %Iterate.facet.353 [symbolic]
// CHECK:STDOUT:   %impl.elem3.5f7: %.f86 = impl_witness_access %Iterate.lookup_impl_witness.18b, element3 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.970: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%facet_value.ba2) [concrete]
// CHECK:STDOUT:   %OptionalStorage.impl_witness.57d: <witness> = impl_witness imports.%OptionalStorage.impl_witness_table.199, @T.as_type.as.OptionalStorage.impl(%facet_value.ba2) [concrete]
// CHECK:STDOUT:   %OptionalStorage.facet.563: %OptionalStorage.type = facet_value %i32, (%OptionalStorage.impl_witness.57d) [concrete]
// CHECK:STDOUT:   %Optional.a23: type = class_type @Optional, @Optional(%OptionalStorage.facet.563) [concrete]
// CHECK:STDOUT:   %specific_impl_fn.9a8: <specific function> = specific_impl_function %impl.elem3.5f7, @Iterate.WithSelf.Next(%Iterate.facet.353) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.560: type = fn_type @Optional.HasValue, @Optional(%OptionalStorage.facet.563) [concrete]
// CHECK:STDOUT:   %Optional.HasValue.bef: %Optional.HasValue.type.560 = struct_value () [concrete]
// CHECK:STDOUT:   %Optional.Get.type.11a: type = fn_type @Optional.Get, @Optional(%OptionalStorage.facet.563) [concrete]
// CHECK:STDOUT:   %Optional.Get.0ee: %Optional.Get.type.11a = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.facet.d07318.2: %Destroy.type = facet_value %i32, (%custom_witness.df9cc1.2) [concrete]
// CHECK:STDOUT:   %MaybeUnformed.023: type = class_type @MaybeUnformed, @MaybeUnformed(%Destroy.facet.d07318.2) [concrete]
// CHECK:STDOUT:   %struct_type.value.has_value.ad0: type = struct_type {.value: %MaybeUnformed.023, .has_value: bool} [concrete]
// CHECK:STDOUT:   %Optional.HasValue.specific_fn: <specific function> = specific_function %Optional.HasValue.bef, @Optional.HasValue(%OptionalStorage.facet.563) [concrete]
// CHECK:STDOUT:   %Optional.Get.specific_fn: <specific function> = specific_function %Optional.Get.0ee, @Optional.Get(%OptionalStorage.facet.563) [concrete]
// CHECK:STDOUT:   %AddAssignWith.type.941: type = facet_type <@AddAssignWith, @AddAssignWith(%i32)> [concrete]
// CHECK:STDOUT:   %ImplicitAs.type.f7de31.2: type = facet_type <@ImplicitAs, @ImplicitAs(%Int.67af24.1)> [symbolic]
// CHECK:STDOUT:   %U.4e6: %ImplicitAs.type.f7de31.2 = symbolic_binding U, 1 [symbolic]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.type.a58fbe.1: type = fn_type @Int.as.AddAssignWith.impl.Op.1, @Int.as.AddAssignWith.impl(%N.fe9, %U.4e6) [symbolic]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.45b360.1: %Int.as.AddAssignWith.impl.Op.type.a58fbe.1 = struct_value () [symbolic]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.type.a58fbe.2: type = fn_type @Int.as.AddAssignWith.impl.Op.2, @Int.as.AddAssignWith.impl(%N.fe9, %U.4e6) [symbolic]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.45b360.2: %Int.as.AddAssignWith.impl.Op.type.a58fbe.2 = struct_value () [symbolic]
// CHECK:STDOUT:   %facet_type.138: type = facet_type <@IntFitsIn, @IntFitsIn(%i32) & @AnyInt> [concrete]
// CHECK:STDOUT:   %custom_witness.36a: <witness> = custom_witness (), @IntFitsIn, @IntFitsIn(%i32) [concrete]
// CHECK:STDOUT:   %Int.as.AnyInt.impl.AsInt.type.80b: type = fn_type @Int.as.AnyInt.impl.AsInt, @Int.as.AnyInt.impl(%N.fe9) [symbolic]
// CHECK:STDOUT:   %Int.as.AnyInt.impl.AsInt.23f: %Int.as.AnyInt.impl.AsInt.type.80b = struct_value () [symbolic]
// CHECK:STDOUT:   %AnyInt.impl_witness.76c: <witness> = impl_witness imports.%AnyInt.impl_witness_table, @Int.as.AnyInt.impl(%int_32) [concrete]
// CHECK:STDOUT:   %facet_value.6b8: %facet_type.138 = facet_value %i32, (%custom_witness.36a, %AnyInt.impl_witness.76c) [concrete]
// CHECK:STDOUT:   %ImplicitAs.impl_witness.03f: <witness> = impl_witness imports.%ImplicitAs.impl_witness_table.3b9, @From.as_type.as.ImplicitAs.impl(%int_32, %facet_value.6b8) [concrete]
// CHECK:STDOUT:   %ImplicitAs.facet.640: %ImplicitAs.type.914 = facet_value %i32, (%ImplicitAs.impl_witness.03f) [concrete]
// CHECK:STDOUT:   %AddAssignWith.impl_witness.ccf: <witness> = impl_witness imports.%AddAssignWith.impl_witness_table, @Int.as.AddAssignWith.impl(%int_32, %ImplicitAs.facet.640) [concrete]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.type.a94901.1: type = fn_type @Int.as.AddAssignWith.impl.Op.2, @Int.as.AddAssignWith.impl(%int_32, %ImplicitAs.facet.640) [concrete]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.83e130.1: %Int.as.AddAssignWith.impl.Op.type.a94901.1 = struct_value () [concrete]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.type.a94901.2: type = fn_type @Int.as.AddAssignWith.impl.Op.1, @Int.as.AddAssignWith.impl(%int_32, %ImplicitAs.facet.640) [concrete]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.83e130.2: %Int.as.AddAssignWith.impl.Op.type.a94901.2 = struct_value () [concrete]
// CHECK:STDOUT:   %AddAssignWith.facet.b9a: %AddAssignWith.type.941 = facet_value %i32, (%AddAssignWith.impl_witness.ccf) [concrete]
// CHECK:STDOUT:   %AddAssignWith.WithSelf.Op.type.51d: type = fn_type @AddAssignWith.WithSelf.Op, @AddAssignWith.WithSelf(%i32, %AddAssignWith.facet.b9a) [concrete]
// CHECK:STDOUT:   %.98a: type = fn_type_with_self_type %AddAssignWith.WithSelf.Op.type.51d, %AddAssignWith.facet.b9a [concrete]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.specific_fn.80c75c.1: <specific function> = specific_function %Int.as.AddAssignWith.impl.Op.83e130.2, @Int.as.AddAssignWith.impl.Op.1(%int_32, %ImplicitAs.facet.640) [concrete]
// CHECK:STDOUT:   %Int.as.AddAssignWith.impl.Op.specific_fn.80c75c.2: <specific function> = specific_function %Int.as.AddAssignWith.impl.Op.83e130.1, @Int.as.AddAssignWith.impl.Op.2(%int_32, %ImplicitAs.facet.640) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.8: type = fn_type @Destroy.Op.loc34_19.5 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.8: %Destroy.Op.type.1d8f74.8 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.d26: <witness> = lookup_impl_witness %impl.elem1.295, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.71c: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1.295) [symbolic]
// CHECK:STDOUT:   %.fa0: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.71c, %impl.elem1.295 [symbolic]
// CHECK:STDOUT:   %impl.elem0.544: %.fa0 = impl_witness_access %Destroy.lookup_impl_witness.d26, element0 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.fa9: <specific function> = specific_impl_function %impl.elem0.544, @Destroy.WithSelf.Op(%impl.elem1.295) [symbolic]
// CHECK:STDOUT:   %MutableRange: type = class_type @MutableRange [concrete]
// CHECK:STDOUT:   %pattern_type.e635: type = pattern_type %MutableRange [concrete]
// CHECK:STDOUT:   %ConstRange: type = class_type @ConstRange [concrete]
// CHECK:STDOUT:   %pattern_type.0ba: type = pattern_type %ConstRange [concrete]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [concrete]
// CHECK:STDOUT:   %complete_type.357: <witness> = complete_type_witness %empty_struct_type [concrete]
// CHECK:STDOUT:   %Iterator.3ee: type = class_type @Iterator.1 [concrete]
// CHECK:STDOUT:   %MutableRange.Begin.type: type = fn_type @MutableRange.Begin [concrete]
// CHECK:STDOUT:   %MutableRange.Begin: %MutableRange.Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %MutableRange.End.type: type = fn_type @MutableRange.End [concrete]
// CHECK:STDOUT:   %MutableRange.End: %MutableRange.End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.ed3: <witness> = custom_witness (%Iterator.3ee, %Iterator.3ee, %MutableRange.Begin, %MutableRange.End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.1: type = fn_type @Iterator.Op.1 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.1: %Iterator.Op.type.0aed5d.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.ef8: <witness> = custom_witness (%i32, %Iterator.Op.a2a866.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.2: type = fn_type @Iterator.Op.2 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.2: %Iterator.Op.type.0aed5d.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.955: <witness> = custom_witness (%Iterator.Op.a2a866.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.3: type = fn_type @Iterator.Op.3 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.3: %Iterator.Op.type.0aed5d.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.1f5: <witness> = custom_witness (%Iterator.Op.a2a866.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type.ca8475.1: type = fn_type @Equal.1 [concrete]
// CHECK:STDOUT:   %Equal.285b15.1: %Equal.type.ca8475.1 = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type.53d9ee.1: type = fn_type @NotEqual.1 [concrete]
// CHECK:STDOUT:   %NotEqual.119263.1: %NotEqual.type.53d9ee.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.981: <witness> = custom_witness (%Equal.285b15.1, %NotEqual.119263.1), @EqWith, @EqWith(%Iterator.3ee) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.4: type = fn_type @Iterator.Op.4 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.4: %Iterator.Op.type.0aed5d.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.444: <witness> = custom_witness (%Iterator.Op.a2a866.4), @Inc [concrete]
// CHECK:STDOUT:   %facet_value.cd6: %CppRangeForIterate_where.type = facet_value %MutableRange, (%custom_witness.df9cc1.2, %Copy.impl_witness.0e0, %custom_witness.ed3, %custom_witness.955, %custom_witness.1f5, %custom_witness.ef8, %custom_witness.981, %custom_witness.444) [concrete]
// CHECK:STDOUT:   %tuple.type.508: type = tuple_type (%Iterator.3ee, %Iterator.3ee) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.9: type = fn_type @Destroy.Op.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.9: %Destroy.Op.type.1d8f74.9 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.9: <witness> = custom_witness (%Destroy.Op.1a2547.9), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.30f: %Destroy.type = facet_value %tuple.type.508, (%custom_witness.df9cc1.9) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.b92: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.cd6) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.c9f: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.cd6) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.d98: %R.as_type.as.Iterate.impl.NewCursor.type.c9f = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.ad0: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.cd6) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.d29: %R.as_type.as.Iterate.impl.Next.type.ad0 = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.b2e: %Iterate.type = facet_value %MutableRange, (%Iterate.impl_witness.b92) [concrete]
// CHECK:STDOUT:   %facet_value.8de: %Iterate_where.type.ec1 = facet_value %MutableRange, (%Iterate.impl_witness.b92) [concrete]
// CHECK:STDOUT:   %Iterator.260: type = class_type @Iterator.2 [concrete]
// CHECK:STDOUT:   %ConstRange.Begin.type: type = fn_type @ConstRange.Begin [concrete]
// CHECK:STDOUT:   %ConstRange.Begin: %ConstRange.Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %ConstRange.End.type: type = fn_type @ConstRange.End [concrete]
// CHECK:STDOUT:   %ConstRange.End: %ConstRange.End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.23e: <witness> = custom_witness (%Iterator.260, %Iterator.260, %ConstRange.Begin, %ConstRange.End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.1: type = fn_type @Iterator.Op.5 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.1: %Iterator.Op.type.0f34b8.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.adb: <witness> = custom_witness (%i32, %Iterator.Op.1c3e4a.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.2: type = fn_type @Iterator.Op.6 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.2: %Iterator.Op.type.0f34b8.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.6e8: <witness> = custom_witness (%Iterator.Op.1c3e4a.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.3: type = fn_type @Iterator.Op.7 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.3: %Iterator.Op.type.0f34b8.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.150: <witness> = custom_witness (%Iterator.Op.1c3e4a.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type.ca8475.2: type = fn_type @Equal.2 [concrete]
// CHECK:STDOUT:   %Equal.285b15.2: %Equal.type.ca8475.2 = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type.53d9ee.2: type = fn_type @NotEqual.2 [concrete]
// CHECK:STDOUT:   %NotEqual.119263.2: %NotEqual.type.53d9ee.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.941: <witness> = custom_witness (%Equal.285b15.2, %NotEqual.119263.2), @EqWith, @EqWith(%Iterator.260) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.4: type = fn_type @Iterator.Op.8 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.4: %Iterator.Op.type.0f34b8.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.746: <witness> = custom_witness (%Iterator.Op.1c3e4a.4), @Inc [concrete]
// CHECK:STDOUT:   %facet_value.e88: %CppRangeForIterate_where.type = facet_value %ConstRange, (%custom_witness.df9cc1.2, %Copy.impl_witness.0e0, %custom_witness.23e, %custom_witness.6e8, %custom_witness.150, %custom_witness.adb, %custom_witness.941, %custom_witness.746) [concrete]
// CHECK:STDOUT:   %tuple.type.69f: type = tuple_type (%Iterator.260, %Iterator.260) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.10: type = fn_type @Destroy.Op.3 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.10: %Destroy.Op.type.1d8f74.10 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.10: <witness> = custom_witness (%Destroy.Op.1a2547.10), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.e4c: %Destroy.type = facet_value %tuple.type.69f, (%custom_witness.df9cc1.10) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.a61: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.e88) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.50d: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.e88) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.0b2: %R.as_type.as.Iterate.impl.NewCursor.type.50d = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.121: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.e88) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.bec: %R.as_type.as.Iterate.impl.Next.type.121 = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.d83: %Iterate.type = facet_value %ConstRange, (%Iterate.impl_witness.a61) [concrete]
// CHECK:STDOUT:   %facet_value.227: %Iterate_where.type.ec1 = facet_value %ConstRange, (%Iterate.impl_witness.a61) [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.7db: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.b2e) [concrete]
// CHECK:STDOUT:   %.55e: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.7db, %Iterate.facet.b2e [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn.bad: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.d98, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.cd6) [concrete]
// CHECK:STDOUT:   %complete_type.c28: <witness> = complete_type_witness %tuple.type.508 [concrete]
// CHECK:STDOUT:   %ptr.45c: type = ptr_type %tuple.type.508 [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.c02: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.b2e) [concrete]
// CHECK:STDOUT:   %.d4b: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.c02, %Iterate.facet.b2e [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn.4ca: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.d29, @R.as_type.as.Iterate.impl.Next(%facet_value.cd6) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.c6c: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.30f) [concrete]
// CHECK:STDOUT:   %.0a4: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.c6c, %Destroy.facet.30f [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.825: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.d83) [concrete]
// CHECK:STDOUT:   %.e89c: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.825, %Iterate.facet.d83 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn.e65: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.0b2, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.e88) [concrete]
// CHECK:STDOUT:   %complete_type.8d5: <witness> = complete_type_witness %tuple.type.69f [concrete]
// CHECK:STDOUT:   %ptr.c5c: type = ptr_type %tuple.type.69f [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.d4a: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.d83) [concrete]
// CHECK:STDOUT:   %.f6d: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.d4a, %Iterate.facet.d83 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn.bf1: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.bec, @R.as_type.as.Iterate.impl.Next(%facet_value.e88) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.7ec: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.e4c) [concrete]
// CHECK:STDOUT:   %.0e7: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.7ec, %Destroy.facet.e4c [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Core.import_ref.bb6: @Optional.%Optional.HasValue.type (%Optional.HasValue.type.e9e) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.HasValue (constants.%Optional.HasValue.6cd)]
// CHECK:STDOUT:   %Core.import_ref.daba: @Optional.%Optional.Get.type (%Optional.Get.type.bb9) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.Get (constants.%Optional.Get.fa1)]
// CHECK:STDOUT:   %Core.import_ref.0c6: type = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%DefaultOptionalStorage (constants.%DefaultOptionalStorage.d50)]
// CHECK:STDOUT:   %Core.import_ref.6d6: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None.type (%T.as_type.as.OptionalStorage.impl.None.type.f62) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None (constants.%T.as_type.as.OptionalStorage.impl.None.faf)]
// CHECK:STDOUT:   %Core.import_ref.6f3: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some.type (%T.as_type.as.OptionalStorage.impl.Some.type.973) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some (constants.%T.as_type.as.OptionalStorage.impl.Some.c3a)]
// CHECK:STDOUT:   %Core.import_ref.af2: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has.type (%T.as_type.as.OptionalStorage.impl.Has.type.d76) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has (constants.%T.as_type.as.OptionalStorage.impl.Has.aa4)]
// CHECK:STDOUT:   %Core.import_ref.e31: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get.type (%T.as_type.as.OptionalStorage.impl.Get.type.671) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get (constants.%T.as_type.as.OptionalStorage.impl.Get.a54)]
// CHECK:STDOUT:   %Core.import_ref.cea = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %OptionalStorage.impl_witness_table.199 = impl_witness_table (%Core.import_ref.0c6, %Core.import_ref.6d6, %Core.import_ref.6f3, %Core.import_ref.af2, %Core.import_ref.e31, %Core.import_ref.cea), @T.as_type.as.OptionalStorage.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.cd6: @Int.as.Copy.impl.%Int.as.Copy.impl.Op.type (%Int.as.Copy.impl.Op.type.ac8) = import_ref Core//prelude/types/int, loc{{\d+_\d+}}, loaded [symbolic = @Int.as.Copy.impl.%Int.as.Copy.impl.Op (constants.%Int.as.Copy.impl.Op.5e0)]
// CHECK:STDOUT:   %Copy.impl_witness_table.367 = impl_witness_table (%Core.import_ref.cd6), @Int.as.Copy.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.2a4: @From.as_type.as.ImplicitAs.impl.%From.as_type.as.ImplicitAs.impl.Convert.type (%From.as_type.as.ImplicitAs.impl.Convert.type.7fa) = import_ref Core//prelude/types/int, loc{{\d+_\d+}}, loaded [symbolic = @From.as_type.as.ImplicitAs.impl.%From.as_type.as.ImplicitAs.impl.Convert (constants.%From.as_type.as.ImplicitAs.impl.Convert.643)]
// CHECK:STDOUT:   %ImplicitAs.impl_witness_table.3b9 = impl_witness_table (%Core.import_ref.2a4), @From.as_type.as.ImplicitAs.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.301: %facet_type.f48 = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%facet_value (constants.%facet_value.194)]
// CHECK:STDOUT:   %Core.import_ref.89f: %Destroy.type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%Destroy.facet (constants.%Destroy.facet.593)]
// CHECK:STDOUT:   %Core.import_ref.940: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor.type (%R.as_type.as.Iterate.impl.NewCursor.type.127) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor (constants.%R.as_type.as.Iterate.impl.NewCursor.627)]
// CHECK:STDOUT:   %Core.import_ref.fe7: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next.type (%R.as_type.as.Iterate.impl.Next.type.d8f) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next (constants.%R.as_type.as.Iterate.impl.Next.c6d)]
// CHECK:STDOUT:   %Iterate.impl_witness_table.ccd = impl_witness_table (%Core.import_ref.301, %Core.import_ref.89f, %Core.import_ref.940, %Core.import_ref.fe7), @R.as_type.as.Iterate.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.098: @Int.as.AddAssignWith.impl.%Int.as.AddAssignWith.impl.Op.type.2 (%Int.as.AddAssignWith.impl.Op.type.a58fbe.1) = import_ref Core//prelude/types/int, loc{{\d+_\d+}}, loaded [symbolic = @Int.as.AddAssignWith.impl.%Int.as.AddAssignWith.impl.Op.2 (constants.%Int.as.AddAssignWith.impl.Op.45b360.1)]
// CHECK:STDOUT:   %AddAssignWith.impl_witness_table = impl_witness_table (%Core.import_ref.098), @Int.as.AddAssignWith.impl [concrete]
// CHECK:STDOUT:   %Core.Op.1b1: @Int.as.AddAssignWith.impl.%Int.as.AddAssignWith.impl.Op.type.1 (%Int.as.AddAssignWith.impl.Op.type.a58fbe.2) = import_ref Core//prelude/types/int, Op, loaded [symbolic = @Int.as.AddAssignWith.impl.%Int.as.AddAssignWith.impl.Op.1 (constants.%Int.as.AddAssignWith.impl.Op.45b360.2)]
// CHECK:STDOUT:   %Core.import_ref.47b: Core.IntLiteral = import_ref Core//prelude/types/int, loc{{\d+_\d+}}, loaded [symbolic = @Int.as.AnyInt.impl.%N (constants.%N.fe9)]
// CHECK:STDOUT:   %Core.import_ref.fd3: @Int.as.AnyInt.impl.%Int.as.AnyInt.impl.AsInt.type (%Int.as.AnyInt.impl.AsInt.type.80b) = import_ref Core//prelude/types/int, loc{{\d+_\d+}}, loaded [symbolic = @Int.as.AnyInt.impl.%Int.as.AnyInt.impl.AsInt (constants.%Int.as.AnyInt.impl.AsInt.23f)]
// CHECK:STDOUT:   %AnyInt.impl_witness_table = impl_witness_table (%Core.import_ref.47b, %Core.import_ref.fd3), @Int.as.AnyInt.impl [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Test(%R.loc30_10.2: %Iterate_where.type.ec1) {
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %Iterate.lookup_impl_witness: <witness> = lookup_impl_witness %R.loc30_10.1, @Iterate [symbolic = %Iterate.lookup_impl_witness (constants.%Iterate.lookup_impl_witness.18b)]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.loc30_55.1, (%Iterate.lookup_impl_witness) [symbolic = %Iterate.facet (constants.%Iterate.facet.353)]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.NewCursor.type (constants.%Iterate.WithSelf.NewCursor.type.8fb)]
// CHECK:STDOUT:   %.loc34_19.12: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type, %Iterate.facet [symbolic = %.loc34_19.12 (constants.%.985)]
// CHECK:STDOUT:   %impl.elem2.loc34_19.2: @Test.%.loc34_19.12 (%.985) = impl_witness_access %Iterate.lookup_impl_witness, element2 [symbolic = %impl.elem2.loc34_19.2 (constants.%impl.elem2.8ec)]
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.4: <specific function> = specific_impl_function %impl.elem2.loc34_19.2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic = %specific_impl_fn.loc34_19.4 (constants.%specific_impl_fn.9ca)]
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %ptr: type = ptr_type %as_type [symbolic = %ptr (constants.%ptr.2ef)]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.Next.type (constants.%Iterate.WithSelf.Next.type.830)]
// CHECK:STDOUT:   %.loc34_19.13: type = fn_type_with_self_type %Iterate.WithSelf.Next.type, %Iterate.facet [symbolic = %.loc34_19.13 (constants.%.f86)]
// CHECK:STDOUT:   %impl.elem3.loc34_19.2: @Test.%.loc34_19.13 (%.f86) = impl_witness_access %Iterate.lookup_impl_witness, element3 [symbolic = %impl.elem3.loc34_19.2 (constants.%impl.elem3.5f7)]
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.5: <specific function> = specific_impl_function %impl.elem3.loc34_19.2, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic = %specific_impl_fn.loc34_19.5 (constants.%specific_impl_fn.9a8)]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1) [symbolic = %Destroy.WithSelf.Op.type (constants.%Destroy.WithSelf.Op.type.71c)]
// CHECK:STDOUT:   %.loc34_19.14: type = fn_type_with_self_type %Destroy.WithSelf.Op.type, %impl.elem1 [symbolic = %.loc34_19.14 (constants.%.fa0)]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness: <witness> = lookup_impl_witness %impl.elem1, @Destroy [symbolic = %Destroy.lookup_impl_witness (constants.%Destroy.lookup_impl_witness.d26)]
// CHECK:STDOUT:   %impl.elem0.loc34_19.2: @Test.%.loc34_19.14 (%.fa0) = impl_witness_access %Destroy.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc34_19.2 (constants.%impl.elem0.544)]
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.6: <specific function> = specific_impl_function %impl.elem0.loc34_19.2, @Destroy.WithSelf.Op(%impl.elem1) [symbolic = %specific_impl_fn.loc34_19.6 (constants.%specific_impl_fn.fa9)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%r.param: @Test.%R.as_type.loc30_55.1 (%R.as_type.a02)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:     name_binding_decl {
// CHECK:STDOUT:       %i.patt: %pattern_type.6b6 = value_binding_pattern i [concrete]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %r.ref: @Test.%R.as_type.loc30_55.1 (%R.as_type.a02) = name_ref r, %r
// CHECK:STDOUT:     %impl.elem2.loc34_19.1: @Test.%.loc34_19.12 (%.985) = impl_witness_access constants.%Iterate.lookup_impl_witness.18b, element2 [symbolic = %impl.elem2.loc34_19.2 (constants.%impl.elem2.8ec)]
// CHECK:STDOUT:     %bound_method.loc34_19.1: <bound method> = bound_method %r.ref, %impl.elem2.loc34_19.1
// CHECK:STDOUT:     %specific_impl_fn.loc34_19.1: <specific function> = specific_impl_function %impl.elem2.loc34_19.1, @Iterate.WithSelf.NewCursor(constants.%Iterate.facet.353) [symbolic = %specific_impl_fn.loc34_19.4 (constants.%specific_impl_fn.9ca)]
// CHECK:STDOUT:     %bound_method.loc34_19.2: <bound method> = bound_method %r.ref, %specific_impl_fn.loc34_19.1
// CHECK:STDOUT:     %var: ref @Test.%as_type (%as_type.c8a) = var invalid
// CHECK:STDOUT:     %Iterate.WithSelf.NewCursor.call: init @Test.%as_type (%as_type.c8a) to %var = call %bound_method.loc34_19.2(%r.ref)
// CHECK:STDOUT:     assign %var, %Iterate.WithSelf.NewCursor.call
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.next:
// CHECK:STDOUT:     %addr: @Test.%ptr (%ptr.2ef) = addr_of %var
// CHECK:STDOUT:     %impl.elem3.loc34_19.1: @Test.%.loc34_19.13 (%.f86) = impl_witness_access constants.%Iterate.lookup_impl_witness.18b, element3 [symbolic = %impl.elem3.loc34_19.2 (constants.%impl.elem3.5f7)]
// CHECK:STDOUT:     %bound_method.loc34_19.3: <bound method> = bound_method %r.ref, %impl.elem3.loc34_19.1
// CHECK:STDOUT:     %.loc34_19.1: %Destroy.type = converted constants.%as_type.c8a, constants.%impl.elem1.295 [symbolic = %impl.elem1 (constants.%impl.elem1.295)]
// CHECK:STDOUT:     %specific_impl_fn.loc34_19.2: <specific function> = specific_impl_function %impl.elem3.loc34_19.1, @Iterate.WithSelf.Next(constants.%Iterate.facet.353) [symbolic = %specific_impl_fn.loc34_19.5 (constants.%specific_impl_fn.9a8)]
// CHECK:STDOUT:     %bound_method.loc34_19.4: <bound method> = bound_method %r.ref, %specific_impl_fn.loc34_19.2
// CHECK:STDOUT:     %.loc34_19.2: ref %Optional.a23 = temporary_storage
// CHECK:STDOUT:     %Iterate.WithSelf.Next.call: init %Optional.a23 to %.loc34_19.2 = call %bound_method.loc34_19.4(%r.ref, %addr)
// CHECK:STDOUT:     %.loc34_19.3: ref %Optional.a23 = temporary %.loc34_19.2, %Iterate.WithSelf.Next.call
// CHECK:STDOUT:     %.loc34_19.4: %Optional.HasValue.type.560 = specific_constant imports.%Core.import_ref.bb6, @Optional(constants.%OptionalStorage.facet.563) [concrete = constants.%Optional.HasValue.bef]
// CHECK:STDOUT:     %HasValue.ref: %Optional.HasValue.type.560 = name_ref HasValue, %.loc34_19.4 [concrete = constants.%Optional.HasValue.bef]
// CHECK:STDOUT:     %Optional.HasValue.bound: <bound method> = bound_method %.loc34_19.3, %HasValue.ref
// CHECK:STDOUT:     %Optional.HasValue.specific_fn: <specific function> = specific_function %HasValue.ref, @Optional.HasValue(constants.%OptionalStorage.facet.563) [concrete = constants.%Optional.HasValue.specific_fn]
// CHECK:STDOUT:     %bound_method.loc34_19.5: <bound method> = bound_method %.loc34_19.3, %Optional.HasValue.specific_fn
// CHECK:STDOUT:     %.loc34_19.5: %Optional.a23 = acquire_value %.loc34_19.3
// CHECK:STDOUT:     %Optional.HasValue.call: init bool = call %bound_method.loc34_19.5(%.loc34_19.5)
// CHECK:STDOUT:     %.loc34_19.6: bool = value_of_initializer %Optional.HasValue.call
// CHECK:STDOUT:     %.loc34_19.7: bool = converted %Optional.HasValue.call, %.loc34_19.6
// CHECK:STDOUT:     if %.loc34_19.7 br !for.body else br !for.done
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.body:
// CHECK:STDOUT:     %.loc34_19.8: %Optional.Get.type.11a = specific_constant imports.%Core.import_ref.daba, @Optional(constants.%OptionalStorage.facet.563) [concrete = constants.%Optional.Get.0ee]
// CHECK:STDOUT:     %Get.ref: %Optional.Get.type.11a = name_ref Get, %.loc34_19.8 [concrete = constants.%Optional.Get.0ee]
// CHECK:STDOUT:     %Optional.Get.bound: <bound method> = bound_method %.loc34_19.3, %Get.ref
// CHECK:STDOUT:     %Optional.Get.specific_fn: <specific function> = specific_function %Get.ref, @Optional.Get(constants.%OptionalStorage.facet.563) [concrete = constants.%Optional.Get.specific_fn]
// CHECK:STDOUT:     %bound_method.loc34_19.6: <bound method> = bound_method %.loc34_19.3, %Optional.Get.specific_fn
// CHECK:STDOUT:     %.loc34_19.9: %Optional.a23 = acquire_value %.loc34_19.3
// CHECK:STDOUT:     %Optional.Get.call: init %i32 = call %bound_method.loc34_19.6(%.loc34_19.9)
// CHECK:STDOUT:     %i32.loc34: type = type_literal constants.%i32 [concrete = constants.%i32]
// CHECK:STDOUT:     %.loc34_19.10: %i32 = value_of_initializer %Optional.Get.call
// CHECK:STDOUT:     %.loc34_19.11: %i32 = converted %Optional.Get.call, %.loc34_19.10
// CHECK:STDOUT:     %i: %i32 = value_binding i, %.loc34_19.11
// CHECK:STDOUT:     %sum.ref: ref %i32 = name_ref sum, %sum
// CHECK:STDOUT:     %i.ref: %i32 = name_ref i, %i
// CHECK:STDOUT:     %impl.elem0.loc35: %.98a = impl_witness_access constants.%AddAssignWith.impl_witness.ccf, element0 [concrete = constants.%Int.as.AddAssignWith.impl.Op.83e130.2]
// CHECK:STDOUT:     %bound_method.loc35_9.1: <bound method> = bound_method %sum.ref, %impl.elem0.loc35
// CHECK:STDOUT:     %specific_fn.loc35: <specific function> = specific_function %impl.elem0.loc35, @Int.as.AddAssignWith.impl.Op.1(constants.%int_32, constants.%ImplicitAs.facet.640) [concrete = constants.%Int.as.AddAssignWith.impl.Op.specific_fn.80c75c.1]
// CHECK:STDOUT:     %bound_method.loc35_9.2: <bound method> = bound_method %sum.ref, %specific_fn.loc35
// CHECK:STDOUT:     %.loc35: %Int.as.AddAssignWith.impl.Op.type.a94901.1 = specific_constant imports.%Core.Op.1b1, @Int.as.AddAssignWith.impl(constants.%int_32, constants.%ImplicitAs.facet.640) [concrete = constants.%Int.as.AddAssignWith.impl.Op.83e130.1]
// CHECK:STDOUT:     %Op.ref: %Int.as.AddAssignWith.impl.Op.type.a94901.1 = name_ref Op, %.loc35 [concrete = constants.%Int.as.AddAssignWith.impl.Op.83e130.1]
// CHECK:STDOUT:     %Int.as.AddAssignWith.impl.Op.bound: <bound method> = bound_method %sum.ref, %Op.ref
// CHECK:STDOUT:     %Int.as.AddAssignWith.impl.Op.specific_fn: <specific function> = specific_function %Op.ref, @Int.as.AddAssignWith.impl.Op.2(constants.%int_32, constants.%ImplicitAs.facet.640) [concrete = constants.%Int.as.AddAssignWith.impl.Op.specific_fn.80c75c.2]
// CHECK:STDOUT:     %bound_method.loc35_9.3: <bound method> = bound_method %sum.ref, %Int.as.AddAssignWith.impl.Op.specific_fn
// CHECK:STDOUT:     %Int.as.AddAssignWith.impl.Op.call: init %empty_tuple.type = call %bound_method.loc35_9.3(%sum.ref, %i.ref)
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.done:
// CHECK:STDOUT:     %Destroy.Op.bound.loc34: <bound method> = bound_method %.loc34_19.3, constants.%Destroy.Op.1a2547.8
// CHECK:STDOUT:     %Destroy.Op.call.loc34: init %empty_tuple.type = call %Destroy.Op.bound.loc34(%.loc34_19.3)
// CHECK:STDOUT:     %impl.elem0.loc34_19.1: @Test.%.loc34_19.14 (%.fa0) = impl_witness_access constants.%Destroy.lookup_impl_witness.d26, element0 [symbolic = %impl.elem0.loc34_19.2 (constants.%impl.elem0.544)]
// CHECK:STDOUT:     %bound_method.loc34_19.7: <bound method> = bound_method %var, %impl.elem0.loc34_19.1
// CHECK:STDOUT:     %specific_impl_fn.loc34_19.3: <specific function> = specific_impl_function %impl.elem0.loc34_19.1, @Destroy.WithSelf.Op(constants.%impl.elem1.295) [symbolic = %specific_impl_fn.loc34_19.6 (constants.%specific_impl_fn.fa9)]
// CHECK:STDOUT:     %bound_method.loc34_19.8: <bound method> = bound_method %var, %specific_impl_fn.loc34_19.3
// CHECK:STDOUT:     %Destroy.WithSelf.Op.call: init %empty_tuple.type = call %bound_method.loc34_19.8(%var)
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc34_19.1(%self.param: ref %MaybeUnformed.023) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc34_19.2(%self.param: ref bool) = "no_op";
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc34_19.3(%self.param: ref %struct_type.value.has_value.ad0) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc34_19.4(%self.param: ref %DefaultOptionalStorage.970) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc34_19.5(%self.param: ref %Optional.a23) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%R.869) {
// CHECK:STDOUT:   %R.loc30_10.1 => constants.%R.869
// CHECK:STDOUT:   %R.as_type.loc30_55.1 => constants.%R.as_type.a02
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.b2da
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.8de) {
// CHECK:STDOUT:   %R.loc30_10.1 => constants.%facet_value.8de
// CHECK:STDOUT:   %R.as_type.loc30_55.1 => constants.%MutableRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.e635
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc30 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.b92
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.b2e
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.7db
// CHECK:STDOUT:   %.loc34_19.12 => constants.%.55e
// CHECK:STDOUT:   %impl.elem2.loc34_19.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.d98
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn.bad
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.30f
// CHECK:STDOUT:   %as_type => constants.%tuple.type.508
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.c28
// CHECK:STDOUT:   %ptr => constants.%ptr.45c
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.c02
// CHECK:STDOUT:   %.loc34_19.13 => constants.%.d4b
// CHECK:STDOUT:   %impl.elem3.loc34_19.2 => constants.%R.as_type.as.Iterate.impl.Next.d29
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn.4ca
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.c6c
// CHECK:STDOUT:   %.loc34_19.14 => constants.%.0a4
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.9
// CHECK:STDOUT:   %impl.elem0.loc34_19.2 => constants.%Destroy.Op.1a2547.9
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.6 => constants.%Destroy.Op.1a2547.9
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.227) {
// CHECK:STDOUT:   %R.loc30_10.1 => constants.%facet_value.227
// CHECK:STDOUT:   %R.as_type.loc30_55.1 => constants.%ConstRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.0ba
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc30 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.a61
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.d83
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.825
// CHECK:STDOUT:   %.loc34_19.12 => constants.%.e89c
// CHECK:STDOUT:   %impl.elem2.loc34_19.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.0b2
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn.e65
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.e4c
// CHECK:STDOUT:   %as_type => constants.%tuple.type.69f
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.8d5
// CHECK:STDOUT:   %ptr => constants.%ptr.c5c
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.d4a
// CHECK:STDOUT:   %.loc34_19.13 => constants.%.f6d
// CHECK:STDOUT:   %impl.elem3.loc34_19.2 => constants.%R.as_type.as.Iterate.impl.Next.bec
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn.bf1
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.7ec
// CHECK:STDOUT:   %.loc34_19.14 => constants.%.0e7
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.10
// CHECK:STDOUT:   %impl.elem0.loc34_19.2 => constants.%Destroy.Op.1a2547.10
// CHECK:STDOUT:   %specific_impl_fn.loc34_19.6 => constants.%Destroy.Op.1a2547.10
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: --- methods_return_different_types.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Iterate.type: type = facet_type <@Iterate> [concrete]
// CHECK:STDOUT:   %OptionalStorage.type: type = facet_type <@OptionalStorage> [concrete]
// CHECK:STDOUT:   %Destroy.type: type = facet_type <@Destroy> [concrete]
// CHECK:STDOUT:   %facet_type: type = facet_type <@Destroy & @Copy> [concrete]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [concrete]
// CHECK:STDOUT:   %T.220: %OptionalStorage.type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Optional.Get.type.bb9: type = fn_type @Optional.Get, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.Get.fa1: %Optional.Get.type.bb9 = struct_value () [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.e9e: type = fn_type @Optional.HasValue, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.6cd: %Optional.HasValue.type.e9e = struct_value () [symbolic]
// CHECK:STDOUT:   %T.283: %facet_type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.d50: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.type.671: type = fn_type @T.as_type.as.OptionalStorage.impl.Get, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.a54: %T.as_type.as.OptionalStorage.impl.Get.type.671 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.type.d76: type = fn_type @T.as_type.as.OptionalStorage.impl.Has, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.aa4: %T.as_type.as.OptionalStorage.impl.Has.type.d76 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.type.973: type = fn_type @T.as_type.as.OptionalStorage.impl.Some, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.c3a: %T.as_type.as.OptionalStorage.impl.Some.type.973 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.type.f62: type = fn_type @T.as_type.as.OptionalStorage.impl.None, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.faf: %T.as_type.as.OptionalStorage.impl.None.type.f62 = struct_value () [symbolic]
// CHECK:STDOUT:   %.Self.0.500: %Iterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.1d8: <witness> = lookup_impl_witness %.Self.0.500, @Iterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.294: %facet_type = impl_witness_access %Iterate.lookup_impl_witness.1d8, element0 [symbolic_self]
// CHECK:STDOUT:   %ValueType: type = class_type @ValueType [concrete]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [concrete]
// CHECK:STDOUT:   %complete_type.357: <witness> = complete_type_witness %empty_struct_type [concrete]
// CHECK:STDOUT:   %pattern_type.e9f: type = pattern_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor.type: type = fn_type @ValueType.cpp_destructor [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor: %ValueType.cpp_destructor.type = struct_value () [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.83af6e.1: type = fn_type @ValueType.Op.1 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4dca31.1: %ValueType.Op.type.83af6e.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.e7a31c.1: <witness> = custom_witness (%ValueType.Op.4dca31.1), @Destroy [concrete]
// CHECK:STDOUT:   %const.243: type = const_type %ValueType [concrete]
// CHECK:STDOUT:   %ptr.6bf: type = ptr_type %const.243 [concrete]
// CHECK:STDOUT:   %ptr.a3d: type = ptr_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.83af6e.2: type = fn_type @ValueType.Op.2 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4dca31.2: %ValueType.Op.type.83af6e.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.d0da43.1: <witness> = custom_witness (%ValueType.Op.4dca31.2), @Copy [concrete]
// CHECK:STDOUT:   %facet_value.bf1: %facet_type = facet_value %ValueType, (%custom_witness.e7a31c.1, %custom_witness.d0da43.1) [concrete]
// CHECK:STDOUT:   %Iterate_where.type.502: type = facet_type <@Iterate where %impl.elem0.294 = %facet_value.bf1> [concrete]
// CHECK:STDOUT:   %R.0bd: %Iterate_where.type.502 = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %R.as_type.f55: type = facet_access_type %R.0bd [symbolic]
// CHECK:STDOUT:   %pattern_type.d2d: type = pattern_type %R.as_type.f55 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.type: type = facet_type <@CppRangeForIterate> [concrete]
// CHECK:STDOUT:   %.Self.0.aed: %CppRangeForIterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.f6b: <witness> = lookup_impl_witness %.Self.0.aed, @CppRangeForIterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.b73: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element0 [symbolic_self]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.595: <witness> = lookup_impl_witness %impl.elem0.b73, @CppUnsafeDeref [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.a2f: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.595, element0 [symbolic_self]
// CHECK:STDOUT:   %impl.elem1.228: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element1 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate_where.type: type = facet_type <@CppRangeForIterate where %impl.elem0.b73 impls @Destroy and %impl.elem0.b73 impls @Copy and %impl.elem0.b73 impls @CppUnsafeDeref and %impl.elem0.b73 impls @EqWith, @EqWith(%impl.elem1.228) and %impl.elem0.b73 impls @Inc and %impl.elem0.a2f impls @Destroy and %impl.elem0.a2f impls @Copy and %impl.elem1.228 impls @Destroy and %impl.elem1.228 impls @Copy> [concrete]
// CHECK:STDOUT:   %R.39b: %CppRangeForIterate_where.type = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.7e2712.2: <witness> = lookup_impl_witness %R.39b, @CppRangeForIterate [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a0bff.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element1 [symbolic]
// CHECK:STDOUT:   %impl.elem0.73eb7f.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element0 [symbolic]
// CHECK:STDOUT:   %tuple.type.3cf: type = tuple_type (%impl.elem0.73eb7f.2, %impl.elem1.7a0bff.2) [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.69f: <witness> = lookup_impl_witness %tuple.type.3cf, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.facet.593: %Destroy.type = facet_value %tuple.type.3cf, (%Destroy.lookup_impl_witness.69f) [symbolic]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.aa7: <witness> = lookup_impl_witness %impl.elem0.73eb7f.2, @CppUnsafeDeref [symbolic]
// CHECK:STDOUT:   %impl.elem0.af7: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.aa7, element0 [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.ec3: <witness> = lookup_impl_witness %impl.elem0.af7, @Destroy [symbolic]
// CHECK:STDOUT:   %Copy.lookup_impl_witness.a7a: <witness> = lookup_impl_witness %impl.elem0.af7, @Copy [symbolic]
// CHECK:STDOUT:   %facet_value.194: %facet_type = facet_value %impl.elem0.af7, (%Destroy.lookup_impl_witness.ec3, %Copy.lookup_impl_witness.a7a) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.d8f: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c6d: %R.as_type.as.Iterate.impl.Next.type.d8f = struct_value () [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.127: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.627: %R.as_type.as.Iterate.impl.NewCursor.type.127 = struct_value () [symbolic]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.06b: <witness> = lookup_impl_witness %R.0bd, @Iterate [symbolic]
// CHECK:STDOUT:   %Iterate.facet.dbf: %Iterate.type = facet_value %R.as_type.f55, (%Iterate.lookup_impl_witness.06b) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.1b1: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.dbf) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.705: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.dbf) [symbolic]
// CHECK:STDOUT:   %.1c2: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.1b1, %Iterate.facet.dbf [symbolic]
// CHECK:STDOUT:   %impl.elem2.49b: %.1c2 = impl_witness_access %Iterate.lookup_impl_witness.06b, element2 [symbolic]
// CHECK:STDOUT:   %impl.elem1.3cf: %Destroy.type = impl_witness_access %Iterate.lookup_impl_witness.06b, element1 [symbolic]
// CHECK:STDOUT:   %as_type.dbb: type = facet_access_type %impl.elem1.3cf [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.6f3: <specific function> = specific_impl_function %impl.elem2.49b, @Iterate.WithSelf.NewCursor(%Iterate.facet.dbf) [symbolic]
// CHECK:STDOUT:   %ptr.bde: type = ptr_type %as_type.dbb [symbolic]
// CHECK:STDOUT:   %.bd3: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.705, %Iterate.facet.dbf [symbolic]
// CHECK:STDOUT:   %impl.elem3.d57: %.bd3 = impl_witness_access %Iterate.lookup_impl_witness.06b, element3 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.84c: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%facet_value.bf1) [concrete]
// CHECK:STDOUT:   %OptionalStorage.impl_witness.634: <witness> = impl_witness imports.%OptionalStorage.impl_witness_table.199, @T.as_type.as.OptionalStorage.impl(%facet_value.bf1) [concrete]
// CHECK:STDOUT:   %OptionalStorage.facet.ada: %OptionalStorage.type = facet_value %ValueType, (%OptionalStorage.impl_witness.634) [concrete]
// CHECK:STDOUT:   %Optional.f2f: type = class_type @Optional, @Optional(%OptionalStorage.facet.ada) [concrete]
// CHECK:STDOUT:   %specific_impl_fn.fca: <specific function> = specific_impl_function %impl.elem3.d57, @Iterate.WithSelf.Next(%Iterate.facet.dbf) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.436: type = fn_type @Optional.HasValue, @Optional(%OptionalStorage.facet.ada) [concrete]
// CHECK:STDOUT:   %Optional.HasValue.fbf: %Optional.HasValue.type.436 = struct_value () [concrete]
// CHECK:STDOUT:   %Optional.Get.type.f8c: type = fn_type @Optional.Get, @Optional(%OptionalStorage.facet.ada) [concrete]
// CHECK:STDOUT:   %Optional.Get.c12: %Optional.Get.type.f8c = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.facet.4e5: %Destroy.type = facet_value %ValueType, (%custom_witness.e7a31c.1) [concrete]
// CHECK:STDOUT:   %MaybeUnformed.02e: type = class_type @MaybeUnformed, @MaybeUnformed(%Destroy.facet.4e5) [concrete]
// CHECK:STDOUT:   %struct_type.value.has_value.761: type = struct_type {.value: %MaybeUnformed.02e, .has_value: bool} [concrete]
// CHECK:STDOUT:   %Optional.HasValue.specific_fn: <specific function> = specific_function %Optional.HasValue.fbf, @Optional.HasValue(%OptionalStorage.facet.ada) [concrete]
// CHECK:STDOUT:   %Optional.Get.specific_fn: <specific function> = specific_function %Optional.Get.c12, @Optional.Get(%OptionalStorage.facet.ada) [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator.type: type = fn_type @ValueType.cpp_operator [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator: %ValueType.cpp_operator.type = struct_value () [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.type: type = fn_type @operator_PlusEqual__carbon_thunk [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk: %operator_PlusEqual__carbon_thunk.type = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.6: type = fn_type @Destroy.Op.loc44_29.5 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.6: %Destroy.Op.type.1d8f74.6 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.b29: <witness> = lookup_impl_witness %impl.elem1.3cf, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.d9c: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1.3cf) [symbolic]
// CHECK:STDOUT:   %.98a: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.d9c, %impl.elem1.3cf [symbolic]
// CHECK:STDOUT:   %impl.elem0.81b: %.98a = impl_witness_access %Destroy.lookup_impl_witness.b29, element0 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.bf3: <specific function> = specific_impl_function %impl.elem0.81b, @Destroy.WithSelf.Op(%impl.elem1.3cf) [symbolic]
// CHECK:STDOUT:   %MutableRange: type = class_type @MutableRange [concrete]
// CHECK:STDOUT:   %pattern_type.e635: type = pattern_type %MutableRange [concrete]
// CHECK:STDOUT:   %ConstRange: type = class_type @ConstRange [concrete]
// CHECK:STDOUT:   %pattern_type.0ba: type = pattern_type %ConstRange [concrete]
// CHECK:STDOUT:   %Iterator.3ee: type = class_type @Iterator.1 [concrete]
// CHECK:STDOUT:   %Sentinel.9b2: type = class_type @Sentinel.1 [concrete]
// CHECK:STDOUT:   %MutableRange.Begin.type: type = fn_type @MutableRange.Begin [concrete]
// CHECK:STDOUT:   %MutableRange.Begin: %MutableRange.Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %MutableRange.End.type: type = fn_type @MutableRange.End [concrete]
// CHECK:STDOUT:   %MutableRange.End: %MutableRange.End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.6b6: <witness> = custom_witness (%Iterator.3ee, %Sentinel.9b2, %MutableRange.Begin, %MutableRange.End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.1: type = fn_type @Iterator.Op.1 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.1: %Iterator.Op.type.0aed5d.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.90a: <witness> = custom_witness (%ValueType, %Iterator.Op.a2a866.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.2: type = fn_type @Iterator.Op.2 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.2: %Iterator.Op.type.0aed5d.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.95581e.1: <witness> = custom_witness (%Iterator.Op.a2a866.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.3: type = fn_type @Iterator.Op.3 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.3: %Iterator.Op.type.0aed5d.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.1f52e9.1: <witness> = custom_witness (%Iterator.Op.a2a866.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type.ca8475.1: type = fn_type @Equal.1 [concrete]
// CHECK:STDOUT:   %Equal.285b15.1: %Equal.type.ca8475.1 = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type.53d9ee.1: type = fn_type @NotEqual.1 [concrete]
// CHECK:STDOUT:   %NotEqual.119263.1: %NotEqual.type.53d9ee.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.3e8: <witness> = custom_witness (%Equal.285b15.1, %NotEqual.119263.1), @EqWith, @EqWith(%Sentinel.9b2) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0aed5d.4: type = fn_type @Iterator.Op.4 [concrete]
// CHECK:STDOUT:   %Iterator.Op.a2a866.4: %Iterator.Op.type.0aed5d.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.444: <witness> = custom_witness (%Iterator.Op.a2a866.4), @Inc [concrete]
// CHECK:STDOUT:   %Sentinel.Op.type.0aed5d.1: type = fn_type @Sentinel.Op.1 [concrete]
// CHECK:STDOUT:   %Sentinel.Op.a2a866.1: %Sentinel.Op.type.0aed5d.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.95581e.2: <witness> = custom_witness (%Sentinel.Op.a2a866.1), @Destroy [concrete]
// CHECK:STDOUT:   %Sentinel.Op.type.0aed5d.2: type = fn_type @Sentinel.Op.2 [concrete]
// CHECK:STDOUT:   %Sentinel.Op.a2a866.2: %Sentinel.Op.type.0aed5d.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.1f52e9.2: <witness> = custom_witness (%Sentinel.Op.a2a866.2), @Copy [concrete]
// CHECK:STDOUT:   %facet_value.55a: %CppRangeForIterate_where.type = facet_value %MutableRange, (%custom_witness.e7a31c.1, %custom_witness.d0da43.1, %custom_witness.6b6, %custom_witness.95581e.1, %custom_witness.1f52e9.1, %custom_witness.90a, %custom_witness.3e8, %custom_witness.444, %custom_witness.95581e.2, %custom_witness.1f52e9.2) [concrete]
// CHECK:STDOUT:   %tuple.type.829: type = tuple_type (%Iterator.3ee, %Sentinel.9b2) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.7: type = fn_type @Destroy.Op.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.7: %Destroy.Op.type.1d8f74.7 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.7: <witness> = custom_witness (%Destroy.Op.1a2547.7), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.305: %Destroy.type = facet_value %tuple.type.829, (%custom_witness.df9cc1.7) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.af4: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.55a) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.ba0: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.55a) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.435: %R.as_type.as.Iterate.impl.NewCursor.type.ba0 = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.52b: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.55a) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.687: %R.as_type.as.Iterate.impl.Next.type.52b = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.cc7: %Iterate.type = facet_value %MutableRange, (%Iterate.impl_witness.af4) [concrete]
// CHECK:STDOUT:   %facet_value.c11: %Iterate_where.type.502 = facet_value %MutableRange, (%Iterate.impl_witness.af4) [concrete]
// CHECK:STDOUT:   %Iterator.260: type = class_type @Iterator.2 [concrete]
// CHECK:STDOUT:   %Sentinel.4c4: type = class_type @Sentinel.2 [concrete]
// CHECK:STDOUT:   %ConstRange.Begin.type: type = fn_type @ConstRange.Begin [concrete]
// CHECK:STDOUT:   %ConstRange.Begin: %ConstRange.Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %ConstRange.End.type: type = fn_type @ConstRange.End [concrete]
// CHECK:STDOUT:   %ConstRange.End: %ConstRange.End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.a03: <witness> = custom_witness (%Iterator.260, %Sentinel.4c4, %ConstRange.Begin, %ConstRange.End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.1: type = fn_type @Iterator.Op.5 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.1: %Iterator.Op.type.0f34b8.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.78b: <witness> = custom_witness (%ValueType, %Iterator.Op.1c3e4a.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.2: type = fn_type @Iterator.Op.6 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.2: %Iterator.Op.type.0f34b8.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.6e8a2e.1: <witness> = custom_witness (%Iterator.Op.1c3e4a.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.3: type = fn_type @Iterator.Op.7 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.3: %Iterator.Op.type.0f34b8.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.15091a.1: <witness> = custom_witness (%Iterator.Op.1c3e4a.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type.ca8475.2: type = fn_type @Equal.2 [concrete]
// CHECK:STDOUT:   %Equal.285b15.2: %Equal.type.ca8475.2 = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type.53d9ee.2: type = fn_type @NotEqual.2 [concrete]
// CHECK:STDOUT:   %NotEqual.119263.2: %NotEqual.type.53d9ee.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.c55: <witness> = custom_witness (%Equal.285b15.2, %NotEqual.119263.2), @EqWith, @EqWith(%Sentinel.4c4) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.0f34b8.4: type = fn_type @Iterator.Op.8 [concrete]
// CHECK:STDOUT:   %Iterator.Op.1c3e4a.4: %Iterator.Op.type.0f34b8.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.746: <witness> = custom_witness (%Iterator.Op.1c3e4a.4), @Inc [concrete]
// CHECK:STDOUT:   %Sentinel.Op.type.0f34b8.1: type = fn_type @Sentinel.Op.3 [concrete]
// CHECK:STDOUT:   %Sentinel.Op.1c3e4a.1: %Sentinel.Op.type.0f34b8.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.6e8a2e.2: <witness> = custom_witness (%Sentinel.Op.1c3e4a.1), @Destroy [concrete]
// CHECK:STDOUT:   %Sentinel.Op.type.0f34b8.2: type = fn_type @Sentinel.Op.4 [concrete]
// CHECK:STDOUT:   %Sentinel.Op.1c3e4a.2: %Sentinel.Op.type.0f34b8.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.15091a.2: <witness> = custom_witness (%Sentinel.Op.1c3e4a.2), @Copy [concrete]
// CHECK:STDOUT:   %facet_value.445: %CppRangeForIterate_where.type = facet_value %ConstRange, (%custom_witness.e7a31c.1, %custom_witness.d0da43.1, %custom_witness.a03, %custom_witness.6e8a2e.1, %custom_witness.15091a.1, %custom_witness.78b, %custom_witness.c55, %custom_witness.746, %custom_witness.6e8a2e.2, %custom_witness.15091a.2) [concrete]
// CHECK:STDOUT:   %tuple.type.99f: type = tuple_type (%Iterator.260, %Sentinel.4c4) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.8: type = fn_type @Destroy.Op.3 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.8: %Destroy.Op.type.1d8f74.8 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.8: <witness> = custom_witness (%Destroy.Op.1a2547.8), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.e08: %Destroy.type = facet_value %tuple.type.99f, (%custom_witness.df9cc1.8) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.534: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.445) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.010: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.445) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.d09: %R.as_type.as.Iterate.impl.NewCursor.type.010 = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.fca: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.445) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.dce: %R.as_type.as.Iterate.impl.Next.type.fca = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.f61: %Iterate.type = facet_value %ConstRange, (%Iterate.impl_witness.534) [concrete]
// CHECK:STDOUT:   %facet_value.877: %Iterate_where.type.502 = facet_value %ConstRange, (%Iterate.impl_witness.534) [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.7c9: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.cc7) [concrete]
// CHECK:STDOUT:   %.753: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.7c9, %Iterate.facet.cc7 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn.f09: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.435, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.55a) [concrete]
// CHECK:STDOUT:   %complete_type.94f: <witness> = complete_type_witness %tuple.type.829 [concrete]
// CHECK:STDOUT:   %ptr.d6b: type = ptr_type %tuple.type.829 [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.464: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.cc7) [concrete]
// CHECK:STDOUT:   %.010: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.464, %Iterate.facet.cc7 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn.5bb: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.687, @R.as_type.as.Iterate.impl.Next(%facet_value.55a) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.c89: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.305) [concrete]
// CHECK:STDOUT:   %.e8a: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.c89, %Destroy.facet.305 [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.f50: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.f61) [concrete]
// CHECK:STDOUT:   %.0be: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.f50, %Iterate.facet.f61 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn.749: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.d09, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.445) [concrete]
// CHECK:STDOUT:   %complete_type.dea: <witness> = complete_type_witness %tuple.type.99f [concrete]
// CHECK:STDOUT:   %ptr.2f7: type = ptr_type %tuple.type.99f [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.724: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.f61) [concrete]
// CHECK:STDOUT:   %.c98: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.724, %Iterate.facet.f61 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn.f0e: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.dce, @R.as_type.as.Iterate.impl.Next(%facet_value.445) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.e30: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.e08) [concrete]
// CHECK:STDOUT:   %.987: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.e30, %Destroy.facet.e08 [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Cpp: <namespace> = namespace file.%Cpp.import_cpp, [concrete] {
// CHECK:STDOUT:     .ValueType = %ValueType.decl
// CHECK:STDOUT:     .MutableRange = %MutableRange.decl
// CHECK:STDOUT:     .ConstRange = %ConstRange.decl
// CHECK:STDOUT:     import Cpp//...
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.bb6: @Optional.%Optional.HasValue.type (%Optional.HasValue.type.e9e) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.HasValue (constants.%Optional.HasValue.6cd)]
// CHECK:STDOUT:   %Core.import_ref.daba: @Optional.%Optional.Get.type (%Optional.Get.type.bb9) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.Get (constants.%Optional.Get.fa1)]
// CHECK:STDOUT:   %Core.import_ref.0c6: type = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%DefaultOptionalStorage (constants.%DefaultOptionalStorage.d50)]
// CHECK:STDOUT:   %Core.import_ref.6d6: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None.type (%T.as_type.as.OptionalStorage.impl.None.type.f62) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None (constants.%T.as_type.as.OptionalStorage.impl.None.faf)]
// CHECK:STDOUT:   %Core.import_ref.6f3: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some.type (%T.as_type.as.OptionalStorage.impl.Some.type.973) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some (constants.%T.as_type.as.OptionalStorage.impl.Some.c3a)]
// CHECK:STDOUT:   %Core.import_ref.af2: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has.type (%T.as_type.as.OptionalStorage.impl.Has.type.d76) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has (constants.%T.as_type.as.OptionalStorage.impl.Has.aa4)]
// CHECK:STDOUT:   %Core.import_ref.e31: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get.type (%T.as_type.as.OptionalStorage.impl.Get.type.671) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get (constants.%T.as_type.as.OptionalStorage.impl.Get.a54)]
// CHECK:STDOUT:   %Core.import_ref.cea = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %OptionalStorage.impl_witness_table.199 = impl_witness_table (%Core.import_ref.0c6, %Core.import_ref.6d6, %Core.import_ref.6f3, %Core.import_ref.af2, %Core.import_ref.e31, %Core.import_ref.cea), @T.as_type.as.OptionalStorage.impl [concrete]
// CHECK:STDOUT:   %ValueType.decl: type = class_decl @ValueType [concrete = constants.%ValueType] {} {}
// CHECK:STDOUT:   %ValueType.cpp_destructor.decl: %ValueType.cpp_destructor.type = fn_decl @ValueType.cpp_destructor [concrete = constants.%ValueType.cpp_destructor] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.301: %facet_type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%facet_value (constants.%facet_value.194)]
// CHECK:STDOUT:   %Core.import_ref.89f: %Destroy.type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%Destroy.facet (constants.%Destroy.facet.593)]
// CHECK:STDOUT:   %Core.import_ref.940: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor.type (%R.as_type.as.Iterate.impl.NewCursor.type.127) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor (constants.%R.as_type.as.Iterate.impl.NewCursor.627)]
// CHECK:STDOUT:   %Core.import_ref.fe7: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next.type (%R.as_type.as.Iterate.impl.Next.type.d8f) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next (constants.%R.as_type.as.Iterate.impl.Next.c6d)]
// CHECK:STDOUT:   %Iterate.impl_witness_table.ccd = impl_witness_table (%Core.import_ref.301, %Core.import_ref.89f, %Core.import_ref.940, %Core.import_ref.fe7), @R.as_type.as.Iterate.impl [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator.decl: %ValueType.cpp_operator.type = fn_decl @ValueType.cpp_operator [concrete = constants.%ValueType.cpp_operator] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.decl: %operator_PlusEqual__carbon_thunk.type = fn_decl @operator_PlusEqual__carbon_thunk [concrete = constants.%operator_PlusEqual__carbon_thunk] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %MutableRange.decl: type = class_decl @MutableRange [concrete = constants.%MutableRange] {} {}
// CHECK:STDOUT:   %ConstRange.decl: type = class_decl @ConstRange [concrete = constants.%ConstRange] {} {}
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Test(%R.loc40_10.2: %Iterate_where.type.502) {
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %Iterate.lookup_impl_witness: <witness> = lookup_impl_witness %R.loc40_10.1, @Iterate [symbolic = %Iterate.lookup_impl_witness (constants.%Iterate.lookup_impl_witness.06b)]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.loc40_69.1, (%Iterate.lookup_impl_witness) [symbolic = %Iterate.facet (constants.%Iterate.facet.dbf)]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.NewCursor.type (constants.%Iterate.WithSelf.NewCursor.type.1b1)]
// CHECK:STDOUT:   %.loc44_29.13: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type, %Iterate.facet [symbolic = %.loc44_29.13 (constants.%.1c2)]
// CHECK:STDOUT:   %impl.elem2.loc44_29.2: @Test.%.loc44_29.13 (%.1c2) = impl_witness_access %Iterate.lookup_impl_witness, element2 [symbolic = %impl.elem2.loc44_29.2 (constants.%impl.elem2.49b)]
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.4: <specific function> = specific_impl_function %impl.elem2.loc44_29.2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic = %specific_impl_fn.loc44_29.4 (constants.%specific_impl_fn.6f3)]
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %ptr: type = ptr_type %as_type [symbolic = %ptr (constants.%ptr.bde)]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.Next.type (constants.%Iterate.WithSelf.Next.type.705)]
// CHECK:STDOUT:   %.loc44_29.14: type = fn_type_with_self_type %Iterate.WithSelf.Next.type, %Iterate.facet [symbolic = %.loc44_29.14 (constants.%.bd3)]
// CHECK:STDOUT:   %impl.elem3.loc44_29.2: @Test.%.loc44_29.14 (%.bd3) = impl_witness_access %Iterate.lookup_impl_witness, element3 [symbolic = %impl.elem3.loc44_29.2 (constants.%impl.elem3.d57)]
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.5: <specific function> = specific_impl_function %impl.elem3.loc44_29.2, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic = %specific_impl_fn.loc44_29.5 (constants.%specific_impl_fn.fca)]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1) [symbolic = %Destroy.WithSelf.Op.type (constants.%Destroy.WithSelf.Op.type.d9c)]
// CHECK:STDOUT:   %.loc44_29.15: type = fn_type_with_self_type %Destroy.WithSelf.Op.type, %impl.elem1 [symbolic = %.loc44_29.15 (constants.%.98a)]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness: <witness> = lookup_impl_witness %impl.elem1, @Destroy [symbolic = %Destroy.lookup_impl_witness (constants.%Destroy.lookup_impl_witness.b29)]
// CHECK:STDOUT:   %impl.elem0.loc44_29.2: @Test.%.loc44_29.15 (%.98a) = impl_witness_access %Destroy.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc44_29.2 (constants.%impl.elem0.81b)]
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.6: <specific function> = specific_impl_function %impl.elem0.loc44_29.2, @Destroy.WithSelf.Op(%impl.elem1) [symbolic = %specific_impl_fn.loc44_29.6 (constants.%specific_impl_fn.bf3)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%r.param: ref @Test.%R.as_type.loc40_69.1 (%R.as_type.f55)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:     name_binding_decl {
// CHECK:STDOUT:       %i.patt: %pattern_type.e9f = value_binding_pattern i [concrete]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %r.ref: ref @Test.%R.as_type.loc40_69.1 (%R.as_type.f55) = name_ref r, %r
// CHECK:STDOUT:     %impl.elem2.loc44_29.1: @Test.%.loc44_29.13 (%.1c2) = impl_witness_access constants.%Iterate.lookup_impl_witness.06b, element2 [symbolic = %impl.elem2.loc44_29.2 (constants.%impl.elem2.49b)]
// CHECK:STDOUT:     %bound_method.loc44_29.1: <bound method> = bound_method %r.ref, %impl.elem2.loc44_29.1
// CHECK:STDOUT:     %specific_impl_fn.loc44_29.1: <specific function> = specific_impl_function %impl.elem2.loc44_29.1, @Iterate.WithSelf.NewCursor(constants.%Iterate.facet.dbf) [symbolic = %specific_impl_fn.loc44_29.4 (constants.%specific_impl_fn.6f3)]
// CHECK:STDOUT:     %bound_method.loc44_29.2: <bound method> = bound_method %r.ref, %specific_impl_fn.loc44_29.1
// CHECK:STDOUT:     %var: ref @Test.%as_type (%as_type.dbb) = var invalid
// CHECK:STDOUT:     %.loc44_28.1: @Test.%R.as_type.loc40_69.1 (%R.as_type.f55) = acquire_value %r.ref
// CHECK:STDOUT:     %Iterate.WithSelf.NewCursor.call: init @Test.%as_type (%as_type.dbb) to %var = call %bound_method.loc44_29.2(%.loc44_28.1)
// CHECK:STDOUT:     assign %var, %Iterate.WithSelf.NewCursor.call
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.next:
// CHECK:STDOUT:     %addr.loc44: @Test.%ptr (%ptr.bde) = addr_of %var
// CHECK:STDOUT:     %impl.elem3.loc44_29.1: @Test.%.loc44_29.14 (%.bd3) = impl_witness_access constants.%Iterate.lookup_impl_witness.06b, element3 [symbolic = %impl.elem3.loc44_29.2 (constants.%impl.elem3.d57)]
// CHECK:STDOUT:     %bound_method.loc44_29.3: <bound method> = bound_method %r.ref, %impl.elem3.loc44_29.1
// CHECK:STDOUT:     %.loc44_29.1: %Destroy.type = converted constants.%as_type.dbb, constants.%impl.elem1.3cf [symbolic = %impl.elem1 (constants.%impl.elem1.3cf)]
// CHECK:STDOUT:     %specific_impl_fn.loc44_29.2: <specific function> = specific_impl_function %impl.elem3.loc44_29.1, @Iterate.WithSelf.Next(constants.%Iterate.facet.dbf) [symbolic = %specific_impl_fn.loc44_29.5 (constants.%specific_impl_fn.fca)]
// CHECK:STDOUT:     %bound_method.loc44_29.4: <bound method> = bound_method %r.ref, %specific_impl_fn.loc44_29.2
// CHECK:STDOUT:     %.loc44_29.2: ref %Optional.f2f = temporary_storage
// CHECK:STDOUT:     %.loc44_28.2: @Test.%R.as_type.loc40_69.1 (%R.as_type.f55) = acquire_value %r.ref
// CHECK:STDOUT:     %Iterate.WithSelf.Next.call: init %Optional.f2f to %.loc44_29.2 = call %bound_method.loc44_29.4(%.loc44_28.2, %addr.loc44)
// CHECK:STDOUT:     %.loc44_29.3: ref %Optional.f2f = temporary %.loc44_29.2, %Iterate.WithSelf.Next.call
// CHECK:STDOUT:     %.loc44_29.4: %Optional.HasValue.type.436 = specific_constant imports.%Core.import_ref.bb6, @Optional(constants.%OptionalStorage.facet.ada) [concrete = constants.%Optional.HasValue.fbf]
// CHECK:STDOUT:     %HasValue.ref: %Optional.HasValue.type.436 = name_ref HasValue, %.loc44_29.4 [concrete = constants.%Optional.HasValue.fbf]
// CHECK:STDOUT:     %Optional.HasValue.bound: <bound method> = bound_method %.loc44_29.3, %HasValue.ref
// CHECK:STDOUT:     %Optional.HasValue.specific_fn: <specific function> = specific_function %HasValue.ref, @Optional.HasValue(constants.%OptionalStorage.facet.ada) [concrete = constants.%Optional.HasValue.specific_fn]
// CHECK:STDOUT:     %bound_method.loc44_29.5: <bound method> = bound_method %.loc44_29.3, %Optional.HasValue.specific_fn
// CHECK:STDOUT:     %.loc44_29.5: %Optional.f2f = acquire_value %.loc44_29.3
// CHECK:STDOUT:     %Optional.HasValue.call: init bool = call %bound_method.loc44_29.5(%.loc44_29.5)
// CHECK:STDOUT:     %.loc44_29.6: bool = value_of_initializer %Optional.HasValue.call
// CHECK:STDOUT:     %.loc44_29.7: bool = converted %Optional.HasValue.call, %.loc44_29.6
// CHECK:STDOUT:     if %.loc44_29.7 br !for.body else br !for.done
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.body:
// CHECK:STDOUT:     %.loc44_29.8: %Optional.Get.type.f8c = specific_constant imports.%Core.import_ref.daba, @Optional(constants.%OptionalStorage.facet.ada) [concrete = constants.%Optional.Get.c12]
// CHECK:STDOUT:     %Get.ref: %Optional.Get.type.f8c = name_ref Get, %.loc44_29.8 [concrete = constants.%Optional.Get.c12]
// CHECK:STDOUT:     %Optional.Get.bound: <bound method> = bound_method %.loc44_29.3, %Get.ref
// CHECK:STDOUT:     %Optional.Get.specific_fn: <specific function> = specific_function %Get.ref, @Optional.Get(constants.%OptionalStorage.facet.ada) [concrete = constants.%Optional.Get.specific_fn]
// CHECK:STDOUT:     %bound_method.loc44_29.6: <bound method> = bound_method %.loc44_29.3, %Optional.Get.specific_fn
// CHECK:STDOUT:     %.loc44_29.9: ref %ValueType = temporary_storage
// CHECK:STDOUT:     %.loc44_29.10: %Optional.f2f = acquire_value %.loc44_29.3
// CHECK:STDOUT:     %Optional.Get.call: init %ValueType to %.loc44_29.9 = call %bound_method.loc44_29.6(%.loc44_29.10)
// CHECK:STDOUT:     %.loc44_14: type = splice_block %ValueType.ref.loc44 [concrete = constants.%ValueType] {
// CHECK:STDOUT:       %Cpp.ref.loc44: <namespace> = name_ref Cpp, imports.%Cpp [concrete = imports.%Cpp]
// CHECK:STDOUT:       %ValueType.ref.loc44: type = name_ref ValueType, imports.%ValueType.decl [concrete = constants.%ValueType]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %.loc44_29.11: ref %ValueType = temporary %.loc44_29.9, %Optional.Get.call
// CHECK:STDOUT:     %.loc44_29.12: %ValueType = acquire_value %.loc44_29.11
// CHECK:STDOUT:     %i: %ValueType = value_binding i, %.loc44_29.12
// CHECK:STDOUT:     %sum.ref: ref %ValueType = name_ref sum, %sum
// CHECK:STDOUT:     %i.ref: %ValueType = name_ref i, %i
// CHECK:STDOUT:     %ValueType.cpp_operator.bound: <bound method> = bound_method %sum.ref, imports.%ValueType.cpp_operator.decl
// CHECK:STDOUT:     %.loc45_12: ref %ValueType = value_as_ref %i.ref
// CHECK:STDOUT:     %addr.loc45: %ptr.a3d = addr_of %.loc45_12
// CHECK:STDOUT:     %.loc45_9.1: %ptr.6bf = as_compatible %addr.loc45
// CHECK:STDOUT:     %.loc45_9.2: %ptr.6bf = converted %addr.loc45, %.loc45_9.1
// CHECK:STDOUT:     %operator_PlusEqual__carbon_thunk.call: ref %ValueType = call imports.%operator_PlusEqual__carbon_thunk.decl(%sum.ref, %.loc45_9.2)
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.done:
// CHECK:STDOUT:     %ValueType.Op.bound.loc44: <bound method> = bound_method %.loc44_29.11, constants.%ValueType.Op.4dca31.1
// CHECK:STDOUT:     %Op.ref.loc44: %ValueType.cpp_destructor.type = name_ref Op, imports.%ValueType.cpp_destructor.decl [concrete = constants.%ValueType.cpp_destructor]
// CHECK:STDOUT:     %ValueType.cpp_destructor.bound.loc44: <bound method> = bound_method %.loc44_29.11, %Op.ref.loc44
// CHECK:STDOUT:     %ValueType.cpp_destructor.call.loc44: init %empty_tuple.type = call %ValueType.cpp_destructor.bound.loc44(%.loc44_29.11)
// CHECK:STDOUT:     %Destroy.Op.bound: <bound method> = bound_method %.loc44_29.3, constants.%Destroy.Op.1a2547.6
// CHECK:STDOUT:     %Destroy.Op.call: init %empty_tuple.type = call %Destroy.Op.bound(%.loc44_29.3)
// CHECK:STDOUT:     %impl.elem0.loc44_29.1: @Test.%.loc44_29.15 (%.98a) = impl_witness_access constants.%Destroy.lookup_impl_witness.b29, element0 [symbolic = %impl.elem0.loc44_29.2 (constants.%impl.elem0.81b)]
// CHECK:STDOUT:     %bound_method.loc44_29.7: <bound method> = bound_method %var, %impl.elem0.loc44_29.1
// CHECK:STDOUT:     %specific_impl_fn.loc44_29.3: <specific function> = specific_impl_function %impl.elem0.loc44_29.1, @Destroy.WithSelf.Op(constants.%impl.elem1.3cf) [symbolic = %specific_impl_fn.loc44_29.6 (constants.%specific_impl_fn.bf3)]
// CHECK:STDOUT:     %bound_method.loc44_29.8: <bound method> = bound_method %var, %specific_impl_fn.loc44_29.3
// CHECK:STDOUT:     %Destroy.WithSelf.Op.call: init %empty_tuple.type = call %bound_method.loc44_29.8(%var)
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc44_29.1(%self.param: ref %MaybeUnformed.02e) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc44_29.2(%self.param: ref bool) = "no_op";
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc44_29.3(%self.param: ref %struct_type.value.has_value.761) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc44_29.4(%self.param: ref %DefaultOptionalStorage.84c) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc44_29.5(%self.param: ref %Optional.f2f) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%R.0bd) {
// CHECK:STDOUT:   %R.loc40_10.1 => constants.%R.0bd
// CHECK:STDOUT:   %R.as_type.loc40_69.1 => constants.%R.as_type.f55
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.d2d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.c11) {
// CHECK:STDOUT:   %R.loc40_10.1 => constants.%facet_value.c11
// CHECK:STDOUT:   %R.as_type.loc40_69.1 => constants.%MutableRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.e635
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc40 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.af4
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.cc7
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.7c9
// CHECK:STDOUT:   %.loc44_29.13 => constants.%.753
// CHECK:STDOUT:   %impl.elem2.loc44_29.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.435
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn.f09
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.305
// CHECK:STDOUT:   %as_type => constants.%tuple.type.829
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.94f
// CHECK:STDOUT:   %ptr => constants.%ptr.d6b
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.464
// CHECK:STDOUT:   %.loc44_29.14 => constants.%.010
// CHECK:STDOUT:   %impl.elem3.loc44_29.2 => constants.%R.as_type.as.Iterate.impl.Next.687
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn.5bb
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.c89
// CHECK:STDOUT:   %.loc44_29.15 => constants.%.e8a
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.7
// CHECK:STDOUT:   %impl.elem0.loc44_29.2 => constants.%Destroy.Op.1a2547.7
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.6 => constants.%Destroy.Op.1a2547.7
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.877) {
// CHECK:STDOUT:   %R.loc40_10.1 => constants.%facet_value.877
// CHECK:STDOUT:   %R.as_type.loc40_69.1 => constants.%ConstRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.0ba
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc40 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.534
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.f61
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.f50
// CHECK:STDOUT:   %.loc44_29.13 => constants.%.0be
// CHECK:STDOUT:   %impl.elem2.loc44_29.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.d09
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn.749
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.e08
// CHECK:STDOUT:   %as_type => constants.%tuple.type.99f
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.dea
// CHECK:STDOUT:   %ptr => constants.%ptr.2f7
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.724
// CHECK:STDOUT:   %.loc44_29.14 => constants.%.c98
// CHECK:STDOUT:   %impl.elem3.loc44_29.2 => constants.%R.as_type.as.Iterate.impl.Next.dce
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn.f0e
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.e30
// CHECK:STDOUT:   %.loc44_29.15 => constants.%.987
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.8
// CHECK:STDOUT:   %impl.elem0.loc44_29.2 => constants.%Destroy.Op.1a2547.8
// CHECK:STDOUT:   %specific_impl_fn.loc44_29.6 => constants.%Destroy.Op.1a2547.8
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: --- adl_return_same_types.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Iterate.type: type = facet_type <@Iterate> [concrete]
// CHECK:STDOUT:   %OptionalStorage.type: type = facet_type <@OptionalStorage> [concrete]
// CHECK:STDOUT:   %Destroy.type: type = facet_type <@Destroy> [concrete]
// CHECK:STDOUT:   %facet_type: type = facet_type <@Destroy & @Copy> [concrete]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [concrete]
// CHECK:STDOUT:   %T.220: %OptionalStorage.type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Optional.Get.type.bb9: type = fn_type @Optional.Get, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.Get.fa1: %Optional.Get.type.bb9 = struct_value () [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.e9e: type = fn_type @Optional.HasValue, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.6cd: %Optional.HasValue.type.e9e = struct_value () [symbolic]
// CHECK:STDOUT:   %T.283: %facet_type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.d50: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.type.671: type = fn_type @T.as_type.as.OptionalStorage.impl.Get, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.a54: %T.as_type.as.OptionalStorage.impl.Get.type.671 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.type.d76: type = fn_type @T.as_type.as.OptionalStorage.impl.Has, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.aa4: %T.as_type.as.OptionalStorage.impl.Has.type.d76 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.type.973: type = fn_type @T.as_type.as.OptionalStorage.impl.Some, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.c3a: %T.as_type.as.OptionalStorage.impl.Some.type.973 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.type.f62: type = fn_type @T.as_type.as.OptionalStorage.impl.None, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.faf: %T.as_type.as.OptionalStorage.impl.None.type.f62 = struct_value () [symbolic]
// CHECK:STDOUT:   %.Self.0.500: %Iterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.1d8: <witness> = lookup_impl_witness %.Self.0.500, @Iterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.294: %facet_type = impl_witness_access %Iterate.lookup_impl_witness.1d8, element0 [symbolic_self]
// CHECK:STDOUT:   %int_64: Core.IntLiteral = int_value 64 [concrete]
// CHECK:STDOUT:   %N.fe9: Core.IntLiteral = symbolic_binding N, 0 [symbolic]
// CHECK:STDOUT:   %f64.dc1: type = class_type @Float, @Float(%int_64) [concrete]
// CHECK:STDOUT:   %pattern_type.fb7: type = pattern_type %f64.dc1 [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.2: type = fn_type @Destroy.Op.loc20_47.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.2: %Destroy.Op.type.1d8f74.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.2: <witness> = custom_witness (%Destroy.Op.1a2547.2), @Destroy [concrete]
// CHECK:STDOUT:   %Float.as.Copy.impl.Op.type.ff3: type = fn_type @Float.as.Copy.impl.Op, @Float.as.Copy.impl(%N.fe9) [symbolic]
// CHECK:STDOUT:   %Float.as.Copy.impl.Op.d93: %Float.as.Copy.impl.Op.type.ff3 = struct_value () [symbolic]
// CHECK:STDOUT:   %Copy.impl_witness.873: <witness> = impl_witness imports.%Copy.impl_witness_table.4e8, @Float.as.Copy.impl(%int_64) [concrete]
// CHECK:STDOUT:   %facet_value.209: %facet_type = facet_value %f64.dc1, (%custom_witness.df9cc1.2, %Copy.impl_witness.873) [concrete]
// CHECK:STDOUT:   %Iterate_where.type.a32: type = facet_type <@Iterate where %impl.elem0.294 = %facet_value.209> [concrete]
// CHECK:STDOUT:   %R.c6e: %Iterate_where.type.a32 = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %R.as_type.087: type = facet_access_type %R.c6e [symbolic]
// CHECK:STDOUT:   %pattern_type.3d7: type = pattern_type %R.as_type.087 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.type: type = facet_type <@CppRangeForIterate> [concrete]
// CHECK:STDOUT:   %.Self.0.aed: %CppRangeForIterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.f6b: <witness> = lookup_impl_witness %.Self.0.aed, @CppRangeForIterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.b73: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element0 [symbolic_self]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.595: <witness> = lookup_impl_witness %impl.elem0.b73, @CppUnsafeDeref [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.a2f: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.595, element0 [symbolic_self]
// CHECK:STDOUT:   %impl.elem1.228: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element1 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate_where.type: type = facet_type <@CppRangeForIterate where %impl.elem0.b73 impls @Destroy and %impl.elem0.b73 impls @Copy and %impl.elem0.b73 impls @CppUnsafeDeref and %impl.elem0.b73 impls @EqWith, @EqWith(%impl.elem1.228) and %impl.elem0.b73 impls @Inc and %impl.elem0.a2f impls @Destroy and %impl.elem0.a2f impls @Copy and %impl.elem1.228 impls @Destroy and %impl.elem1.228 impls @Copy> [concrete]
// CHECK:STDOUT:   %R.39b: %CppRangeForIterate_where.type = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.7e2712.2: <witness> = lookup_impl_witness %R.39b, @CppRangeForIterate [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a0bff.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element1 [symbolic]
// CHECK:STDOUT:   %impl.elem0.73eb7f.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element0 [symbolic]
// CHECK:STDOUT:   %tuple.type.3cf: type = tuple_type (%impl.elem0.73eb7f.2, %impl.elem1.7a0bff.2) [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.69f: <witness> = lookup_impl_witness %tuple.type.3cf, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.facet.593: %Destroy.type = facet_value %tuple.type.3cf, (%Destroy.lookup_impl_witness.69f) [symbolic]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.aa7: <witness> = lookup_impl_witness %impl.elem0.73eb7f.2, @CppUnsafeDeref [symbolic]
// CHECK:STDOUT:   %impl.elem0.af7: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.aa7, element0 [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.ec3: <witness> = lookup_impl_witness %impl.elem0.af7, @Destroy [symbolic]
// CHECK:STDOUT:   %Copy.lookup_impl_witness.a7a: <witness> = lookup_impl_witness %impl.elem0.af7, @Copy [symbolic]
// CHECK:STDOUT:   %facet_value.194: %facet_type = facet_value %impl.elem0.af7, (%Destroy.lookup_impl_witness.ec3, %Copy.lookup_impl_witness.a7a) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.d8f: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c6d: %R.as_type.as.Iterate.impl.Next.type.d8f = struct_value () [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.127: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.627: %R.as_type.as.Iterate.impl.NewCursor.type.127 = struct_value () [symbolic]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.93c: <witness> = lookup_impl_witness %R.c6e, @Iterate [symbolic]
// CHECK:STDOUT:   %Iterate.facet.94d: %Iterate.type = facet_value %R.as_type.087, (%Iterate.lookup_impl_witness.93c) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.4c7: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.275: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %.a62: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.4c7, %Iterate.facet.94d [symbolic]
// CHECK:STDOUT:   %impl.elem2.c7b: %.a62 = impl_witness_access %Iterate.lookup_impl_witness.93c, element2 [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a9: %Destroy.type = impl_witness_access %Iterate.lookup_impl_witness.93c, element1 [symbolic]
// CHECK:STDOUT:   %as_type.8e4: type = facet_access_type %impl.elem1.7a9 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.1b8: <specific function> = specific_impl_function %impl.elem2.c7b, @Iterate.WithSelf.NewCursor(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %ptr.bac: type = ptr_type %as_type.8e4 [symbolic]
// CHECK:STDOUT:   %.a06: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.275, %Iterate.facet.94d [symbolic]
// CHECK:STDOUT:   %impl.elem3.7bd: %.a06 = impl_witness_access %Iterate.lookup_impl_witness.93c, element3 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.541: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%facet_value.209) [concrete]
// CHECK:STDOUT:   %OptionalStorage.impl_witness.be7: <witness> = impl_witness imports.%OptionalStorage.impl_witness_table.199, @T.as_type.as.OptionalStorage.impl(%facet_value.209) [concrete]
// CHECK:STDOUT:   %OptionalStorage.facet.c07: %OptionalStorage.type = facet_value %f64.dc1, (%OptionalStorage.impl_witness.be7) [concrete]
// CHECK:STDOUT:   %Optional.c42: type = class_type @Optional, @Optional(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %specific_impl_fn.666: <specific function> = specific_impl_function %impl.elem3.7bd, @Iterate.WithSelf.Next(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.c09: type = fn_type @Optional.HasValue, @Optional(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %Optional.HasValue.53b: %Optional.HasValue.type.c09 = struct_value () [concrete]
// CHECK:STDOUT:   %Optional.Get.type.4f6: type = fn_type @Optional.Get, @Optional(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %Optional.Get.5f1: %Optional.Get.type.4f6 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.facet.339: %Destroy.type = facet_value %f64.dc1, (%custom_witness.df9cc1.2) [concrete]
// CHECK:STDOUT:   %MaybeUnformed.b7e: type = class_type @MaybeUnformed, @MaybeUnformed(%Destroy.facet.339) [concrete]
// CHECK:STDOUT:   %struct_type.value.has_value.ad9: type = struct_type {.value: %MaybeUnformed.b7e, .has_value: bool} [concrete]
// CHECK:STDOUT:   %Optional.HasValue.specific_fn: <specific function> = specific_function %Optional.HasValue.53b, @Optional.HasValue(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %Optional.Get.specific_fn: <specific function> = specific_function %Optional.Get.5f1, @Optional.Get(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %AddAssignWith.type.ff9: type = facet_type <@AddAssignWith, @AddAssignWith(%f64.dc1)> [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.type.fdd: type = fn_type @Float.as.AddAssignWith.impl.Op, @Float.as.AddAssignWith.impl(%N.fe9) [symbolic]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.430: %Float.as.AddAssignWith.impl.Op.type.fdd = struct_value () [symbolic]
// CHECK:STDOUT:   %AddAssignWith.impl_witness.e85: <witness> = impl_witness imports.%AddAssignWith.impl_witness_table, @Float.as.AddAssignWith.impl(%int_64) [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.type.a92: type = fn_type @Float.as.AddAssignWith.impl.Op, @Float.as.AddAssignWith.impl(%int_64) [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.ac1: %Float.as.AddAssignWith.impl.Op.type.a92 = struct_value () [concrete]
// CHECK:STDOUT:   %AddAssignWith.facet: %AddAssignWith.type.ff9 = facet_value %f64.dc1, (%AddAssignWith.impl_witness.e85) [concrete]
// CHECK:STDOUT:   %AddAssignWith.WithSelf.Op.type.f8a: type = fn_type @AddAssignWith.WithSelf.Op, @AddAssignWith.WithSelf(%f64.dc1, %AddAssignWith.facet) [concrete]
// CHECK:STDOUT:   %.746: type = fn_type_with_self_type %AddAssignWith.WithSelf.Op.type.f8a, %AddAssignWith.facet [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.specific_fn: <specific function> = specific_function %Float.as.AddAssignWith.impl.Op.ac1, @Float.as.AddAssignWith.impl.Op(%int_64) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.8: type = fn_type @Destroy.Op.loc24_19.5 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.8: %Destroy.Op.type.1d8f74.8 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.def: <witness> = lookup_impl_witness %impl.elem1.7a9, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.41f: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1.7a9) [symbolic]
// CHECK:STDOUT:   %.148: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.41f, %impl.elem1.7a9 [symbolic]
// CHECK:STDOUT:   %impl.elem0.461: %.148 = impl_witness_access %Destroy.lookup_impl_witness.def, element0 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.095: <specific function> = specific_impl_function %impl.elem0.461, @Destroy.WithSelf.Op(%impl.elem1.7a9) [symbolic]
// CHECK:STDOUT:   %ConstRange: type = class_type @ConstRange [concrete]
// CHECK:STDOUT:   %pattern_type.025: type = pattern_type %ConstRange [concrete]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [concrete]
// CHECK:STDOUT:   %complete_type.357: <witness> = complete_type_witness %empty_struct_type [concrete]
// CHECK:STDOUT:   %Iterator: type = class_type @Iterator.1 [concrete]
// CHECK:STDOUT:   %Begin.type: type = fn_type @Begin [concrete]
// CHECK:STDOUT:   %Begin: %Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %End.type: type = fn_type @End [concrete]
// CHECK:STDOUT:   %End: %End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.5d5: <witness> = custom_witness (%Iterator, %Iterator, %Begin, %End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.1: type = fn_type @Iterator.Op.1 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.1: %Iterator.Op.type.ac7e09.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.994: <witness> = custom_witness (%f64.dc1, %Iterator.Op.583fda.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.2: type = fn_type @Iterator.Op.2 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.2: %Iterator.Op.type.ac7e09.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.213: <witness> = custom_witness (%Iterator.Op.583fda.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.3: type = fn_type @Iterator.Op.3 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.3: %Iterator.Op.type.ac7e09.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.a31: <witness> = custom_witness (%Iterator.Op.583fda.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type: type = fn_type @Equal [concrete]
// CHECK:STDOUT:   %Equal: %Equal.type = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type: type = fn_type @NotEqual [concrete]
// CHECK:STDOUT:   %NotEqual: %NotEqual.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.821: <witness> = custom_witness (%Equal, %NotEqual), @EqWith, @EqWith(%Iterator) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.4: type = fn_type @Iterator.Op.4 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.4: %Iterator.Op.type.ac7e09.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.393: <witness> = custom_witness (%Iterator.Op.583fda.4), @Inc [concrete]
// CHECK:STDOUT:   %facet_value.c05: %CppRangeForIterate_where.type = facet_value %ConstRange, (%custom_witness.df9cc1.2, %Copy.impl_witness.873, %custom_witness.5d5, %custom_witness.213, %custom_witness.a31, %custom_witness.994, %custom_witness.821, %custom_witness.393) [concrete]
// CHECK:STDOUT:   %tuple.type.005: type = tuple_type (%Iterator, %Iterator) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.9: type = fn_type @Destroy.Op.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.9: %Destroy.Op.type.1d8f74.9 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.9: <witness> = custom_witness (%Destroy.Op.1a2547.9), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.40b: %Destroy.type = facet_value %tuple.type.005, (%custom_witness.df9cc1.9) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.e5c: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.c05) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.979: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.c05) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.662: %R.as_type.as.Iterate.impl.NewCursor.type.979 = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.496: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.c05) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c12: %R.as_type.as.Iterate.impl.Next.type.496 = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.c32: %Iterate.type = facet_value %ConstRange, (%Iterate.impl_witness.e5c) [concrete]
// CHECK:STDOUT:   %facet_value.d21: %Iterate_where.type.a32 = facet_value %ConstRange, (%Iterate.impl_witness.e5c) [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.ebd: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.c32) [concrete]
// CHECK:STDOUT:   %.243: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.ebd, %Iterate.facet.c32 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.662, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.c05) [concrete]
// CHECK:STDOUT:   %complete_type.320: <witness> = complete_type_witness %tuple.type.005 [concrete]
// CHECK:STDOUT:   %ptr.d1a: type = ptr_type %tuple.type.005 [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.377: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.c32) [concrete]
// CHECK:STDOUT:   %.c31: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.377, %Iterate.facet.c32 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.c12, @R.as_type.as.Iterate.impl.Next(%facet_value.c05) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.117: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.40b) [concrete]
// CHECK:STDOUT:   %.5a4: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.117, %Destroy.facet.40b [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Core.import_ref.bb6: @Optional.%Optional.HasValue.type (%Optional.HasValue.type.e9e) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.HasValue (constants.%Optional.HasValue.6cd)]
// CHECK:STDOUT:   %Core.import_ref.daba: @Optional.%Optional.Get.type (%Optional.Get.type.bb9) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.Get (constants.%Optional.Get.fa1)]
// CHECK:STDOUT:   %Core.import_ref.0c6: type = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%DefaultOptionalStorage (constants.%DefaultOptionalStorage.d50)]
// CHECK:STDOUT:   %Core.import_ref.6d6: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None.type (%T.as_type.as.OptionalStorage.impl.None.type.f62) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None (constants.%T.as_type.as.OptionalStorage.impl.None.faf)]
// CHECK:STDOUT:   %Core.import_ref.6f3: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some.type (%T.as_type.as.OptionalStorage.impl.Some.type.973) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some (constants.%T.as_type.as.OptionalStorage.impl.Some.c3a)]
// CHECK:STDOUT:   %Core.import_ref.af2: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has.type (%T.as_type.as.OptionalStorage.impl.Has.type.d76) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has (constants.%T.as_type.as.OptionalStorage.impl.Has.aa4)]
// CHECK:STDOUT:   %Core.import_ref.e31: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get.type (%T.as_type.as.OptionalStorage.impl.Get.type.671) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get (constants.%T.as_type.as.OptionalStorage.impl.Get.a54)]
// CHECK:STDOUT:   %Core.import_ref.cea = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %OptionalStorage.impl_witness_table.199 = impl_witness_table (%Core.import_ref.0c6, %Core.import_ref.6d6, %Core.import_ref.6f3, %Core.import_ref.af2, %Core.import_ref.e31, %Core.import_ref.cea), @T.as_type.as.OptionalStorage.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.e69: @Float.as.Copy.impl.%Float.as.Copy.impl.Op.type (%Float.as.Copy.impl.Op.type.ff3) = import_ref Core//prelude/types/float, loc{{\d+_\d+}}, loaded [symbolic = @Float.as.Copy.impl.%Float.as.Copy.impl.Op (constants.%Float.as.Copy.impl.Op.d93)]
// CHECK:STDOUT:   %Copy.impl_witness_table.4e8 = impl_witness_table (%Core.import_ref.e69), @Float.as.Copy.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.301: %facet_type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%facet_value (constants.%facet_value.194)]
// CHECK:STDOUT:   %Core.import_ref.89f: %Destroy.type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%Destroy.facet (constants.%Destroy.facet.593)]
// CHECK:STDOUT:   %Core.import_ref.940: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor.type (%R.as_type.as.Iterate.impl.NewCursor.type.127) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor (constants.%R.as_type.as.Iterate.impl.NewCursor.627)]
// CHECK:STDOUT:   %Core.import_ref.fe7: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next.type (%R.as_type.as.Iterate.impl.Next.type.d8f) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next (constants.%R.as_type.as.Iterate.impl.Next.c6d)]
// CHECK:STDOUT:   %Iterate.impl_witness_table.ccd = impl_witness_table (%Core.import_ref.301, %Core.import_ref.89f, %Core.import_ref.940, %Core.import_ref.fe7), @R.as_type.as.Iterate.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.cb3: @Float.as.AddAssignWith.impl.%Float.as.AddAssignWith.impl.Op.type (%Float.as.AddAssignWith.impl.Op.type.fdd) = import_ref Core//prelude/types/float, loc{{\d+_\d+}}, loaded [symbolic = @Float.as.AddAssignWith.impl.%Float.as.AddAssignWith.impl.Op (constants.%Float.as.AddAssignWith.impl.Op.430)]
// CHECK:STDOUT:   %AddAssignWith.impl_witness_table = impl_witness_table (%Core.import_ref.cb3), @Float.as.AddAssignWith.impl [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Test(%R.loc20_10.2: %Iterate_where.type.a32) {
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %Iterate.lookup_impl_witness: <witness> = lookup_impl_witness %R.loc20_10.1, @Iterate [symbolic = %Iterate.lookup_impl_witness (constants.%Iterate.lookup_impl_witness.93c)]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.loc20_55.1, (%Iterate.lookup_impl_witness) [symbolic = %Iterate.facet (constants.%Iterate.facet.94d)]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.NewCursor.type (constants.%Iterate.WithSelf.NewCursor.type.4c7)]
// CHECK:STDOUT:   %.loc24_19.12: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type, %Iterate.facet [symbolic = %.loc24_19.12 (constants.%.a62)]
// CHECK:STDOUT:   %impl.elem2.loc24_19.2: @Test.%.loc24_19.12 (%.a62) = impl_witness_access %Iterate.lookup_impl_witness, element2 [symbolic = %impl.elem2.loc24_19.2 (constants.%impl.elem2.c7b)]
// CHECK:STDOUT:   %specific_impl_fn.loc24_19.4: <specific function> = specific_impl_function %impl.elem2.loc24_19.2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic = %specific_impl_fn.loc24_19.4 (constants.%specific_impl_fn.1b8)]
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %ptr: type = ptr_type %as_type [symbolic = %ptr (constants.%ptr.bac)]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.Next.type (constants.%Iterate.WithSelf.Next.type.275)]
// CHECK:STDOUT:   %.loc24_19.13: type = fn_type_with_self_type %Iterate.WithSelf.Next.type, %Iterate.facet [symbolic = %.loc24_19.13 (constants.%.a06)]
// CHECK:STDOUT:   %impl.elem3.loc24_19.2: @Test.%.loc24_19.13 (%.a06) = impl_witness_access %Iterate.lookup_impl_witness, element3 [symbolic = %impl.elem3.loc24_19.2 (constants.%impl.elem3.7bd)]
// CHECK:STDOUT:   %specific_impl_fn.loc24_19.5: <specific function> = specific_impl_function %impl.elem3.loc24_19.2, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic = %specific_impl_fn.loc24_19.5 (constants.%specific_impl_fn.666)]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1) [symbolic = %Destroy.WithSelf.Op.type (constants.%Destroy.WithSelf.Op.type.41f)]
// CHECK:STDOUT:   %.loc24_19.14: type = fn_type_with_self_type %Destroy.WithSelf.Op.type, %impl.elem1 [symbolic = %.loc24_19.14 (constants.%.148)]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness: <witness> = lookup_impl_witness %impl.elem1, @Destroy [symbolic = %Destroy.lookup_impl_witness (constants.%Destroy.lookup_impl_witness.def)]
// CHECK:STDOUT:   %impl.elem0.loc24_19.2: @Test.%.loc24_19.14 (%.148) = impl_witness_access %Destroy.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc24_19.2 (constants.%impl.elem0.461)]
// CHECK:STDOUT:   %specific_impl_fn.loc24_19.6: <specific function> = specific_impl_function %impl.elem0.loc24_19.2, @Destroy.WithSelf.Op(%impl.elem1) [symbolic = %specific_impl_fn.loc24_19.6 (constants.%specific_impl_fn.095)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%r.param: @Test.%R.as_type.loc20_55.1 (%R.as_type.087)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:     name_binding_decl {
// CHECK:STDOUT:       %i.patt: %pattern_type.fb7 = value_binding_pattern i [concrete]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %r.ref: @Test.%R.as_type.loc20_55.1 (%R.as_type.087) = name_ref r, %r
// CHECK:STDOUT:     %impl.elem2.loc24_19.1: @Test.%.loc24_19.12 (%.a62) = impl_witness_access constants.%Iterate.lookup_impl_witness.93c, element2 [symbolic = %impl.elem2.loc24_19.2 (constants.%impl.elem2.c7b)]
// CHECK:STDOUT:     %bound_method.loc24_19.1: <bound method> = bound_method %r.ref, %impl.elem2.loc24_19.1
// CHECK:STDOUT:     %specific_impl_fn.loc24_19.1: <specific function> = specific_impl_function %impl.elem2.loc24_19.1, @Iterate.WithSelf.NewCursor(constants.%Iterate.facet.94d) [symbolic = %specific_impl_fn.loc24_19.4 (constants.%specific_impl_fn.1b8)]
// CHECK:STDOUT:     %bound_method.loc24_19.2: <bound method> = bound_method %r.ref, %specific_impl_fn.loc24_19.1
// CHECK:STDOUT:     %var: ref @Test.%as_type (%as_type.8e4) = var invalid
// CHECK:STDOUT:     %Iterate.WithSelf.NewCursor.call: init @Test.%as_type (%as_type.8e4) to %var = call %bound_method.loc24_19.2(%r.ref)
// CHECK:STDOUT:     assign %var, %Iterate.WithSelf.NewCursor.call
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.next:
// CHECK:STDOUT:     %addr: @Test.%ptr (%ptr.bac) = addr_of %var
// CHECK:STDOUT:     %impl.elem3.loc24_19.1: @Test.%.loc24_19.13 (%.a06) = impl_witness_access constants.%Iterate.lookup_impl_witness.93c, element3 [symbolic = %impl.elem3.loc24_19.2 (constants.%impl.elem3.7bd)]
// CHECK:STDOUT:     %bound_method.loc24_19.3: <bound method> = bound_method %r.ref, %impl.elem3.loc24_19.1
// CHECK:STDOUT:     %.loc24_19.1: %Destroy.type = converted constants.%as_type.8e4, constants.%impl.elem1.7a9 [symbolic = %impl.elem1 (constants.%impl.elem1.7a9)]
// CHECK:STDOUT:     %specific_impl_fn.loc24_19.2: <specific function> = specific_impl_function %impl.elem3.loc24_19.1, @Iterate.WithSelf.Next(constants.%Iterate.facet.94d) [symbolic = %specific_impl_fn.loc24_19.5 (constants.%specific_impl_fn.666)]
// CHECK:STDOUT:     %bound_method.loc24_19.4: <bound method> = bound_method %r.ref, %specific_impl_fn.loc24_19.2
// CHECK:STDOUT:     %.loc24_19.2: ref %Optional.c42 = temporary_storage
// CHECK:STDOUT:     %Iterate.WithSelf.Next.call: init %Optional.c42 to %.loc24_19.2 = call %bound_method.loc24_19.4(%r.ref, %addr)
// CHECK:STDOUT:     %.loc24_19.3: ref %Optional.c42 = temporary %.loc24_19.2, %Iterate.WithSelf.Next.call
// CHECK:STDOUT:     %.loc24_19.4: %Optional.HasValue.type.c09 = specific_constant imports.%Core.import_ref.bb6, @Optional(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.HasValue.53b]
// CHECK:STDOUT:     %HasValue.ref: %Optional.HasValue.type.c09 = name_ref HasValue, %.loc24_19.4 [concrete = constants.%Optional.HasValue.53b]
// CHECK:STDOUT:     %Optional.HasValue.bound: <bound method> = bound_method %.loc24_19.3, %HasValue.ref
// CHECK:STDOUT:     %Optional.HasValue.specific_fn: <specific function> = specific_function %HasValue.ref, @Optional.HasValue(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.HasValue.specific_fn]
// CHECK:STDOUT:     %bound_method.loc24_19.5: <bound method> = bound_method %.loc24_19.3, %Optional.HasValue.specific_fn
// CHECK:STDOUT:     %.loc24_19.5: %Optional.c42 = acquire_value %.loc24_19.3
// CHECK:STDOUT:     %Optional.HasValue.call: init bool = call %bound_method.loc24_19.5(%.loc24_19.5)
// CHECK:STDOUT:     %.loc24_19.6: bool = value_of_initializer %Optional.HasValue.call
// CHECK:STDOUT:     %.loc24_19.7: bool = converted %Optional.HasValue.call, %.loc24_19.6
// CHECK:STDOUT:     if %.loc24_19.7 br !for.body else br !for.done
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.body:
// CHECK:STDOUT:     %.loc24_19.8: %Optional.Get.type.4f6 = specific_constant imports.%Core.import_ref.daba, @Optional(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.Get.5f1]
// CHECK:STDOUT:     %Get.ref: %Optional.Get.type.4f6 = name_ref Get, %.loc24_19.8 [concrete = constants.%Optional.Get.5f1]
// CHECK:STDOUT:     %Optional.Get.bound: <bound method> = bound_method %.loc24_19.3, %Get.ref
// CHECK:STDOUT:     %Optional.Get.specific_fn: <specific function> = specific_function %Get.ref, @Optional.Get(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.Get.specific_fn]
// CHECK:STDOUT:     %bound_method.loc24_19.6: <bound method> = bound_method %.loc24_19.3, %Optional.Get.specific_fn
// CHECK:STDOUT:     %.loc24_19.9: %Optional.c42 = acquire_value %.loc24_19.3
// CHECK:STDOUT:     %Optional.Get.call: init %f64.dc1 = call %bound_method.loc24_19.6(%.loc24_19.9)
// CHECK:STDOUT:     %f64.loc24: type = type_literal constants.%f64.dc1 [concrete = constants.%f64.dc1]
// CHECK:STDOUT:     %.loc24_19.10: %f64.dc1 = value_of_initializer %Optional.Get.call
// CHECK:STDOUT:     %.loc24_19.11: %f64.dc1 = converted %Optional.Get.call, %.loc24_19.10
// CHECK:STDOUT:     %i: %f64.dc1 = value_binding i, %.loc24_19.11
// CHECK:STDOUT:     %sum.ref: ref %f64.dc1 = name_ref sum, %sum
// CHECK:STDOUT:     %i.ref: %f64.dc1 = name_ref i, %i
// CHECK:STDOUT:     %impl.elem0.loc25: %.746 = impl_witness_access constants.%AddAssignWith.impl_witness.e85, element0 [concrete = constants.%Float.as.AddAssignWith.impl.Op.ac1]
// CHECK:STDOUT:     %bound_method.loc25_9.1: <bound method> = bound_method %sum.ref, %impl.elem0.loc25
// CHECK:STDOUT:     %specific_fn.loc25: <specific function> = specific_function %impl.elem0.loc25, @Float.as.AddAssignWith.impl.Op(constants.%int_64) [concrete = constants.%Float.as.AddAssignWith.impl.Op.specific_fn]
// CHECK:STDOUT:     %bound_method.loc25_9.2: <bound method> = bound_method %sum.ref, %specific_fn.loc25
// CHECK:STDOUT:     %Float.as.AddAssignWith.impl.Op.call: init %empty_tuple.type = call %bound_method.loc25_9.2(%sum.ref, %i.ref)
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.done:
// CHECK:STDOUT:     %Destroy.Op.bound.loc24: <bound method> = bound_method %.loc24_19.3, constants.%Destroy.Op.1a2547.8
// CHECK:STDOUT:     %Destroy.Op.call.loc24: init %empty_tuple.type = call %Destroy.Op.bound.loc24(%.loc24_19.3)
// CHECK:STDOUT:     %impl.elem0.loc24_19.1: @Test.%.loc24_19.14 (%.148) = impl_witness_access constants.%Destroy.lookup_impl_witness.def, element0 [symbolic = %impl.elem0.loc24_19.2 (constants.%impl.elem0.461)]
// CHECK:STDOUT:     %bound_method.loc24_19.7: <bound method> = bound_method %var, %impl.elem0.loc24_19.1
// CHECK:STDOUT:     %specific_impl_fn.loc24_19.3: <specific function> = specific_impl_function %impl.elem0.loc24_19.1, @Destroy.WithSelf.Op(constants.%impl.elem1.7a9) [symbolic = %specific_impl_fn.loc24_19.6 (constants.%specific_impl_fn.095)]
// CHECK:STDOUT:     %bound_method.loc24_19.8: <bound method> = bound_method %var, %specific_impl_fn.loc24_19.3
// CHECK:STDOUT:     %Destroy.WithSelf.Op.call: init %empty_tuple.type = call %bound_method.loc24_19.8(%var)
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc24_19.1(%self.param: ref %MaybeUnformed.b7e) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc24_19.2(%self.param: ref bool) = "no_op";
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc24_19.3(%self.param: ref %struct_type.value.has_value.ad9) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc24_19.4(%self.param: ref %DefaultOptionalStorage.541) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc24_19.5(%self.param: ref %Optional.c42) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%R.c6e) {
// CHECK:STDOUT:   %R.loc20_10.1 => constants.%R.c6e
// CHECK:STDOUT:   %R.as_type.loc20_55.1 => constants.%R.as_type.087
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.3d7
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.d21) {
// CHECK:STDOUT:   %R.loc20_10.1 => constants.%facet_value.d21
// CHECK:STDOUT:   %R.as_type.loc20_55.1 => constants.%ConstRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.025
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc20 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.e5c
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.c32
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.ebd
// CHECK:STDOUT:   %.loc24_19.12 => constants.%.243
// CHECK:STDOUT:   %impl.elem2.loc24_19.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.662
// CHECK:STDOUT:   %specific_impl_fn.loc24_19.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.40b
// CHECK:STDOUT:   %as_type => constants.%tuple.type.005
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.320
// CHECK:STDOUT:   %ptr => constants.%ptr.d1a
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.377
// CHECK:STDOUT:   %.loc24_19.13 => constants.%.c31
// CHECK:STDOUT:   %impl.elem3.loc24_19.2 => constants.%R.as_type.as.Iterate.impl.Next.c12
// CHECK:STDOUT:   %specific_impl_fn.loc24_19.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.117
// CHECK:STDOUT:   %.loc24_19.14 => constants.%.5a4
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.9
// CHECK:STDOUT:   %impl.elem0.loc24_19.2 => constants.%Destroy.Op.1a2547.9
// CHECK:STDOUT:   %specific_impl_fn.loc24_19.6 => constants.%Destroy.Op.1a2547.9
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: --- fail_todo_adl_returns_same_types_mutable.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Iterate.type: type = facet_type <@Iterate> [concrete]
// CHECK:STDOUT:   %OptionalStorage.type: type = facet_type <@OptionalStorage> [concrete]
// CHECK:STDOUT:   %Destroy.type: type = facet_type <@Destroy> [concrete]
// CHECK:STDOUT:   %facet_type: type = facet_type <@Destroy & @Copy> [concrete]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [concrete]
// CHECK:STDOUT:   %T.220: %OptionalStorage.type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Optional.Get.type.bb9: type = fn_type @Optional.Get, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.Get.fa1: %Optional.Get.type.bb9 = struct_value () [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.e9e: type = fn_type @Optional.HasValue, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.6cd: %Optional.HasValue.type.e9e = struct_value () [symbolic]
// CHECK:STDOUT:   %T.283: %facet_type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.d50: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.type.671: type = fn_type @T.as_type.as.OptionalStorage.impl.Get, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.a54: %T.as_type.as.OptionalStorage.impl.Get.type.671 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.type.d76: type = fn_type @T.as_type.as.OptionalStorage.impl.Has, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.aa4: %T.as_type.as.OptionalStorage.impl.Has.type.d76 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.type.973: type = fn_type @T.as_type.as.OptionalStorage.impl.Some, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.c3a: %T.as_type.as.OptionalStorage.impl.Some.type.973 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.type.f62: type = fn_type @T.as_type.as.OptionalStorage.impl.None, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.faf: %T.as_type.as.OptionalStorage.impl.None.type.f62 = struct_value () [symbolic]
// CHECK:STDOUT:   %.Self.0.500: %Iterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.1d8: <witness> = lookup_impl_witness %.Self.0.500, @Iterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.294: %facet_type = impl_witness_access %Iterate.lookup_impl_witness.1d8, element0 [symbolic_self]
// CHECK:STDOUT:   %int_64: Core.IntLiteral = int_value 64 [concrete]
// CHECK:STDOUT:   %N.fe9: Core.IntLiteral = symbolic_binding N, 0 [symbolic]
// CHECK:STDOUT:   %f64.dc1: type = class_type @Float, @Float(%int_64) [concrete]
// CHECK:STDOUT:   %pattern_type.fb7: type = pattern_type %f64.dc1 [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.2: type = fn_type @Destroy.Op.loc22_47.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.2: %Destroy.Op.type.1d8f74.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.2: <witness> = custom_witness (%Destroy.Op.1a2547.2), @Destroy [concrete]
// CHECK:STDOUT:   %Float.as.Copy.impl.Op.type.ff3: type = fn_type @Float.as.Copy.impl.Op, @Float.as.Copy.impl(%N.fe9) [symbolic]
// CHECK:STDOUT:   %Float.as.Copy.impl.Op.d93: %Float.as.Copy.impl.Op.type.ff3 = struct_value () [symbolic]
// CHECK:STDOUT:   %Copy.impl_witness.873: <witness> = impl_witness imports.%Copy.impl_witness_table.4e8, @Float.as.Copy.impl(%int_64) [concrete]
// CHECK:STDOUT:   %facet_value.209: %facet_type = facet_value %f64.dc1, (%custom_witness.df9cc1.2, %Copy.impl_witness.873) [concrete]
// CHECK:STDOUT:   %Iterate_where.type.a32: type = facet_type <@Iterate where %impl.elem0.294 = %facet_value.209> [concrete]
// CHECK:STDOUT:   %R.c6e: %Iterate_where.type.a32 = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %R.as_type.087: type = facet_access_type %R.c6e [symbolic]
// CHECK:STDOUT:   %pattern_type.3d7: type = pattern_type %R.as_type.087 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.type: type = facet_type <@CppRangeForIterate> [concrete]
// CHECK:STDOUT:   %.Self.0.aed: %CppRangeForIterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.f6b: <witness> = lookup_impl_witness %.Self.0.aed, @CppRangeForIterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.b73: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element0 [symbolic_self]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.595: <witness> = lookup_impl_witness %impl.elem0.b73, @CppUnsafeDeref [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.a2f: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.595, element0 [symbolic_self]
// CHECK:STDOUT:   %impl.elem1.228: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element1 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate_where.type: type = facet_type <@CppRangeForIterate where %impl.elem0.b73 impls @Destroy and %impl.elem0.b73 impls @Copy and %impl.elem0.b73 impls @CppUnsafeDeref and %impl.elem0.b73 impls @EqWith, @EqWith(%impl.elem1.228) and %impl.elem0.b73 impls @Inc and %impl.elem0.a2f impls @Destroy and %impl.elem0.a2f impls @Copy and %impl.elem1.228 impls @Destroy and %impl.elem1.228 impls @Copy> [concrete]
// CHECK:STDOUT:   %R.39b: %CppRangeForIterate_where.type = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.7e2712.2: <witness> = lookup_impl_witness %R.39b, @CppRangeForIterate [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a0bff.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element1 [symbolic]
// CHECK:STDOUT:   %impl.elem0.73eb7f.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element0 [symbolic]
// CHECK:STDOUT:   %tuple.type.3cf: type = tuple_type (%impl.elem0.73eb7f.2, %impl.elem1.7a0bff.2) [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.69f: <witness> = lookup_impl_witness %tuple.type.3cf, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.facet.593: %Destroy.type = facet_value %tuple.type.3cf, (%Destroy.lookup_impl_witness.69f) [symbolic]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.aa7: <witness> = lookup_impl_witness %impl.elem0.73eb7f.2, @CppUnsafeDeref [symbolic]
// CHECK:STDOUT:   %impl.elem0.af7: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.aa7, element0 [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.ec3: <witness> = lookup_impl_witness %impl.elem0.af7, @Destroy [symbolic]
// CHECK:STDOUT:   %Copy.lookup_impl_witness.a7a: <witness> = lookup_impl_witness %impl.elem0.af7, @Copy [symbolic]
// CHECK:STDOUT:   %facet_value.194: %facet_type = facet_value %impl.elem0.af7, (%Destroy.lookup_impl_witness.ec3, %Copy.lookup_impl_witness.a7a) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.d8f: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c6d: %R.as_type.as.Iterate.impl.Next.type.d8f = struct_value () [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.127: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.627: %R.as_type.as.Iterate.impl.NewCursor.type.127 = struct_value () [symbolic]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.93c: <witness> = lookup_impl_witness %R.c6e, @Iterate [symbolic]
// CHECK:STDOUT:   %Iterate.facet.94d: %Iterate.type = facet_value %R.as_type.087, (%Iterate.lookup_impl_witness.93c) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.4c7: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.275: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %.a62: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.4c7, %Iterate.facet.94d [symbolic]
// CHECK:STDOUT:   %impl.elem2.c7b: %.a62 = impl_witness_access %Iterate.lookup_impl_witness.93c, element2 [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a9: %Destroy.type = impl_witness_access %Iterate.lookup_impl_witness.93c, element1 [symbolic]
// CHECK:STDOUT:   %as_type.8e4: type = facet_access_type %impl.elem1.7a9 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.1b8: <specific function> = specific_impl_function %impl.elem2.c7b, @Iterate.WithSelf.NewCursor(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %ptr.bac: type = ptr_type %as_type.8e4 [symbolic]
// CHECK:STDOUT:   %.a06: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.275, %Iterate.facet.94d [symbolic]
// CHECK:STDOUT:   %impl.elem3.7bd: %.a06 = impl_witness_access %Iterate.lookup_impl_witness.93c, element3 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.541: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%facet_value.209) [concrete]
// CHECK:STDOUT:   %OptionalStorage.impl_witness.be7: <witness> = impl_witness imports.%OptionalStorage.impl_witness_table.199, @T.as_type.as.OptionalStorage.impl(%facet_value.209) [concrete]
// CHECK:STDOUT:   %OptionalStorage.facet.c07: %OptionalStorage.type = facet_value %f64.dc1, (%OptionalStorage.impl_witness.be7) [concrete]
// CHECK:STDOUT:   %Optional.c42: type = class_type @Optional, @Optional(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %specific_impl_fn.666: <specific function> = specific_impl_function %impl.elem3.7bd, @Iterate.WithSelf.Next(%Iterate.facet.94d) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.c09: type = fn_type @Optional.HasValue, @Optional(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %Optional.HasValue.53b: %Optional.HasValue.type.c09 = struct_value () [concrete]
// CHECK:STDOUT:   %Optional.Get.type.4f6: type = fn_type @Optional.Get, @Optional(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %Optional.Get.5f1: %Optional.Get.type.4f6 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.facet.339: %Destroy.type = facet_value %f64.dc1, (%custom_witness.df9cc1.2) [concrete]
// CHECK:STDOUT:   %MaybeUnformed.b7e: type = class_type @MaybeUnformed, @MaybeUnformed(%Destroy.facet.339) [concrete]
// CHECK:STDOUT:   %struct_type.value.has_value.ad9: type = struct_type {.value: %MaybeUnformed.b7e, .has_value: bool} [concrete]
// CHECK:STDOUT:   %Optional.HasValue.specific_fn: <specific function> = specific_function %Optional.HasValue.53b, @Optional.HasValue(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %Optional.Get.specific_fn: <specific function> = specific_function %Optional.Get.5f1, @Optional.Get(%OptionalStorage.facet.c07) [concrete]
// CHECK:STDOUT:   %AddAssignWith.type.ff9: type = facet_type <@AddAssignWith, @AddAssignWith(%f64.dc1)> [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.type.fdd: type = fn_type @Float.as.AddAssignWith.impl.Op, @Float.as.AddAssignWith.impl(%N.fe9) [symbolic]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.430: %Float.as.AddAssignWith.impl.Op.type.fdd = struct_value () [symbolic]
// CHECK:STDOUT:   %AddAssignWith.impl_witness.e85: <witness> = impl_witness imports.%AddAssignWith.impl_witness_table, @Float.as.AddAssignWith.impl(%int_64) [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.type.a92: type = fn_type @Float.as.AddAssignWith.impl.Op, @Float.as.AddAssignWith.impl(%int_64) [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.ac1: %Float.as.AddAssignWith.impl.Op.type.a92 = struct_value () [concrete]
// CHECK:STDOUT:   %AddAssignWith.facet: %AddAssignWith.type.ff9 = facet_value %f64.dc1, (%AddAssignWith.impl_witness.e85) [concrete]
// CHECK:STDOUT:   %AddAssignWith.WithSelf.Op.type.f8a: type = fn_type @AddAssignWith.WithSelf.Op, @AddAssignWith.WithSelf(%f64.dc1, %AddAssignWith.facet) [concrete]
// CHECK:STDOUT:   %.746: type = fn_type_with_self_type %AddAssignWith.WithSelf.Op.type.f8a, %AddAssignWith.facet [concrete]
// CHECK:STDOUT:   %Float.as.AddAssignWith.impl.Op.specific_fn: <specific function> = specific_function %Float.as.AddAssignWith.impl.Op.ac1, @Float.as.AddAssignWith.impl.Op(%int_64) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.8: type = fn_type @Destroy.Op.loc26_19.5 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.8: %Destroy.Op.type.1d8f74.8 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.def: <witness> = lookup_impl_witness %impl.elem1.7a9, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.41f: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1.7a9) [symbolic]
// CHECK:STDOUT:   %.148: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.41f, %impl.elem1.7a9 [symbolic]
// CHECK:STDOUT:   %impl.elem0.461: %.148 = impl_witness_access %Destroy.lookup_impl_witness.def, element0 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.095: <specific function> = specific_impl_function %impl.elem0.461, @Destroy.WithSelf.Op(%impl.elem1.7a9) [symbolic]
// CHECK:STDOUT:   %MutableRange: type = class_type @MutableRange [concrete]
// CHECK:STDOUT:   %pattern_type.992: type = pattern_type %MutableRange [concrete]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [concrete]
// CHECK:STDOUT:   %complete_type.357: <witness> = complete_type_witness %empty_struct_type [concrete]
// CHECK:STDOUT:   %Iterator: type = class_type @Iterator.1 [concrete]
// CHECK:STDOUT:   %Begin.type: type = fn_type @Begin [concrete]
// CHECK:STDOUT:   %Begin: %Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %End.type: type = fn_type @End [concrete]
// CHECK:STDOUT:   %End: %End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.902: <witness> = custom_witness (%Iterator, %Iterator, %Begin, %End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.b9731e.1: type = fn_type @Iterator.Op.1 [concrete]
// CHECK:STDOUT:   %Iterator.Op.ac6aad.1: %Iterator.Op.type.b9731e.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.05b: <witness> = custom_witness (%f64.dc1, %Iterator.Op.ac6aad.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.b9731e.2: type = fn_type @Iterator.Op.2 [concrete]
// CHECK:STDOUT:   %Iterator.Op.ac6aad.2: %Iterator.Op.type.b9731e.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.c08: <witness> = custom_witness (%Iterator.Op.ac6aad.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.b9731e.3: type = fn_type @Iterator.Op.3 [concrete]
// CHECK:STDOUT:   %Iterator.Op.ac6aad.3: %Iterator.Op.type.b9731e.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.29f: <witness> = custom_witness (%Iterator.Op.ac6aad.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type: type = fn_type @Equal [concrete]
// CHECK:STDOUT:   %Equal: %Equal.type = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type: type = fn_type @NotEqual [concrete]
// CHECK:STDOUT:   %NotEqual: %NotEqual.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.ed8: <witness> = custom_witness (%Equal, %NotEqual), @EqWith, @EqWith(%Iterator) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.b9731e.4: type = fn_type @Iterator.Op.4 [concrete]
// CHECK:STDOUT:   %Iterator.Op.ac6aad.4: %Iterator.Op.type.b9731e.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.491: <witness> = custom_witness (%Iterator.Op.ac6aad.4), @Inc [concrete]
// CHECK:STDOUT:   %facet_value.85f: %CppRangeForIterate_where.type = facet_value %MutableRange, (%custom_witness.df9cc1.2, %Copy.impl_witness.873, %custom_witness.902, %custom_witness.c08, %custom_witness.29f, %custom_witness.05b, %custom_witness.ed8, %custom_witness.491) [concrete]
// CHECK:STDOUT:   %tuple.type.dd0: type = tuple_type (%Iterator, %Iterator) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.9: type = fn_type @Destroy.Op.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.9: %Destroy.Op.type.1d8f74.9 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.9: <witness> = custom_witness (%Destroy.Op.1a2547.9), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.e1e: %Destroy.type = facet_value %tuple.type.dd0, (%custom_witness.df9cc1.9) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.57f: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.85f) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.cac: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.85f) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.b0d: %R.as_type.as.Iterate.impl.NewCursor.type.cac = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.82c: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.85f) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c07: %R.as_type.as.Iterate.impl.Next.type.82c = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.d2f: %Iterate.type = facet_value %MutableRange, (%Iterate.impl_witness.57f) [concrete]
// CHECK:STDOUT:   %facet_value.37c: %Iterate_where.type.a32 = facet_value %MutableRange, (%Iterate.impl_witness.57f) [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.1cb: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.d2f) [concrete]
// CHECK:STDOUT:   %.dab: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.1cb, %Iterate.facet.d2f [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.b0d, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.85f) [concrete]
// CHECK:STDOUT:   %complete_type.843: <witness> = complete_type_witness %tuple.type.dd0 [concrete]
// CHECK:STDOUT:   %ptr.a4f: type = ptr_type %tuple.type.dd0 [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.ba9: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.d2f) [concrete]
// CHECK:STDOUT:   %.7d2: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.ba9, %Iterate.facet.d2f [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.c07, @R.as_type.as.Iterate.impl.Next(%facet_value.85f) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.452: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.e1e) [concrete]
// CHECK:STDOUT:   %.899: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.452, %Destroy.facet.e1e [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Core.import_ref.bb6: @Optional.%Optional.HasValue.type (%Optional.HasValue.type.e9e) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.HasValue (constants.%Optional.HasValue.6cd)]
// CHECK:STDOUT:   %Core.import_ref.daba: @Optional.%Optional.Get.type (%Optional.Get.type.bb9) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.Get (constants.%Optional.Get.fa1)]
// CHECK:STDOUT:   %Core.import_ref.0c6: type = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%DefaultOptionalStorage (constants.%DefaultOptionalStorage.d50)]
// CHECK:STDOUT:   %Core.import_ref.6d6: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None.type (%T.as_type.as.OptionalStorage.impl.None.type.f62) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None (constants.%T.as_type.as.OptionalStorage.impl.None.faf)]
// CHECK:STDOUT:   %Core.import_ref.6f3: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some.type (%T.as_type.as.OptionalStorage.impl.Some.type.973) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some (constants.%T.as_type.as.OptionalStorage.impl.Some.c3a)]
// CHECK:STDOUT:   %Core.import_ref.af2: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has.type (%T.as_type.as.OptionalStorage.impl.Has.type.d76) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has (constants.%T.as_type.as.OptionalStorage.impl.Has.aa4)]
// CHECK:STDOUT:   %Core.import_ref.e31: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get.type (%T.as_type.as.OptionalStorage.impl.Get.type.671) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get (constants.%T.as_type.as.OptionalStorage.impl.Get.a54)]
// CHECK:STDOUT:   %Core.import_ref.cea = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %OptionalStorage.impl_witness_table.199 = impl_witness_table (%Core.import_ref.0c6, %Core.import_ref.6d6, %Core.import_ref.6f3, %Core.import_ref.af2, %Core.import_ref.e31, %Core.import_ref.cea), @T.as_type.as.OptionalStorage.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.e69: @Float.as.Copy.impl.%Float.as.Copy.impl.Op.type (%Float.as.Copy.impl.Op.type.ff3) = import_ref Core//prelude/types/float, loc{{\d+_\d+}}, loaded [symbolic = @Float.as.Copy.impl.%Float.as.Copy.impl.Op (constants.%Float.as.Copy.impl.Op.d93)]
// CHECK:STDOUT:   %Copy.impl_witness_table.4e8 = impl_witness_table (%Core.import_ref.e69), @Float.as.Copy.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.301: %facet_type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%facet_value (constants.%facet_value.194)]
// CHECK:STDOUT:   %Core.import_ref.89f: %Destroy.type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%Destroy.facet (constants.%Destroy.facet.593)]
// CHECK:STDOUT:   %Core.import_ref.940: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor.type (%R.as_type.as.Iterate.impl.NewCursor.type.127) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor (constants.%R.as_type.as.Iterate.impl.NewCursor.627)]
// CHECK:STDOUT:   %Core.import_ref.fe7: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next.type (%R.as_type.as.Iterate.impl.Next.type.d8f) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next (constants.%R.as_type.as.Iterate.impl.Next.c6d)]
// CHECK:STDOUT:   %Iterate.impl_witness_table.ccd = impl_witness_table (%Core.import_ref.301, %Core.import_ref.89f, %Core.import_ref.940, %Core.import_ref.fe7), @R.as_type.as.Iterate.impl [concrete]
// CHECK:STDOUT:   %Core.import_ref.cb3: @Float.as.AddAssignWith.impl.%Float.as.AddAssignWith.impl.Op.type (%Float.as.AddAssignWith.impl.Op.type.fdd) = import_ref Core//prelude/types/float, loc{{\d+_\d+}}, loaded [symbolic = @Float.as.AddAssignWith.impl.%Float.as.AddAssignWith.impl.Op (constants.%Float.as.AddAssignWith.impl.Op.430)]
// CHECK:STDOUT:   %AddAssignWith.impl_witness_table = impl_witness_table (%Core.import_ref.cb3), @Float.as.AddAssignWith.impl [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Test(%R.loc22_10.2: %Iterate_where.type.a32) {
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %Iterate.lookup_impl_witness: <witness> = lookup_impl_witness %R.loc22_10.1, @Iterate [symbolic = %Iterate.lookup_impl_witness (constants.%Iterate.lookup_impl_witness.93c)]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.loc22_55.1, (%Iterate.lookup_impl_witness) [symbolic = %Iterate.facet (constants.%Iterate.facet.94d)]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.NewCursor.type (constants.%Iterate.WithSelf.NewCursor.type.4c7)]
// CHECK:STDOUT:   %.loc26_19.12: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type, %Iterate.facet [symbolic = %.loc26_19.12 (constants.%.a62)]
// CHECK:STDOUT:   %impl.elem2.loc26_19.2: @Test.%.loc26_19.12 (%.a62) = impl_witness_access %Iterate.lookup_impl_witness, element2 [symbolic = %impl.elem2.loc26_19.2 (constants.%impl.elem2.c7b)]
// CHECK:STDOUT:   %specific_impl_fn.loc26_19.4: <specific function> = specific_impl_function %impl.elem2.loc26_19.2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic = %specific_impl_fn.loc26_19.4 (constants.%specific_impl_fn.1b8)]
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %ptr: type = ptr_type %as_type [symbolic = %ptr (constants.%ptr.bac)]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.Next.type (constants.%Iterate.WithSelf.Next.type.275)]
// CHECK:STDOUT:   %.loc26_19.13: type = fn_type_with_self_type %Iterate.WithSelf.Next.type, %Iterate.facet [symbolic = %.loc26_19.13 (constants.%.a06)]
// CHECK:STDOUT:   %impl.elem3.loc26_19.2: @Test.%.loc26_19.13 (%.a06) = impl_witness_access %Iterate.lookup_impl_witness, element3 [symbolic = %impl.elem3.loc26_19.2 (constants.%impl.elem3.7bd)]
// CHECK:STDOUT:   %specific_impl_fn.loc26_19.5: <specific function> = specific_impl_function %impl.elem3.loc26_19.2, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic = %specific_impl_fn.loc26_19.5 (constants.%specific_impl_fn.666)]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1) [symbolic = %Destroy.WithSelf.Op.type (constants.%Destroy.WithSelf.Op.type.41f)]
// CHECK:STDOUT:   %.loc26_19.14: type = fn_type_with_self_type %Destroy.WithSelf.Op.type, %impl.elem1 [symbolic = %.loc26_19.14 (constants.%.148)]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness: <witness> = lookup_impl_witness %impl.elem1, @Destroy [symbolic = %Destroy.lookup_impl_witness (constants.%Destroy.lookup_impl_witness.def)]
// CHECK:STDOUT:   %impl.elem0.loc26_19.2: @Test.%.loc26_19.14 (%.148) = impl_witness_access %Destroy.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc26_19.2 (constants.%impl.elem0.461)]
// CHECK:STDOUT:   %specific_impl_fn.loc26_19.6: <specific function> = specific_impl_function %impl.elem0.loc26_19.2, @Destroy.WithSelf.Op(%impl.elem1) [symbolic = %specific_impl_fn.loc26_19.6 (constants.%specific_impl_fn.095)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%r.param: @Test.%R.as_type.loc22_55.1 (%R.as_type.087)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:     name_binding_decl {
// CHECK:STDOUT:       %i.patt: %pattern_type.fb7 = value_binding_pattern i [concrete]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %r.ref: @Test.%R.as_type.loc22_55.1 (%R.as_type.087) = name_ref r, %r
// CHECK:STDOUT:     %impl.elem2.loc26_19.1: @Test.%.loc26_19.12 (%.a62) = impl_witness_access constants.%Iterate.lookup_impl_witness.93c, element2 [symbolic = %impl.elem2.loc26_19.2 (constants.%impl.elem2.c7b)]
// CHECK:STDOUT:     %bound_method.loc26_19.1: <bound method> = bound_method %r.ref, %impl.elem2.loc26_19.1
// CHECK:STDOUT:     %specific_impl_fn.loc26_19.1: <specific function> = specific_impl_function %impl.elem2.loc26_19.1, @Iterate.WithSelf.NewCursor(constants.%Iterate.facet.94d) [symbolic = %specific_impl_fn.loc26_19.4 (constants.%specific_impl_fn.1b8)]
// CHECK:STDOUT:     %bound_method.loc26_19.2: <bound method> = bound_method %r.ref, %specific_impl_fn.loc26_19.1
// CHECK:STDOUT:     %var: ref @Test.%as_type (%as_type.8e4) = var invalid
// CHECK:STDOUT:     %Iterate.WithSelf.NewCursor.call: init @Test.%as_type (%as_type.8e4) to %var = call %bound_method.loc26_19.2(%r.ref)
// CHECK:STDOUT:     assign %var, %Iterate.WithSelf.NewCursor.call
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.next:
// CHECK:STDOUT:     %addr: @Test.%ptr (%ptr.bac) = addr_of %var
// CHECK:STDOUT:     %impl.elem3.loc26_19.1: @Test.%.loc26_19.13 (%.a06) = impl_witness_access constants.%Iterate.lookup_impl_witness.93c, element3 [symbolic = %impl.elem3.loc26_19.2 (constants.%impl.elem3.7bd)]
// CHECK:STDOUT:     %bound_method.loc26_19.3: <bound method> = bound_method %r.ref, %impl.elem3.loc26_19.1
// CHECK:STDOUT:     %.loc26_19.1: %Destroy.type = converted constants.%as_type.8e4, constants.%impl.elem1.7a9 [symbolic = %impl.elem1 (constants.%impl.elem1.7a9)]
// CHECK:STDOUT:     %specific_impl_fn.loc26_19.2: <specific function> = specific_impl_function %impl.elem3.loc26_19.1, @Iterate.WithSelf.Next(constants.%Iterate.facet.94d) [symbolic = %specific_impl_fn.loc26_19.5 (constants.%specific_impl_fn.666)]
// CHECK:STDOUT:     %bound_method.loc26_19.4: <bound method> = bound_method %r.ref, %specific_impl_fn.loc26_19.2
// CHECK:STDOUT:     %.loc26_19.2: ref %Optional.c42 = temporary_storage
// CHECK:STDOUT:     %Iterate.WithSelf.Next.call: init %Optional.c42 to %.loc26_19.2 = call %bound_method.loc26_19.4(%r.ref, %addr)
// CHECK:STDOUT:     %.loc26_19.3: ref %Optional.c42 = temporary %.loc26_19.2, %Iterate.WithSelf.Next.call
// CHECK:STDOUT:     %.loc26_19.4: %Optional.HasValue.type.c09 = specific_constant imports.%Core.import_ref.bb6, @Optional(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.HasValue.53b]
// CHECK:STDOUT:     %HasValue.ref: %Optional.HasValue.type.c09 = name_ref HasValue, %.loc26_19.4 [concrete = constants.%Optional.HasValue.53b]
// CHECK:STDOUT:     %Optional.HasValue.bound: <bound method> = bound_method %.loc26_19.3, %HasValue.ref
// CHECK:STDOUT:     %Optional.HasValue.specific_fn: <specific function> = specific_function %HasValue.ref, @Optional.HasValue(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.HasValue.specific_fn]
// CHECK:STDOUT:     %bound_method.loc26_19.5: <bound method> = bound_method %.loc26_19.3, %Optional.HasValue.specific_fn
// CHECK:STDOUT:     %.loc26_19.5: %Optional.c42 = acquire_value %.loc26_19.3
// CHECK:STDOUT:     %Optional.HasValue.call: init bool = call %bound_method.loc26_19.5(%.loc26_19.5)
// CHECK:STDOUT:     %.loc26_19.6: bool = value_of_initializer %Optional.HasValue.call
// CHECK:STDOUT:     %.loc26_19.7: bool = converted %Optional.HasValue.call, %.loc26_19.6
// CHECK:STDOUT:     if %.loc26_19.7 br !for.body else br !for.done
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.body:
// CHECK:STDOUT:     %.loc26_19.8: %Optional.Get.type.4f6 = specific_constant imports.%Core.import_ref.daba, @Optional(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.Get.5f1]
// CHECK:STDOUT:     %Get.ref: %Optional.Get.type.4f6 = name_ref Get, %.loc26_19.8 [concrete = constants.%Optional.Get.5f1]
// CHECK:STDOUT:     %Optional.Get.bound: <bound method> = bound_method %.loc26_19.3, %Get.ref
// CHECK:STDOUT:     %Optional.Get.specific_fn: <specific function> = specific_function %Get.ref, @Optional.Get(constants.%OptionalStorage.facet.c07) [concrete = constants.%Optional.Get.specific_fn]
// CHECK:STDOUT:     %bound_method.loc26_19.6: <bound method> = bound_method %.loc26_19.3, %Optional.Get.specific_fn
// CHECK:STDOUT:     %.loc26_19.9: %Optional.c42 = acquire_value %.loc26_19.3
// CHECK:STDOUT:     %Optional.Get.call: init %f64.dc1 = call %bound_method.loc26_19.6(%.loc26_19.9)
// CHECK:STDOUT:     %f64.loc26: type = type_literal constants.%f64.dc1 [concrete = constants.%f64.dc1]
// CHECK:STDOUT:     %.loc26_19.10: %f64.dc1 = value_of_initializer %Optional.Get.call
// CHECK:STDOUT:     %.loc26_19.11: %f64.dc1 = converted %Optional.Get.call, %.loc26_19.10
// CHECK:STDOUT:     %i: %f64.dc1 = value_binding i, %.loc26_19.11
// CHECK:STDOUT:     %sum.ref: ref %f64.dc1 = name_ref sum, %sum
// CHECK:STDOUT:     %i.ref: %f64.dc1 = name_ref i, %i
// CHECK:STDOUT:     %impl.elem0.loc27: %.746 = impl_witness_access constants.%AddAssignWith.impl_witness.e85, element0 [concrete = constants.%Float.as.AddAssignWith.impl.Op.ac1]
// CHECK:STDOUT:     %bound_method.loc27_9.1: <bound method> = bound_method %sum.ref, %impl.elem0.loc27
// CHECK:STDOUT:     %specific_fn.loc27: <specific function> = specific_function %impl.elem0.loc27, @Float.as.AddAssignWith.impl.Op(constants.%int_64) [concrete = constants.%Float.as.AddAssignWith.impl.Op.specific_fn]
// CHECK:STDOUT:     %bound_method.loc27_9.2: <bound method> = bound_method %sum.ref, %specific_fn.loc27
// CHECK:STDOUT:     %Float.as.AddAssignWith.impl.Op.call: init %empty_tuple.type = call %bound_method.loc27_9.2(%sum.ref, %i.ref)
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.done:
// CHECK:STDOUT:     %Destroy.Op.bound.loc26: <bound method> = bound_method %.loc26_19.3, constants.%Destroy.Op.1a2547.8
// CHECK:STDOUT:     %Destroy.Op.call.loc26: init %empty_tuple.type = call %Destroy.Op.bound.loc26(%.loc26_19.3)
// CHECK:STDOUT:     %impl.elem0.loc26_19.1: @Test.%.loc26_19.14 (%.148) = impl_witness_access constants.%Destroy.lookup_impl_witness.def, element0 [symbolic = %impl.elem0.loc26_19.2 (constants.%impl.elem0.461)]
// CHECK:STDOUT:     %bound_method.loc26_19.7: <bound method> = bound_method %var, %impl.elem0.loc26_19.1
// CHECK:STDOUT:     %specific_impl_fn.loc26_19.3: <specific function> = specific_impl_function %impl.elem0.loc26_19.1, @Destroy.WithSelf.Op(constants.%impl.elem1.7a9) [symbolic = %specific_impl_fn.loc26_19.6 (constants.%specific_impl_fn.095)]
// CHECK:STDOUT:     %bound_method.loc26_19.8: <bound method> = bound_method %var, %specific_impl_fn.loc26_19.3
// CHECK:STDOUT:     %Destroy.WithSelf.Op.call: init %empty_tuple.type = call %bound_method.loc26_19.8(%var)
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc26_19.1(%self.param: ref %MaybeUnformed.b7e) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc26_19.2(%self.param: ref bool) = "no_op";
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc26_19.3(%self.param: ref %struct_type.value.has_value.ad9) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc26_19.4(%self.param: ref %DefaultOptionalStorage.541) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc26_19.5(%self.param: ref %Optional.c42) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%R.c6e) {
// CHECK:STDOUT:   %R.loc22_10.1 => constants.%R.c6e
// CHECK:STDOUT:   %R.as_type.loc22_55.1 => constants.%R.as_type.087
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.3d7
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.37c) {
// CHECK:STDOUT:   %R.loc22_10.1 => constants.%facet_value.37c
// CHECK:STDOUT:   %R.as_type.loc22_55.1 => constants.%MutableRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.992
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc22 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.57f
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.d2f
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.1cb
// CHECK:STDOUT:   %.loc26_19.12 => constants.%.dab
// CHECK:STDOUT:   %impl.elem2.loc26_19.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.b0d
// CHECK:STDOUT:   %specific_impl_fn.loc26_19.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.e1e
// CHECK:STDOUT:   %as_type => constants.%tuple.type.dd0
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.843
// CHECK:STDOUT:   %ptr => constants.%ptr.a4f
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.ba9
// CHECK:STDOUT:   %.loc26_19.13 => constants.%.7d2
// CHECK:STDOUT:   %impl.elem3.loc26_19.2 => constants.%R.as_type.as.Iterate.impl.Next.c07
// CHECK:STDOUT:   %specific_impl_fn.loc26_19.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.452
// CHECK:STDOUT:   %.loc26_19.14 => constants.%.899
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.9
// CHECK:STDOUT:   %impl.elem0.loc26_19.2 => constants.%Destroy.Op.1a2547.9
// CHECK:STDOUT:   %specific_impl_fn.loc26_19.6 => constants.%Destroy.Op.1a2547.9
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: --- adl_returns_different_types.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Iterate.type: type = facet_type <@Iterate> [concrete]
// CHECK:STDOUT:   %OptionalStorage.type: type = facet_type <@OptionalStorage> [concrete]
// CHECK:STDOUT:   %Destroy.type: type = facet_type <@Destroy> [concrete]
// CHECK:STDOUT:   %facet_type: type = facet_type <@Destroy & @Copy> [concrete]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [concrete]
// CHECK:STDOUT:   %T.220: %OptionalStorage.type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Optional.Get.type.bb9: type = fn_type @Optional.Get, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.Get.fa1: %Optional.Get.type.bb9 = struct_value () [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.e9e: type = fn_type @Optional.HasValue, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.6cd: %Optional.HasValue.type.e9e = struct_value () [symbolic]
// CHECK:STDOUT:   %T.283: %facet_type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.d50: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.type.671: type = fn_type @T.as_type.as.OptionalStorage.impl.Get, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.a54: %T.as_type.as.OptionalStorage.impl.Get.type.671 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.type.d76: type = fn_type @T.as_type.as.OptionalStorage.impl.Has, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.aa4: %T.as_type.as.OptionalStorage.impl.Has.type.d76 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.type.973: type = fn_type @T.as_type.as.OptionalStorage.impl.Some, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.c3a: %T.as_type.as.OptionalStorage.impl.Some.type.973 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.type.f62: type = fn_type @T.as_type.as.OptionalStorage.impl.None, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.faf: %T.as_type.as.OptionalStorage.impl.None.type.f62 = struct_value () [symbolic]
// CHECK:STDOUT:   %.Self.0.500: %Iterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.1d8: <witness> = lookup_impl_witness %.Self.0.500, @Iterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.294: %facet_type = impl_witness_access %Iterate.lookup_impl_witness.1d8, element0 [symbolic_self]
// CHECK:STDOUT:   %ValueType: type = class_type @ValueType [concrete]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [concrete]
// CHECK:STDOUT:   %complete_type.357: <witness> = complete_type_witness %empty_struct_type [concrete]
// CHECK:STDOUT:   %pattern_type.e41: type = pattern_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor.type: type = fn_type @ValueType.cpp_destructor [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor: %ValueType.cpp_destructor.type = struct_value () [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.79266b.1: type = fn_type @ValueType.Op.1 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4c94b9.1: %ValueType.Op.type.79266b.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.fef: <witness> = custom_witness (%ValueType.Op.4c94b9.1), @Destroy [concrete]
// CHECK:STDOUT:   %const.773: type = const_type %ValueType [concrete]
// CHECK:STDOUT:   %ptr.32e: type = ptr_type %const.773 [concrete]
// CHECK:STDOUT:   %ptr.9d3: type = ptr_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.79266b.2: type = fn_type @ValueType.Op.2 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4c94b9.2: %ValueType.Op.type.79266b.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.c19: <witness> = custom_witness (%ValueType.Op.4c94b9.2), @Copy [concrete]
// CHECK:STDOUT:   %facet_value.ccb: %facet_type = facet_value %ValueType, (%custom_witness.fef, %custom_witness.c19) [concrete]
// CHECK:STDOUT:   %Iterate_where.type.f9d: type = facet_type <@Iterate where %impl.elem0.294 = %facet_value.ccb> [concrete]
// CHECK:STDOUT:   %R.db4: %Iterate_where.type.f9d = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %R.as_type.c37: type = facet_access_type %R.db4 [symbolic]
// CHECK:STDOUT:   %pattern_type.17d: type = pattern_type %R.as_type.c37 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.type: type = facet_type <@CppRangeForIterate> [concrete]
// CHECK:STDOUT:   %.Self.0.aed: %CppRangeForIterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.f6b: <witness> = lookup_impl_witness %.Self.0.aed, @CppRangeForIterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.b73: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element0 [symbolic_self]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.595: <witness> = lookup_impl_witness %impl.elem0.b73, @CppUnsafeDeref [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.a2f: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.595, element0 [symbolic_self]
// CHECK:STDOUT:   %impl.elem1.228: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element1 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate_where.type: type = facet_type <@CppRangeForIterate where %impl.elem0.b73 impls @Destroy and %impl.elem0.b73 impls @Copy and %impl.elem0.b73 impls @CppUnsafeDeref and %impl.elem0.b73 impls @EqWith, @EqWith(%impl.elem1.228) and %impl.elem0.b73 impls @Inc and %impl.elem0.a2f impls @Destroy and %impl.elem0.a2f impls @Copy and %impl.elem1.228 impls @Destroy and %impl.elem1.228 impls @Copy> [concrete]
// CHECK:STDOUT:   %R.39b: %CppRangeForIterate_where.type = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.7e2712.2: <witness> = lookup_impl_witness %R.39b, @CppRangeForIterate [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a0bff.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element1 [symbolic]
// CHECK:STDOUT:   %impl.elem0.73eb7f.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element0 [symbolic]
// CHECK:STDOUT:   %tuple.type.3cf: type = tuple_type (%impl.elem0.73eb7f.2, %impl.elem1.7a0bff.2) [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.69f: <witness> = lookup_impl_witness %tuple.type.3cf, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.facet.593: %Destroy.type = facet_value %tuple.type.3cf, (%Destroy.lookup_impl_witness.69f) [symbolic]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.aa7: <witness> = lookup_impl_witness %impl.elem0.73eb7f.2, @CppUnsafeDeref [symbolic]
// CHECK:STDOUT:   %impl.elem0.af7: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.aa7, element0 [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.ec3: <witness> = lookup_impl_witness %impl.elem0.af7, @Destroy [symbolic]
// CHECK:STDOUT:   %Copy.lookup_impl_witness.a7a: <witness> = lookup_impl_witness %impl.elem0.af7, @Copy [symbolic]
// CHECK:STDOUT:   %facet_value.194: %facet_type = facet_value %impl.elem0.af7, (%Destroy.lookup_impl_witness.ec3, %Copy.lookup_impl_witness.a7a) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.d8f: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c6d: %R.as_type.as.Iterate.impl.Next.type.d8f = struct_value () [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.127: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.627: %R.as_type.as.Iterate.impl.NewCursor.type.127 = struct_value () [symbolic]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.173: <witness> = lookup_impl_witness %R.db4, @Iterate [symbolic]
// CHECK:STDOUT:   %Iterate.facet.b38: %Iterate.type = facet_value %R.as_type.c37, (%Iterate.lookup_impl_witness.173) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.5cd: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.d51: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %.592: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.5cd, %Iterate.facet.b38 [symbolic]
// CHECK:STDOUT:   %impl.elem2.ae2: %.592 = impl_witness_access %Iterate.lookup_impl_witness.173, element2 [symbolic]
// CHECK:STDOUT:   %impl.elem1.834: %Destroy.type = impl_witness_access %Iterate.lookup_impl_witness.173, element1 [symbolic]
// CHECK:STDOUT:   %as_type.e41: type = facet_access_type %impl.elem1.834 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.06e: <specific function> = specific_impl_function %impl.elem2.ae2, @Iterate.WithSelf.NewCursor(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %ptr.d27: type = ptr_type %as_type.e41 [symbolic]
// CHECK:STDOUT:   %.524: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.d51, %Iterate.facet.b38 [symbolic]
// CHECK:STDOUT:   %impl.elem3.7a5: %.524 = impl_witness_access %Iterate.lookup_impl_witness.173, element3 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.257: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%facet_value.ccb) [concrete]
// CHECK:STDOUT:   %OptionalStorage.impl_witness.9db: <witness> = impl_witness imports.%OptionalStorage.impl_witness_table.199, @T.as_type.as.OptionalStorage.impl(%facet_value.ccb) [concrete]
// CHECK:STDOUT:   %OptionalStorage.facet.cac: %OptionalStorage.type = facet_value %ValueType, (%OptionalStorage.impl_witness.9db) [concrete]
// CHECK:STDOUT:   %Optional.c14: type = class_type @Optional, @Optional(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %specific_impl_fn.24b: <specific function> = specific_impl_function %impl.elem3.7a5, @Iterate.WithSelf.Next(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.36e: type = fn_type @Optional.HasValue, @Optional(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %Optional.HasValue.3c0: %Optional.HasValue.type.36e = struct_value () [concrete]
// CHECK:STDOUT:   %Optional.Get.type.862: type = fn_type @Optional.Get, @Optional(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %Optional.Get.28e: %Optional.Get.type.862 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.facet.306: %Destroy.type = facet_value %ValueType, (%custom_witness.fef) [concrete]
// CHECK:STDOUT:   %MaybeUnformed.669: type = class_type @MaybeUnformed, @MaybeUnformed(%Destroy.facet.306) [concrete]
// CHECK:STDOUT:   %struct_type.value.has_value.5a1: type = struct_type {.value: %MaybeUnformed.669, .has_value: bool} [concrete]
// CHECK:STDOUT:   %Optional.HasValue.specific_fn: <specific function> = specific_function %Optional.HasValue.3c0, @Optional.HasValue(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %Optional.Get.specific_fn: <specific function> = specific_function %Optional.Get.28e, @Optional.Get(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator.type: type = fn_type @ValueType.cpp_operator [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator: %ValueType.cpp_operator.type = struct_value () [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.type: type = fn_type @operator_PlusEqual__carbon_thunk [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk: %operator_PlusEqual__carbon_thunk.type = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.6: type = fn_type @Destroy.Op.loc31_31.5 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.6: %Destroy.Op.type.1d8f74.6 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.198: <witness> = lookup_impl_witness %impl.elem1.834, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.9d6: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1.834) [symbolic]
// CHECK:STDOUT:   %.57c: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.9d6, %impl.elem1.834 [symbolic]
// CHECK:STDOUT:   %impl.elem0.152: %.57c = impl_witness_access %Destroy.lookup_impl_witness.198, element0 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.9fb: <specific function> = specific_impl_function %impl.elem0.152, @Destroy.WithSelf.Op(%impl.elem1.834) [symbolic]
// CHECK:STDOUT:   %ConstRange: type = class_type @ConstRange [concrete]
// CHECK:STDOUT:   %pattern_type.025: type = pattern_type %ConstRange [concrete]
// CHECK:STDOUT:   %Iterator: type = class_type @Iterator.1 [concrete]
// CHECK:STDOUT:   %Sentinel: type = class_type @Sentinel.1 [concrete]
// CHECK:STDOUT:   %Begin.type: type = fn_type @Begin [concrete]
// CHECK:STDOUT:   %Begin: %Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %End.type: type = fn_type @End [concrete]
// CHECK:STDOUT:   %End: %End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.c2f: <witness> = custom_witness (%Iterator, %Sentinel, %Begin, %End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.1: type = fn_type @Iterator.Op.1 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.1: %Iterator.Op.type.ac7e09.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.1d3: <witness> = custom_witness (%ValueType, %Iterator.Op.583fda.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.2: type = fn_type @Iterator.Op.2 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.2: %Iterator.Op.type.ac7e09.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.21358e.1: <witness> = custom_witness (%Iterator.Op.583fda.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.3: type = fn_type @Iterator.Op.3 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.3: %Iterator.Op.type.ac7e09.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.a3150e.1: <witness> = custom_witness (%Iterator.Op.583fda.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type: type = fn_type @Equal [concrete]
// CHECK:STDOUT:   %Equal: %Equal.type = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type: type = fn_type @NotEqual [concrete]
// CHECK:STDOUT:   %NotEqual: %NotEqual.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.aa4: <witness> = custom_witness (%Equal, %NotEqual), @EqWith, @EqWith(%Sentinel) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.ac7e09.4: type = fn_type @Iterator.Op.4 [concrete]
// CHECK:STDOUT:   %Iterator.Op.583fda.4: %Iterator.Op.type.ac7e09.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.393: <witness> = custom_witness (%Iterator.Op.583fda.4), @Inc [concrete]
// CHECK:STDOUT:   %Sentinel.Op.type.ac7e09.1: type = fn_type @Sentinel.Op.1 [concrete]
// CHECK:STDOUT:   %Sentinel.Op.583fda.1: %Sentinel.Op.type.ac7e09.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.21358e.2: <witness> = custom_witness (%Sentinel.Op.583fda.1), @Destroy [concrete]
// CHECK:STDOUT:   %Sentinel.Op.type.ac7e09.2: type = fn_type @Sentinel.Op.2 [concrete]
// CHECK:STDOUT:   %Sentinel.Op.583fda.2: %Sentinel.Op.type.ac7e09.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.a3150e.2: <witness> = custom_witness (%Sentinel.Op.583fda.2), @Copy [concrete]
// CHECK:STDOUT:   %facet_value.b1e: %CppRangeForIterate_where.type = facet_value %ConstRange, (%custom_witness.fef, %custom_witness.c19, %custom_witness.c2f, %custom_witness.21358e.1, %custom_witness.a3150e.1, %custom_witness.1d3, %custom_witness.aa4, %custom_witness.393, %custom_witness.21358e.2, %custom_witness.a3150e.2) [concrete]
// CHECK:STDOUT:   %tuple.type.df8: type = tuple_type (%Iterator, %Sentinel) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.7: type = fn_type @Destroy.Op.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.7: %Destroy.Op.type.1d8f74.7 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.7: <witness> = custom_witness (%Destroy.Op.1a2547.7), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.777: %Destroy.type = facet_value %tuple.type.df8, (%custom_witness.df9cc1.7) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.887: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.b1e) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.9c3: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.b1e) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.4e7: %R.as_type.as.Iterate.impl.NewCursor.type.9c3 = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.795: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.b1e) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.4d5: %R.as_type.as.Iterate.impl.Next.type.795 = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.9a5: %Iterate.type = facet_value %ConstRange, (%Iterate.impl_witness.887) [concrete]
// CHECK:STDOUT:   %facet_value.a17: %Iterate_where.type.f9d = facet_value %ConstRange, (%Iterate.impl_witness.887) [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.8d8: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.9a5) [concrete]
// CHECK:STDOUT:   %.2d3f: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.8d8, %Iterate.facet.9a5 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.4e7, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.b1e) [concrete]
// CHECK:STDOUT:   %complete_type.e35: <witness> = complete_type_witness %tuple.type.df8 [concrete]
// CHECK:STDOUT:   %ptr.fc0: type = ptr_type %tuple.type.df8 [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.069: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.9a5) [concrete]
// CHECK:STDOUT:   %.e3b: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.069, %Iterate.facet.9a5 [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.4d5, @R.as_type.as.Iterate.impl.Next(%facet_value.b1e) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.589: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.777) [concrete]
// CHECK:STDOUT:   %.4e1: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.589, %Destroy.facet.777 [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Cpp: <namespace> = namespace file.%Cpp.import_cpp, [concrete] {
// CHECK:STDOUT:     .N = %N
// CHECK:STDOUT:     import Cpp//...
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.bb6: @Optional.%Optional.HasValue.type (%Optional.HasValue.type.e9e) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.HasValue (constants.%Optional.HasValue.6cd)]
// CHECK:STDOUT:   %Core.import_ref.daba: @Optional.%Optional.Get.type (%Optional.Get.type.bb9) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.Get (constants.%Optional.Get.fa1)]
// CHECK:STDOUT:   %Core.import_ref.0c6: type = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%DefaultOptionalStorage (constants.%DefaultOptionalStorage.d50)]
// CHECK:STDOUT:   %Core.import_ref.6d6: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None.type (%T.as_type.as.OptionalStorage.impl.None.type.f62) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None (constants.%T.as_type.as.OptionalStorage.impl.None.faf)]
// CHECK:STDOUT:   %Core.import_ref.6f3: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some.type (%T.as_type.as.OptionalStorage.impl.Some.type.973) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some (constants.%T.as_type.as.OptionalStorage.impl.Some.c3a)]
// CHECK:STDOUT:   %Core.import_ref.af2: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has.type (%T.as_type.as.OptionalStorage.impl.Has.type.d76) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has (constants.%T.as_type.as.OptionalStorage.impl.Has.aa4)]
// CHECK:STDOUT:   %Core.import_ref.e31: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get.type (%T.as_type.as.OptionalStorage.impl.Get.type.671) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get (constants.%T.as_type.as.OptionalStorage.impl.Get.a54)]
// CHECK:STDOUT:   %Core.import_ref.cea = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %OptionalStorage.impl_witness_table.199 = impl_witness_table (%Core.import_ref.0c6, %Core.import_ref.6d6, %Core.import_ref.6f3, %Core.import_ref.af2, %Core.import_ref.e31, %Core.import_ref.cea), @T.as_type.as.OptionalStorage.impl [concrete]
// CHECK:STDOUT:   %N: <namespace> = namespace [concrete] {
// CHECK:STDOUT:     .ValueType = %ValueType.decl
// CHECK:STDOUT:     .ConstRange = %ConstRange.decl
// CHECK:STDOUT:     import Cpp//...
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %ValueType.decl: type = class_decl @ValueType [concrete = constants.%ValueType] {} {}
// CHECK:STDOUT:   %ValueType.cpp_destructor.decl: %ValueType.cpp_destructor.type = fn_decl @ValueType.cpp_destructor [concrete = constants.%ValueType.cpp_destructor] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.301: %facet_type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%facet_value (constants.%facet_value.194)]
// CHECK:STDOUT:   %Core.import_ref.89f: %Destroy.type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%Destroy.facet (constants.%Destroy.facet.593)]
// CHECK:STDOUT:   %Core.import_ref.940: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor.type (%R.as_type.as.Iterate.impl.NewCursor.type.127) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor (constants.%R.as_type.as.Iterate.impl.NewCursor.627)]
// CHECK:STDOUT:   %Core.import_ref.fe7: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next.type (%R.as_type.as.Iterate.impl.Next.type.d8f) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next (constants.%R.as_type.as.Iterate.impl.Next.c6d)]
// CHECK:STDOUT:   %Iterate.impl_witness_table.ccd = impl_witness_table (%Core.import_ref.301, %Core.import_ref.89f, %Core.import_ref.940, %Core.import_ref.fe7), @R.as_type.as.Iterate.impl [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator.decl: %ValueType.cpp_operator.type = fn_decl @ValueType.cpp_operator [concrete = constants.%ValueType.cpp_operator] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.decl: %operator_PlusEqual__carbon_thunk.type = fn_decl @operator_PlusEqual__carbon_thunk [concrete = constants.%operator_PlusEqual__carbon_thunk] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %ConstRange.decl: type = class_decl @ConstRange [concrete = constants.%ConstRange] {} {}
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Test(%R.loc27_10.2: %Iterate_where.type.f9d) {
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %Iterate.lookup_impl_witness: <witness> = lookup_impl_witness %R.loc27_10.1, @Iterate [symbolic = %Iterate.lookup_impl_witness (constants.%Iterate.lookup_impl_witness.173)]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.loc27_67.1, (%Iterate.lookup_impl_witness) [symbolic = %Iterate.facet (constants.%Iterate.facet.b38)]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.NewCursor.type (constants.%Iterate.WithSelf.NewCursor.type.5cd)]
// CHECK:STDOUT:   %.loc31_31.13: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type, %Iterate.facet [symbolic = %.loc31_31.13 (constants.%.592)]
// CHECK:STDOUT:   %impl.elem2.loc31_31.2: @Test.%.loc31_31.13 (%.592) = impl_witness_access %Iterate.lookup_impl_witness, element2 [symbolic = %impl.elem2.loc31_31.2 (constants.%impl.elem2.ae2)]
// CHECK:STDOUT:   %specific_impl_fn.loc31_31.4: <specific function> = specific_impl_function %impl.elem2.loc31_31.2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic = %specific_impl_fn.loc31_31.4 (constants.%specific_impl_fn.06e)]
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %ptr: type = ptr_type %as_type [symbolic = %ptr (constants.%ptr.d27)]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.Next.type (constants.%Iterate.WithSelf.Next.type.d51)]
// CHECK:STDOUT:   %.loc31_31.14: type = fn_type_with_self_type %Iterate.WithSelf.Next.type, %Iterate.facet [symbolic = %.loc31_31.14 (constants.%.524)]
// CHECK:STDOUT:   %impl.elem3.loc31_31.2: @Test.%.loc31_31.14 (%.524) = impl_witness_access %Iterate.lookup_impl_witness, element3 [symbolic = %impl.elem3.loc31_31.2 (constants.%impl.elem3.7a5)]
// CHECK:STDOUT:   %specific_impl_fn.loc31_31.5: <specific function> = specific_impl_function %impl.elem3.loc31_31.2, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic = %specific_impl_fn.loc31_31.5 (constants.%specific_impl_fn.24b)]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1) [symbolic = %Destroy.WithSelf.Op.type (constants.%Destroy.WithSelf.Op.type.9d6)]
// CHECK:STDOUT:   %.loc31_31.15: type = fn_type_with_self_type %Destroy.WithSelf.Op.type, %impl.elem1 [symbolic = %.loc31_31.15 (constants.%.57c)]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness: <witness> = lookup_impl_witness %impl.elem1, @Destroy [symbolic = %Destroy.lookup_impl_witness (constants.%Destroy.lookup_impl_witness.198)]
// CHECK:STDOUT:   %impl.elem0.loc31_31.2: @Test.%.loc31_31.15 (%.57c) = impl_witness_access %Destroy.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc31_31.2 (constants.%impl.elem0.152)]
// CHECK:STDOUT:   %specific_impl_fn.loc31_31.6: <specific function> = specific_impl_function %impl.elem0.loc31_31.2, @Destroy.WithSelf.Op(%impl.elem1) [symbolic = %specific_impl_fn.loc31_31.6 (constants.%specific_impl_fn.9fb)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%r.param: @Test.%R.as_type.loc27_67.1 (%R.as_type.c37)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:     name_binding_decl {
// CHECK:STDOUT:       %i.patt: %pattern_type.e41 = value_binding_pattern i [concrete]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %r.ref: @Test.%R.as_type.loc27_67.1 (%R.as_type.c37) = name_ref r, %r
// CHECK:STDOUT:     %impl.elem2.loc31_31.1: @Test.%.loc31_31.13 (%.592) = impl_witness_access constants.%Iterate.lookup_impl_witness.173, element2 [symbolic = %impl.elem2.loc31_31.2 (constants.%impl.elem2.ae2)]
// CHECK:STDOUT:     %bound_method.loc31_31.1: <bound method> = bound_method %r.ref, %impl.elem2.loc31_31.1
// CHECK:STDOUT:     %specific_impl_fn.loc31_31.1: <specific function> = specific_impl_function %impl.elem2.loc31_31.1, @Iterate.WithSelf.NewCursor(constants.%Iterate.facet.b38) [symbolic = %specific_impl_fn.loc31_31.4 (constants.%specific_impl_fn.06e)]
// CHECK:STDOUT:     %bound_method.loc31_31.2: <bound method> = bound_method %r.ref, %specific_impl_fn.loc31_31.1
// CHECK:STDOUT:     %var: ref @Test.%as_type (%as_type.e41) = var invalid
// CHECK:STDOUT:     %Iterate.WithSelf.NewCursor.call: init @Test.%as_type (%as_type.e41) to %var = call %bound_method.loc31_31.2(%r.ref)
// CHECK:STDOUT:     assign %var, %Iterate.WithSelf.NewCursor.call
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.next:
// CHECK:STDOUT:     %addr.loc31: @Test.%ptr (%ptr.d27) = addr_of %var
// CHECK:STDOUT:     %impl.elem3.loc31_31.1: @Test.%.loc31_31.14 (%.524) = impl_witness_access constants.%Iterate.lookup_impl_witness.173, element3 [symbolic = %impl.elem3.loc31_31.2 (constants.%impl.elem3.7a5)]
// CHECK:STDOUT:     %bound_method.loc31_31.3: <bound method> = bound_method %r.ref, %impl.elem3.loc31_31.1
// CHECK:STDOUT:     %.loc31_31.1: %Destroy.type = converted constants.%as_type.e41, constants.%impl.elem1.834 [symbolic = %impl.elem1 (constants.%impl.elem1.834)]
// CHECK:STDOUT:     %specific_impl_fn.loc31_31.2: <specific function> = specific_impl_function %impl.elem3.loc31_31.1, @Iterate.WithSelf.Next(constants.%Iterate.facet.b38) [symbolic = %specific_impl_fn.loc31_31.5 (constants.%specific_impl_fn.24b)]
// CHECK:STDOUT:     %bound_method.loc31_31.4: <bound method> = bound_method %r.ref, %specific_impl_fn.loc31_31.2
// CHECK:STDOUT:     %.loc31_31.2: ref %Optional.c14 = temporary_storage
// CHECK:STDOUT:     %Iterate.WithSelf.Next.call: init %Optional.c14 to %.loc31_31.2 = call %bound_method.loc31_31.4(%r.ref, %addr.loc31)
// CHECK:STDOUT:     %.loc31_31.3: ref %Optional.c14 = temporary %.loc31_31.2, %Iterate.WithSelf.Next.call
// CHECK:STDOUT:     %.loc31_31.4: %Optional.HasValue.type.36e = specific_constant imports.%Core.import_ref.bb6, @Optional(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.HasValue.3c0]
// CHECK:STDOUT:     %HasValue.ref: %Optional.HasValue.type.36e = name_ref HasValue, %.loc31_31.4 [concrete = constants.%Optional.HasValue.3c0]
// CHECK:STDOUT:     %Optional.HasValue.bound: <bound method> = bound_method %.loc31_31.3, %HasValue.ref
// CHECK:STDOUT:     %Optional.HasValue.specific_fn: <specific function> = specific_function %HasValue.ref, @Optional.HasValue(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.HasValue.specific_fn]
// CHECK:STDOUT:     %bound_method.loc31_31.5: <bound method> = bound_method %.loc31_31.3, %Optional.HasValue.specific_fn
// CHECK:STDOUT:     %.loc31_31.5: %Optional.c14 = acquire_value %.loc31_31.3
// CHECK:STDOUT:     %Optional.HasValue.call: init bool = call %bound_method.loc31_31.5(%.loc31_31.5)
// CHECK:STDOUT:     %.loc31_31.6: bool = value_of_initializer %Optional.HasValue.call
// CHECK:STDOUT:     %.loc31_31.7: bool = converted %Optional.HasValue.call, %.loc31_31.6
// CHECK:STDOUT:     if %.loc31_31.7 br !for.body else br !for.done
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.body:
// CHECK:STDOUT:     %.loc31_31.8: %Optional.Get.type.862 = specific_constant imports.%Core.import_ref.daba, @Optional(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.Get.28e]
// CHECK:STDOUT:     %Get.ref: %Optional.Get.type.862 = name_ref Get, %.loc31_31.8 [concrete = constants.%Optional.Get.28e]
// CHECK:STDOUT:     %Optional.Get.bound: <bound method> = bound_method %.loc31_31.3, %Get.ref
// CHECK:STDOUT:     %Optional.Get.specific_fn: <specific function> = specific_function %Get.ref, @Optional.Get(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.Get.specific_fn]
// CHECK:STDOUT:     %bound_method.loc31_31.6: <bound method> = bound_method %.loc31_31.3, %Optional.Get.specific_fn
// CHECK:STDOUT:     %.loc31_31.9: ref %ValueType = temporary_storage
// CHECK:STDOUT:     %.loc31_31.10: %Optional.c14 = acquire_value %.loc31_31.3
// CHECK:STDOUT:     %Optional.Get.call: init %ValueType to %.loc31_31.9 = call %bound_method.loc31_31.6(%.loc31_31.10)
// CHECK:STDOUT:     %.loc31_16: type = splice_block %ValueType.ref.loc31 [concrete = constants.%ValueType] {
// CHECK:STDOUT:       %Cpp.ref.loc31: <namespace> = name_ref Cpp, imports.%Cpp [concrete = imports.%Cpp]
// CHECK:STDOUT:       %N.ref.loc31: <namespace> = name_ref N, imports.%N [concrete = imports.%N]
// CHECK:STDOUT:       %ValueType.ref.loc31: type = name_ref ValueType, imports.%ValueType.decl [concrete = constants.%ValueType]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %.loc31_31.11: ref %ValueType = temporary %.loc31_31.9, %Optional.Get.call
// CHECK:STDOUT:     %.loc31_31.12: %ValueType = acquire_value %.loc31_31.11
// CHECK:STDOUT:     %i: %ValueType = value_binding i, %.loc31_31.12
// CHECK:STDOUT:     %sum.ref: ref %ValueType = name_ref sum, %sum
// CHECK:STDOUT:     %i.ref: %ValueType = name_ref i, %i
// CHECK:STDOUT:     %ValueType.cpp_operator.bound: <bound method> = bound_method %sum.ref, imports.%ValueType.cpp_operator.decl
// CHECK:STDOUT:     %.loc32_12: ref %ValueType = value_as_ref %i.ref
// CHECK:STDOUT:     %addr.loc32: %ptr.9d3 = addr_of %.loc32_12
// CHECK:STDOUT:     %.loc32_9.1: %ptr.32e = as_compatible %addr.loc32
// CHECK:STDOUT:     %.loc32_9.2: %ptr.32e = converted %addr.loc32, %.loc32_9.1
// CHECK:STDOUT:     %operator_PlusEqual__carbon_thunk.call: ref %ValueType = call imports.%operator_PlusEqual__carbon_thunk.decl(%sum.ref, %.loc32_9.2)
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.done:
// CHECK:STDOUT:     %ValueType.Op.bound.loc31: <bound method> = bound_method %.loc31_31.11, constants.%ValueType.Op.4c94b9.1
// CHECK:STDOUT:     %Op.ref.loc31: %ValueType.cpp_destructor.type = name_ref Op, imports.%ValueType.cpp_destructor.decl [concrete = constants.%ValueType.cpp_destructor]
// CHECK:STDOUT:     %ValueType.cpp_destructor.bound.loc31: <bound method> = bound_method %.loc31_31.11, %Op.ref.loc31
// CHECK:STDOUT:     %ValueType.cpp_destructor.call.loc31: init %empty_tuple.type = call %ValueType.cpp_destructor.bound.loc31(%.loc31_31.11)
// CHECK:STDOUT:     %Destroy.Op.bound: <bound method> = bound_method %.loc31_31.3, constants.%Destroy.Op.1a2547.6
// CHECK:STDOUT:     %Destroy.Op.call: init %empty_tuple.type = call %Destroy.Op.bound(%.loc31_31.3)
// CHECK:STDOUT:     %impl.elem0.loc31_31.1: @Test.%.loc31_31.15 (%.57c) = impl_witness_access constants.%Destroy.lookup_impl_witness.198, element0 [symbolic = %impl.elem0.loc31_31.2 (constants.%impl.elem0.152)]
// CHECK:STDOUT:     %bound_method.loc31_31.7: <bound method> = bound_method %var, %impl.elem0.loc31_31.1
// CHECK:STDOUT:     %specific_impl_fn.loc31_31.3: <specific function> = specific_impl_function %impl.elem0.loc31_31.1, @Destroy.WithSelf.Op(constants.%impl.elem1.834) [symbolic = %specific_impl_fn.loc31_31.6 (constants.%specific_impl_fn.9fb)]
// CHECK:STDOUT:     %bound_method.loc31_31.8: <bound method> = bound_method %var, %specific_impl_fn.loc31_31.3
// CHECK:STDOUT:     %Destroy.WithSelf.Op.call: init %empty_tuple.type = call %bound_method.loc31_31.8(%var)
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc31_31.1(%self.param: ref %MaybeUnformed.669) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc31_31.2(%self.param: ref bool) = "no_op";
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc31_31.3(%self.param: ref %struct_type.value.has_value.5a1) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc31_31.4(%self.param: ref %DefaultOptionalStorage.257) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc31_31.5(%self.param: ref %Optional.c14) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%R.db4) {
// CHECK:STDOUT:   %R.loc27_10.1 => constants.%R.db4
// CHECK:STDOUT:   %R.as_type.loc27_67.1 => constants.%R.as_type.c37
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.17d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.a17) {
// CHECK:STDOUT:   %R.loc27_10.1 => constants.%facet_value.a17
// CHECK:STDOUT:   %R.as_type.loc27_67.1 => constants.%ConstRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.025
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc27 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.887
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.9a5
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.8d8
// CHECK:STDOUT:   %.loc31_31.13 => constants.%.2d3f
// CHECK:STDOUT:   %impl.elem2.loc31_31.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.4e7
// CHECK:STDOUT:   %specific_impl_fn.loc31_31.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.777
// CHECK:STDOUT:   %as_type => constants.%tuple.type.df8
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.e35
// CHECK:STDOUT:   %ptr => constants.%ptr.fc0
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.069
// CHECK:STDOUT:   %.loc31_31.14 => constants.%.e3b
// CHECK:STDOUT:   %impl.elem3.loc31_31.2 => constants.%R.as_type.as.Iterate.impl.Next.4d5
// CHECK:STDOUT:   %specific_impl_fn.loc31_31.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.589
// CHECK:STDOUT:   %.loc31_31.15 => constants.%.4e1
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.7
// CHECK:STDOUT:   %impl.elem0.loc31_31.2 => constants.%Destroy.Op.1a2547.7
// CHECK:STDOUT:   %specific_impl_fn.loc31_31.6 => constants.%Destroy.Op.1a2547.7
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: --- fail_todo_adl_returns_different_types_mutable.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Iterate.type: type = facet_type <@Iterate> [concrete]
// CHECK:STDOUT:   %OptionalStorage.type: type = facet_type <@OptionalStorage> [concrete]
// CHECK:STDOUT:   %Destroy.type: type = facet_type <@Destroy> [concrete]
// CHECK:STDOUT:   %facet_type: type = facet_type <@Destroy & @Copy> [concrete]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [concrete]
// CHECK:STDOUT:   %T.220: %OptionalStorage.type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Optional.Get.type.bb9: type = fn_type @Optional.Get, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.Get.fa1: %Optional.Get.type.bb9 = struct_value () [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.e9e: type = fn_type @Optional.HasValue, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.6cd: %Optional.HasValue.type.e9e = struct_value () [symbolic]
// CHECK:STDOUT:   %T.283: %facet_type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.d50: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.type.671: type = fn_type @T.as_type.as.OptionalStorage.impl.Get, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.a54: %T.as_type.as.OptionalStorage.impl.Get.type.671 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.type.d76: type = fn_type @T.as_type.as.OptionalStorage.impl.Has, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.aa4: %T.as_type.as.OptionalStorage.impl.Has.type.d76 = struct_value () [symbolic]
// CHECK:STDOUT:   %.Self.0.500: %Iterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.1d8: <witness> = lookup_impl_witness %.Self.0.500, @Iterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.294: %facet_type = impl_witness_access %Iterate.lookup_impl_witness.1d8, element0 [symbolic_self]
// CHECK:STDOUT:   %ValueType: type = class_type @ValueType [concrete]
// CHECK:STDOUT:   %pattern_type.e41: type = pattern_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor.type: type = fn_type @ValueType.cpp_destructor [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor: %ValueType.cpp_destructor.type = struct_value () [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.79266b.1: type = fn_type @ValueType.Op.1 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4c94b9.1: %ValueType.Op.type.79266b.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.fef: <witness> = custom_witness (%ValueType.Op.4c94b9.1), @Destroy [concrete]
// CHECK:STDOUT:   %const.773: type = const_type %ValueType [concrete]
// CHECK:STDOUT:   %ptr.32e: type = ptr_type %const.773 [concrete]
// CHECK:STDOUT:   %ptr.9d3: type = ptr_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.79266b.2: type = fn_type @ValueType.Op.2 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4c94b9.2: %ValueType.Op.type.79266b.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.c19: <witness> = custom_witness (%ValueType.Op.4c94b9.2), @Copy [concrete]
// CHECK:STDOUT:   %facet_value.ccb: %facet_type = facet_value %ValueType, (%custom_witness.fef, %custom_witness.c19) [concrete]
// CHECK:STDOUT:   %Iterate_where.type.f9d: type = facet_type <@Iterate where %impl.elem0.294 = %facet_value.ccb> [concrete]
// CHECK:STDOUT:   %R.db4: %Iterate_where.type.f9d = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %R.as_type.c37: type = facet_access_type %R.db4 [symbolic]
// CHECK:STDOUT:   %pattern_type.17d: type = pattern_type %R.as_type.c37 [symbolic]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.173: <witness> = lookup_impl_witness %R.db4, @Iterate [symbolic]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.c37, (%Iterate.lookup_impl_witness.173) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.5cd: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.d51: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic]
// CHECK:STDOUT:   %.592: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.5cd, %Iterate.facet [symbolic]
// CHECK:STDOUT:   %impl.elem2.ae2: %.592 = impl_witness_access %Iterate.lookup_impl_witness.173, element2 [symbolic]
// CHECK:STDOUT:   %impl.elem1.834: %Destroy.type = impl_witness_access %Iterate.lookup_impl_witness.173, element1 [symbolic]
// CHECK:STDOUT:   %as_type.e41: type = facet_access_type %impl.elem1.834 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.06e: <specific function> = specific_impl_function %impl.elem2.ae2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic]
// CHECK:STDOUT:   %ptr.d27: type = ptr_type %as_type.e41 [symbolic]
// CHECK:STDOUT:   %.524: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.d51, %Iterate.facet [symbolic]
// CHECK:STDOUT:   %impl.elem3.7a5: %.524 = impl_witness_access %Iterate.lookup_impl_witness.173, element3 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.257: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%facet_value.ccb) [concrete]
// CHECK:STDOUT:   %OptionalStorage.impl_witness.96c: <witness> = impl_witness imports.%OptionalStorage.impl_witness_table.96b, @T.as_type.as.OptionalStorage.impl(%facet_value.ccb) [concrete]
// CHECK:STDOUT:   %OptionalStorage.facet.f7e: %OptionalStorage.type = facet_value %ValueType, (%OptionalStorage.impl_witness.96c) [concrete]
// CHECK:STDOUT:   %Optional.df6: type = class_type @Optional, @Optional(%OptionalStorage.facet.f7e) [concrete]
// CHECK:STDOUT:   %specific_impl_fn.24b: <specific function> = specific_impl_function %impl.elem3.7a5, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.a63: type = fn_type @Optional.HasValue, @Optional(%OptionalStorage.facet.f7e) [concrete]
// CHECK:STDOUT:   %Optional.HasValue.bee: %Optional.HasValue.type.a63 = struct_value () [concrete]
// CHECK:STDOUT:   %Optional.Get.type.fe3: type = fn_type @Optional.Get, @Optional(%OptionalStorage.facet.f7e) [concrete]
// CHECK:STDOUT:   %Optional.Get.3f8: %Optional.Get.type.fe3 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.facet.306: %Destroy.type = facet_value %ValueType, (%custom_witness.fef) [concrete]
// CHECK:STDOUT:   %MaybeUnformed.669: type = class_type @MaybeUnformed, @MaybeUnformed(%Destroy.facet.306) [concrete]
// CHECK:STDOUT:   %struct_type.value.has_value.5a1: type = struct_type {.value: %MaybeUnformed.669, .has_value: bool} [concrete]
// CHECK:STDOUT:   %Optional.HasValue.specific_fn: <specific function> = specific_function %Optional.HasValue.bee, @Optional.HasValue(%OptionalStorage.facet.f7e) [concrete]
// CHECK:STDOUT:   %Optional.Get.specific_fn: <specific function> = specific_function %Optional.Get.3f8, @Optional.Get(%OptionalStorage.facet.f7e) [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator.type: type = fn_type @ValueType.cpp_operator [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator: %ValueType.cpp_operator.type = struct_value () [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.type: type = fn_type @operator_PlusEqual__carbon_thunk [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk: %operator_PlusEqual__carbon_thunk.type = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.6: type = fn_type @Destroy.Op.loc32_31.5 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.6: %Destroy.Op.type.1d8f74.6 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.198: <witness> = lookup_impl_witness %impl.elem1.834, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.9d6: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1.834) [symbolic]
// CHECK:STDOUT:   %.57c: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.9d6, %impl.elem1.834 [symbolic]
// CHECK:STDOUT:   %impl.elem0.152: %.57c = impl_witness_access %Destroy.lookup_impl_witness.198, element0 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.9fb: <specific function> = specific_impl_function %impl.elem0.152, @Destroy.WithSelf.Op(%impl.elem1.834) [symbolic]
// CHECK:STDOUT:   %MutableRange: type = class_type @MutableRange [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Cpp: <namespace> = namespace file.%Cpp.import_cpp, [concrete] {
// CHECK:STDOUT:     .N = %N
// CHECK:STDOUT:     import Cpp//...
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.bb6: @Optional.%Optional.HasValue.type (%Optional.HasValue.type.e9e) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.HasValue (constants.%Optional.HasValue.6cd)]
// CHECK:STDOUT:   %Core.import_ref.daba: @Optional.%Optional.Get.type (%Optional.Get.type.bb9) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.Get (constants.%Optional.Get.fa1)]
// CHECK:STDOUT:   %Core.import_ref.0c6: type = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%DefaultOptionalStorage (constants.%DefaultOptionalStorage.d50)]
// CHECK:STDOUT:   %Core.import_ref.887 = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %Core.import_ref.6eb = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %Core.import_ref.af2: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has.type (%T.as_type.as.OptionalStorage.impl.Has.type.d76) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has (constants.%T.as_type.as.OptionalStorage.impl.Has.aa4)]
// CHECK:STDOUT:   %Core.import_ref.e31: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get.type (%T.as_type.as.OptionalStorage.impl.Get.type.671) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get (constants.%T.as_type.as.OptionalStorage.impl.Get.a54)]
// CHECK:STDOUT:   %Core.import_ref.cea = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %OptionalStorage.impl_witness_table.96b = impl_witness_table (%Core.import_ref.0c6, %Core.import_ref.887, %Core.import_ref.6eb, %Core.import_ref.af2, %Core.import_ref.e31, %Core.import_ref.cea), @T.as_type.as.OptionalStorage.impl [concrete]
// CHECK:STDOUT:   %N: <namespace> = namespace [concrete] {
// CHECK:STDOUT:     .ValueType = %ValueType.decl
// CHECK:STDOUT:     .MutableRange = %MutableRange.decl
// CHECK:STDOUT:     import Cpp//...
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %ValueType.decl: type = class_decl @ValueType [concrete = constants.%ValueType] {} {}
// CHECK:STDOUT:   %ValueType.cpp_destructor.decl: %ValueType.cpp_destructor.type = fn_decl @ValueType.cpp_destructor [concrete = constants.%ValueType.cpp_destructor] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %ValueType.cpp_operator.decl: %ValueType.cpp_operator.type = fn_decl @ValueType.cpp_operator [concrete = constants.%ValueType.cpp_operator] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.decl: %operator_PlusEqual__carbon_thunk.type = fn_decl @operator_PlusEqual__carbon_thunk [concrete = constants.%operator_PlusEqual__carbon_thunk] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %MutableRange.decl: type = class_decl @MutableRange [concrete = constants.%MutableRange] {} {}
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Test(%R.loc28_10.2: %Iterate_where.type.f9d) {
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %Iterate.lookup_impl_witness: <witness> = lookup_impl_witness %R.loc28_10.1, @Iterate [symbolic = %Iterate.lookup_impl_witness (constants.%Iterate.lookup_impl_witness.173)]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.loc28_67.1, (%Iterate.lookup_impl_witness) [symbolic = %Iterate.facet (constants.%Iterate.facet)]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.NewCursor.type (constants.%Iterate.WithSelf.NewCursor.type.5cd)]
// CHECK:STDOUT:   %.loc32_31.13: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type, %Iterate.facet [symbolic = %.loc32_31.13 (constants.%.592)]
// CHECK:STDOUT:   %impl.elem2.loc32_31.2: @Test.%.loc32_31.13 (%.592) = impl_witness_access %Iterate.lookup_impl_witness, element2 [symbolic = %impl.elem2.loc32_31.2 (constants.%impl.elem2.ae2)]
// CHECK:STDOUT:   %specific_impl_fn.loc32_31.4: <specific function> = specific_impl_function %impl.elem2.loc32_31.2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic = %specific_impl_fn.loc32_31.4 (constants.%specific_impl_fn.06e)]
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %ptr: type = ptr_type %as_type [symbolic = %ptr (constants.%ptr.d27)]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.Next.type (constants.%Iterate.WithSelf.Next.type.d51)]
// CHECK:STDOUT:   %.loc32_31.14: type = fn_type_with_self_type %Iterate.WithSelf.Next.type, %Iterate.facet [symbolic = %.loc32_31.14 (constants.%.524)]
// CHECK:STDOUT:   %impl.elem3.loc32_31.2: @Test.%.loc32_31.14 (%.524) = impl_witness_access %Iterate.lookup_impl_witness, element3 [symbolic = %impl.elem3.loc32_31.2 (constants.%impl.elem3.7a5)]
// CHECK:STDOUT:   %specific_impl_fn.loc32_31.5: <specific function> = specific_impl_function %impl.elem3.loc32_31.2, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic = %specific_impl_fn.loc32_31.5 (constants.%specific_impl_fn.24b)]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1) [symbolic = %Destroy.WithSelf.Op.type (constants.%Destroy.WithSelf.Op.type.9d6)]
// CHECK:STDOUT:   %.loc32_31.15: type = fn_type_with_self_type %Destroy.WithSelf.Op.type, %impl.elem1 [symbolic = %.loc32_31.15 (constants.%.57c)]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness: <witness> = lookup_impl_witness %impl.elem1, @Destroy [symbolic = %Destroy.lookup_impl_witness (constants.%Destroy.lookup_impl_witness.198)]
// CHECK:STDOUT:   %impl.elem0.loc32_31.2: @Test.%.loc32_31.15 (%.57c) = impl_witness_access %Destroy.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc32_31.2 (constants.%impl.elem0.152)]
// CHECK:STDOUT:   %specific_impl_fn.loc32_31.6: <specific function> = specific_impl_function %impl.elem0.loc32_31.2, @Destroy.WithSelf.Op(%impl.elem1) [symbolic = %specific_impl_fn.loc32_31.6 (constants.%specific_impl_fn.9fb)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%r.param: @Test.%R.as_type.loc28_67.1 (%R.as_type.c37)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:     name_binding_decl {
// CHECK:STDOUT:       %i.patt: %pattern_type.e41 = value_binding_pattern i [concrete]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %r.ref: @Test.%R.as_type.loc28_67.1 (%R.as_type.c37) = name_ref r, %r
// CHECK:STDOUT:     %impl.elem2.loc32_31.1: @Test.%.loc32_31.13 (%.592) = impl_witness_access constants.%Iterate.lookup_impl_witness.173, element2 [symbolic = %impl.elem2.loc32_31.2 (constants.%impl.elem2.ae2)]
// CHECK:STDOUT:     %bound_method.loc32_31.1: <bound method> = bound_method %r.ref, %impl.elem2.loc32_31.1
// CHECK:STDOUT:     %specific_impl_fn.loc32_31.1: <specific function> = specific_impl_function %impl.elem2.loc32_31.1, @Iterate.WithSelf.NewCursor(constants.%Iterate.facet) [symbolic = %specific_impl_fn.loc32_31.4 (constants.%specific_impl_fn.06e)]
// CHECK:STDOUT:     %bound_method.loc32_31.2: <bound method> = bound_method %r.ref, %specific_impl_fn.loc32_31.1
// CHECK:STDOUT:     %var: ref @Test.%as_type (%as_type.e41) = var invalid
// CHECK:STDOUT:     %Iterate.WithSelf.NewCursor.call: init @Test.%as_type (%as_type.e41) to %var = call %bound_method.loc32_31.2(%r.ref)
// CHECK:STDOUT:     assign %var, %Iterate.WithSelf.NewCursor.call
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.next:
// CHECK:STDOUT:     %addr.loc32: @Test.%ptr (%ptr.d27) = addr_of %var
// CHECK:STDOUT:     %impl.elem3.loc32_31.1: @Test.%.loc32_31.14 (%.524) = impl_witness_access constants.%Iterate.lookup_impl_witness.173, element3 [symbolic = %impl.elem3.loc32_31.2 (constants.%impl.elem3.7a5)]
// CHECK:STDOUT:     %bound_method.loc32_31.3: <bound method> = bound_method %r.ref, %impl.elem3.loc32_31.1
// CHECK:STDOUT:     %.loc32_31.1: %Destroy.type = converted constants.%as_type.e41, constants.%impl.elem1.834 [symbolic = %impl.elem1 (constants.%impl.elem1.834)]
// CHECK:STDOUT:     %specific_impl_fn.loc32_31.2: <specific function> = specific_impl_function %impl.elem3.loc32_31.1, @Iterate.WithSelf.Next(constants.%Iterate.facet) [symbolic = %specific_impl_fn.loc32_31.5 (constants.%specific_impl_fn.24b)]
// CHECK:STDOUT:     %bound_method.loc32_31.4: <bound method> = bound_method %r.ref, %specific_impl_fn.loc32_31.2
// CHECK:STDOUT:     %.loc32_31.2: ref %Optional.df6 = temporary_storage
// CHECK:STDOUT:     %Iterate.WithSelf.Next.call: init %Optional.df6 to %.loc32_31.2 = call %bound_method.loc32_31.4(%r.ref, %addr.loc32)
// CHECK:STDOUT:     %.loc32_31.3: ref %Optional.df6 = temporary %.loc32_31.2, %Iterate.WithSelf.Next.call
// CHECK:STDOUT:     %.loc32_31.4: %Optional.HasValue.type.a63 = specific_constant imports.%Core.import_ref.bb6, @Optional(constants.%OptionalStorage.facet.f7e) [concrete = constants.%Optional.HasValue.bee]
// CHECK:STDOUT:     %HasValue.ref: %Optional.HasValue.type.a63 = name_ref HasValue, %.loc32_31.4 [concrete = constants.%Optional.HasValue.bee]
// CHECK:STDOUT:     %Optional.HasValue.bound: <bound method> = bound_method %.loc32_31.3, %HasValue.ref
// CHECK:STDOUT:     %Optional.HasValue.specific_fn: <specific function> = specific_function %HasValue.ref, @Optional.HasValue(constants.%OptionalStorage.facet.f7e) [concrete = constants.%Optional.HasValue.specific_fn]
// CHECK:STDOUT:     %bound_method.loc32_31.5: <bound method> = bound_method %.loc32_31.3, %Optional.HasValue.specific_fn
// CHECK:STDOUT:     %.loc32_31.5: %Optional.df6 = acquire_value %.loc32_31.3
// CHECK:STDOUT:     %Optional.HasValue.call: init bool = call %bound_method.loc32_31.5(%.loc32_31.5)
// CHECK:STDOUT:     %.loc32_31.6: bool = value_of_initializer %Optional.HasValue.call
// CHECK:STDOUT:     %.loc32_31.7: bool = converted %Optional.HasValue.call, %.loc32_31.6
// CHECK:STDOUT:     if %.loc32_31.7 br !for.body else br !for.done
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.body:
// CHECK:STDOUT:     %.loc32_31.8: %Optional.Get.type.fe3 = specific_constant imports.%Core.import_ref.daba, @Optional(constants.%OptionalStorage.facet.f7e) [concrete = constants.%Optional.Get.3f8]
// CHECK:STDOUT:     %Get.ref: %Optional.Get.type.fe3 = name_ref Get, %.loc32_31.8 [concrete = constants.%Optional.Get.3f8]
// CHECK:STDOUT:     %Optional.Get.bound: <bound method> = bound_method %.loc32_31.3, %Get.ref
// CHECK:STDOUT:     %Optional.Get.specific_fn: <specific function> = specific_function %Get.ref, @Optional.Get(constants.%OptionalStorage.facet.f7e) [concrete = constants.%Optional.Get.specific_fn]
// CHECK:STDOUT:     %bound_method.loc32_31.6: <bound method> = bound_method %.loc32_31.3, %Optional.Get.specific_fn
// CHECK:STDOUT:     %.loc32_31.9: ref %ValueType = temporary_storage
// CHECK:STDOUT:     %.loc32_31.10: %Optional.df6 = acquire_value %.loc32_31.3
// CHECK:STDOUT:     %Optional.Get.call: init %ValueType to %.loc32_31.9 = call %bound_method.loc32_31.6(%.loc32_31.10)
// CHECK:STDOUT:     %.loc32_16: type = splice_block %ValueType.ref.loc32 [concrete = constants.%ValueType] {
// CHECK:STDOUT:       %Cpp.ref.loc32: <namespace> = name_ref Cpp, imports.%Cpp [concrete = imports.%Cpp]
// CHECK:STDOUT:       %N.ref.loc32: <namespace> = name_ref N, imports.%N [concrete = imports.%N]
// CHECK:STDOUT:       %ValueType.ref.loc32: type = name_ref ValueType, imports.%ValueType.decl [concrete = constants.%ValueType]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %.loc32_31.11: ref %ValueType = temporary %.loc32_31.9, %Optional.Get.call
// CHECK:STDOUT:     %.loc32_31.12: %ValueType = acquire_value %.loc32_31.11
// CHECK:STDOUT:     %i: %ValueType = value_binding i, %.loc32_31.12
// CHECK:STDOUT:     %sum.ref: ref %ValueType = name_ref sum, %sum
// CHECK:STDOUT:     %i.ref: %ValueType = name_ref i, %i
// CHECK:STDOUT:     %ValueType.cpp_operator.bound: <bound method> = bound_method %sum.ref, imports.%ValueType.cpp_operator.decl
// CHECK:STDOUT:     %.loc33_12: ref %ValueType = value_as_ref %i.ref
// CHECK:STDOUT:     %addr.loc33: %ptr.9d3 = addr_of %.loc33_12
// CHECK:STDOUT:     %.loc33_9.1: %ptr.32e = as_compatible %addr.loc33
// CHECK:STDOUT:     %.loc33_9.2: %ptr.32e = converted %addr.loc33, %.loc33_9.1
// CHECK:STDOUT:     %operator_PlusEqual__carbon_thunk.call: ref %ValueType = call imports.%operator_PlusEqual__carbon_thunk.decl(%sum.ref, %.loc33_9.2)
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.done:
// CHECK:STDOUT:     %ValueType.Op.bound.loc32: <bound method> = bound_method %.loc32_31.11, constants.%ValueType.Op.4c94b9.1
// CHECK:STDOUT:     %Op.ref.loc32: %ValueType.cpp_destructor.type = name_ref Op, imports.%ValueType.cpp_destructor.decl [concrete = constants.%ValueType.cpp_destructor]
// CHECK:STDOUT:     %ValueType.cpp_destructor.bound.loc32: <bound method> = bound_method %.loc32_31.11, %Op.ref.loc32
// CHECK:STDOUT:     %ValueType.cpp_destructor.call.loc32: init %empty_tuple.type = call %ValueType.cpp_destructor.bound.loc32(%.loc32_31.11)
// CHECK:STDOUT:     %Destroy.Op.bound: <bound method> = bound_method %.loc32_31.3, constants.%Destroy.Op.1a2547.6
// CHECK:STDOUT:     %Destroy.Op.call: init %empty_tuple.type = call %Destroy.Op.bound(%.loc32_31.3)
// CHECK:STDOUT:     %impl.elem0.loc32_31.1: @Test.%.loc32_31.15 (%.57c) = impl_witness_access constants.%Destroy.lookup_impl_witness.198, element0 [symbolic = %impl.elem0.loc32_31.2 (constants.%impl.elem0.152)]
// CHECK:STDOUT:     %bound_method.loc32_31.7: <bound method> = bound_method %var, %impl.elem0.loc32_31.1
// CHECK:STDOUT:     %specific_impl_fn.loc32_31.3: <specific function> = specific_impl_function %impl.elem0.loc32_31.1, @Destroy.WithSelf.Op(constants.%impl.elem1.834) [symbolic = %specific_impl_fn.loc32_31.6 (constants.%specific_impl_fn.9fb)]
// CHECK:STDOUT:     %bound_method.loc32_31.8: <bound method> = bound_method %var, %specific_impl_fn.loc32_31.3
// CHECK:STDOUT:     %Destroy.WithSelf.Op.call: init %empty_tuple.type = call %bound_method.loc32_31.8(%var)
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc32_31.1(%self.param: ref %MaybeUnformed.669) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc32_31.2(%self.param: ref bool) = "no_op";
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc32_31.3(%self.param: ref %struct_type.value.has_value.5a1) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc32_31.4(%self.param: ref %DefaultOptionalStorage.257) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc32_31.5(%self.param: ref %Optional.df6) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%R.db4) {
// CHECK:STDOUT:   %R.loc28_10.1 => constants.%R.db4
// CHECK:STDOUT:   %R.as_type.loc28_67.1 => constants.%R.as_type.c37
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.17d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: --- fail_todo_adl_overloads.carbon
// CHECK:STDOUT:
// CHECK:STDOUT: constants {
// CHECK:STDOUT:   %Iterate.type: type = facet_type <@Iterate> [concrete]
// CHECK:STDOUT:   %OptionalStorage.type: type = facet_type <@OptionalStorage> [concrete]
// CHECK:STDOUT:   %Destroy.type: type = facet_type <@Destroy> [concrete]
// CHECK:STDOUT:   %facet_type: type = facet_type <@Destroy & @Copy> [concrete]
// CHECK:STDOUT:   %empty_tuple.type: type = tuple_type () [concrete]
// CHECK:STDOUT:   %T.220: %OptionalStorage.type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %Optional.Get.type.bb9: type = fn_type @Optional.Get, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.Get.fa1: %Optional.Get.type.bb9 = struct_value () [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.e9e: type = fn_type @Optional.HasValue, @Optional(%T.220) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.6cd: %Optional.HasValue.type.e9e = struct_value () [symbolic]
// CHECK:STDOUT:   %T.283: %facet_type = symbolic_binding T, 0 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.d50: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.type.671: type = fn_type @T.as_type.as.OptionalStorage.impl.Get, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Get.a54: %T.as_type.as.OptionalStorage.impl.Get.type.671 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.type.d76: type = fn_type @T.as_type.as.OptionalStorage.impl.Has, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Has.aa4: %T.as_type.as.OptionalStorage.impl.Has.type.d76 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.type.973: type = fn_type @T.as_type.as.OptionalStorage.impl.Some, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.Some.c3a: %T.as_type.as.OptionalStorage.impl.Some.type.973 = struct_value () [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.type.f62: type = fn_type @T.as_type.as.OptionalStorage.impl.None, @T.as_type.as.OptionalStorage.impl(%T.283) [symbolic]
// CHECK:STDOUT:   %T.as_type.as.OptionalStorage.impl.None.faf: %T.as_type.as.OptionalStorage.impl.None.type.f62 = struct_value () [symbolic]
// CHECK:STDOUT:   %.Self.0.500: %Iterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.1d8: <witness> = lookup_impl_witness %.Self.0.500, @Iterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.294: %facet_type = impl_witness_access %Iterate.lookup_impl_witness.1d8, element0 [symbolic_self]
// CHECK:STDOUT:   %ValueType: type = class_type @ValueType [concrete]
// CHECK:STDOUT:   %empty_struct_type: type = struct_type {} [concrete]
// CHECK:STDOUT:   %complete_type.357: <witness> = complete_type_witness %empty_struct_type [concrete]
// CHECK:STDOUT:   %pattern_type.e41: type = pattern_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor.type: type = fn_type @ValueType.cpp_destructor [concrete]
// CHECK:STDOUT:   %ValueType.cpp_destructor: %ValueType.cpp_destructor.type = struct_value () [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.79266b.1: type = fn_type @ValueType.Op.1 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4c94b9.1: %ValueType.Op.type.79266b.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.fef: <witness> = custom_witness (%ValueType.Op.4c94b9.1), @Destroy [concrete]
// CHECK:STDOUT:   %const.773: type = const_type %ValueType [concrete]
// CHECK:STDOUT:   %ptr.32e: type = ptr_type %const.773 [concrete]
// CHECK:STDOUT:   %ptr.9d3: type = ptr_type %ValueType [concrete]
// CHECK:STDOUT:   %ValueType.Op.type.79266b.2: type = fn_type @ValueType.Op.2 [concrete]
// CHECK:STDOUT:   %ValueType.Op.4c94b9.2: %ValueType.Op.type.79266b.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.c19: <witness> = custom_witness (%ValueType.Op.4c94b9.2), @Copy [concrete]
// CHECK:STDOUT:   %facet_value.ccb: %facet_type = facet_value %ValueType, (%custom_witness.fef, %custom_witness.c19) [concrete]
// CHECK:STDOUT:   %Iterate_where.type.f9d: type = facet_type <@Iterate where %impl.elem0.294 = %facet_value.ccb> [concrete]
// CHECK:STDOUT:   %R.db4: %Iterate_where.type.f9d = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %R.as_type.c37: type = facet_access_type %R.db4 [symbolic]
// CHECK:STDOUT:   %pattern_type.17d: type = pattern_type %R.as_type.c37 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.type: type = facet_type <@CppRangeForIterate> [concrete]
// CHECK:STDOUT:   %.Self.0.aed: %CppRangeForIterate.type = symbolic_binding .Self.0 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.f6b: <witness> = lookup_impl_witness %.Self.0.aed, @CppRangeForIterate [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.b73: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element0 [symbolic_self]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.595: <witness> = lookup_impl_witness %impl.elem0.b73, @CppUnsafeDeref [symbolic_self]
// CHECK:STDOUT:   %impl.elem0.a2f: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.595, element0 [symbolic_self]
// CHECK:STDOUT:   %impl.elem1.228: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.f6b, element1 [symbolic_self]
// CHECK:STDOUT:   %CppRangeForIterate_where.type: type = facet_type <@CppRangeForIterate where %impl.elem0.b73 impls @Destroy and %impl.elem0.b73 impls @Copy and %impl.elem0.b73 impls @CppUnsafeDeref and %impl.elem0.b73 impls @EqWith, @EqWith(%impl.elem1.228) and %impl.elem0.b73 impls @Inc and %impl.elem0.a2f impls @Destroy and %impl.elem0.a2f impls @Copy and %impl.elem1.228 impls @Destroy and %impl.elem1.228 impls @Copy> [concrete]
// CHECK:STDOUT:   %R.39b: %CppRangeForIterate_where.type = symbolic_binding R, 0 [symbolic]
// CHECK:STDOUT:   %CppRangeForIterate.lookup_impl_witness.7e2712.2: <witness> = lookup_impl_witness %R.39b, @CppRangeForIterate [symbolic]
// CHECK:STDOUT:   %impl.elem1.7a0bff.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element1 [symbolic]
// CHECK:STDOUT:   %impl.elem0.73eb7f.2: type = impl_witness_access %CppRangeForIterate.lookup_impl_witness.7e2712.2, element0 [symbolic]
// CHECK:STDOUT:   %tuple.type.3cf: type = tuple_type (%impl.elem0.73eb7f.2, %impl.elem1.7a0bff.2) [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.69f: <witness> = lookup_impl_witness %tuple.type.3cf, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.facet.593: %Destroy.type = facet_value %tuple.type.3cf, (%Destroy.lookup_impl_witness.69f) [symbolic]
// CHECK:STDOUT:   %CppUnsafeDeref.lookup_impl_witness.aa7: <witness> = lookup_impl_witness %impl.elem0.73eb7f.2, @CppUnsafeDeref [symbolic]
// CHECK:STDOUT:   %impl.elem0.af7: type = impl_witness_access %CppUnsafeDeref.lookup_impl_witness.aa7, element0 [symbolic]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.ec3: <witness> = lookup_impl_witness %impl.elem0.af7, @Destroy [symbolic]
// CHECK:STDOUT:   %Copy.lookup_impl_witness.a7a: <witness> = lookup_impl_witness %impl.elem0.af7, @Copy [symbolic]
// CHECK:STDOUT:   %facet_value.194: %facet_type = facet_value %impl.elem0.af7, (%Destroy.lookup_impl_witness.ec3, %Copy.lookup_impl_witness.a7a) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.d8f: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.c6d: %R.as_type.as.Iterate.impl.Next.type.d8f = struct_value () [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.127: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%R.39b) [symbolic]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.627: %R.as_type.as.Iterate.impl.NewCursor.type.127 = struct_value () [symbolic]
// CHECK:STDOUT:   %Iterate.lookup_impl_witness.173: <witness> = lookup_impl_witness %R.db4, @Iterate [symbolic]
// CHECK:STDOUT:   %Iterate.facet.b38: %Iterate.type = facet_value %R.as_type.c37, (%Iterate.lookup_impl_witness.173) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.5cd: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.d51: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %.592: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.5cd, %Iterate.facet.b38 [symbolic]
// CHECK:STDOUT:   %impl.elem2.ae2: %.592 = impl_witness_access %Iterate.lookup_impl_witness.173, element2 [symbolic]
// CHECK:STDOUT:   %impl.elem1.834: %Destroy.type = impl_witness_access %Iterate.lookup_impl_witness.173, element1 [symbolic]
// CHECK:STDOUT:   %as_type.e41: type = facet_access_type %impl.elem1.834 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.06e: <specific function> = specific_impl_function %impl.elem2.ae2, @Iterate.WithSelf.NewCursor(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %ptr.d27: type = ptr_type %as_type.e41 [symbolic]
// CHECK:STDOUT:   %.524: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.d51, %Iterate.facet.b38 [symbolic]
// CHECK:STDOUT:   %impl.elem3.7a5: %.524 = impl_witness_access %Iterate.lookup_impl_witness.173, element3 [symbolic]
// CHECK:STDOUT:   %DefaultOptionalStorage.257: type = class_type @DefaultOptionalStorage, @DefaultOptionalStorage(%facet_value.ccb) [concrete]
// CHECK:STDOUT:   %OptionalStorage.impl_witness.9db: <witness> = impl_witness imports.%OptionalStorage.impl_witness_table.199, @T.as_type.as.OptionalStorage.impl(%facet_value.ccb) [concrete]
// CHECK:STDOUT:   %OptionalStorage.facet.cac: %OptionalStorage.type = facet_value %ValueType, (%OptionalStorage.impl_witness.9db) [concrete]
// CHECK:STDOUT:   %Optional.c14: type = class_type @Optional, @Optional(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %specific_impl_fn.24b: <specific function> = specific_impl_function %impl.elem3.7a5, @Iterate.WithSelf.Next(%Iterate.facet.b38) [symbolic]
// CHECK:STDOUT:   %Optional.HasValue.type.36e: type = fn_type @Optional.HasValue, @Optional(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %Optional.HasValue.3c0: %Optional.HasValue.type.36e = struct_value () [concrete]
// CHECK:STDOUT:   %Optional.Get.type.862: type = fn_type @Optional.Get, @Optional(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %Optional.Get.28e: %Optional.Get.type.862 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.facet.306: %Destroy.type = facet_value %ValueType, (%custom_witness.fef) [concrete]
// CHECK:STDOUT:   %MaybeUnformed.669: type = class_type @MaybeUnformed, @MaybeUnformed(%Destroy.facet.306) [concrete]
// CHECK:STDOUT:   %struct_type.value.has_value.5a1: type = struct_type {.value: %MaybeUnformed.669, .has_value: bool} [concrete]
// CHECK:STDOUT:   %Optional.HasValue.specific_fn: <specific function> = specific_function %Optional.HasValue.3c0, @Optional.HasValue(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %Optional.Get.specific_fn: <specific function> = specific_function %Optional.Get.28e, @Optional.Get(%OptionalStorage.facet.cac) [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator.type: type = fn_type @ValueType.cpp_operator [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator: %ValueType.cpp_operator.type = struct_value () [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.type: type = fn_type @operator_PlusEqual__carbon_thunk [concrete]
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk: %operator_PlusEqual__carbon_thunk.type = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.6: type = fn_type @Destroy.Op.loc39_31.5 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.6: %Destroy.Op.type.1d8f74.6 = struct_value () [concrete]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness.198: <witness> = lookup_impl_witness %impl.elem1.834, @Destroy [symbolic]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.9d6: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1.834) [symbolic]
// CHECK:STDOUT:   %.57c: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.9d6, %impl.elem1.834 [symbolic]
// CHECK:STDOUT:   %impl.elem0.152: %.57c = impl_witness_access %Destroy.lookup_impl_witness.198, element0 [symbolic]
// CHECK:STDOUT:   %specific_impl_fn.9fb: <specific function> = specific_impl_function %impl.elem0.152, @Destroy.WithSelf.Op(%impl.elem1.834) [symbolic]
// CHECK:STDOUT:   %MutableAndConstRange: type = class_type @MutableAndConstRange [concrete]
// CHECK:STDOUT:   %pattern_type.394: type = pattern_type %MutableAndConstRange [concrete]
// CHECK:STDOUT:   %Iterator: type = class_type @Iterator.1 [concrete]
// CHECK:STDOUT:   %Begin.type: type = fn_type @Begin [concrete]
// CHECK:STDOUT:   %Begin: %Begin.type = struct_value () [concrete]
// CHECK:STDOUT:   %End.type: type = fn_type @End [concrete]
// CHECK:STDOUT:   %End: %End.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.a40: <witness> = custom_witness (%Iterator, %Iterator, %Begin, %End), @CppRangeForIterate [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.fa7609.1: type = fn_type @Iterator.Op.1 [concrete]
// CHECK:STDOUT:   %Iterator.Op.549055.1: %Iterator.Op.type.fa7609.1 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.dd5: <witness> = custom_witness (%ValueType, %Iterator.Op.549055.1), @CppUnsafeDeref [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.fa7609.2: type = fn_type @Iterator.Op.2 [concrete]
// CHECK:STDOUT:   %Iterator.Op.549055.2: %Iterator.Op.type.fa7609.2 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.04a: <witness> = custom_witness (%Iterator.Op.549055.2), @Destroy [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.fa7609.3: type = fn_type @Iterator.Op.3 [concrete]
// CHECK:STDOUT:   %Iterator.Op.549055.3: %Iterator.Op.type.fa7609.3 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.cfc: <witness> = custom_witness (%Iterator.Op.549055.3), @Copy [concrete]
// CHECK:STDOUT:   %Equal.type: type = fn_type @Equal [concrete]
// CHECK:STDOUT:   %Equal: %Equal.type = struct_value () [concrete]
// CHECK:STDOUT:   %NotEqual.type: type = fn_type @NotEqual [concrete]
// CHECK:STDOUT:   %NotEqual: %NotEqual.type = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.c66: <witness> = custom_witness (%Equal, %NotEqual), @EqWith, @EqWith(%Iterator) [concrete]
// CHECK:STDOUT:   %Iterator.Op.type.fa7609.4: type = fn_type @Iterator.Op.4 [concrete]
// CHECK:STDOUT:   %Iterator.Op.549055.4: %Iterator.Op.type.fa7609.4 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.01a: <witness> = custom_witness (%Iterator.Op.549055.4), @Inc [concrete]
// CHECK:STDOUT:   %facet_value.88d: %CppRangeForIterate_where.type = facet_value %MutableAndConstRange, (%custom_witness.fef, %custom_witness.c19, %custom_witness.a40, %custom_witness.04a, %custom_witness.cfc, %custom_witness.dd5, %custom_witness.c66, %custom_witness.01a) [concrete]
// CHECK:STDOUT:   %tuple.type.56e: type = tuple_type (%Iterator, %Iterator) [concrete]
// CHECK:STDOUT:   %Destroy.Op.type.1d8f74.7: type = fn_type @Destroy.Op.2 [concrete]
// CHECK:STDOUT:   %Destroy.Op.1a2547.7: %Destroy.Op.type.1d8f74.7 = struct_value () [concrete]
// CHECK:STDOUT:   %custom_witness.df9cc1.7: <witness> = custom_witness (%Destroy.Op.1a2547.7), @Destroy [concrete]
// CHECK:STDOUT:   %Destroy.facet.7aa: %Destroy.type = facet_value %tuple.type.56e, (%custom_witness.df9cc1.7) [concrete]
// CHECK:STDOUT:   %Iterate.impl_witness.b32: <witness> = impl_witness imports.%Iterate.impl_witness_table.ccd, @R.as_type.as.Iterate.impl(%facet_value.88d) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.type.b61: type = fn_type @R.as_type.as.Iterate.impl.NewCursor, @R.as_type.as.Iterate.impl(%facet_value.88d) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.b31: %R.as_type.as.Iterate.impl.NewCursor.type.b61 = struct_value () [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.type.1dc: type = fn_type @R.as_type.as.Iterate.impl.Next, @R.as_type.as.Iterate.impl(%facet_value.88d) [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.b70: %R.as_type.as.Iterate.impl.Next.type.1dc = struct_value () [concrete]
// CHECK:STDOUT:   %Iterate.facet.2df: %Iterate.type = facet_value %MutableAndConstRange, (%Iterate.impl_witness.b32) [concrete]
// CHECK:STDOUT:   %facet_value.139: %Iterate_where.type.f9d = facet_value %MutableAndConstRange, (%Iterate.impl_witness.b32) [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type.7c9: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet.2df) [concrete]
// CHECK:STDOUT:   %.59c: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type.7c9, %Iterate.facet.2df [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.NewCursor.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.NewCursor.b31, @R.as_type.as.Iterate.impl.NewCursor(%facet_value.88d) [concrete]
// CHECK:STDOUT:   %complete_type.1b5: <witness> = complete_type_witness %tuple.type.56e [concrete]
// CHECK:STDOUT:   %ptr.484: type = ptr_type %tuple.type.56e [concrete]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type.248: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet.2df) [concrete]
// CHECK:STDOUT:   %.641: type = fn_type_with_self_type %Iterate.WithSelf.Next.type.248, %Iterate.facet.2df [concrete]
// CHECK:STDOUT:   %R.as_type.as.Iterate.impl.Next.specific_fn: <specific function> = specific_function %R.as_type.as.Iterate.impl.Next.b70, @R.as_type.as.Iterate.impl.Next(%facet_value.88d) [concrete]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type.b7b: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%Destroy.facet.7aa) [concrete]
// CHECK:STDOUT:   %.1ad: type = fn_type_with_self_type %Destroy.WithSelf.Op.type.b7b, %Destroy.facet.7aa [concrete]
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: imports {
// CHECK:STDOUT:   %Cpp: <namespace> = namespace file.%Cpp.import_cpp, [concrete] {
// CHECK:STDOUT:     .N = %N
// CHECK:STDOUT:     import Cpp//...
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.bb6: @Optional.%Optional.HasValue.type (%Optional.HasValue.type.e9e) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.HasValue (constants.%Optional.HasValue.6cd)]
// CHECK:STDOUT:   %Core.import_ref.daba: @Optional.%Optional.Get.type (%Optional.Get.type.bb9) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @Optional.%Optional.Get (constants.%Optional.Get.fa1)]
// CHECK:STDOUT:   %Core.import_ref.0c6: type = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%DefaultOptionalStorage (constants.%DefaultOptionalStorage.d50)]
// CHECK:STDOUT:   %Core.import_ref.6d6: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None.type (%T.as_type.as.OptionalStorage.impl.None.type.f62) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.None (constants.%T.as_type.as.OptionalStorage.impl.None.faf)]
// CHECK:STDOUT:   %Core.import_ref.6f3: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some.type (%T.as_type.as.OptionalStorage.impl.Some.type.973) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Some (constants.%T.as_type.as.OptionalStorage.impl.Some.c3a)]
// CHECK:STDOUT:   %Core.import_ref.af2: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has.type (%T.as_type.as.OptionalStorage.impl.Has.type.d76) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Has (constants.%T.as_type.as.OptionalStorage.impl.Has.aa4)]
// CHECK:STDOUT:   %Core.import_ref.e31: @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get.type (%T.as_type.as.OptionalStorage.impl.Get.type.671) = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], loaded [symbolic = @T.as_type.as.OptionalStorage.impl.%T.as_type.as.OptionalStorage.impl.Get (constants.%T.as_type.as.OptionalStorage.impl.Get.a54)]
// CHECK:STDOUT:   %Core.import_ref.cea = import_ref Core//prelude/iterate, inst{{[0-9A-F]+}} [indirect], unloaded
// CHECK:STDOUT:   %OptionalStorage.impl_witness_table.199 = impl_witness_table (%Core.import_ref.0c6, %Core.import_ref.6d6, %Core.import_ref.6f3, %Core.import_ref.af2, %Core.import_ref.e31, %Core.import_ref.cea), @T.as_type.as.OptionalStorage.impl [concrete]
// CHECK:STDOUT:   %N: <namespace> = namespace [concrete] {
// CHECK:STDOUT:     .ValueType = %ValueType.decl
// CHECK:STDOUT:     .MutableAndConstRange = %MutableAndConstRange.decl
// CHECK:STDOUT:     import Cpp//...
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %ValueType.decl: type = class_decl @ValueType [concrete = constants.%ValueType] {} {}
// CHECK:STDOUT:   %ValueType.cpp_destructor.decl: %ValueType.cpp_destructor.type = fn_decl @ValueType.cpp_destructor [concrete = constants.%ValueType.cpp_destructor] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %Core.import_ref.301: %facet_type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%facet_value (constants.%facet_value.194)]
// CHECK:STDOUT:   %Core.import_ref.89f: %Destroy.type = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%Destroy.facet (constants.%Destroy.facet.593)]
// CHECK:STDOUT:   %Core.import_ref.940: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor.type (%R.as_type.as.Iterate.impl.NewCursor.type.127) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.NewCursor (constants.%R.as_type.as.Iterate.impl.NewCursor.627)]
// CHECK:STDOUT:   %Core.import_ref.fe7: @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next.type (%R.as_type.as.Iterate.impl.Next.type.d8f) = import_ref Core//prelude/iterate, loc{{\d+_\d+}}, loaded [symbolic = @R.as_type.as.Iterate.impl.%R.as_type.as.Iterate.impl.Next (constants.%R.as_type.as.Iterate.impl.Next.c6d)]
// CHECK:STDOUT:   %Iterate.impl_witness_table.ccd = impl_witness_table (%Core.import_ref.301, %Core.import_ref.89f, %Core.import_ref.940, %Core.import_ref.fe7), @R.as_type.as.Iterate.impl [concrete]
// CHECK:STDOUT:   %ValueType.cpp_operator.decl: %ValueType.cpp_operator.type = fn_decl @ValueType.cpp_operator [concrete = constants.%ValueType.cpp_operator] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %operator_PlusEqual__carbon_thunk.decl: %operator_PlusEqual__carbon_thunk.type = fn_decl @operator_PlusEqual__carbon_thunk [concrete = constants.%operator_PlusEqual__carbon_thunk] {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   } {
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT:   %MutableAndConstRange.decl: type = class_decl @MutableAndConstRange [concrete = constants.%MutableAndConstRange] {} {}
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: generic fn @Test(%R.loc35_10.2: %Iterate_where.type.f9d) {
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %Iterate.lookup_impl_witness: <witness> = lookup_impl_witness %R.loc35_10.1, @Iterate [symbolic = %Iterate.lookup_impl_witness (constants.%Iterate.lookup_impl_witness.173)]
// CHECK:STDOUT:   %Iterate.facet: %Iterate.type = facet_value %R.as_type.loc35_67.1, (%Iterate.lookup_impl_witness) [symbolic = %Iterate.facet (constants.%Iterate.facet.b38)]
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type: type = fn_type @Iterate.WithSelf.NewCursor, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.NewCursor.type (constants.%Iterate.WithSelf.NewCursor.type.5cd)]
// CHECK:STDOUT:   %.loc39_31.13: type = fn_type_with_self_type %Iterate.WithSelf.NewCursor.type, %Iterate.facet [symbolic = %.loc39_31.13 (constants.%.592)]
// CHECK:STDOUT:   %impl.elem2.loc39_31.2: @Test.%.loc39_31.13 (%.592) = impl_witness_access %Iterate.lookup_impl_witness, element2 [symbolic = %impl.elem2.loc39_31.2 (constants.%impl.elem2.ae2)]
// CHECK:STDOUT:   %specific_impl_fn.loc39_31.4: <specific function> = specific_impl_function %impl.elem2.loc39_31.2, @Iterate.WithSelf.NewCursor(%Iterate.facet) [symbolic = %specific_impl_fn.loc39_31.4 (constants.%specific_impl_fn.06e)]
// CHECK:STDOUT:   <elided>
// CHECK:STDOUT:   %ptr: type = ptr_type %as_type [symbolic = %ptr (constants.%ptr.d27)]
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type: type = fn_type @Iterate.WithSelf.Next, @Iterate.WithSelf(%Iterate.facet) [symbolic = %Iterate.WithSelf.Next.type (constants.%Iterate.WithSelf.Next.type.d51)]
// CHECK:STDOUT:   %.loc39_31.14: type = fn_type_with_self_type %Iterate.WithSelf.Next.type, %Iterate.facet [symbolic = %.loc39_31.14 (constants.%.524)]
// CHECK:STDOUT:   %impl.elem3.loc39_31.2: @Test.%.loc39_31.14 (%.524) = impl_witness_access %Iterate.lookup_impl_witness, element3 [symbolic = %impl.elem3.loc39_31.2 (constants.%impl.elem3.7a5)]
// CHECK:STDOUT:   %specific_impl_fn.loc39_31.5: <specific function> = specific_impl_function %impl.elem3.loc39_31.2, @Iterate.WithSelf.Next(%Iterate.facet) [symbolic = %specific_impl_fn.loc39_31.5 (constants.%specific_impl_fn.24b)]
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type: type = fn_type @Destroy.WithSelf.Op, @Destroy.WithSelf(%impl.elem1) [symbolic = %Destroy.WithSelf.Op.type (constants.%Destroy.WithSelf.Op.type.9d6)]
// CHECK:STDOUT:   %.loc39_31.15: type = fn_type_with_self_type %Destroy.WithSelf.Op.type, %impl.elem1 [symbolic = %.loc39_31.15 (constants.%.57c)]
// CHECK:STDOUT:   %Destroy.lookup_impl_witness: <witness> = lookup_impl_witness %impl.elem1, @Destroy [symbolic = %Destroy.lookup_impl_witness (constants.%Destroy.lookup_impl_witness.198)]
// CHECK:STDOUT:   %impl.elem0.loc39_31.2: @Test.%.loc39_31.15 (%.57c) = impl_witness_access %Destroy.lookup_impl_witness, element0 [symbolic = %impl.elem0.loc39_31.2 (constants.%impl.elem0.152)]
// CHECK:STDOUT:   %specific_impl_fn.loc39_31.6: <specific function> = specific_impl_function %impl.elem0.loc39_31.2, @Destroy.WithSelf.Op(%impl.elem1) [symbolic = %specific_impl_fn.loc39_31.6 (constants.%specific_impl_fn.9fb)]
// CHECK:STDOUT:
// CHECK:STDOUT:   fn(%r.param: @Test.%R.as_type.loc35_67.1 (%R.as_type.c37)) {
// CHECK:STDOUT:   !entry:
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:     name_binding_decl {
// CHECK:STDOUT:       %i.patt: %pattern_type.e41 = value_binding_pattern i [concrete]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %r.ref: @Test.%R.as_type.loc35_67.1 (%R.as_type.c37) = name_ref r, %r
// CHECK:STDOUT:     %impl.elem2.loc39_31.1: @Test.%.loc39_31.13 (%.592) = impl_witness_access constants.%Iterate.lookup_impl_witness.173, element2 [symbolic = %impl.elem2.loc39_31.2 (constants.%impl.elem2.ae2)]
// CHECK:STDOUT:     %bound_method.loc39_31.1: <bound method> = bound_method %r.ref, %impl.elem2.loc39_31.1
// CHECK:STDOUT:     %specific_impl_fn.loc39_31.1: <specific function> = specific_impl_function %impl.elem2.loc39_31.1, @Iterate.WithSelf.NewCursor(constants.%Iterate.facet.b38) [symbolic = %specific_impl_fn.loc39_31.4 (constants.%specific_impl_fn.06e)]
// CHECK:STDOUT:     %bound_method.loc39_31.2: <bound method> = bound_method %r.ref, %specific_impl_fn.loc39_31.1
// CHECK:STDOUT:     %var: ref @Test.%as_type (%as_type.e41) = var invalid
// CHECK:STDOUT:     %Iterate.WithSelf.NewCursor.call: init @Test.%as_type (%as_type.e41) to %var = call %bound_method.loc39_31.2(%r.ref)
// CHECK:STDOUT:     assign %var, %Iterate.WithSelf.NewCursor.call
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.next:
// CHECK:STDOUT:     %addr.loc39: @Test.%ptr (%ptr.d27) = addr_of %var
// CHECK:STDOUT:     %impl.elem3.loc39_31.1: @Test.%.loc39_31.14 (%.524) = impl_witness_access constants.%Iterate.lookup_impl_witness.173, element3 [symbolic = %impl.elem3.loc39_31.2 (constants.%impl.elem3.7a5)]
// CHECK:STDOUT:     %bound_method.loc39_31.3: <bound method> = bound_method %r.ref, %impl.elem3.loc39_31.1
// CHECK:STDOUT:     %.loc39_31.1: %Destroy.type = converted constants.%as_type.e41, constants.%impl.elem1.834 [symbolic = %impl.elem1 (constants.%impl.elem1.834)]
// CHECK:STDOUT:     %specific_impl_fn.loc39_31.2: <specific function> = specific_impl_function %impl.elem3.loc39_31.1, @Iterate.WithSelf.Next(constants.%Iterate.facet.b38) [symbolic = %specific_impl_fn.loc39_31.5 (constants.%specific_impl_fn.24b)]
// CHECK:STDOUT:     %bound_method.loc39_31.4: <bound method> = bound_method %r.ref, %specific_impl_fn.loc39_31.2
// CHECK:STDOUT:     %.loc39_31.2: ref %Optional.c14 = temporary_storage
// CHECK:STDOUT:     %Iterate.WithSelf.Next.call: init %Optional.c14 to %.loc39_31.2 = call %bound_method.loc39_31.4(%r.ref, %addr.loc39)
// CHECK:STDOUT:     %.loc39_31.3: ref %Optional.c14 = temporary %.loc39_31.2, %Iterate.WithSelf.Next.call
// CHECK:STDOUT:     %.loc39_31.4: %Optional.HasValue.type.36e = specific_constant imports.%Core.import_ref.bb6, @Optional(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.HasValue.3c0]
// CHECK:STDOUT:     %HasValue.ref: %Optional.HasValue.type.36e = name_ref HasValue, %.loc39_31.4 [concrete = constants.%Optional.HasValue.3c0]
// CHECK:STDOUT:     %Optional.HasValue.bound: <bound method> = bound_method %.loc39_31.3, %HasValue.ref
// CHECK:STDOUT:     %Optional.HasValue.specific_fn: <specific function> = specific_function %HasValue.ref, @Optional.HasValue(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.HasValue.specific_fn]
// CHECK:STDOUT:     %bound_method.loc39_31.5: <bound method> = bound_method %.loc39_31.3, %Optional.HasValue.specific_fn
// CHECK:STDOUT:     %.loc39_31.5: %Optional.c14 = acquire_value %.loc39_31.3
// CHECK:STDOUT:     %Optional.HasValue.call: init bool = call %bound_method.loc39_31.5(%.loc39_31.5)
// CHECK:STDOUT:     %.loc39_31.6: bool = value_of_initializer %Optional.HasValue.call
// CHECK:STDOUT:     %.loc39_31.7: bool = converted %Optional.HasValue.call, %.loc39_31.6
// CHECK:STDOUT:     if %.loc39_31.7 br !for.body else br !for.done
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.body:
// CHECK:STDOUT:     %.loc39_31.8: %Optional.Get.type.862 = specific_constant imports.%Core.import_ref.daba, @Optional(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.Get.28e]
// CHECK:STDOUT:     %Get.ref: %Optional.Get.type.862 = name_ref Get, %.loc39_31.8 [concrete = constants.%Optional.Get.28e]
// CHECK:STDOUT:     %Optional.Get.bound: <bound method> = bound_method %.loc39_31.3, %Get.ref
// CHECK:STDOUT:     %Optional.Get.specific_fn: <specific function> = specific_function %Get.ref, @Optional.Get(constants.%OptionalStorage.facet.cac) [concrete = constants.%Optional.Get.specific_fn]
// CHECK:STDOUT:     %bound_method.loc39_31.6: <bound method> = bound_method %.loc39_31.3, %Optional.Get.specific_fn
// CHECK:STDOUT:     %.loc39_31.9: ref %ValueType = temporary_storage
// CHECK:STDOUT:     %.loc39_31.10: %Optional.c14 = acquire_value %.loc39_31.3
// CHECK:STDOUT:     %Optional.Get.call: init %ValueType to %.loc39_31.9 = call %bound_method.loc39_31.6(%.loc39_31.10)
// CHECK:STDOUT:     %.loc39_16: type = splice_block %ValueType.ref.loc39 [concrete = constants.%ValueType] {
// CHECK:STDOUT:       %Cpp.ref.loc39: <namespace> = name_ref Cpp, imports.%Cpp [concrete = imports.%Cpp]
// CHECK:STDOUT:       %N.ref.loc39: <namespace> = name_ref N, imports.%N [concrete = imports.%N]
// CHECK:STDOUT:       %ValueType.ref.loc39: type = name_ref ValueType, imports.%ValueType.decl [concrete = constants.%ValueType]
// CHECK:STDOUT:     }
// CHECK:STDOUT:     %.loc39_31.11: ref %ValueType = temporary %.loc39_31.9, %Optional.Get.call
// CHECK:STDOUT:     %.loc39_31.12: %ValueType = acquire_value %.loc39_31.11
// CHECK:STDOUT:     %i: %ValueType = value_binding i, %.loc39_31.12
// CHECK:STDOUT:     %sum.ref: ref %ValueType = name_ref sum, %sum
// CHECK:STDOUT:     %i.ref: %ValueType = name_ref i, %i
// CHECK:STDOUT:     %ValueType.cpp_operator.bound: <bound method> = bound_method %sum.ref, imports.%ValueType.cpp_operator.decl
// CHECK:STDOUT:     %.loc40_12: ref %ValueType = value_as_ref %i.ref
// CHECK:STDOUT:     %addr.loc40: %ptr.9d3 = addr_of %.loc40_12
// CHECK:STDOUT:     %.loc40_9.1: %ptr.32e = as_compatible %addr.loc40
// CHECK:STDOUT:     %.loc40_9.2: %ptr.32e = converted %addr.loc40, %.loc40_9.1
// CHECK:STDOUT:     %operator_PlusEqual__carbon_thunk.call: ref %ValueType = call imports.%operator_PlusEqual__carbon_thunk.decl(%sum.ref, %.loc40_9.2)
// CHECK:STDOUT:     br !for.next
// CHECK:STDOUT:
// CHECK:STDOUT:   !for.done:
// CHECK:STDOUT:     %ValueType.Op.bound.loc39: <bound method> = bound_method %.loc39_31.11, constants.%ValueType.Op.4c94b9.1
// CHECK:STDOUT:     %Op.ref.loc39: %ValueType.cpp_destructor.type = name_ref Op, imports.%ValueType.cpp_destructor.decl [concrete = constants.%ValueType.cpp_destructor]
// CHECK:STDOUT:     %ValueType.cpp_destructor.bound.loc39: <bound method> = bound_method %.loc39_31.11, %Op.ref.loc39
// CHECK:STDOUT:     %ValueType.cpp_destructor.call.loc39: init %empty_tuple.type = call %ValueType.cpp_destructor.bound.loc39(%.loc39_31.11)
// CHECK:STDOUT:     %Destroy.Op.bound: <bound method> = bound_method %.loc39_31.3, constants.%Destroy.Op.1a2547.6
// CHECK:STDOUT:     %Destroy.Op.call: init %empty_tuple.type = call %Destroy.Op.bound(%.loc39_31.3)
// CHECK:STDOUT:     %impl.elem0.loc39_31.1: @Test.%.loc39_31.15 (%.57c) = impl_witness_access constants.%Destroy.lookup_impl_witness.198, element0 [symbolic = %impl.elem0.loc39_31.2 (constants.%impl.elem0.152)]
// CHECK:STDOUT:     %bound_method.loc39_31.7: <bound method> = bound_method %var, %impl.elem0.loc39_31.1
// CHECK:STDOUT:     %specific_impl_fn.loc39_31.3: <specific function> = specific_impl_function %impl.elem0.loc39_31.1, @Destroy.WithSelf.Op(constants.%impl.elem1.834) [symbolic = %specific_impl_fn.loc39_31.6 (constants.%specific_impl_fn.9fb)]
// CHECK:STDOUT:     %bound_method.loc39_31.8: <bound method> = bound_method %var, %specific_impl_fn.loc39_31.3
// CHECK:STDOUT:     %Destroy.WithSelf.Op.call: init %empty_tuple.type = call %bound_method.loc39_31.8(%var)
// CHECK:STDOUT:     <elided>
// CHECK:STDOUT:   }
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc39_31.1(%self.param: ref %MaybeUnformed.669) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc39_31.2(%self.param: ref bool) = "no_op";
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc39_31.3(%self.param: ref %struct_type.value.has_value.5a1) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc39_31.4(%self.param: ref %DefaultOptionalStorage.257) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: fn @Destroy.Op.loc39_31.5(%self.param: ref %Optional.c14) {
// CHECK:STDOUT: !entry:
// CHECK:STDOUT:   return
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%R.db4) {
// CHECK:STDOUT:   %R.loc35_10.1 => constants.%R.db4
// CHECK:STDOUT:   %R.as_type.loc35_67.1 => constants.%R.as_type.c37
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.17d
// CHECK:STDOUT: }
// CHECK:STDOUT:
// CHECK:STDOUT: specific @Test(constants.%facet_value.139) {
// CHECK:STDOUT:   %R.loc35_10.1 => constants.%facet_value.139
// CHECK:STDOUT:   %R.as_type.loc35_67.1 => constants.%MutableAndConstRange
// CHECK:STDOUT:   %pattern_type => constants.%pattern_type.394
// CHECK:STDOUT:
// CHECK:STDOUT: !definition:
// CHECK:STDOUT:   %require_complete.loc35 => constants.%complete_type.357
// CHECK:STDOUT:   %Iterate.lookup_impl_witness => constants.%Iterate.impl_witness.b32
// CHECK:STDOUT:   %Iterate.facet => constants.%Iterate.facet.2df
// CHECK:STDOUT:   %Iterate.WithSelf.NewCursor.type => constants.%Iterate.WithSelf.NewCursor.type.7c9
// CHECK:STDOUT:   %.loc39_31.13 => constants.%.59c
// CHECK:STDOUT:   %impl.elem2.loc39_31.2 => constants.%R.as_type.as.Iterate.impl.NewCursor.b31
// CHECK:STDOUT:   %specific_impl_fn.loc39_31.4 => constants.%R.as_type.as.Iterate.impl.NewCursor.specific_fn
// CHECK:STDOUT:   %impl.elem1 => constants.%Destroy.facet.7aa
// CHECK:STDOUT:   %as_type => constants.%tuple.type.56e
// CHECK:STDOUT:   %require_complete.1 => constants.%complete_type.1b5
// CHECK:STDOUT:   %ptr => constants.%ptr.484
// CHECK:STDOUT:   %Iterate.WithSelf.Next.type => constants.%Iterate.WithSelf.Next.type.248
// CHECK:STDOUT:   %.loc39_31.14 => constants.%.641
// CHECK:STDOUT:   %impl.elem3.loc39_31.2 => constants.%R.as_type.as.Iterate.impl.Next.b70
// CHECK:STDOUT:   %specific_impl_fn.loc39_31.5 => constants.%R.as_type.as.Iterate.impl.Next.specific_fn
// CHECK:STDOUT:   %Destroy.WithSelf.Op.type => constants.%Destroy.WithSelf.Op.type.b7b
// CHECK:STDOUT:   %.loc39_31.15 => constants.%.1ad
// CHECK:STDOUT:   %Destroy.lookup_impl_witness => constants.%custom_witness.df9cc1.7
// CHECK:STDOUT:   %impl.elem0.loc39_31.2 => constants.%Destroy.Op.1a2547.7
// CHECK:STDOUT:   %specific_impl_fn.loc39_31.6 => constants.%Destroy.Op.1a2547.7
// CHECK:STDOUT: }
// CHECK:STDOUT:
