// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include "toolchain/diagnostics/diagnostic_emitter.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "llvm/ADT/StringRef.h"
#include "toolchain/diagnostics/mocks.h"

namespace Carbon::Testing {
namespace {

using ::Carbon::Testing::IsDiagnostic;
using ::Carbon::Testing::IsSingleDiagnostic;
using testing::ElementsAre;

class FakeDiagnosticEmitter : public DiagnosticEmitter<int> {
 public:
  using DiagnosticEmitter::DiagnosticEmitter;

 protected:
  auto ConvertLoc(int n, ContextFnT /*context_fn*/) const
      -> ConvertedDiagnosticLoc override {
    return {.loc = {.line_number = 1, .column_number = n},
            .last_byte_offset = -1};
  }
};

class DiagnosticEmitterTest : public ::testing::Test {
 public:
  DiagnosticEmitterTest() : emitter_(&consumer_) {}

  Testing::MockDiagnosticConsumer consumer_;
  FakeDiagnosticEmitter emitter_;
};

TEST_F(DiagnosticEmitterTest, EmitSimpleError) {
  CARBON_DIAGNOSTIC(TestDiagnostic, Error, "simple error");
  EXPECT_CALL(consumer_, HandleDiagnostic(IsSingleDiagnostic(
                             DiagnosticKind::TestDiagnostic,
                             DiagnosticLevel::Error, 1, 1, "simple error")));
  EXPECT_CALL(consumer_, HandleDiagnostic(IsSingleDiagnostic(
                             DiagnosticKind::TestDiagnostic,
                             DiagnosticLevel::Error, 1, 2, "simple error")));
  emitter_.Emit(1, TestDiagnostic);
  emitter_.Emit(2, TestDiagnostic);
}

TEST_F(DiagnosticEmitterTest, EmitSimpleWarning) {
  CARBON_DIAGNOSTIC(TestDiagnostic, Warning, "simple warning");
  EXPECT_CALL(consumer_,
              HandleDiagnostic(IsSingleDiagnostic(
                  DiagnosticKind::TestDiagnostic, DiagnosticLevel::Warning, 1,
                  1, "simple warning")));
  emitter_.Emit(1, TestDiagnostic);
}

TEST_F(DiagnosticEmitterTest, EmitOneArgDiagnostic) {
  CARBON_DIAGNOSTIC(TestDiagnostic, Error, "arg: `{0}`", std::string);
  EXPECT_CALL(consumer_, HandleDiagnostic(IsSingleDiagnostic(
                             DiagnosticKind::TestDiagnostic,
                             DiagnosticLevel::Error, 1, 1, "arg: `str`")));
  emitter_.Emit(1, TestDiagnostic, "str");
}

TEST_F(DiagnosticEmitterTest, EmitNote) {
  CARBON_DIAGNOSTIC(TestDiagnostic, Warning, "simple warning");
  CARBON_DIAGNOSTIC(TestDiagnosticNote, Note, "note");
  EXPECT_CALL(
      consumer_,
      HandleDiagnostic(IsDiagnostic(
          DiagnosticLevel::Warning,
          ElementsAre(
              IsDiagnosticMessage(DiagnosticKind::TestDiagnostic,
                                  DiagnosticLevel::Warning, 1, 1,
                                  "simple warning"),
              IsDiagnosticMessage(DiagnosticKind::TestDiagnosticNote,
                                  DiagnosticLevel::Note, 1, 2, "note")))));
  emitter_.Build(1, TestDiagnostic).Note(2, TestDiagnosticNote).Emit();
}

}  // namespace
}  // namespace Carbon::Testing
