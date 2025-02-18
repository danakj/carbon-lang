// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#ifndef CARBON_TESTING_FILE_TEST_TEST_FILE_H_
#define CARBON_TESTING_FILE_TEST_TEST_FILE_H_

#include <gmock/gmock.h>

#include <string>

#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "testing/file_test/file_test_base.h"
#include "testing/file_test/line.h"

namespace Carbon::Testing {

// Encapsulates test context generated by processing and running.
//
// Note this should remain internal to `FileTestBase`, not exposed to individual
// tests.
struct TestFile {
  // Represents a split within the test file.
  struct Split {
    friend void PrintTo(const Split& f, std::ostream* os) {
      // Print content escaped.
      llvm::raw_os_ostream os_wrap(*os);
      os_wrap << "Split(" << f.filename << ", \"" << FormatEscaped(f.content)
              << "\")";
    }

    std::string filename;
    std::string content;
  };

  // The input test file content. Other parts may reference this.
  std::string input_content;

  // Lines which don't contain CHECKs, and thus need to be retained by
  // autoupdate. Their file and line numbers are attached.
  //
  // If there are splits, then the splitting line is in the respective file.
  // For N splits, the 0th file is the parts of the input file which are not
  // in any split, plus one file per split file.
  llvm::SmallVector<FileTestLine> non_check_lines;

  // Whether there are splits.
  bool has_splits = false;

  // Arguments for the test, generated from ARGS.
  llvm::SmallVector<std::string> test_args;

  // Extra arguments for the test, generated from EXTRA-ARGS. Unlike ARGS,
  // setting EXTRA-ARGS does not suppress the default arguments.
  llvm::SmallVector<std::string> extra_args;

  // Files in the test, generated by content and splits.
  llvm::SmallVector<Split> file_splits;

  // The location of the autoupdate marker, for autoupdated files.
  std::optional<int> autoupdate_line_number;

  // Whether there should be an AUTOUPDATE-SPLIT.
  bool autoupdate_split = false;

  // Whether to capture stderr and stdout that would head to console,
  // generated from SET-CAPTURE-CONSOLE-OUTPUT.
  bool capture_console_output = false;

  // Whether checks are a subset, generated from SET-CHECK-SUBSET.
  bool check_subset = false;

  // stdout and stderr based on CHECK lines in the file.
  llvm::SmallVector<testing::Matcher<std::string>> expected_stdout;
  llvm::SmallVector<testing::Matcher<std::string>> expected_stderr;

  // stdout and stderr from Run. 16 is arbitrary but a required value.
  llvm::SmallString<16> actual_stdout;
  llvm::SmallString<16> actual_stderr;

  FileTestBase::RunResult run_result = {.success = false};
};

// Processes the test input, producing test files and expected output.
auto ProcessTestFile(llvm::StringRef test_name, bool running_autoupdate)
    -> ErrorOr<TestFile>;

}  // namespace Carbon::Testing

#endif  // CARBON_TESTING_FILE_TEST_TEST_FILE_H_
