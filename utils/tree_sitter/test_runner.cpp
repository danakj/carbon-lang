// Part of the Carbon Language project, under the Apache License v2.0 with LLVM
// Exceptions. See /LICENSE for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <tree_sitter/api.h>

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "testing/base/file_helpers.h"
#include "utils/tree_sitter/src/tree_sitter/parser.h"

extern "C" {
auto tree_sitter_carbon() -> TSLanguage*;
}

// TODO: use file_test.cpp
auto main(int argc, char** argv) -> int {
  if (argc < 2) {
    std::cerr << "Usage: test_runner <file>...\n";
    return 2;
  }

  auto* parser = ts_parser_new();
  ts_parser_set_language(parser, tree_sitter_carbon());

  bool fail_tests = std::getenv("FAIL_TESTS") != nullptr;

  std::vector<std::string> incorrect;
  for (int i = 1; i < argc; i++) {
    std::string file_path = argv[i];
    std::string source = std::move(*Carbon::Testing::ReadFile(file_path));

    auto* tree =
        ts_parser_parse_string(parser, nullptr, source.data(), source.size());

    auto root = ts_tree_root_node(tree);
    auto has_error = ts_node_has_error(root);
    char* node_debug = ts_node_string(root);

    std::cout << file_path << ":\n" << node_debug << "\n";
    if (has_error ^ fail_tests) {
      incorrect.push_back(file_path);
    }

    free(node_debug);
    ts_tree_delete(tree);
  }
  ts_parser_delete(parser);
  for (const auto& file : incorrect) {
    if (fail_tests) {
      std::cout << "INCORRECTLY PASSING " << file << "\n";
    } else {
      std::cout << "FAILED " << file << "\n";
    }
  }
  if (!incorrect.empty()) {
    if (fail_tests) {
      std::cout << incorrect.size() << " tests incorrectly passing.\n";
    } else {
      std::cout << incorrect.size() << " tests failing.\n";
    }
    return 1;
  }
}
