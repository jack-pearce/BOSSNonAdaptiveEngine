#define CATCH_CONFIG_RUNNER
#include "../Source/BOSS.hpp"
#include "../Source/BootstrapEngine.hpp"
#include "../Source/ExpressionUtilities.hpp"
#include <catch2/catch.hpp>
#include <numeric>
#include <variant>

using boss::Expression;
using std::string;
using std::literals::string_literals::operator""s;
using boss::utilities::operator""_;
using Catch::Generators::random;
using Catch::Generators::table;
using Catch::Generators::take;
using Catch::Generators::values;
using std::vector;
using namespace Catch::Matchers;
using boss::expressions::CloneReason;
using boss::expressions::generic::get;
using boss::expressions::generic::get_if;
using boss::expressions::generic::holds_alternative;
namespace boss {
using boss::expressions::atoms::Span;
};
using std::int32_t;
using std::int64_t;

static std::vector<string>
    librariesToTest{}; // NOLINT(cppcoreguidelines-avoid-non-const-global-variables)

using intType = int64_t;

auto createIntSpanOf = [](auto... values) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<intType> v = {values...};
  auto s = boss::Span<intType>(std::move(v));
  SpanArguments args;
  args.emplace_back(std::move(s));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

auto createIndexesSpan = [](auto... values) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<int64_t> v = {values...};
  auto s = boss::Span<int64_t>(std::move(v));
  SpanArguments args;
  args.emplace_back(std::move(s));
  return boss::expressions::ComplexExpression("Indexes"_, {}, {}, std::move(args));
};

auto createTwoSpansIntStartingFrom = [](intType n) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<intType> v1 = {0 + n, 1 + n};
  std::vector<intType> v2 = {2 + n, 3 + n};
  auto s1 = boss::Span<intType>(std::move(v1));
  auto s2 = boss::Span<intType>(std::move(v2));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

auto createTwoSpansInt = [](intType n1, intType n2) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<intType> v1 = {n1, n1 + 1, n1 + 2};
  std::vector<intType> v2 = {n2, n2 + 1, n2 + 2};
  auto s1 = boss::Span<intType>(std::move(v1));
  auto s2 = boss::Span<intType>(std::move(v2));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

TEST_CASE("Join") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(!librariesToTest.empty());
  auto eval = [&engine](boss::Expression&& expression) mutable {
    return engine.evaluate("EvaluateInEngines"_("List"_(GENERATE(from_range(librariesToTest))),
                                                std::move(expression)));
  };

  SECTION("Simple join 1") {
    auto result = eval("Join"_("RadixPartition"_("Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                                          "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                            "Partition"_("L_key"_(createIntSpanOf(2, 1, 3)),
                                            createIndexesSpan(0, 1, 2))),
                               "RadixPartition"_("Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                                          "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                            "Partition"_("O_key"_(createIntSpanOf(1, 2)),
                                            createIndexesSpan(2, 3))),
                               "Where"_("Equal"_("L_key"_, "O_key"_))));

    CHECK(result == "TableIndexed"_("Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                             "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                    createIndexesSpan(1,0),
                                    "Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                             "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                    createIndexesSpan(2,3)));
  }

  SECTION("Simple join 1 + project") {
    auto result = eval("Project"_("Join"_("RadixPartition"_("Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                                          "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                            "Partition"_("L_key"_(createIntSpanOf(2, 1, 3)),
                                            createIndexesSpan(0, 1, 2))),
                               "RadixPartition"_("Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                                          "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                            "Partition"_("O_key"_(createIntSpanOf(1, 2)),
                                            createIndexesSpan(2, 3))),
                               "Where"_("Equal"_("L_key"_, "O_key"_))),
                        "As"_("L_value"_, "L_value"_, "O_value"_, "O_value"_)));

    CHECK(result == "Table"_("L_value"_(createIntSpanOf(2, 1)),
                             "O_value"_(createIntSpanOf(3, 4))));
  }

  SECTION("Simple join 2") {
    auto result = eval("Join"_("RadixPartition"_("Table"_("L_key"_(createTwoSpansIntStartingFrom(0)),
                                                          "L_value"_(createTwoSpansIntStartingFrom(10))),
                                            "Partition"_("L_key"_(createIntSpanOf(0, 1, 2, 3)),
                                            createIndexesSpan(0, 1, 4294967296, 4294967297))),
                               "RadixPartition"_("Table"_("O_key"_(createTwoSpansIntStartingFrom(2)),
                                                          "O_value"_(createTwoSpansIntStartingFrom(22))),
                                            "Partition"_("O_key"_(createIntSpanOf(2, 3, 4, 5)),
                                            createIndexesSpan(0, 1, 4294967296, 4294967297))),
                               "Where"_("Equal"_("L_key"_, "O_key"_))));

    CHECK(result == "TableIndexed"_("Table"_("L_key"_(createIntSpanOf(0, 1, 2, 3)),
                                             "L_value"_(createIntSpanOf(10, 11, 12, 13))),
                                    createIndexesSpan(4294967296, 4294967297),
                                    "Table"_("O_key"_(createIntSpanOf(2, 3, 4, 5)),
                                             "O_value"_(createIntSpanOf(22, 23, 24, 25))),
                                    createIndexesSpan(0, 1)));
  }

  SECTION("Simple join 2 + project") {
    auto result = eval("Project"_("Join"_("RadixPartition"_("Table"_("L_key"_(createTwoSpansIntStartingFrom(0)),
                                                          "L_value"_(createTwoSpansIntStartingFrom(10))),
                                            "Partition"_("L_key"_(createIntSpanOf(0, 1, 2, 3)),
                                            createIndexesSpan(0, 1, 4294967296, 4294967297))),
                               "RadixPartition"_("Table"_("O_key"_(createTwoSpansIntStartingFrom(2)),
                                                          "O_value"_(createTwoSpansIntStartingFrom(22))),
                                            "Partition"_("O_key"_(createIntSpanOf(2, 3, 4, 5)),
                                            createIndexesSpan(0, 1, 4294967296, 4294967297))),
                               "Where"_("Equal"_("L_key"_, "O_key"_))),
                        "As"_("L_value"_, "L_value"_, "O_value"_, "O_value"_)));

    CHECK(result == "Table"_("L_value"_(createIntSpanOf(12, 13)),
                             "O_value"_(createIntSpanOf(22, 23))));
  }

  SECTION("Simple join 3 - table as input") {
    auto result = eval("Join"_("Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                        "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                               "Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                        "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                               "Where"_("Equal"_("L_key"_, "O_key"_))));

    CHECK(result == "TableIndexed"_("Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                             "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                    createIndexesSpan(1,0),
                                    "Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                             "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                    createIndexesSpan(2,3)));
  }

  SECTION("Simple join 4 - table as input") {
    auto result = eval("Join"_("Table"_("L_key"_(createTwoSpansIntStartingFrom(0)),
                                        "L_value"_(createTwoSpansIntStartingFrom(10))),
                               "Table"_("O_key"_(createTwoSpansIntStartingFrom(2)),
                                        "O_value"_(createTwoSpansIntStartingFrom(22))),
                               "Where"_("Equal"_("L_key"_, "O_key"_))));

    CHECK(result == "TableIndexed"_("Table"_("L_key"_(createIntSpanOf(0, 1, 2, 3)),
                                             "L_value"_(createIntSpanOf(10, 11, 12, 13))),
                                    createIndexesSpan(4294967296, 4294967297),
                                    "Table"_("O_key"_(createIntSpanOf(2, 3, 4, 5)),
                                             "O_value"_(createIntSpanOf(22, 23, 24, 25))),
                                    createIndexesSpan(0, 1)));
  }

  SECTION("Simple join 5 - project including complex expression") {
    auto result = eval("Project"_("TableIndexed"_(
                                    "Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                             "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                    createIndexesSpan(1,0),
                                    "Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                             "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                    createIndexesSpan(2,3)),
                                    "As"_("newCol"_, "Times"_("L_value"_, "O_value"_))));

    CHECK(result == "Table"_("newCol"_(createIntSpanOf(6, 4))));
  }

  SECTION("Simple join 6 - project including complex expression") {
    auto result = eval("Project"_("TableIndexed"_(
                                    "Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                             "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                    createIndexesSpan(1,0),
                                    "Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                             "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                    createIndexesSpan(2,3)),
                                    "As"_("newCol"_, "Times"_("L_value"_, "L_value"_))));

    CHECK(result == "Table"_("newCol"_(createIntSpanOf(4, 1))));
  }

  SECTION("Simple join 7 - project including complex expression") {
    auto result = eval("Project"_("TableIndexed"_(
                                    "Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                             "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                    createIndexesSpan(1,0),
                                    "Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                             "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                    createIndexesSpan(2,3)),
                                    "As"_("newCol"_, "Times"_("L_value"_, 2))));

    CHECK(result == "Table"_("newCol"_(createIntSpanOf(4, 2))));
  }

  SECTION("Simple join 8 - project including complex expression") {
    auto result = eval("Project"_("TableIndexed"_(
                                    "Table"_("L_key"_(createIntSpanOf(2, 1, 3, 99, 98)),
                                             "L_value"_(createIntSpanOf(1, 2, 3, 4, 5))),
                                    createIndexesSpan(1,0),
                                    "Table"_("O_key"_(createIntSpanOf(50, 51, 1, 2)),
                                             "O_value"_(createIntSpanOf(1, 2, 3, 4))),
                                    createIndexesSpan(2,3)),
                                    "As"_("newCol"_, "Times"_("L_value"_, "Minus"_(0, "O_value"_)))));

    CHECK(result == "Table"_("newCol"_(createIntSpanOf(-6, -4))));
  }

  SECTION("Simple join 9 with two keys + project") {
    auto result = eval("Project"_("Join"_("Table"_("L_key"_(createTwoSpansIntStartingFrom(0)),
                                                   "L_value"_(createTwoSpansIntStartingFrom(10))),
                                          "Table"_("O_key"_(createTwoSpansIntStartingFrom(0)),
                                                  "O_value"_(createTwoSpansIntStartingFrom(10))),
                                          "Where"_("Equal"_("List"_("L_key"_, "L_value"_), 
                                                           "List"_("O_key"_, "O_value"_)))),
                                  "As"_("L_key"_,"L_key"_,"O_key"_,"O_key"_,
                                        "L_value"_, "L_value"_, "O_value"_, "O_value"_)));

    CHECK(result == "Table"_("L_key"_(createIntSpanOf(0,1,2,3)),
                             "O_key"_(createIntSpanOf(0,1,2,3)),
                             "L_value"_(createIntSpanOf(10,11,12,13)),
                             "O_value"_(createIntSpanOf(10,11,12,13))));
  }
}

TEST_CASE("Join - multi-key join") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(!librariesToTest.empty());
  auto eval = [&engine](boss::Expression&& expression) mutable {
    return engine.evaluate("EvaluateInEngines"_("List"_(GENERATE(from_range(librariesToTest))),
                                                std::move(expression)));
  };

  SECTION("Join (non-partitioned) with 3 or more keys is not evaluated") {
    auto intTable1 = "Table"_("L_key1"_(createTwoSpansInt(1, 100)),
                              "L_key2"_(createTwoSpansInt(100, 1)),
                              "L_key3"_(createTwoSpansInt(100, 1)),
                              "L_value"_(createTwoSpansInt(1, 4))); // NOLINT
    auto intTable2 = "Table"_("O_key1"_(createTwoSpansInt(10000, 1)),
                              "O_key2"_(createTwoSpansInt(1, 10000)),
                              "O_key3"_(createTwoSpansInt(1, 10000)),
                              "O_value"_(createTwoSpansInt(1, 4))); // NOLINT
    auto result = eval("Join"_(std::move(intTable1), std::move(intTable2),
                               "Where"_("Equal"_("List"_("L_key1"_, "L_key2"_, "L_key3"_),
                                                 "List"_("O_key1"_, "O_key2"_, "O_key3"_)))));

    CHECK(result == "Join"_("Table"_("L_key1"_("List"_(1,2,3,100,101,102)),
                                     "L_key2"_("List"_(100,101,102, 1,2,3)),
                                     "L_key3"_("List"_(100,101,102, 1,2,3)),
                                     "L_value"_("List"_(1,2,3,4,5,6))),
                            "Table"_("O_key1"_("List"_(10000,10001,10002,1,2,3)),
                                     "O_key2"_("List"_(1,2,3,10000,10001,10002)),
                                     "O_key3"_("List"_(1,2,3,10000,10001,10002)),
                                     "O_value"_("List"_(1,2,3,4,5,6))),
                            "Where"_("Equal"_("List"_("L_key1"_, "L_key2"_, "L_key3"_),
                                              "List"_("O_key1"_, "O_key2"_, "O_key3"_)))));
  }
}

int main(int argc, char* argv[]) {
  Catch::Session session;
  session.configData().showSuccessfulTests = true;
  session.cli(session.cli() | Catch::clara::Opt(librariesToTest, "library")["--library"]);
  auto const returnCode = session.applyCommandLine(argc, argv);
  if(returnCode != 0) {
    return returnCode;
  }
  return session.run();
}
// NOLINTEND(readability-function-cognitive-complexity)
// NOLINTEND(bugprone-exception-escape)
// NOLINTEND(readability-magic-numbers)