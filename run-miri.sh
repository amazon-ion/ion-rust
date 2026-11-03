#!/usr/bin/env bash
#
# Runs `cargo miri test` with the given pass-through arguments, reports each
# test's execution time, lists the slowest tests, and fails if the run executed
# zero tests.
#
# The `representations` Miri job (see .github/workflows/miri.yml) selects
# tests by MODULE PATH rather than by name. That fails closed for a *new* test
# in a selected module — it runs with no per-name registration — but a module
# *rename* would make the selection match nothing, and libtest exits 0 on an
# empty filter. This guard turns that silent pass into a failure.
#
# The guard checks only the total across all filters, so the workflow passes one
# module path per invocation.
#
# MIRIFLAGS is read from the environment; the caller sets it. Arguments before
# `--` are forwarded to `cargo miri test`; arguments after it are forwarded to
# libtest, after the flags this script adds. For example:
#   MIRIFLAGS="..." ./run-miri.sh --target i686-unknown-linux-gnu -- types::overflowing_int::
#
# When GITHUB_STEP_SUMMARY is set, the slowest tests are also written there.
set -euo pipefail

# Number of slowest tests to list.
slowest=10

cargo_args=()
test_args=()
while [ $# -gt 0 ]; do
  if [ "$1" = "--" ]; then
    shift
    test_args=("$@")
    break
  fi
  cargo_args+=("$1")
  shift
done

log="$(mktemp)"
trap 'rm -f "$log"' EXIT

# libtest's JSON output is captured for the post-run analysis and rendered as one
# line per test for the CI log. Lines that are not JSON (e.g. a test writing to
# stdout directly, bypassing capture) pass through unchanged. Miri's diagnostics
# go to stderr and are not piped.
#
# The status is recorded rather than failing immediately so that the slowest
# tests are reported for failed runs too.
status=0
cargo miri test "${cargo_args[@]}" -- -Zunstable-options --format json --report-time "${test_args[@]}" \
  | tee "$log" \
  | jq --unbuffered -rR '. as $line | try (fromjson |
      if .type == "suite" and .event == "started" then
        "\nrunning \(.test_count) tests"
      elif .type == "test" and .event != "started" then
        "test \(.name) ... \(.event)" + (if .exec_time then " <\(.exec_time)s>" else "" end)
          + (if .stdout then "\n\(.stdout)" else "" end)
      elif .type == "suite" then
        "\ntest result: \(.event). \(.passed) passed; \(.failed) failed; \(.ignored) ignored; \(.filtered_out) filtered out; finished in \(.exec_time)s"
      else empty end
    ) catch $line' \
  || status=$?

slowest_table="$(jq -nrR --argjson n "$slowest" '
  [inputs | fromjson? | select(.type == "test" and .exec_time != null)]
  | sort_by(-.exec_time) | .[:$n][]
  | "| \(.exec_time * 1000 | round / 1000)s | `\(.name)` |"' "$log")"
if [ -n "$slowest_table" ]; then
  report="$(printf '### Slowest Miri tests\n\n| Time | Test |\n| ---: | --- |\n%s\n' "$slowest_table")"
  printf '\n%s\n' "$report"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    printf '%s\n\n' "$report" >> "$GITHUB_STEP_SUMMARY"
  fi
fi

if [ "$status" -ne 0 ]; then
  exit "$status"
fi

# libtest reports a test count once per test binary. Sum across binaries and
# require a non-zero total: a renamed module makes every binary report 0.
total="$(jq -nR '[inputs | fromjson? | select(.type == "suite" and .event == "started") | .test_count] | add // 0' "$log")"
if [ "$total" -eq 0 ]; then
  echo "::error::Miri executed 0 tests — the module-path selection matched nothing. Was a selected module renamed? See the representations matrix in .github/workflows/miri.yml." >&2
  exit 1
fi
echo "Miri executed ${total} test(s)."
