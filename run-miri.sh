#!/usr/bin/env bash
#
# Runs `cargo miri test` with the given pass-through arguments, split across
# MIRI_PROCS concurrent Miri processes (default 1). Miri interprets on a single
# host thread, so concurrent processes are the only way to use more cores.
# Reports failures, totals, and the slowest tests, and fails if the selection
# matches zero tests.
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
# `--` are forwarded to `cargo miri test`; arguments after it are libtest
# filters and options that select the tests to run. For example:
#   MIRIFLAGS="..." ./run-miri.sh --target i686-unknown-linux-gnu -- types::overflowing_int::
#
# When GITHUB_STEP_SUMMARY is set, the slowest tests are also written there.
set -euo pipefail

procs="${MIRI_PROCS:-1}"
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

dir="$(mktemp -d)"
trap 'rm -rf "$dir"' EXIT

# Listing also compiles the test binary, so the processes below share one build.
mapfile -t tests < <(cargo miri test "${cargo_args[@]}" -- --list --format terse "${test_args[@]}" | sed -n 's/: test$//p')
if [ "${#tests[@]}" -eq 0 ]; then
  echo "::error::Miri selected 0 tests — the module-path selection matched nothing. Was a selected module renamed? See the representations matrix in .github/workflows/miri.yml." >&2
  exit 1
fi
# An empty shard would pass no names, and an unfiltered libtest runs every test.
if [ "$procs" -gt "${#tests[@]}" ]; then
  procs="${#tests[@]}"
fi
echo "Running ${#tests[@]} test(s) across ${procs} Miri process(es)."

# Tests are dealt round-robin so that slow tests, which cluster by module, are
# spread across processes. Each process writes libtest's JSON to its own file;
# Miri's diagnostics go to stderr, which is not redirected.
pids=()
for ((k = 0; k < procs; k++)); do
  shard=()
  for ((i = k; i < ${#tests[@]}; i += procs)); do
    shard+=("${tests[i]}")
  done
  cargo miri test "${cargo_args[@]}" -- -Zunstable-options --format json --report-time --exact "${shard[@]}" \
    > "$dir/$k.json" &
  pids+=($!)
done
status=0
for pid in "${pids[@]}"; do
  wait "$pid" || status=1
done

# Lines that are not JSON (e.g. a test writing to stdout directly, bypassing
# capture) are skipped.
jq -nrR '[inputs | fromjson?] as $events
  | ($events[] | select(.type == "test" and .event == "failed")
      | "\n---- \(.name) ----\n\(.stdout // "")"),
    ([$events[] | select(.type == "suite" and .event != "started")]
      | "\ntest result: \(map(.passed) | add) passed; \(map(.failed) | add) failed; \(map(.ignored) | add) ignored")' \
  "$dir"/*.json

slowest_table="$(jq -nrR --argjson n "$slowest" '
  [inputs | fromjson? | select(.type == "test" and .exec_time != null)]
  | sort_by(-.exec_time) | .[:$n][]
  | "| \(.exec_time * 1000 | round / 1000)s | `\(.name)` |"' "$dir"/*.json)"
if [ -n "$slowest_table" ]; then
  report="$(printf '### Slowest Miri tests\n\n| Time | Test |\n| ---: | --- |\n%s\n' "$slowest_table")"
  printf '\n%s\n' "$report"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    printf '%s\n\n' "$report" >> "$GITHUB_STEP_SUMMARY"
  fi
fi

exit "$status"
