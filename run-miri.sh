#!/usr/bin/env bash
#
# Runs `cargo miri test` with the given pass-through arguments and fails if the
# run executed zero tests.
#
# The unsafe-representation Miri job (see .github/workflows/miri.yml) selects
# tests by MODULE PATH rather than by name. That fails closed for a *new* test
# in a selected module — it runs with no per-name registration — but a module
# *rename* would make the selection match nothing, and libtest exits 0 on an
# empty filter. This guard turns that silent pass into a failure.
#
# LIMITATION: the guard requires only that the run executed at least one test in
# total. With a single module in the selection (today's case) that fully catches
# a rename. If the selection ever lists multiple modules, renaming just one of
# them leaves the others' counts non-zero and the total positive, so this guard
# would NOT catch that. Per-module protection would need per-filter counts.
#
# MIRIFLAGS is read from the environment; the caller sets it. Everything passed
# to this script is forwarded verbatim to `cargo miri test`, e.g.
#   MIRIFLAGS="..." ./run-miri.sh --target i686-unknown-linux-gnu -- overflowing_int
set -euo pipefail

log="$(mktemp)"
trap 'rm -f "$log"' EXIT

# Stream to the CI log while capturing the output for the count check. pipefail
# ensures a `cargo miri test` failure fails the pipeline (and, under `set -e`,
# the script) before the count is examined.
cargo miri test "$@" 2>&1 | tee "$log"

# libtest prints "running N tests" once per test binary. Sum across binaries and
# require a non-zero total: a renamed module makes every binary report 0. The
# `|| true` keeps a no-match `grep` (which exits non-zero under `pipefail`) from
# aborting the script before the diagnostic below; `awk` then yields 0.
total="$(grep -oE 'running [0-9]+ test' "$log" | grep -oE '[0-9]+' | awk '{ s += $1 } END { print s + 0 }' || true)"
if [ "$total" -eq 0 ]; then
  echo "::error::Miri executed 0 tests — the module-path selection matched nothing. Was a selected module renamed? See MIRI_TEST_SELECTION in .github/workflows/miri.yml." >&2
  exit 1
fi
echo "Miri executed ${total} test(s)."
