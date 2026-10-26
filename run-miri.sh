#!/usr/bin/env bash
#
# Runs `cargo miri test` with the given pass-through arguments and fails if the
# run executed zero tests.
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
# MIRIFLAGS is read from the environment; the caller sets it. Everything passed
# to this script is forwarded verbatim to `cargo miri test`, e.g.
#   MIRIFLAGS="..." ./run-miri.sh --target i686-unknown-linux-gnu -- types::overflowing_int::
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
  echo "::error::Miri executed 0 tests — the module-path selection matched nothing. Was a selected module renamed? See the representations matrix in .github/workflows/miri.yml." >&2
  exit 1
fi
echo "Miri executed ${total} test(s)."
