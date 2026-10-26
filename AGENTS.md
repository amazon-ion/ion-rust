# Agent Instructions for `ion-rust`

`ion-rs` is a Rust implementation of
[Amazon Ion](https://amazon-ion.github.io/ion-docs/). It supports Ion 1.0 only, and
the 1.1 and `conformance` corpora in `ion-tests` are intentionally not run.

## Setup

- Initialize submodules before building or testing:
  `git submodule update --init --recursive`. The `ion-tests` and `ion-hash-test`
  submodules supply conformance test data.
- Library MSRV is `rust-version` in `Cargo.toml`; do not use newer language
  features or std APIs in `src/`. CI never builds on the MSRV (dev-dependencies
  need a newer toolchain); it tests on stable.

## API stability

- The stable public surface is what compiles with default features (plus
  `bigdecimal`). Everything behind `experimental*` features is explicitly
  unstable.
- Put new public APIs behind an existing `experimental*` feature (do not add
  Cargo features without asking) unless maintainers have agreed to stabilize
  them. If crate code uses the item under default features, gate its visibility,
  not the item: `#[cfg_attr(feature = "...", visibility::make(pub))]` on a
  `pub(crate)` item, or paired `cfg`/`cfg(not)` `pub use`/`pub(crate) use`
  re-exports.
- Do not change the stable surface without discussion. Snapshots of it live in
  `api/` but omit auto traits and derives: do not drop `Send`/`Sync` or derives
  from stable types (pin `Send + Sync` with a test-local `assert_send_sync` fn,
  as in `src/element/annotations.rs`).
- `=`-pinned dependency versions in `Cargo.toml` are deliberate. Do not bump
  them as a side effect of other work.

## Verifying changes

Run what CI runs, including its `RUSTFLAGS="-D warnings"`. Feature-gated code
breaks easily if only default features are tested. You MUST run at least the
following before opening a PR.

```bash
cargo fmt --check
RUSTFLAGS="-D warnings" cargo test --workspace
RUSTFLAGS="-D warnings" cargo test --workspace --all-features
RUSTFLAGS="-D warnings" cargo clippy --workspace --all-features --tests -- -Dwarnings
```

CI also checks the public API. With the nightly and `cargo-public-api` versions
pinned in `api/README.md`, regenerate the snapshots as it describes, then run
`git diff --exit-code HEAD -- 'api/*.txt'`. If the diff is not an agreed change,
discard the regenerated files with `git checkout -- 'api/*.txt'`, then stop and
report it (including any already-staged snapshot changes); never commit
regenerated snapshots just to make CI pass.

Refer to `.github/workflows/rust.yml` for complete information about the CI checks.

## Tests

- Known, accepted failures are in skip/ignore lists under `tests/` (e.g.,
  `ELEMENT_GLOBAL_SKIP_LIST`). Do not add entries to make a failing test pass;
  fix the bug or ask. Skipped files report success without running, so if a fix
  may cover one, remove its entry and run with `--all-features`.
- Prefer adding tests to an existing module's `#[cfg(test)]` block over creating
  new test files.
- When possible use `rstest` when adding test cases that only vary in the inputs
  and the asserted value. `rstest` is preferred over wrapper tests that delegate
  to helper functions for the entire test body.

## `unsafe` code

- New or modified `unsafe` blocks and `unsafe impl`s need a `// SAFETY:` comment
  stating the invariant that makes them sound; `unsafe fn`s document caller
  obligations in `/// # Safety`. Do not backfill existing code.
- Miri runs in CI (`.github/workflows/miri.yml`). The `full-library` job runs
  every library unit test under both tree and stacked borrows. The
  `representations` job runs each module in its matrix on 32-bit and big-endian
  targets, using default features.
- Mark a test `#[cfg_attr(miri, ignore = "too slow under Miri")]` only if other
  tests reach every `unsafe` line it does.
- Test new `unsafe` code in the library's unit tests. If its soundness depends
  on pointer width or endianness, make those tests compile under default
  features and add their module path to the `representations` matrix.
- Refer to the CI workflow to see how to run Miri tests locally, using its
  pinned `MIRI_TOOLCHAIN`.

## Performance

- Readers, writers, and value types are hot paths. Do not add allocations,
  clones, or dynamic dispatch there without benchmark evidence. `size_of`
  assertions are budgets; do not raise one without discussion.
- Back performance claims with Criterion baselines on one machine and session.

## Commits and pull requests

- Use [Conventional Commits](https://www.conventionalcommits.org/) with a scope
  where one fits, e.g., `perf(text): ...`, `fix(binary): ...`, `ci: ...`.
- Follow `CONTRIBUTING.md`. In particular: work against the latest `main` and
  keep changes focused — no unrelated reformatting. Before significant work,
  confirm with the user that a tracking issue exists; do not open issues or PRs
  unless asked.
- Do not edit files in submodules; change their recorded commit only when the
  task calls for it.
- Do not commit local data files, benchmark output, or other scratch artifacts;
  stage by explicit path, never `git add -A`/`git add .`.
- Before submitting anything for a pull request, run a local review that checks
  for any newly introduced complexity that is not absolutely necessary.
  Complexity may include implementation choices, API choices, code organization,
  excessive or obtuse documentation, or even an excessively noisy diff.

## Issues, PRs, and comments

- Do not hard-wrap prose in issue bodies, PR descriptions, or comments. GitHub
  soft-wraps; manual line breaks render as ragged text. Code blocks, lists, and
  tables keep their intentional line breaks.
- Be concise. Lead with the main point. Extra detail is tiring to read and
  buries the point; link to code, commits, or other issues rather than restating
  them.
- Assume readers know the Ion specification. Don't explain Ion concepts (e.g.,
  symbol tables, IVMs, annotations); refer to them directly.
- Don't summarize the diff file by file; reviewers can read it. Explain _why_
  and anything non-obvious.
- Never describe a potential security issue in a public issue, PR, or comment;
  see `CONTRIBUTING.md`.
