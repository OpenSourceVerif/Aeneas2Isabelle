# About this fork (X-Bulow/aeneas_isabelle)

This repository is a fork of [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas)
whose only purpose is to add an **Isabelle/HOL backend** (`-backend isabelle`).
Everything else is kept identical to upstream so that syncing stays cheap.

## Branches

| Branch | Role |
|--------|------|
| `main` | Upstream `main` **plus** the Isabelle backend. This is the branch to build and to base work on. |
| `dev`  | Scratch/feature branch. Normally equal to `main`; open feature work lives here before it is merged into `main`. |

There is no branch that mirrors upstream verbatim; use the `upstream` remote for that.

## Isabelle-specific files

- `backends/isabelle/Primitives.thy` — the Isabelle prelude (`Primitives` theory) imported by every generated theory.
- `src/extract/Extract.ml`, `ExtractTypes.ml`, `ExtractBase.ml`, `Translate.ml`, `Config.ml`, `Main.ml` — the `Isabelle` cases of the backend-dispatching code. All other backends are untouched: every change in shared code is an added `| Isabelle ->` arm or a block guarded by `backend () = Isabelle`.
- `tests/test_runner/run_isabelle.ml` — standalone runner that translates every input in `tests/src` to Isabelle (`make isabelle`).
- `casestudy/sbpf/` — the SBPF JIT safe-mode case study and its generated theories.
- `paper/` — sources of the Rust2Isabelle paper.

## Building

```sh
opam switch create aeneas 5.3.0
opam install calendar core_unix domainslib easy_logging menhir \
  ocamlformat.0.27.0 ocamlgraph odoc ppx_deriving ppx_deriving_yojson \
  progress unionFind visitors yojson zarith dune
make setup-charon        # clones and builds Charon at the commit in ./charon-pin
make build-dev           # on macOS use GNU make: brew install make; gmake build-dev
```

Translating one test to Isabelle:

```sh
make test-isabelle-loops           # tests/src/loops.rs -> tests/isabelle/
make isabelle                      # every input in tests/src, ignoring per-test directives
```

## Syncing with upstream

```sh
git remote add upstream https://github.com/AeneasVerif/aeneas.git   # once
git fetch upstream
git checkout main
git merge upstream/main          # conflicts, if any, are confined to the files listed above
make setup-charon && make build-dev && make extract-tests
```

After a sync, `git status` must show **no changes under `tests/coq`, `tests/fstar`, `tests/lean`**:
that is the check that the other backends were not affected.

## CI

GitHub Actions is **disabled** for this repository (Settings → Actions). The workflow
files under `.github/workflows/` are kept identical to upstream so that they never
conflict during a sync, but none of them run here: the fork does not publish releases,
nightly builds or documentation.
