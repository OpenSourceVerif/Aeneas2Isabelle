# About this fork (OpenSourceVerif/Aeneas2Isabelle)

This repository is a fork of [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas)
whose only purpose is to add an **Isabelle/HOL backend** (`-backend isabelle`).
Everything else is kept identical to upstream so that syncing stays cheap.

## Branches

| Branch | Role |
|--------|------|
| `main` | Upstream `main` **plus** the Isabelle backend. This is the branch to build and to base work on. |
| `test` | Scratch/feature branch. Normally equal to `main`; open feature work lives here before it is merged into `main`. |

The canonical repository is `OpenSourceVerif/Aeneas2Isabelle`; `X-Bulow/aeneas_isabelle`
is a personal mirror of it (branches `main` and `dev`). There is no branch that mirrors
upstream verbatim; use the `upstream` remote (`AeneasVerif/aeneas`) for that.

## Isabelle-specific files

- `backends/isabelle/Primitives.thy` — the Isabelle prelude (`Primitives` theory) imported by every generated theory.
- `src/extract/Extract.ml`, `ExtractTypes.ml`, `ExtractBase.ml`, `Translate.ml`, `Config.ml`, `Main.ml` — the `Isabelle` cases of the backend-dispatching code. All other backends are untouched: every change in shared code is an added `| Isabelle ->` arm or a block guarded by `backend () = Isabelle`.
- `tests/test_runner/run_isabelle.ml` — standalone runner that translates every input in `tests/src` to Isabelle (`make isabelle`).
- `casestudy/sbpf/` — the SBPF JIT safe-mode case study and its generated theories.
- `paper/` — sources of the Rust2Isabelle paper.

## How the Isabelle backend models Rust (summary)

- **Failure and divergence**: `'a result = Ok | Fail error | Diverge`. Recursive
  functions and loop bodies are least fixed points via `partial_function (result)`
  (mode defined in `Primitives.thy`, with monotonicity lemmas for `bind` and tuple
  destructuring and an induction rule `f.fixp_induct`); no termination proof is needed.
  Mutually recursive groups are still emitted as opaque constants.
- **std models**: functions, types and traits of `core`/`alloc` that the prelude models
  are registered in `src/extract/ExtractBuiltin.ml` inside `mk_isabelle_only` lists
  (the Lean backend's `ExtractBuiltinLean.ml` is the reference); the extract name
  `a.b.c` becomes the Isabelle constant `a_b_c`, which must be defined in the prelude.
  Default trait methods omitted by an impl are filled with
  `<trait>_<method>_default` prelude functions (table in `Extract.ml`).
- **Trait objects**: `dyn Trait` is the abstract prelude type `dyn`, built with the
  uninterpreted `dyn_mk`. Enough for `derive(Debug)` (the formatting model ignores
  its arguments), not for calling methods on a trait object.
- **Formatting**: `core::fmt` follows Lean's simplistic model (abstract `Formatter`,
  every operation succeeds).
- **Matches on integer literals** become `if` chains (`case` only matches constructors).
- **Known gaps**: generics instantiated with `&mut` (Aeneas-level; e.g. `Option::ok_or`
  on `Option<&mut [u8]>` in the SBPF JIT), trait methods with their own type
  parameters (axiomatized), const-generic well-formedness lemmas for functions with
  loops (admitted with `sorry`), mutual recursion.

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

## Checking generated theories with Isabelle

```sh
scripts/check-isabelle.sh            # prelude + every theory in tests/isabelle, one session each
scripts/check-isabelle.sh --strict   # also fail on `sorry`
```

The script needs `isabelle` (Isabelle2025-2) on `PATH` or as its last argument.
Two things it handles that bite in batch mode: `isabelle build` rejects raw
Unicode symbols (only jEdit recodes them), so sources are recoded with
`scripts/isabelle-recode.py`; and the generated `imports "Primitives"` is
qualified with the prelude session. The backend itself prints `\<Rightarrow>`-style
escapes, and `backends/isabelle/Primitives.thy` is kept in that form too.

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
