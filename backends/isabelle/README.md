# Isabelle/HOL backend

`aeneas -backend isabelle` translates the Pure AST into Isabelle/HOL theories that
import `Primitives.thy` (this directory). See `FORK.md` at the repository root for the
build and check workflow (`scripts/check-isabelle.sh`), and `backends/isabelle/ROOT`
for the Isabelle session of the prelude.

## Status (2026-10-01)

Translation sweep over `tests/src` (114 inputs, per-test skip directives ignored):

| | count |
|---|---|
| inputs fully translated | 103 |
| partially translated (Aeneas-level limitations, see below) | 8 |
| generated theories accepted by Isabelle2025-2 | 94 of 111 |
| remaining `axiomatization` in the regression theories | 1 (trait method with its own type parameters) |
| admitted lemmas (`sorry`) | 21 (const-generic well-formedness of functions with loops) |

## Known gaps that are fixable in the backend

Failures of the translation sweep when the theories are checked by Isabelle, by cause:

1. **Builtin trait impls printed out of record order** (6 theories: ArraySliceIndex,
   Issue789LoopCtxMatch, IterAdapters, Order, Slices, VecIter). Implementations of the
   prelude's `core_slice_index_SliceIndex` record (e.g. for `RangeFrom<usize>`) are
   printed without the `sealedInst` parent field and with the fields in an order Isabelle
   rejects. Fix: print the fields of builtin trait records in declaration order and emit
   the parent-clause field.
2. **Missing prelude models** (5 theories): `core::default::Default` with its integer
   instances (Default, IssueCharon1172), `core::iter::traits::collect::IntoIterator`
   (Issue1043IteratorMethods, StringChars), `core::slice::iter::IterMut` (Issue1192, also
   blocked by an Aeneas limitation). Register them in `ExtractBuiltin.ml`
   (`mk_isabelle_only`) and define them in `Primitives.thy`, following
   `ExtractBuiltinLean.ml` and `Aeneas/Std`.
3. **Name clashes with Isabelle/HOL** (5 theories): a Rust variable called `sum`
   shadows the HOL constant (Issue1140GlobalLoop); anonymous constants produce a
   malformed name (Issue1250AnonymousConst); identifiers that are Isabelle keywords are
   printed unescaped (LeanKeywordsClash, LoopsIssues); the recursive trait-impl path
   prints `sorry` where a type is expected (MutuallyRecursiveTraits). Fix: extend
   `escape_isabelle_standard_library_name` / the keyword list, and the anonymous-const
   and recursive-impl printers.
4. **Literal `case` with a non-integer scrutinee** (Scalars): the if-chain translation of
   literal matches only covers integer literals; extend it to `char`/`bool`.

Other gaps:

- **Mutual recursion**: only pairs of `u32` countdown functions get a `function ... and`
  definition with a generated termination proof; other groups are opaque constants. A
  general encoding is a single `partial_function (result)` over a sum type of the
  arguments.
- **Trait objects**: `dyn Trait` is the abstract type `dyn` with the uninterpreted
  constructor `dyn_mk`; methods cannot be called on a trait object (enough for
  `derive(Debug)`).
- **Default methods of user traits**: the impl record refers to itself through the
  trait's default-method function. Only the builtin traits (Clone, PartialEq, Eq,
  PartialOrd, Iterator) are handled, via the prelude's `<trait>_<method>_default_body`.
- **Trait methods with their own type parameters** are axiomatized (no polymorphic
  record fields in HOL).
- **Iterator adapters** (enumerate, take, zip, rev, map, chunks_exact, Vec::into_iter),
  **strings/chars**, **Default**, **IntoIterator** have no models yet.
- **Proof support**: the prelude provides `f.fixp_induct` for `partial_function` definitions
  and nothing else (no counterpart of Lean's `progress`/`step`/`scalar_tac`); the
  const-generic well-formedness lemmas of functions with loops are admitted.

## Aeneas-level limitations (shared with the Lean backend)

Higher-ranked implied lifetime bounds (`higher_ranked_implied_bounds_*`), raw-pointer
dereferencing, `iter_mut` combined with `zip` (issue-1192), mutually recursive traits,
generics instantiated with `&mut` (e.g. `Option::ok_or` on `Option<&mut [u8]>` in the SBPF
case study), floats, async, mutually recursive globals.

## Modelling choices

- `'a result = Ok | Fail error | Diverge`; recursive functions and loops are least fixed
  points via `partial_function (result)`; `loop_unfold` is a lemma.
- Machine integers are `int` with range predicates; arrays, slices and `Vec` are lists.
- Traits are records; const generics are explicit `usize` parameters plus well-formedness
  predicates; associated types are type parameters.
- The printer emits Isabelle escape symbols (`\<Rightarrow>`); `isabelle build` rejects raw
  Unicode, only jEdit recodes it.
- `core::fmt` is the Lean backend's simplistic model (abstract formatter, every operation
  succeeds).
