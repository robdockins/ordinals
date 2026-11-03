# Constructive Ordinals in Lean 4 (port in progress)

This directory is a Lean 4 port of the Rocq development in `../Ordinal`. The
port aims to be mathematically faithful: every definition and theorem keeps
its meaning, including every `complete`, excluded-middle and choice
hypothesis. Names and syntax follow Lean conventions.

The type of ordinals is `ConstructiveOrdinals.Ordinal`.

## Rules

- **No axioms.** No declaration may depend on `propext`, `Quot.sound`,
  `Classical.choice`, `sorryAx` or `Lean.ofReduceBool`. Classical principles
  appear only as explicit hypotheses (`ExcludedMiddle`,
  `DependentFunctionalChoice`, … in `Prelude/Logic.lean`).
  `scripts/AxiomAudit.lean` enforces this.
  In practice this rules out `simp`, `omega`, and `rw` with an `↔`. A
  `match` with an overlapping wildcard case (`| .eq => b | a => a`) also
  compiles to a proof that uses `propext`, so definitions spell out every
  case; for the same reason core's `Ordering.then` is replaced by
  `lexCompare`. Many core
  `List` lemmas also use `propext`, so `Prelude/` re-proves the facts we need.
- **Lean core only.** No Mathlib, Batteries or Aesop.
- **Every Rocq declaration is accounted for.** Each Lean docstring cites its
  Rocq source as ``Rocq: `File.name` ``. `scripts/port_map.py` generates
  `PORTING_MAP.csv` from these citations, plus `scripts/port_overrides.csv` for
  deliberate drops and merges. It fails if any declaration of a Rocq file
  that has a Lean module is unaccounted for.

## Tactics

Lean has no counterpart to Rocq's setoid rewriting, so
`Tactic/OrdRewrite.lean` provides one:

- `ord_rw [h, ← h']` rewrites with `h : a ≤ b`, `a < b` or `a ≈ b` inside
  goals or hypotheses of the form `L ρ R`, for `ρ` one of `≤`, `<` or `≈`. It
  proves the needed monotonicity facts with lemmas tagged `@[ord_mono]`, the
  analogue of Rocq's `Add Parametric Morphism`. It also accepts `=` (passed to
  `rw`) and `↔` (applied with `Iff.mpr`, avoiding `propext`).
- `ord_mono` proves `s ρ t` by congruence, like Mathlib's `gcongr`.
- `ord_auto` is the analogue of `auto with ord`: a `solve_by_elim` over
  lemmas tagged `@[ord_hint]`.

## Commands (run from this directory)

```sh
lake build                              # build the library
lake env lean test/OrdRewrite.lean      # tactic tests
lake env lean scripts/AxiomAudit.lean   # axiom audit
python3 scripts/port_map.py             # porting map and progress
```

## Status

| Rocq file | Lean module | State |
|---|---|---|
| `Defs.v` | `Defs.lean` | done |
| `Operators.v` | `Operators.lean` | done |
| `Arith.v` | `Arith.lean` | done |
| `Classical.v` | `Classical.lean` | done |
| `Enumerate.v` | `Enumerate.lean` | done |
| `Fixpoints.v` | `Fixpoints.lean` | done |
| `Cantor.v` | `Cantor.lean` | done |
| `Reflection.v` | `Reflection.lean` | done |
| `VeblenDefs.v` | `Veblen/Defs.lean` | done |
| `VeblenCon.v` | `Veblen/Constructive.lean` | done |
| `VeblenFacts.v` | `Veblen/Facts.lean` | done |
| `VeblenClassical.v` | `Veblen/Classical.lean` | done |
| `NaturalArith.v` | `NaturalArith.lean` | done |
| `WellFounded.v` | `WellFounded.lean` | done |
| `Examples.v` | `Examples.lean` | done |
| `GoodsteinSequences.v` | `GoodsteinSequences.lean` | done |
| `AckermannTower.v` | `AckermannTower.lean` | done |
| `SchutteColumn.v` | `Schutte/Column.lean` | done |
| `SchutteColumnFacts.v` | `Schutte/ColumnFacts.lean` | done |
| `Notation/CantorNotation.v` | `Notation/Cantor.lean` | done |
| `Notation/CantorDecomposition.v` | `Notation/CantorDecomposition.lean` | done |
| `Notation/VNotation.v` | `Notation/V.lean` | done |
| `Notation/VWNotation.v` | `Notation/VW.lean` | done |
| `Notation/ATowerFinNotation.v` | `Notation/ATowerFin.lean` | done |
| `Notation/ATowerNotation.v` | `Notation/ATower.lean` | done |
| `Notation/SchutteStack.v` | `Notation/SchutteStack.lean` | done |
| everything else | — | not started |

`python3 scripts/port_map.py` prints per-file progress.

Deliberate differences from Rocq (statements are otherwise transliterated):

- Rocq's binary `positive`/`N` and their ordinal embeddings (`posOrd`,
  `nOrd`, `ωN`) are merged into the `Nat` embedding `Ordinal.ofNat`, since
  Lean's `Nat` is already binary in the kernel.
- The Rocq standard library's relation constructions (closures, `Desc`,
  `lex_exp`, `list_ext`, `Permutation`, symmetric and lexicographic
  products) are re-proved axiom-free in `Prelude/Relations.lean`. In
  `WellFounded`, `wf_lex_exp` and `wf_list_ext` are not taken from a library
  but derived from the ordinal interpretations (`lex_exp_lt_interp`,
  `listExtInterp_lt_of_ext`).
- Rocq's canonical structures that attach measures to types become `Sized`
  instances. Lemmas in `Examples` that take `(A : Ord)` and values in its
  carrier take a type with a `[Sized α]` instance instead; the named ordinals
  (`FunOrd`, `ListOrd`, …) are kept as definitions. In the nested-inductive
  example, Rocq's `list (qwerty n)` becomes a third mutual type `QwertyList`,
  because Lean's kernel rejects nested occurrences whose parameters mention
  constructor arguments.
- In `GoodsteinSequences`, binary `N` becomes `Nat`, and division and
  remainder are `ConstructiveOrdinals.Nat.div`/`mod` (repeated subtraction
  with fuel), because every core lemma about `/` and `%` uses `propext`. The
  `Program Fixpoint`s `hbn_decompose_step` and `hbn_decompose` recurse on
  explicit fuel, so `compute_goodstein_eq` is checked by kernel computation
  (`decide +kernel`). Their unfolding equations are proved separately.
  Rocq's `nth_error` is `ConstructiveOrdinals.List.nthError`, because core's
  `l[i]?` depends on `propext` through its `GetElem?` instance.
- `ackermannTower` and `schutteColumn` use the same pattern as `veblen`. The
  nested Rocq `fix`es become separate inner functions, parameterised by the
  outer recursive calls; `schutteColumn` needs two (`schutteColumnα`,
  `schutteColumnX`), since its inner `α`-recursion supplies the base function
  of the outer recursive call.
- Lean has no universe cumulativity, so carriers built from `Prop` or `Nat`
  use `PLift`/`ULift` (for example `truthOrd P` is indexed by
  `ULift (PLift P)`, and `ω` by `ULift Nat`). In `Reflection`, the
  ordinal-side interpretations of the `prop` and `nat` shapes are `ULift`ed.
- Rocq reuses names across files (each file is its own module); Lean's
  namespaces are shared, so clashes are resolved as follows. `VeblenCon.v`'s
  variants of `Enumerate.v`/`Fixpoints.v` names (with normal-function and
  completeness hypotheses) are in `Ordinal.Con`, for example
  `Con.Enumerates`; declarations with identical statements are merged.
  `VeblenClassical.v` is in `Ordinal.VeblenClassical`.
- Each notation system lives in its own namespace
  (`ConstructiveOrdinals.CantorNotation`, …), with the syntax and its
  operations in a namespace named after the type (`CantorForm.compare`,
  `CantorNormalForm.add`, …). The syntax types are nested inductives over
  `List`, as in Rocq; functions on them are pairs of mutually recursive
  functions on terms and on lists of terms (instead of an inner `fix` or a
  `fold_right`), and proofs about them are mutually recursive theorems of the
  same shape. Notation systems denote `Ordinal.{0}`.
- `SchutteStack.v` defines its comparison by well-founded recursion on the
  term size, through dependently typed functions that return their own
  correctness proofs. The Lean port uses plain functions with explicit fuel
  (`compareFuel`), so that comparison computes in the kernel, and proves
  correctness separately.
- Theorems stated in a Rocq `Section` take exactly the hypotheses Rocq's
  `Check` reports after the section is closed. `Hypothesis EM` becomes an
  explicit `(em : ExcludedMiddle)` argument.

The `Countable.v` theory is experimental and is not being ported.
