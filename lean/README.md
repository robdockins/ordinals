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
  In practice this rules out `simp`, `omega`, and `rw` with an `↔`. Many core
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
| everything else | — | not started |

`python3 scripts/port_map.py` prints per-file progress.

Deliberate differences from Rocq (statements are otherwise transliterated):

- Rocq's binary `positive`/`N` and their ordinal embeddings (`posOrd`,
  `nOrd`, `ωN`) are merged into the `Nat` embedding `Ordinal.ofNat`, since
  Lean's `Nat` is already binary in the kernel.
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
- Theorems stated in a Rocq `Section` take exactly the hypotheses Rocq's
  `Check` reports after the section is closed. `Hypothesis EM` becomes an
  explicit `(em : ExcludedMiddle)` argument.

The `Countable.v` theory is experimental and is not being ported.
