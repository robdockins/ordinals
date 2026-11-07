# Constructive Ordinals in Lean 4

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
lake env lean scripts/CheckPortMap.lean # every Lean name in the map exists
python3 scripts/statement_review.py     # regenerate STATEMENT_REVIEW.md
```

`statement_review.py` also needs the Rocq development built (`make` in the
repository root) and `coqc` on the path. CI
(`../.github/workflows/lean.yml`) runs all the other commands on every push.

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
| `NaturalProduct.v` | `NaturalProduct.lean` | done |
| `WellFounded.v` | `WellFounded.lean` | done |
| `Examples.v` | `Examples.lean` | done |
| `GoodsteinSequences.v` | `GoodsteinSequences.lean` | done |
| `AckermannTower.v` | `AckermannTower.lean` | done |
| `SchutteColumn.v` | `Schutte/Column.lean` | done |
| `SchutteColumnFacts.v` | `Schutte/ColumnFacts.lean` | done |
| `Notation/CantorNotation.v` | `Notation/Cantor.lean` | done |
| `Notation/Interpolants.v` | `Notation/Interpolants.lean` | done |
| `Notation/CantorDecomposition.v` | `Notation/CantorDecomposition.lean` | done |
| `Notation/CantorProduct.v` | `Notation/CantorProduct.lean` | done |
| `Notation/VNotation.v` | `Notation/V.lean` | done |
| `Notation/VWNotation.v` | `Notation/VW.lean` | done |
| `Notation/ATowerFinNotation.v` | `Notation/ATowerFin.lean` | done |
| `Notation/ATowerNotation.v` | `Notation/ATower.lean` | done |
| `Notation/SchutteStack.v` | `Notation/SchutteStack.lean` | done |
| `Notation/SchutteMatrix.v` | `Notation/SchutteMatrix.lean` | done |

The port is complete. Of the 2,163 Rocq declarations outside `Countable.v`:
- 2,150 are ported;
- 12 are merged into an equivalent declaration (mostly the binary-number
  embeddings, which coincide with `ofNat`);
- one, `tree_selection_complete`, is dropped because its Rocq proof is
  aborted.

`scripts/port_overrides.csv` gives a reason for each merge and drop. No
declaration depends on any axiom, and the build has no warnings.

`STATEMENT_REVIEW.md` sets the statements of 331 headline results beside their
Rocq originals: every Rocq `Theorem`, plus the reflection, notation and
order-type theorems. Both sides are printed by the provers themselves. The
review found no mathematical discrepancies, and its introduction lists the
systematic presentational differences.

Kernel computations check the Goodstein sequence starting at 4 against OEIS
A056193. Each notation system has sample comparisons or normalizations checked
by `rfl` or `decide`.

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
- In `NaturalProduct` and `Notation/CantorProduct`, Rocq's `flat_map`s
  (`cut`, `cnf_prod`, `cantor_pairs`) are the same lists built by direct
  recursion, so that their membership lemmas are axiom-free. The natural
  product is `NaturalProduct.nmul`; it has no infix notation, to avoid
  confusion with the incorrect product `⨳` of `NaturalArith`. The canonical
  tree of notations `CantorProduct.Trec` recurses on an accessibility proof.
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
- `SchutteStack.v` and `SchutteMatrix.v` define their comparisons by
  well-founded recursion on the term size, through dependently typed functions that return their own
  correctness proofs. The Lean port uses plain functions with explicit fuel
  (`compareFuel`), so that comparison computes in the kernel, and proves
  correctness separately.
- Theorems stated in a Rocq `Section` take exactly the hypotheses Rocq's
  `Check` reports after the section is closed. `Hypothesis EM` becomes an
  explicit `(em : ExcludedMiddle)` argument.

The `Countable.v` theory is experimental and is not being ported.

## How this port was made

The port was written by an AI model, Claude Opus 5.5 (`claude-opus-5-5`),
working in Claude Code under the direction of the Rocq development's author.

**Process.** The author set the constraints at the start: mathematical
fidelity first, no axioms, Lean core only, and `Countable.v` skipped. The
model drafted a plan, the author approved it, and the author then started
each phase:
- **Phase 0:** tooling and a pilot.
- **Phase 1:** the arithmetic core.
- **Phase 2:** the Veblen hierarchy.
- **Phase 3:** natural arithmetic, well-founded relations, examples and
  Goodstein sequences.
- **Phase 4:** Ackermann towers and Schütte columns.
- **Phase 5:** the notation systems.
- **Phase 6:** wrap-up.

**Tooling.** Phase 0 built the tooling everything else relied on:
- the axiom audit;
- the porting-map generator, driven by `Rocq:` citations in docstrings;
- the `ord_rw` / `ord_mono` / `ord_auto` tactics, which stand in for Rocq's
  setoid rewriting and hint databases.

**Working method.** Files were ported in dependency order, one commit per
Rocq file. Each file was built, audited and checked against the map before
the next began. Most of the debugging was about keeping proofs axiom-free:
- overlapping `match` cases, `simp`, `omega` and many core lemmas introduce
  `propext`;
- avoiding `funext` meant working with pointwise equivalences;
- comparison functions were rewritten with explicit fuel, so that they
  compute in the kernel.

Proof simplifications noticed along the way are recorded in
`BACKPORT_NOTES.md`. Phase 6 compared the headline statements against Rocq's
own `Check` output (`STATEMENT_REVIEW.md`).

**Resources (approximate).** These figures come from the session transcript;
the work ran as a single long session with periodic context compaction.
- **Wall-clock time:** about 20 hours from the first request (evening of
  2 November 2026) to the end of Phase 6 (afternoon of 3 November). This
  includes pauses waiting on the author and at least one usage-limit reset.
  The commits span about 14 hours, from Phase 0 to the last notation file.
  Time spent actively working was roughly 5–15 hours; the bounds depend on
  how long gaps (long builds and long generations) are counted.
- **Model calls:** about 600.
- **Output tokens:** about 1.8 million generated by the model.
- **Input tokens:** about 250 million, almost all of them prompt-cache reads
  of the conversation context, which is re-sent on every call. About
  5.5 million were cache writes, and only a few thousand were uncached.
- **Not counted:** the machine time for Lean builds and Rocq checks.
