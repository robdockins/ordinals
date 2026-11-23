# Plan: one rewrite system for all Bachmann notations (not started)

Status (2026-11-22): PLAN ONLY, nothing formalized.  Optional: the
development is complete without it.  Written after Option 1 (below) was
done, to record what the larger unification would involve.

## Where things stand

Files (all under `Ordinal/Notation/`):

- `BachmannNormalize.v`: the rewrite system on *proper* terms.
  `redex` has two rules: `redex_arg` (φ_T(y) ≤ y ⇒ y) and `redex_coef`
  (φ_T(y) ≤ k, k a coefficient of T ⇒ k).  `red_S`/`red_I` close it under
  contexts.  Results: `redex_sound`, `red_size` (every step decreases
  size) ⇒ `strongly_normalizing`; `normS`/`normI` (the normalizer),
  `normalize_correct`; `nf_iff_irreducible`, `normalizes_unique`,
  `reduce_confluent`.  Also the smart constructor `smartN` (decides the
  two redex conditions on a normal `T`, `y`: `fix_test`, `coll_test`).
- `BachmannImproper.v`: `normSX`, defined on *every* notation, by
  functions (`normTX`, `normX`/`addT`, `offX`, `smartC`, `smartN`);
  correctness from `hereditary_absorption` and `normalizeX_correct`;
  `normSX_nf`, `normSX_equal`, `normSX_complete`.

Proper = indices hereditarily in Ω-Cantor normal form (exponents strictly
decreasing, positive coefficients), with coefficients and arguments
arbitrary terms.  After Option 1, `BS_proper`, `BI_proper`, `normS` and
`normI` are used only inside `BachmannNormalize.v`; the rest of the
development uses `BS_nf` and `smartN` (`smartN_nf`, `smartN_equal`).

Why the two layers exist: `normSX` is built on interpolants and the
absorption theory, which in turn need a smart constructor, so the
proper-only layer is the bootstrap.  It is not needed to normalize
improper terms.

## What "folding in" means

A single relation `red` on all terms (no properness hypothesis) with:

- normal forms exactly `BS_nf`;
- strong normalization;
- confluence (from unique normal forms, as now);
- `normSX` becoming one strategy, stated as `reds x (normSX x)`.

Then `BS_proper`, `BI_proper`, `normS`, `normI` and the proper-only
`normalize_correct` disappear.

## Rules

Existing, to be generalized:

1. `redex_arg`: sound for every term (φ is normal, so φ_T(y) ≥ y).
2. `redex_coef`: needs `dominance`, which already holds for improper
   indices with positive coefficients (`imp_ok_pos`, used in
   `Kend_of_valueX`).  Check the exact positivity side condition for
   unnormalized coefficients.

New, index-local and `bequiv`-sound (they preserve the denoted tree up to
`bequiv`, hence φ), so they may fire at any position:

3. Drop a zero summand: `BIC e BZ r → r`.  Size decreases.  (Coefficients
   are reduced to normal form first by `red_coef`, so syntactic `BZ`
   suffices.)
4. Merge equal exponents: `BIC e c (BIC e' c' r) → BIC e (c ⊞ c') r` when
   `e`, `e'` are normal and equal.  Sound by `bequiv_merge`.  The sum
   `c ⊞ c'` must be a term: use `BS_add` on normal coefficients (a function
   in the rule), or add a sum constructor.  See Termination.

New, not index-local:

5. Absorption.  Dropping an out-of-order summand is *not* a `bequiv`
   (e.g. φ_{c+Ω} enumerates the ε-numbers above c, which is not φ_Ω); it
   holds only with an argument shift: φ_X(y) = φ_{normX X}(offX X + y).
   So the rule acts at a `BN`: `BN X y → BN X' (t ⊕ y)`.
   Absorption inside an exponent also feeds the shift, via the *global*
   largest absorbed coefficient `absM` over every depth.

## Choices for rule 5

(A) Big-step: `BN X y → BN (normX X) (offX X ⊕ y)` whenever `normX X ≠ X`
    (X `imp_ok`: normal exponents, positive normal coefficients).
    Soundness is exactly `hereditary_absorption`; nothing new to prove.
    Drawback: the rule is the normalizer in disguise (a function call, not a
    local pattern).  Still gives a relation with SN and confluence, and
    makes the final theorem uniform.  Rules 3 and 4 would then be subsumed
    for `imp_ok` indices but are still wanted to reach `imp_ok` (zero
    coefficients, unnormalized coefficients) and as honest local rules.

(B) Small-step: remove one out-of-order summand at any depth, shifting by
    its offset against the resulting index.  Needs a new lemma: `absorb`
    (currently top-level only, section `absorb`/`abs_all`) generalized to a
    prefix context and to summands inside exponents.  Likely the size of the
    `absorb` section (about 400 lines) plus lifting through contexts.
    Offsets of successive steps add, while `offX` uses the maximum absorbed
    coefficient; both are correct by soundness, but the agreement of the
    final shift as a *term* (up to `BS_denote`) should be checked.
    Not recommended unless a genuinely local description is wanted.

Recommendation: (A) first.  Treat (B) as a separate research task.

## Termination (the real unknown)

`red_size` no longer works: `t ⊕ y` and `c ⊞ c'` can be larger than what
they replace.  Candidate measure (unverified): an ordinal-valued or
multiset measure such as ω^{size T} ⊕ size y (so reducing T dominates
anything done to y), with bounds

- `size (BS_offset R m)` ≲ `size m` + constant,
- `size (BS_add c c')` ≲ `size c + size c'`,

so that absorbing summand `Ω^e·c` (size ≥ size e + size c + 1) pays for the
shift.  These bounds need proofs about `BS_offset` (`offN`, `offStep`) and
`BS_add` (via the Cantor decomposition).  If they fail, fall back to a
lexicographic measure on (number of out-of-order or equal-exponent adjacent
pairs, size).

## Irreducible ⇔ normal

Prove: every non-`BS_nf` term has a redex.  Cases on why `BI_nf` fails
for an index: zero coefficient (3), equal exponents (4), increasing
exponents (5), non-normal coefficient or exponent (context rules), then
`smartN`-style tests (1, 2) at the `BN`.  Needs `normX X = X` iff the
index has no out-of-order, equal or zero summand (`normX_id` is one
direction).

## Confluence

As now: SN + value preservation + unique normal forms per value
(`BS_compare_correct`, `BS_nf_unique`, `normSX_complete`) ⇒ confluence.
Cheap once SN and soundness are done.

## Reorganization

- The new system lives in a new file `BachmannRewrite.v`, after
  `BachmannImproper.v` (it needs `hereditary_absorption`).
- `BachmannNormalize.v` keeps the functions the earlier files need
  (`fix_test`, `coll_test`, `kmax`, `smartN`, `Kend` machinery, `dominance`
  uses) and loses the rewrite system, `BS_proper`, `normS`, `normI`.
- The notation README row for `BachmannNormalize.v` moves to the new file.
- Examples and the `reduce_confluent`/`strongly_normalizing` names are
  kept, restated without properness.

## Order of work

1. Generalize `redex_sound` to arbitrary terms (rules 1, 2); decide the
   positivity side condition.
2. Rules 3 and 4 with soundness (`bequiv`); size bounds for `BS_add`.
3. Rule 5(A); termination measure and the size bounds for `BS_offset`.
4. Irreducible ⇔ normal; SN; confluence.
5. Move the files, delete `BS_proper`/`normS`/`normI`, update README.

## What this buys, and what it does not

Buys: one relation, no properness hypotheses, `normSX` explained as a
strategy.  Does not buy: any new equality of ordinals.  `normSX_complete`
already decides equality of denotations for arbitrary notations, so SN and
confluence for improper terms are mostly presentational.
