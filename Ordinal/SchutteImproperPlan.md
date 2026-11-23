# Plan: normalizing improper Schütte matrices natively

Goal: a normalizer for arbitrary `VForm` matrices (columns in any order,
repeated heights, zero entries, height-0 columns anywhere) that returns
the normal form of the same ordinal, built directly on `schutte_column`
/ `schutte_matrix` rather than by translating to and from the Bachmann
notation.  The Bachmann development (`hereditary_absorption`, `normSX` in
`Notation/BachmannImproper.v`) supplies the ideas, not the code.

Target theorem: for every VForm x, `VF_normal (VF_normalizeX x)` and
`VF_denote (VF_normalizeX x) ≈ VF_denote x`.

## Status (2026-11-22)

Milestone 1 (ordinal level) DONE, axiom-free, `Ordinal/SchutteAbsorb.v`:

- `schutte_column_merge` (≤ and ≥ halves):
  `col (col P c a) c x y ≈ col P c (a + x) y`.
- `absorb_critical` (⇐) and `absorb_critical_inv` (⇒): for b < β, in the
  principal regime `Reg P β := Prin P ∨ 1 < β` (`Prin P`: fixpoints of P
  are additively principal), and z principal with 1 < z:
  `crit_{col P b a}(β,α) z  ⟺  crit_P(β,α) z ∧ a < z`.
- `absorb_shift`: given s with a < col P β α s and col P β α s below every
  critical point above a, `col (col P b a) β α x ≈ col P β α (s + x)`.
- `low_regime_veblen`: for ω^m ≤ d < ω^(m+1) and e > 0,
  `veblen (d + ·) e y ≈ ω^(m+e) + y` (the case Reg excludes).

Milestone 2 (notation level): NOT STARTED.  Design below.

## Conventions

`schutte_matrix f (c :: l) x = schutte_matrix (schutte_column f b a) l x`
for c = (b, a): the first column modifies the base innermost, and later
columns are built over it.  `VF_denote (N l)` is the matrix at argument 0.
A normal matrix (`VF_normal`) is sparse, has strictly decreasing heights
(so at most a final height-0 column), normal entries, and entries below
its value.  `crit_P(β,α)` is `schutte_critical P β α`.

## How milestone 1 avoids the constructivity problems

The earlier plan worried about subtraction and least elements.  Both are
avoided:

- Critical sets, not ranges.  The invariant is stated on the predicates
  `schutte_critical`, which `schutte_column_enumerates` relates to the
  columns constructively.  No preimages are ever computed.
- U = (a < ·), not (a + · ≤ ·).  In the principal regime the upward closed
  region is "above a", which is trivially upward closed.  The low regime
  (where a + z ≤ z is not equivalent to a < z) is a separate closed-form
  lemma.
- The shift s is supplied by the caller (notations compute it); the shift
  theorem then follows from the two enumerations and `addOrd_lt_cases'`.
- No comparison of ordinals: where the proof would compare two heights b,
  b' < β, it uses a common child of β above both (`below_join`) and the
  merge lemma instead.
- The induction for `absorb_critical` is on β, then α, quantified over all
  bases.  For a' < α it uses the bound
  `col (col P b a) β a' y ≤ col P β a' (succ a + y)` (from the inductive
  hypothesis at a'), which makes the lower column a 0-column absorbed at
  a smaller height b' < β.

## Milestone 2: the normalizer (design)

State: (N, T) with N a normal-entried list of strictly decreasing
heights ≥ 1, and T a normal pending shift; invariant
`M_input(x) ≈ M_N(T + x)` for complete x (M_L = schutte_matrix (1+·) L).
Process the input columns left to right after normalizing all heights
and entries:

- (0, a): T := T ⊕ a.
- (h, Z): skip.
- (h, e), h ≥ 1, e ≠ 0: split N = N_keep ++ Popped (Popped = maximal
  suffix with heights < h).
  - Nothing absorbed (Popped = [], T = 0): push (h,e), or merge with an
    equal last height (`schutte_column_merge`); T' := 0.
  - Low regime (h = 1, T ≠ 0, N has no height ≥ 2; then N ∈ {[], [(1,c)]}):
    M_N(T + ·) = d + · with d = value of N ++ [(0,T)]; result
    N' := [(1, lead(d) ⊕ e)], T' := 0 (`low_regime_veblen`, lead via the
    Cantor decomposition).
  - Principal regime (h ≥ 2, or N has a height ≥ 2 column): every popped
    column and T is absorbed.  N_new := N_keep ++ [(h,e)], merged if the
    last height of N_keep is h; T' := off_{N_new}(max of the popped entries
    and T).  Correctness: iterate `absorb_critical`/`_inv` over
    Popped ++ [(0,T)] (all heights < h) to get "crit over the state =
    crit over M_{N_keep} ∩ above every absorbed entry", then a list
    version of `absorb_shift`.

Final: `Nnorm (N ++ [(0,T)])` (dropping (0,T) if T = 0).

Offset off_X(m) for a normal list X (heights ≥ 1, last entry > 0,
principal values): least t with m < M_X(t); spec used:
`m < M_X(t) ∧ ∀ y < t, M_X(y) ≤ m` (implies the `absorb_shift` hypothesis
via `enumerates_least`).  Recursion on the size of m:
- m < M_X(0): t = 0.
- else m = N ys, ys = Y (++ [(0,y')]); compare Y with X lexicographically
  (heights, then entries, columnwise from the first column):
  - Y = X: t = succ y'.
  - Y > X: m is a fixpoint of M_X (lemma FIXGT), t = succ m.
  - Y < X: t = off_X(u), u = max of y' and Y's entries (lemma NEST: every
    value of M_X above u is above m).

Ordinal-level lemmas still needed for milestone 2:
- `Prin` propagation: Prin P ⇒ Prin (col P b a); Prin (col P b a) for
  1 < b, 0 < a.  Hence Prin M_N when N has a column of height ≥ 2.
- Iterated absorption over a list of columns (heights < β, entries < z):
  crit_G(β,·) z preserved, and its converse.
- List version of `absorb_shift`.
- NEST and FIXGT for lexicographically ordered proper matrices (both
  reduce to iterated absorption at the first differing column; the
  regime holds because the relevant height is ≥ 2 whenever a column is
  actually absorbed).
- Entries of a proper nonzero matrix lie below its value
  (`nontrivial_matrix_member_lt` may suffice).

Notation-level pieces: lexicographic compare of column lists via
`VF_compare`; `off` with fuel; the append step and fold; lead exponent
from `VF_decompose`; `VF_normalizeX`; correctness and normality (finish
with `Nnorm_eq`, `Nnorm_normal`).

## Not needed after all

- The general "absorption = shift for any base" conjecture: only the
  principal regime and the explicit low-regime formula are used.
- Ordinal subtraction: the state keeps one pending shift T, and each
  absorption recomputes the offset from the maximum absorbed entry against
  the new list (crit sets intersect to "above the maximum"), so shifts are
  never composed.
