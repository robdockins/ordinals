# Plan: normalizing improper Schütte matrices natively

Goal: a normalizer for arbitrary `VForm` matrices (columns in any order,
repeated heights, zero entries, height-0 columns anywhere) that returns
the normal form of the same ordinal, built directly on `schutte_column`
/ `schutte_matrix` rather than by translating to and from the Bachmann
notation.  The Bachmann development (`hereditary_absorption`, `normSX` in
`Notation/BachmannNotation.v`) supplies the ideas, not the code.

Status (2026-11-22): PLAN ONLY, nothing formalized.  Do not start until
the user gives the go-ahead.

## Conventions

`schutte_matrix f (c :: l) x = schutte_matrix (schutte_column f b a) l x`
for c = (b, a): the first column modifies the base innermost, and later
columns are built over it.  `schutte_matrix_app`:
`schutte_matrix f (m1 ++ m2) x = schutte_matrix (schutte_matrix f m1) m2 x`.
`schutte_column G 0 a x = G (a + x)` (`schutte_column0`).  A proper
matrix has strictly decreasing heights with the height-0 column last.
Under `Kl`, list order matches Bachmann index order, so "an earlier
column followed by a strictly higher one" is exactly Bachmann absorption
(P + R with lead R > e).

## Why the Bachmann route fails for middle 0-columns

A 0-column (0, a) in the middle replaces the base function P of the later
columns by P ∘ (a + ·).  A Bachmann index always uses the fixed base
f = 1 + x, and a 0-column would be a term with "exponent −1", for which
the index has no slot.

## Key idea: a middle 0-column is a shift

Let P := schutte_matrix f pre (a normal function).

1. Base level.  z = P(a + z) implies z ≥ a + z, so a + z = z and P(z) = z.
   Conversely, P(z) = z and a + z ≤ z give P(a + z) = z.  Hence
   Fix(P ∘ (a+·)) = Fix(P) ∩ U_a with U_a = {z | a + z ≤ z}, which is
   upward closed.  So the fixpoints form a final segment of Fix(P).
2. Final segments shift enumerations.  A final segment of a club C with
   enumeration e is enumerated by y ↦ e(t + y), where t is the first
   index with e(t) in the segment.
3. Propagation.  If a level function satisfies L' = L ∘ (t + ·), then
   Fix(L') = Fix(L) ∩ {z | t + z ≤ z} (same argument as step 1), so the
   next level is again a shift.  At limit stages an intersection of
   final segments (⋂ U_j is upward closed) is a final segment of the
   intersection of the fixpoint sets.  The `schutte_column` recursion
   rebuilds the base inside each column (`inner_α`), so the induction
   on (β, α) must be quantified over all base functions.

Consequence (the 0-column identity):

    [pre; (0,a); post; (0,y)]  ≈  [pre; post; (0, t + y)]

for an offset t depending on a, P and post.  Trailing 0-columns merge:
(0,a), (0,b) ↦ (0, a+b), since G(a + (b + x)) = G((a + b) + x).

## Offsets

- Principal regime (post contains a column of height ≥ 2).  The values
  of the relevant levels are additively principal, so a + z ≤ z iff
  a < z.  As in Bachmann, t is the least index whose value exceeds every
  absorbed entry (the analogue of `BS_offset` / `OffSpec`).  Check
  carefully that intermediate height-1 levels inside post do not add
  conditions beyond "every absorbed entry < z" in this regime.
- Low regime (post has only height-1 and height-0 columns).  Values are
  ω^c + y, which are not principal, and offsets compound.  Example:
  [(0,ω); (1,1); (0,y)] = ω² + y, not ω·2 + y (via (1+a)·ω^c-style
  products).  This regime is plain Cantor normal form arithmetic and
  should be computed directly with the existing VForm/Cantor machinery.

## Generalization: all column absorption as a shift

Conjecture: whenever an earlier column is followed by a strictly higher
one, the higher columns built over it enumerate a final segment of what
they would enumerate without it.  So absorption of any column, not only
0-columns, is "post over Q = post over P, shifted".  If this holds, it
may give a direct proof of matrix-level hereditary absorption without
the cover machinery (`coverX`, `JE_all`) of the Bachmann proof.  If it
does not, fall back to porting the Bachmann argument:
- the Bachmann-rule clause;
- covers of matrix children with coefficient tracking;
- the joint (⇐)/enumeration induction;
- shifted enumeration (`shift_enum`).

## Planned normalizer (matrix-native)

On a column list, bottom-up (entries and heights normalized first, by
value):
1. drop columns with entry Z (schutte_column G b 0 = G up to ≈);
2. merge adjacent equal heights: (b,a),(b,a') ↦ (b, a + a') (matrix
   analogue of `bequiv_merge`; to be proved);
3. absorb any column, including height 0, that is followed later by a
   strictly higher column (right-to-left pass, like `normX`), recording
   the largest absorbed entry (like `absM`);
4. compute the offset (principal regime: least t with value > m; low
   regime: Cantor arithmetic) and shift the final argument;
5. finish with the existing `VF_normalize` (`Nnorm`) on the now-proper
   matrix.
Target theorem: for every VForm x, VF_normal (VF_normalizeX x) and
VF_denote (VF_normalizeX x) ≈ VF_denote x.

## Implementation order (when approved)

1. Shift-propagation lemma in the `SchutteColumn` setting: for any
   normal base G and any t, at every (β, α), the column over G ∘ (t + ·)
   is the column over G shifted.  Self-contained; the core of the
   0-column result and a test of the whole approach.
2. 0-column identity for matrices, via `schutte_matrix_app`.
3. Merge lemma for equal adjacent heights.
4. Test the general "absorption = shift" conjecture on positive heights;
   otherwise port the Bachmann J/E argument.
5. Offset computation in both regimes; normalizer; correctness.

## Risks

- Constructivity.  Already at height 0 the propagation needs t' with
  α + t' ≈ t + α (ordinal subtraction), and "least index in a final
  segment" is a minimization.  Neither is obviously available on
  Brouwer trees without classical logic.  Option: state "is a shift of"
  relationally (every value of one function is a value of the other,
  and vice versa, order-preservingly), or with offsets only for
  notations, where they are computed.
- The low regime's compounding offsets need their own arithmetic.
- The general absorption conjecture may fail or need hypotheses; the
  fallback (porting the cover-based proof) is substantial.
