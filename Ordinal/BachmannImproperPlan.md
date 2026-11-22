# Plan: normalizing improper index notations (and improper Schütte matrices)

Goal: a normalizer that accepts *improper* notations (index summands not
in strictly decreasing exponent order, zero coefficients) and returns the
normal form of the same ordinal.  Via the Klammersymbol embedding this
should also normalize improper `SchutteMatrix` matrices.

## Why the matrix case reduces to this one

- `ofold_rep` holds for column lists in any order, so an arbitrary
  (improper) Klammersymbol denotes `bach` on the corresponding (improper)
  index tree.
- `bsdirH` is preserved by `badd`, `bmul` (positive left factor) and
  `bexpΩ` unconditionally, so every index tree is directed and
  `bach = bphi` on all of them (`BNotation_ok` already covers improper
  terms).  So improper matrices *are* improper index notations.
- In the Ω^Ω fragment exponents are small notations (only their values
  matter), so absorption *inside exponents* never arises for matrices.

## Two kinds of improperness

1. **Equal adjacent exponents / zero coefficients: solved up to `bequiv`.**
   `BachmannFacts.v`: `bequiv_embed_add` (embed (a+b) ≈ embed a + embed b),
   `bequiv_bmul_badd` (P·(x+y) ≈ P·x + P·y), `bequiv_merge`
   (Ω^e·c + (Ω^e·c' + r) ≈ Ω^e·(c+c') + r); zero coefficients drop by
   `smartC_bequiv`.  These are index-level rewrites (`bphi_bequiv`).

2. **Increasing exponents (absorption): not an index-level rewrite.**
   For P = Ω^e·c and R normal with lead(R) > e, ⟦P+R⟧ and ⟦R⟧ give
   different hierarchies (e.g. φ_{c+Ω} enumerates the ε-numbers above c,
   φ_Ω all ε-numbers).  Expected theorem:

       Fix(P+R) = Fix(R) ∩ {z | coefficients of P < z (end ≤ z)}

   where Fix(T) = {z | bfix T z} is the range of φ_T.  Hence

       φ_{P+R}(y) = φ_R(t + y),   t = least x with φ_R(x) above the threshold,

   so the rewrite is `BN (P+R) y → BN R (t ⊕ y)`: it changes the argument,
   not just the index.

## Proof sketch for one absorption step (P nf term, R nf, lead R > e)

- (⊆) easy: K ⊑ P + K (`bsub_absorb`) and `bphi_mono_index`, plus
  dominance (`Kgs_ctx`, strict at non-end positions) for the threshold.
- (⊇) at z = a notation value with z ∈ Fix(R) above the threshold:
  comps of P fix z by `nest` (P ilt R, Klt z P).  For a component K of
  ⟦R⟧, sandwich it by a normal K' (`cover`); then P + K' is either again
  an absorption instance with smaller R-part (induction; N(P+K') = K'
  and K' ilt R), or has lead ≤ e and normalizes by merging to an index
  ilt R; in both cases `nest`/`zlt_nest` gives the fixpoint.  Family
  members are handled at the argument z itself (`bfix_member`).
- Converting "z ∈ Fix" into "z is a fixpoint of φ" (needed for small
  components) uses the offset lemma: if Fix(A) = Fix(B) ∩ (m,∞) and
  z > m is a fixpoint of φ_B with B ≥ Ω (so z is an ε-number, additively
  principal), then t < z, t + z = z and φ_A(z) = φ_B(t + z) = z.
  (Alternatively: φ_C(z) ≤ z ⟺ bfix (C+1) z.)
- The offset t is computable on normal forms by recursion on the
  threshold m: least x with φ_R(x) > m is 0 if φ_R(0) > m; if
  m = φ_{T'}(y') then: T' = R gives y'+1; T' > R and K(R) < m gives m+1
  (m is a fixpoint); T' < R reduces to max(y', kmax T').

## Open problem: absorption inside exponents

Ω^{c+Ω} vs Ω^Ω (and deeper contexts) are not related by `bequiv`, and
Fix-set equality above a threshold is extensional, so it does not by
itself pass through `bexpΩ` (whose components come from the exponent's
children).  This needs a structural, z-relative bisimulation ("`bequiv`
above m"), and it is the same obstacle as bounding improper notations
(additive closure of z-reachability under left addition).  Not needed
for Schütte matrices.

## Milestones

1. DONE: merge identities (`bequiv_embed_add`, `bequiv_bmul_badd`,
   `bequiv_merge`).
2. DONE. `cfe_offset` (`BachmannFacts.v`): if the common fixpoints of
   (f,F) are those of (f,G) in an upward-closed region U containing all
   values of the first enumerator, the fixpoints of (f,G) are additively
   principal, and t is least with φ_G(t) ∈ U and t < φ_G(t), then
   φ_F(y) = φ_G(t + y).  Helpers: `bphi_succ_le` (φ_T(a+1) is the least
   common fixpoint above φ_T(a)), `zlt_embed_Ω`.
   `BS_offset R m` (`Notation/BachmannNotation.v`), for normal R with a
   nonzero leading exponent (`lead_big`): `BS_offset_correct` gives
   `OffSpec` — t normal, m < φ_R(t), t < φ_R(t), and φ_R(t) lies below
   every common fixpoint of ⟦R⟧'s components above m.  Supporting facts:
   `fix_principal` (those fixpoints are additively principal),
   `fix_succ_lt`, `off_max_spec`.  Computed examples included.
   Axiom-free.
3. DONE: one-step absorption theorem (P = Ω^e·c normal term,
   R normal with leading exponent > e; section `absorb` in
   `Notation/BachmannNotation.v`).
   - DONE: `absorb_sub` (⊆: common fixpoints for P+R are common
     fixpoints for R), `absorb_region` (values of φ_{P+R} exceed P's
     coefficients, via `Kgs_ctx`), and `absorb_enum`:
     φ_{P+R}(y) = φ_R(t + y) for normal y, with t = `absorb_offset`
     (= `BS_offset R m`, m = P's largest coefficient).  `absorb_enum`
     takes the hard direction as the section hypothesis `ABS`:
     for a notation value z = φ_R(s), z ∈ Fix(R) and Klt z P imply
     z ∈ Fix(P+R).  The proof uses interpolants of y for the children,
     so it never needs ABS at non-notation points.
   - DONE (`ABS_all`, section `abs_all`): `absorb` is unconditional:
     φ_{P+R}(y) = φ_R(absorb_offset e c R + y) for normal y.  Helpers:
     `bfix_eq` (transport along ≈), `Kgs_lt`, `Kend_of_value` (φ_T(0) ≤ z
     gives Kend z T), `Klt_of_value`.  Axiom-free.  The proof followed
     the plan below:  First restate it
     for any notation value w (z = ⟦w⟧), transporting `bfix` along ≈.
     f and the components of P are handled by `nest` (P ilt R).  For a
     component K of ⟦R⟧, sandwich it by a normal K' (`cover`, at argument
     w for families); compare lead(K') with e:
       * lead(K') > e: absorption instance with smaller R-part.  For
         small K use `absorb_enum` for K' (IH) at argument w, plus
         t' < z (OffSpec), t' + z = z (`fix_principal`) and
         φ_{K'}(z) ≤ z; for families use ABS for K' directly.
       * lead(K') = e: merge (`bequiv_merge`, coefficient c ⊕ c₂ < z
         by principality), then as below.
       * lead(K') < e or K' = 0: N = Ω^e·c + K' is normal and ilt R.
         Small K: Klt z N, because K' has coefficients
         ≤ φ_{K'}(0) < φ_{K'}(z) ≤ z (dominance), so `nest` + `zlt_nest`
         apply.  Families: the argument z sits at the end of K', so only
         Kend z N holds; `nest_le` gives bleZ z ⟦N⟧ ⟦R⟧ but requires
         Klt z R, which fails when z equals R's end coefficient (e.g.
         R = Ω·k with φ_{Ω·k}(0) = k).  RESOLVED: `nest_le` now only
         requires Kend z of the target (`Klt_Kend`, `Kend_exp`,
         `Kend_coef`, `Kend_tail`); the target's coefficient bound was
         only used at its exponent, its coefficient (where an end
         coefficient ≈ 1 is impossible) and its nonempty tail.
         Remaining work for ABS is assembly along the plan above.
4. BLOCKED on theory: normalizer for indices with normal exponents.
   `absorb` only covers absorption at the top (P + R with R normal).
   A general improper sum needs absorption in non-top positions
   (exponents 1,2,3; Ω + (1 + Ω)), and that is not a tree identity:
   Ω + (1 + Ω) is not `bequiv` to Ω·2 (its family member Ω + (1+ξ)
   exceeds Ω + ξ at finite ξ), although they agree above a threshold.
   So the rest cannot be normalized before absorbing at the top.
   - Supported now: merges anywhere (`bequiv`) plus one lower head term
     over an otherwise normal index (`absorb`).  Too weak for matrices.
   - Needed: a hereditary absorption theorem for every improper X with
     normal exponents, Fix(X) = Fix(N(X)) ∩ {z above the absorbed
     coefficients}, hence φ_X(y) = φ_{N(X)}(t + y) (the offset still
     appears only at the top; checked by hand on Ω + (c + Ω)).
     Proof by one induction over all improper X.  The new difficulty
     is the direction Fix(X) ⊆ Fix(N(X)), trivial for P + R but not in
     general, since N(X)'s components are not contained in X's tree.
     Same nature as absorption inside exponents and as bounding
     improper notations; a solution likely settles all three.
5. Transfer to `SchutteMatrix`: extend `Kl_correct` to improper
   matrices and normalize via `Kinv`.
6. (Research) absorption inside exponents.

## Hereditary absorption: design (2026-11-22)

Goal: for every index notation X with positive coefficients and normal
exponents, with N(X) its ordinal normal form,
Fix(X) = Fix(N(X)) ∩ {z above the coefficients absorbed in X}, hence
φ_X(y) = φ_{N(X)}(t + y) (generalize `absorb_enum`: it only used ⊆,
the region lemma, ⊇ at notation values, principality and the offset).

N on summand lists: N(BIZ) = BIZ, N(BIC e c r) = addT e c (N r) with
addT e c A = A if lead(A) > e; Ω^e·(c ⊕ c₂) + r₂ if A = Ω^e·c₂ + r₂;
BIC e c A otherwise.  Ordinal addition is strictly monotone in its right
argument, so addT is strictly monotone in A (ilt); this replaces any
need for blt/ordinal arithmetic on trees.

Key idea, avoiding the circular "Fix(X) ⊆ Fix(N X)": characterize Fix by
the normal form alone (Bachmann's rule).  For a notation value z with
z above X's non-end coefficients (Kend-style), conjecture

  BachChar(X): bfix ⟦X⟧ z ⟺ f z ≤ z ∧
     (∀ T' nf, ilt T' (N X), Klt z T' → φ_{T'}(z) ≤ z) ∧
     (∀ T' nf, ilt T' (N X), Kend z T' → φ_{T'}(0) ≤ z).

The right side depends only on N(X), so Fix(X) and Fix(N X) agree on
such z.  Proof by induction on ⟦X⟧ (blt):
- (⇐): cover the components of ⟦X⟧ by (improper) notations K' with
  ilt (N K') (N X) (generalize `cover`; N(P + K) for a lower K is
  addT, strictly monotone).  Small components: by IH and the offset,
  φ_{K'}(z) = φ_{N K'}(t + z) ≤ φ_{N K'}(z) ≤ z (z principal, t < z).
  Families: IH gives z ∈ Fix(K') since BachChar(K') reduces to
  BachChar(X)'s clauses for T' < N K' < N X; then `bphi_le_fix`.
- (⇒): one-step cofinality: every nf T' < N(X) with Klt z T' satisfies
  T' ≤ N(K') (ilt or ieq) for some component K' of ⟦X⟧, a small child
  or a family member at an argument ξ ≤ z (members at ξ ≤ z are in
  Fix by `bfix_member` + `bfix_bsub` + monotone families).  Then IH on
  K' (z ∈ Fix(K') ⇒ z ∈ Fix(N K')) and `nest` (T' < N K') or the
  offset (T' ieq N K').  Cofinality itself needs an induction through
  exponents, like `nest`'s proof.
- Normal X is the special case N X = X (gives a Bachmann-rule
  characterization of Fix for normal indices, of independent interest).

Sub-milestones: (H1) DONE: `addT`, `normX`, `imp_ok`, `addT_nf`,
`addT_mono` (strict), `normX_nf`, `normX_id`, `ilt_irrefl`, `ilt_asym`,
`cmpIX_spec`; (H2) DONE: `coverX`
(components of an `imp_ok` index sandwiched by `imp_ok` notations K' with
ilt (normX K') (normX X)); (H3) cofinality; (H4) BachChar by induction;
(H5) generalized offset/enumeration theorem; (H6) BS normalizer
BN X y → BN (N X) (t ⊕ y) and correctness; then step 5 (matrices).
Absorption inside exponents stays out of scope (exponents normal).

### Refined plan for (⇒), i.e. Fix(X) ⊆ Fix(N X)

Induction on X = P + r (P = Ω^e·c), z ∈ Fix(X), T' nf, T' < N(X), Klt z T':
- N(X) = N(r) (absorbed): Fix(P + r) ⊆ Fix(r) (components of r sit
  below P + components, `bsub_absorb`, as in `absorb_sub`), then IH on
  r (a syntactic subterm: use induction on size for this direction).
- otherwise N(X) = addT e c (N r) has head exponent e; compare T'
  lexicographically:
  * T' < P (lower exponent, or exponent e with smaller coefficient):
    z ∈ Fix(⟦P⟧) because P's children are children of P + r, then
    `nest` for the normal P.
  * T' = Ω^e·c + T'' with T'' < N(r) (or the merged analogue):
    one-step cofinality in r gives a component K of ⟦r⟧ (small, or a
    family member at an argument ≤ z, which lies in Fix by
    `bfix_member`/`bfix_bsub`) with T'' ≤ N(K'), K' its cover.  P + K
    is a component of X, so φ_{P+K} fixes z; by IH (P + K' is
    blt-smaller) z ∈ Fix(N(P + K')), and with the offset
    φ_{N(P+K')}(z) ≤ z; then P + T'' ≤ N(P + K') (`addT_mono`), and
    `nest` or equality finishes.
- (H3) one-step cofinality: for normal N (= N(r)) and nf T'' < N with
  Klt z T'', some component of ⟦r⟧ has a cover K' with T'' ≤ N(K').
  By recursion on r = P' + r' as for N: absorbed tail → recurse into r'
  (addT e' c' A ≥ A); otherwise lexicographic cases, descending into
  the exponent e' for lower exponents (families Ω^{e'_a}·ξ, ξ ≤ z),
  as in `nest`'s proof.  Needs a lemma `addT_ge`: A ≤ addT e c A.

### Further refinement (after H1/H2)

- (⇒) is better done structurally: `nestX`: for imp_ok X, nf T' with
  Klt z T' and ilt T' (normX X), zlt z ⟦T'⟧ ⟦X⟧, for any infinite z.
  Cases: absorbed head → IH on the rest plus `bsub_absorb` (zlt_mono_r);
  T' below P → `nest` for P, then ⟦P⟧ ⊑ ⟦X⟧; prepend/merge tail cases
  → IH on the rest and `zlt_shift`, with `bequiv_merge`.  For a merged
  coefficient c ≤ c₁ < c + c₂ pick a notation d < c₂ with c₁ ≤ c + d
  (d = c₁ if c₁ < c₂, otherwise from the interpolants of c₂ via
  `addOrd_lt_cases`).  Then zlt_nest gives the Klt-clause of BachChar
  at every z ∈ Fix(X).
- BachChar needs only the Klt-clause: family members at z can be
  reached by continuity of the (normal) diagonal, approximating z from
  below by notations x < z (interpolants of z), whose members have all
  coefficients < z.
- New circularity: the enumeration step (generalized `absorb_enum`)
  needs "z ∈ Fix(N X)" at z = φ_X(y), the value of an improper
  notation.  From nestX we get the Klt-clause there, but turning it
  into bfix ⟦N X⟧ z needs the families at z, i.e. interpolants of z,
  which are only known for normal notation values.  Small components
  of the induction (φ_{K'}(z) ≤ z) also need the enumeration for K'.
  Likely resolution: one simultaneous induction on ordinal value v
  proving, for all improper terms with value < v, the enumeration
  identity and interpolants (with witnesses from the induction).  To be
  designed before H3–H6 are implemented.

## Design pass: breaking the circularity (2026-11-22)

Target (core case; coefficients, arguments and exponents normalized
bottom-up first, exponents required normal-shaped):
  E(X): for imp_ok X with nf coefficients and every nf y,
        φ_X(y) ≈ φ_{N X}(t_X + y),
so φ_X(y) is (≈) the normal notation normS (BN (N X) (t_X ⊕ y)).

E(X) splits as in `absorb_enum`:
  (≤) φ_X(y) ≤ φ_N(t + y): cfe_least on X at the target v = φ_N(t+y),
      which IS a normal notation value.  Needs v ∈ Fix(X), i.e. the (⇐)
      direction of BachChar at notation values only.  Interpolants of v
      are available (v normal), so the continuity argument for family
      members and `coverX` both work.  No circularity here.
  (≥) φ_N(t + y) ≤ φ_X(y) =: z'.  This is where the circularity was
      (z' ∈ Fix(N) would need interpolants of z').

Resolution for (≥): avoid z' ∈ Fix(N) entirely.  Since v = φ_N(t+y)
has interpolants (normal), it suffices to show

  (LB) every nf notation n with ⟦n⟧ < φ_N(t + y) satisfies ⟦n⟧ < z',

by induction on the size of n (and the outer induction on y via
interpolants of y, as in `absorb_enum`).  For n = φ_{T''}(y''):
- T'' ≡ N: y'' < t + y.  If y'' < t then φ_N(y'') ≤ m (minimality of t;
  decidable comparison of notations) and m < z' (region: X's values
  exceed its absorbed coefficients, `Kgs_lt`).  Otherwise
  `addOrd_lt_cases` gives y'' ≤ t + y_j, and the outer IH gives
  φ_N(t + y_j) ≈ φ_X(y_j) < φ_X(y).
- T'' < N: y'' and the coefficients of T'' are smaller notations below
  ⟦n⟧ < φ_N(t+y), so by the inner IH they are < z'; hence Klt z' T''.
  `nestX` (structural, valid at every z') gives zlt z' ⟦T''⟧ ⟦X⟧, and
  z' ∈ Fix(X), so φ_{T''}(z') ≤ z' and ⟦n⟧ < φ_{T''}(z') ≤ z'.
- T'' > N: if Klt ⟦n⟧ N then n is a fixpoint of φ_N (as in
  `fix_test_correct`), so n = φ_N(n) and we are in the first case with
  y'' := n.  Otherwise n ≤ some coefficient k of N.  If k is not N's end
  coefficient, k < z' (region for non-end coefficients, after merging:
  sums of non-end coefficients of X, z' principal).  DELICATE: if k is
  N's end coefficient k_end and n ≈ k_end, we must still show n < z'
  (i.e. exclude φ_X(y) = k_end < φ_N(t+y)).  Candidate argument: then
  n ≈ k_end ≤ φ_N(0), so φ_N(0) collapses onto k_end or exceeds it;
  compare with `coll_test`'s end-position criterion and show the same
  collapse happens for X (X's end coefficient sits at the end of X).
  This sub-case must be settled before implementation.

So the plan is: BachChar (⇐) only at normal notation values (via
coverX, continuity for families, induction on ⟦X⟧ by blt, using E for
the smaller components K' to get φ_{K'}(z) ≤ z by the offset), and
(≥) via (LB) with the structural `nestX`.  Interpolants are only ever
needed for normal notation values, which we have.

Remaining risks, in order: (1) the end-coefficient collapse sub-case of
(LB); (2) small components in (⇐) need E for K' at the argument z,
fine by IH since K' is blt-smaller, but the threshold of K' must lie
below z (its absorbed coefficients come from X's coefficients and
approximations, all < z); (3) `nestX`'s merged-coefficient case
(choice of d, worked out above).

Implementation order: H3 = nestX; H4 = BachChar (⇐) at notation values;
H5 = offset/minimality for N X with threshold m_X (reuse `BS_offset`);
H6 = E(X) by (≤) and (LB); H7 = BS normalizer and correctness.

## Risks worked out (2026-11-22)

### Risk 1 (end-coefficient case of LB): avoided by dropping (LB)

Better route for (≥): prove that z' := φ_X(y) HAS INTERPOLANTS inside the
induction, then show z' ∈ Fix(N X) directly and finish as in
`absorb_enum`.  Interpolants of z' (every i < z' lies in [i, z') for a
normal notation n) come from the `interp_aux` argument run on X:
- `bphi_interp`: i < 1 + y, or i < a word in f and the components of
  ⟦X⟧ applied to 0 or to succ φ_X(y_j);
- start: y_j ≤ n_j < y (interpolants of y), and φ_X(n_j) is a normal
  notation value by E(X) at n_j (inner induction on y); BS_succ;
- small component C ⊑ ⟦K'⟧ ⊑ C' (`coverX`): φ_C(m) ≤ φ_{K'}(m) =
  φ_{N K'}(t' + m) (E for K', the outer IH, since K' is blt-smaller),
  a normal notation value, and ≤ φ_{C'}(z') ≤ z';
- family component: likewise with E(K'_m) at argument 0;
- f: `BS_onePlus`.
Every chain value is ≤ z' and is a normal notation value, so it has
interpolants and supplies witnesses strictly below z'.  With
interpolants of z', z' ∈ Fix(N X) follows from:
- small components of ⟦N X⟧ (cover of the normal N X): K' < N X, with
  Klt z' K', so `nestX` + zlt_nest (z' ∈ Fix(X)) gives φ_{K'}(z') ≤ z';
- families at z': continuity of the normal diagonal, approximating z'
  by notations x < z', whose members' covers have all coefficients
  < z' (same argument).
For Klt z' K' we need Kend z' (N X): the non-end coefficients of N X are
< z' and its end coefficient is ≤ z'.  Position lemma (see below):
every coefficient of N X is a sum of coefficients of X, and a non-end
one involves a non-end X-coefficient (strictly below z' by `Kgs_lt`)
or is a merged sum c + c'' with c'' > 0.  Since z' is principal,
sums stay below z'.  So the end-coefficient collapse never has to be
excluded: only ≤ is needed at the end, and approximations of the end
coefficient are strictly below it.

### Risk 2 (small components in (⇐)): fine, with coefficient tracking

For z a normal notation value with f z ≤ z, Kend z X and the Klt-clause
(φ_{T'}(z) ≤ z for nf T' < N X with Klt z T'):
- `coverX` must also track coefficients: small covers K' satisfy
  Klt z K', and family covers at x ≤ z satisfy Kend z K', whenever
  Kend z X (P kept only at non-end positions, approximations strictly
  below a coefficient, the argument x at the end).  Extend `coverX`'s
  statement accordingly.
- Klt z K' and z principal give Klt z (N K') (merged sums).
- z ∈ Fix(N K') by the clause (N K' < N X) and `bfix_of_fix`; hence by
  the offset's minimality φ_{N K'}(t') ≤ z, and t' < z.
- E(K') (outer IH) at the argument z: φ_{K'}(z) = φ_{N K'}(t' + z)
  ≤ φ_{N K'}(z) ≤ z, using t' + z = z (z principal, `fix_principal`).
- Families: approximate z from below by notations x < z (z normal has
  interpolants) and use continuity of the diagonal; each member's cover
  K'_x has Klt z K'_x, and z ∈ Fix(K'_x) by the IH (⇐) for K'_x, whose
  clause is inherited (T' < N K'_x < N X).
So H4 (⇐) and H6 (E) form ONE induction on ⟦X⟧ (blt), with an inner
induction on y for E.

### Risk 3 (nestX merged coefficients): settled

Cases for N X = addT e c (N r):
- absorbed: IH on r, then ⟦r⟧ ⊑ ⟦X⟧ (`bsub_absorb`, `zlt_mono_r`);
- T' = BIZ: zlt via bpos;
- T' below P (lower exponent, or coefficient c₁ < c): `nest` for the
  normal P, then ⟦P⟧ ⊑ ⟦X⟧;
- prepend, tail (c₁ ≈ c, T'' < N r): IH on r, `zlt_shift`, ieq/bsub to
  rewrite the head;
- merged, c ≤ c₁ < c + c₂: choose nf d < c₂ with c₁ ≤ c + d and d < z
  (d := c₁ if c₁ < c₂, else an interpolant of c₂ above the child given
  by `addOrd_lt_cases`; decide with `BS_compare`).  Then
  D' := smartC e d T'' < N r, IH, shift, and ⟦T'⟧ ⊑ Pt + ⟦D'⟧ via
  `bequiv_merge`/`smartC_bequiv`;
- merged, tail (c₁ ≈ c + c₂, T'' < r₂): D' := BIC e₂ c₂ T'', same.

### Position lemmas needed (new, tedious but elementary)

(P1) Kgs k X with k not absorbed ⇒ k is strictly below some coefficient
of N X at a non-end position, or below a merged end coefficient
c + c'' (c'' > 0); absorbed k ≤ m_X.  Used for Kend v X at
v = φ_{N X}(t + y) in (≤).
(P2) every coefficient of N X at a non-end position is a sum of
X-coefficients including a non-end one; its end coefficient is a sum
of X-coefficients.  Used for Kend z' (N X) in (≥).
Both by induction on X along `addT`; the merged coefficient's exponent
positions are non-end because c + c'' > 1.

### Revised implementation order

H3 nestX; H3' coverX with coefficient tracking; P1/P2;
H4+H6 joint induction (⇐ at normal values; E with interpolants of z');
H5 offset for N X with threshold m_X (reuse `BS_offset`, `absorb_max`
generalized to absorbed coefficients); H7 BS normalizer.
