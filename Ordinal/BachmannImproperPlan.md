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
4. Normalizer for indices with normal exponents (merge + absorption,
   bottom-up on summands) and for `BS` terms; correctness.
5. Transfer to `SchutteMatrix`: extend `Kl_correct` to improper
   matrices and normalize via `Kinv`.
6. (Research) absorption inside exponents.
