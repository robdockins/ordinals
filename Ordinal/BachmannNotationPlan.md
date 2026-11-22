# Plan: a notation system up to the Bachmann–Howard ordinal

Goal: a syntactic notation system whose terms denote ordinals via
`bach onePlus`, with the same properties as the existing notation
systems (`CantorNotation`, `SchutteMatrix`, …): order testing, Cantor
decompositions (hence arithmetic), and interpolants, plus an embedding
of Schütte's Klammersymbols (`SchutteMatrix.VForm`).

Files:

- `Ordinal/BachmannFacts.v`: semantic prerequisites (Phase 0).
- `Ordinal/Notation/BachmannNotation.v`: the notation system.

## Design

**Syntax.** Two mutually nested sorts:

```coq
Inductive BSmall := BZ | BN : BIdx -> BSmall -> BSmall      (* φ_T(y) *)
with BIdx := BIZ | BIC : BIdx -> BSmall -> BIdx -> BIdx.    (* Ω^e·c + r *)
```

- An index is an Ω-Cantor normal form. Its exponents are indices and
  its coefficients are small ordinals. (Originally a list of pairs; the
  single-summand constructor avoids nested list fixpoints.)
- Its denotation is a canonical `BOrd`, right-nested:
  `⟦Ω^e·c + r⟧ = badd (bmul (bexpΩ ⟦e⟧) (embed ⟦c⟧)) ⟦r⟧`.
- A small notation denotes `⟦BN T y⟧ = bphi (addOrd 1) ⟦T⟧ ⟦y⟧`, which
  agrees with `bach (addOrd 1) ⟦T⟧ ⟦y⟧` (`BS_denote_bach`); `bach`'s own
  values are not known to be complete trees.

**What the existing development gives for free.** Index denotations
are built only from `embed` of complete values, `badd`, `bmul` and
`bexpΩ`, so they satisfy `bcd` and `bsdirH` by the existing
preservation lemmas. Then `bach_bphi_canon` gives
`⟦BN T y⟧ ≈ bphi onePlus ⟦T⟧ ⟦y⟧`, normal in `y`, and every denotation
is complete.

**Why the onePlus base.** `bphi onePlus (embed α) y ≈ ω^α + y`, so
additive (Cantor) structure is built into the notation, as in `VF`.
Values with an Ω-part in the index are ε-numbers and decompose to
themselves, the convention `VF_decompose` uses.

## Phases

**Phase 0: semantic prerequisites** (`BachmannFacts.v`)

- (a) onePlus calibration: `bphi onePlus (embed α) y ≈ ω^α + y`.
- (b) Successor step: the fixpoints of φ_T are exactly the range of
  φ_{T+1} (from `bach_veblen_step` with ξ = 1).
- (c) General nesting theorem: for normal indices T < T', φ_T fixes
  every value of φ_{T'} that exceeds T's coefficients. Generalizes
  `tower_rel`/`bleZ_nest` by induction on the syntactic comparison;
  exponents via `bslt_bexpΩ`, coefficients via `bslt_bmul_r`/`embed`,
  large-vs-small coefficient cases via the z-relative `bleZ`.
- (d) Absorption by domination: if every component of A is dominated by
  a component of B, then φ_{A+B} ≈ φ_B (start from `BRep_extend`).
- (e) Interpolation for `cfe`/`bphi`: every i < φ_T(y) lies below an
  iterate of finitely many components applied to earlier values
  (counterpart of `schutte_matrix_interpolants_aux`).

**Phase 1: syntax and denotation.** Hand-written induction principles
and size measures for the nested inductives; completeness, `bcd`,
`bsdirH` and normality of denotations.

**Phase 2: normal forms.** An index is normal when its exponents
strictly decrease, its coefficients are nonzero and normal, and its
subterms are normal. φ_T(y) is normal when

- every small coefficient occurring in T (Buchholz-style K-set) is
  < φ_T(y), and
- y is not a fixpoint of φ_T (not of the form φ_{T'}(y') with T' > T
  and K(T) < y).

Both conditions decidable; uniqueness of normal forms.

**Phase 3: order testing.** Mutually recursive comparison of indices
(lexicographic on the Ω-CNF) and small notations: if T = T' compare y
with y'; if T < T' compare y and K(T) against φ_{T'}(y'); symmetric
otherwise. Termination by combined size, as in `VF_compare_loop`;
correctness from 0(b) and 0(c).

**Phase 4: Cantor decomposition.** `BN ∅ y` is `1 + y`;
`BN (Ω^0·α) y` decomposes as α followed by the decomposition of y;
anything with an Ω-part decomposes to itself. Arithmetic (`succ`,
`add`, `mul`, `exp`, `nadd`, `nmul`) then comes from the generic
machinery.

**Phase 5: interpolants.** Syntactic fundamental sequences `T[ξ]`
matching `bbigSz` of the denotation up to `bsub` both ways; a
normalizer; with 0(e), `has_all_interpolants`. Bound every notation
below the Bachmann–Howard ordinal; order type of normal forms;
`has_enough_notations` under EM.

**Phase 6: Klammersymbol embedding.** `N [(β₁,α₁),…]` maps to
`BN (Ω^{ζ₁}·α₁ + …) y` with `1+ζᵢ = βᵢ`; the height-0 column becomes
the argument `y`. Main theorem `VF_denote x ≈ ⟦K x⟧`, by induction
over columns from `bach_zero_rep` with one `bach_bexpΩ_rep` step per
column (exactly one step of `schutte_matrix`).

## Difficulties

1. **An argument slot is needed.** `bach onePlus T 0` gives only
   principal values, and the argument cannot be folded into the index
   (`bach f (T + ξ) 0 = veblen G ξ 0`, not `G ξ`). So `BN T y` denotes
   `bach onePlus ⟦T⟧ ⟦y⟧`; `bach onePlus x 0` is the case y = 0.
2. **φ depends on the tree, not the order type of the index.** Every
   syntactic identification (merging equal exponents, absorbing a
   smaller summand, fundamental sequences) must be justified by `bsub`
   both ways or by domination (0(d)). Some need new tree-arithmetic
   lemmas, e.g. distributivity of `bmul` over `badd` up to `bsub`.
3. **The nesting theorem 0(c) is the main mathematical risk.** It holds
   only under coefficient bounds and must be z-relative throughout,
   like `tower_rel`.
4. **Base change.** The notations are bounded by
   `bphi onePlus bεΩ1 0`; `BachmannHoward` uses `powOmega`. (Resolved
   in 5e by comparing hierarchies, without tree-level absorption.)
5. **Interpolants need a normalizer and syntactic fundamental
   sequences.** Coefficient merging needs a direct syntactic small
   addition (not via the Cantor decomposition, which would be circular).
6. **Coefficient sets and termination** of the comparison, as with
   `active_subterm` in `SchutteMatrix`.
7. **Klammersymbol bookkeeping.** `1+ζ = β` needs "predecessor if
   finite, else itself" on `VF`; `VF` normal forms may not map onto
   ours, so the safe target is equality of denotations.
8. **Mutual nested inductives**: induction principles, decidable
   equality, sizes. Boilerplate only.

## Milestones

1. Syntax, denotation, normality, and the Klammersymbol embedding
   (Phases 1 and 6).
2. Phase 0(c) for the `Ω^Ω` fragment, with comparison and normal forms
   there; reproduce the LVO result as a sanity check.
3. Full indices: comparison and normal forms up to ε_{Ω+1}.
4. Cantor decomposition and arithmetic.
5. Split into:
   - 5a. Upper bound: every normal notation lies below
     BHO₁ := `bphi (addOrd 1) bεΩ1 0` (height lemma via part (B) of
     `nest`, then `zlt_value` at the ε_{Ω+1} node).
   - 5b. Normalizer (highest risk): small-level collapse of fixpoint
     arguments and coefficient repair; index-level merging and
     absorption, justified by `bequiv` or domination (needs e.g.
     distributivity of `bmul` over `badd` up to `bequiv`, and 0(d)).
   - 5c. DONE. Syntactic fundamental sequences and interpolation.
     Semantic half (`BachmannFacts.v`): `cfe_interp`/`bphi_interp`;
     everything below φ_T(u) lies below 1+u, or below a finite word in
     f and the components applied to 0 or to succ φ_T(u_j). Syntactic
     half: `cover` gives, for every small child and every Ω-family
     member at a notation argument of ⟦T⟧, a normal index T' (with
     T' < T) sandwiched up to `bsub` between that child and another
     child of the same kind. This replaces exact `T[ξ]` matching:
     children of Ω^e·c involve arbitrary ordinals γ < c, which are
     approximated by notations from the coefficient's interpolants.
     Then `interp_aux` (induction on `blt` of the index tree, then on
     the argument) gives `BS_has_all_interpolants` and, under EM,
     `BS_has_enough_notations`. Axiom-free.
   - 5d. DONE. `BS_order_type : NFOrd ≈ BHO₁` (the limit of the
     normal forms is a common fixpoint of 1+x and the components
     φ_{tower n} of ε_{Ω+1}, each bounded via `bsub_tower` by φ of a
     notation index `BI_tower n` = Ω+1, Ω^(Ω+1), …; then `cfe_least`),
     and `BS_nmul_reflects` (natural product from `CantorProduct` and
     the interpolants). Axiom-free.
   - 5e. DONE. `BHO1_BachmannHoward : BHO₁ ≈ BachmannHoward`, hence
     `BS_order_type_BH`. No tree-level absorption needed: a comparison
     lemma for enumerators (`cfe_dom`) gives φ^{1+x}_T ≤ φ^{ω^x}_T
     (`bphi_base_mono`) and φ^{ω^x}_T ≤ φ^{1+x}_{Ω+T}
     (`bphi_powOmega_shift`); Ω + tower n is z-reachably below
     tower (n+2) (`zlt_Ω_tower`), so BHO₁ is closed under the ω^x
     hierarchy's components and `cfe_least` applies. Axiom-free.

## Follow-up items

- **Bounding improper notations.** Show every term, proper or not,
  denotes an ordinal below BHO₁ (analogue of `VForm_bounded` /
  `VF_LVO`), e.g. `ord BSmall BS_denote ≈ BHO1`; this would also let the
  normalizer accept improper input. `SchutteMatrix`'s trick (one proper
  column at the maximum height dominates any matrix,
  `matrix_E_unreachable`) does not transfer: φ is monotone only in
  `bsub`, and improper index shapes (e.g. Ω^0·c + Ω) are not
  `bsub`-below proper ones. Likely route: prove semantically that BHO₁
  is a common fixpoint of the components of every index tree with
  coefficients below it. The missing lemma is additive closure of the
  tower levels in the reachability order (if t and r are z-reachably
  below Ω^{tower n}, so is t + r), which runs into left addition not
  preserving reachability. Not needed for 5c/5d.

Each milestone ends in a commit.
