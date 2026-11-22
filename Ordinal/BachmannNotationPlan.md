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
with BIdx := BI : list (BIdx * BSmall) -> BIdx.              (* Ω^e₁·c₁ + … + Ω^eₙ·cₙ *)
```

- An index is an Ω-Cantor normal form. Its exponents `eᵢ` are indices
  and its coefficients `cᵢ` are small ordinals.
- Its denotation is a canonical `BOrd`: a left-nested `badd` of terms
  `bmul (bexpΩ ⟦eᵢ⟧) (embed ⟦cᵢ⟧)`.
- A small notation denotes `⟦BN T y⟧ = bach onePlus ⟦T⟧ ⟦y⟧`.

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
   `bphi onePlus bεΩ1 0`; `BachmannHoward` uses `powOmega`.
   Identifying them needs tree-level absorption of Ω + ε_{Ω+1}. State
   the bound with the onePlus base; treat the identification as an
   optional separate lemma.
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
5. Normalizer, fundamental sequences, interpolants, order type.

Each milestone ends in a commit.
