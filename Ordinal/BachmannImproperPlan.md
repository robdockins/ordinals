# Plan: normalizing improper index notations (and improper Schütte matrices)

Goal: a normalizer accepting *improper* notations (index summands not in
strictly decreasing exponent order, zero coefficients) and returning the
normal form of the same ordinal.  Via the Klammersymbol embedding this
should also normalize improper `SchutteMatrix` matrices (a long-standing
annoyance: no method was found there).

Files: `Ordinal/BachmannFacts.v` (tree-level facts),
`Ordinal/Notation/BachmannNotation.v` (everything notation-level; the
improper-index work is appended at the end of the file, in the order
listed under "Done").  Branch `bachmann`.  Workflow used so far: develop
in a scratch file `Ordinal/Notation/BXxxScratch.v` compiled with
`rocq c -R Ordinal Ordinal <file>`, then append to the target file,
delete the scratch, `make -j4`, commit (one commit per milestone).

## Status (2026-11-22)

DONE: merge identities; offset algorithm; one-step absorption at the top
(`absorb`, unconditional); `nest_le` generalized; H1 (normal forms of
improper sums); H2 (`coverX`); H3 `nestX`; H3' (coefficient tracking
in `cover`/`coverX`, `Klt_normX`).  DESIGN COMPLETE (on paper) for
hereditary absorption; (C) P1/P2 and (F) bookkeeping DONE; (D)+(E) DONE:
`hereditary_absorption` (closed under the global context, no axioms).
(G) normalizer DONE (`normSX`, `normalizeX_correct`).  NEXT: Schütte
matrices (extend `Kl_correct` to improper matrices, normalize via `Kinv`).
Out of scope: absorption inside exponents (exponents must be normal).

## Background facts

- Improper matrices = improper indices: `ofold_rep` holds for column
  lists in any order, and `bsdirH` is preserved by `badd`/`bmul`/`bexpΩ`
  unconditionally, so `bach = bphi` on every index tree
  (`BNotation_ok` covers improper terms).  Below Ω^Ω exponents are small
  notations, so matrices need only absorption at sum level, never
  inside exponents.
- Equal exponents / zero coefficients normalize up to `bequiv` (index
  rewrite).  Increasing exponents (absorption) do NOT: e.g. φ_{c+Ω}
  enumerates the ε-numbers above c; Ω + (1+Ω) is not `bequiv` to Ω·2.
  Absorption shifts the argument: φ_{P+R}(y) = φ_R(t + y).
- Notation: Fix(T) = {z | bfix (addOrd 1) ⟦T⟧ z} (common fixpoints of
  f = 1+x and the components; the range of φ_T when T has components).
  `PHI T` abbreviates `bphi (addOrd 1) (BI_denote T)`.

## Done (names to reuse)

`BachmannFacts.v`:
- merges: `bequiv_embed_add`, `bequiv_bmul_badd`, `bequiv_merge`
  (Ω^e·c + (Ω^e·c' + r) ≈ Ω^e·(c+c') + r), helpers `bsub_badd_intro`,
  `bsub_bmul_intro`, `bmul_small_cases`, `bmul_big_cases`;
- `cfe_offset` (shifted enumeration: Fix(F) = Fix(G) ∩ U, U upward
  closed and containing F's values, G's fixpoints additively principal,
  t least with φ_G(t) ∈ U and t < φ_G(t) ⇒ φ_F(y) = φ_G(t + y));
  `bphi_succ_le`, `addOrd_lt_cases`, `bsmall_mul_embed_inh`,
  `zlt_embed_Ω`; `cfe_interp`/`bphi_interp` (interpolation of cfe:
  i < f y or below a word of components on 0 / succ of earlier value).

`Notation/BachmannNotation.v`:
- interpolants: `HI`, `KHI`, `cover`/`icov` (normal covers of the
  components of a normal index), `interp_aux`, `notation_KHI`,
  `BS_has_all_interpolants`;
- offset: `BS_offset R m` (least t with m < φ_R(t)), `OffSpec`,
  `BS_offset_correct` (needs `lead_big R`: nonzero leading exponent),
  `fix_principal` (fixpoints for such R are additively principal),
  `fix_succ_lt`, `off_max_spec`;
- one-step absorption (section `absorb`; P = Ω^e·c normal term, R
  normal, `lead_gt R e`): `absorb_sub` (⊆), `absorb_region`,
  `absorb_max`, `absorb_offset`, `absorb_enum`; section `abs_all`:
  `ABSw`, `ABSw_ABS`, `ABS_all` (⊇ by blt-induction on ⟦R⟧ with cover
  and cases lead(K') <,=,> e), `absorb` (unconditional:
  PHI (BIC e c R) y ≈ PHI R (absorb_offset e c R + y));
  helpers `bfix_eq`, `Kgs_lt`, `Kend_of`, `Kend_of_value`,
  `Klt_of_value`;
- `nest_le` now needs only `Kend z` of the target (`Klt_Kend`,
  `Kend_exp`, `Kend_coef`, `Kend_tail`);
- H1: `addT e c A` (put Ω^e·c in front of a normal A: absorbed if
  lead A > e, merged if equal, prepended otherwise), `normX` (right to
  left), `imp_ok` (normal exponents, positive normal coefficients),
  `addT_nf`, `addT_mono` (strict in A), `normX_nf`, `normX_id`,
  `ilt_irrefl`, `ilt_asym`, `ilt_ieq_false`, `cmpIX`, `cmpIX_spec`,
  `cmpIX_total`, `addT_lt/eq/gt`;
- H2: `icovX`, `coverX`: components of an imp_ok index are sandwiched
  (bsub both ways) between imp_ok notations K' with
  ilt (normX K') (normX X); P's children reuse `cover`;
- H3: `nestX` (oinf z, imp_ok X, nf T', Klt z T', ilt T' (normX X) ⇒
  zlt z ⟦T'⟧ ⟦X⟧), helpers `Klt_smartC`, `ilt_lead`, `merge_bsub`;
- H3': `icov` and `icovX` now carry tracking: a small cover T satisfies
  ∀ z, oinf z → Kend z T0 → Klt z T; a family cover at x satisfies
  ∀ z, oinf z → Kend z T0 → ⟦x⟧ < z → Klt z T (strict in x, which is all
  (D)/(E) need: family arguments are interpolants below z).  Helpers
  `Kend_rest`, `Kend_head`, `Klt_smartC_coef`, `ilt_ne`, `oinf_one`,
  `normX_ne`; `Klt_addT`, `Klt_normX` (z with a < z → a + z ≤ z);
- (C)/(F), simpler than the paper design (plain structural inductions
  along addT, no "sum of coefficients" reasoning):
  `Kend_normX` (P2: oinf z, z principal, Kend z X ⇒ Kend z (normX X)),
  `AbsLt v X` (absorbed terms have all coefficients < v), `Kend_back`
  (P1: oinf z, AbsLt z X, Kend z (normX X) ⇒ Kend z X),
  `Kend_ofX`/`Kend_of_valueX` (PHI X 0 ≤ z ⇒ Kend z X for imp_ok X),
  `imp_ok_pos`, `normX_BIZ`; bookkeeping `absb`, `absX`/`absM` (largest
  absorbed coefficient, via kmax/omax), `absM_spec` (nf, Kgs m X, and
  m < v ⇒ AbsLt v X; None ⇒ AbsLt v X for all v), `offX X` (BZ or
  BS_offset (normX X) m), `absM_lead_big` (needed by BS_offset_correct);
- (D)+(E), as actually proved (simpler than the paper design below):
  `shift_enum` (section `shift`: `absorb_enum` abstracted over a region
  U, an offset t and hypotheses Hsub/Hreg/Hup/Hleast/Hprin/ABS);
  `bsub_normX` (⟦normX X⟧ ⊑ ⟦X⟧, so Fix(X) ⊆ Fix(normX X) by
  `bfix_bsub` and no interpolants of improper values are needed);
  `bequiv_normX` (nothing absorbed ⇒ ⟦normX X⟧ ≈ ⟦X⟧), `merge_bequiv`;
  `ClX`, `JX` (⇐ at notation values w: Kend, z principal, ClX ⇒
  bfix), `EX`; `EX_of_JX` (None: bphi_bequiv; Some m: shift_enum with
  U z := m < z, ABS via JX at w := normS (BN N s), Kend_back, nest);
  `JE_all` (blt-induction: small children via coverX + E of the cover at
  z + offset minimality + principality; family children at the notation
  w itself via coverX + J of the cover + bphi_le_fix);
  `hereditary_absorption`: imp_ok X ⇒ PHI X y ≈ PHI (normX X) (offX X + y).
  Family tracking in `icov`/`icovX` was switched to the Kend form
  (⟦x⟧ ≤ z ⇒ Kend z T) for this; helpers `Kend_cons`,
  `Kend_smartC_coef`, `Kend_smartC_end`, `imp_ok_KHI`, `Kgs_Kge`,
  `omax_some_l/r`, `kmax_some`.  `nestX` turned out not to be needed.
- (G): accepted inputs `BS_okX`/`BI_okX`/`BI_okE` (top-level index sums
  improper, zero coefficients allowed; exponents of proper term
  structure; coefficients/arguments recursively accepted inputs, by
  value); `normSX`/`normTX`/`normEX` (BN T y ↦ smartN (normX X)
  (offX X ⊕ y'), X = normTX T, zero terms dropped by smartC);
  `normalizeX_correct` (nf + same value; normTX: imp_ok + bequiv;
  normEX: nf + ieq), `normSX_nf`, `normSX_equal`, `offX_nf`,
  `proper_okX` (proper notations are accepted); examples
  `normSX_Γ0_Ω` (Γ₀+Ω ↦ φ_Ω(1)), `normSX_Γ0_Ω_Ω2`, `normSX_Ω_Γ0_Ω`.

## Final design: hereditary absorption (historical; see Done for what was proved)

Target theorem E(X): for imp_ok X and every nf y,
  PHI X ⟦y⟧ ≈ PHI (normX X) (⟦t_X⟧ + ⟦y⟧),
where t_X = `BS_offset (normX X) m_X` and m_X = the largest *absorbed*
coefficient of X (coefficients of summands dropped by normX; t_X = 0
when nothing is absorbed).  Then BN X y normalizes to
normS (BN (normX X) (t_X ⊕ y)).  (Coefficients, arguments and exponent
coefficients are normalized bottom-up first; only values matter for
coefficients, `bequiv_embed`.)

Bachmann-rule clause for X at z:
  Cl(X,z) := f z ≤ z ∧ ∀ T' nf, ilt T' (normX X) → Klt z T' → PHI T' z ≤ z.

Ingredients:

(A) `nestX` (H3, structural, any infinite z): for imp_ok X, nf T' with
    Klt z T' and ilt T' (normX X): zlt z ⟦T'⟧ ⟦X⟧.  Hence z ∈ Fix(X)
    implies the clause.  Induction on X = BIC e c r along
    normX X = addT e c (normX r):
    - absorbed (lead normX r > e): IH on r, then ⟦r⟧ ⊑ ⟦X⟧
      (`bsub_absorb`, `zlt_mono_r`);
    - T' = BIZ: `zlt_bslt` with bpos;
    - T' below P (lower exponent, or exponent ≈ e and coefficient < c):
      `nest` for the normal P = BIC e c BIZ, then ⟦P⟧ ⊑ ⟦X⟧;
    - prepend, tail (T' = Ω^e₁·c₁ + T'', e₁ ≈ e, c₁ ≈ c, T'' < normX r):
      IH on r, `zlt_shift` by Pt = bmul (bexpΩ ⟦e⟧) (embed ⟦c⟧), and
      ⟦T'⟧ ⊑ Pt + ⟦T''⟧ (ieq_bequiv, bsub_embed);
    - merged (normX r = BIC e₂ c₂ r₂, e₂ ≈ e, normX X = BIC e (c⊕c₂) r₂):
      coefficient case c ≤ c₁ < c + c₂: pick nf d < c₂ with c₁ ≤ c + d
      and d < z (d := c₁ if c₁ < c₂, decided by `BS_compare`; otherwise
      `addOrd_lt_cases` gives c₁ ≤ c + c₂ j and an interpolant d of c₂
      above c₂ j, with d < c₂ ≤ c₁ < z); D' := smartC e d T'' < normX r,
      IH, shift, ⟦T'⟧ ⊑ Pt + ⟦D'⟧ via `bequiv_merge`/`smartC_bequiv`;
      tail case c₁ ≈ c + c₂, T'' < r₂: D' := BIC e₂ c₂ T'', same.

(B) `coverX` with coefficient tracking (H3'): add to `icovX`: small
    covers satisfy (∀ z, Kend z X → Klt z K'); family covers at x satisfy
    (∀ z, Kend z X → ⟦x⟧ ≤ z → Kend z K').  (P's coefficients are kept
    only at non-end positions; approximations are strictly below a
    coefficient; the argument x sits at the end.)  Plus: Klt z K' and z
    principal ⇒ Klt z (normX K') (merged sums stay below z).

(C) Position lemmas (P1/P2), by induction along `addT`:
    P1: a non-end coefficient of X (Kgs k X) is absorbed (k ≤ m_X), or
        strictly below a coefficient of normX X (non-end, or a merged
        end coefficient c + c'' with c'' > 0).  Gives Kend v X for
        v = PHI (normX X) (t + y) (v > m_X by OffSpec).
    P2: each coefficient of normX X is a sum of X-coefficients; a
        non-end one contains a non-end X-coefficient (merged
        coefficients are > 1, so exponent positions under them are
        non-end).  With dominance (`dominance`, `Kgs_lt`, valid for
        BI_pos X) and principality: Kend z' (normX X) for z' = PHI X y.

(D) Joint induction J(X) on ⟦X⟧ by blt (well_founded_induction blt_wf),
    for all imp_ok X with KHI X:
    (⇐) for z a normal notation value (z = ⟦w⟧, BS_nf w) with Kend z X,
        z principal, and Cl(X,z): bfix ⟦X⟧ z.
        - f: from Cl;
        - small component C ⊑ ⟦K'⟧ (coverX): Klt z K' (tracking),
          Klt z (normX K'); z ∈ Fix(normX K') from Cl (normX K' < normX X)
          and `bfix_of_fix`; offset minimality gives t' < z; E(K') (IH)
          at argument z: PHI K' z ≈ PHI (normX K') (t' + z) ≤
          PHI (normX K') z ≤ z (t' + z = z by principality);
        - family component at z: continuity of the normal diagonal
          (`bgood_diag`, `normal_continuous`; z ≤ sup succ z_j, succ z_j < z
          by principality), approximate by notations x < z (interpolants
          of the normal z); member cover K'_x has Klt z K'_x, and
          z ∈ Fix(K'_x) by IH (⇐) for K'_x (its clause is inherited since
          normX K'_x < normX X); then `bphi_le_fix`.
    (E) E(X), by inner induction on y (size_induction (ord BSmall
        BS_denote), interpolants of y for children), as in `absorb_enum`:
        - (≤) cfe_least for X at v = PHI N (t + y) (N = normX X), a normal
          notation value: v ∈ Fix(N) (value), Kend v X by P1, Cl(X,v) by
          `nest` + `zlt_nest` for T' < N (normal), so (⇐) gives
          v ∈ Fix(X);
        - (≥) cfe_least for N at z' = PHI X y.  Needs z' ∈ Fix(N):
          first, interpolants of z' by the `interp_aux` argument run on X
          (`bphi_interp`; chain values bounded by normal notation values
          using E(K') for components (IH) and E(X) at notations n_j < y
          (inner IH) for start values succ φ_X(y_j), `BS_succ`,
          `BS_onePlus`); then small components of ⟦N⟧ via `cover` of N
          (normal covers K' < N with Klt z' K' from Kend z' N, P2) and
          `nestX` + `zlt_nest` (z' ∈ Fix(X) by `bfix_value_full`);
          families of ⟦N⟧ at z' by continuity with the interpolants of z'.
          Then minimality (OffSpec at z': m_X < z' by dominance for X)
          gives PHI N t ≤ z', t < z', principality gives t + y ≤ z', and
          children as in `absorb_enum`.
    Only normal notation values ever need interpolants.

(F) Offset for the general case (H5): m_X computed like `absorb_max`
    over absorbed coefficients (track them in a variant of normX
    returning (normX X, list of absorbed coefficients)); `BS_offset`
    needs `lead_big (normX X)`; if normX X has leading exponent 0
    (everything small) absorption cannot occur at all (exponents all 0),
    and E(X) is a pure `bequiv` statement.

(G) Normalizer (H7): BS-level, bottom-up; BN X y ↦
    normS (BN (normX X') (t ⊕ y')) after normalizing coefficients
    (value only) and the argument; correctness from E.  Then step 5:
    extend `Kl_correct` to improper matrices and normalize via `Kinv`.

## Implementation order

1. H3 `nestX` (self-contained; design (A)). DONE.
2. H3' tracking in `coverX` (B). DONE.
3. P1/P2 (C) and the absorbed-coefficient bookkeeping (F). DONE.
4. Joint induction (D) + (E). DONE (`hereditary_absorption`).
5. Normalizer (G) DONE; then Schütte matrices.

## Superseded ideas (do not revisit)

- Sum-level rewriting of the rest before absorbing: impossible, non-top
  absorption is not `bequiv`.
- A lower-bound induction over notations n < φ_N(t+y) for (≥): stuck on
  the case n = end coefficient of N; replaced by interpolants of z'.
- Restricted normalizer (merges + one head absorption): judged useless
  by the user.
