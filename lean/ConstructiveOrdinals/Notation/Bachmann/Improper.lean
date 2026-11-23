import ConstructiveOrdinals.Notation.Bachmann.Absorb
import ConstructiveOrdinals.Notation.Bachmann.OrderType

/-!
# Hereditary absorption and the normalizer for arbitrary notations

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

An improper index (normal exponents, positive normal coefficients, but the
summands in any order) has a normal form `normX X`; the improper `φ_X` is
`φ_{normX X}` shifted by an offset (`hereditary_absorption`). With it,
`normSX` normalizes every notation, proper or not, and the full term algebra
has order type `BHO₁`.

Ported from the Rocq file `Notation/BachmannImproper.v`.

Lean notes:

- Rocq's abbreviation `PHI R` is the local notation `Φ[R]`.
- The section variables of `addT` and `shift` become explicit arguments.
- `normalizeX_correct` is proved by the mutual recursions
  `normalizeX_correct_S` and `normalizeX_correct_I` (Rocq uses the combined
  scheme `BNotation_mut`).
- `normSX_complete` uses `BS_nf_unique` in place of Rocq's appeal to
  `cmp_eq`.
- The examples are checked by `rfl` (Rocq: `vm_compute`).
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx

local notation "Φ[" R "]" => bphi (fun x => 1 + x) (BI_denote R)

/-! ## Normal forms of improper index sums -/

/-- Rocq: `Notation.BachmannImproper.ilt_ieq_false`. -/
theorem ilt_ieq_false {a b : BIdx} (H : ilt a b) (E : ieq a b) : False := by
  induction H with
  | nil => cases E
  | exp _ _ _ _ _ _ _ IH => cases E with | cons _ _ _ _ _ _ E1 _ _ => exact IH E1
  | coef _ _ _ _ _ _ _ Hcc => cases E with | cons _ _ _ _ _ _ _ E2 _ => exact lt_irrefl _ (lt_of_lt_of_le Hcc E2.ge)
  | tail _ _ _ _ _ _ _ _ _ IH => cases E with | cons _ _ _ _ _ _ _ _ E3 => exact IH E3

/-- Rocq: `Notation.BachmannImproper.ilt_irrefl`. -/
theorem ilt_irrefl (a : BIdx) (H : ilt a a) : False := ilt_ieq_false H (ieq_refl a)

/-- Rocq: `Notation.BachmannImproper.ilt_asym`. -/
theorem ilt_asym (a b : BIdx) (H1 : ilt a b) (H2 : ilt b a) : False := ilt_irrefl a (ilt_trans H1 H2)

/-- Rocq: `Notation.BachmannImproper.cmpIX`. -/
def cmpIX (a b : BIdx) : Ordering := cmpI (BI_size a + BI_size b + 1) a b

/-- Rocq: `Notation.BachmannImproper.cmpIX_spec`. -/
theorem cmpIX_spec (a b : BIdx) (Ha : BI_nf a) (Hb : BI_nf b) :
    (ilt a b → cmpIX a b = .lt) ∧ (ieq a b → cmpIX a b = .eq) ∧ (ilt b a → cmpIX a b = .gt) := by
  have H := (cmp_correct (BI_size a + BI_size b + 1)).2 a b (Nat.lt_succ_self _) Ha Hb
  unfold cmpIX
  revert H
  cases cmpI (BI_size a + BI_size b + 1) a b with
  | lt => intro H; exact ⟨fun _ => rfl, fun H' => (ilt_ieq_false H H').elim, fun H' => (ilt_asym _ _ H H').elim⟩
  | eq =>
    intro H
    exact ⟨fun H' => (ilt_ieq_false H' H).elim, fun _ => rfl, fun H' => (ilt_ieq_false H' (ieq_sym H)).elim⟩
  | gt =>
    intro H
    exact ⟨fun H' => (ilt_asym _ _ H H').elim, fun H' => (ilt_ieq_false H (ieq_sym H')).elim, fun _ => rfl⟩

/-- Rocq: `Notation.BachmannImproper.cmpIX_total`. -/
theorem cmpIX_total (a b : BIdx) (Ha : BI_nf a) (Hb : BI_nf b) : ilt a b ∨ ieq a b ∨ ilt b a := by
  have H := (cmp_correct (BI_size a + BI_size b + 1)).2 a b (Nat.lt_succ_self _) Ha Hb
  revert H
  cases cmpI (BI_size a + BI_size b + 1) a b with
  | lt => exact .inl
  | eq => exact fun H => .inr (.inl H)
  | gt => exact fun H => .inr (.inr H)

/-- Adding a term `Ω^e·c` in front of a normal index. Rocq: `Notation.BachmannImproper.addT`. -/
def addT (e : BIdx) (c : BSmall) (A : BIdx) : BIdx :=
  match A with
  | BIZ => BIC e c BIZ
  | BIC e2 c2 r2 =>
    match cmpIX e e2 with
    | .lt => BIC e2 c2 r2
    | .eq => BIC e (BS_add c c2) r2
    | .gt => BIC e c (BIC e2 c2 r2)

/-- Rocq: `Notation.BachmannImproper.normX`. -/
def normX : BIdx → BIdx
  | BIZ => BIZ
  | BIC e c r => addT (normX e) c (normX r)

/-- Improper indices, at every depth of exponents, with positive normal
coefficients. Rocq: `Notation.BachmannImproper.imp_ok`. -/
def imp_ok : BIdx → Prop
  | BIZ => True
  | BIC e c r => imp_ok e ∧ BS_nf c ∧ 0 < BS_denote c ∧ imp_ok r

/-- Rocq: `Notation.BachmannImproper.nf_imp_ok`. -/
theorem nf_imp_ok : ∀ X : BIdx, BI_nf X → imp_ok X
  | BIZ, _ => trivial
  | BIC e _ r, ⟨He, Hc, Hc0, Hr, _⟩ => ⟨nf_imp_ok e He, Hc, Hc0, nf_imp_ok r Hr⟩

/-! ### The section `addT`: `e` is normal, `c` normal and positive -/

/-- Rocq: `Notation.BachmannImproper.addT_lt`. -/
theorem addT_lt (e : BIdx) (c : BSmall) (He : BI_nf e) (e2 : BIdx) (c2 : BSmall) (r2 : BIdx) (H2 : BI_nf e2)
    (H : ilt e e2) : addT e c (BIC e2 c2 r2) = BIC e2 c2 r2 := by
  show (match cmpIX e e2 with
    | .lt => BIC e2 c2 r2
    | .eq => BIC e (BS_add c c2) r2
    | .gt => BIC e c (BIC e2 c2 r2)) = _
  rw [(cmpIX_spec e e2 He H2).1 H]

/-- Rocq: `Notation.BachmannImproper.addT_eq`. -/
theorem addT_eq (e : BIdx) (c : BSmall) (He : BI_nf e) (e2 : BIdx) (c2 : BSmall) (r2 : BIdx) (H2 : BI_nf e2)
    (H : ieq e e2) : addT e c (BIC e2 c2 r2) = BIC e (BS_add c c2) r2 := by
  show (match cmpIX e e2 with
    | .lt => BIC e2 c2 r2
    | .eq => BIC e (BS_add c c2) r2
    | .gt => BIC e c (BIC e2 c2 r2)) = _
  rw [(cmpIX_spec e e2 He H2).2.1 H]

/-- Rocq: `Notation.BachmannImproper.addT_gt`. -/
theorem addT_gt (e : BIdx) (c : BSmall) (He : BI_nf e) (e2 : BIdx) (c2 : BSmall) (r2 : BIdx) (H2 : BI_nf e2)
    (H : ilt e2 e) : addT e c (BIC e2 c2 r2) = BIC e c (BIC e2 c2 r2) := by
  show (match cmpIX e e2 with
    | .lt => BIC e2 c2 r2
    | .eq => BIC e (BS_add c c2) r2
    | .gt => BIC e c (BIC e2 c2 r2)) = _
  rw [(cmpIX_spec e e2 He H2).2.2 H]

/-- Rocq: `Notation.BachmannImproper.add_reflect`. -/
theorem add_reflect (c : BSmall) (Hc : BS_nf c) (c2 : BSmall) (H2 : BS_nf c2) :
    BS_denote (BS_add c c2) ≈ BS_denote c + BS_denote c2 ∧ BS_nf (BS_add c c2) :=
  let ⟨E, N⟩ := BS_add_reflects _ c ⟨equiv_refl _, Hc⟩ _ c2 ⟨equiv_refl _, H2⟩
  ⟨equiv_symm E, N⟩

/-- Rocq: `Notation.BachmannImproper.addT_nf`. -/
theorem addT_nf (e : BIdx) (c : BSmall) (He : BI_nf e) (Hc : BS_nf c) (Hc0 : 0 < BS_denote c) (A : BIdx)
    (HA : BI_nf A) : BI_nf (addT e c A) := by
  match A, HA with
  | BIZ, _ => exact ⟨He, Hc, Hc0, trivial, trivial⟩
  | BIC e2 c2 r2, HA =>
    have HA' := HA
    obtain ⟨He2, Hc2, _, Hr2, Hl2⟩ := HA'
    match cmpIX_total e e2 He He2 with
    | .inl H => rw [addT_lt e c He e2 c2 r2 He2 H]; exact HA
    | .inr (.inl H) =>
      rw [addT_eq e c He e2 c2 r2 He2 H]
      obtain ⟨E, N⟩ := add_reflect c Hc c2 Hc2
      exact ⟨He, N, lt_of_lt_of_le Hc0 (le_trans (le_add_right _ _) E.ge), Hr2,
        lead_below_ieq r2 r2 e2 e (ieq_refl _) (ieq_sym H) Hl2⟩
    | .inr (.inr H) => rw [addT_gt e c He e2 c2 r2 He2 H]; exact ⟨He, Hc, Hc0, HA, H⟩

theorem lt_add_pos (a b : Ordinal.{0}) (H : 0 < b) : a < a + b :=
  lt_of_le_of_lt (add_zero a).ge (add_lt_add_left a H)

/-- Ordinal addition is strictly monotone on the right.
Rocq: `Notation.BachmannImproper.addT_mono`. -/
theorem addT_mono (e : BIdx) (c : BSmall) (He : BI_nf e) (Hc : BS_nf c) (_Hc0 : 0 < BS_denote c) (A B : BIdx)
    (HA : BI_nf A) (HB : BI_nf B) (Hlt : ilt A B) : ilt (addT e c A) (addT e c B) := by
  match B, HB, Hlt with
  | BIZ, _, Hlt => cases Hlt
  | BIC eB cB rB, HB, Hlt =>
    obtain ⟨HeB, HcB, HcB0, _⟩ := HB
    obtain ⟨EB, _⟩ := add_reflect c Hc cB HcB
    match A, HA, Hlt with
    | BIZ, _, _ =>
      show ilt (BIC e c BIZ) _
      match cmpIX_total e eB He HeB with
      | .inl H => rw [addT_lt e c He eB cB rB HeB H]; exact .exp _ _ _ _ _ _ H
      | .inr (.inl H) =>
        rw [addT_eq e c He eB cB rB HeB H]
        exact .coef _ _ _ _ _ _ (ieq_refl e) (lt_of_lt_of_le (lt_add_pos _ _ HcB0) EB.ge)
      | .inr (.inr H) => rw [addT_gt e c He eB cB rB HeB H]; exact .tail _ _ _ _ _ _ (ieq_refl e) (equiv_refl _) (.nil _ _ _)
    | BIC eA cA rA, HA, Hlt =>
      obtain ⟨HeA, HcA, _⟩ := HA
      obtain ⟨EA, _⟩ := add_reflect c Hc cA HcA
      have HeAB : ilt eA eB ∨ ieq eA eB := by
        cases Hlt with
        | exp _ _ _ _ _ _ H => exact .inl H
        | coef _ _ _ _ _ _ H _ => exact .inr H
        | tail _ _ _ _ _ _ H _ _ => exact .inr H
      match cmpIX_total e eA He HeA with
      | .inl H =>
        rw [addT_lt e c He eA cA rA HeA H]
        have HeB' : ilt e eB := match HeAB with
          | .inl H' => ilt_trans H H'
          | .inr H' => ilt_ieq H (ieq_refl e) H'
        rw [addT_lt e c He eB cB rB HeB HeB']
        exact Hlt
      | .inr (.inl H) =>
        rw [addT_eq e c He eA cA rA HeA H]
        match HeAB with
        | .inl H' =>
          rw [addT_lt e c He eB cB rB HeB (ilt_ieq H' (ieq_sym H) (ieq_refl eB))]
          exact .exp _ _ _ _ _ _ (ilt_ieq H' (ieq_sym H) (ieq_refl eB))
        | .inr H' =>
          rw [addT_eq e c He eB cB rB HeB (ieq_trans H H')]
          cases Hlt with
          | exp _ _ _ _ _ _ Hx => exact (ilt_ieq_false Hx H').elim
          | coef _ _ _ _ _ _ _ Hc' =>
            exact .coef _ _ _ _ _ _ (ieq_refl e) (lt_of_le_of_lt EA.le (lt_of_lt_of_le (add_lt_add_left _ Hc') EB.ge))
          | tail _ _ _ _ _ _ _ Hc' Hr' =>
            exact .tail _ _ _ _ _ _ (ieq_refl e)
              (equiv_trans EA (equiv_trans (add_congr (equiv_refl _) Hc') (equiv_symm EB))) Hr'
      | .inr (.inr H) =>
        rw [addT_gt e c He eA cA rA HeA H]
        match cmpIX_total e eB He HeB with
        | .inl H2 => rw [addT_lt e c He eB cB rB HeB H2]; exact .exp _ _ _ _ _ _ H2
        | .inr (.inl H2) =>
          rw [addT_eq e c He eB cB rB HeB H2]
          exact .coef _ _ _ _ _ _ (ieq_refl e) (lt_of_lt_of_le (lt_add_pos _ _ HcB0) EB.ge)
        | .inr (.inr H2) => rw [addT_gt e c He eB cB rB HeB H2]; exact .tail _ _ _ _ _ _ (ieq_refl e) (equiv_refl _) Hlt

/-- Rocq: `Notation.BachmannImproper.normX_nf`. -/
theorem normX_nf : ∀ X : BIdx, imp_ok X → BI_nf (normX X)
  | BIZ, _ => trivial
  | BIC e c r, ⟨He, Hc, Hc0, Hr⟩ => addT_nf (normX e) c (normX_nf e He) Hc Hc0 _ (normX_nf r Hr)

/-- On normal indices, `normX` is the identity. Rocq: `Notation.BachmannImproper.normX_id`. -/
theorem normX_id : ∀ X : BIdx, BI_nf X → normX X = X
  | BIZ, _ => rfl
  | BIC e c r, ⟨He, _, _, Hr, Hl⟩ => by
    show addT (normX e) c (normX r) = BIC e c r
    rw [normX_id r Hr, normX_id e He]
    match r, Hr, Hl with
    | BIZ, _, _ => rfl
    | BIC e2 c2 r2, Hr, Hl => exact addT_gt e c He e2 c2 r2 Hr.1 Hl

/-! ## Covering the components of an improper index -/

/-- Rocq: `Notation.BachmannImproper.icovX`. -/
def icovX (T0 : BIdx) : Prop :=
  (∀ a, ∃ T, imp_ok T ∧ KHI T ∧ ilt (normX T) (normX T0) ∧ (∀ z, OInf z → Kend z T0 → Klt z T) ∧
    bsub (bsmallSz (BI_denote T0) a) (BI_denote T) ∧ ∃ a', bsub (BI_denote T) (bsmallSz (BI_denote T0) a')) ∧
  (∀ d x, BS_nf x → HI (BS_denote x) → ∃ T, imp_ok T ∧ KHI T ∧ ilt (normX T) (normX T0) ∧
    (∀ z, OInf z → Kend z T0 → BS_denote x ≤ z → Kend z T) ∧
    bsub (bbigSz (BI_denote T0) d (BS_denote x)) (BI_denote T) ∧
    ∃ d', bsub (BI_denote T) (bbigSz (BI_denote T0) d' (BS_denote x)))

/-- Rocq: `Notation.BachmannImproper.normX_ne`. -/
theorem normX_ne (K r : BIdx) (H : ilt (normX K) (normX r)) : r ≠ BIZ := by
  intro E
  subst E
  generalize normX K = A at H
  exact (nomatch (H : ilt A BIZ))

/-- Rocq: `Notation.BachmannImproper.imp_ok_smartC`. -/
theorem imp_ok_smartC (e : BIdx) (n : BSmall) (x : BIdx) (He : imp_ok e) (Hn : BS_nf n) (Hx : imp_ok x) :
    imp_ok (smartC e n x) :=
  match n, Hn with
  | BZ, _ => Hx
  | BN T y, Hn => ⟨He, Hn, BS_pos T y, Hx⟩

/-- Anything below the leading term `Ω^{normX e}·c` is below `normX (Ω^e·c + r)`.
Rocq: `Notation.BachmannImproper.ilt_below_head`. -/
theorem ilt_below_head (e : BIdx) (c : BSmall) (r K : BIdx) (He : imp_ok e) (Hc : BS_nf c) (Hc0 : 0 < BS_denote c)
    (Hr : imp_ok r) (HKl : ilt K (BIC (normX e) c BIZ)) : ilt K (normX (BIC e c r)) := by
  have HnR := normX_nf r Hr
  have HnE := normX_nf e He
  show ilt K (addT (normX e) c (normX r))
  revert HnR
  cases normX r with
  | BIZ => intro _; exact HKl
  | BIC e2 c2 r2 =>
    intro HnR
    exact ilt_trans HKl (addT_mono (normX e) c HnE Hc Hc0 BIZ (BIC e2 c2 r2) trivial HnR (.nil _ _ _))

/-- Rocq: `Notation.BachmannImproper.ilt_cover_term`. -/
theorem ilt_cover_term (e : BIdx) (c : BSmall) (r : BIdx) (n : BSmall) (x : BIdx) (He : imp_ok e) (Hc : BS_nf c)
    (Hc0 : 0 < BS_denote c) (Hr : imp_ok r) (_Hn : BS_nf n) (Hnc : BS_denote n < BS_denote c) (Hx : imp_ok x)
    (Hl : lead_below (normX x) (normX e)) : ilt (normX (smartC e n x)) (normX (BIC e c r)) := by
  refine ilt_below_head e c r _ He Hc Hc0 Hr ?_
  have HnE := normX_nf e He
  have Hnx := normX_nf x Hx
  match n with
  | BZ =>
    show ilt (normX x) (BIC (normX e) c BIZ)
    revert Hl Hnx
    cases normX x with
    | BIZ => intro _ _; exact .nil _ _ _
    | BIC _ _ _ => intro Hl _; exact .exp _ _ _ _ _ _ Hl
  | BN Tn yn =>
    show ilt (addT (normX e) (BN Tn yn) (normX x)) (BIC (normX e) c BIZ)
    revert Hl Hnx
    cases normX x with
    | BIZ => intro _ _; exact .coef _ _ _ _ _ _ (ieq_refl _) Hnc
    | BIC e2 c2 r2 =>
      intro Hl Hnx
      rw [addT_gt (normX e) (BN Tn yn) HnE e2 c2 r2 Hnx.1 Hl]
      exact .coef _ _ _ _ _ _ (ieq_refl _) Hnc

/-- Rocq: `Notation.BachmannImproper.lead_cover_small`. -/
theorem lead_cover_small (e e' : BIdx) (x : BSmall) (_He' : imp_ok e') (Hl : ilt (normX e') (normX e)) :
    lead_below (normX (smartC e' x BIZ)) (normX e) :=
  match x with
  | BZ => trivial
  | BN _ _ => Hl

/-- Rocq: `Notation.BachmannImproper.coverX`. -/
theorem coverX : ∀ T0 : BIdx, imp_ok T0 → KHI T0 → icovX T0
  | BIZ, _, _ => ⟨fun a => (nomatch a), fun d => (nomatch d)⟩
  | BIC e c r, ⟨He, Hc, Hc0, Hr⟩, HK => by
    obtain ⟨HKe, HKc, HKr⟩ := KHI_cons _ _ _ HK
    obtain ⟨Sr, Fr⟩ := coverX r Hr HKr
    obtain ⟨Se, Fe⟩ := coverX e He HKe
    have HnR := normX_nf r Hr
    have HnE := normX_nf e He
    have Hmono : ∀ K, imp_ok K → ilt (normX K) (normX r) → ilt (normX (BIC e c K)) (normX (BIC e c r)) :=
      fun K HKo Hl => addT_mono (normX e) c HnE Hc Hc0 _ _ (normX_nf K HKo) HnR Hl
    refine ⟨fun a => ?_, fun d x Hx HIx => ?_⟩
    · match badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a with
      | .inl ⟨a', Ea⟩ =>
        obtain ⟨γ, Hγ, k, Hk⟩ := mul_small_form (bexpΩ (BI_denote e)) (BS_denote c) a'
        obtain ⟨n, Hn, HIn, Hγn, Hnc, j, Hj⟩ := coef_approx c γ HKc Hγ
        have E3 := Ea.trans (Hk.trans (congrArg _ (bexpΩ_small_all _ k)))
        obtain ⟨t0, Ht0⟩ := bexpΩ_small_zero (BI_denote e)
        obtain ⟨a0, Ha0⟩ := mul_small_back (bexpΩ (BI_denote e)) (BS_denote c) j t0
        obtain ⟨a'', Ha''⟩ := badd_small_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a0
        exact ⟨smartC e n BIZ, imp_ok_smartC e n BIZ He Hn trivial, KHI_smartC e n BIZ HKe HIn KHI_nil,
          ilt_cover_term e c r n BIZ He Hc Hc0 Hr Hn Hnc trivial trivial,
          fun z _ HKz => Klt_smartC_coef z e c r n BIZ HKz Hnc trivial,
          bsub_eq_l E3 (bsub_trans (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hγn) bzero)
            (smartC_bequiv e n BIZ).2),
          a'', bsub_eq_r (Ha''.trans (Ha0.trans (congrArg _ Ht0)))
            (bsub_trans (smartC_bequiv e n BIZ).1 (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hj) bzero))⟩
      | .inr ⟨b, Eb⟩ =>
        obtain ⟨K, HKo, HKK, HKl, Htr, Hlo, b', Hup⟩ := Sr b
        obtain ⟨t, Et⟩ := badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) b'
        exact ⟨BIC e c K, ⟨He, Hc, Hc0, HKo⟩, KHI_intro e c K HKe HKc HKK, Hmono K HKo HKl,
          fun z Hz HKz => let ⟨H1, H2, H3⟩ := Kend_rest z e c r (normX_ne _ _ HKl) HKz; ⟨H1, H2, Htr z Hz H3⟩,
          bsub_eq_l Eb (bsub_badd_r _ _ _ Hlo), t, bsub_eq_r Et (bsub_badd_r _ _ _ Hup)⟩
    · match badd_big_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d with
      | .inl ⟨d', Ed⟩ =>
        obtain ⟨γ, Hγ, k, Hk⟩ := mul_big_form (bexpΩ (BI_denote e)) (BS_denote c) d'
        obtain ⟨n, Hn, HIn, Hγn, Hnc, j, Hj⟩ := coef_approx c γ HKc Hγ
        match bexpΩ_big_cases (BI_denote e) k with
        | .inl ⟨q, Hq⟩ =>
          obtain ⟨e', He', HKe', Hlte, Htre, Hloe, q', Hupe⟩ := Se q
          obtain ⟨t0, Ht0⟩ := bexpΩ_fam_s (BI_denote e) q'
          obtain ⟨d0, Hd0⟩ := mul_big_back (bexpΩ (BI_denote e)) (BS_denote c) j t0
          obtain ⟨d'', Hd''⟩ := badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d0
          have Hx' := imp_ok_smartC e' x BIZ He' Hx trivial
          refine ⟨smartC e n (smartC e' x BIZ), imp_ok_smartC e n _ He Hn Hx',
            KHI_smartC e n _ HKe HIn (KHI_smartC e' x BIZ HKe' HIx KHI_nil),
            ilt_cover_term e c r n _ He Hc Hc0 Hr Hn Hnc Hx' (lead_cover_small e e' x He' Hlte),
            fun z Hz HKz Hxz => Kend_smartC_coef z e c r n _ HKz Hnc
              (Kend_smartC_end z e' x (Htre z Hz (Kend_exp z e c r Hz HKz)) Hxz), ?_, d'', ?_⟩
          · refine bsub_eq_l ((Ed _).trans ((Hk _).trans (congrArg _ (Hq _)))) ?_
            refine bsub_trans (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hγn) _) ?_
            refine bsub_trans (bsub_badd_r _ _ (BI_denote (BIC e' x BIZ))
              (bsub_trans (bsub_term_mono _ _ _ _ Hloe (le_refl _)) (bequiv_badd_zero_r _).2)) ?_
            exact bsub_trans (bsub_badd_r _ _ _ (smartC_bequiv e' x BIZ).2) (smartC_bequiv _ _ _).2
          · refine bsub_eq_r ((Hd'' _).trans ((Hd0 _).trans (congrArg _ (Ht0 _)))) ?_
            refine bsub_trans (smartC_bequiv _ _ _).1 ?_
            refine bsub_trans (bsub_badd_r _ _ (BI_denote (BIC e' x BIZ)) (smartC_bequiv e' x BIZ).1) ?_
            refine bsub_trans (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hj) _) ?_
            exact bsub_badd_r _ _ _ (bsub_trans (bequiv_badd_zero_r _).1 (bsub_term_mono _ _ _ _ Hupe (le_refl _)))
        | .inr ⟨de, Hde⟩ =>
          obtain ⟨e', He', HKe', Hlte, Htre, Hloe, de', Hupe⟩ := Fe de x Hx HIx
          have H1 : BEquiv (bmul (bexpΩ (BI_denote e')) (embed (BS_denote BS_one))) (bexpΩ (BI_denote e')) :=
            bequiv_trans (bequiv_bmul _ _ _ _ (bequiv_refl _) (bequiv_embed _ _ BS_one_denote))
              ⟨(bsub_bmul_one _).1, (bsub_bmul_one _).2⟩
          have Hx1 : imp_ok (BIC e' BS_one BIZ) := ⟨He', BS_one_nf, BS_pos _ _, trivial⟩
          obtain ⟨t0, Ht0⟩ := bexpΩ_big_b (BI_denote e) de'
          obtain ⟨d0, Hd0⟩ := mul_big_back (bexpΩ (BI_denote e)) (BS_denote c) j t0
          obtain ⟨d'', Hd''⟩ := badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d0
          refine ⟨smartC e n (BIC e' BS_one BIZ), imp_ok_smartC e n _ He Hn Hx1,
            KHI_smartC e n _ HKe HIn (KHI_intro e' BS_one BIZ HKe' HI_one KHI_nil),
            ilt_cover_term e c r n _ He Hc Hc0 Hr Hn Hnc Hx1 Hlte,
            fun z Hz HKz Hxz => Kend_smartC_coef z e c r n _ HKz Hnc
              (.inr ⟨Htre z Hz (Kend_exp z e c r Hz HKz) Hxz, BS_one_denote⟩), ?_, d'', ?_⟩
          · refine bsub_eq_l ((Ed _).trans ((Hk _).trans (congrArg _ (Hde _)))) ?_
            refine bsub_trans (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hγn) _) ?_
            refine bsub_trans (bsub_badd_r _ _ (BI_denote (BIC e' BS_one BIZ))
              (bsub_trans (bsub_trans (bsub_bexpΩ _ _ Hloe) H1.2) (bequiv_badd_zero_r _).2)) ?_
            exact (smartC_bequiv _ _ _).2
          · refine bsub_eq_r ((Hd'' _).trans ((Hd0 _).trans (congrArg _ (Ht0 _)))) ?_
            refine bsub_trans (smartC_bequiv _ _ _).1 ?_
            refine bsub_trans (bsub_badd_r _ _ (bexpΩ (BI_denote e')) (bsub_trans (bequiv_badd_zero_r _).1 H1.1)) ?_
            refine bsub_trans (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hj) _) ?_
            exact bsub_badd_r _ _ _ (bsub_bexpΩ _ _ Hupe)
      | .inr ⟨d', Ed⟩ =>
        obtain ⟨K, HKo, HKK, HKl, Htr, Hlo, d'', Hup⟩ := Fr d' x Hx HIx
        obtain ⟨t, Et⟩ := badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d''
        exact ⟨BIC e c K, ⟨He, Hc, Hc0, HKo⟩, KHI_intro e c K HKe HKc HKK, Hmono K HKo HKl,
          fun z Hz HKz Hxz => let ⟨H1, H2, H3⟩ := Kend_rest z e c r (normX_ne _ _ HKl) HKz;
            Kend_cons z e c K H1 H2 (Htr z Hz H3 Hxz),
          bsub_eq_l (Ed _) (bsub_badd_r _ _ _ Hlo), t, bsub_eq_r (Et _) (bsub_badd_r _ _ _ Hup)⟩

/-! ## Nesting for improper indices -/

/-- Rocq: `Notation.BachmannImproper.ilt_lead`. -/
theorem ilt_lead (r1 e1 e2 : BIdx) (c2 : BSmall) (r2 : BIdx) (H : lead_below r1 e1) (He : ieq e1 e2) :
    ilt r1 (BIC e2 c2 r2) :=
  match r1, H with
  | BIZ, _ => .nil _ _ _
  | BIC e3 _ _, H => .exp _ _ _ _ _ _ (ilt_ieq (H : ilt e3 e1) (ieq_refl e3) He)

/-- `Ω^E1·c1 + R ⊑ Ω^E·c + (Ω^E1·d + R)` when `E1 ≈ E` and `c1 ≤ c + d`.
Rocq: `Notation.BachmannImproper.merge_bsub`. -/
theorem merge_bsub (E1 E : BOrd.{0}) (c c1 d : Ordinal.{0}) (R : BOrd.{0}) (HE : BEquiv E1 E) (Hc : c1 ≤ c + d) :
    bsub (badd (bmul (bexpΩ E1) (embed c1)) R) (badd (bmul (bexpΩ E) (embed c)) (badd (bmul (bexpΩ E1) (embed d)) R)) :=
  bsub_trans (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ HE.1 Hc) _)
    (bsub_trans (bequiv_merge (bexpΩ E) c d R).2
      (bsub_badd_r _ _ _ (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ HE.2 (le_refl _)) _)))

/-- Coefficients below an additively principal `z` stay below `z` under
`normX` (merged coefficients are sums of coefficients).
Rocq: `Notation.BachmannImproper.Klt_addT`. -/
theorem Klt_addT (z : Ordinal.{0}) (e : BIdx) (c : BSmall) (A : BIdx) (Hp : ∀ a, a < z → a + z ≤ z) (He : BI_nf e)
    (Hc : BS_nf c) (HA : BI_nf A) (HKe : Klt z e) (Hcz : BS_denote c < z) (HKA : Klt z A) : Klt z (addT e c A) := by
  match A, HA, HKA with
  | BIZ, _, _ => exact ⟨HKe, Hcz, trivial⟩
  | BIC e2 c2 r2, ⟨He2, Hc2, _⟩, HKA =>
    match cmpIX_total e e2 He He2 with
    | .inl H => rw [addT_lt e c He e2 c2 r2 He2 H]; exact HKA
    | .inr (.inl H) =>
      rw [addT_eq e c He e2 c2 r2 He2 H]
      obtain ⟨E, _⟩ := add_reflect c Hc c2 Hc2
      exact ⟨HKe, lt_of_le_of_lt E.le (lt_of_lt_of_le (add_lt_add_left _ HKA.2.1) (Hp _ Hcz)), HKA.2.2⟩
    | .inr (.inr H) => rw [addT_gt e c He e2 c2 r2 He2 H]; exact ⟨HKe, Hcz, HKA⟩

/-- Rocq: `Notation.BachmannImproper.Klt_normX`. -/
theorem Klt_normX (z : Ordinal.{0}) (Hp : ∀ a, a < z → a + z ≤ z) : ∀ X : BIdx, imp_ok X → Klt z X → Klt z (normX X)
  | BIZ, _, _ => trivial
  | BIC e c r, ⟨He, Hc, _, Hr⟩, ⟨HKe, Hcz, HKr⟩ =>
    Klt_addT z _ c _ Hp (normX_nf e He) Hc (normX_nf r Hr) (Klt_normX z Hp e He HKe) Hcz (Klt_normX z Hp r Hr HKr)

/-! ## Coefficient positions under `normX` -/

/-- Rocq: `Notation.BachmannImproper.imp_ok_pos`. -/
theorem imp_ok_pos : ∀ X : BIdx, imp_ok X → BI_pos X
  | BIZ, _ => trivial
  | BIC e _ r, ⟨He, _, Hc0, Hr⟩ => ⟨imp_ok_pos e He, Hc0, imp_ok_pos r Hr⟩

/-- Rocq: `Notation.BachmannImproper.normX_BIZ`. -/
theorem normX_BIZ (X : BIdx) (H : normX X = BIZ) : X = BIZ := by
  match X, H with
  | BIZ, _ => rfl
  | BIC e c r, H =>
    revert H
    show addT (normX e) c (normX r) = BIZ → _
    cases normX r with
    | BIZ => intro H; exact (nomatch H)
    | BIC e2 c2 r2 =>
      show (match cmpIX (normX e) e2 with
        | .lt => BIC e2 c2 r2
        | .eq => BIC (normX e) (BS_add c c2) r2
        | .gt => BIC (normX e) c (BIC e2 c2 r2)) = BIZ → _
      cases cmpIX (normX e) e2 <;> intro H <;> exact (nomatch H)

/-- Rocq: `Notation.BachmannImproper.Kend_ofX`. -/
theorem Kend_ofX : ∀ (T : BIdx) (z : Ordinal.{0}), imp_ok T → (∀ k, Kge k T → k ≤ z) → (∀ k, Kgs k T → k < z) →
    Kend z T
  | BIZ, _, _, _, _ => trivial
  | BIC e c r, z, ⟨He, Hc, Hc0, Hr⟩, H1, H2 => by
    have ihe := Kend_ofX e z He
    have ihr := Kend_ofX r z Hr
    match r, H1, H2, ihr with
    | BIZ, H1, H2, _ =>
      have Hcmp := BS_compare_correct c BS_one Hc BS_one_nf
      revert Hcmp
      cases BS_compare c BS_one with
      | lt =>
        intro Hcmp
        exact absurd (lt_of_lt_of_le Hc0 (le_zero_of_lt_one (lt_of_lt_of_le Hcmp BS_one_denote.le))) (lt_irrefl _)
      | eq =>
        intro Hcmp
        have Hc1 := equiv_trans Hcmp BS_one_denote
        exact .inr ⟨ihe (fun k hk => H1 k (.inl hk)) (fun k hk => H2 k (.inr ⟨Hc1, hk⟩)), Hc1⟩
      | gt =>
        intro Hcmp
        exact .inl ⟨Klt_of_Kge _ e fun k hk => H2 k (.inl ⟨hk, lt_of_le_of_lt BS_one_denote.ge Hcmp⟩),
          H1 _ (.inr (.inl (le_refl _)))⟩
    | BIC _ _ _, H1, H2, ihr =>
      exact ⟨Klt_of_Kge _ e fun k hk => H2 k (.inl hk), H2 _ (.inr (.inl (le_refl _))),
        ihr (fun k hk => H1 k (.inr (.inr hk))) (fun k hk => H2 k (.inr (.inr hk)))⟩

/-- Coefficients of an improper `T` lie below `z` except at the end, when
`φ_T(0) ≤ z`. Rocq: `Notation.BachmannImproper.Kend_of_valueX`. -/
theorem Kend_of_valueX (T : BIdx) (z : Ordinal.{0}) (HT : imp_ok T) (Hz : Φ[T] 0 ≤ z) : Kend z T :=
  Kend_ofX T z HT (fun k Hk => le_trans (dominance T BZ k (imp_ok_pos T HT) Hk) Hz)
    (fun k Hk => lt_of_lt_of_le (Kgs_lt T k (imp_ok_pos T HT) Hk) Hz)

/-- P2: for an additively principal infinite `z`, the `Kend` condition passes
from `X` to its normal form. Rocq: `Notation.BachmannImproper.Kend_normX`. -/
theorem Kend_normX (z : Ordinal.{0}) (Hz : OInf z) (Hp : ∀ a, a < z → a + z ≤ z) :
    ∀ X : BIdx, imp_ok X → Kend z X → Kend z (normX X)
  | BIZ, _, _ => trivial
  | BIC e c r, ⟨He, Hc, _, Hr⟩, HK => by
    have HE := normX_nf e He
    have HN := normX_nf r Hr
    have IHe := Kend_normX z Hz Hp e He
    have IHr := Kend_normX z Hz Hp r Hr
    show Kend z (addT (normX e) c (normX r))
    revert HN IHr
    cases hN : normX r with
    | BIZ =>
      intro _ _
      have Er := normX_BIZ r hN
      subst Er
      match HK with
      | .inl ⟨H1, H2⟩ => exact .inl ⟨Klt_normX z Hp e He H1, H2⟩
      | .inr ⟨H1, H2⟩ => exact .inr ⟨IHe H1, H2⟩
    | BIC e2 c2 r2 =>
      intro HN IHr
      have Hne : r ≠ BIZ := by intro E; subst E; exact (nomatch hN)
      obtain ⟨HKe0, Hcz, HKr⟩ := Kend_rest z e c r Hne HK
      have HKe := Klt_normX z Hp e He HKe0
      have IH := IHr HKr
      obtain ⟨He2, Hc2, _⟩ := HN
      match cmpIX_total (normX e) e2 HE He2 with
      | .inl H => rw [addT_lt _ c HE e2 c2 r2 He2 H]; exact IH
      | .inr (.inl H) =>
        rw [addT_eq _ c HE e2 c2 r2 He2 H]
        obtain ⟨E, _⟩ := add_reflect c Hc c2 Hc2
        match r2, IH with
        | BIZ, IH =>
          have Hc2z : BS_denote c2 ≤ z := match IH with
            | .inl ⟨_, H'⟩ => H'
            | .inr ⟨_, H'⟩ => le_trans H'.le (le_of_lt (oinf_one z Hz))
          exact .inl ⟨HKe, le_trans E.le (le_trans (add_le_add (le_refl _) Hc2z) (Hp _ Hcz))⟩
        | BIC _ _ _, ⟨_, Hc2z, HK3⟩ =>
          exact ⟨HKe, lt_of_le_of_lt E.le (lt_of_lt_of_le (add_lt_add_left _ Hc2z) (Hp _ Hcz)), HK3⟩
      | .inr (.inr H) => rw [addT_gt _ c HE e2 c2 r2 He2 H]; exact ⟨HKe, Hcz, IH⟩

/-- The absorbed terms of `X`, at every depth: those `Ω^e·c` dropped by `normX`.
Rocq: `Notation.BachmannImproper.AbsLt`. -/
def AbsLt (v : Ordinal.{0}) : BIdx → Prop
  | BIZ => True
  | BIC e c r => AbsLt v e ∧ AbsLt v r ∧ (lead_gt (normX r) (normX e) → Klt v (BIC e c BIZ))

/-- Given the absorbed coefficients below `z`, coefficients below `z` pass back
from the normal form to `X`. Rocq: `Notation.BachmannImproper.Klt_back`. -/
theorem Klt_back (z : Ordinal.{0}) : ∀ X : BIdx, imp_ok X → AbsLt z X → Klt z (normX X) → Klt z X
  | BIZ, _, _, _ => trivial
  | BIC e c r, ⟨He, Hc, _, Hr⟩, ⟨HAe, HAr, HAt⟩, HK => by
    have HE := normX_nf e He
    have HN := normX_nf r Hr
    have IHe := Klt_back z e He HAe
    have IHr := Klt_back z r Hr HAr
    revert HK HN HAt IHr
    show (lead_gt (normX r) (normX e) → _) → Klt z (addT (normX e) c (normX r)) → BI_nf (normX r) → _ → _
    cases hN : normX r with
    | BIZ =>
      intro _ HK _ _
      have Er := normX_BIZ r hN
      subst Er
      obtain ⟨H1, H2, _⟩ := HK
      exact ⟨IHe H1, H2, trivial⟩
    | BIC e2 c2 r2 =>
      intro HAt HK HN IHr
      obtain ⟨He2, Hc2, _⟩ := HN
      match cmpIX_total (normX e) e2 HE He2 with
      | .inl H =>
        rw [addT_lt _ c HE e2 c2 r2 He2 H] at HK
        obtain ⟨H1, H2, _⟩ := HAt H
        exact ⟨H1, H2, IHr HK⟩
      | .inr (.inl H) =>
        rw [addT_eq _ c HE e2 c2 r2 He2 H] at HK
        obtain ⟨E, _⟩ := add_reflect c Hc c2 Hc2
        obtain ⟨HKe, Hs, HK3⟩ := HK
        have Hs' := lt_of_le_of_lt E.ge Hs
        exact ⟨IHe HKe, lt_of_le_of_lt (le_add_right _ _) Hs',
          IHr ⟨Klt_ieq z (ieq_sym H) HKe, lt_of_le_of_lt (le_add_left _ _) Hs', HK3⟩⟩
      | .inr (.inr H) =>
        rw [addT_gt _ c HE e2 c2 r2 He2 H] at HK
        obtain ⟨HKe, Hcz, HK2⟩ := HK
        exact ⟨IHe HKe, Hcz, IHr HK2⟩

/-- P1: given the absorbed coefficients below `z`, the `Kend` condition passes
back from the normal form to `X`. Rocq: `Notation.BachmannImproper.Kend_back`. -/
theorem Kend_back (z : Ordinal.{0}) (Hz : OInf z) : ∀ X : BIdx, imp_ok X → AbsLt z X → Kend z (normX X) → Kend z X
  | BIZ, _, _, _ => trivial
  | BIC e c r, ⟨He, Hc, Hc0, Hr⟩, ⟨HAe, HAr, HAt⟩, HK => by
    have HE := normX_nf e He
    have HN := normX_nf r Hr
    have IHe := Kend_back z Hz e He HAe
    have IHr := Kend_back z Hz r Hr HAr
    revert HK HN HAt IHr
    show (lead_gt (normX r) (normX e) → _) → Kend z (addT (normX e) c (normX r)) → BI_nf (normX r) → _ → _
    cases hN : normX r with
    | BIZ =>
      intro _ HK _ _
      have Er := normX_BIZ r hN
      subst Er
      match HK with
      | .inl ⟨H1, H2⟩ => exact .inl ⟨Klt_back z e He HAe H1, H2⟩
      | .inr ⟨H1, H2⟩ => exact .inr ⟨IHe H1, H2⟩
    | BIC e2 c2 r2 =>
      intro HAt HK HN IHr
      obtain ⟨He2, Hc2, Hc20, _⟩ := HN
      have Goal : Klt z e → BS_denote c < z → Kend z (BIC e2 c2 r2) → Kend z (BIC e c r) := fun H1 H2 H3 =>
        Kend_cons z e c r H1 H2 (IHr H3)
      match cmpIX_total (normX e) e2 HE He2 with
      | .inl H =>
        rw [addT_lt _ c HE e2 c2 r2 He2 H] at HK
        obtain ⟨H1, H2, _⟩ := HAt H
        exact Goal H1 H2 HK
      | .inr (.inl H) =>
        rw [addT_eq _ c HE e2 c2 r2 He2 H] at HK
        obtain ⟨E, _⟩ := add_reflect c Hc c2 Hc2
        have Hcc : BS_denote c < BS_denote c + BS_denote c2 := lt_add_pos _ _ Hc20
        match r2, HK, Goal with
        | BIZ, .inl ⟨HKe, Hs⟩, Goal =>
          have Hs' := le_trans E.ge Hs
          exact Goal (Klt_back z e He HAe HKe) (lt_of_lt_of_le Hcc Hs')
            (.inl ⟨Klt_ieq z (ieq_sym H) HKe, le_trans (le_add_left _ _) Hs'⟩)
        | BIZ, .inr ⟨_, Hs⟩, _ =>
          exact absurd (lt_of_le_of_lt (succ_least Hc0) (lt_of_lt_of_le Hcc (le_trans E.ge Hs.le))) (lt_irrefl 1)
        | BIC _ _ _, ⟨HKe, Hs, HK3⟩, Goal =>
          have Hs' := lt_of_le_of_lt E.ge Hs
          exact Goal (Klt_back z e He HAe HKe) (lt_trans Hcc Hs')
            ⟨Klt_ieq z (ieq_sym H) HKe, lt_of_le_of_lt (le_add_left _ _) Hs', HK3⟩
      | .inr (.inr H) =>
        rw [addT_gt _ c HE e2 c2 r2 He2 H] at HK
        obtain ⟨HKe, Hcz, HK2⟩ := HK
        exact Goal (Klt_back z e He HAe HKe) Hcz HK2

/-! ## The largest absorbed coefficient -/

/-- Rocq: `Notation.BachmannImproper.absb`. -/
def absb (e A : BIdx) : Bool :=
  match A with
  | BIZ => false
  | BIC e2 _ _ => isLT (cmpIX e e2)

/-- Rocq: `Notation.BachmannImproper.absb_true`. -/
theorem absb_true (e A : BIdx) (He : BI_nf e) (HA : BI_nf A) (Hb : absb e A = true) : lead_gt A e := by
  match A, HA, Hb with
  | BIZ, _, Hb => exact (nomatch Hb)
  | BIC e2 _ _, HA, Hb =>
    obtain ⟨_, S2, S3⟩ := cmpIX_spec e e2 He HA.1
    match cmpIX_total e e2 He HA.1 with
    | .inl H => exact H
    | .inr (.inl H) => exact absurd ((S2 H) ▸ Hb : isLT .eq = true) (fun h => nomatch h)
    | .inr (.inr H) => exact absurd ((S3 H) ▸ Hb : isLT .gt = true) (fun h => nomatch h)

/-- Rocq: `Notation.BachmannImproper.absb_false`. -/
theorem absb_false (e A : BIdx) (He : BI_nf e) (HA : BI_nf A) (Hb : absb e A = false) (H : lead_gt A e) : False :=
  match A, HA, Hb, H with
  | BIZ, _, _, H => H
  | BIC e2 _ _, HA, Hb, H => absurd (((cmpIX_spec e e2 He HA.1).1 H) ▸ Hb : isLT .lt = false) (fun h => nomatch h)

/-- Rocq: `Notation.BachmannImproper.absX`. -/
def absX (n : Nat) : BIdx → Option BSmall
  | BIZ => none
  | BIC e c r =>
    omax n (absX n e)
      (match absb (normX e) (normX r) with
        | true => omax n (kmax n (BIC e c BIZ)) (absX n r)
        | false => absX n r)

/-- Rocq: `Notation.BachmannImproper.Kin_nfX`. -/
theorem Kin_nfX (k : BSmall) : ∀ T : BIdx, Kin k T → imp_ok T → BS_nf k
  | BIZ, h, _ => h.elim
  | BIC e _ _, .inl H, HT => Kin_nfX k e H HT.1
  | BIC _ _ _, .inr (.inl rfl), HT => HT.2.1
  | BIC _ _ r, .inr (.inr H), HT => Kin_nfX k r H HT.2.2.2

/-- Rocq: `Notation.BachmannImproper.kmax_specX`. -/
theorem kmax_specX (n : Nat) : ∀ T : BIdx, imp_ok T → BI_size T + BI_size T < n → kmax_ok T (kmax n T)
  | BIZ, _, _ => rfl
  | BIC e c r, ⟨He, Hc, _, Hr⟩, Hsz => by
    let P : BSmall → Prop := fun u => BS_nf u ∧ BS_size u ≤ BI_size (BIC e c r) ∧ Kin u (BIC e c r)
    have HP : ∀ u v, P u → P v → OrderingCorrect (cmpS n u v) (BS_denote u) (BS_denote v) :=
      fun u v ⟨Hu, Hsu, _⟩ ⟨Hv, Hsv, _⟩ => (cmp_correct n).1 u v (Nat.lt_of_le_of_lt (Nat.add_le_add Hsu Hsv) Hsz) Hu Hv
    have He' := kmax_specX n e He
      (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt (size_C_e e c r)) (Nat.le_of_lt (size_C_e e c r))) Hsz)
    have Hr' := kmax_specX n r Hr
      (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt (size_C_r e c r)) (Nat.le_of_lt (size_C_r e c r))) Hsz)
    have Pe : OptAll P (kmax n e) := by
      revert He'
      cases kmax n e with
      | none => intro _; exact trivial
      | some u =>
        intro ⟨Hin, _⟩
        exact ⟨Kin_nfX u e Hin He, Nat.le_trans (Kin_size' u e Hin) (Nat.le_of_lt (size_C_e e c r)), .inl Hin⟩
    have Pc : P c := ⟨Hc, Nat.le_of_lt (size_C_c e c r), .inr (.inl rfl)⟩
    have Pr : OptAll P (kmax n r) := by
      revert Hr'
      cases kmax n r with
      | none => intro _; exact trivial
      | some u =>
        intro ⟨Hin, _⟩
        exact ⟨Kin_nfX u r Hin Hr, Nat.le_trans (Kin_size' u r Hin) (Nat.le_of_lt (size_C_r e c r)), .inr (.inr Hin)⟩
    have S1 := omax_spec n (kmax n e) (some c) P HP Pe Pc
    show kmax_ok (BIC e c r) (omax n (omax n (kmax n e) (some c)) (kmax n r))
    revert S1
    cases omax n (kmax n e) (some c) with
    | none => intro S1; exact (nomatch S1.2)
    | some w1 =>
      intro ⟨Pw1, _, Lw1e, Lw1c⟩
      have S2 := omax_spec n (some w1) (kmax n r) P HP Pw1 Pr
      revert S2
      cases omax n (some w1) (kmax n r) with
      | none => intro S2; exact (nomatch S2.1)
      | some w =>
        intro ⟨Pw, _, Lw1, Lwr⟩
        have Ke : Kle (BS_denote w) e := by
          revert He' Lw1e
          cases kmax n e with
          | none => intro He' _; subst He'; exact trivial
          | some u => intro He' Lu; exact Kle_mono _ _ (le_trans Lu Lw1) e He'.2
        have Kr : Kle (BS_denote w) r := by
          revert Hr' Lwr
          cases kmax n r with
          | none => intro Hr' _; subst Hr'; exact trivial
          | some u => intro Hr' Lu; exact Kle_mono _ _ Lu r Hr'.2
        exact ⟨Pw.2.2, Ke, le_trans Lw1c Lw1, Kr⟩

/-- Rocq: `Notation.BachmannImproper.Kgs_Kge`. -/
theorem Kgs_Kge (k : Ordinal.{0}) : ∀ T : BIdx, Kgs k T → Kge k T
  | BIZ, h => h.elim
  | BIC e _ r, H =>
    have ihe := Kgs_Kge k e
    have ihr := Kgs_Kge k r
    match r, H, ihr with
    | BIZ, .inl ⟨H, _⟩, _ => .inl H
    | BIZ, .inr ⟨_, H⟩, _ => .inl (ihe H)
    | BIC _ _ _, .inl H, _ => .inl H
    | BIC _ _ _, .inr (.inl H), _ => .inr (.inl H)
    | BIC _ _ _, .inr (.inr H), ihr => .inr (.inr (ihr H))

/-- Rocq: `Notation.BachmannImproper.Kgs_cons`. -/
theorem Kgs_cons (k : Ordinal.{0}) (e : BIdx) (c : BSmall) (r : BIdx) (H : Kgs k r) : Kgs k (BIC e c r) :=
  match r, H with
  | BIZ, h => h.elim
  | BIC _ _ _, h => .inr (.inr h)

/-- Rocq: `Notation.BachmannImproper.Kgs_absorbed`. -/
theorem Kgs_absorbed (k : BSmall) (e : BIdx) (c : BSmall) (r : BIdx) (Hne : r ≠ BIZ) (H : Kin k (BIC e c BIZ)) :
    Kgs (BS_denote k) (BIC e c r) :=
  match r, Hne, Kin_Kge k _ H with
  | BIZ, Hne, _ => absurd rfl Hne
  | BIC _ _ _, _, .inl h => .inl h
  | BIC _ _ _, _, .inr (.inl h) => .inr (.inl h)
  | BIC _ _ _, _, .inr (.inr h) => h.elim

/-- Rocq: `Notation.BachmannImproper.Kgs_exp`. -/
theorem Kgs_exp (k : Ordinal.{0}) (e : BIdx) (c : BSmall) (r : BIdx) (Hc : BS_nf c) (Hc0 : 0 < BS_denote c)
    (H : Kgs k e) : Kgs k (BIC e c r) := by
  match r with
  | BIC _ _ _ => exact .inl (Kgs_Kge k e H)
  | BIZ =>
    have Hcmp := BS_compare_correct c BS_one Hc BS_one_nf
    revert Hcmp
    cases BS_compare c BS_one with
    | lt =>
      intro Hcmp
      exact absurd (lt_of_lt_of_le Hc0 (le_zero_of_lt_one (lt_of_lt_of_le Hcmp BS_one_denote.le))) (lt_irrefl _)
    | eq => intro Hcmp; exact .inr ⟨equiv_trans Hcmp BS_one_denote, H⟩
    | gt => intro Hcmp; exact .inl ⟨Kgs_Kge k e H, lt_of_le_of_lt BS_one_denote.ge Hcmp⟩

/-- The specification shape of a candidate maximum. Rocq: `Notation.BachmannImproper.ospec`. -/
def ospec (n : Nat) (P : Ordinal.{0} → Prop) (K : BSmall → Prop) : Option BSmall → Prop
  | none => ∀ v, P v
  | some m => BS_nf m ∧ BS_size m + BS_size m < n ∧ K m ∧ ∀ v, BS_denote m < v → P v

/-- Rocq: `Notation.BachmannImproper.ospec_mono`. -/
theorem ospec_mono (n : Nat) (P1 P2 : Ordinal.{0} → Prop) (K1 K2 : BSmall → Prop) (o : Option BSmall)
    (HP : ∀ v, P1 v → P2 v) (HK : ∀ m, K1 m → K2 m) : ospec n P1 K1 o → ospec n P2 K2 o :=
  match o with
  | none => fun h v => HP v (h v)
  | some m => fun ⟨a, b, c, d⟩ => ⟨a, b, HK m c, fun v hv => HP v (d v hv)⟩

theorem size_pair_lt {a b n : Nat} (Ha : a + a < n) (Hb : b + b < n) : a + b < n :=
  match Nat.le_total a b with
  | .inl h => Nat.lt_of_le_of_lt (Nat.add_le_add_right h b) Hb
  | .inr h => Nat.lt_of_le_of_lt (Nat.add_le_add_left h a) Ha

/-- Rocq: `Notation.BachmannImproper.omax_join`. -/
theorem omax_join (n : Nat) (Pa Pb : Ordinal.{0} → Prop) (K : BSmall → Prop) (oa ob : Option BSmall)
    (Ha : ospec n Pa K oa) (Hb : ospec n Pb K ob) : ospec n (fun v => Pa v ∧ Pb v) K (omax n oa ob) := by
  match oa, ob, Ha, Hb with
  | some a, some b, ⟨Na, Sa, Ka, Va⟩, ⟨Nb, Sb, Kb, Vb⟩ =>
    obtain ⟨S1, S2⟩ := isLT_spec _ _ _ ((cmp_correct n).1 a b (size_pair_lt Sa Sb) Na Nb)
    show ospec n _ K (match isLT (cmpS n a b) with
      | true => some b
      | false => some a)
    revert S1 S2
    cases isLT (cmpS n a b) with
    | true => intro S1 _; exact ⟨Nb, Sb, Kb, fun v hv => ⟨Va v (lt_trans (S1 rfl) hv), Vb v hv⟩⟩
    | false => intro _ S2; exact ⟨Na, Sa, Ka, fun v hv => ⟨Va v hv, Vb v (lt_of_le_of_lt (S2 rfl) hv)⟩⟩
  | some _, none, ⟨Na, Sa, Ka, Va⟩, Hb => exact ⟨Na, Sa, Ka, fun v hv => ⟨Va v hv, Hb v⟩⟩
  | none, some _, Ha, ⟨Nb, Sb, Kb, Vb⟩ => exact ⟨Nb, Sb, Kb, fun v hv => ⟨Ha v, Vb v hv⟩⟩
  | none, none, Ha, Hb => exact fun v => ⟨Ha v, Hb v⟩

theorem BI_size_pos : ∀ T : BIdx, 1 ≤ BI_size T
  | BIZ => Nat.le_refl 1
  | BIC _ _ _ => Nat.succ_le_succ (Nat.zero_le _)

/-- Rocq: `Notation.BachmannImproper.absX_spec`. -/
theorem absX_spec (n : Nat) : ∀ X : BIdx, imp_ok X → BI_size X + BI_size X < n →
    ospec n (fun v => AbsLt v X) (fun m => Kgs (BS_denote m) X) (absX n X)
  | BIZ, _, _ => fun _ => trivial
  | BIC e c r, HX, Hsz => by
    have HX' := HX
    obtain ⟨He, Hc, Hc0, Hr⟩ := HX'
    have IHe := absX_spec n e He
      (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt (size_C_e e c r)) (Nat.le_of_lt (size_C_e e c r))) Hsz)
    have IH := absX_spec n r Hr
      (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt (size_C_r e c r)) (Nat.le_of_lt (size_C_r e c r))) Hsz)
    have HN := normX_nf r Hr
    have HE := normX_nf e He
    show ospec n (fun v => AbsLt v e ∧ AbsLt v r ∧ (lead_gt (normX r) (normX e) → Klt v (BIC e c BIZ)))
      (fun m => Kgs (BS_denote m) (BIC e c r))
      (omax n (absX n e) (match absb (normX e) (normX r) with
        | true => omax n (kmax n (BIC e c BIZ)) (absX n r)
        | false => absX n r))
    refine omax_join n _ _ _ _ _ (ospec_mono n _ _ _ _ _ (fun _ h => h) (fun m Hm => Kgs_exp _ e c r Hc Hc0 Hm) IHe) ?_
    cases Eb : absb (normX e) (normX r) with
    | true =>
      have Hlg := absb_true (normX e) (normX r) HE HN Eb
      have Hne : r ≠ BIZ := by intro E; subst E; exact (Hlg : False)
      have HP : imp_ok (BIC e c BIZ) := ⟨He, Hc, Hc0, trivial⟩
      have HPsz : BI_size (BIC e c BIZ) ≤ BI_size (BIC e c r) :=
        Nat.add_le_add_right (Nat.add_le_add_left (BI_size_pos r) _) 1
      have Hk := kmax_specX n (BIC e c BIZ) HP (Nat.lt_of_le_of_lt (Nat.add_le_add HPsz HPsz) Hsz)
      revert Hk
      cases kmax n (BIC e c BIZ) with
      | none => intro Hk; exact (nomatch (Hk : BIC e c BIZ = BIZ))
      | some k =>
        intro ⟨Hkin, Hkle⟩
        have Hks := Nat.le_trans (Kin_size' k _ Hkin) HPsz
        refine ospec_mono n (fun v => Klt v (BIC e c BIZ) ∧ AbsLt v r) _ _ _ _ (fun _ ⟨H1, H2⟩ => ⟨H2, fun _ => H1⟩)
          (fun _ h => h) (omax_join n _ _ _ _ _ ?_ ?_)
        · exact ⟨Kin_nfX k _ Hkin HP, Nat.lt_of_le_of_lt (Nat.add_le_add Hks Hks) Hsz, Kgs_absorbed k e c r Hne Hkin,
            fun v hv => Kle_lt _ _ _ Hkle hv⟩
        · exact ospec_mono n _ _ _ _ _ (fun _ h => h) (fun m Hm => Kgs_cons _ e c r Hm) IH
    | false =>
      have Hna := absb_false (normX e) (normX r) HE HN Eb
      exact ospec_mono n _ _ _ _ _ (fun _ h => ⟨h, fun H' => (Hna H').elim⟩) (fun m Hm => Kgs_cons _ e c r Hm) IH

/-- Rocq: `Notation.BachmannImproper.absM`. -/
def absM (X : BIdx) : Option BSmall := absX (BI_size X + BI_size X + 1) X

/-- The offset of `X`: the least `t` with `m_X < φ_{normX X}(t)`, or 0 when
nothing is absorbed. Rocq: `Notation.BachmannImproper.offX`. -/
def offX (X : BIdx) : BSmall :=
  match absM X with
  | none => BZ
  | some m => BS_offset (normX X) m

/-- Rocq: `Notation.BachmannImproper.absM_spec`. -/
theorem absM_spec (X : BIdx) (HX : imp_ok X) :
    match absM X with
    | none => ∀ v, AbsLt v X
    | some m => BS_nf m ∧ Kgs (BS_denote m) X ∧ ∀ v, BS_denote m < v → AbsLt v X := by
  have H := absX_spec (BI_size X + BI_size X + 1) X HX (Nat.lt_succ_self _)
  unfold absM
  revert H
  cases absX (BI_size X + BI_size X + 1) X with
  | none => exact id
  | some _ => exact fun ⟨a, _, c, d⟩ => ⟨a, c, d⟩

/-- Rocq: `Notation.BachmannImproper.lead_big_addT`. -/
theorem lead_big_addT (e : BIdx) (c : BSmall) (A : BIdx) (He : BI_nf e) (HA : BI_nf A) (Hb : lead_big A) :
    lead_big (addT e c A) := by
  match A, HA, Hb with
  | BIZ, _, Hb => exact Hb.elim
  | BIC e2 c2 r2, HA, Hb =>
    match cmpIX_total e e2 He HA.1 with
    | .inl H => rw [addT_lt e c He e2 c2 r2 HA.1 H]; exact Hb
    | .inr (.inl H) =>
      rw [addT_eq e c He e2 c2 r2 HA.1 H]
      intro E
      subst E
      cases H
      exact Hb rfl
    | .inr (.inr H) =>
      rw [addT_gt e c He e2 c2 r2 HA.1 H]
      intro E
      subst E
      cases H

/-- Rocq: `Notation.BachmannImproper.lead_big_addT_e`. -/
theorem lead_big_addT_e (e : BIdx) (c : BSmall) (A : BIdx) (He : BI_nf e) (Hne : e ≠ BIZ) (HA : BI_nf A) :
    lead_big (addT e c A) := by
  match A, HA with
  | BIZ, _ => exact Hne
  | BIC e2 c2 r2, HA =>
    match cmpIX_total e e2 He HA.1 with
    | .inl H =>
      rw [addT_lt e c He e2 c2 r2 HA.1 H]
      intro E
      subst E
      cases H
    | .inr (.inl H) => rw [addT_eq e c He e2 c2 r2 HA.1 H]; exact Hne
    | .inr (.inr H) => rw [addT_gt e c He e2 c2 r2 HA.1 H]; exact Hne

/-- Rocq: `Notation.BachmannImproper.lead_gt_big'`. -/
theorem lead_gt_big' (A e : BIdx) (H : lead_gt A e) : lead_big A := lead_gt_big e A H

/-- Rocq: `Notation.BachmannImproper.omax_none`. -/
theorem omax_none (n : Nat) (a b : Option BSmall) (H : omax n a b = none) : a = none ∧ b = none := by
  match a, b, H with
  | none, none, _ => exact ⟨rfl, rfl⟩
  | none, some _, H => exact (nomatch H)
  | some _, none, H => exact (nomatch H)
  | some u, some v, H =>
    revert H
    show (match isLT (cmpS n u v) with
      | true => some v
      | false => some u) = none → _
    cases isLT (cmpS n u v) <;> intro H <;> exact (nomatch H)

/-- Something is absorbed only if the normal form has a nonzero leading
exponent. Rocq: `Notation.BachmannImproper.absX_lead_big`. -/
theorem absX_lead_big (n : Nat) : ∀ X : BIdx, imp_ok X → absX n X ≠ none → lead_big (normX X)
  | BIZ, _, Hn => absurd rfl Hn
  | BIC e c r, ⟨He, _, _, Hr⟩, Hn => by
    have HN := normX_nf r Hr
    have HE := normX_nf e He
    show lead_big (addT (normX e) c (normX r))
    cases Ee : absX n e with
    | some m =>
      exact lead_big_addT_e _ c _ HE
        (lead_big_ne _ (absX_lead_big n e He (fun h => by rw [Ee] at h; exact (nomatch h)))) HN
    | none =>
      cases Eb : absb (normX e) (normX r) with
      | true => exact lead_big_addT _ c _ HE HN (lead_gt_big' _ _ (absb_true _ _ HE HN Eb))
      | false =>
        refine lead_big_addT _ c _ HE HN (absX_lead_big n r Hr fun h => Hn ?_)
        show omax n (absX n e) (match absb (normX e) (normX r) with
          | true => omax n (kmax n (BIC e c BIZ)) (absX n r)
          | false => absX n r) = none
        rw [Ee, Eb]
        exact h

/-- Rocq: `Notation.BachmannImproper.absM_lead_big`. -/
theorem absM_lead_big (X : BIdx) (HX : imp_ok X) (H : absM X ≠ none) : lead_big (normX X) :=
  absX_lead_big _ X HX H

/-! ## Hereditary absorption -/

/-- Shifted enumeration, abstracting `absorb_enum`: if `Fix(X) ⊆ Fix(R)`, the
values of `φ_X` lie in an upward closed region `U`, and the common fixpoints
of `R` at notations in `U` are common fixpoints of `X`, then `φ_X` is `φ_R`
shifted by the least `t` with `φ_R(t) ∈ U`. Rocq: `Notation.BachmannImproper.shift_enum`. -/
theorem shift_enum (X R : BIdx) (U : Ordinal.{0} → Prop) (t : BSmall)
    (HXinh : Nonempty (bsmall (BI_denote X) ⊕ bbig (BI_denote X)))
    (Hsub : ∀ z, Complete z → BFix (fun x => 1 + x) (BI_denote X) z → BFix (fun x => 1 + x) (BI_denote R) z)
    (Hreg : ∀ y, Complete y → U (Φ[X] y)) (Hup : ∀ a b, a ≤ b → U a → U b) (Ht : BS_nf t)
    (HUt : U (Φ[R] (BS_denote t)))
    (Hleast : ∀ z, Complete z → BFix (fun x => 1 + x) (BI_denote R) z → U z → Φ[R] (BS_denote t) ≤ z)
    (Hprin : ∀ z, Complete z → BFix (fun x => 1 + x) (BI_denote R) z → U z → BS_denote t + z ≤ z)
    (ABS : ∀ s, BS_nf s → U (Φ[R] (BS_denote s)) → BFix (fun x => 1 + x) (BI_denote X) (Φ[R] (BS_denote s))) :
    ∀ y, BS_nf y → Φ[X] (BS_denote y) ≈ Φ[R] (BS_denote t + BS_denote y) := by
  have Htc := BS_complete t
  have Hgx := BI_good X
  have Hgr := BI_good R
  refine BS_denote_ind (motive := fun y => BS_nf y → Φ[X] (BS_denote y) ≈ Φ[R] (BS_denote t + BS_denote y)) ?_
  intro y IH Hy
  have HIy := BS_has_all_interpolants y Hy
  have Hyc := BS_complete y
  obtain ⟨Es, Ns⟩ := BS_add_reflects _ t ⟨equiv_refl _, Ht⟩ _ y ⟨equiv_refl _, Hy⟩
  have EPs : Φ[R] (BS_denote (BS_add t y)) ≈ Φ[R] (BS_denote t + BS_denote y) :=
    ord_eq_normal _ (BI_normal R) _ _ (equiv_symm Es)
  refine equiv_trans (equiv_intro ?_ ?_) EPs
  · have HK : U (Φ[R] (BS_denote (BS_add t y))) :=
      Hup _ _ ((bphi_mono_index _ onePlus_mono _ (BI_bfam R)).1 _ _ (le_trans (le_add_right _ _) Es.le)) HUt
    obtain ⟨H1', H2', H3'⟩ := ABS _ Ns HK
    rw [bphi_unfold _ (BI_denote X)]
    refine cfe_least _ onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgx) _ _ ?_ ?_ ?_
    · exact le_trans (onePlus_mono _ _ (le_trans (le_add_left _ _) Es.le)) (bphi_ge_f _ _ _)
    · refine limit_least fun j => ?_
      obtain ⟨n, Hn, _, Hjn, Hny⟩ := HI_below _ _ HIy (index_lt _ j)
      have h : Φ[X] ((BS_denote y).size j) < Φ[R] (BS_denote (BS_add t y)) :=
        lt_of_le_of_lt ((bphi_mono_index _ onePlus_mono _ (BI_bfam _)).1 _ _ Hjn)
          (lt_of_le_of_lt (IH n Hny Hn).le
            (lt_of_lt_of_le ((BI_normal R).increasing _ _ (add_complete Htc Hyc) (add_lt_add_left _ Hny)) EPs.ge))
      exact (congrFun (bphi_unfold _ (BI_denote X)) _) ▸ h
    · intro i
      match i with
      | .inl k => exact ⟨H2' k, H1'⟩
      | .inr k => exact ⟨H3' k, H1'⟩
  · have Hzc : Complete (Φ[X] (BS_denote y)) := BS_complete (BN X y)
    have Hzfix := Hsub _ Hzc (bfix_value_full _ onePlus_normal _ _ Hgx HXinh Hyc)
    have HUz := Hreg _ Hyc
    have Hlz := Hleast _ Hzc Hzfix HUz
    have Hpr := Hprin _ Hzc Hzfix HUz
    obtain ⟨H1', H2', H3'⟩ := Hzfix
    rw [bphi_unfold _ (BI_denote R)]
    refine cfe_least _ onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgr) _ _ ?_ ?_ ?_
    · exact le_trans (onePlus_mono _ _ (le_trans Es.ge (le_trans (add_le_add (le_refl _)
        (normal_inflationary (BI_normal X) _ Hyc)) Hpr))) H1'
    · refine limit_least fun j => ?_
      have Hj : (BS_denote (BS_add t y)).size j < BS_denote t + BS_denote y := lt_of_lt_of_le (index_lt _ j) Es.ge
      have h : Φ[R] ((BS_denote (BS_add t y)).size j) < Φ[X] (BS_denote y) := by
        match addOrd_lt_cases _ _ _ Hj with
        | .inl Ha => exact lt_of_lt_of_le ((BI_normal R).increasing _ _ Htc Ha) Hlz
        | .inr ⟨j0, Ha⟩ =>
          obtain ⟨n, Hn, _, Hjn, Hny⟩ := HI_below _ _ HIy (index_lt _ j0)
          exact lt_of_le_of_lt ((bphi_mono_index _ onePlus_mono _ (BI_bfam R)).1 _ _
              (le_trans Ha (add_le_add (le_refl _) Hjn)))
            (lt_of_le_of_lt (IH n Hny Hn).ge ((BI_normal X).increasing _ _ Hyc Hny))
      exact (congrFun (bphi_unfold _ (BI_denote R)) _) ▸ h
    · intro i
      match i with
      | .inl k => exact ⟨H2' k, H1'⟩
      | .inr k => exact ⟨H3' k, H1'⟩

/-- `⟦normX X⟧ ⊑ ⟦X⟧`, with equality when nothing is absorbed.
Rocq: `Notation.BachmannImproper.merge_bequiv`. -/
theorem merge_bequiv (e : BIdx) (c : BSmall) (e2 : BIdx) (c2 : BSmall) (r2 : BIdx) (H : ieq e e2) (Hc : BS_nf c)
    (Hc2 : BS_nf c2) :
    BEquiv (BI_denote (BIC e (BS_add c c2) r2))
      (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote (BIC e2 c2 r2))) :=
  let ⟨E, _⟩ := add_reflect c Hc c2 Hc2
  bequiv_sym (bequiv_trans
    (bequiv_badd _ _ _ _ (bequiv_refl _) (bequiv_badd _ _ _ _
      (bequiv_bmul _ _ _ _ (bequiv_bexpΩ _ _ (bequiv_sym (ieq_bequiv H))) (bequiv_refl _)) (bequiv_refl _)))
    (bequiv_trans (bequiv_merge _ _ _ _)
      (bequiv_badd _ _ _ _ (bequiv_bmul _ _ _ _ (bequiv_refl _) (bequiv_embed _ _ (equiv_symm E))) (bequiv_refl _))))

/-- Rocq: `Notation.BachmannImproper.bsub_normX`. -/
theorem bsub_normX : ∀ X : BIdx, imp_ok X → bsub (BI_denote (normX X)) (BI_denote X)
  | BIZ, _ => bsub_refl _
  | BIC e c r, ⟨He0, Hc, _, Hr⟩ => by
    have IH := bsub_normX r Hr
    have IHe := bsub_normX e He0
    show bsub (BI_denote (addT (normX e) c (normX r))) (BI_denote (BIC e c r))
    refine bsub_trans ?_ (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ IHe (le_refl _)) (BI_denote r))
    have He := normX_nf e He0
    generalize normX e = E at He ⊢
    have HN := normX_nf r Hr
    revert IH HN
    cases hN : normX r with
    | BIZ => intro _ _; rw [normX_BIZ r hN]; exact bsub_refl _
    | BIC e2 c2 r2 =>
      intro IH HN
      obtain ⟨He2, Hc2, _⟩ := HN
      match cmpIX_total E e2 He He2 with
      | .inl H => rw [addT_lt E c He e2 c2 r2 He2 H]; exact bsub_trans IH (bsub_absorb _ _)
      | .inr (.inl H) =>
        rw [addT_eq E c He e2 c2 r2 He2 H]
        exact bsub_trans (merge_bequiv E c e2 c2 r2 H Hc Hc2).1 (bsub_badd_r _ _ _ IH)
      | .inr (.inr H) => rw [addT_gt E c He e2 c2 r2 He2 H]; exact bsub_badd_r _ _ _ IH

/-- Rocq: `Notation.BachmannImproper.omax_some_l`. -/
theorem omax_some_l (n : Nat) (u : BSmall) (b : Option BSmall) : omax n (some u) b ≠ none := by
  match b with
  | none => exact fun h => nomatch h
  | some v =>
    show (match isLT (cmpS n u v) with
      | true => some v
      | false => some u) ≠ none
    cases isLT (cmpS n u v) <;> exact fun h => nomatch h

/-- Rocq: `Notation.BachmannImproper.omax_some_r`. -/
theorem omax_some_r (n : Nat) (a : Option BSmall) (v : BSmall) : omax n a (some v) ≠ none := by
  match a with
  | none => exact fun h => nomatch h
  | some u =>
    show (match isLT (cmpS n u v) with
      | true => some v
      | false => some u) ≠ none
    cases isLT (cmpS n u v) <;> exact fun h => nomatch h

/-- Rocq: `Notation.BachmannImproper.kmax_some`. -/
theorem kmax_some (n : Nat) (e : BIdx) (c : BSmall) (r : BIdx) : kmax n (BIC e c r) ≠ none := by
  show omax n (omax n (kmax n e) (some c)) (kmax n r) ≠ none
  cases E : omax n (kmax n e) (some c) with
  | some b => exact omax_some_l n b _
  | none => exact absurd E (omax_some_r n (kmax n e) c)

/-- Rocq: `Notation.BachmannImproper.bequiv_normX`. -/
theorem bequiv_normX (n : Nat) : ∀ X : BIdx, imp_ok X → absX n X = none → BEquiv (BI_denote (normX X)) (BI_denote X)
  | BIZ, _, _ => bequiv_refl _
  | BIC e c r, ⟨He0, Hc, _, Hr⟩, Ha => by
    obtain ⟨Hae, Ha'⟩ := omax_none _ _ _ Ha
    have IHe := bequiv_normX n e He0 Hae
    have HN := normX_nf r Hr
    have He := normX_nf e He0
    revert Ha'
    cases Eb : absb (normX e) (normX r) with
    | true =>
      intro Ha'
      exfalso
      revert Ha'
      cases Ek : kmax n (BIC e c BIZ) with
      | some b => exact omax_some_l n b _
      | none => exact absurd Ek (kmax_some n e c BIZ)
    | false =>
      intro Ha'
      have IH := bequiv_normX n r Hr Ha'
      show BEquiv (BI_denote (addT (normX e) c (normX r))) (BI_denote (BIC e c r))
      refine bequiv_trans ?_ (bequiv_badd _ _ _ _ (bequiv_bmul _ _ _ _ (bequiv_bexpΩ _ _ IHe) (bequiv_refl _))
        (bequiv_refl (BI_denote r)))
      generalize normX e = E at He Eb ⊢
      cases hN : normX r with
      | BIZ => rw [normX_BIZ r hN]; exact bequiv_refl _
      | BIC e2 c2 r2 =>
        rw [hN] at IH HN Eb
        have HN' := HN
        obtain ⟨He2, Hc2, _⟩ := HN'
        match cmpIX_total E e2 He He2 with
        | .inl H => exact (absb_false E (BIC e2 c2 r2) He HN Eb H).elim
        | .inr (.inl H) =>
          rw [addT_eq E c He e2 c2 r2 He2 H]
          exact bequiv_trans (merge_bequiv E c e2 c2 r2 H Hc Hc2) (bequiv_badd _ _ _ _ (bequiv_refl _) IH)
        | .inr (.inr H) => rw [addT_gt E c He e2 c2 r2 He2 H]; exact bequiv_badd _ _ _ _ (bequiv_refl _) IH

/-- Rocq: `Notation.BachmannImproper.imp_ok_KHI`. -/
theorem imp_ok_KHI : ∀ X : BIdx, imp_ok X → KHI X
  | BIZ, _ => KHI_nil
  | BIC e c r, ⟨He, Hc, _, Hr⟩ => KHI_intro e c r (imp_ok_KHI e He) (notation_KHI_S c Hc) (imp_ok_KHI r Hr)

/-- The Bachmann-rule clause for `X` at `z`. Rocq: `Notation.BachmannImproper.ClX`. -/
def ClX (X : BIdx) (z : Ordinal.{0}) : Prop :=
  1 + z ≤ z ∧ ∀ T', BI_nf T' → ilt T' (normX X) → Klt z T' → Φ[T'] z ≤ z

/-- (⇐) at notation values: an additively principal `z` satisfying the
coefficient condition and the clause is a common fixpoint for `X`.
Rocq: `Notation.BachmannImproper.JX`. -/
def JX (X : BIdx) : Prop :=
  ∀ w, BS_nf w → Kend (BS_denote w) X → (∀ a, a < BS_denote w → a + BS_denote w ≤ BS_denote w) →
    ClX X (BS_denote w) → BFix (fun x => 1 + x) (BI_denote X) (BS_denote w)

/-- The enumeration theorem. Rocq: `Notation.BachmannImproper.EX`. -/
def EX (X : BIdx) : Prop :=
  ∀ y, BS_nf y → Φ[X] (BS_denote y) ≈ Φ[normX X] (BS_denote (offX X) + BS_denote y)

/-- Rocq: `Notation.BachmannImproper.EX_of_JX`. -/
theorem EX_of_JX (X : BIdx) (HX : imp_ok X) (HJ : JX X) : EX X := by
  have HN := normX_nf X HX
  have HA := absM_spec X HX
  unfold EX offX
  revert HA
  cases Em : absM X with
  | none =>
    intro _ y _
    exact equiv_trans
      (bphi_bequiv _ onePlus_mono _ _ _ (bequiv_sym (bequiv_normX _ X HX Em)) (BI_bfam X) (BI_bfam _))
      (ord_eq_normal _ (BI_normal _) _ _ (equiv_symm (zero_add _)))
  | some m =>
    intro ⟨Hm, Hmg, Hmv⟩
    have Hlb : lead_big (normX X) := absM_lead_big X HX (by rw [Em]; exact fun h => nomatch h)
    have HNne := lead_big_ne _ Hlb
    have HXne : X ≠ BIZ := by intro E; subst E; exact (nomatch Em)
    obtain ⟨Nt, Hmt, Htt, Hleast⟩ := BS_offset_correct (normX X) HN Hlb m Hm
    refine shift_enum X (normX X) (fun z => BS_denote m < z) _ (Hinh_of' X HX HXne)
      (fun z _ Hf => bfix_bsub _ onePlus_normal _ _ z (bsub_normX X HX) (BI_bfam X) Hf)
      (fun y _ => lt_of_lt_of_le (Kgs_lt X _ (imp_ok_pos X HX) Hmg)
        ((bphi_mono_index _ onePlus_mono _ (BI_bfam X)).1 _ _ (zero_least y)))
      (fun _ _ Hab Ha => lt_of_lt_of_le Ha Hab) Nt Hmt Hleast
      (fun z Hz Hf Hmz => fix_principal _ z _ HN Hlb Hz Hf (lt_of_lt_of_le Htt (Hleast z Hz Hf Hmz))) ?_
    intro s Hs Hms
    have Hw := smartN_nf (normX X) s HN Hs
    have Ew := smartN_equal (normX X) s HN Hs
    have Hvfix := bfix_value_full _ onePlus_normal _ _ (BI_good _) (Hinh_of _ HN HNne) (BS_complete s)
    have Hzc := BS_complete (smartN (normX X) s)
    have Hzfix := bfix_eq _ _ _ (BI_good _) (BI_bfam _) (equiv_symm Ew) Hvfix
    have Hinf := fix_onePlus_finite _ onePlus_normal _ Hzc Hzfix.1
    refine bfix_eq _ _ _ (BI_good X) (BI_bfam X) Ew (HJ _ Hw ?_ ?_ ⟨Hzfix.1, fun T' HT' Hlt HK => ?_⟩)
    · exact Kend_back _ Hinf X HX (Hmv _ (lt_of_lt_of_le Hms Ew.ge))
        (Kend_of_value _ _ HN (bphi_le_fix _ onePlus_normal _ _ (BI_good _) Hzc Hzfix))
    · exact fun a Ha => fix_principal _ _ a HN Hlb Hzc Hzfix Ha
    · exact zlt_nest _ onePlus_normal _ _ _ ((nest _ Hinf (BI_size T' + 1) T' (Nat.lt_succ_self _) HT' HK).1 _ HN Hlt)
        (BI_good _) (BI_bfam _) Hzc Hzfix
where
  Hinh_of' (X : BIdx) (HX : imp_ok X) (HXne : X ≠ BIZ) : Nonempty (bsmall (BI_denote X) ⊕ bbig (BI_denote X)) :=
    match X, HX, HXne with
    | BIZ, _, HXne => absurd rfl HXne
    | BIC e c r, HX, _ => BI_inh e c r HX.2.2.1

/-- Rocq: `Notation.BachmannImproper.JE_all`. -/
theorem JE_all : ∀ (U : BOrd.{0}) (X : BIdx), ble (BI_denote X) U → imp_ok X → JX X ∧ EX X := by
  intro U
  refine blt_wf.induction (C := fun U => ∀ (X : BIdx), ble (BI_denote X) U → imp_ok X → JX X ∧ EX X) U ?_
  intro U IHU X HU HX
  have IH : ∀ K, imp_ok K → blt (BI_denote K) (BI_denote X) → JX K ∧ EX K := fun K HK Hlt =>
    IHU (BI_denote K) (blt_le_trans Hlt HU) K (ble_refl _) HK
  have HJ : JX X := by
    intro w Hw HKX Hpr ⟨Hf1, HCl⟩
    have Hzc := BS_complete w
    have Hinf := fix_onePlus_finite _ onePlus_normal _ Hzc Hf1
    obtain ⟨CS, CF⟩ := coverX X HX (imp_ok_KHI X HX)
    have HIw := notation_KHI_S w Hw
    refine ⟨Hf1, fun a => ?_, fun d => ?_⟩
    · obtain ⟨K, HKo, _, HKl, Htr, Hlo, a', Hup⟩ := CS a
      have HKz := Htr _ Hinf HKX
      have Hblt := bsub_child_blt _ _ (.inl a') Hup
      obtain ⟨_, HE⟩ := IH K HKo Hblt
      have HN' := normX_nf K HKo
      have HKN' := Klt_normX _ Hpr K HKo HKz
      have HN'z := HCl _ HN' HKl HKN'
      have Hoff : BS_denote (offX K) + BS_denote w ≤ BS_denote w := by
        have HA := absM_spec K HKo
        unfold offX
        revert HA
        cases Em' : absM K with
        | some m' =>
          intro ⟨Hm', Hmg', _⟩
          have Hlb' := absM_lead_big K HKo (by rw [Em']; exact fun h => nomatch h)
          obtain ⟨_, _, Htt, Hleast⟩ := BS_offset_correct _ HN' Hlb' m' Hm'
          have HfN' := bfix_of_fix _ onePlus_normal _ _ (BI_good _) (BI_bfam _) Hzc HN'z
          have Hmz := Kge_lt _ _ K (Kgs_Kge _ K Hmg') HKz
          exact Hpr _ (lt_of_lt_of_le Htt (Hleast _ Hzc HfN' Hmz))
        | none => intro _; exact (zero_add _).le
      exact le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam K)).2 _ Hlo _)
        (le_trans (HE w Hw).le (le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam _)).1 _ _ Hoff) HN'z))
    · obtain ⟨K, HKo, _, HKl, Htr, Hlo, d', Hup⟩ := CF d w Hw HIw
      have HKz := Htr _ Hinf HKX (le_refl _)
      have Hblt := bsub_child_blt _ _ (.inr (d', BS_denote w)) Hup
      obtain ⟨HJK, _⟩ := IH K HKo Hblt
      have HfK := HJK w Hw HKz Hpr ⟨Hf1, fun T' HT' Hlt HK => HCl T' HT' (ilt_trans Hlt HKl) HK⟩
      exact le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam K)).2 _ Hlo 0)
        (bphi_le_fix _ onePlus_normal _ _ (BI_good K) Hzc HfK)
  exact ⟨HJ, EX_of_JX X HX HJ⟩

/-- Hereditary absorption: for an improper index `X` (normal exponents,
positive normal coefficients), `φ_X` is `φ_{normX X}` shifted by `offX X`.
Rocq: `Notation.BachmannImproper.hereditary_absorption`. -/
theorem hereditary_absorption (X : BIdx) (HX : imp_ok X) :
    ∀ y, BS_nf y → Φ[X] (BS_denote y) ≈ Φ[normX X] (BS_denote (offX X) + BS_denote y) :=
  (JE_all (BI_denote X) X (ble_refl _) HX).2

/-! ## Normalizing arbitrary notations

Every notation is accepted: index sums at any depth (including inside
exponents) may be improper, with terms in any order, repeated exponents and
zero coefficients; coefficients and arguments are normalized by value. Zero
terms are dropped by `smartC`; the remaining improper index is handled by
`hereditary_absorption`. -/

mutual
/-- Rocq: `Notation.BachmannImproper.normSX`. -/
def normSX : BSmall → BSmall
  | BZ => BZ
  | BN T y => smartN (normX (normTX T)) (BS_add (offX (normTX T)) (normSX y))

/-- Rocq: `Notation.BachmannImproper.normTX`. -/
def normTX : BIdx → BIdx
  | BIZ => BIZ
  | BIC e c r => smartC (normTX e) (normSX c) (normTX r)
end

/-- Rocq: `Notation.BachmannImproper.offX_nf`. -/
theorem offX_nf (X : BIdx) (HX : imp_ok X) : BS_nf (offX X) := by
  have HA := absM_spec X HX
  unfold offX
  revert HA
  cases Em : absM X with
  | none => intro _; exact trivial
  | some m =>
    intro ⟨Hm, _⟩
    exact (BS_offset_correct (normX X) (normX_nf X HX) (absM_lead_big X HX (by rw [Em]; exact fun h => nomatch h))
      m Hm).1

mutual
theorem normalizeX_correct_S : ∀ x : BSmall, BS_nf (normSX x) ∧ BS_denote (normSX x) ≈ BS_denote x
  | BZ => ⟨trivial, equiv_refl _⟩
  | BN T y =>
    let ⟨HX, HXe⟩ := normalizeX_correct_I T
    let ⟨Hy', Hye⟩ := normalizeX_correct_S y
    have Ht := offX_nf (normTX T) HX
    let ⟨Es, Ns⟩ := BS_add_reflects _ (offX (normTX T)) ⟨equiv_refl _, Ht⟩ _ (normSX y) ⟨equiv_refl _, Hy'⟩
    let ⟨N1, N2⟩ := smartN_correct (normX (normTX T)) _ (normX_nf _ HX) Ns
    ⟨N1, equiv_trans N2 (equiv_trans (ord_eq_normal _ (BI_normal _) _ _ (equiv_symm Es))
      (equiv_trans (equiv_symm (hereditary_absorption _ HX (normSX y) Hy'))
        (equiv_trans (ord_eq_normal _ (BI_normal _) _ _ Hye) (bphi_bequiv _ onePlus_mono _ _ _ HXe (BI_bfam _) (BI_bfam _)))))⟩

theorem normalizeX_correct_I : ∀ T : BIdx, imp_ok (normTX T) ∧ BEquiv (BI_denote (normTX T)) (BI_denote T)
  | BIZ => ⟨trivial, bequiv_refl _⟩
  | BIC e c r =>
    let ⟨He', Hee⟩ := normalizeX_correct_I e
    let ⟨Hc', Hce⟩ := normalizeX_correct_S c
    let ⟨Hr', Hre⟩ := normalizeX_correct_I r
    ⟨imp_ok_smartC _ _ _ He' Hc' Hr', bequiv_trans (smartC_bequiv _ _ _)
      (bequiv_badd _ _ _ _ (bequiv_bmul _ _ _ _ (bequiv_bexpΩ _ _ Hee) (bequiv_embed _ _ Hce)) Hre)⟩
end

/-- Rocq: `Notation.BachmannImproper.normalizeX_correct`. -/
theorem normalizeX_correct :
    (∀ x, BS_nf (normSX x) ∧ BS_denote (normSX x) ≈ BS_denote x) ∧
      ∀ T, imp_ok (normTX T) ∧ BEquiv (BI_denote (normTX T)) (BI_denote T) :=
  ⟨normalizeX_correct_S, normalizeX_correct_I⟩

/-- Rocq: `Notation.BachmannImproper.normSX_nf`. -/
theorem normSX_nf (x : BSmall) : BS_nf (normSX x) := (normalizeX_correct_S x).1

/-- Rocq: `Notation.BachmannImproper.normSX_equal`. -/
theorem normSX_equal (x : BSmall) : BS_denote (normSX x) ≈ BS_denote x := (normalizeX_correct_S x).2

/-- Two notations denote the same ordinal iff they normalize to the same normal
form (normal forms are unique). Rocq: `Notation.BachmannImproper.normSX_complete`. -/
theorem normSX_complete (x y : BSmall) (H : BS_denote x ≈ BS_denote y) : normSX x = normSX y :=
  BS_nf_unique _ _ (normSX_nf x) (normSX_nf y)
    (equiv_trans (normSX_equal x) (equiv_trans H (equiv_symm (normSX_equal y))))

/-- `Γ₀ = φ_Ω(0)`. Rocq: `Notation.BachmannImproper.BS_Γ0`. -/
def BS_Γ0 : BSmall := BN BI_Ω BZ

/-- `Γ₀ + Ω` absorbs `Γ₀` with offset 1, since `Γ₀ = φ_Ω(0)` is not above
`Γ₀`: `φ_{Γ₀+Ω}(0) = φ_Ω(1) = Γ₁`. -/
example : normSX (BN (BIC BIZ BS_Γ0 BI_Ω) BZ) = BN BI_Ω (BS_succ BZ) := rfl

/-- Hereditary: `Γ₀ + Ω + Ω²` at 0 is `φ_{Ω²}(0)` (both lower terms absorbed,
offset 0 since `Γ₀ < φ_{Ω²}(0)`). -/
example :
    normSX (BN (BIC BIZ BS_Γ0 (BIC BI_one BS_one (BIC (BIC BIZ (BS_succ BS_one) BIZ) BS_one BIZ))) BZ) =
      BN (BIC (BIC BIZ (BS_succ BS_one) BIZ) BS_one BIZ) BZ := rfl

/-- Absorption inside an exponent: `φ_{Ω^{Γ₀+Ω}}(0) = φ_{Ω^Ω}(0)`, the Large
Veblen Ordinal (`Γ₀` lies below it, so the offset is 0). -/
example : normSX (BN (BIC (BIC BIZ BS_Γ0 BI_Ω) BS_one BIZ) BZ) = BN BI_ΩΩ BZ := rfl

/-- Absorption below a merge: `Ω + Γ₀ + Ω = Ω·2` as an index, offset 0. -/
example : normSX (BN (BIC BI_one BS_one (BIC BIZ BS_Γ0 BI_Ω)) BZ) = BN (BIC BI_one (BS_succ BS_one) BIZ) BZ := rfl

/-! ## All notations, proper or not, lie below `BHO₁`

Every term denotes the value of its normal form, so the full term algebra has
the same order type as the normal forms. -/

/-- Rocq: `Notation.BachmannImproper.BS_bounded_all`. -/
theorem BS_bounded_all (x : BSmall) : BS_denote x < BHO1 :=
  lt_of_le_of_lt (normSX_equal x).ge (BS_bounded _ (normSX_nf x))

/-- Rocq: `Notation.BachmannImproper.AllOrd`. -/
def AllOrd : Ordinal.{0} := mk BSmall BS_denote

/-- Rocq: `Notation.BachmannImproper.BS_all_order_type`. -/
theorem BS_all_order_type : AllOrd ≈ BHO1 :=
  equiv_intro (limit_least fun x => BS_bounded_all x)
    (le_trans BS_order_type.ge (limit_least fun x => index_lt AllOrd x.1))

/-- Rocq: `Notation.BachmannImproper.BS_all_order_type_BH`. -/
theorem BS_all_order_type_BH : AllOrd ≈ BachmannHoward := equiv_trans BS_all_order_type BHO1_BachmannHoward

end BachmannNotation

end ConstructiveOrdinals
