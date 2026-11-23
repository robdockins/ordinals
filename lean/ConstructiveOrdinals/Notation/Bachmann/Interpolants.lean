import ConstructiveOrdinals.Notation.Bachmann.Normalize
import ConstructiveOrdinals.Notation.Bachmann.Cantor
import ConstructiveOrdinals.Notation.Interpolants

/-!
# Interpolants for the Bachmann notation

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

Every normal notation has interpolants: each ordinal below it is bounded by a
smaller normal notation which has interpolants in turn. Under excluded middle
this means that every ordinal below a notation is denoted by a normal
notation. The proof has a semantic half (`cfe_interp`/`bphi_interp`:
everything below `φ_T(u)` lies below `1+u` or below a finite composition of
the components of `⟦T⟧`) and a syntactic half (`cover`: each component is
sandwiched, up to `bsub`, between components given by normal notations, i.e.
syntactic fundamental sequences).

Ported from the Rocq file `Notation/BachmannInterpolants.v`.

Lean notes:

- Rocq's abbreviation `HI` is the abbrev `HI`.
- Rocq rewrites the shapes of children (`badd_small_cases`, `mul_small_form`,
  …); here the equations are applied with `bsub_eq_l`/`bsub_eq_r`.
- `notation_KHI` is proved by the mutual recursions `notation_KHI_S` and
  `notation_KHI_I` (Rocq uses the combined scheme `BNotation_mut`).
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx Interpolants

/-- `HI z`: `z` has interpolants among the normal notations (the Rocq
abbreviation `HI`). -/
abbrev HI (z : Ordinal.{0}) : Prop := HasInterpolants BS_denote BS_nf z

/-- Rocq: `Notation.BachmannInterpolants.HI_zero`. -/
theorem HI_zero : HI 0 :=
  (has_interpolants_unfold 0).2 fun i hi => absurd (lt_of_le_of_lt (zero_least i) hi) (lt_irrefl 0)

/-- Rocq: `Notation.BachmannInterpolants.HI_below`. -/
theorem HI_below (z γ : Ordinal.{0}) (H : HI z) (Hγ : γ < z) :
    ∃ n, BS_nf n ∧ HI (BS_denote n) ∧ γ ≤ BS_denote n ∧ BS_denote n < z :=
  let ⟨n, H1, H2, H3, H4⟩ := (has_interpolants_unfold z).1 H γ Hγ
  ⟨n, H1, H4, H2, H3⟩

/-- Rocq: `Notation.BachmannInterpolants.HI_succ`. -/
theorem HI_succ (m : BSmall) (Hm : BS_nf m) (H : HI (BS_denote m)) : HI (succ (BS_denote m)) :=
  (has_interpolants_unfold _).2 fun _ hi =>
    let ⟨_, h⟩ := lt_elim hi
    ⟨m, Hm, h, succ_lt _, H⟩

/-- Rocq: `Notation.BachmannInterpolants.BS_onePlus`. -/
def BS_onePlus (a : BSmall) : BSmall := smartN BIZ a

/-- Rocq: `Notation.BachmannInterpolants.BS_onePlus_reflects`. -/
theorem BS_onePlus_reflects : Reflects BSmall BS_denote BS_nf (.ord ==> .ord) (fun x => 1 + x) BS_onePlus :=
  fun _ a ⟨Hx, Ha⟩ =>
    ⟨equiv_trans (add_congr (equiv_refl 1) Hx)
        (equiv_trans (equiv_symm (BS_denote_onePlus a)) (equiv_symm (smartN_equal BIZ a trivial Ha))),
      smartN_nf BIZ a trivial Ha⟩

/-- Rocq: `Notation.BachmannInterpolants.HI_onePlus`. -/
theorem HI_onePlus (x : Ordinal.{0}) (H : HI x) : HI (1 + x) :=
  onePlus_interpolants BZ ⟨equiv_refl _, trivial⟩ BS_onePlus BS_onePlus_reflects x H

/-- Rocq: `Notation.BachmannInterpolants.HI_eq`. -/
theorem HI_eq (x y : Ordinal.{0}) (H : x ≈ y) : HI x → HI y := (has_interpolants_eq_mor H).1

/-- Rocq: `Notation.BachmannInterpolants.HI_one`. -/
theorem HI_one : HI (BS_denote BS_one) :=
  HI_eq (1 + 0) _ (equiv_trans (add_zero 1) (equiv_symm BS_one_denote)) (HI_onePlus 0 HI_zero)

/-! ## Syntactic covers of the children

`Ω^e·0` is not a proper index term; `smartC` drops a zero coefficient. -/

/-- Rocq: `Notation.BachmannInterpolants.smartC`. -/
def smartC (e : BIdx) (c : BSmall) (r : BIdx) : BIdx :=
  match c with
  | BZ => r
  | BN T y => BIC e (BN T y) r

/-- Rocq: `Notation.BachmannInterpolants.smartC_bequiv`. -/
theorem smartC_bequiv (e : BIdx) (c : BSmall) (r : BIdx) : BEquiv (BI_denote (smartC e c r)) (BI_denote (BIC e c r)) :=
  match c with
  | BZ => bequiv_trans (bequiv_sym (bequiv_badd_zero_l _))
      (bequiv_badd _ _ _ _ ⟨bsub_bzero_l _, bsub_mul_zero _⟩ (bequiv_refl _))
  | BN _ _ => bequiv_refl _

/-- Rocq: `Notation.BachmannInterpolants.smartC_nf`. -/
theorem smartC_nf (e : BIdx) (c : BSmall) (r : BIdx) (He : BI_nf e) (Hc : BS_nf c) (Hr : BI_nf r) (Hl : lead_below r e) :
    BI_nf (smartC e c r) :=
  match c, Hc with
  | BZ, _ => Hr
  | BN T y, Hc => ⟨He, Hc, BS_pos T y, Hr, Hl⟩

/-- Rocq: `Notation.BachmannInterpolants.Kin_smartC`. -/
theorem Kin_smartC (k : BSmall) (e : BIdx) (c : BSmall) (r : BIdx) : Kin k (smartC e c r) → Kin k (BIC e c r) :=
  match c with
  | BZ => fun h => .inr (.inr h)
  | BN _ _ => id

/-- Rocq: `Notation.BachmannInterpolants.ilt_smartC`. -/
theorem ilt_smartC (e : BIdx) (c : BSmall) (r T0 : BIdx) (H1 : ilt (BIC e c r) T0) (H2 : ilt r T0) :
    ilt (smartC e c r) T0 :=
  match c, H1 with
  | BZ, _ => H2
  | BN _ _, H1 => H1

/-- Rocq: `Notation.BachmannInterpolants.ilt_trans`. -/
theorem ilt_trans {a b d : BIdx} (H : ilt a b) (H' : ilt b d) : ilt a d := by
  induction H generalizing d with
  | nil => cases H' <;> exact .nil _ _ _
  | exp e _ _ _ _ _ Hee IH =>
    cases H' with
    | exp _ _ _ _ _ _ H1 => exact .exp _ _ _ _ _ _ (IH H1)
    | coef _ _ _ _ _ _ H1 _ => exact .exp _ _ _ _ _ _ (ilt_ieq Hee (ieq_refl e) H1)
    | tail _ _ _ _ _ _ H1 _ _ => exact .exp _ _ _ _ _ _ (ilt_ieq Hee (ieq_refl e) H1)
  | coef _ _ _ _ _ _ Hee Hcc =>
    cases H' with
    | exp _ _ _ e2 _ _ H1 => exact .exp _ _ _ _ _ _ (ilt_ieq H1 (ieq_sym Hee) (ieq_refl e2))
    | coef _ _ _ _ _ _ H1 H2 => exact .coef _ _ _ _ _ _ (ieq_trans Hee H1) (lt_trans Hcc H2)
    | tail _ _ _ _ _ _ H1 H2 _ => exact .coef _ _ _ _ _ _ (ieq_trans Hee H1) (lt_of_lt_of_le Hcc H2.le)
  | tail _ _ _ _ _ _ Hee Hcc _ IH =>
    cases H' with
    | exp _ _ _ e2 _ _ H1 => exact .exp _ _ _ _ _ _ (ilt_ieq H1 (ieq_sym Hee) (ieq_refl e2))
    | coef _ _ _ _ _ _ H1 H2 => exact .coef _ _ _ _ _ _ (ieq_trans Hee H1) (lt_of_le_of_lt Hcc.le H2)
    | tail _ _ _ _ _ _ H1 H2 H3 => exact .tail _ _ _ _ _ _ (ieq_trans Hee H1) (equiv_trans Hcc H2) (IH H3)

/-- Rocq: `Notation.BachmannInterpolants.lead_below_ilt`. -/
theorem lead_below_ilt (r' r e : BIdx) (H : ilt r' r) (Hl : lead_below r e) : lead_below r' e := by
  cases H with
  | nil => exact trivial
  | exp _ _ _ _ _ _ H => exact ilt_trans H Hl
  | coef _ _ _ _ _ _ H _ => exact ilt_ieq (Hl : ilt _ e) (ieq_sym H) (ieq_refl e)
  | tail _ _ _ _ _ _ H _ _ => exact ilt_ieq (Hl : ilt _ e) (ieq_sym H) (ieq_refl e)

/-- Rocq: `Notation.BachmannInterpolants.KHI`. -/
def KHI (T : BIdx) : Prop := ∀ k, Kin k T → HI (BS_denote k)

/-! Coefficient tracking for covers: a cover's coefficients stay below any
infinite `z` that bounds the coefficients of `T₀` in the `Kend` sense. -/

/-- Rocq: `Notation.BachmannInterpolants.Kend_rest`. -/
theorem Kend_rest (z : Ordinal.{0}) (e : BIdx) (c : BSmall) (r : BIdx) (Hne : r ≠ BIZ) (H : Kend z (BIC e c r)) :
    Klt z e ∧ BS_denote c < z ∧ Kend z r :=
  match r, Hne, H with
  | BIZ, Hne, _ => absurd rfl Hne
  | BIC _ _ _, _, H => H

/-- Rocq: `Notation.BachmannInterpolants.Klt_smartC_coef`. -/
theorem Klt_smartC_coef (z : Ordinal.{0}) (e : BIdx) (c : BSmall) (r : BIdx) (n : BSmall) (R : BIdx)
    (H : Kend z (BIC e c r)) (Hn : BS_denote n < BS_denote c) (HR : Klt z R) : Klt z (smartC e n R) :=
  match n, Hn with
  | BZ, _ => HR
  | BN T y, Hn => let ⟨He, Hc⟩ := Kend_coef z e c r (BN T y) H Hn (BS_pos T y); ⟨He, Hc, HR⟩

/-- Rocq: `Notation.BachmannInterpolants.Klt_smartC`. -/
theorem Klt_smartC (z : Ordinal.{0}) (e : BIdx) (d : BSmall) (r : BIdx) :
    Klt z e → BS_denote d < z → Klt z r → Klt z (smartC e d r) :=
  match d with
  | BZ => fun _ _ h => h
  | BN _ _ => fun h1 h2 h3 => ⟨h1, h2, h3⟩

/-- Rocq: `Notation.BachmannInterpolants.Kend_cons`. -/
theorem Kend_cons (z : Ordinal.{0}) (e : BIdx) (c : BSmall) (r : BIdx) (He : Klt z e) (Hc : BS_denote c < z)
    (Hr : Kend z r) : Kend z (BIC e c r) :=
  match r, Hr with
  | BIZ, _ => .inl ⟨He, le_of_lt Hc⟩
  | BIC _ _ _, Hr => ⟨He, Hc, Hr⟩

/-- Rocq: `Notation.BachmannInterpolants.Kend_smartC_coef`. -/
theorem Kend_smartC_coef (z : Ordinal.{0}) (e : BIdx) (c : BSmall) (r : BIdx) (n : BSmall) (R : BIdx)
    (H : Kend z (BIC e c r)) (Hn : BS_denote n < BS_denote c) (HR : Kend z R) : Kend z (smartC e n R) :=
  match n, Hn with
  | BZ, _ => HR
  | BN T y, Hn => let ⟨He, Hc⟩ := Kend_coef z e c r (BN T y) H Hn (BS_pos T y); Kend_cons z e _ R He Hc HR

/-- Rocq: `Notation.BachmannInterpolants.Kend_smartC_end`. -/
theorem Kend_smartC_end (z : Ordinal.{0}) (e : BIdx) (x : BSmall) (He : Klt z e) (Hx : BS_denote x ≤ z) :
    Kend z (smartC e x BIZ) :=
  match x, Hx with
  | BZ, _ => trivial
  | BN _ _, Hx => .inl ⟨He, Hx⟩

/-- Rocq: `Notation.BachmannInterpolants.ilt_ne`. -/
theorem ilt_ne (r' r : BIdx) (H : ilt r' r) : r ≠ BIZ := by
  intro E
  subst E
  cases H

/-- Rocq: `Notation.BachmannInterpolants.oinf_one`. -/
theorem oinf_one (z : Ordinal.{0}) (Hz : OInf z) : 1 < z := lt_of_lt_of_le (succ_lt 1) (Hz 2)

/-- Every small child of `⟦T₀⟧` lies, up to `bsub`, below a normal index `T`
which lies below another small child; every Ω-family member at a notation
lies below a normal index which lies below another family's member at the
same argument. These are Bachmann's fundamental sequences up to `bsub` in
both directions. Rocq: `Notation.BachmannInterpolants.icov`. -/
def icov (T0 : BIdx) : Prop :=
  (∀ a, ∃ T, BI_nf T ∧ KHI T ∧ ilt T T0 ∧ (∀ z, OInf z → Kend z T0 → Klt z T) ∧
    bsub (bsmallSz (BI_denote T0) a) (BI_denote T) ∧ ∃ a', bsub (BI_denote T) (bsmallSz (BI_denote T0) a')) ∧
  (∀ d x, BS_nf x → HI (BS_denote x) → ∃ T, BI_nf T ∧ KHI T ∧ ilt T T0 ∧
    (∀ z, OInf z → Kend z T0 → BS_denote x ≤ z → Kend z T) ∧
    bsub (bbigSz (BI_denote T0) d (BS_denote x)) (BI_denote T) ∧
    ∃ d', bsub (BI_denote T) (bbigSz (BI_denote T0) d' (BS_denote x)))

/-- Rocq: `Notation.BachmannInterpolants.KHI_cons`. -/
theorem KHI_cons (e : BIdx) (c : BSmall) (r : BIdx) (H : KHI (BIC e c r)) : KHI e ∧ HI (BS_denote c) ∧ KHI r :=
  ⟨fun k hk => H k (.inl hk), H c (.inr (.inl rfl)), fun k hk => H k (.inr (.inr hk))⟩

/-- Rocq: `Notation.BachmannInterpolants.KHI_intro`. -/
theorem KHI_intro (e : BIdx) (c : BSmall) (r : BIdx) (H1 : KHI e) (H2 : HI (BS_denote c)) (H3 : KHI r) :
    KHI (BIC e c r) := fun k hk =>
  match hk with
  | .inl h => H1 k h
  | .inr (.inl h) => h ▸ H2
  | .inr (.inr h) => H3 k h

/-- Rocq: `Notation.BachmannInterpolants.KHI_smartC`. -/
theorem KHI_smartC (e : BIdx) (c : BSmall) (r : BIdx) (H1 : KHI e) (H2 : HI (BS_denote c)) (H3 : KHI r) :
    KHI (smartC e c r) := fun k hk => KHI_intro e c r H1 H2 H3 k (Kin_smartC k e c r hk)

/-- Rocq: `Notation.BachmannInterpolants.KHI_nil`. -/
theorem KHI_nil : KHI BIZ := fun _ h => h.elim

/-- A coefficient approximated from below by a notation `n`, itself below an
immediate predecessor of the coefficient. Rocq: `Notation.BachmannInterpolants.coef_approx`. -/
theorem coef_approx (c : BSmall) (γ : Ordinal.{0}) (H : HI (BS_denote c)) (Hγ : γ < BS_denote c) :
    ∃ n, BS_nf n ∧ HI (BS_denote n) ∧ γ ≤ BS_denote n ∧ BS_denote n < BS_denote c ∧
      ∃ j, BS_denote n ≤ (BS_denote c).size j :=
  let ⟨n, Hn, HIn, H1, H2⟩ := HI_below _ _ H Hγ
  ⟨n, Hn, HIn, H1, H2, lt_elim H2⟩

/-- Rocq: `Notation.BachmannInterpolants.bsub_term_mono`. -/
theorem bsub_term_mono (e e' : BOrd.{0}) (γ n : Ordinal.{0}) (He : bsub e e') (Hγ : γ ≤ n) :
    bsub (bmul (bexpΩ e) (embed γ)) (bmul (bexpΩ e') (embed n)) :=
  bsub_trans (bsub_bmul_r _ _ _ (bsub_embed _ _ Hγ)) (bsub_bmul_l _ _ (bsub_bexpΩ _ _ He) _)

theorem bsub_eq_l {x x' y : BOrd.{0}} (E : x = x') (h : bsub x' y) : bsub x y :=
  Eq.mpr (congrArg (fun t => bsub t y) E) h

theorem bsub_eq_r {x y y' : BOrd.{0}} (E : y = y') (h : bsub x y') : bsub x y :=
  Eq.mpr (congrArg (fun t => bsub x t) E) h

theorem lead_below_smartC (e e' : BIdx) (x : BSmall) (H : ilt e' e) : lead_below (smartC e' x BIZ) e :=
  match x with
  | BZ => trivial
  | BN _ _ => H

/-- Rocq: `Notation.BachmannInterpolants.cover`. -/
theorem cover : ∀ T0 : BIdx, BI_nf T0 → KHI T0 → icov T0
  | BIZ, _, _ => ⟨fun a => (nomatch a), fun d => (nomatch d)⟩
  | BIC e c r, ⟨He, Hc, Hc0, Hr, Hl⟩, HK => by
    obtain ⟨HKe, HKc, HKr⟩ := KHI_cons _ _ _ HK
    obtain ⟨Se, Fe⟩ := cover e He HKe
    obtain ⟨Sr, Fr⟩ := cover r Hr HKr
    have Hnf : ∀ n x, BS_nf n → BI_nf x → lead_below x e → BI_nf (smartC e n x) :=
      fun n x Hn Hx Hlx => smartC_nf e n x He Hn Hx Hlx
    have Hilt : ∀ n x, BS_denote n < BS_denote c → ilt x (BIC e c r) → ilt (smartC e n x) (BIC e c r) :=
      fun n x Hn Hx => ilt_smartC e n x _ (.coef _ _ _ _ _ _ (ieq_refl e) Hn) Hx
    refine ⟨fun a => ?_, fun d x Hx HIx => ?_⟩
    · match badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a with
      | .inl ⟨a', Ea⟩ =>
        obtain ⟨γ, Hγ, k, Hk⟩ := mul_small_form (bexpΩ (BI_denote e)) (BS_denote c) a'
        obtain ⟨n, Hn, HIn, Hγn, Hnc, j, Hj⟩ := coef_approx c γ HKc Hγ
        have E3 := Ea.trans (Hk.trans (congrArg _ (bexpΩ_small_all _ k)))
        obtain ⟨t0, Ht0⟩ := bexpΩ_small_zero (BI_denote e)
        obtain ⟨a0, Ha0⟩ := mul_small_back (bexpΩ (BI_denote e)) (BS_denote c) j t0
        obtain ⟨a'', Ha''⟩ := badd_small_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a0
        exact ⟨smartC e n BIZ, Hnf n BIZ Hn trivial trivial, KHI_smartC e n BIZ HKe HIn KHI_nil,
          Hilt n BIZ Hnc (.nil _ _ _), fun z _ HKz => Klt_smartC_coef z e c r n BIZ HKz Hnc trivial,
          bsub_eq_l E3 (bsub_trans (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hγn) bzero)
            (smartC_bequiv e n BIZ).2),
          a'', bsub_eq_r (Ha''.trans (Ha0.trans (congrArg _ Ht0)))
            (bsub_trans (smartC_bequiv e n BIZ).1 (bsub_badd_l _ _ (bsub_term_mono _ _ _ _ (bsub_refl _) Hj) bzero))⟩
      | .inr ⟨b, Eb⟩ =>
        obtain ⟨r', Hr', HKr', Hlt, Htr, Hlo, b', Hup⟩ := Sr b
        obtain ⟨a'', Ha''⟩ := badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) b'
        exact ⟨BIC e c r', ⟨He, Hc, Hc0, Hr', lead_below_ilt r' r e Hlt Hl⟩, KHI_intro e c r' HKe HKc HKr',
          .tail _ _ _ _ _ _ (ieq_refl e) (equiv_refl _) Hlt,
          fun z Hz HKz => let ⟨H1, H2, H3⟩ := Kend_rest z e c r (ilt_ne _ _ Hlt) HKz; ⟨H1, H2, Htr z Hz H3⟩,
          bsub_eq_l Eb (bsub_badd_r _ _ _ Hlo), a'', bsub_eq_r Ha'' (bsub_badd_r _ _ _ Hup)⟩
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
          refine ⟨smartC e n (smartC e' x BIZ),
            Hnf n _ Hn (smartC_nf e' x BIZ He' Hx trivial trivial) (lead_below_smartC e e' x Hlte),
            KHI_smartC e n _ HKe HIn (KHI_smartC e' x BIZ HKe' HIx KHI_nil),
            Hilt n _ Hnc (ilt_smartC e' x BIZ _ (.exp _ _ _ _ _ _ Hlte) (.nil _ _ _)),
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
          obtain ⟨t0, Ht0⟩ := bexpΩ_big_b (BI_denote e) de'
          obtain ⟨d0, Hd0⟩ := mul_big_back (bexpΩ (BI_denote e)) (BS_denote c) j t0
          obtain ⟨d'', Hd''⟩ := badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d0
          refine ⟨smartC e n (BIC e' BS_one BIZ),
            Hnf n _ Hn ⟨He', BS_one_nf, BS_pos _ _, trivial, trivial⟩ Hlte,
            KHI_smartC e n _ HKe HIn (KHI_intro e' BS_one BIZ HKe' HI_one KHI_nil),
            Hilt n _ Hnc (.exp _ _ _ _ _ _ Hlte),
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
        obtain ⟨r', Hr', HKr', Hlt, Htr, Hlo, d'', Hup⟩ := Fr d' x Hx HIx
        obtain ⟨d0, Hd0⟩ := badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d''
        exact ⟨BIC e c r', ⟨He, Hc, Hc0, Hr', lead_below_ilt r' r e Hlt Hl⟩, KHI_intro e c r' HKe HKc HKr',
          .tail _ _ _ _ _ _ (ieq_refl e) (equiv_refl _) Hlt,
          fun z Hz HKz Hxz => let ⟨H1, H2, H3⟩ := Kend_rest z e c r (ilt_ne _ _ Hlt) HKz;
            Kend_cons z e c r' H1 H2 (Htr z Hz H3 Hxz),
          bsub_eq_l (Ed _) (bsub_badd_r _ _ _ Hlo), d0, bsub_eq_r (Hd0 _) (bsub_badd_r _ _ _ Hup)⟩

/-! ## Interpolation

By induction on the index tree (in the well-founded order `blt`) and then on
the argument: below `φ_T(u)`, everything lies below `1+u` (handled by the
interpolants of `1+x`), or below a word in `f` and the components applied to
0 or to the successor of an earlier value. Each component is replaced by the
`φ` of a covering normal index, which takes notations to notations, has
interpolants by induction (its tree lies below a child of `⟦T⟧`), and stays
below `φ_T(u)` because it lies below another component. -/

/-- Rocq: `Notation.BachmannInterpolants.onePlus_mono`. -/
theorem onePlus_mono : ∀ x y : Ordinal.{0}, x ≤ y → 1 + x ≤ 1 + y := onePlus_normal.monotone

/-- Rocq: `Notation.BachmannInterpolants.interp_aux`. -/
theorem interp_aux : ∀ (U : BOrd.{0}) (T : BIdx), BI_nf T → KHI T → ble (BI_denote T) U →
    ∀ u, Complete u → HI u → HI (bphi (fun x => 1 + x) (BI_denote T) u) := by
  intro U
  refine blt_wf.induction (C := fun U => ∀ (T : BIdx), BI_nf T → KHI T → ble (BI_denote T) U →
    ∀ u, Complete u → HI u → HI (bphi (fun x => 1 + x) (BI_denote T) u)) U ?_
  intro U IHU T HT HK HU u
  refine ltRec (motive := fun u => Complete u → HI u → HI (bphi (fun x => 1 + x) (BI_denote T) u)) ?_ u
  intro u IHu Hu HIu
  obtain ⟨CS, CF⟩ := cover T HT HK
  have Hg := BI_good T
  have Hfam := BI_bfam T
  have Hcomp : ∀ T', BI_nf T' → KHI T' → blt (BI_denote T') (BI_denote T) →
      ∀ m, BS_nf m → HI (BS_denote m) → HI (bphi (fun x => 1 + x) (BI_denote T') (BS_denote m)) :=
    fun T' HT' HK' Hlt m _ HIm =>
      IHU (BI_denote T') (blt_le_trans Hlt HU) T' HT' HK' (ble_refl _) _ (BS_complete m) HIm
  refine (has_interpolants_unfold _).2 fun i Hi => ?_
  match bphi_interp _ onePlus_normal (BI_denote T) u i Hg Hu Hi with
  | .inl Hi1 =>
    obtain ⟨n, Hn, HIn, H1, H2⟩ := HI_below _ _ (HI_onePlus u HIu) Hi1
    exact ⟨n, Hn, H1, lt_of_lt_of_le H2 (bphi_ge_f _ _ u), HIn⟩
  | .inr ⟨Hinh, o, w, Hiw, _⟩ =>
    obtain ⟨Hf1, Hf2, Hf3⟩ := bfix_value_full _ onePlus_normal (BI_denote T) u Hg Hinh Hu
    have Hchain : ∀ (w : List (Option (bsmall (BI_denote T) ⊕ bbig (BI_denote T)))) x0 m, BS_nf m →
        x0 ≤ BS_denote m → BS_denote m ≤ bphi (fun x => 1 + x) (BI_denote T) u → HI (BS_denote m) →
        ∃ m', BS_nf m' ∧
          wev (fun x => 1 + x) _ (bphi_fam (fun x => 1 + x) (bsmallSz (BI_denote T)) (bbigSz (BI_denote T))) w x0 ≤
            BS_denote m' ∧ BS_denote m' ≤ bphi (fun x => 1 + x) (BI_denote T) u ∧ HI (BS_denote m') := by
      intro w0
      induction w0 with
      | nil => exact fun _ m Hm L0 U0 HI0 => ⟨m, Hm, L0, U0, HI0⟩
      | cons o w0 IHw =>
        intro x0 m Hm L0 U0 HI0
        obtain ⟨m1, Hm1, L1, U1, HI1⟩ := IHw x0 m Hm L0 U0 HI0
        match o with
        | some (.inl a) =>
          obtain ⟨T', HT', HK', _, _, Hlo, a', Hup⟩ := CS a
          have E := smartN_equal T' m1 HT' Hm1
          refine ⟨smartN T' m1, smartN_nf T' m1 HT' Hm1, ?_, ?_, ?_⟩
          · exact le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a)).1 _ _ L1)
              (le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam T')).2 _ Hlo _) E.ge)
          · exact le_trans E.le (le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a')).2 _ Hup _)
              (le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a')).1 _ _ U1) (Hf2 a')))
          · exact HI_eq _ _ (equiv_symm E) (Hcomp T' HT' HK' (bsub_child_blt _ _ (.inl a') Hup) m1 Hm1 HI1)
        | some (.inr c) =>
          obtain ⟨T', HT', HK', _, _, Hlo, c', Hup⟩ := CF c m1 Hm1 HI1
          have E := smartN_equal T' BZ HT' trivial
          refine ⟨smartN T' BZ, smartN_nf T' BZ HT' trivial, ?_, ?_, ?_⟩
          · exact le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c _)).2 _ (bfam_fam _ Hfam c _ _ L1) 0)
              (le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam T')).2 _ Hlo 0) E.ge)
          · exact le_trans E.le (le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c' _)).2 _ Hup 0)
              (le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c' _)).2 _ (bfam_fam _ Hfam c' _ _ U1) 0)
                (Hf3 c')))
          · exact HI_eq _ _ (equiv_symm E)
              (Hcomp T' HT' HK' (bsub_child_blt _ _ (.inr (c', BS_denote m1)) Hup) BZ trivial HI_zero)
        | none =>
          obtain ⟨E1, N1⟩ := BS_onePlus_reflects (BS_denote m1) m1 ⟨equiv_refl _, Hm1⟩
          exact ⟨BS_onePlus m1, N1, le_trans (onePlus_mono _ _ L1) E1.le,
            le_trans E1.ge (le_trans (onePlus_mono _ _ U1) Hf1), HI_eq _ _ E1 (HI_onePlus _ HI1)⟩
    have Hstart : ∃ m, BS_nf m ∧
        (match (generalizing := false) o with
          | none => 0
          | some j => succ (bphi (fun x => 1 + x) (BI_denote T) (u j))) ≤ BS_denote m ∧
        BS_denote m ≤ bphi (fun x => 1 + x) (BI_denote T) u ∧ HI (BS_denote m) := by
      match o with
      | some j =>
        obtain ⟨n, Hn, HIn, H1, H2⟩ := HI_below _ _ HIu (index_lt u j)
        have Hm0 := smartN_nf T n HT Hn
        have E0 := smartN_equal T n HT Hn
        obtain ⟨E1, N1⟩ := BS_succ_reflects (BS_denote (smartN T n)) (smartN T n) ⟨equiv_refl _, Hm0⟩
        exact ⟨BS_succ (smartN T n), N1,
          le_trans (succ_monotone (le_trans ((bphi_mono_index _ onePlus_mono _ Hfam).1 _ _ H1) E0.ge)) E1.le,
          le_trans E1.ge (succ_least (lt_of_le_of_lt E0.le ((BI_normal T).increasing _ _ Hu H2))),
          HI_eq _ _ E1 (HI_succ _ Hm0 (HI_eq _ _ (equiv_symm E0) (IHu (BS_denote n) H2 (BS_complete n) HIn)))⟩
      | none => exact ⟨BZ, trivial, le_refl _, zero_least _, HI_zero⟩
    obtain ⟨m, Hm, L0, U0, HI0⟩ := Hstart
    obtain ⟨m', _, L, U', HI'⟩ := Hchain w _ m Hm L0 U0 HI0
    obtain ⟨n, Hn, HIn, H1, H2⟩ := HI_below _ i HI' (lt_of_lt_of_le Hiw L)
    exact ⟨n, Hn, H1, lt_of_lt_of_le H2 U', HIn⟩

mutual
theorem notation_KHI_S : ∀ x : BSmall, BS_nf x → HI (BS_denote x)
  | BZ, _ => HI_zero
  | BN T y, ⟨HT, Hy, _⟩ =>
    interp_aux (BI_denote T) T HT (notation_KHI_I T HT) (ble_refl _) _ (BS_complete y) (notation_KHI_S y Hy)

theorem notation_KHI_I : ∀ T : BIdx, BI_nf T → KHI T
  | BIZ, _ => KHI_nil
  | BIC e c r, ⟨He, Hc, _, Hr, _⟩ =>
    KHI_intro e c r (notation_KHI_I e He) (notation_KHI_S c Hc) (notation_KHI_I r Hr)
end

/-- Rocq: `Notation.BachmannInterpolants.notation_KHI`. -/
theorem notation_KHI : (∀ x, BS_nf x → HI (BS_denote x)) ∧ ∀ T, BI_nf T → KHI T :=
  ⟨notation_KHI_S, notation_KHI_I⟩

/-- Rocq: `Notation.BachmannInterpolants.BS_has_all_interpolants`. -/
theorem BS_has_all_interpolants : HasAllInterpolants BS_denote BS_nf := notation_KHI_S

/-- Rocq: `Notation.BachmannInterpolants.BS_has_enough_notations`. -/
theorem BS_has_enough_notations (EM : ExcludedMiddle) : HasEnoughNotations BS_denote BS_nf :=
  has_interpolants_has_enough_notations EM BS_has_all_interpolants

end BachmannNotation

end ConstructiveOrdinals
