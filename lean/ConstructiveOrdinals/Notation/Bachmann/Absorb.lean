import ConstructiveOrdinals.Notation.Bachmann.Interpolants
import ConstructiveOrdinals.Notation.CantorProduct

/-!
# Offsets and absorption of the leading summand

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

## The offset of a threshold

For a normal index `R` with a nonzero leading exponent and a normal notation
`m`, `BS_offset R m` is the least `t` with `m < φ_R(t)`: the least value of
`φ_R` above `m` is `φ_R(t)`. It is computed by recursion on `m`: if
`m < φ_R(0)` then `t = 0`; otherwise `m = φ_{T'}(y')` with

- `T' = R`: `t = y' + 1`;
- `T' > R`: if `R`'s coefficients lie below `m`, `m` is a fixpoint of `φ_R`
  and `t = m + 1`; otherwise `m = φ_R(0)` and `t = 1`;
- `T' < R`: the values of `φ_R` above `max(y', coefficients of T')` are the
  values above `m`, so recurse on that maximum.

Ported from the Rocq file `Notation/BachmannAbsorb.v`.

Lean notes:

- Rocq's abbreviation `PHI R` is the local notation `Φ[R]`.
- The section variables of `offset`, `absorb` and `abs_all` become explicit
  arguments. The section-local `Let`s become `have`s or lemmas (Rocq:
  `Notation.BachmannAbsorb.HRpos`, `Notation.BachmannAbsorb.Hinh`,
  `Notation.BachmannAbsorb.Hvfix`, `Notation.BachmannAbsorb.Hvc`,
  `Notation.BachmannAbsorb.Hinc`, `Notation.BachmannAbsorb.P`,
  `Notation.BachmannAbsorb.X`, `Notation.BachmannAbsorb.n0`); `succ_case` is
  a lemma.
- The induction on denotations (Rocq's `size_induction`) is `BS_denote_ind`.
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx

/-- `φ_R` at the base `1+x`: the Rocq abbreviation `PHI R`. -/
local notation "Φ[" R "]" => bphi (fun x => 1 + x) (BI_denote R)

/-- Induction on the denotation of a notation. -/
theorem BS_denote_ind {motive : BSmall → Prop} (h : ∀ y, (∀ n, BS_denote n < BS_denote y → motive n) → motive y)
    (y : BSmall) : motive y :=
  ltRec (motive := fun o => ∀ y, BS_denote y ≤ o → motive y)
    (fun _ ih y hy => h y fun n hn => ih (BS_denote n) (lt_of_lt_of_le hn hy) n (le_refl _))
    (BS_denote y) y (le_refl _)

theorem bphi_eq_le {x y : BOrd.{0}} {a b : Ordinal.{0}} (E : x = y) (h : bphi (fun x => 1 + x) y a ≤ b) :
    bphi (fun x => 1 + x) x a ≤ b :=
  Eq.mpr (congrArg (fun t => bphi (fun x => 1 + x) t a ≤ b) E) h

/-- Rocq: `Notation.BachmannAbsorb.lead_big`. -/
def lead_big (R : BIdx) : Prop :=
  match R with
  | BIC e _ _ => e ≠ BIZ
  | BIZ => False

theorem lead_big_ne (R : BIdx) (H : lead_big R) : R ≠ BIZ := by
  intro E
  subst E
  exact H

/-- Rocq: `Notation.BachmannAbsorb.Ω_le_R`. -/
theorem Ω_le_R (R : BIdx) (HR : BI_nf R) (Hl : lead_big R) : bsub bOmega (BI_denote R) :=
  match R, HR, Hl with
  | BIZ, _, h => h.elim
  | BIC BIZ _ _, _, h => absurd rfl h
  | BIC (BIC e1 c1 r1) _ _, ⟨He, _, Hc0, _⟩, _ =>
    let ⟨t⟩ := bsmall_mul_embed_inh (BI_denote e1) (BS_denote c1) He.2.2.1
    let ⟨a, _⟩ := badd_small_l (bmul (bexpΩ (BI_denote e1)) (embed (BS_denote c1))) (BI_denote r1) t
    bsub_trans (bsub_trans (Ω_le_bexp _ a) (bsub_P_Pz _ _ Hc0)) (bsub_le_badd _ _)

/-- Common fixpoints of the components of such an `R` are additively principal.
Rocq: `Notation.BachmannAbsorb.fix_principal`. -/
theorem fix_principal (R : BIdx) (z a : Ordinal.{0}) (HR : BI_nf R) (Hl : lead_big R) (Hz : Complete z)
    (Hfix : BFix (fun x => 1 + x) (BI_denote R) z) (Ha : a < z) : a + z ≤ z :=
  let ⟨j, Hj⟩ := lt_elim Ha
  have Hc := complete_subord Hz j
  le_trans (add_le_add Hj (le_refl z))
    (le_trans (add_le_add (CantorProduct.le_powOmega _) (le_refl z))
      (le_trans (bphi_onePlus_embed _ _ Hc Hz).ge
        (zlt_nest _ onePlus_normal z (embed (z.size j)) (BI_denote R)
          (zlt_mono_r z _ bOmega _ (zlt_embed_Ω z _ (index_lt z j)) (Ω_le_R R HR Hl)) (BI_good R) (BI_bfam R) Hz Hfix)))

/-- Rocq: `Notation.BachmannAbsorb.fix_succ_lt`. -/
theorem fix_succ_lt (R : BIdx) (z a : Ordinal.{0}) (HR : BI_nf R) (Hl : lead_big R) (Hz : Complete z)
    (Hfix : BFix (fun x => 1 + x) (BI_denote R) z) (Ha : a < z) : succ a < z :=
  have Hinf := fix_onePlus_finite _ onePlus_normal z Hz Hfix.1
  lt_of_le_of_lt (le_trans (succ_monotone (le_add_right a 0)) (add_succ a 0).ge)
    (lt_of_lt_of_le (add_lt_add_left a (oinf_one z Hinf)) (fix_principal R z a HR Hl Hz Hfix Ha))

/-- Rocq: `Notation.BachmannAbsorb.off_max`. -/
def off_max (y' : BSmall) (T' : BIdx) : BSmall :=
  match kmax (BI_size T' + BI_size T' + 1) T' with
  | none => y'
  | some k =>
    match BS_compare k y' with
    | .lt => y'
    | .eq => k
    | .gt => k

/-- Rocq: `Notation.BachmannAbsorb.off_max_spec`. -/
theorem off_max_spec (T' : BIdx) (y' : BSmall) (Hm : BS_nf (BN T' y')) :
    BS_nf (off_max y' T') ∧ BS_size (off_max y' T') < BS_size (BN T' y') ∧
      BS_denote (off_max y' T') < BS_denote (BN T' y') ∧
      ∀ z, BS_denote (off_max y' T') < z → BS_denote y' < z ∧ Klt z T' := by
  have Hm' := Hm
  obtain ⟨HT', Hy', Hylt, HK⟩ := Hm'
  have Hk := kmax_spec (BI_size T' + BI_size T' + 1) T' HT' (Nat.lt_succ_self _)
  unfold off_max
  revert Hk
  cases kmax (BI_size T' + BI_size T' + 1) T' with
  | none =>
    intro Hk
    subst Hk
    exact ⟨Hy', size_N_y BIZ y', Hylt, fun _ Hw => ⟨Hw, trivial⟩⟩
  | some k =>
    intro ⟨Hkin, HKle⟩
    dsimp only
    have Hkn := Kin_nf k T' Hkin HT'
    have Hkm : BS_denote k < BS_denote (BN T' y') := Kge_lt _ _ T' (Kin_Kge k T' Hkin) HK
    have Hks : BS_size k < BS_size (BN T' y') := Nat.lt_of_le_of_lt (Kin_size' k T' Hkin) (size_N_T T' y')
    have Hc := BS_compare_correct k y' Hkn Hy'
    revert Hc
    cases BS_compare k y' with
    | lt => intro Hc; exact ⟨Hy', size_N_y _ _, Hylt, fun _ Hw => ⟨Hw, Kle_lt _ _ T' HKle (lt_trans Hc Hw)⟩⟩
    | eq => intro Hc; exact ⟨Hkn, Hks, Hkm, fun _ Hw => ⟨lt_of_le_of_lt Hc.ge Hw, Kle_lt _ _ T' HKle Hw⟩⟩
    | gt => intro Hc; exact ⟨Hkn, Hks, Hkm, fun _ Hw => ⟨lt_trans Hc Hw, Kle_lt _ _ T' HKle Hw⟩⟩

/-- Rocq: `Notation.BachmannAbsorb.offStep`. -/
def offStep (rec : BSmall → BSmall) (R : BIdx) (m : BSmall) : BSmall :=
  match m with
  | BZ => BZ
  | BN T' y' =>
    match cmpI (BI_size T' + BI_size R + 1) T' R with
    | .eq => BS_succ y'
    | .lt => rec (off_max y' T')
    | .gt =>
      match coefs_below (BI_size R + BS_size (BN T' y') + 1) R (BN T' y') with
      | true => BS_succ (BN T' y')
      | false => BS_one

/-- Rocq: `Notation.BachmannAbsorb.offN`. -/
def offN : Nat → BIdx → BSmall → BSmall
  | 0, _, _ => BZ
  | fuel + 1, R, m =>
    match BS_compare m (smartN R BZ) with
    | .lt => BZ
    | .eq => offStep (offN fuel R) R m
    | .gt => offStep (offN fuel R) R m

/-- Rocq: `Notation.BachmannAbsorb.BS_offset`. -/
def BS_offset (R : BIdx) (m : BSmall) : BSmall := offN (BS_size m + 1) R m

/-- Rocq: `Notation.BachmannAbsorb.OffSpec`. -/
def OffSpec (R : BIdx) (m t : BSmall) : Prop :=
  BS_nf t ∧ BS_denote m < Φ[R] (BS_denote t) ∧ BS_denote t < Φ[R] (BS_denote t) ∧
    ∀ z, Complete z → BFix (fun x => 1 + x) (BI_denote R) z → BS_denote m < z → Φ[R] (BS_denote t) ≤ z

/-- Rocq: `Notation.BachmannAbsorb.Hinh_of`. -/
theorem Hinh_of (T : BIdx) (HT : BI_nf T) (Hne : T ≠ BIZ) : Nonempty (bsmall (BI_denote T) ⊕ bbig (BI_denote T)) :=
  match T, HT, Hne with
  | BIZ, _, Hne => absurd rfl Hne
  | BIC e c r, HT, _ => BI_inh e c r HT.2.2.1

/-! ### The offset section: `R` is a normal index with a nonzero leading exponent -/

/-- If `φ_R(a)` lies below `m`, then `φ_R(a+1)` is the least common fixpoint
above `m`. Rocq: `Notation.BachmannAbsorb.succ_case`. -/
theorem succ_case (R : BIdx) (HR : BI_nf R) (HRl : lead_big R) (m : BSmall) (a : Ordinal.{0}) (t : BSmall)
    (Ht : BS_nf t) (Et : BS_denote t ≈ succ a) (Ha : Complete a) (Hle : Φ[R] a ≤ BS_denote m)
    (Hlt : BS_denote m < Φ[R] (succ a)) : OffSpec R m t := by
  have Hinh := Hinh_of R HR (lead_big_ne R HRl)
  have E : Φ[R] (BS_denote t) ≈ Φ[R] (succ a) := ord_eq_normal _ (BI_normal R) _ _ Et
  have Hsa := succ_complete Ha
  refine ⟨Ht, lt_of_lt_of_le Hlt E.ge, ?_, fun z Hz Hfix Hmz => ?_⟩
  · refine lt_of_le_of_lt Et.le (lt_of_lt_of_le ?_ E.ge)
    exact fix_succ_lt R _ a HR HRl ((BI_normal R).complete _ Hsa)
      (bfix_value_full _ onePlus_normal _ _ (BI_good R) Hinh Hsa)
      (lt_of_le_of_lt (normal_inflationary (BI_normal R) a Ha) ((BI_normal R).increasing _ _ Hsa (succ_lt a)))
  · exact le_trans E.le (bphi_succ_le _ onePlus_normal _ z a (BI_good R) Hz Hfix Ha (lt_of_le_of_lt Hle Hmz))

/-- Rocq: `Notation.BachmannAbsorb.offStep_correct`. -/
theorem offStep_correct (R : BIdx) (HR : BI_nf R) (HRl : lead_big R) (rec : BSmall → BSmall) (m : BSmall)
    (Hm : BS_nf m) (Hge : Φ[R] 0 ≤ BS_denote m)
    (IH : ∀ m', BS_nf m' → BS_size m' < BS_size m → OffSpec R m' (rec m')) : OffSpec R m (offStep rec R m) := by
  match m, Hm, Hge, IH with
  | BZ, _, Hge, _ => exact absurd (lt_of_lt_of_le (bphi_nonzero onePlus_normal _ _) Hge) (lt_irrefl _)
  | BN T' y', Hm, Hge, IH =>
    have Hm' := Hm
    obtain ⟨HT', Hy', _, _⟩ := Hm'
    have Hc := (cmp_correct (BI_size T' + BI_size R + 1)).2 T' R (Nat.lt_succ_self _) HT' HR
    show OffSpec R (BN T' y') (match cmpI (BI_size T' + BI_size R + 1) T' R with
      | .eq => BS_succ y'
      | .lt => rec (off_max y' T')
      | .gt =>
        match coefs_below (BI_size R + BS_size (BN T' y') + 1) R (BN T' y') with
        | true => BS_succ (BN T' y')
        | false => BS_one)
    revert Hc
    cases cmpI (BI_size T' + BI_size R + 1) T' R with
    | lt =>
      -- `T' < R`: recurse on the maximum of `y'` and the coefficients of `T'`
      intro Hc
      obtain ⟨Hmx, Hsz, Hlt, Habove⟩ := off_max_spec T' y' Hm
      obtain ⟨Nt, Hm1, Ht1, Hmin⟩ := IH _ Hmx Hsz
      have Lz : ∀ z, Complete z → BFix (fun x => 1 + x) (BI_denote R) z →
          BS_denote (off_max y' T') < z → BS_denote (BN T' y') < z := fun z Hz Hfix Hxz =>
        let ⟨Hyz, HKz⟩ := Habove z Hxz
        have Hinf := fix_onePlus_finite _ onePlus_normal z Hz Hfix.1
        have Hzlt := (nest z Hinf (BI_size T' + 1) T' (Nat.lt_succ_self _) HT' HKz).1 R HR Hc
        lt_of_lt_of_le ((BI_normal T').increasing _ _ Hz Hyz)
          (zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good R) (BI_bfam R) Hz Hfix)
      have Hinh := Hinh_of R HR (lead_big_ne R HRl)
      exact ⟨Nt, Lz _ ((BI_normal R).complete _ (BS_complete _))
          (bfix_value_full _ onePlus_normal _ _ (BI_good R) Hinh (BS_complete _)) Hm1, Ht1,
        fun z Hz Hfix Hmz => Hmin z Hz Hfix (lt_trans Hlt Hmz)⟩
    | eq =>
      -- `T' = R`
      intro Hc
      obtain ⟨E1, N1⟩ := BS_succ_reflects (BS_denote y') y' ⟨equiv_refl _, Hy'⟩
      exact succ_case R HR HRl _ (BS_denote y') _ N1 (equiv_symm E1) (BS_complete y') (bphi_ieq _ _ _ Hc).ge
        (lt_of_le_of_lt (bphi_ieq _ _ _ Hc).le
          ((BI_normal R).increasing _ _ (succ_complete (BS_complete _)) (succ_lt _)))
    | gt =>
      -- `R < T'`
      intro Hc
      have HT'ne : T' ≠ BIZ := by intro E; subst E; cases Hc
      have Hcb := coefs_below_spec (BI_size R + BS_size (BN T' y') + 1) (BN T' y') R
        (fun c Hs Hcn => (cmp_correct _).1 c (BN T' y') (Nat.lt_succ_of_le (Nat.add_le_add_right Hs _)) Hcn Hm) HR
      revert Hcb
      cases coefs_below (BI_size R + BS_size (BN T' y') + 1) R (BN T' y') with
      | true =>
        intro Hcb
        have HK' := Hcb.1 rfl
        have Hz := (nest _ (BN_inf T' y' HT' HT'ne) (BI_size R + 1) R (Nat.lt_succ_self _) HR HK').1 T' HT' Hc
        have Hfix := zlt_value _ onePlus_normal _ _ (BS_denote y') Hz (BI_good T') (BI_bfam T')
          (Hinh_of T' HT' HT'ne) (BS_complete y')
        obtain ⟨E1, N1⟩ := BS_succ_reflects _ _ ⟨equiv_refl _, Hm⟩
        exact succ_case R HR HRl _ (BS_denote (BN T' y')) _ N1 (equiv_symm E1) (BS_complete _) Hfix
          (lt_of_le_of_lt (normal_inflationary (BI_normal R) _ (BS_complete _))
            ((BI_normal R).increasing _ _ (succ_complete (BS_complete _)) (succ_lt _)))
      | false =>
        intro Hcb
        have Hd := dominance R BZ _ (BI_nf_pos R HR) (Hcb.2 rfl)
        exact succ_case R HR HRl _ 0 _ BS_one_nf BS_one_denote zero_complete Hge
          (lt_of_le_of_lt Hd ((BI_normal R).increasing _ _ (succ_complete zero_complete) (succ_lt _)))

/-- Rocq: `Notation.BachmannAbsorb.offN_correct`. -/
theorem offN_correct (R : BIdx) (HR : BI_nf R) (HRl : lead_big R) :
    ∀ (fuel : Nat) (m : BSmall), BS_size m < fuel → BS_nf m → OffSpec R m (offN fuel R m)
  | 0, _, Hsz, _ => absurd Hsz (Nat.not_lt_zero _)
  | fuel + 1, m, Hsz, Hm => by
    have Hm0 := smartN_nf R BZ HR trivial
    have E0 := smartN_equal R BZ HR trivial
    have Hc := BS_compare_correct m _ Hm Hm0
    have IH : ∀ m', BS_nf m' → BS_size m' < BS_size m → OffSpec R m' (offN fuel R m') := fun m' Hm' Hs =>
      offN_correct R HR HRl fuel m' (Nat.lt_of_lt_of_le Hs (Nat.le_of_lt_succ Hsz)) Hm'
    show OffSpec R m (match BS_compare m (smartN R BZ) with
      | .lt => BZ
      | .eq => offStep (offN fuel R) R m
      | .gt => offStep (offN fuel R) R m)
    revert Hc
    cases BS_compare m (smartN R BZ) with
    | lt =>
      intro Hc
      exact ⟨trivial, lt_of_lt_of_le Hc E0.le, bphi_nonzero onePlus_normal _ _,
        fun z Hz Hfix _ => bphi_le_fix _ onePlus_normal _ z (BI_good R) Hz Hfix⟩
    | eq => intro Hc; exact offStep_correct R HR HRl _ m Hm (le_trans E0.ge Hc.ge) IH
    | gt => intro Hc; exact offStep_correct R HR HRl _ m Hm (le_trans E0.ge (le_of_lt Hc)) IH

/-- Rocq: `Notation.BachmannAbsorb.BS_offset_correct`. -/
theorem BS_offset_correct (R : BIdx) (HR : BI_nf R) (HRl : lead_big R) (m : BSmall) (Hm : BS_nf m) :
    OffSpec R m (BS_offset R m) :=
  offN_correct R HR HRl _ m (Nat.lt_succ_self _) Hm

/-! ### Examples, by computation -/

/-- Above 1, the first ε-number is `ε₀ = φ_Ω(0)`. -/
example : BS_offset BI_Ω BS_one = BZ := rfl

/-- Above `ε₀ = φ_Ω(0)`, the next one is `φ_Ω(1)`. -/
example : BS_offset BI_Ω (BN BI_Ω BZ) = BS_succ BZ := rfl

/-- Above `ε₀ + 1 = ω^{ε₀} + 1`, still `φ_Ω(1)`. -/
example : BS_offset BI_Ω BS_ε0_plus1 = BS_succ BZ := rfl

/-- `φ_{Ω·2}(0)` is a fixpoint of `φ_Ω`, so the least `φ_Ω`-value above it is
`φ_Ω(φ_{Ω·2}(0) + 1)`. -/
example : BS_offset BI_Ω (BN (BIC BI_one (BN BIZ BS_one) BIZ) BZ) =
    BS_succ (BN (BIC BI_one (BN BIZ BS_one) BIZ) BZ) := rfl

/-! ## One absorption step

`P = Ω^e·c` is a normal summand and `R` a normal index whose leading exponent
exceeds `e`. The index `P + R` is improper. Its common fixpoints are those of
`R` that lie above the coefficients of `P`, so `φ_{P+R}(y) = φ_R(t + y)` with
`t = BS_offset R m`, `m` the largest coefficient of `P`. -/

/-- Rocq: `Notation.BachmannAbsorb.lead_gt`. -/
def lead_gt (R : BIdx) (e : BIdx) : Prop :=
  match R with
  | BIC e' _ _ => ilt e e'
  | BIZ => False

/-- Rocq: `Notation.BachmannAbsorb.R_lead_big`. -/
theorem R_lead_big (e R : BIdx) (HRe : lead_gt R e) : lead_big R :=
  match R, HRe with
  | BIZ, h => h.elim
  | BIC _ _ _, h => fun E => by subst E; exact (nomatch (h : ilt e BIZ))

/-- Rocq: `Notation.BachmannAbsorb.X_pos`. -/
theorem X_pos (e : BIdx) (c : BSmall) (R : BIdx) (HP : BI_nf (BIC e c BIZ)) (HR : BI_nf R) : BI_pos (BIC e c R) :=
  ⟨BI_nf_pos e HP.1, HP.2.2.1, BI_nf_pos R HR⟩

/-- Rocq: `Notation.BachmannAbsorb.X_inh`. -/
theorem X_inh (e : BIdx) (c : BSmall) (R : BIdx) (HP : BI_nf (BIC e c BIZ)) :
    Nonempty (bsmall (BI_denote (BIC e c R)) ⊕ bbig (BI_denote (BIC e c R))) :=
  BI_inh e c R HP.2.2.1

/-- (⊆) Every common fixpoint for `P + R` is one for `R`: `R`'s children sit
below `P + (R's children)`. Rocq: `Notation.BachmannAbsorb.absorb_sub`. -/
theorem absorb_sub (e : BIdx) (c : BSmall) (R : BIdx) (z : Ordinal.{0}) (_Hz : Complete z)
    (H : BFix (fun x => 1 + x) (BI_denote (BIC e c R)) z) : BFix (fun x => 1 + x) (BI_denote R) z :=
  let ⟨H1, H2, H3⟩ := H
  ⟨H1, fun a =>
    let ⟨k, Hk⟩ := badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) a
    le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_small _ (BI_bfam (BIC e c R)) k)).2 _
      (bsub_eq_r Hk (bsub_absorb _ _)) z) (H2 k),
   fun d =>
    let ⟨k, Hk⟩ := badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) d
    le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_big _ (BI_bfam (BIC e c R)) k z)).2 _
      (bsub_eq_r (Hk z) (bsub_absorb _ _)) 0) (H3 k)⟩

/-- The values of `φ_{P+R}` lie above the coefficients of `P`, which occur at
positions that are not the end. Rocq: `Notation.BachmannAbsorb.absorb_region`. -/
theorem absorb_region (e : BIdx) (c : BSmall) (R : BIdx) (HP : BI_nf (BIC e c BIZ)) (HR : BI_nf R)
    (HRe : lead_gt R e) (y : Ordinal.{0}) (_Hy : Complete y) : Klt (Φ[BIC e c R] y) (BIC e c BIZ) :=
  Klt_of_Kge _ _ fun z Hz => by
    have HK : Kgs z (BIC e c R) := by
      match R, HRe, Hz with
      | BIZ, h, _ => exact h.elim
      | BIC _ _ _, _, .inl h => exact .inl h
      | BIC _ _ _, _, .inr (.inl h) => exact .inr (.inl h)
      | BIC _ _ _, _, .inr (.inr h) => exact h.elim
    obtain ⟨C, ζ, HC, Hζ, Hzζ, Hlt⟩ := Kgs_ctx _ (X_pos e c R HP HR) _ HK
    exact lt_of_le_of_lt (le_trans Hzζ (bctx_dom _ onePlus_normal C HC ζ Hζ))
      (lt_of_lt_of_le (bphi_strict _ onePlus_normal _ (BI_denote (BIC e c R)) Hlt (BI_good _) (BI_bfam _))
        ((bphi_mono_index _ onePlus_mono _ (BI_bfam _)).1 _ _ (zero_least y)))

/-- Rocq: `Notation.BachmannAbsorb.absorb_max`. -/
def absorb_max (e : BIdx) (c : BSmall) : BSmall :=
  match kmax (BI_size (BIC e c BIZ) + BI_size (BIC e c BIZ) + 1) (BIC e c BIZ) with
  | some k => k
  | none => BZ

/-- Rocq: `Notation.BachmannAbsorb.absorb_max_spec`. -/
theorem absorb_max_spec (e : BIdx) (c : BSmall) (HP : BI_nf (BIC e c BIZ)) :
    BS_nf (absorb_max e c) ∧ Kin (absorb_max e c) (BIC e c BIZ) ∧ Kle (BS_denote (absorb_max e c)) (BIC e c BIZ) := by
  have H := kmax_spec (BI_size (BIC e c BIZ) + BI_size (BIC e c BIZ) + 1) (BIC e c BIZ) HP (Nat.lt_succ_self _)
  unfold absorb_max
  revert H
  cases kmax (BI_size (BIC e c BIZ) + BI_size (BIC e c BIZ) + 1) (BIC e c BIZ) with
  | none => intro H; exact (nomatch (H : BIC e c BIZ = BIZ))
  | some k => intro ⟨H1, H2⟩; exact ⟨Kin_nf k _ H1 HP, H1, H2⟩

/-- Rocq: `Notation.BachmannAbsorb.absorb_offset`. -/
def absorb_offset (e : BIdx) (c : BSmall) (R : BIdx) : BSmall := BS_offset R (absorb_max e c)

/-- Absorption, assuming the hard direction at notation values (`ABS`: common
fixpoints for `R` above the coefficients of `P` are common fixpoints for
`P + R`), which is proved below (`ABS_all`).
Rocq: `Notation.BachmannAbsorb.absorb_enum`. -/
theorem absorb_enum (e : BIdx) (c : BSmall) (R : BIdx) (HP : BI_nf (BIC e c BIZ)) (HR : BI_nf R)
    (HRe : lead_gt R e)
    (ABS : ∀ s, BS_nf s → Klt (Φ[R] (BS_denote s)) (BIC e c BIZ) →
      BFix (fun x => 1 + x) (BI_denote (BIC e c R)) (Φ[R] (BS_denote s))) :
    ∀ y, BS_nf y → Φ[BIC e c R] (BS_denote y) ≈ Φ[R] (BS_denote (absorb_offset e c R) + BS_denote y) := by
  obtain ⟨Hm, Hmin, HmK⟩ := absorb_max_spec e c HP
  obtain ⟨Nt, Hmt, Htt, Hleast⟩ := BS_offset_correct R HR (R_lead_big e R HRe) _ Hm
  have Htc := BS_complete (absorb_offset e c R)
  have Hgx := BI_good (BIC e c R)
  have Hgr := BI_good R
  refine BS_denote_ind (motive := fun y => BS_nf y →
    Φ[BIC e c R] (BS_denote y) ≈ Φ[R] (BS_denote (absorb_offset e c R) + BS_denote y)) ?_
  intro y IH Hy
  have HIy := BS_has_all_interpolants y Hy
  have Hyc := BS_complete y
  obtain ⟨Es, Ns⟩ := BS_add_reflects _ (absorb_offset e c R) ⟨equiv_refl _, Nt⟩ _ y ⟨equiv_refl _, Hy⟩
  have EPs : Φ[R] (BS_denote (BS_add (absorb_offset e c R) y)) ≈
      Φ[R] (BS_denote (absorb_offset e c R) + BS_denote y) :=
    ord_eq_normal _ (BI_normal R) _ _ (equiv_symm Es)
  have Hsc := BS_complete (BS_add (absorb_offset e c R) y)
  refine equiv_trans (equiv_intro ?_ ?_) EPs
  · -- `φ_{P+R}(y) ≤ φ_R(t + y)`
    have HK : Klt (Φ[R] (BS_denote (BS_add (absorb_offset e c R) y))) (BIC e c BIZ) :=
      Kle_lt _ _ _ HmK (lt_of_lt_of_le Hmt
        ((bphi_mono_index _ onePlus_mono _ (BI_bfam R)).1 _ _ (le_trans (le_add_right _ _) Es.le)))
    obtain ⟨H1', H2', H3'⟩ := ABS _ Ns HK
    rw [bphi_unfold _ (BI_denote (BIC e c R))]
    refine cfe_least _ onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgx) _ _ ?_ ?_ ?_
    · exact le_trans (onePlus_mono _ _ (le_trans (le_add_left _ _) Es.le)) (bphi_ge_f _ _ _)
    · refine limit_least fun j => ?_
      obtain ⟨n, Hn, _, Hjn, Hny⟩ := HI_below _ _ HIy (index_lt _ j)
      have h : Φ[BIC e c R] ((BS_denote y).size j) < Φ[R] (BS_denote (BS_add (absorb_offset e c R) y)) :=
        lt_of_le_of_lt ((bphi_mono_index _ onePlus_mono _ (BI_bfam _)).1 _ _ Hjn)
          (lt_of_le_of_lt (IH n Hny Hn).le
            (lt_of_lt_of_le ((BI_normal R).increasing _ _ (add_complete Htc Hyc) (add_lt_add_left _ Hny)) EPs.ge))
      exact (congrFun (bphi_unfold _ (BI_denote (BIC e c R))) _) ▸ h
    · intro i
      match i with
      | .inl k => exact ⟨H2' k, H1'⟩
      | .inr k => exact ⟨H3' k, H1'⟩
  · -- `φ_R(t + y) ≤ φ_{P+R}(y)`
    have Hzc : Complete (Φ[BIC e c R] (BS_denote y)) := BS_complete (BN (BIC e c R) y)
    have Hzfix := absorb_sub e c R _ Hzc
      (bfix_value_full _ onePlus_normal _ _ Hgx (X_inh e c R HP) Hyc)
    have Hreg := absorb_region e c R HP HR HRe _ Hyc
    have Hmz := Kge_lt _ _ _ (Kin_Kge _ _ Hmin) Hreg
    have Hlz := Hleast _ Hzc Hzfix Hmz
    have Htz := lt_of_lt_of_le Htt Hlz
    have Hpr := fix_principal R _ _ HR (R_lead_big e R HRe) Hzc Hzfix Htz
    obtain ⟨H1', H2', H3'⟩ := Hzfix
    rw [bphi_unfold _ (BI_denote R)]
    refine cfe_least _ onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgr) _ _ ?_ ?_ ?_
    · exact le_trans (onePlus_mono _ _ (le_trans Es.ge (le_trans (add_le_add (le_refl _)
        (normal_inflationary (BI_normal (BIC e c R)) _ Hyc)) Hpr))) H1'
    · refine limit_least fun j => ?_
      have Hj : (BS_denote (BS_add (absorb_offset e c R) y)).size j < BS_denote (absorb_offset e c R) + BS_denote y :=
        lt_of_lt_of_le (index_lt _ j) Es.ge
      have h : Φ[R] ((BS_denote (BS_add (absorb_offset e c R) y)).size j) < Φ[BIC e c R] (BS_denote y) := by
        match addOrd_lt_cases _ _ _ Hj with
        | .inl Ha => exact lt_of_lt_of_le ((BI_normal R).increasing _ _ Htc Ha) Hlz
        | .inr ⟨j0, Ha⟩ =>
          obtain ⟨n, Hn, _, Hjn, Hny⟩ := HI_below _ _ HIy (index_lt _ j0)
          exact lt_of_le_of_lt ((bphi_mono_index _ onePlus_mono _ (BI_bfam R)).1 _ _
              (le_trans Ha (add_le_add (le_refl _) Hjn)))
            (lt_of_le_of_lt (IH n Hny Hn).ge ((BI_normal (BIC e c R)).increasing _ _ Hyc Hny))
      exact (congrFun (bphi_unfold _ (BI_denote R)) _) ▸ h
    · intro i
      match i with
      | .inl k => exact ⟨H2' k, H1'⟩
      | .inr k => exact ⟨H3' k, H1'⟩

/-! ## The hard direction of absorption -/

/-- Rocq: `Notation.BachmannAbsorb.bfix_eq`. -/
theorem bfix_eq (T : BOrd.{0}) (z z' : Ordinal.{0}) (_Hg : BGood (fun x => 1 + x) T) (Hf : BFam T) (E : z ≈ z')
    (H : BFix (fun x => 1 + x) T z) : BFix (fun x => 1 + x) T z' :=
  let ⟨H1, H2, H3⟩ := H
  ⟨le_trans (onePlus_mono _ _ E.ge) (le_trans H1 E.le),
    fun a => le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_small _ Hf a)).1 _ _ E.ge) (le_trans (H2 a) E.le),
    fun d => le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_big _ Hf d z)).2 _ (bfam_fam _ Hf d _ _ E.ge) 0)
      (le_trans (H3 d) E.le)⟩

/-- Rocq: `Notation.BachmannAbsorb.Kgs_lt`. -/
theorem Kgs_lt (T : BIdx) (k : Ordinal.{0}) (HT : BI_pos T) (HK : Kgs k T) : k < Φ[T] 0 :=
  let ⟨C, ζ, HC, Hζ, Hkζ, Hlt⟩ := Kgs_ctx T HT _ HK
  lt_of_le_of_lt (le_trans Hkζ (bctx_dom _ onePlus_normal C HC ζ Hζ))
    (bphi_strict _ onePlus_normal _ _ Hlt (BI_good T) (BI_bfam T))

/-- Rocq: `Notation.BachmannAbsorb.Kend_of`. -/
theorem Kend_of : ∀ (T : BIdx) (z : Ordinal.{0}), BI_nf T → (∀ k, Kge k T → k ≤ z) → (∀ k, Kgs k T → k < z) →
    Kend z T
  | BIZ, _, _, _, _ => trivial
  | BIC e c r, z, ⟨He, Hc, Hc0, Hr, _⟩, H1, H2 => by
    have ihe := Kend_of e z He
    have ihr := Kend_of r z Hr
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

/-- Coefficients of `T` lie below `z` except at the end, when `φ_T(0) ≤ z`.
Rocq: `Notation.BachmannAbsorb.Kend_of_value`. -/
theorem Kend_of_value (T : BIdx) (z : Ordinal.{0}) (HT : BI_nf T) (Hz : Φ[T] 0 ≤ z) : Kend z T :=
  Kend_of T z HT (fun k Hk => le_trans (dominance T BZ k (BI_nf_pos T HT) Hk) Hz)
    (fun k Hk => lt_of_lt_of_le (Kgs_lt T k (BI_nf_pos T HT) Hk) Hz)

/-- Rocq: `Notation.BachmannAbsorb.Klt_of_value`. -/
theorem Klt_of_value (T : BIdx) (z : Ordinal.{0}) (HT : BI_nf T) (Hz : Φ[T] 0 < z) : Klt z T :=
  Klt_of_Kge _ T fun k Hk => lt_of_le_of_lt (dominance T BZ k (BI_nf_pos T HT) Hk) Hz

/-- Rocq: `Notation.BachmannAbsorb.ABSw`. -/
def ABSw (e : BIdx) (c : BSmall) (R : BIdx) : Prop :=
  ∀ w, BS_nf w → BFix (fun x => 1 + x) (BI_denote R) (BS_denote w) → Klt (BS_denote w) (BIC e c BIZ) →
    BFix (fun x => 1 + x) (BI_denote (BIC e c R)) (BS_denote w)

/-- Rocq: `Notation.BachmannAbsorb.lead_gt_big`. -/
theorem lead_gt_big (e R : BIdx) (H : lead_gt R e) : lead_big R := R_lead_big e R H

/-- Rocq: `Notation.BachmannAbsorb.lead_gt_ilt`. -/
theorem lead_gt_ilt (e R : BIdx) (c'' : BSmall) (r'' : BIdx) (H : lead_gt R e) : ilt (BIC e c'' r'') R :=
  match R, H with
  | BIZ, h => h.elim
  | BIC _ _ _, h => .exp _ _ _ _ _ _ h

/-- Rocq: `Notation.BachmannAbsorb.ABSw_ABS`. -/
theorem ABSw_ABS (e : BIdx) (c : BSmall) (R : BIdx) (HR : BI_nf R) (HRe : lead_gt R e) (HA : ABSw e c R) :
    ∀ s, BS_nf s → Klt (Φ[R] (BS_denote s)) (BIC e c BIZ) →
      BFix (fun x => 1 + x) (BI_denote (BIC e c R)) (Φ[R] (BS_denote s)) := fun s Hs HK =>
  have Ew := smartN_equal R s HR Hs
  have Hne : R ≠ BIZ := lead_big_ne R (lead_gt_big e R HRe)
  bfix_eq _ _ _ (BI_good _) (BI_bfam _) Ew
    (HA _ (smartN_nf R s HR Hs)
      (bfix_eq _ _ _ (BI_good R) (BI_bfam R) (equiv_symm Ew)
        (bfix_value_full _ onePlus_normal _ _ (BI_good R) (Hinh_of R HR Hne) (BS_complete s)))
      (Klt_mono _ _ Ew.ge _ HK))

/-- Rocq: `Notation.BachmannAbsorb.ABS_all`. -/
theorem ABS_all (e : BIdx) (c : BSmall) (HP : BI_nf (BIC e c BIZ)) :
    ∀ (U : BOrd.{0}) (R : BIdx), ble (BI_denote R) U → BI_nf R → lead_gt R e → ABSw e c R := by
  intro U
  refine blt_wf.induction (C := fun U => ∀ (R : BIdx), ble (BI_denote R) U → BI_nf R → lead_gt R e → ABSw e c R) U ?_
  intro U IHU R HU HR HRe w Hw Hfix HK
  have HP' := HP
  obtain ⟨He, Hc, Hc0, _⟩ := HP'
  have Hzc := BS_complete w
  have Hinf := fix_onePlus_finite _ onePlus_normal _ Hzc Hfix.1
  have Hz0 : 0 < BS_denote w := lt_of_lt_of_le (succ_lt 0) (Hinf 1)
  have Hprin : ∀ a, a < BS_denote w → a + BS_denote w ≤ BS_denote w := fun a ha =>
    fix_principal R _ a HR (lead_gt_big e R HRe) Hzc Hfix ha
  have HKendR : Kend (BS_denote w) R :=
    Kend_of_value R _ HR (bphi_le_fix _ onePlus_normal _ _ (BI_good R) Hzc Hfix)
  have HKe : Klt (BS_denote w) e := HK.1
  have Hcz : BS_denote c < BS_denote w := HK.2.1
  -- `P` fixes `z`, by nesting
  have HPz : Φ[BIC e c BIZ] (BS_denote w) ≤ BS_denote w :=
    zlt_nest _ onePlus_normal _ _ _
      ((nest _ Hinf (BI_size (BIC e c BIZ) + 1) (BIC e c BIZ) (Nat.lt_succ_self _) HP HK).1 R HR
        (lead_gt_ilt e R c BIZ HRe)) (BI_good R) (BI_bfam R) Hzc Hfix
  have HfixP := bfix_of_fix _ onePlus_normal _ _ (BI_good _) (BI_bfam _) Hzc HPz
  -- nesting for a normal `N` below `R`
  have Nest : ∀ N, BI_nf N → ilt N R → Klt (BS_denote w) N → Φ[N] (BS_denote w) ≤ BS_denote w :=
    fun N HN Hlt HKN =>
      zlt_nest _ onePlus_normal _ _ _ ((nest _ Hinf (BI_size N + 1) N (Nat.lt_succ_self _) HN HKN).1 R HR Hlt)
        (BI_good R) (BI_bfam R) Hzc Hfix
  have NestLe : ∀ N, BI_nf N → ilt N R → Kend (BS_denote w) N → Φ[N] 0 ≤ BS_denote w := fun N HN Hlt HKN =>
    bleZ_sound _ onePlus_normal _ _ _ ((nest_le _ Hinf (BI_size N + 1) N (Nat.lt_succ_self _) HN HKN).1 R HR HKendR Hlt)
      (BI_denote R) (bsub_refl _) (BI_good R) (BI_bfam R) Hzc Hfix
  -- the classification of `P + K'` for a normal `K'` below `R`
  have Hcls : ∀ K', BI_nf K' → blt (BI_denote K') (BI_denote R) →
      BFix (fun x => 1 + x) (BI_denote K') (BS_denote w) →
      (Φ[K'] (BS_denote w) ≤ BS_denote w → Φ[BIC e c K'] (BS_denote w) ≤ BS_denote w) ∧
        Φ[BIC e c K'] 0 ≤ BS_denote w := by
    intro K' HK' Hblt HfK
    have HK'0 : Φ[K'] 0 ≤ BS_denote w := bphi_le_fix _ onePlus_normal _ _ (BI_good K') Hzc HfK
    have HKendK := Kend_of_value K' _ HK' HK'0
    match K', HK', Hblt, HfK, HKendK with
    | BIZ, _, _, _, _ =>
      exact ⟨fun _ => HPz, le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam _)).1 _ _ (zero_least _)) HPz⟩
    | BIC e2 c2 r2, HK', Hblt, HfK, HKendK =>
      have HK'' := HK'
      obtain ⟨He2, Hc2, _, Hr2, Hl2⟩ := HK''
      have Hsmall_Klt : Φ[BIC e2 c2 r2] (BS_denote w) ≤ BS_denote w → Klt (BS_denote w) (BIC e2 c2 r2) := fun H =>
        Klt_of_value _ _ HK' (lt_of_lt_of_le ((BI_normal _).increasing _ _ Hzc Hz0) H)
      have Hcmp := (cmp_correct (BI_size e2 + BI_size e + 1)).2 e2 e (Nat.lt_succ_self _) He2 He
      revert Hcmp
      cases cmpI (BI_size e2 + BI_size e + 1) e2 e with
      | lt =>
        -- lead(K') < e: P + K' is normal
        intro Hcmp
        have HN : BI_nf (BIC e c (BIC e2 c2 r2)) := ⟨He, Hc, Hc0, HK', Hcmp⟩
        exact ⟨fun H => Nest _ HN (lead_gt_ilt e R c _ HRe) ⟨HKe, Hcz, Hsmall_Klt H⟩,
          NestLe _ HN (lead_gt_ilt e R c _ HRe) ⟨HKe, Hcz, HKendK⟩⟩
      | eq =>
        -- lead(K') = e: merge the coefficients
        intro Hcmp
        obtain ⟨Ea, Na⟩ := BS_add_reflects _ c ⟨equiv_refl _, Hc⟩ _ c2 ⟨equiv_refl _, Hc2⟩
        have HN : BI_nf (BIC e (BS_add c c2) r2) :=
          ⟨He, Na, lt_of_lt_of_le Hc0 (le_trans (le_add_right _ _) Ea.le), Hr2,
            lead_below_ieq r2 r2 e2 e (ieq_refl r2) Hcmp Hl2⟩
        have Heq : BEquiv (BI_denote (BIC e c (BIC e2 c2 r2))) (BI_denote (BIC e (BS_add c c2) r2)) :=
          bequiv_trans (bequiv_badd _ _ _ _ (bequiv_refl _) (bequiv_badd _ _ _ _
              (bequiv_bmul _ _ _ _ (bequiv_bexpΩ _ _ (ieq_bequiv Hcmp)) (bequiv_refl _)) (bequiv_refl _)))
            (bequiv_trans (bequiv_merge _ _ _ _)
              (bequiv_badd _ _ _ _ (bequiv_bmul _ _ _ _ (bequiv_refl _) (bequiv_embed _ _ Ea)) (bequiv_refl _)))
        have EN : ∀ y, Φ[BIC e c (BIC e2 c2 r2)] y ≈ Φ[BIC e (BS_add c c2) r2] y := fun y =>
          bphi_bequiv _ onePlus_mono _ _ y Heq (BI_bfam _) (BI_bfam _)
        have Hsum_lt : BS_denote c2 < BS_denote w → BS_denote (BS_add c c2) < BS_denote w := fun h =>
          lt_of_le_of_lt Ea.ge (lt_of_lt_of_le (add_lt_add_left _ h) (Hprin _ Hcz))
        have HKN : Kend (BS_denote w) (BIC e (BS_add c c2) r2) := by
          match r2, HKendK with
          | BIZ, HKendK =>
            have Hc2le : BS_denote c2 ≤ BS_denote w :=
              match HKendK with
              | .inl ⟨_, H⟩ => H
              | .inr ⟨_, H⟩ => le_trans H.le (Hinf 1)
            exact .inl ⟨HKe, le_trans Ea.ge (le_trans (add_le_add (le_refl _) Hc2le) (Hprin _ Hcz))⟩
          | BIC _ _ _, ⟨_, Hc2z, HKr3⟩ => exact ⟨HKe, Hsum_lt Hc2z, HKr3⟩
        exact ⟨fun H => le_trans (EN _).le (Nest _ HN (lead_gt_ilt e R _ _ HRe)
            (let ⟨_, Hc2z, HKr2⟩ := Hsmall_Klt H; ⟨HKe, Hsum_lt Hc2z, HKr2⟩)),
          le_trans (EN 0).le (NestLe _ HN (lead_gt_ilt e R _ _ HRe) HKN)⟩
      | gt =>
        -- lead(K') > e: absorption with a smaller R-part
        intro Hcmp
        have Hgt : lead_gt (BIC e2 c2 r2) e := Hcmp
        have HA : ABSw e c (BIC e2 c2 r2) :=
          IHU (BI_denote (BIC e2 c2 r2)) (blt_le_trans Hblt HU) _ (ble_refl _) HK' Hgt
        refine ⟨fun H => ?_, bphi_le_fix _ onePlus_normal _ _ (BI_good _) Hzc (HA w Hw HfK HK)⟩
        have Eabs := absorb_enum e c _ HP HK' Hgt (ABSw_ABS e c _ HK' Hgt HA) w Hw
        obtain ⟨Hm, Hmin, _⟩ := absorb_max_spec e c HP
        obtain ⟨_, _, Htt, Hleast⟩ := BS_offset_correct _ HK' (lead_gt_big e _ Hgt) _ Hm
        have Hmz : BS_denote (absorb_max e c) < BS_denote w := Kge_lt _ _ _ (Kin_Kge _ _ Hmin) HK
        have Htz : BS_denote (absorb_offset e c (BIC e2 c2 r2)) < BS_denote w :=
          lt_of_lt_of_le Htt (Hleast _ Hzc HfK Hmz)
        exact le_trans Eabs.le (le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam _)).1 _ _ (Hprin _ Htz)) H)
  -- now the components of `P + R`
  obtain ⟨CS, CF⟩ := cover R HR (notation_KHI_I R HR)
  have HIw := notation_KHI_S w Hw
  obtain ⟨_, HP2, HP3⟩ := HfixP
  obtain ⟨Hf1, Hf2, Hf3⟩ := Hfix
  refine ⟨Hf1, fun a => ?_, fun d => ?_⟩
  · match badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) a with
    | .inl ⟨a', E⟩ =>
      obtain ⟨k, Ek⟩ := badd_small_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero a'
      exact bphi_eq_le (E.trans Ek.symm) (HP2 k)
    | .inr ⟨b, E⟩ =>
      obtain ⟨K', HK', _, _, _, Hlo, b', Hup⟩ := CS b
      have HK'z : Φ[K'] (BS_denote w) ≤ BS_denote w :=
        le_trans ((bphi_mono_index _ onePlus_mono _ (bfam_small _ (BI_bfam R) b')).2 _ Hup _) (Hf2 b')
      have Hblt := bsub_child_blt _ _ (.inl b') Hup
      have HfK := bfix_of_fix _ onePlus_normal _ _ (BI_good K') (BI_bfam K') Hzc HK'z
      exact bphi_eq_le E (le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam (BIC e c K'))).2 _
        (bsub_badd_r _ _ _ Hlo) _) ((Hcls K' HK' Hblt HfK).1 HK'z))
  · match badd_big_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) d with
    | .inl ⟨d', E⟩ =>
      obtain ⟨k, Ek⟩ := badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero d'
      exact bphi_eq_le ((E _).trans (Ek _).symm) (HP3 k)
    | .inr ⟨d', E⟩ =>
      obtain ⟨K', HK', _, _, _, Hlo, d'', Hup⟩ := CF d' w Hw HIw
      have Hmem := bfix_member _ onePlus_normal _ d'' _ (BI_good R) (BI_bfam R) Hzc (Hf3 d'')
      have HfK := bfix_bsub _ onePlus_normal _ _ _ Hup (bfam_big _ (BI_bfam R) d'' _) Hmem
      have Hblt := bsub_child_blt _ _ (.inr (d'', BS_denote w)) Hup
      exact bphi_eq_le (E _) (le_trans ((bphi_mono_index _ onePlus_mono _ (BI_bfam (BIC e c K'))).2 _
        (bsub_badd_r _ _ _ Hlo) 0) (Hcls K' HK' Hblt HfK).2)

/-- Absorption, unconditionally. Rocq: `Notation.BachmannAbsorb.absorb`. -/
theorem absorb (e : BIdx) (c : BSmall) (HP : BI_nf (BIC e c BIZ)) (R : BIdx) (HR : BI_nf R) (HRe : lead_gt R e)
    (y : BSmall) (Hy : BS_nf y) :
    Φ[BIC e c R] (BS_denote y) ≈ Φ[R] (BS_denote (absorb_offset e c R) + BS_denote y) :=
  absorb_enum e c R HP HR HRe (ABSw_ABS e c R HR HRe (ABS_all e c HP (BI_denote R) R (ble_refl _) HR HRe)) y Hy

/-- The index `1 + Ω` (`= Ω^0·1 + Ω`) absorbs into `Ω` with offset 0, since
`ε₀ = φ_Ω(0)` already exceeds 1: `φ_{1+Ω}(y) = φ_Ω(0 + y)`. -/
example : absorb_offset BIZ BS_one BI_Ω = BZ := rfl

/-- With coefficient `ε₀ = φ_Ω(0)` the threshold is `ε₀` itself, so the offset
is 1: `φ_{ε₀+Ω}(y) = φ_Ω(1 + y)`. -/
example : absorb_offset BIZ (BN BI_Ω BZ) BI_Ω = BS_succ BZ := rfl

end BachmannNotation

end ConstructiveOrdinals
