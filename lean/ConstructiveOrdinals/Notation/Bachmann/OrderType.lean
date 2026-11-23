import ConstructiveOrdinals.Notation.Bachmann.Interpolants
import ConstructiveOrdinals.Notation.CantorProduct

/-!
# The natural product and the order type of the Bachmann notation

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

Ported from the Rocq file `Notation/BachmannOrderType.v`.
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx CantorDecomposition

/-! ## The natural product -/

/-- Rocq: `Notation.BachmannOrderType.BS_nmul`. -/
def BS_nmul : BSmall → BSmall → BSmall := CantorProduct.cantorNmul BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannOrderType.BS_nmul_reflects`. -/
theorem BS_nmul_reflects :
    Reflects BSmall BS_denote BS_nf (.ord ==> .ord ==> .ord) NaturalProduct.nmul BS_nmul :=
  CantorProduct.cantor_nmul_reflects BS_has_cantor_decomposition BS_has_all_interpolants

/-! ## The order type of the normal forms

The normal forms are cofinal in `BHO₁`: their limit is a fixpoint of `1+x`
and of the components `φ_{tower n}` of `ε_{Ω+1}`, since each component is
bounded by `φ` of a notation index `tₙ` (`Ω+1, Ω^(Ω+1), …`) and so takes
notations to notations. -/

/-- Rocq: `Notation.BachmannOrderType.BI_tower`. -/
def BI_tower : Nat → BIdx
  | 0 => BIC BI_one BS_one (BIC BIZ BS_one BIZ)
  | n + 1 => BIC (BI_tower n) BS_one BIZ

/-- Rocq: `Notation.BachmannOrderType.BS_one_pos`. -/
theorem BS_one_pos : 0 < BS_denote BS_one := BS_pos _ _

/-- Rocq: `Notation.BachmannOrderType.BI_tower_nf`. -/
theorem BI_tower_nf : ∀ n : Nat, BI_nf (BI_tower n)
  | 0 => ⟨⟨trivial, BS_one_nf, BS_one_pos, trivial, trivial⟩, BS_one_nf, BS_one_pos,
      ⟨trivial, BS_one_nf, BS_one_pos, trivial, trivial⟩, .nil _ _ _⟩
  | n + 1 => ⟨BI_tower_nf n, BS_one_nf, BS_one_pos, trivial, trivial⟩

/-- Rocq: `Notation.BachmannOrderType.bequiv_mul_one`. -/
theorem bequiv_mul_one (P : BOrd.{0}) : BEquiv (bmul P (embed (BS_denote BS_one))) P :=
  bequiv_trans (bequiv_bmul _ _ _ _ (bequiv_refl _) (bequiv_embed _ _ BS_one_denote))
    ⟨(bsub_bmul_one _).1, (bsub_bmul_one _).2⟩

/-- Rocq: `Notation.BachmannOrderType.bsub_succ_add`. -/
theorem bsub_succ_add (x : BOrd.{0}) : bsub (bsucc x) (badd x (embed 1)) :=
  bsub_intro _ _ (fun _ => let ⟨t, Ht⟩ := badd_small_r x (embed 1) ⟨⟩; ⟨t, bsub_eq_r Ht (bsub_le_badd _ _)⟩)
    (fun c => (nomatch c))

/-- Rocq: `Notation.BachmannOrderType.bsub_tower`. -/
theorem bsub_tower : ∀ n : Nat, bsub (btower n) (BI_denote (BI_tower n))
  | 0 => by
    have H1 : BEquiv (BI_denote BI_one) (embed 1) :=
      bequiv_trans (exp_equiv BI_one BS_one rfl) (bequiv_embed _ _ BS_one_denote)
    refine bsub_trans (bsub_trans (bsub_succ_add bOmega) (bsub_badd_l _ _ (Ω_le_exp 1 zero_lt_one) _)) ?_
    refine bsub_trans (bsub_badd_r _ _ (badd (bmul (bexpΩ bzero) (embed (BS_denote BS_one))) bzero)
      (bsub_trans (bsub_trans (bequiv_embed _ _ BS_one_denote).2 (bequiv_one_mul _).2) (bequiv_badd_zero_r _).2)) ?_
    exact bsub_badd_l _ _ (bsub_trans (bsub_bexpΩ _ _ H1.2) (bequiv_mul_one _).2) _
  | n + 1 =>
    bsub_trans (bsub_trans (bsub_bexpΩ _ _ (bsub_tower n)) (bequiv_mul_one _).2) (bequiv_badd_zero_r _).2

/-- Rocq: `Notation.BachmannOrderType.NFOrd`. -/
def NFOrd : Ordinal.{0} := mk { x : BSmall // BS_nf x } fun x => BS_denote x.1

/-- Rocq: `Notation.BachmannOrderType.NF_below`. -/
theorem NF_below (x : BSmall) (Hx : BS_nf x) : BS_denote x < NFOrd := index_lt NFOrd ⟨x, Hx⟩

/-- A normal function taking notations below notations fixes the limit of the
normal forms. Rocq: `Notation.BachmannOrderType.NF_closed`. -/
theorem NF_closed (G : Ordinal.{0} → Ordinal.{0}) (HG : NormalFunction G)
    (HGn : ∀ x, BS_nf x → ∃ y, BS_nf y ∧ G (BS_denote x) ≤ BS_denote y) : G NFOrd ≤ NFOrd := by
  let s : { x : BSmall // BS_nf x } → Ordinal.{0} := fun x => succ (BS_denote x.1)
  have Hdir : Directed _ s := fun ⟨x1, H1⟩ ⟨x2, H2⟩ =>
    let ⟨E, N⟩ := BS_add_reflects (BS_denote x1) x1 ⟨equiv_refl _, H1⟩ (BS_denote x2) x2 ⟨equiv_refl _, H2⟩
    ⟨⟨BS_add x1 x2, N⟩, succ_monotone (le_trans (le_add_right _ _) E.le), succ_monotone (le_trans (le_add_left _ _) E.le)⟩
  have Hc : ∀ a, Complete (s a) := fun _ => succ_complete (BS_complete _)
  have Hle : NFOrd ≤ sup s := le_intro fun a => lt_of_lt_of_le (succ_lt _) (sup_le s a)
  refine le_trans (HG.monotone _ _ Hle) (le_trans (HG.continuous _ s ⟨BZ, trivial⟩ Hdir Hc) (sup_least fun ⟨x, Hx⟩ => ?_))
  obtain ⟨E, N⟩ := BS_succ_reflects (BS_denote x) x ⟨equiv_refl _, Hx⟩
  obtain ⟨y, Hy, Hyl⟩ := HGn _ N
  exact le_trans (HG.monotone _ _ E.le) (le_trans Hyl (le_of_lt (NF_below y Hy)))

/-- The normal forms have order type `BHO₁`. Rocq: `Notation.BachmannOrderType.BS_order_type`. -/
theorem BS_order_type : NFOrd ≈ BHO1 := by
  refine equiv_intro (limit_least fun x => BS_bounded x.1 x.2) ?_
  have HF := bphi_fam_normal' onePlus_normal _ _ _ _ bεΩ1_good.2
  have H1 : 1 + NFOrd ≤ NFOrd := NF_closed _ onePlus_normal fun x Hx =>
    let ⟨E, N⟩ := BS_onePlus_reflects (BS_denote x) x ⟨equiv_refl _, Hx⟩
    ⟨BS_onePlus x, N, E.le⟩
  exact cfe_least _ onePlus_normal _ _ HF 0 NFOrd
    (le_trans (BS_denote_onePlus BZ).ge (le_of_lt (NF_below BS_one BS_one_nf)))
    (limit_least fun j => (nomatch j))
    (fun i => match i with
      | .inl n => ⟨NF_closed _ (HF (.inl n)) fun x Hx =>
          ⟨smartN (BI_tower n.down) x, smartN_nf _ _ (BI_tower_nf _) Hx,
            le_trans ((bphi_mono_index _ onePlus_normal.monotone _ (BI_bfam _)).2 _ (bsub_tower n.down) _)
              (smartN_equal _ _ (BI_tower_nf _) Hx).ge⟩, H1⟩
      | .inr e => (nomatch e))

/-! ## Base change: `BHO₁` is the Bachmann–Howard ordinal

`φ^{1+x}_T ≤ φ^{ω^x}_T` gives one direction. For the other,
`φ^{ω^x}_T ≤ φ^{1+x}_{Ω+T}`, and `Ω + tower n` lies z-reachably below
`tower (n+2)`, so `BHO₁` is closed under `ω^x` and every
`φ^{ω^x}_{tower n}`. -/

/-- Rocq: `Notation.BachmannOrderType.BHO1_BachmannHoward`. -/
theorem BHO1_BachmannHoward : BHO1 ≈ BachmannHoward := by
  refine equiv_intro (bphi_base_mono _ bcd_bεΩ1 0 zero_complete) ?_
  have Hg := bcd_good powOmega powOmega_normal _ bcd_bεΩ1
  have Hcomp : ∀ n, bphi powOmega (btower n) BHO1 ≤ BHO1 := fun n => by
    refine le_trans (bphi_powOmega_shift _ (bcd_btower n) _ BHO1_complete) ?_
    obtain ⟨Hfam1, Hg1⟩ := bεΩ1_good
    have Hgt : BGood (fun x => 1 + x) (btower (n + 2)) := bgood_small _ bεΩ1 ⟨n + 2⟩ Hg1
    have Hft : BFam (btower (n + 2)) := bfam_small bεΩ1 Hfam1 ⟨n + 2⟩
    exact zlt_nest _ onePlus_normal _ _ (btower (n + 2)) (zlt_Ω_tower n _ BHO1_inf) Hgt Hft BHO1_complete
      (bfix_of_fix _ onePlus_normal _ _ Hgt Hft BHO1_complete
        (bphi_fix_small' onePlus_normal bεΩ1 ⟨n + 2⟩ 0 Hg1 zero_complete))
  have Hpow : powOmega BHO1 ≤ BHO1 :=
    le_trans (bphi_bzero _ powOmega_normal BHO1).ge
      (le_trans ((bphi_mono_index _ powOmega_normal.monotone _ (bfam_btower 0)).2 _ (bsub_bzero_l _) _) (Hcomp 0))
  exact cfe_least powOmega powOmega_normal _ _ (bphi_fam_normal' powOmega_normal _ _ _ _ Hg) 0 BHO1
    (le_trans (powOmega_normal.monotone _ _ (zero_least _)) Hpow) (limit_least fun j => (nomatch j))
    (fun i => match i with
      | .inl n => ⟨Hcomp n.down, Hpow⟩
      | .inr e => (nomatch e))

/-- Rocq: `Notation.BachmannOrderType.BS_order_type_BH`. -/
theorem BS_order_type_BH : NFOrd ≈ BachmannHoward := equiv_trans BS_order_type BHO1_BachmannHoward

end BachmannNotation

end ConstructiveOrdinals
