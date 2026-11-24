import ConstructiveOrdinals.Notation.Bachmann.Notation

/-!
# The upper bound: every normal form lies below the Bachmann–Howard ordinal

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

At the base `1+x` the Bachmann–Howard ordinal is `BHO₁ = φ_{ε_{Ω+1}}(0)`.
Every normal index is reachable below some level `Ω+1, Ω^(Ω+1), …` of the
tower whose limit is `ε_{Ω+1}`, relative to any infinite `z` above its
coefficients; this is part (B) of `nest` applied along leading exponents.
Since `BHO₁` is a common fixpoint of the components of `ε_{Ω+1}`, it is a
fixpoint of every `φ_T`, and the bound follows by induction on notations.

Ported from the Rocq file `Notation/BachmannBound.v`.

Lean notes: `BNotation_bounded` is proved by the mutual recursions
`BNotation_bounded_S` and `BNotation_bounded_I` (Rocq uses the combined scheme
`BNotation_mut`).
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx

/-- Rocq: `Notation.BachmannBound.BHO1`. -/
def BHO1 : Ordinal.{0} := bphi (fun x => 1 + x) bεΩ1 0

/-- Rocq: `Notation.BachmannBound.bεΩ1_inh`. -/
theorem bεΩ1_inh : Nonempty (bsmall bεΩ1.{0} ⊕ bbig bεΩ1.{0}) := ⟨.inl ⟨0⟩⟩

/-- Rocq: `Notation.BachmannBound.bεΩ1_good`. -/
theorem bεΩ1_good : BFam bεΩ1.{0} ∧ BGood (fun x => 1 + x) bεΩ1.{0} :=
  bcanon_good _ onePlus_normal _ bcanon_bεΩ1 bdec_bεΩ1

/-- Rocq: `Notation.BachmannBound.BHO1_complete`. -/
theorem BHO1_complete : Complete BHO1 := bphi_complete onePlus_normal _ 0 bεΩ1_good.2 zero_complete

/-- Rocq: `Notation.BachmannBound.BHO1_inf`. -/
theorem BHO1_inf : OInf BHO1 :=
  bphi_value_inf _ onePlus_normal bεΩ1 0 (fun x => le_add_left 1 x) (fun _ _ => le_refl _) bεΩ1_good.2 bεΩ1_inh
    zero_complete

/-- Every normal index is z-reachably below some level of the tower.
Rocq: `Notation.BachmannBound.idx_height`. -/
theorem idx_height (z : Ordinal.{0}) (Hz : OInf z) :
    ∀ T : BIdx, BI_nf T → Klt z T → ∃ n, zlt z (BI_denote T) (btower n)
  | BIZ, _, _ => ⟨0, zlt_bslt _ _ _ (.small (bsucc bOmega) ⟨⟩ (bsub_bzero_l _))⟩
  | BIC e c r, HT, HK =>
    let ⟨m, Hm⟩ := idx_height z Hz e HT.1 HK.1
    ⟨m + 1, (nest z Hz (BI_size (BIC e c r) + 1) (BIC e c r) (Nat.lt_succ_self _) HT HK).2 (btower m) Hm⟩

/-- Rocq: `Notation.BachmannBound.zlt_tower_top`. -/
theorem zlt_tower_top (z : Ordinal.{0}) (x : BOrd.{0}) (n : Nat) (H : zlt z x (btower n)) : zlt z x bεΩ1 :=
  let ⟨D, H1, H2⟩ := H
  ⟨D, H1, .small bεΩ1 ⟨n⟩ H2⟩

/-- `BHO₁` is a fixpoint of `φ_T` for every normal index whose coefficients
lie below it. Rocq: `Notation.BachmannBound.BHO1_fix`. -/
theorem BHO1_fix (T : BIdx) (HT : BI_nf T) (HK : Klt BHO1 T) : bphi (fun x => 1 + x) (BI_denote T) BHO1 ≤ BHO1 :=
  let ⟨n, Hn⟩ := idx_height BHO1 BHO1_inf T HT HK
  zlt_value _ onePlus_normal (BI_denote T) bεΩ1 0 (zlt_tower_top _ _ n Hn) bεΩ1_good.2 bεΩ1_good.1 bεΩ1_inh
    zero_complete

mutual
theorem BNotation_bounded_S : ∀ x : BSmall, BS_nf x → BS_denote x < BHO1
  | BZ, _ => bphi_nonzero onePlus_normal _ _
  | BN T y, ⟨HT, Hy, _⟩ =>
    lt_of_lt_of_le ((BI_normal T).increasing _ _ BHO1_complete (BNotation_bounded_S y Hy))
      (BHO1_fix T HT (BNotation_bounded_I T HT))

theorem BNotation_bounded_I : ∀ T : BIdx, BI_nf T → Klt BHO1 T
  | BIZ, _ => trivial
  | BIC e c r, ⟨He, Hc, _, Hr, _⟩ => ⟨BNotation_bounded_I e He, BNotation_bounded_S c Hc, BNotation_bounded_I r Hr⟩
end

/-- Rocq: `Notation.BachmannBound.BNotation_bounded`. -/
theorem BNotation_bounded : (∀ x, BS_nf x → BS_denote x < BHO1) ∧ ∀ T, BI_nf T → Klt BHO1 T :=
  ⟨BNotation_bounded_S, BNotation_bounded_I⟩

/-- Every normal form denotes an ordinal below the Bachmann–Howard ordinal
(at the base `1+x`). Rocq: `Notation.BachmannBound.BS_bounded`. -/
theorem BS_bounded (x : BSmall) (Hx : BS_nf x) : BS_denote x < BHO1 := BNotation_bounded_S x Hx

/-! # Dominance: coefficients lie at or below `φ_T(0)`

Every coefficient `k` of a normal index `T`, at any depth, sits in a strict
context `C` with `C k ⊑ ⟦T⟧` (`BCtx`): the hole runs through the right summand
of an addition, the coefficient of `Ω^e·_`, or an exponent. So
`k ≤ φ_{C k}(0) ≤ φ_T(0)`. Equality can occur, e.g. `φ_{Ω^d}(0) = d` for `d`
the Large Veblen Ordinal. -/

/-- Rocq: `Notation.BachmannBound.idx_term_bcd`. -/
theorem idx_term_bcd (e : BIdx) (c : BSmall) : BCd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) :=
  (idx_ok_term _ _ (BI_ok e) (BS_complete c)).1

/-- All coefficients, at any depth, are positive. Rocq: `Notation.BachmannBound.BI_pos`. -/
def BI_pos : BIdx → Prop
  | BIZ => True
  | BIC e c r => BI_pos e ∧ 0 < BS_denote c ∧ BI_pos r

/-- Rocq: `Notation.BachmannBound.BI_nf_pos`. -/
theorem BI_nf_pos : ∀ T : BIdx, BI_nf T → BI_pos T
  | BIZ, _ => trivial
  | BIC e _ r, ⟨He, _, Hc, Hr, _⟩ => ⟨BI_nf_pos e He, Hc, BI_nf_pos r Hr⟩

/-- Rocq: `Notation.BachmannBound.Kge_ctx`. -/
theorem Kge_ctx : ∀ T : BIdx, BI_pos T → ∀ z, Kge z T →
    ∃ (C : Ordinal.{0} → BOrd.{0}) (ζ : Ordinal.{0}), BCtx C ∧ Complete ζ ∧ z ≤ ζ ∧ bsub (C ζ) (BI_denote T)
  | BIZ, _, _, h => h.elim
  | BIC e _ _, ⟨He, Hc0, _⟩, z, .inl Hz =>
    let ⟨C, ζ, HC, Hζ, Hzζ, Hsub⟩ := Kge_ctx e He z Hz
    ⟨fun ξ => bexpΩ (C ξ), ζ, bctx_exp C HC, Hζ, Hzζ,
      bsub_trans (bsub_bexpΩ _ _ Hsub) (bsub_trans (bsub_P_Pz _ _ Hc0) (bsub_le_badd _ _))⟩
  | BIC e c _, _, _, .inr (.inl Hz) =>
    ⟨fun ξ => bmul (bexpΩ (BI_denote e)) (embed ξ), BS_denote c,
      bctx_mul _ _ (bcd_bexpΩ _ (BI_ok e).1) (bpos_bexpΩ _) bctx_embed, BS_complete c, Hz, bsub_le_badd _ _⟩
  | BIC e c r, ⟨_, _, Hr⟩, z, .inr (.inr Hz) =>
    let ⟨C, ζ, HC, Hζ, Hzζ, Hsub⟩ := Kge_ctx r Hr z Hz
    ⟨fun ξ => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (C ξ), ζ,
      bctx_add _ C (idx_term_bcd e c) HC, Hζ, Hzζ, bsub_badd_r _ _ _ Hsub⟩

/-- Rocq: `Notation.BachmannBound.dominance`. -/
theorem dominance (T : BIdx) (y : BSmall) (z : Ordinal.{0}) (HT : BI_pos T) (Hz : Kge z T) :
    z ≤ BS_denote (BN T y) :=
  let ⟨C, ζ, HC, Hζ, Hzζ, Hsub⟩ := Kge_ctx T HT z Hz
  le_trans Hzζ (le_trans (bctx_dom _ onePlus_normal C HC ζ Hζ)
    (le_trans ((bphi_mono_index _ onePlus_normal.monotone _ (BI_bfam T)).2 _ Hsub 0)
      ((BI_normal T).monotone _ _ (zero_least _))))

end BachmannNotation

end ConstructiveOrdinals
