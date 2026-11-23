import ConstructiveOrdinals.Notation.Bachmann.Notation
import ConstructiveOrdinals.Notation.CantorDecomposition

/-!
# Cantor decomposition of the Bachmann notation

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

At the base `1+x`, `φ_∅(y) = 1 + y` and `φ_{Ω^0·a}(y) = ω^a + y`. A value
whose index has a nonzero leading exponent is an ε-number: `ω^v = v`. So a
normal form decomposes as a sum of powers of ω whose exponents are again
normal forms, and the generic Cantor arithmetic applies.

Ported from the Rocq file `Notation/BachmannCantor.v`.

Lean notes: the Rocq section variables `A`, `f` and `Hf` of `cantor_sums`
become arguments of `cantor_lt_succ` and `cantor_lt_shift`.
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx CantorDecomposition

/-! ## Generic facts about Cantor sums -/

/-- Rocq: `Notation.BachmannCantor.cantor_lt_succ`. -/
theorem cantor_lt_succ {A : Type} (f : A → Ordinal.{0}) (Hf : ∀ x, Complete (f x)) :
    ∀ (xs : List A) (a : A), CantorOrdered f (a :: xs) → cantorDenote f (a :: xs) < ω ^ succ (f a)
  | [], _, _ => lt_of_le_of_lt (add_zero _).le (pow_lt_pow_right omega_gt1 (succ_lt _))
  | b :: xs, a, ⟨Hab, Hord⟩ =>
    powOmega_additively_closed (succ_complete (Hf a)) _ _ (pow_lt_pow_right omega_gt1 (succ_lt _))
      (lt_of_lt_of_le (cantor_lt_succ f Hf xs b Hord)
        (pow_le_pow_right ω (succ_least (lt_of_le_of_lt Hab (succ_lt _)))))

/-- Rocq: `Notation.BachmannCantor.cantor_lt_shift`. -/
theorem cantor_lt_shift {A : Type} (f : A → Ordinal.{0}) :
    ∀ (xs : List A) (a : Ordinal.{0}), CantorOrdered f xs → HeadLe f a xs → cantorDenote f xs < ω ^ a + cantorDenote f xs
  | [], a, _, _ => lt_of_lt_of_le (pow_pos ω a) (add_zero _).ge
  | b :: xs, _, ⟨Hhead, Hord⟩, Hb =>
    lt_of_lt_of_le (add_lt_add_left _ (cantor_lt_shift f xs (f b) Hord Hhead))
      (add_le_add (pow_le_pow_right ω Hb) (le_refl _))

/-- `u + (ω^b + r) = ω^b + r` whenever `u < ω^b`. Rocq: `Notation.BachmannCantor.lead_absorb`. -/
theorem lead_absorb (u b r : Ordinal.{0}) (Hb : Complete b) (Hu : u < ω ^ b) : u + (ω ^ b + r) ≈ ω ^ b + r :=
  equiv_trans (add_assoc u _ r)
    (equiv_intro (add_le_add (additively_closed_collapse (powOmega_additively_closed Hb) Hu) (le_refl r))
      (add_le_add (le_add_left u _) (le_refl r)))

/-! ## The values of the three shapes -/

/-- Rocq: `Notation.BachmannCantor.BS_denote_small`. -/
theorem BS_denote_small (a y : BSmall) : BS_denote (BN (BIC BIZ a BIZ) y) ≈ ω ^ BS_denote a + BS_denote y :=
  equiv_trans
    (bphi_bequiv _ onePlus_normal.monotone _ _ _ (exp_equiv (BIC BIZ a BIZ) a rfl) (BI_bfam _) (bfam_embed _))
    (bphi_onePlus_embed _ _ (BS_complete a) (BS_complete y))

/-- A value whose index has a nonzero leading exponent is an ε-number: the
family `ξ ↦ Ω^0·ξ = ξ` is reachable from `Ω^e` at the argument `v` itself, so
`φ_{Ω^0·v}(0) = ω^v` lies below `v`. Rocq: `Notation.BachmannCantor.BN_eps`. -/
theorem BN_eps (e : BIdx) (c : BSmall) (r : BIdx) (y : BSmall) (Hx : BS_nf (BN (BIC e c r) y)) (He : e ≠ BIZ) :
    ω ^ BS_denote (BN (BIC e c r) y) ≤ BS_denote (BN (BIC e c r) y) := by
  have HT := Hx.1
  have Hv : OInf (BS_denote (BN (BIC e c r) y)) := BN_inf _ y HT (fun h => nomatch h)
  have Hc : 0 < BS_denote c := HT.2.2.1
  have Hepos : bpos (BI_denote e) := by
    match e, He, HT with
    | BIZ, He, _ => exact absurd rfl He
    | BIC _ _ _, _, HT => exact lead_pos _ _ _ HT.1.2.2.1
  have HZ : bleZ (BS_denote (BN (BIC e c r) y)) (bmul (bexpΩ bzero) (embed (BS_denote (BN (BIC e c r) y))))
      (BI_denote (BIC e c r)) :=
    bleZ_mono_r _ _ _ _ (zlt_exp _ bzero (BI_denote e) (zlt_bslt _ _ _ Hepos) Hv)
      (bsub_trans (bsub_P_Pz _ _ Hc) (bsub_le_badd _ _))
  have Hfix := bleZ_sound (fun x => 1 + x) onePlus_normal _ _ _ HZ (BI_denote (BIC e c r)) (bsub_refl _)
    (BI_good _) (BI_bfam _) (BS_complete (BN (BIC e c r) y))
    (bfix_value_full (fun x => 1 + x) onePlus_normal (BI_denote (BIC e c r)) (BS_denote y) (BI_good _)
      (BI_inh e c r Hc) (BS_complete y))
  refine le_trans ?_ Hfix
  refine le_trans (le_trans (le_add_right _ 0) (bphi_onePlus_embed _ 0 (BS_complete (BN (BIC e c r) y)) zero_complete).ge) ?_
  exact (bphi_bequiv _ onePlus_normal.monotone _ _ _ (bequiv_sym (bequiv_one_mul _)) (bfam_embed _)
    (bfam_bmul _ _ (bfam_bexpΩ _ bfam_bzero) (bfam_embed _))).le

/-! ## Decomposition -/

/-- Rocq: `Notation.BachmannCantor.BS_decompose`. -/
def BS_decompose : BSmall → List BSmall
  | BZ => []
  | BN BIZ y => BZ :: BS_decompose y
  | BN (BIC BIZ a BIZ) y => a :: BS_decompose y
  | BN (BIC BIZ a (BIC e c r)) y => [BN (BIC BIZ a (BIC e c r)) y]
  | BN (BIC (BIC e1 c1 r1) c r) y => [BN (BIC (BIC e1 c1 r1) c r) y]

/-- Rocq: `Notation.BachmannCantor.decompose_correct`. -/
theorem decompose_correct : ∀ x : BSmall, BS_nf x →
    Each BS_nf (BS_decompose x) ∧ CantorOrdered BS_denote (BS_decompose x) ∧
      BS_denote x ≈ cantorDenote BS_denote (BS_decompose x)
  | BZ, _ => ⟨trivial, trivial, equiv_refl _⟩
  | BN BIZ y, ⟨_, Hy, Hlt, _⟩ => by
    obtain ⟨Hall, Hord, Heq⟩ := decompose_correct y Hy
    have key : ∀ l : List BSmall, BS_denote y ≈ cantorDenote BS_denote l → HeadLe BS_denote (BS_denote BZ) l
      | [], _ => trivial
      | BZ :: _, _ => le_refl _
      | BN Tb yb :: bs, Heq => by
        have Habs := lead_absorb 1 (BS_denote (BN Tb yb)) (cantorDenote BS_denote bs) (BS_complete _)
          (lt_of_le_of_lt (pow_zero ω).ge (pow_lt_pow_right omega_gt1 (BS_pos Tb yb)))
        exact absurd (lt_of_lt_of_le Hlt (le_trans (BS_denote_onePlus y).le
          (le_trans (add_le_add (le_refl 1) Heq.le) (le_trans Habs.le Heq.ge)))) (lt_irrefl _)
    exact ⟨⟨trivial, Hall⟩, ⟨key _ Heq, Hord⟩,
      equiv_trans (BS_denote_onePlus y) (add_congr (equiv_symm (pow_zero ω)) Heq)⟩
  | BN (BIC BIZ a BIZ) y, ⟨HT, Hy, Hlt, _⟩ => by
    obtain ⟨Hall, Hord, Heq⟩ := decompose_correct y Hy
    have Hc : BS_nf a := HT.2.1
    have key : ∀ l : List BSmall, Each BS_nf l → BS_denote y ≈ cantorDenote BS_denote l →
        HeadLe BS_denote (BS_denote a) l
      | [], _, _ => trivial
      | b :: bs, ⟨Hb, _⟩, Heq =>
        match BS_decide_order a b Hc Hb with
        | .inr h => h
        | .inl Hcb => by
          have Habs := lead_absorb (ω ^ BS_denote a) (BS_denote b) (cantorDenote BS_denote bs) (BS_complete _)
            (pow_lt_pow_right omega_gt1 Hcb)
          exact absurd (lt_of_lt_of_le Hlt (le_trans (BS_denote_small a y).le
            (le_trans (add_le_add (le_refl _) Heq.le) (le_trans Habs.le Heq.ge)))) (lt_irrefl _)
    exact ⟨⟨Hc, Hall⟩, ⟨key _ Hall Heq, Hord⟩, equiv_trans (BS_denote_small a y) (add_congr (equiv_refl _) Heq)⟩
  | BN (BIC BIZ _ (BIC e2 _ _)) _, ⟨HT, _⟩ => (nomatch (HT.2.2.2.2 : ilt e2 BIZ))
  | BN (BIC (BIC e1 c1 r1) c r) y, Hx =>
    ⟨⟨Hx, trivial⟩, ⟨trivial, trivial⟩,
      equiv_intro (le_trans (normal_inflationary powOmega_normal _ (BS_complete _)) (le_add_right _ 0))
        (le_trans (add_zero _).le (BN_eps (BIC e1 c1 r1) c r y Hx (fun h => nomatch h)))⟩

/-- A normal form that is not an ε-number lies below its ω-power.
Rocq: `Notation.BachmannCantor.not_eps_lt`. -/
theorem not_eps_lt (x : BSmall) (Hx : BS_nf x)
    (Hs : match x with
      | BZ => False
      | BN BIZ _ => True
      | BN (BIC BIZ _ _) _ => True
      | BN (BIC (BIC _ _ _) _ _) _ => False) :
    BS_denote x < ω ^ BS_denote x := by
  obtain ⟨_, Hord, Heq⟩ := decompose_correct x Hx
  match x, Hx, Hs, Hord, Heq with
  | BZ, _, Hs, _, _ => exact Hs.elim
  | BN BIZ y, _, _, Hord, Heq =>
    exact lt_of_le_of_lt Heq.le (lt_of_lt_of_le (cantor_lt_succ BS_denote BS_complete (BS_decompose y) BZ Hord)
      (pow_le_pow_right ω (succ_least (BS_pos BIZ y))))
  | BN (BIC BIZ c BIZ) y, Hx, _, Hord, Heq =>
    exact lt_of_le_of_lt Heq.le (lt_of_lt_of_le (cantor_lt_succ BS_denote BS_complete (BS_decompose y) c Hord)
      (pow_le_pow_right ω (succ_least Hx.2.2.2.2.1)))
  | BN (BIC BIZ _ (BIC e2 _ _)) _, Hx, _, _, _ => exact (nomatch (Hx.1.2.2.2.2 : ilt e2 BIZ))
  | BN (BIC (BIC _ _ _) _ _) _, _, Hs, _, _ => exact Hs.elim

/-! ## Recomposition -/

/-- Rocq: `Notation.BachmannCantor.BS_recompose`. -/
def BS_recompose : List BSmall → BSmall
  | [] => BZ
  | e :: xs' =>
    let r := BS_recompose xs'
    match e, xs' with
    | BZ, _ => BN BIZ r
    | BN (BIC (BIC a b c) d g) h, [] => BN (BIC (BIC a b c) d g) h
    | BN (BIC (BIC a b c) d g) h, _ :: _ => BN (BIC BIZ (BN (BIC (BIC a b c) d g) h) BIZ) r
    | BN BIZ h, _ => BN (BIC BIZ (BN BIZ h) BIZ) r
    | BN (BIC BIZ d g) h, _ => BN (BIC BIZ (BN (BIC BIZ d g) h) BIZ) r

/-- Rocq: `Notation.BachmannCantor.small_nf`. -/
theorem small_nf (e r : BSmall) (He : BS_nf e) (He0 : 0 < BS_denote e) (Hr : BS_nf r)
    (H1 : BS_denote r < ω ^ BS_denote e + BS_denote r) (H2 : BS_denote e < ω ^ BS_denote e + BS_denote r) :
    BS_nf (BN (BIC BIZ e BIZ) r) :=
  ⟨⟨trivial, He, He0, trivial, trivial⟩, Hr, lt_of_lt_of_le H1 (BS_denote_small e r).ge,
    ⟨trivial, lt_of_lt_of_le H2 (BS_denote_small e r).ge, trivial⟩⟩

/-- Rocq: `Notation.BachmannCantor.recompose_correct`. -/
theorem recompose_correct : ∀ xs : List BSmall, Each BS_nf xs → CantorOrdered BS_denote xs →
    BS_nf (BS_recompose xs) ∧ cantorDenote BS_denote xs ≈ BS_denote (BS_recompose xs)
  | [], _, _ => ⟨trivial, equiv_refl _⟩
  | e :: xs, ⟨He, Hall⟩, ⟨Hhead, Hord⟩ => by
    obtain ⟨Hr, Heq⟩ := recompose_correct xs Hall Hord
    have Hshift := cantor_lt_shift BS_denote xs (BS_denote e) Hord Hhead
    have Hshift' : BS_denote (BS_recompose xs) < ω ^ BS_denote e + BS_denote (BS_recompose xs) :=
      lt_of_le_of_lt Heq.ge (lt_of_lt_of_le Hshift (add_le_add (le_refl _) Heq.le))
    -- the general case `Ω^0·e`
    have Hgen : 0 < BS_denote e → BS_denote e < ω ^ BS_denote e + BS_denote (BS_recompose xs) →
        BS_nf (BN (BIC BIZ e BIZ) (BS_recompose xs)) ∧
          cantorDenote BS_denote (e :: xs) ≈ BS_denote (BN (BIC BIZ e BIZ) (BS_recompose xs)) := fun He0 Hlt =>
      ⟨small_nf e _ He He0 Hr Hshift' Hlt, equiv_trans (add_congr (equiv_refl _) Heq) (equiv_symm (BS_denote_small _ _))⟩
    -- when the tail is nonempty, `e` lies below `ω^e + rest`
    have Hne : xs ≠ [] → BS_denote e < ω ^ BS_denote e + BS_denote (BS_recompose xs) := by
      intro Hxs
      match xs, Heq, Hxs with
      | [], _, Hxs => exact absurd rfl Hxs
      | b :: bs, Heq, _ =>
        exact lt_of_le_of_lt (le_trans (normal_inflationary powOmega_normal _ (BS_complete e)) (add_zero _).ge)
          (add_lt_add_left _ (lt_of_lt_of_le (lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)) Heq.le))
    match e, xs, He, Hgen, Hne, Hr, Heq, Hshift' with
    | BZ, xs, _, _, _, Hr, Heq, Hshift' =>
      exact ⟨⟨trivial, Hr, lt_of_lt_of_le Hshift' (le_trans (add_le_add (pow_zero ω).le (le_refl _))
          (BS_denote_onePlus _).ge), trivial⟩,
        equiv_trans (add_congr (pow_zero ω) Heq) (equiv_symm (BS_denote_onePlus _))⟩
    | BN BIZ y, [], He, Hgen, _, _, _, _ =>
      exact Hgen (BS_pos _ _) (lt_of_lt_of_le (not_eps_lt _ He trivial) (le_add_right _ _))
    | BN (BIC BIZ c r) y, [], He, Hgen, _, _, _, _ =>
      exact Hgen (BS_pos _ _) (lt_of_lt_of_le (not_eps_lt _ He trivial) (le_add_right _ _))
    | BN (BIC (BIC e1 c1 r1) c r) y, [], He, _, _, _, _, _ =>
      exact ⟨He, equiv_intro (le_trans (add_zero _).le (BN_eps _ _ _ _ He (fun h => nomatch h)))
        (le_trans (normal_inflationary powOmega_normal _ (BS_complete _)) (le_add_right _ _))⟩
    | BN BIZ _, _ :: _, _, Hgen, Hne, _, _, _ => exact Hgen (BS_pos _ _) (Hne (fun h => nomatch h))
    | BN (BIC BIZ _ _) _, _ :: _, _, Hgen, Hne, _, _, _ => exact Hgen (BS_pos _ _) (Hne (fun h => nomatch h))
    | BN (BIC (BIC _ _ _) _ _) _, _ :: _, _, Hgen, Hne, _, _, _ => exact Hgen (BS_pos _ _) (Hne (fun h => nomatch h))

/-! ## The Cantor decomposition and the derived arithmetic -/

/-- Rocq: `Notation.BachmannCantor.BS_has_cantor_decomposition`. -/
def BS_has_cantor_decomposition : HasCantorDecomposition BS_denote BS_nf where
  compare := BS_compare
  decompose := BS_decompose
  recompose := BS_recompose
  complete := BS_complete
  compare_correct := BS_compare_correct
  decompose_correct := decompose_correct
  recompose_correct := recompose_correct

/-- Rocq: `Notation.BachmannCantor.BS_succ`. -/
def BS_succ : BSmall → BSmall := cantorSucc BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_add`. -/
def BS_add : BSmall → BSmall → BSmall := cantorAdd BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_mul`. -/
def BS_mul : BSmall → BSmall → BSmall := cantorMul BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_exp`. -/
def BS_exp : BSmall → BSmall → BSmall := cantorExp BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_nadd`. -/
def BS_nadd : BSmall → BSmall → BSmall := cantorNadd BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_succ_reflects`. -/
theorem BS_succ_reflects : Reflects BSmall BS_denote BS_nf (.ord ==> .ord) Ordinal.succ BS_succ :=
  cantor_succ_reflects BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_add_reflects`. -/
theorem BS_add_reflects : Reflects BSmall BS_denote BS_nf (.ord ==> .ord ==> .ord) (· + ·) BS_add :=
  cantor_add_reflects BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_mul_reflects`. -/
theorem BS_mul_reflects : Reflects BSmall BS_denote BS_nf (.ord ==> .ord ==> .ord) (· * ·) BS_mul :=
  cantor_mul_reflects BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_exp_reflects`. -/
theorem BS_exp_reflects : Reflects BSmall BS_denote BS_nf (.ord ==> .ord ==> .ord) (· ^ ·) BS_exp :=
  cantor_exp_reflects BS_has_cantor_decomposition

/-- Rocq: `Notation.BachmannCantor.BS_nadd_reflects`. -/
theorem BS_nadd_reflects : Reflects BSmall BS_denote BS_nf (.ord ==> .ord ==> .ord) (· ♯ ·) BS_nadd :=
  cantor_nadd_reflects BS_has_cantor_decomposition

end BachmannNotation

end ConstructiveOrdinals
