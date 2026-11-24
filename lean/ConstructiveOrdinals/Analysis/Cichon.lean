import ConstructiveOrdinals.GoodsteinSequences
import ConstructiveOrdinals.Analysis.Hardy

/-!
# Goodstein sequences and the Hardy hierarchy (Cichon)

Port of `Ordinal/Analysis/Cichon.v`.

Reading a hereditary base-`b` numeral as an ordinal, by replacing the base by
`ω`, does not depend on `b`, and subtracting one in base `b` is the
predecessor `P_b` (`hbn_dec_Pn`). The `i`-th step of the Goodstein sequence
subtracts one in base `i+3`, so the sequence starting at `m` first reaches
zero at step `k` exactly when `H_(o(m))(3) = k + 3`, where `o(m)` is the
ordinal of `m` in hereditary base 2 (`cichon`).

Lean notes:

- Binary `N` is `Nat`, as in `GoodsteinSequences`.
- The induction schemes `hbn_dec_mut`, `hbn_exp_dec_mut` and `hbn_dec_comb`
  are replaced by mutual structural recursion (`hbn_dec_Pn_x`,
  `hbn_dec_Pn_e`).
-/

namespace ConstructiveOrdinals.Cichon

open VNotation VForm Hardy Goodstein

/-- Rocq: `Analysis.Cichon.hbn_vf`. -/
def hbnVf : HBN → VForm
  | .z => Z
  | .term e n x => vrep n (hbnVf e) (hbnVf x)

/-- All multiplicities are positive. Rocq: `Analysis.Cichon.hbn_pos`. -/
def HbnPos : HBN → Prop
  | .z => True
  | .term e n x => 0 < n ∧ HbnPos e ∧ HbnPos x

/-- Rocq: `Analysis.Cichon.hbn_proper_pos`. -/
theorem hbn_proper_pos {base : Nat} {h : HBN} (hp : HbnProper base h) : HbnPos h := by
  induction hp with
  | z => exact trivial
  | term _ hn _ _ ihe ihx => exact ⟨hn.1, ihe, ihx⟩

/-- Rocq: `Analysis.Cichon.hbn_vf_Z`. -/
theorem hbn_vf_Z : ∀ {h : HBN}, HbnPos h → hbnVf h = Z → h = .z
  | .z, _, _ => rfl
  | .term _ (_ + 1) _, _, e => VForm.noConfusion e
  | .term _ 0 _, hp, _ => absurd hp.1 (Nat.lt_irrefl 0)

/-- Rocq: `Analysis.Cichon.hbn_term_vf`. -/
theorem hbn_term_vf (e : HBN) (n : Nat) (x : HBN) : hbnVf (hbnTerm e n x) = vrep n (hbnVf e) (hbnVf x) := by
  unfold hbnTerm
  by_cases h : n = 0
  · rw [ite_eq_left h, h]; rfl
  · rw [ite_eq_right h]; rfl

/-- Rocq: `Analysis.Cichon.hbn_term_pos`. -/
theorem hbn_term_pos {e x : HBN} (n : Nat) (he : HbnPos e) (hx : HbnPos x) : HbnPos (hbnTerm e n x) := by
  unfold hbnTerm
  by_cases h : n = 0
  · rw [ite_eq_left h]; exact hx
  · rw [ite_eq_right h]; exact ⟨Nat.pos_of_ne_zero h, he, hx⟩

private theorem pred_pos {base : Nat} (h : 1 < base) : 0 < base - 1 :=
  match base, h with
  | _ + 2, _ => Nat.zero_lt_succ _

mutual
/-- Subtracting one is the predecessor `P_b`. Rocq: `Analysis.Cichon.hbn_dec_Pn`. -/
theorem hbn_dec_Pn_x {base : Nat} (hb : 1 < base) : ∀ {x x' : HBN}, HbnDec base x x' → HbnPos x →
    HbnPos x' ∧ Pn base (hbnVf x) (hbnVf x')
  | _, _, @HbnDec.term_x _ e n _ x' h, ⟨hn, he, hx⟩ =>
    let ⟨hx', hp⟩ := hbn_dec_Pn_x hb h hx
    ⟨⟨hn, he, hx'⟩, by
      show Pn base (vrep n (hbnVf e) _) (vrep n (hbnVf e) (hbnVf x'))
      rw [vrep_vcat n (hbnVf e), vrep_vcat n (hbnVf e) (hbnVf x')]
      exact Pn_vcat hp _⟩
  | _, _, @HbnDec.term_n _ e n x h, ⟨hn, he, _⟩ =>
    let ⟨hx, hp⟩ := hbn_dec_Pn_e hb h he
    ⟨hbn_term_pos _ he hx, by
      rw [hbn_term_vf]
      match n, hn with
      | k + 1, _ =>
        show Pn base (vrep (k + 1) (hbnVf e) Z) (vrep k (hbnVf e) (hbnVf x))
        rw [vrep_S_r, vrep_vcat k (hbnVf e) (V (hbnVf e) Z), vrep_vcat k (hbnVf e) (hbnVf x)]
        exact Pn_vcat hp _⟩
/-- Rocq: `Analysis.Cichon.hbn_dec_Pn`. -/
theorem hbn_dec_Pn_e {base : Nat} (hb : 1 < base) : ∀ {e w : HBN}, HbnExpDec base e w → HbnPos e →
    HbnPos w ∧ Pn base (V (hbnVf e) Z) (hbnVf w)
  | _, _, .z, _ => ⟨trivial, .one⟩
  | _, _, .term_x h1 h2, he =>
    let ⟨he', hp1⟩ := hbn_dec_Pn_x hb h1 he
    let ⟨hw, hp2⟩ := hbn_dec_Pn_e hb h2 he'
    ⟨⟨pred_pos hb, he', hw⟩, .exp _ _ _ hp1 hp2⟩
end

/-! ## The ordinals of a Goodstein sequence -/

/-- Rocq: `Analysis.Cichon.goodstein_ord`. -/
def goodsteinOrd (m i : Nat) : VForm := hbnVf (goodsteinHbn m i)

/-- The ordinal of `m` in hereditary base 2. Rocq: `Analysis.Cichon.ord2`. -/
def ord2 (m : Nat) : VForm := hbnVf (hbnDecompose 2 (plus2_base 0) m)

/-- Rocq: `Analysis.Cichon.goodstein_ord_0`. -/
theorem goodstein_ord_0 (m : Nat) : goodsteinOrd m 0 = ord2 m := rfl

/-- Rocq: `Analysis.Cichon.goodstein_hbn_pos`. -/
theorem goodstein_hbn_pos (m i : Nat) : HbnPos (goodsteinHbn m i) :=
  hbn_proper_pos (hbn_decompose_proper _ _ _)

theorem decompose_zero (b : Nat) (H : 1 < b) : hbnDecompose b H 0 = .z :=
  hbn_decompose_unique b H 0 .z .z rfl

/-- Rocq: `Analysis.Cichon.goodstein_ord_Z`. -/
theorem goodstein_ord_Z (m i : Nat) : goodsteinOrd m i = Z ↔ goodsteinSequence m i = 0 :=
  ⟨fun h => hbn_decompose_zero _ _ _ (hbn_vf_Z (goodstein_hbn_pos m i) h),
   fun h => by
    show hbnVf (hbnDecompose (i + 2) (plus2_base i) (goodsteinSequence m i)) = Z
    rw [h, decompose_zero]
    rfl⟩

/-- Rocq: `Analysis.Cichon.goodstein_ord_step`. -/
theorem goodstein_ord_step (m i : Nat) (h : goodsteinOrd m i ≠ Z) :
    Pn (i + 3) (goodsteinOrd m i) (goodsteinOrd m (i + 1)) :=
  match goodstein_hbn_decreasing m i with
  | .inl hz => absurd (by show hbnVf (goodsteinHbn m i) = Z; rw [hz]; rfl) h
  | .inr hd => (hbn_dec_Pn_x (plus3_base i) hd (goodstein_hbn_pos m i)).2

/-! ## Cichon's theorem -/

/-- Rocq: `Analysis.Cichon.goodstein_hardy_from`. -/
theorem goodstein_hardy_from (m : Nat) : ∀ (d i : Nat), goodsteinSequence m (i + d) = 0 →
    (∀ j, i ≤ j → j < i + d → goodsteinSequence m j ≠ 0) →
    Hardy (goodsteinOrd m i) (i + 3) (i + d + 3)
  | 0, i, h0, _ => by
    rw [Nat.add_zero] at h0 ⊢
    rw [(goodstein_ord_Z m i).2 h0]
    exact .z _
  | d + 1, i, h0, hne => by
    have hi : goodsteinOrd m i ≠ Z := fun hz =>
      hne i (Nat.le_refl i) (Nat.lt_add_of_pos_right (Nat.zero_lt_succ d)) ((goodstein_ord_Z m i).1 hz)
    refine .p _ _ _ _ (goodstein_ord_step m i hi) ?_
    have e1 : i + (d + 1) = i + 1 + d := (Nat.succ_add i d).symm
    have e2 : i + 3 + 1 = i + 1 + 3 := Nat.add_right_comm i 3 1
    rw [e2, e1]
    refine goodstein_hardy_from m d (i + 1) (e1 ▸ h0) (fun j hj hjd => hne j (Nat.le_of_succ_le hj) (e1 ▸ hjd))

theorem least_below (P : Nat → Prop) [DecidablePred P] :
    ∀ k, (∀ j, j < k → ¬ P j) ∨ (∃ k0, k0 < k ∧ P k0 ∧ ∀ j, j < k0 → ¬ P j)
  | 0 => .inl (fun _ h => absurd h (Nat.not_lt_zero _))
  | k + 1 =>
    match least_below P k with
    | .inr ⟨k0, hk0, hp, hne⟩ => .inr ⟨k0, Nat.lt_succ_of_lt hk0, hp, hne⟩
    | .inl hall =>
      if hk : P k then .inr ⟨k, Nat.lt_succ_self k, hk, hall⟩
      else .inl (fun j hj => match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
        | .inl h => hall j h
        | .inr e => e ▸ hk)

/-- A least zero of the sequence. Rocq: `Analysis.Cichon.goodstein_least_zero`. -/
theorem goodstein_least_zero (m k : Nat) (hk : goodsteinSequence m k = 0) :
    ∃ k0, k0 ≤ k ∧ goodsteinSequence m k0 = 0 ∧ ∀ j, j < k0 → goodsteinSequence m j ≠ 0 :=
  match least_below (fun j => goodsteinSequence m j = 0) (k + 1) with
  | .inl hall => absurd hk (hall k (Nat.lt_succ_self k))
  | .inr ⟨k0, hk0, hp, hne⟩ => ⟨k0, Nat.le_of_lt_succ hk0, hp, hne⟩

/-- Rocq: `Analysis.Cichon.cichon`. -/
theorem cichon (m k : Nat) :
    (goodsteinSequence m k = 0 ∧ ∀ j, j < k → goodsteinSequence m j ≠ 0) ↔ Hardy (ord2 m) 3 (k + 3) := by
  constructor
  · intro ⟨hz, hne⟩
    have h := goodstein_hardy_from m k 0 (by rw [Nat.zero_add]; exact hz)
      (fun j _ hj => hne j (by rw [Nat.zero_add] at hj; exact hj))
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  · intro h
    obtain ⟨i, hi⟩ := goodstein_zero m
    obtain ⟨k0, _, hz, hne⟩ := goodstein_least_zero m i hi
    have h0 := goodstein_hardy_from m k0 0 (by rw [Nat.zero_add]; exact hz)
      (fun j _ hj => hne j (by rw [Nat.zero_add] at hj; exact hj))
    rw [Nat.zero_add, Nat.zero_add] at h0
    have e : k = k0 := Nat.add_right_cancel (hardy_fun h h0)
    subst e
    exact ⟨hz, hne⟩

/-- The sequence takes at least `H_(o(m))(3) - 3` steps to reach zero.
Rocq: `Analysis.Cichon.goodstein_length_lower`. -/
theorem goodstein_length_lower (m k h : Nat) (hk : goodsteinSequence m k = 0) (hh : Hardy (ord2 m) 3 h) :
    h ≤ k + 3 := by
  obtain ⟨k0, hle, hz, hne⟩ := goodstein_least_zero m k hk
  have h0 := (cichon m k0).1 ⟨hz, hne⟩
  rw [hardy_fun hh h0]
  exact Nat.add_le_add_right hle 3

end ConstructiveOrdinals.Cichon
