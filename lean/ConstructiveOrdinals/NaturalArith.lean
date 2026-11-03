import ConstructiveOrdinals.Cantor
import ConstructiveOrdinals.Prelude.List

/-!
# Natural (Hessenberg) arithmetic

Port of `Ordinal/NaturalArith.v`.

The natural sum `x ♯ y` (Rocq: `x ⊕ y`) is commutative, associative, absorbs
zero and is strictly monotone in both arguments. It is the smallest binary
operation with the last property. Rocq's notation `⊕` is Lean's sum type, so
this file uses `♯`, as Mathlib does, with the same precedence relative to `+`
as in Rocq (binding tighter).

The file also contains:

* the relation between natural sums and Cantor normal forms;
* a natural multiplication that turns out to be wrong (`IncorrectNmul`,
  Rocq: module `incorrect_nmul`), with a proof that it is not distributive;
* Jacobsthal multiplication `jmul` (Rocq: `a × b`), the transfinite
  iteration of natural addition;
* the smash sum and its iterates.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-! ## The natural sum -/

/-- The inner recursion of `nadd`, on the second argument. -/
def naddInner {A : Type u} (outer : A → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk B g => mk (A ⊕ B) (Sum.elim (fun a => outer a (mk B g)) (fun b => naddInner outer (g b)))

/-- The natural (Hessenberg) sum. Rocq: `NaturalArith.naddOrd`. -/
def nadd : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | mk _ f => naddInner fun a => nadd (f a)

/-- Natural sum. -/
scoped infixr:66 " ♯ " => Ordinal.nadd

/-- Rocq: `NaturalArith.naddOrd_unfold`. -/
theorem nadd_unfold (x y : Ordinal.{u}) :
    x ♯ y = (lim fun a : x => x a ♯ y) ⊔ (lim fun b : y => x ♯ y b) := by
  cases x; cases y; rfl

attribute [irreducible] nadd

theorem nadd_lt_left (x y : Ordinal.{u}) (a : x) : x a ♯ y < x ♯ y := by
  rw [nadd_unfold x y]
  exact lt_of_lt_of_le (limit_lt (fun a : x => x a ♯ y) a) (lub_le1 _ _)

theorem nadd_lt_right (x y : Ordinal.{u}) (b : y) : x ♯ y b < x ♯ y := by
  rw [nadd_unfold x y]
  exact lt_of_lt_of_le (limit_lt (fun b : y => x ♯ y b) b) (lub_le2 _ _)

/-- Anything below `x ♯ y` is below a natural sum with a smaller component. -/
theorem nadd_lt_cases {q x y : Ordinal.{u}} (h : q < x ♯ y) :
    (∃ a : x, q ≤ x a ♯ y) ∨ ∃ b : y, q ≤ x ♯ y b := by
  rw [nadd_unfold x y] at h
  match lub_lt h with
  | .inl h => exact .inl (lt_elim h)
  | .inr h => exact .inr (lt_elim h)

/-- Rocq: `NaturalArith.naddOrd_least2`. -/
theorem nadd_least2 {x y z : Ordinal.{u}} (h₁ : ∀ i : x, x i ♯ y < z) (h₂ : ∀ j : y, x ♯ y j < z) :
    x ♯ y ≤ z := by
  rw [nadd_unfold]
  exact lub_least (limit_least h₁) (limit_least h₂)

/-- Rocq: `NaturalArith.naddOrd_least3`. -/
theorem nadd_least3 {x y z : Ordinal.{u}} (h₁ : ∀ i, i < x → i ♯ y < z) (h₂ : ∀ j, j < y → x ♯ j < z) :
    x ♯ y ≤ z :=
  nadd_least2 (fun i => h₁ _ (index_lt x i)) (fun j => h₂ _ (index_lt y j))

/-- Rocq: `NaturalArith.naddOrd_le1`. -/
theorem nadd_le1 : ∀ x y : Ordinal.{u}, x ≤ x ♯ y
  | mk A f, y => le_intro fun a => lt_of_le_of_lt (nadd_le1 (f a) y) (nadd_lt_left (mk A f) y a)

/-- Rocq: `NaturalArith.naddOrd_le2`. -/
theorem nadd_le2 (x : Ordinal.{u}) : ∀ y : Ordinal.{u}, y ≤ x ♯ y
  | mk B g => le_intro fun b => lt_of_le_of_lt (nadd_le2 x (g b)) (nadd_lt_right x (mk B g) b)

/-- Rocq: `NaturalArith.naddOrd_zero_r`. -/
theorem nadd_zero_r : ∀ x : Ordinal.{u}, x ♯ 0 ≈ x
  | mk A f => equiv_intro
    (nadd_least2 (fun a => lt_of_le_of_lt (nadd_zero_r (f a)).le (index_lt (mk A f) a))
      (fun b => PEmpty.elim b))
    (nadd_le1 _ _)

/-- Rocq: `NaturalArith.naddOrd_comm_le`. -/
theorem nadd_comm_le (x : Ordinal.{u}) : ∀ y : Ordinal.{u}, x ♯ y ≤ y ♯ x := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      exact nadd_least2
        (fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) y) (nadd_lt_right y x i))
        (fun j => lt_of_le_of_lt (ihy (y j) (index_lt y j)) (nadd_lt_left y x j))

/-- Rocq: `NaturalArith.naddOrd_comm`. -/
theorem nadd_comm (x y : Ordinal.{u}) : x ♯ y ≈ y ♯ x :=
  equiv_intro (nadd_comm_le x y) (nadd_comm_le y x)

/-- Rocq: `NaturalArith.naddOrd_zero_l`. -/
theorem nadd_zero_l (x : Ordinal.{u}) : 0 ♯ x ≈ x :=
  equiv_trans (nadd_comm 0 x) (nadd_zero_r x)

/-- Rocq: `NaturalArith.naddOrd_monotone`. -/
theorem nadd_monotone (x : Ordinal.{u}) :
    ∀ y z₁ z₂ : Ordinal.{u}, x ≤ y → z₁ ≤ z₂ → x ♯ z₁ ≤ y ♯ z₂ := by
  induction x using ltRec with
  | ind x ihx =>
    intro y z₁
    induction z₁ using ltRec with
    | ind z₁ ihz =>
      intro z₂ hxy hz
      refine nadd_least2 (fun a => ?_) (fun c => ?_)
      · obtain ⟨b, hb⟩ := le_subord hxy a
        exact lt_of_le_of_lt (ihx (x a) (index_lt x a) (y b) z₁ z₂ hb hz) (nadd_lt_left y z₂ b)
      · obtain ⟨d, hd⟩ := le_subord hz c
        exact lt_of_le_of_lt (ihz (z₁ c) (index_lt z₁ c) (z₂ d) hxy hd) (nadd_lt_right y z₂ d)

/-- Rocq: `NaturalArith.naddOrd_le_mor`. -/
@[ord_mono]
theorem nadd_le_nadd {x y z₁ z₂ : Ordinal.{u}} (h₁ : x ≤ y) (h₂ : z₁ ≤ z₂) : x ♯ z₁ ≤ y ♯ z₂ :=
  nadd_monotone x y z₁ z₂ h₁ h₂

/-- Rocq: `NaturalArith.naddOrd_increasing_both`. -/
theorem nadd_increasing_both (x y z₁ z₂ : Ordinal.{u}) :
    (x < y → z₁ ≤ z₂ → x ♯ z₁ < y ♯ z₂) ∧ (x ≤ y → z₁ < z₂ → x ♯ z₁ < y ♯ z₂) :=
  ⟨fun h hz =>
    let ⟨b, hb⟩ := lt_elim h
    lt_of_le_of_lt (nadd_le_nadd hb hz) (nadd_lt_left y z₂ b),
   fun h hz =>
    let ⟨d, hd⟩ := lt_elim hz
    lt_of_le_of_lt (nadd_le_nadd h hd) (nadd_lt_right y z₂ d)⟩

/-- Rocq: `NaturalArith.naddOrd_increasing1`. -/
theorem nadd_increasing1 {x y : Ordinal.{u}} (z : Ordinal.{u}) (h : x < y) : x ♯ z < y ♯ z :=
  (nadd_increasing_both x y z z).1 h (le_refl z)

/-- Rocq: `NaturalArith.naddOrd_increasing2`. -/
theorem nadd_increasing2 {x y : Ordinal.{u}} (z : Ordinal.{u}) (h : x < y) : z ♯ x < z ♯ y :=
  (nadd_increasing_both z z x y).2 (le_refl z) h

/-- Rocq: `NaturalArith.naddOrd_lt_mor1`. -/
theorem nadd_lt_mor1 {x y z₁ z₂ : Ordinal.{u}} (h : x < y) (hz : z₁ ≤ z₂) : x ♯ z₁ < y ♯ z₂ :=
  (nadd_increasing_both x y z₁ z₂).1 h hz

/-- Rocq: `NaturalArith.naddOrd_lt_mor2`. -/
theorem nadd_lt_mor2 {x y z₁ z₂ : Ordinal.{u}} (h : x ≤ y) (hz : z₁ < z₂) : x ♯ z₁ < y ♯ z₂ :=
  (nadd_increasing_both x y z₁ z₂).2 h hz

/-- Rocq: `NaturalArith.naddOrd_eq_mor`. -/
theorem nadd_congr {x y z₁ z₂ : Ordinal.{u}} (h₁ : x ≈ y) (h₂ : z₁ ≈ z₂) : x ♯ z₁ ≈ y ♯ z₂ :=
  equiv_intro (nadd_le_nadd h₁.le h₂.le) (nadd_le_nadd h₁.ge h₂.ge)

/-- Rocq: `NaturalArith.naddOrd_assoc1`. -/
theorem nadd_assoc1 (x : Ordinal.{u}) : ∀ y z : Ordinal.{u}, x ♯ (y ♯ z) ≤ (x ♯ y) ♯ z := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      intro z
      induction z using ltRec with
      | ind z ihz =>
        refine nadd_least3 (fun i hi => ?_) (fun q hq => ?_)
        · exact lt_of_le_of_lt (ihx i hi y z) (nadd_increasing1 z (nadd_increasing1 y hi))
        · match nadd_lt_cases hq with
          | .inl ⟨b, hb⟩ =>
            exact lt_of_le_of_lt (le_trans (nadd_le_nadd (le_refl x) hb) (ihy (y b) (index_lt y b) z))
              (nadd_increasing1 z (nadd_lt_right x y b))
          | .inr ⟨c, hc⟩ =>
            exact lt_of_le_of_lt (le_trans (nadd_le_nadd (le_refl x) hc) (ihz (z c) (index_lt z c)))
              (nadd_lt_right (x ♯ y) z c)

/-- Rocq: `NaturalArith.naddOrd_assoc2`. -/
theorem nadd_assoc2 (x y z : Ordinal.{u}) : (x ♯ y) ♯ z ≤ x ♯ (y ♯ z) :=
  calc (x ♯ y) ♯ z ≤ z ♯ (x ♯ y) := nadd_comm_le _ _
    _ ≤ (z ♯ x) ♯ y := nadd_assoc1 _ _ _
    _ ≤ y ♯ (z ♯ x) := nadd_comm_le _ _
    _ ≤ (y ♯ z) ♯ x := nadd_assoc1 _ _ _
    _ ≤ x ♯ (y ♯ z) := nadd_comm_le _ _

/-- Rocq: `NaturalArith.naddOrd_assoc`. -/
theorem nadd_assoc (x y z : Ordinal.{u}) : x ♯ (y ♯ z) ≈ (x ♯ y) ♯ z :=
  equiv_intro (nadd_assoc1 x y z) (nadd_assoc2 x y z)

theorem nadd_left_comm (x y z : Ordinal.{u}) : x ♯ (y ♯ z) ≈ y ♯ (x ♯ z) :=
  equiv_trans (nadd_assoc x y z) (equiv_trans (nadd_congr (nadd_comm x y) (equiv_refl z))
    (equiv_symm (nadd_assoc y x z)))

theorem nadd_right_comm (x y z : Ordinal.{u}) : (x ♯ y) ♯ z ≈ (x ♯ z) ♯ y :=
  equiv_trans (equiv_symm (nadd_assoc x y z)) (equiv_trans (nadd_congr (equiv_refl x)
    (nadd_comm y z)) (nadd_assoc x z y))

/-- Rocq: `NaturalArith.naddOrd_cancel`. -/
theorem nadd_cancel (x : Ordinal.{u}) : ∀ y z : Ordinal.{u}, x ♯ z < y ♯ z → x < y := by
  induction x using ltRec with
  | ind x ihx =>
    intro y z
    induction z using ltRec with
    | ind z ihz =>
      intro h
      match nadd_lt_cases h with
      | .inl ⟨b, hb⟩ =>
        exact lt_intro b (le_intro fun a =>
          ihx (x a) (index_lt x a) (y b) z (lt_of_lt_of_le (nadd_lt_left x z a) hb))
      | .inr ⟨c, hc⟩ =>
        exact ihz (z c) (index_lt z c) (lt_of_lt_of_le (nadd_lt_right x z c) hc)

/-- Rocq: `NaturalArith.naddOrd_cancel_le`. -/
theorem nadd_cancel_le {x y z : Ordinal.{u}} (h : x ♯ z ≤ y ♯ z) : x ≤ y :=
  le_intro fun i => nadd_cancel _ y z (lt_of_lt_of_le (nadd_lt_left x z i) h)

/-- The natural sum is the least operation strictly monotone in both
arguments. Rocq: `NaturalArith.naddOrd_least`. -/
theorem nadd_least (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (hmono₁ : ∀ a b c, a < b → f a c < f b c) (hmono₂ : ∀ a b c, a < b → f c a < f c b)
    (x : Ordinal.{u}) : ∀ y : Ordinal.{u}, x ♯ y ≤ f x y := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      exact nadd_least3 (fun i hi => lt_of_le_of_lt (ihx i hi y) (hmono₁ i x y hi))
        (fun j hj => lt_of_le_of_lt (ihy j hj) (hmono₂ j y x hj))

/-- Rocq: `NaturalArith.naddOrd_succ`. -/
theorem nadd_succ (x y : Ordinal.{u}) : succ x ♯ y ≈ succ (x ♯ y) := by
  refine equiv_intro ?_ (succ_least (nadd_increasing1 y (succ_lt x)))
  induction y using ltRec with
  | ind y ih =>
    exact nadd_least3
      (fun i hi => lt_of_le_of_lt (nadd_le_nadd ((lt_elim hi).elim fun _ h => h) (le_refl y))
        (succ_lt _))
      (fun j hj => lt_of_le_of_lt (ih j hj) (succ_increasing (nadd_increasing2 x hj)))

/-- Rocq: `NaturalArith.naddOrd_succ2`. -/
theorem nadd_succ2 (x y : Ordinal.{u}) : x ♯ succ y ≈ succ (x ♯ y) :=
  equiv_trans (nadd_comm x _) (equiv_trans (nadd_succ y x) (succ_congruence (nadd_comm y x)))

/-- Rocq: `NaturalArith.add_nadd_le`. -/
theorem add_nadd_le (x y : Ordinal.{u}) : x + y ≤ x ♯ y := by
  induction y using ltRec with
  | ind y ih =>
    rw [add_unfold]
    exact lub_least (nadd_le1 x y) (sup_least fun a =>
      succ_least (lt_of_le_of_lt (ih (y a) (index_lt y a)) (nadd_lt_right x y a)))

/-- Rocq: `NaturalArith.add_nadd_assoc1`. -/
theorem add_nadd_assoc1 (x : Ordinal.{u}) : ∀ y z : Ordinal.{u}, x + (y ♯ z) ≤ (x + y) ♯ z := by
  intro y
  induction y using ltRec with
  | ind y ihy =>
    intro z
    induction z using ltRec with
    | ind z ihz =>
      rw [add_unfold]
      refine lub_least (le_trans (le_add_right x y) (nadd_le1 _ _)) (sup_least fun q => succ_least ?_)
      match nadd_lt_cases (index_lt (y ♯ z) q) with
      | .inl ⟨b, hb⟩ =>
        exact lt_of_le_of_lt (le_trans (add_le_add (le_refl x) hb) (ihy (y b) (index_lt y b) z))
          (nadd_increasing1 z (add_lt_add_left x (index_lt y b)))
      | .inr ⟨c, hc⟩ =>
        exact lt_of_le_of_lt (le_trans (add_le_add (le_refl x) hc) (ihz (z c) (index_lt z c)))
          (nadd_lt_right _ z c)

/-- Rocq: `NaturalArith.nadd_1_omega`. -/
theorem nadd_1_omega : (1 : Ordinal.{u}) ♯ ω ≈ ω + 1 :=
  equiv_trans (nadd_comm 1 ω) (equiv_trans (nadd_succ2 ω 0)
    (equiv_trans (succ_congruence (nadd_zero_r ω))
      (equiv_symm (equiv_trans (add_succ ω 0) (succ_congruence (add_zero ω))))))

/-- Natural sums do not associate with ordinal sums in this direction.
Rocq: `NaturalArith.add_nadd_assoc_impossible`. -/
theorem add_nadd_assoc_impossible :
    ¬ ∀ x y z : Ordinal.{u}, (x + y) ♯ z ≤ x + (y ♯ z) := fun H => by
  have h₁ : (1 : Ordinal.{u}) + (1 ♯ ω) ≤ 1 ♯ ω :=
    calc (1 : Ordinal.{u}) + (1 ♯ ω) ≤ 1 + (ω + 1) := add_le_add (le_refl 1) nadd_1_omega.le
      _ ≤ 1 + ω + 1 := (add_assoc 1 ω 1).le
      _ ≤ ω + 1 := add_le_add (additively_closed_collapse additively_closed_omega omega_gt1)
          (le_refl 1)
      _ ≤ 1 ♯ ω := nadd_1_omega.ge
  have h₂ := nadd_cancel_le (le_trans (H 1 1 ω) h₁)
  exact lt_irrefl (1 : Ordinal.{u}) (lt_of_lt_of_le (lt_of_lt_of_le (succ_lt 1)
    (le_trans (succ_monotone (add_zero 1).ge) (add_succ 1 0).ge)) h₂)

/-- Rocq: `NaturalArith.add_nadd_assoc2`. -/
theorem add_nadd_assoc2 (x : Ordinal.{u}) : ∀ y z : Ordinal.{u},
    (∀ q, q ≤ z → x ♯ q ≤ x + q) → (x + y) ♯ z ≤ x + (y ♯ z) := by
  intro y
  induction y using ltRec with
  | ind y ihy =>
    intro z
    induction z using ltRec with
    | ind z ihz =>
      intro H
      refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
      · match add_lt hi with
        | .inl h =>
          exact lt_of_lt_of_le (nadd_increasing1 z h)
            (le_trans (H z (le_refl z)) (add_le_add (le_refl x) (nadd_le2 y z)))
        | .inr ⟨b, hb⟩ =>
          exact lt_of_le_of_lt (le_trans (nadd_le_nadd hb (le_refl z)) (ihy (y b) (index_lt y b) z H))
            (add_lt_add_left x (nadd_increasing1 z (index_lt y b)))
      · exact lt_of_le_of_lt (ihz j hj fun q hq => H q (le_trans hq (le_of_lt hj)))
          (add_lt_add_left x (nadd_increasing2 y hj))

/-! ## Natural sums of powers of ω

These results use the excluded middle, through Cantor normal forms.
-/

private theorem cantorDenote_lt_cons (o : Ordinal.{u}) :
    ∀ ls : List Ordinal.{u}, CantorSequence o ls → cantorDenote ls < ω ^ o + cantorDenote ls
  | [], _ => lt_of_lt_of_le (pow_pos ω o) (le_add_right _ _)
  | y :: ys, ⟨hy, hys⟩ =>
    lt_of_le_of_lt (add_le_add (pow_le_pow_right ω hy) (le_refl _))
      (add_lt_add_left _ (cantorDenote_lt_cons y ys hys))

/-- Rocq: `NaturalArith.leading_cantor_term`. -/
theorem leading_cantor_term (em : ExcludedMiddle) (n : Nat) (a q : Ordinal.{u})
    (h₁ : ω ^ a ≤ q) (h₂ : q ≤ ω ^ a * ofNat (n + 1)) : ∃ q', q' < q ∧ q ≈ ω ^ a + q' := by
  obtain ⟨ls, hseq, hd⟩ := cantor_decomposition em q
  match ls, hseq, hd with
  | [], _, hd => exact (lt_irrefl 0 (lt_of_lt_of_le (pow_pos ω a) (le_trans h₁ hd.ge))).elim
  | o :: ls, ⟨_, hls⟩, hd =>
    have ho : o ≈ a := match order_trichotomy em o a with
      | .inl hoa =>
        (lt_irrefl q (lt_of_le_of_lt hd.ge (lt_of_lt_of_le
          (powOmega_additively_closed (ord_complete em a) _ _ (pow_lt_pow_right omega_gt1 hoa)
            (cantorDenote_lt em ls o a hls hoa)) h₁))).elim
      | .inr (.inl h) => h
      | .inr (.inr hao) =>
        let ⟨j, hj⟩ := lt_elim hao
        (lt_irrefl q (lt_of_le_of_lt h₂ (lt_of_lt_of_le
          (lt_of_le_of_lt (mul_le_mul_right _ (pow_le_pow_right ω hj))
            (mul_lt_mul_left (pow_pos ω _) (index_lt ω ⟨n + 1⟩)))
          (le_trans (pow_index_mul_omega_le o j) (le_trans (le_add_right _ _) hd.le))))).elim
    exact ⟨cantorDenote ls, lt_of_lt_of_le (cantorDenote_lt_cons o ls hls) hd.le,
      equiv_trans (equiv_symm hd) (add_congr (pow_congr (equiv_refl ω) ho) (equiv_refl _))⟩

section nadd_closed

variable (em : ExcludedMiddle) (a : Ordinal.{u}) (ha : Complete a)
  (hind : ∀ a' : Ordinal.{u}, a' ≤ a → ∀ x y : Ordinal.{u}, Complete a' →
    x < ω ^ a' → y < ω ^ a' → x ♯ y < ω ^ a')

include ha hind in
private theorem pow_nadd_le_add (q₀ : Ordinal.{u}) : q₀ < ω ^ a → ω ^ a ♯ q₀ ≤ ω ^ a + q₀ := by
  induction q₀ using ltRec with
  | ind q₀ ih =>
    intro hq₀
    exact nadd_least3 (fun i hi => lt_of_lt_of_le (hind a (le_refl a) i q₀ ha hi hq₀) (le_add_right _ _))
      (fun j hj => lt_of_le_of_lt (ih j hj (lt_trans hj hq₀)) (add_lt_add_left _ hj))

include em ha hind in
/-- Rocq: `NaturalArith.nadd_closed_technical1`. -/
theorem nadd_closed_technical1 (n : Nat) (q : Ordinal.{u}) :
    ∀ r : Ordinal.{u}, r < ω ^ a → q ≤ ω ^ a * succ (ofNat n) → r ♯ q < ω ^ a + q := by
  induction q using ltRec with
  | ind q ih =>
    intro r hr hq
    match order_total em (ω ^ a) q with
    | .inl hle =>
      obtain ⟨q', hq', hqe⟩ := leading_cantor_term em n a q hle hq
      calc r ♯ q ≤ r ♯ (ω ^ a + q') := nadd_le_nadd (le_refl r) hqe.le
        _ ≤ (ω ^ a + q') ♯ r := nadd_comm_le _ _
        _ ≤ ω ^ a + (q' ♯ r) :=
            add_nadd_assoc2 _ _ _ fun q₀ hq₀ => pow_nadd_le_add a ha hind q₀ (lt_of_le_of_lt hq₀ hr)
        _ ≤ ω ^ a + (r ♯ q') := add_le_add (le_refl _) (nadd_comm_le _ _)
        _ < ω ^ a + (ω ^ a + q') :=
            add_lt_add_left _ (ih q' hq' r hr (le_trans (le_of_lt hq') hq))
        _ ≤ ω ^ a + q := add_le_add (le_refl _) hqe.ge
    | .inr hlt => exact lt_of_lt_of_le (hind a (le_refl a) r q ha hr hlt) (le_add_right _ _)

include em ha hind in
/-- Rocq: `NaturalArith.nadd_closed_technical2`. -/
theorem nadd_closed_technical2 (m : Nat) : ∀ (n : Nat) (q : Ordinal.{u}),
    q ≤ ω ^ a * succ (ofNat n) → ω ^ a * ofNat m ♯ q ≤ ω ^ a * ofNat m + q := by
  induction m with
  | zero =>
    intro n q _
    exact le_trans (nadd_le_nadd (mul_zero _).le (le_refl q))
      (le_trans (nadd_zero_l q).le (le_add_left _ q))
  | succ m ihm =>
    intro n q
    induction q using ltRec with
    | ind q ihq =>
      intro hq
      refine nadd_least3 (fun i hi => ?_) (fun j hj =>
        lt_of_le_of_lt (ihq j hj (le_trans (le_of_lt hj) hq)) (add_lt_add_left _ hj))
      match add_lt (lt_of_lt_of_le hi (mul_succ (ω ^ a) (ofNat m)).le) with
      | .inl h =>
        exact lt_of_lt_of_le (nadd_increasing1 q h) (le_trans (ihm n q hq)
          (add_le_add (mul_le_mul_left _ (ofNat_monotone (Nat.le_succ m))) (le_refl q)))
      | .inr ⟨r, hr⟩ =>
        calc i ♯ q ≤ (ω ^ a * ofNat m + (ω ^ a) r) ♯ q := nadd_le_nadd hr (le_refl q)
          _ ≤ ω ^ a * ofNat m + ((ω ^ a) r ♯ q) :=
              add_nadd_assoc2 _ _ _ fun q₀ hq₀ => ihm n q₀ (le_trans hq₀ hq)
          _ < ω ^ a * ofNat m + (ω ^ a + q) :=
              add_lt_add_left _ (nadd_closed_technical1 em a ha hind n q _ (index_lt _ r) hq)
          _ ≤ ω ^ a * ofNat m + ω ^ a + q := (add_assoc _ _ _).le
          _ ≤ ω ^ a * ofNat (m + 1) + q := add_le_add (mul_succ _ _).ge (le_refl q)

include em ha hind in
/-- Rocq: `NaturalArith.nadd_add_same_powers_step`. -/
theorem nadd_add_same_powers_step (m n : Nat) :
    ω ^ a * ofNat (m + 1) ♯ ω ^ a * ofNat (n + 1) ≤ ω ^ a * (ω : Ordinal.{u}) ⟨m + n + 2⟩ := by
  have hnat : n + 1 + (m + 1) = m + n + 2 := by
    show (n + 1 + m) + 1 = (m + n + 1) + 1
    rw [Nat.add_right_comm n 1 m, Nat.add_comm n m]
  calc ω ^ a * ofNat (m + 1) ♯ ω ^ a * ofNat (n + 1)
      ≤ ω ^ a * ofNat (m + 1) + ω ^ a * ofNat (n + 1) :=
        nadd_closed_technical2 em a ha hind (m + 1) n _ (le_refl _)
    _ ≤ ω ^ a * (ofNat (m + 1) + ofNat (n + 1)) := (mul_add _ _ _).ge
    _ ≤ ω ^ a * ofNat (n + 1 + (m + 1)) := mul_le_mul_left _ (ofNat_add (n + 1) (m + 1)).ge
    _ = ω ^ a * ofNat (m + n + 2) := by rw [hnat]

end nadd_closed

/-- Powers of ω are closed under natural sums. Rocq: `NaturalArith.nadd_closed`. -/
theorem nadd_closed (em : ExcludedMiddle) (a : Ordinal.{u}) :
    ∀ x y : Ordinal.{u}, Complete a → x < ω ^ a → y < ω ^ a → x ♯ y < ω ^ a := by
  induction a using ltRec with
  | ind a ih =>
    intro x y ha hx hy
    have hx' := hx
    have hy' := hy
    rw [pow_unfold] at hx' hy'
    match lub_lt hx' with
    | .inl hx₁ =>
      obtain ⟨_, hx₀⟩ := lt_elim hx₁
      exact lt_of_le_of_lt (le_trans (nadd_le_nadd hx₀ (le_refl y)) (nadd_zero_l y).le) hy
    | .inr hxs =>
      match lub_lt hy' with
      | .inl hy₁ =>
        obtain ⟨_, hy₀⟩ := lt_elim hy₁
        exact lt_of_le_of_lt (le_trans (nadd_le_nadd (le_refl x) hy₀) (nadd_zero_r x).le) hx
      | .inr hys =>
        obtain ⟨i, hxi⟩ := sup_lt hxs
        obtain ⟨j, hyj⟩ := sup_lt hys
        obtain ⟨k, hk₁, hk₂⟩ := complete_directed ha i j
        rw [mul_unfold] at hxi hyj
        obtain ⟨⟨m⟩, hxm⟩ := sup_lt hxi
        obtain ⟨⟨n⟩, hyn⟩ := sup_lt hyj
        have hbound : ∀ (c : a.Carrier) (z : Ordinal.{u}) (p : Nat), a c ≤ a k →
            z < ω ^ a c * ofNat p + ω ^ a c → z ≤ ω ^ a k * ofNat (p + 1) :=
          fun c z p hc hz => le_trans (le_of_lt hz) (le_trans (mul_succ _ _).ge
            (mul_le_mul_right _ (pow_le_pow_right ω hc)))
        calc x ♯ y ≤ ω ^ a k * ofNat (m + 1) ♯ ω ^ a k * ofNat (n + 1) :=
              nadd_le_nadd (hbound i x m hk₁ hxm) (hbound j y n hk₂ hyn)
          _ ≤ ω ^ a k * (ω : Ordinal.{u}) ⟨m + n + 2⟩ :=
              nadd_add_same_powers_step em (a k) (complete_subord ha k)
                (fun a' h x y hc => ih a' (lt_of_le_of_lt h (index_lt a k)) x y hc) m n
          _ < ω ^ a k * ω := mul_lt_mul_left (pow_pos ω _) (index_lt ω ⟨m + n + 2⟩)
          _ ≤ ω ^ a := pow_index_mul_omega_le a k

/-- Rocq: `NaturalArith.nadd_add_same_powers`. -/
theorem nadd_add_same_powers (em : ExcludedMiddle) (a : Ordinal.{u}) (m n : (ω : Ordinal.{u}).Carrier)
    (ha : Complete a) : ω ^ a * ω m ♯ ω ^ a * ω n ≤ ω ^ a * (ω : Ordinal.{u}) ⟨m.down + n.down⟩ := by
  obtain ⟨m⟩ := m
  obtain ⟨n⟩ := n
  match m, n with
  | 0, n =>
    show ω ^ a * ofNat 0 ♯ ω ^ a * ofNat n ≤ ω ^ a * ofNat (0 + n)
    rw [Nat.zero_add]
    exact le_trans (nadd_le_nadd (mul_zero _).le (le_refl _)) (nadd_zero_l _).le
  | m + 1, 0 =>
    exact le_trans (nadd_le_nadd (le_refl _) (mul_zero _).le) (nadd_zero_r _).le
  | m + 1, n + 1 =>
    have hnat : m + 1 + (n + 1) = m + n + 2 := by
      show (m + 1 + n) + 1 = (m + n + 1) + 1
      rw [Nat.add_right_comm m 1 n]
    show ω ^ a * ofNat (m + 1) ♯ ω ^ a * ofNat (n + 1) ≤ ω ^ a * ofNat (m + 1 + (n + 1))
    rw [hnat]
    exact nadd_add_same_powers_step em a ha (fun a' _ x y hc => nadd_closed em a' x y hc) m n

/-! ## Natural sums and Cantor normal forms -/

/-- Rocq: `NaturalArith.cantor_denote_app`. -/
theorem cantor_denote_app : ∀ xs ys : List Ordinal.{u},
    cantorDenote (xs ++ ys) ≈ cantorDenote xs + cantorDenote ys
  | [], ys => equiv_symm (zero_add _)
  | x :: xs, ys => equiv_trans (add_congr (equiv_refl _) (cantor_denote_app xs ys)) (add_assoc _ _ _)

/-- Rocq: `NaturalArith.each_app`. -/
theorem each_app {A : Type u} (P : A → Prop) : ∀ xs ys : List A,
    Each P (xs ++ ys) → Each P xs ∧ Each P ys
  | [], _, h => ⟨trivial, h⟩
  | _ :: xs, ys, ⟨hx, h⟩ => let ⟨h₁, h₂⟩ := each_app P xs ys h; ⟨⟨hx, h₁⟩, h₂⟩

/-- Rocq: `NaturalArith.cantor_sequence_le1`. -/
theorem cantor_sequence_le1 : ∀ (xs : List Ordinal.{u}) (x : Ordinal.{u}),
    CantorSequence x xs → ∀ x', x' ∈ xs → x' ≤ x
  | _ :: _, _, ⟨hy, _⟩, _, .head _ => hy
  | _ :: ys, _, ⟨hy, hys⟩, x', .tail _ h => le_trans (cantor_sequence_le1 ys _ hys x' h) hy

/-- Rocq: `NaturalArith.cantor_sequence_le`. -/
theorem cantor_sequence_le : ∀ (xs : List Ordinal.{u}) (x : Ordinal.{u}) (ys : List Ordinal.{u}),
    CantorSequence x (xs ++ ys) → ∀ x' y, x' ∈ xs → y ∈ ys → y ≤ x'
  | _ :: xs, _, ys, ⟨_, hseq⟩, _, y, .head _, hy =>
    cantor_sequence_le1 _ _ hseq y (List.mem_append_right xs hy)
  | _ :: xs, _, ys, ⟨_, hseq⟩, x', y, .tail _ h, hy => cantor_sequence_le xs _ ys hseq x' y h hy

/-- `ω ^ x ♯ q ≤ ω ^ x + q` when `q ≤ ω ^ x`. -/
private theorem pow_nadd_le (em : ExcludedMiddle) {x : Ordinal.{u}} (hx : Complete x)
    (q : Ordinal.{u}) : q ≤ ω ^ x → ω ^ x ♯ q ≤ ω ^ x + q := by
  induction q using ltRec with
  | ind q ih =>
    intro hq
    exact nadd_least3
      (fun i hi => nadd_closed_technical1 em x hx (fun a' _ x y hc => nadd_closed em a' x y hc) 0 q i hi
        (le_trans hq (mul_one _).ge))
      (fun j hj => lt_of_le_of_lt (ih j hj (le_trans (le_of_lt hj) hq)) (add_lt_add_left _ hj))

/-- Rocq: `NaturalArith.cantor_denote_nadd_add`. -/
theorem cantor_denote_nadd_add (em : ExcludedMiddle) : ∀ (xs : List Ordinal.{u}) (b : Ordinal.{u}),
    Each Complete xs → (∀ a, a ∈ xs → b ≤ a) → ∀ q, q ≤ ω ^ b →
      cantorDenote xs ♯ q ≤ cantorDenote xs + q
  | [], _, _, _, q, _ => le_trans (nadd_zero_l q).le (le_add_left _ q)
  | x :: xs, b, ⟨hx, hxs⟩, hb, q, hq =>
    calc (ω ^ x + cantorDenote xs) ♯ q ≤ ω ^ x + (cantorDenote xs ♯ q) :=
          add_nadd_assoc2 _ _ _ fun q₀ hq₀ => pow_nadd_le em hx q₀
            (le_trans hq₀ (le_trans hq (pow_le_pow_right ω (hb x (.head _)))))
      _ ≤ ω ^ x + (cantorDenote xs + q) :=
          add_le_add (le_refl _) (cantor_denote_nadd_add em xs b hxs (fun a h => hb a (.tail _ h)) q hq)
      _ ≤ ω ^ x + cantorDenote xs + q := (add_assoc _ _ _).le

/-- The ordinal denoted by a list of exponents using natural sums.
Rocq: `NaturalArith.cantor_denote_nadd`. -/
def cantorDenoteNadd : List Ordinal.{u} → Ordinal.{u}
  | [] => 0
  | x :: xs => ω ^ x ♯ cantorDenoteNadd xs

/-- Rocq: `NaturalArith.cantor_denote_nadd_app`. -/
theorem cantor_denote_nadd_app : ∀ xs ys : List Ordinal.{u},
    cantorDenoteNadd (xs ++ ys) ≈ cantorDenoteNadd xs ♯ cantorDenoteNadd ys
  | [], ys => equiv_symm (nadd_zero_l _)
  | x :: xs, ys =>
    equiv_trans (nadd_congr (equiv_refl _) (cantor_denote_nadd_app xs ys)) (nadd_assoc _ _ _)

/-- Rocq: `NaturalArith.cantor_sequence_app1`. -/
theorem cantor_sequence_app1 : ∀ (xs : List Ordinal.{u}) (x : Ordinal.{u}) (ys : List Ordinal.{u}),
    CantorSequence x (xs ++ ys) → CantorSequence x xs
  | [], _, _, _ => trivial
  | _ :: xs, _, ys, ⟨hy, h⟩ => ⟨hy, cantor_sequence_app1 xs _ ys h⟩

/-- For Cantor normal forms, ordinary and natural sums agree.
Rocq: `NaturalArith.cantor_denote_nadd_eq`. -/
theorem cantor_denote_nadd_eq (em : ExcludedMiddle) (xs : List Ordinal.{u}) :
    ∀ x : Ordinal.{u}, Each Complete xs → CantorSequence x xs → cantorDenote xs ≈ cantorDenoteNadd xs := by
  induction xs using List.rev_ind with
  | hnil => intro _ _ _; exact equiv_refl _
  | hsnoc z ys ih =>
    intro x hxs hseq
    obtain ⟨hys, ⟨hz, _⟩⟩ := each_app _ ys [z] hxs
    calc cantorDenote (ys ++ [z]) ≈ cantorDenote ys + (ω ^ z + 0) := cantor_denote_app ys [z]
      _ ≈ cantorDenote ys + ω ^ z := add_congr (equiv_refl _) (add_zero _)
      _ ≈ cantorDenote ys ♯ ω ^ z := equiv_intro (add_nadd_le _ _)
          (cantor_denote_nadd_add em ys z hys
            (fun a ha => cantor_sequence_le ys x [z] hseq a z ha (.head _)) _ (le_refl _))
      _ ≈ cantorDenoteNadd ys ♯ ω ^ z :=
          nadd_congr (ih x hys (cantor_sequence_app1 ys x [z] hseq)) (equiv_refl _)
      _ ≈ cantorDenoteNadd ys ♯ (ω ^ z ♯ 0) := nadd_congr (equiv_refl _) (equiv_symm (nadd_zero_r _))
      _ ≈ cantorDenoteNadd (ys ++ [z]) := equiv_symm (cantor_denote_nadd_app ys [z])

/-- `zs` is an interleaving of `xs` and `ys`. Rocq: `NaturalArith.merge_lists`. -/
inductive MergeLists {A : Type u} : List A → List A → List A → Prop
  /-- Rocq: `merge_lists_nil`. -/
  | nil : MergeLists [] [] []
  /-- Rocq: `merge_lists_left`. -/
  | left (x : A) {xs ys zs} : MergeLists xs ys zs → MergeLists (x :: xs) ys (x :: zs)
  /-- Rocq: `merge_lists_right`. -/
  | right {xs} (y : A) {ys zs} : MergeLists xs ys zs → MergeLists xs (y :: ys) (y :: zs)

/-- Rocq: `NaturalArith.cantor_denote_nadd_merge`. -/
theorem cantor_denote_nadd_merge {xs ys zs : List Ordinal.{u}} (h : MergeLists xs ys zs) :
    cantorDenoteNadd xs ♯ cantorDenoteNadd ys ≈ cantorDenoteNadd zs := by
  induction h with
  | nil => exact nadd_zero_r _
  | left x _ ih => exact equiv_trans (equiv_symm (nadd_assoc _ _ _)) (nadd_congr (equiv_refl _) ih)
  | right y _ ih =>
    exact equiv_trans (nadd_left_comm _ _ _) (nadd_congr (equiv_refl _) ih)

private theorem each_complete (em : ExcludedMiddle) : ∀ xs : List Ordinal.{u}, Each Complete xs
  | [] => trivial
  | x :: xs => ⟨ord_complete em x, each_complete em xs⟩

/-- Natural sums of Cantor normal forms merge their exponents.
Rocq: `NaturalArith.nadd_cantor_sequences`. -/
theorem nadd_cantor_sequences (em : ExcludedMiddle) {xs ys zs : List Ordinal.{u}}
    (hm : MergeLists xs ys zs) (a b c : Ordinal.{u}) (hxs : CantorSequence a xs)
    (hys : CantorSequence b ys) (hzs : CantorSequence c zs) :
    cantorDenote xs ♯ cantorDenote ys ≈ cantorDenote zs :=
  equiv_trans (nadd_congr (cantor_denote_nadd_eq em xs a (each_complete em xs) hxs)
      (cantor_denote_nadd_eq em ys b (each_complete em ys) hys))
    (equiv_trans (cantor_denote_nadd_merge hm)
      (equiv_symm (cantor_denote_nadd_eq em zs c (each_complete em zs) hzs)))

/-! ## An incorrect natural multiplication

Rocq module `incorrect_nmul`. This candidate definition of
natural multiplication turns out to be wrong: it does not distribute over
natural addition, as `nmul_not_distributive` shows.
-/

namespace IncorrectNmul

/-- The inner recursion of `nmul`, on the second argument. -/
def nmulInner (x : Ordinal.{u}) {A : Type u} (outer : A → Ordinal.{u} → Ordinal.{u}) :
    Ordinal.{u} → Ordinal.{u}
  | mk B g => (sup fun a => outer a (mk B g) ♯ mk B g) ⊔ (sup fun b => nmulInner x outer (g b) ♯ x)

/-- Rocq: `NaturalArith.nmulOrd`. -/
def nmul : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | mk A f => nmulInner (mk A f) fun a => nmul (f a)

/-- The incorrect natural product (Rocq: `x ⊗ y`). -/
scoped infixr:67 " ⨳ " => IncorrectNmul.nmul

/-- Rocq: `NaturalArith.nmulOrd_unfold`. -/
theorem nmul_unfold (x y : Ordinal.{u}) :
    x ⨳ y = (sup fun a : x => x a ⨳ y ♯ y) ⊔ (sup fun b : y => x ⨳ y b ♯ x) := by
  cases x; cases y; rfl

attribute [irreducible] nmul

/-- Rocq: `NaturalArith.nmulOrd_stepl`. -/
theorem nmul_stepl (x y : Ordinal.{u}) (i : x) : x i ⨳ y ♯ y ≤ x ⨳ y := by
  rw [nmul_unfold x y]
  exact le_trans (sup_le (fun a : x => x a ⨳ y ♯ y) i) (lub_le1 _ _)

/-- Rocq: `NaturalArith.nmulOrd_stepr`. -/
theorem nmul_stepr (x y : Ordinal.{u}) (i : y) : x ⨳ y i ♯ x ≤ x ⨳ y := by
  rw [nmul_unfold x y]
  exact le_trans (sup_le (fun b : y => x ⨳ y b ♯ x) i) (lub_le2 _ _)

/-- Rocq: `NaturalArith.nmulOrd_comm_le`. -/
theorem nmul_comm_le (x : Ordinal.{u}) : ∀ y : Ordinal.{u}, x ⨳ y ≤ y ⨳ x := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      rw [nmul_unfold x y]
      exact lub_least
        (sup_least fun a => le_trans (nadd_le_nadd (ihx (x a) (index_lt x a) y) (le_refl y))
          (nmul_stepr y x a))
        (sup_least fun b => le_trans (nadd_le_nadd (ihy (y b) (index_lt y b)) (le_refl x))
          (nmul_stepl y x b))

/-- Rocq: `NaturalArith.nmulOrd_comm`. -/
theorem nmul_comm (x y : Ordinal.{u}) : x ⨳ y ≈ y ⨳ x :=
  equiv_intro (nmul_comm_le x y) (nmul_comm_le y x)

/-- Rocq: `NaturalArith.nmulOrd_monotone`. -/
theorem nmul_monotone (x : Ordinal.{u}) : ∀ y a b : Ordinal.{u}, a ≤ x → b ≤ y → a ⨳ b ≤ x ⨳ y := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      intro a b ha hb
      rw [nmul_unfold a b]
      refine lub_least (sup_least fun ai => ?_) (sup_least fun bi => ?_)
      · obtain ⟨xi, hxi⟩ := le_subord ha ai
        exact le_trans (nadd_le_nadd (ihx (x xi) (index_lt x xi) y _ _ hxi hb) hb) (nmul_stepl x y xi)
      · obtain ⟨yi, hyi⟩ := le_subord hb bi
        exact le_trans (nadd_le_nadd (ihy (y yi) (index_lt y yi) _ _ ha hyi) ha) (nmul_stepr x y yi)

/-- Rocq: `NaturalArith.nmulOrd_le_mor`. -/
@[ord_mono]
theorem nmul_le_nmul {x y x₀ y₀ : Ordinal.{u}} (h : x ≤ y) (h₀ : x₀ ≤ y₀) : x ⨳ x₀ ≤ y ⨳ y₀ :=
  nmul_monotone y y₀ x x₀ h h₀

/-- As stated in Rocq, this lemma is about `♯` (Rocq: `⊕`) rather than `⨳`,
apparently a copy-paste slip; it is ported as stated.
Rocq: `NaturalArith.nmulOrd_eq_mor`. -/
theorem nmul_eq_mor {x y x₀ y₀ : Ordinal.{u}} (h : x ≈ y) (h₀ : x₀ ≈ y₀) : x ♯ x₀ ≈ y ♯ y₀ :=
  nadd_congr h h₀

/-- Rocq: `NaturalArith.nmulOrd_increasing2`. -/
theorem nmul_increasing2 {x y z₁ z₂ : Ordinal.{u}} (h : x < y) (hz₁ : 0 < z₁) (hz : z₁ ≤ z₂) :
    x ⨳ z₁ < y ⨳ z₂ := by
  obtain ⟨b, hb⟩ := lt_elim h
  refine lt_of_le_of_lt (nmul_le_nmul hb hz) (lt_of_lt_of_le ?_ (nmul_stepl y z₂ b))
  exact lt_of_le_of_lt (nadd_zero_r _).ge (nadd_increasing2 _ (lt_of_lt_of_le hz₁ hz))

/-- Rocq: `NaturalArith.nmulOrd_increasing1`. -/
theorem nmul_increasing1 {x y z₁ z₂ : Ordinal.{u}} (h : x < y) (hz₁ : 0 < z₁) (hz : z₁ ≤ z₂) :
    z₁ ⨳ x < z₂ ⨳ y :=
  lt_of_le_of_lt (nmul_comm z₁ x).le (lt_of_lt_of_le (nmul_increasing2 h hz₁ hz) (nmul_comm y z₂).le)

/-- Rocq: `NaturalArith.nmulOrd_zero`. -/
theorem nmul_zero : ∀ x : Ordinal.{u}, x ⨳ 0 ≈ 0
  | mk A f => by
    refine equiv_intro ?_ (zero_least _)
    rw [nmul_unfold]
    exact lub_least (sup_least fun a => le_trans (nadd_zero_r _).le (nmul_zero (f a)).le)
      (sup_least fun b => PEmpty.elim b)

/-- Rocq: `NaturalArith.nmulOrd_one`. -/
theorem nmul_one : ∀ x : Ordinal.{u}, x ⨳ 1 ≈ x
  | mk A f => by
    refine equiv_intro ?_ (le_trans (nadd_le2 _ _) (nmul_stepr (mk A f) 1 PUnit.unit))
    rw [nmul_unfold]
    refine lub_least (sup_least fun a => ?_) (sup_least fun _ => ?_)
    · exact le_trans (nadd_le_nadd (nmul_one (f a)).le (le_refl 1))
        (le_trans (nadd_succ2 _ 0).le (succ_least (lt_of_le_of_lt (nadd_zero_r _).le
          (index_lt (mk A f) a))))
    · exact le_trans (nadd_le_nadd (nmul_zero _).le (le_refl _)) (nadd_zero_l _).le

/-- Rocq: `NaturalArith.nmulOrd_succ`. -/
theorem nmul_succ (x y : Ordinal.{u}) : succ x ⨳ y ≈ x ⨳ y ♯ y := by
  induction y using ltRec with
  | ind y ih =>
    refine equiv_intro ?_ (nmul_stepl (succ x) y PUnit.unit)
    rw [nmul_unfold (succ x) y]
    refine lub_least (sup_least fun _ => le_refl _) (sup_least fun a => ?_)
    calc succ x ⨳ y a ♯ succ x ≤ (x ⨳ y a ♯ y a) ♯ succ x := nadd_le_nadd (ih (y a) (index_lt y a)).le (le_refl _)
      _ ≤ succ ((x ⨳ y a ♯ y a) ♯ x) := (nadd_succ2 _ _).le
      _ ≤ x ⨳ y ♯ y := succ_least (calc
          (x ⨳ y a ♯ y a) ♯ x ≤ (x ⨳ y a ♯ x) ♯ y a := (nadd_right_comm _ _ _).le
          _ < (x ⨳ y a ♯ x) ♯ y := nadd_increasing2 _ (index_lt y a)
          _ ≤ x ⨳ y ♯ y := nadd_le_nadd (nmul_stepr x y a) (le_refl y))

/-- Rocq: `NaturalArith.nmulDistrib1`. -/
theorem nmulDistrib1 (x : Ordinal.{u}) : ∀ y z : Ordinal.{u}, x ⨳ (y ♯ z) ≤ x ⨳ y ♯ x ⨳ z := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      intro z
      induction z using ltRec with
      | ind z ihz =>
        rw [nmul_unfold x (y ♯ z)]
        refine lub_least (sup_least fun i => ?_) (sup_least fun q => ?_)
        · calc x i ⨳ (y ♯ z) ♯ (y ♯ z) ≤ (x i ⨳ y ♯ x i ⨳ z) ♯ (y ♯ z) :=
                nadd_le_nadd (ihx (x i) (index_lt x i) y z) (le_refl _)
            _ ≤ (x i ⨳ y ♯ y) ♯ (x i ⨳ z ♯ z) := by
                refine le_trans (nadd_assoc2 _ _ _) (le_trans (nadd_le_nadd (le_refl _)
                  (le_trans (nadd_assoc1 _ _ _) (le_trans (nadd_le_nadd (nadd_comm_le _ _) (le_refl _))
                    (nadd_assoc2 _ _ _)))) (nadd_assoc1 _ _ _))
            _ ≤ x ⨳ y ♯ x ⨳ z := nadd_le_nadd (nmul_stepl x y i) (nmul_stepl x z i)
        · match nadd_lt_cases (index_lt (y ♯ z) q) with
          | .inl ⟨b, hb⟩ =>
            calc x ⨳ (y ♯ z) q ♯ x ≤ (x ⨳ y b ♯ x ⨳ z) ♯ x :=
                  nadd_le_nadd (le_trans (nmul_le_nmul (le_refl x) hb) (ihy (y b) (index_lt y b) z))
                    (le_refl x)
              _ ≤ (x ⨳ y b ♯ x) ♯ x ⨳ z := (nadd_right_comm _ _ _).le
              _ ≤ x ⨳ y ♯ x ⨳ z := nadd_le_nadd (nmul_stepr x y b) (le_refl _)
          | .inr ⟨c, hc⟩ =>
            calc x ⨳ (y ♯ z) q ♯ x ≤ (x ⨳ y ♯ x ⨳ z c) ♯ x :=
                  nadd_le_nadd (le_trans (nmul_le_nmul (le_refl x) hc) (ihz (z c) (index_lt z c)))
                    (le_refl x)
              _ ≤ x ⨳ y ♯ (x ⨳ z c ♯ x) := nadd_assoc2 _ _ _
              _ ≤ x ⨳ y ♯ x ⨳ z := nadd_le_nadd (le_refl _) (nmul_stepr x z c)

/-- The witness for non-distributivity: the closure of `1` under `ω ⨳ ·`.
Rocq: `NaturalArith.Q`. -/
def Q : Ordinal.{u} := sup fun n : (ω : Ordinal.{u}).Carrier => iterF (nmul ω) 1 n.down

/-- Rocq: `NaturalArith.nmul_distrib_counterexample`. -/
theorem nmul_distrib_counterexample : (ω : Ordinal.{u}) ⨳ (Q ♯ Q) < ω ⨳ Q ♯ ω ⨳ Q := by
  have hQ₀ : (0 : Ordinal.{u}) < Q :=
    lt_of_lt_of_le (succ_lt 0) (sup_le (fun n : (ω : Ordinal.{u}).Carrier => iterF (nmul ω) 1 n.down) ⟨0⟩)
  have hiter : ∀ n : Nat, iterF (nmul ω) (1 : Ordinal.{u}) n ≤ Q := fun n =>
    sup_le (fun n : (ω : Ordinal.{u}).Carrier => iterF (nmul ω) 1 n.down) ⟨n⟩
  -- The terms of `Q` are absorbed by `ω ⨳ ·`.
  have hsmall : ∀ b : (Q : Ordinal.{u}).Carrier, ω ⨳ Q b ♯ ω ≤ Q := fun b => by
    obtain ⟨⟨n⟩, hn⟩ := sup_lt (index_lt Q b)
    obtain ⟨q', hq'⟩ := lt_elim hn
    exact le_trans (nadd_le_nadd (nmul_le_nmul (le_refl ω) hq') (le_refl ω))
      (le_trans (nmul_stepr ω _ q') (hiter (n + 1)))
  have hfin : ∀ n : Nat, ofNat n ⨳ (Q ♯ Q) ≤ ofNat (2 * n) ⨳ (Q : Ordinal.{u}) := by
    intro n
    induction n with
    | zero => exact le_trans (nmul_comm _ _).le (le_trans (nmul_zero _).le (zero_least _))
    | succ n ih =>
      calc ofNat (n + 1) ⨳ (Q ♯ Q) ≤ ofNat n ⨳ (Q ♯ Q) ♯ (Q ♯ Q) := (nmul_succ _ _).le
        _ ≤ ofNat (2 * n) ⨳ Q ♯ (Q ♯ Q) := nadd_le_nadd ih (le_refl _)
        _ ≤ (ofNat (2 * n) ⨳ Q ♯ Q) ♯ Q := nadd_assoc1 _ _ _
        _ ≤ ofNat (2 * n + 1) ⨳ Q ♯ Q := nadd_le_nadd (nmul_succ _ _).ge (le_refl _)
        _ ≤ ofNat (2 * n + 2) ⨳ (Q : Ordinal.{u}) := (nmul_succ _ _).ge
  have hstep : ω ⨳ (Q ♯ Q) ≤ Q ♯ (ω : Ordinal.{u}) ⨳ Q := by
    rw [nmul_unfold ω (Q ♯ Q)]
    refine lub_least (sup_least fun ⟨n⟩ => ?_) (sup_least fun q => ?_)
    · show ofNat n ⨳ (Q ♯ Q) ♯ (Q ♯ Q) ≤ Q ♯ ω ⨳ Q
      calc ofNat n ⨳ (Q ♯ Q) ♯ (Q ♯ Q) ≤ ofNat (2 * n) ⨳ Q ♯ (Q ♯ Q) := nadd_le_nadd (hfin n) (le_refl _)
        _ ≤ Q ♯ (ofNat (2 * n) ⨳ Q ♯ Q) := (nadd_left_comm _ _ _).le
        _ ≤ Q ♯ ω ⨳ Q := nadd_le_nadd (le_refl _) (nmul_stepl ω Q ⟨2 * n⟩)
    · match nadd_lt_cases (index_lt (Q ♯ Q) q) with
      | .inl ⟨b, hb⟩ =>
        calc ω ⨳ (Q ♯ Q) q ♯ ω ≤ (ω ⨳ Q b ♯ ω ⨳ Q) ♯ ω :=
              nadd_le_nadd (le_trans (nmul_le_nmul (le_refl ω) hb) (nmulDistrib1 _ _ _)) (le_refl ω)
          _ ≤ (ω ⨳ Q b ♯ ω) ♯ ω ⨳ Q := (nadd_right_comm _ _ _).le
          _ ≤ Q ♯ ω ⨳ Q := nadd_le_nadd (hsmall b) (le_refl _)
      | .inr ⟨c, hc⟩ =>
        calc ω ⨳ (Q ♯ Q) q ♯ ω ≤ (ω ⨳ Q ♯ ω ⨳ Q c) ♯ ω :=
              nadd_le_nadd (le_trans (nmul_le_nmul (le_refl ω) hc) (nmulDistrib1 _ _ _)) (le_refl ω)
          _ ≤ ω ⨳ Q ♯ (ω ⨳ Q c ♯ ω) := nadd_assoc2 _ _ _
          _ ≤ (ω ⨳ Q c ♯ ω) ♯ ω ⨳ Q := nadd_comm_le _ _
          _ ≤ Q ♯ ω ⨳ Q := nadd_le_nadd (hsmall c) (le_refl _)
  refine lt_of_le_of_lt hstep (nadd_increasing1 _ ?_)
  calc (Q : Ordinal.{u}) ≤ Q ♯ 0 := (nadd_zero_r Q).ge
    _ < Q ♯ Q := nadd_increasing2 _ hQ₀
    _ ≤ 1 ⨳ Q ♯ Q := nadd_le_nadd (le_trans (nmul_one Q).ge (nmul_comm Q 1).le) (le_refl Q)
    _ ≤ (ω : Ordinal.{u}) ⨳ Q := nmul_stepl ω Q ⟨1⟩

/-- This natural multiplication is not distributive.
Rocq: `NaturalArith.nmul_not_distributive`. -/
theorem nmul_not_distributive : ¬ ∀ x y z : Ordinal.{u}, x ⨳ (y ♯ z) ≈ x ⨳ y ♯ x ⨳ z := fun H =>
  lt_irrefl _ (lt_of_lt_of_le nmul_distrib_counterexample (H ω Q Q).ge)

end IncorrectNmul

/-! ## Jacobsthal multiplication

The transfinite iteration of natural addition.
-/

/-- Rocq: `NaturalArith.jmulOrd` (notation `a × b`). -/
def jmul (a : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk _ g => sup fun i => jmul a (g i) ♯ a

/-- Rocq: `NaturalArith.jmulOrd_unfold`. -/
theorem jmul_unfold (a b : Ordinal.{u}) : jmul a b = sup fun i : b => jmul a (b i) ♯ a := by
  cases b; rfl

/-- Rocq: `NaturalArith.jmulOrd_monotone1`. -/
theorem jmul_monotone1 : ∀ (z : Ordinal.{u}) {a b : Ordinal.{u}}, a ≤ b → jmul a z ≤ jmul b z
  | mk C h, a, b, hab => by
    rw [jmul_unfold a, jmul_unfold b]
    exact sup_monotone fun c => nadd_le_nadd (jmul_monotone1 (h c) hab) hab

/-- Rocq: `NaturalArith.jmulOrd_monotone2`. -/
theorem jmul_monotone2 (a : Ordinal.{u}) : ∀ {b z : Ordinal.{u}}, b ≤ z → jmul a b ≤ jmul a z
  | mk B g, z, h => by
    rw [jmul_unfold a (mk B g)]
    refine sup_least fun i => ?_
    obtain ⟨q, hq⟩ := lt_elim (le_elim h i)
    rw [jmul_unfold a z]
    exact le_trans (nadd_le_nadd (jmul_monotone2 a hq) (le_refl a))
      (sup_le (fun i : z => jmul a (z i) ♯ a) q)

/-- Rocq: `NaturalArith.jmulOrd_increasing2`. -/
theorem jmul_increasing2 {a b c : Ordinal.{u}} (ha : 0 < a) (h : b < c) : jmul a b < jmul a c := by
  obtain ⟨i, hi⟩ := lt_elim h
  rw [jmul_unfold a c]
  exact lt_of_le_of_lt (jmul_monotone2 a hi) (lt_of_le_of_lt (nadd_zero_r _).ge
    (lt_of_lt_of_le (nadd_increasing2 _ ha) (sup_le (fun i : c => jmul a (c i) ♯ a) i)))

/-- Rocq: `NaturalArith.jmulOrd_le_mor`. -/
@[ord_mono]
theorem jmul_le_jmul {x y x₀ y₀ : Ordinal.{u}} (h : x ≤ y) (h₀ : x₀ ≤ y₀) : jmul x x₀ ≤ jmul y y₀ :=
  le_trans (jmul_monotone2 x h₀) (jmul_monotone1 y₀ h)

/-- Rocq: `NaturalArith.jmulOrd_eq_mor`. -/
theorem jmul_congr {x y x₀ y₀ : Ordinal.{u}} (h : x ≈ y) (h₀ : x₀ ≈ y₀) : jmul x x₀ ≈ jmul y y₀ :=
  equiv_intro (jmul_le_jmul h.le h₀.le) (jmul_le_jmul h.ge h₀.ge)

/-- Rocq: `NaturalArith.jmulOrd_zero_r`. -/
theorem jmul_zero_r (a : Ordinal.{u}) : jmul a 0 ≈ 0 := by
  refine equiv_intro ?_ (zero_least _)
  rw [jmul_unfold]
  exact sup_least fun i => PEmpty.elim i

/-- Rocq: `NaturalArith.jmulOrd_zero_l`. -/
theorem jmul_zero_l : ∀ a : Ordinal.{u}, jmul 0 a ≈ 0
  | mk A f => by
    refine equiv_intro ?_ (zero_least _)
    rw [jmul_unfold]
    exact sup_least fun x => le_trans (nadd_zero_r _).le (jmul_zero_l (f x)).le

/-- Rocq: `NaturalArith.jmulOrd_succ`. -/
theorem jmul_succ (a b : Ordinal.{u}) : jmul a (succ b) ≈ jmul a b ♯ a := by
  rw [jmul_unfold]
  exact equiv_intro (sup_least fun _ => le_refl _)
    (sup_le (fun i : (succ b).Carrier => jmul a (succ b i) ♯ a) PUnit.unit)

/-- Rocq: `NaturalArith.jmulOrd_one`. -/
theorem jmul_one (a : Ordinal.{u}) : jmul a 1 ≈ a :=
  equiv_trans (jmul_succ a 0) (equiv_trans (nadd_congr (jmul_zero_r a) (equiv_refl a)) (nadd_zero_l a))

/-- Rocq: `NaturalArith.jmulOrd_positive`. -/
theorem jmul_positive {a b : Ordinal.{u}} (ha : 0 < a) (hb : 0 < b) : 0 < jmul a b := by
  obtain ⟨j, _⟩ := lt_elim hb
  rw [jmul_unfold]
  exact lt_of_lt_of_le (lt_of_lt_of_le ha (nadd_le2 _ a)) (sup_le (fun i : b => jmul a (b i) ♯ a) j)

/-- Rocq: `NaturalArith.jmulOrd_limit`. -/
theorem jmul_limit (a : Ordinal.{u}) {b : Ordinal.{u}} (hb : IsLimit b) :
    jmul a b ≈ sup fun i : b => jmul a (b i) := by
  rw [jmul_unfold]
  refine equiv_intro (sup_least fun i => ?_) (sup_least fun i => ?_)
  · obtain ⟨i', hi'⟩ := hb.2 i
    exact le_trans (jmul_succ a (b i)).ge
      (le_trans (jmul_monotone2 a (succ_least hi')) (sup_le (fun i : b => jmul a (b i)) i'))
  · exact le_trans (nadd_le1 _ a) (sup_le (fun i : b => jmul a (b i) ♯ a) i)

/-- Rocq: `NaturalArith.jmulOrd_continuous`. -/
theorem jmul_continuous (a : Ordinal.{u}) : StronglyContinuous (jmul a) := fun A f _ => by
  rw [jmul_unfold a (sup f)]
  refine sup_least fun p => le_trans ?_ (sup_le (fun i => jmul a (f i)) p.1)
  rw [jmul_unfold a (f p.1)]
  exact sup_le (fun i : f p.1 => jmul a (f p.1 i) ♯ a) p.2

/-! ## Smash sums -/

/-- Rocq: `NaturalArith.smash_sum`. -/
def smashSum (x y : Ordinal.{u}) : Ordinal.{u} := lim fun i : x.Carrier × y.Carrier => x i.1 ♯ y i.2

/-- Rocq: `NaturalArith.smash_sum_zero_l`. -/
theorem smashSum_zero_l (x : Ordinal.{u}) : smashSum 0 x ≈ 0 :=
  equiv_intro (le_intro fun i => PEmpty.elim i.1) (zero_least _)

/-- Rocq: `NaturalArith.smash_sum_zero_r`. -/
theorem smashSum_zero_r (x : Ordinal.{u}) : smashSum x 0 ≈ 0 :=
  equiv_intro (le_intro fun i => PEmpty.elim i.2) (zero_least _)

/-- Rocq: `NaturalArith.smash_sum_one_l`. -/
theorem smashSum_one_l (x : Ordinal.{u}) : smashSum 1 x ≈ x :=
  equiv_intro (limit_least fun i => lt_of_le_of_lt (nadd_zero_l _).le (index_lt x i.2))
    (le_intro fun i => lt_intro (show (smashSum 1 x).Carrier from (PUnit.unit, i)) (nadd_zero_l _).ge)

/-- Rocq: `NaturalArith.smash_sum_one_r`. -/
theorem smashSum_one_r (x : Ordinal.{u}) : smashSum x 1 ≈ x :=
  equiv_intro (limit_least fun i => lt_of_le_of_lt (nadd_zero_r _).le (index_lt x i.1))
    (le_intro fun i => lt_intro (show (smashSum x 1).Carrier from (i, PUnit.unit)) (nadd_zero_r _).ge)

/-- Rocq: `NaturalArith.smash_sum_sym_le`. -/
theorem smashSum_sym_le (x y : Ordinal.{u}) : smashSum x y ≤ smashSum y x :=
  le_intro fun i => lt_intro (show (smashSum y x).Carrier from (i.2, i.1)) (nadd_comm _ _).le

/-- Rocq: `NaturalArith.smash_sum_sym`. -/
theorem smashSum_sym (x y : Ordinal.{u}) : smashSum x y ≈ smashSum y x :=
  equiv_intro (smashSum_sym_le x y) (smashSum_sym_le y x)

/-- Rocq: `NaturalArith.smash_sum_assoc1`. -/
theorem smashSum_assoc1 (x y z : Ordinal.{u}) :
    smashSum x (smashSum y z) ≤ smashSum (smashSum x y) z :=
  limit_least fun ⟨a, b, c⟩ =>
    lt_intro (show (smashSum (smashSum x y) z).Carrier from ((a, b), c)) (nadd_assoc _ _ _).le

/-- Rocq: `NaturalArith.smash_sum_assoc2`. -/
theorem smashSum_assoc2 (x y z : Ordinal.{u}) :
    smashSum (smashSum x y) z ≤ smashSum x (smashSum y z) :=
  limit_least fun ⟨⟨a, b⟩, c⟩ =>
    lt_intro (show (smashSum x (smashSum y z)).Carrier from (a, (b, c))) (nadd_assoc _ _ _).ge

/-- Rocq: `NaturalArith.smash_sum_assoc`. -/
theorem smashSum_assoc (x y z : Ordinal.{u}) :
    smashSum (smashSum x y) z ≈ smashSum x (smashSum y z) :=
  equiv_intro (smashSum_assoc2 x y z) (smashSum_assoc1 x y z)

/-- The natural sum of a list of elements of `x`. -/
def smashList (x : Ordinal.{u}) (xs : List x.Carrier) : Ordinal.{u} :=
  xs.foldr (fun i acc => x i ♯ acc) 0

/-- Rocq: `NaturalArith.iterated_smash_sum`. -/
def iteratedSmashSum (x : Ordinal.{u}) : Ordinal.{u} := lim fun xs : List x.Carrier => smashList x xs

/-- Rocq: `NaturalArith.iterated_smash_sum_nonzero`. -/
theorem iteratedSmashSum_nonzero (x : Ordinal.{u}) : 0 < iteratedSmashSum x :=
  lt_intro (show (iteratedSmashSum x).Carrier from []) (zero_least _)

/-- Rocq: `NaturalArith.iterated_smash_sum_monotone`. -/
theorem iteratedSmashSum_monotone {x y : Ordinal.{u}} (h : x ≤ y) :
    iteratedSmashSum x ≤ iteratedSmashSum y :=
  limit_least fun xs => by
    have hys : ∃ ys : List y.Carrier, Forall₂ (fun a b => x a ≤ y b) xs ys := by
      induction xs with
      | nil => exact ⟨[], .nil⟩
      | cons a xs ih =>
        obtain ⟨b, hb⟩ := le_subord h a
        obtain ⟨ys, hys⟩ := ih
        exact ⟨b :: ys, .cons hb hys⟩
    obtain ⟨ys, hys⟩ := hys
    refine lt_intro (show (iteratedSmashSum y).Carrier from ys) ?_
    show smashList x xs ≤ smashList y ys
    induction hys with
    | nil => exact le_refl _
    | cons hab _ ih => exact nadd_le_nadd hab ih

/-- Rocq: `NaturalArith.iterated_smash_sum_eq`. -/
theorem iteratedSmashSum_eq (x : Ordinal.{u}) :
    iteratedSmashSum x ≈ sup fun i : ULift.{u} Nat => Nat.repeat (smashSum x) i.down 1 := by
  refine equiv_intro (limit_least fun xs => ?_) (sup_least fun ⟨i⟩ => ?_)
  · refine lt_of_lt_of_le ?_ (sup_le (fun i : ULift.{u} Nat => Nat.repeat (smashSum x) i.down 1) ⟨xs.length⟩)
    show smashList x xs < Nat.repeat (smashSum x) xs.length 1
    induction xs with
    | nil => exact succ_lt 0
    | cons a xs ih =>
      obtain ⟨b, hb⟩ := lt_elim ih
      exact lt_intro (show (smashSum x (Nat.repeat (smashSum x) xs.length 1)).Carrier from (a, b))
        (nadd_le_nadd (le_refl _) hb)
  · show Nat.repeat (smashSum x) i 1 ≤ iteratedSmashSum x
    induction i with
    | zero => exact succ_least (iteratedSmashSum_nonzero x)
    | succ i ih =>
      refine limit_least fun ⟨a, q⟩ => ?_
      obtain ⟨xs, hxs⟩ := lt_elim (lt_of_lt_of_le (index_lt _ q) ih)
      exact lt_intro (show (iteratedSmashSum x).Carrier from a :: xs) (nadd_le_nadd (le_refl _) hxs)

end Ordinal

end ConstructiveOrdinals
