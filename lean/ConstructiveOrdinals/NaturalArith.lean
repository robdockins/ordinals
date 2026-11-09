import ConstructiveOrdinals.Cantor
import ConstructiveOrdinals.Veblen.Constructive
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

/-! ## Constructive closure of ω-powers under natural sum

`nadd_closed` and `nadd_add_same_powers` above assume the excluded middle,
which enters only through `nadd_closed_technical1`: it compares `ω ^ a` with
an arbitrary `q` and splits off a leading Cantor term. Keeping every quantity
in the explicit form `ω ^ c * m + u` with `u < ω ^ c` avoids the comparison:
a child of `ω ^ c * m + u` is either `ω ^ c * m + u'` for a child `u'` of `u`,
or lies below `ω ^ c * (m - 1) + w` for some `w < ω ^ c`. The completeness
hypothesis on the exponent is still needed (it is what makes the children of
`ω ^ a` directed); without it, closure fails constructively.

In Rocq these results live in a section with `Let E := expOrd ω c`; here
`E` is written out as `ω ^ c`.
-/

section same_powers

variable (c : Ordinal.{u}) (hc : ∀ x y, x < ω ^ c → y < ω ^ c → x ♯ y < ω ^ c)

/-- `ω ^ c * (k + 1)` as `ω ^ c * k + ω ^ c`, with the successor on the right.
Rocq: `NaturalArith.mul_succ_strict`; Rocq's `NaturalArith.E` is `ω ^ c`. -/
theorem mul_succ_strict (k : Nat) {w : Ordinal.{u}} (hw : w < ω ^ c) :
    ω ^ c * ofNat k + w < ω ^ c * ofNat (k + 1) :=
  lt_of_lt_of_le (add_lt_add_left _ hw) (mul_succ _ _).ge

/-- A child of `ω ^ c * (m + 1)` lies below `ω ^ c * m + w` for some `w < ω ^ c`. -/
private theorem below_mul_succ {i : Ordinal.{u}} (m : Nat) (h : i < ω ^ c * ofNat (m + 1)) :
    ∃ w, w < ω ^ c ∧ i ≤ ω ^ c * ofNat m + w :=
  match add_lt (lt_of_lt_of_le h (mul_succ _ _).le) with
  | .inl h₁ => ⟨0, pow_pos ω c, le_trans (le_of_lt h₁) (add_zero _).ge⟩
  | .inr ⟨w, hw⟩ => ⟨(ω ^ c) w, index_lt _ w, hw⟩

include hc in
/-- Rocq: `NaturalArith.same_powers_le`. -/
theorem same_powers_le (o : Ordinal.{u}) : ∀ (m : Nat) (u : Ordinal.{u}) (n : Nat) (v : Ordinal.{u}),
    (ω ^ c * ofNat m + u) ♯ (ω ^ c * ofNat n + v) ≤ o → u < ω ^ c → v < ω ^ c →
    (ω ^ c * ofNat m + u) ♯ (ω ^ c * ofNat n + v) ≤ ω ^ c * ofNat (m + n) + (u ♯ v) := by
  induction o using ltRec with
  | ind o ih =>
    intro m u n v ho hu hv
    refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
    · match add_lt hi with
      | .inl hi' =>
        match m, hi', hu, ho with
        | 0, hi', _, _ => exact (zero_lt i (lt_of_lt_of_le hi' (mul_zero _).le)).elim
        | m' + 1, hi', hu, ho =>
          obtain ⟨w, hw, hiw⟩ := below_mul_succ c m' hi'
          have hlt : (ω ^ c * ofNat m' + w) ♯ (ω ^ c * ofNat n + v) <
              (ω ^ c * ofNat (m' + 1) + u) ♯ (ω ^ c * ofNat n + v) :=
            nadd_increasing1 _ (lt_of_lt_of_le (mul_succ_strict c m' hw) (le_add_right _ _))
          refine lt_of_le_of_lt (nadd_le_nadd hiw (le_refl _))
            (lt_of_le_of_lt (ih _ (lt_of_lt_of_le hlt ho) m' w n v (le_refl _) hw hv) ?_)
          rw [Nat.add_right_comm m' 1 n]
          exact lt_of_lt_of_le (mul_succ_strict c (m' + n) (hc w v hw hv)) (le_add_right _ _)
      | .inr ⟨k, hk⟩ =>
        have hlt : (ω ^ c * ofNat m + u k) ♯ (ω ^ c * ofNat n + v) <
            (ω ^ c * ofNat m + u) ♯ (ω ^ c * ofNat n + v) :=
          nadd_increasing1 _ (add_lt_add_left _ (index_lt u k))
        exact lt_of_le_of_lt (nadd_le_nadd hk (le_refl _))
          (lt_of_le_of_lt (ih _ (lt_of_lt_of_le hlt ho) m (u k) n v (le_refl _)
            (lt_trans (index_lt u k) hu) hv)
            (add_lt_add_left _ (nadd_increasing1 v (index_lt u k))))
    · match add_lt hj with
      | .inl hj' =>
        match n, hj', hv, ho with
        | 0, hj', _, _ => exact (zero_lt j (lt_of_lt_of_le hj' (mul_zero _).le)).elim
        | n' + 1, hj', hv, ho =>
          obtain ⟨w, hw, hjw⟩ := below_mul_succ c n' hj'
          have hlt : (ω ^ c * ofNat m + u) ♯ (ω ^ c * ofNat n' + w) <
              (ω ^ c * ofNat m + u) ♯ (ω ^ c * ofNat (n' + 1) + v) :=
            nadd_increasing2 _ (lt_of_lt_of_le (mul_succ_strict c n' hw) (le_add_right _ _))
          exact lt_of_le_of_lt (nadd_le_nadd (le_refl _) hjw)
            (lt_of_le_of_lt (ih _ (lt_of_lt_of_le hlt ho) m u n' w (le_refl _) hu hw)
              (lt_of_lt_of_le (mul_succ_strict c (m + n') (hc u w hu hw)) (le_add_right _ _)))
      | .inr ⟨k, hk⟩ =>
        have hlt : (ω ^ c * ofNat m + u) ♯ (ω ^ c * ofNat n + v k) <
            (ω ^ c * ofNat m + u) ♯ (ω ^ c * ofNat n + v) :=
          nadd_increasing2 _ (add_lt_add_left _ (index_lt v k))
        exact lt_of_le_of_lt (nadd_le_nadd (le_refl _) hk)
          (lt_of_le_of_lt (ih _ (lt_of_lt_of_le hlt ho) m u n (v k) (le_refl _) hu
            (lt_trans (index_lt v k) hv))
            (add_lt_add_left _ (nadd_increasing2 u (index_lt v k))))

include hc in
/-- Rocq: `NaturalArith.same_powers_lt`. -/
theorem same_powers_lt (m n : Nat) :
    ω ^ c * ofNat m ♯ ω ^ c * ofNat n < ω ^ c * ofNat (m + n + 1) :=
  lt_of_le_of_lt (nadd_le_nadd (add_zero _).ge (add_zero _).ge)
    (lt_of_le_of_lt (same_powers_le c hc _ m 0 n 0 (le_refl _) (pow_pos ω c) (pow_pos ω c))
      (mul_succ_strict c (m + n) (hc 0 0 (pow_pos ω c) (pow_pos ω c))))

end same_powers

/-- Powers of ω with complete exponents are closed under natural sums,
constructively. Rocq: `NaturalArith.nadd_closed_con`. -/
theorem nadd_closed_con (a : Ordinal.{u}) :
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
          _ < ω ^ a k * ofNat (m + 1 + (n + 1) + 1) :=
              same_powers_lt (a k) (fun x y => ih (a k) (index_lt a k) x y (complete_subord ha k))
                (m + 1) (n + 1)
          _ < ω ^ a k * ω := mul_lt_mul_left (pow_pos ω _) (index_lt ω ⟨m + 1 + (n + 1) + 1⟩)
          _ ≤ ω ^ a := pow_index_mul_omega_le a k

/-- Rocq: `NaturalArith.nadd_add_same_powers_con`. -/
theorem nadd_add_same_powers_con (a : Ordinal.{u}) (m n : Nat) (ha : Complete a) :
    ω ^ a * ofNat m ♯ ω ^ a * ofNat n ≤ ω ^ a * ofNat (m + n) :=
  le_trans (nadd_le_nadd (add_zero _).ge (add_zero _).ge)
    (le_trans (same_powers_le a (fun x y => nadd_closed_con a x y ha) _ m 0 n 0 (le_refl _)
      (pow_pos ω a) (pow_pos ω a))
      (le_trans (add_le_add (le_refl _) (nadd_zero_r 0).le) (add_zero _).le))

/-- The completeness hypothesis cannot be dropped: closure of every `ω ^ a`
under natural sum implies the weak excluded middle. Take `a` with exactly two
children `c₁` (`0`, or `ω + 1` if `P`) and `c₂ = succ e` (`1`, or `2` if `P`).
Then `ω ^ c₁ ♯ ω ^ c₂ < ω ^ a` must name a child of `ω ^ a`: below
`ω ^ c₁ * (n + 1)`, refuted by `¬P` (it is then finite, while `ω ^ c₂ ≥ ω`), or
below `ω ^ c₂ * (n + 1)`, refuted by `P` (it is then below `ω ^ 3 ≤ ω ^ c₁`).
Rocq: `NaturalArith.nadd_closed_needs_complete`. -/
theorem nadd_closed_needs_complete
    (h : ∀ a x y : Ordinal.{u}, x < ω ^ a → y < ω ^ a → x ♯ y < ω ^ a) :
    WeakExcludedMiddle := fun P => by
  let c₁ : Ordinal.{u} := mk (ULift (PLift P)) fun _ => ω
  let e : Ordinal.{u} := mk (ULift (PLift P)) fun _ => 0
  let c₂ : Ordinal.{u} := succ e
  let a : Ordinal.{u} := mk (ULift Bool) fun b => cond b.down c₁ c₂
  have hx : ω ^ c₁ < ω ^ a := pow_lt_pow_right omega_gt1 (index_lt a ⟨true⟩)
  have hy : ω ^ c₂ < ω ^ a := pow_lt_pow_right omega_gt1 (index_lt a ⟨false⟩)
  have he1 : e ≤ 1 := le_intro fun _ => succ_lt 0
  have hyω : ω ≤ ω ^ c₂ :=
    le_trans (pow_one' omega_gt0).ge (pow_le_pow_right ω (succ_monotone (zero_least e)))
  have hxy := h a _ _ hx hy
  rw [pow_unfold ω a] at hxy
  match lub_lt hxy with
  | .inl h₁ =>
    obtain ⟨_, h₁⟩ := lt_elim h₁
    exact (lt_irrefl 0 (lt_of_lt_of_le (pow_pos ω c₂) (le_trans (nadd_le2 _ _) h₁))).elim
  | .inr h₁ =>
    obtain ⟨⟨i⟩, h₁⟩ := sup_lt h₁
    rw [mul_unfold] at h₁
    obtain ⟨⟨n⟩, h₁⟩ := sup_lt h₁
    cases i
    · -- the child `c₂`: refuted by `P`
      refine .inr fun p => ?_
      have hc₁ω : ω ≤ c₁ := le_of_lt (lt_intro (show c₁.Carrier from ⟨⟨p⟩⟩) (le_refl _))
      have he : ω ^ c₂ ≤ ω ^ (2 : Ordinal.{u}) := pow_le_pow_right ω (succ_monotone he1)
      refine lt_irrefl (ω ^ c₁) (lt_of_le_of_lt (nadd_le1 _ _) (lt_of_lt_of_le h₁ ?_))
      calc ω ^ c₂ * ofNat n + ω ^ c₂ ≤ ω ^ (2 : Ordinal.{u}) * ofNat n + ω ^ (2 : Ordinal.{u}) :=
            add_le_add (mul_le_mul_right _ he) he
        _ ≤ ω ^ (2 : Ordinal.{u}) * ofNat (n + 1) := (mul_succ _ _).ge
        _ ≤ ω ^ (2 : Ordinal.{u}) * ω :=
            le_of_lt (mul_lt_mul_left (pow_pos ω _) (index_lt ω ⟨n + 1⟩))
        _ ≤ ω ^ succ (2 : Ordinal.{u}) := (pow_succ 2 omega_gt0).ge
        _ ≤ ω ^ c₁ := pow_le_pow_right ω (le_trans (le_of_lt (index_lt ω ⟨3⟩)) hc₁ω)
    · -- the child `c₁`: refuted by `¬P`
      refine .inl fun np => ?_
      have hc₁z : c₁ ≤ 0 := le_intro fun ⟨⟨p⟩⟩ => (np p).elim
      have he : ω ^ c₁ ≤ 1 := le_trans (pow_le_pow_right ω hc₁z) (pow_zero ω).le
      have hfin : ω ^ c₁ * ofNat n + ω ^ c₁ < ω :=
        lt_of_le_of_lt (le_trans (add_le_add (mul_le_mul_right _ he) he)
          (le_trans (add_le_add (one_mul _).le (le_refl 1))
            (le_trans (add_succ _ 0).le (succ_monotone (add_zero _).le))))
          (index_lt ω ⟨n + 1⟩)
      exact lt_irrefl ω (lt_of_le_of_lt (le_trans hyω (nadd_le2 _ _)) (lt_trans h₁ hfin))

/-! ## Natural sums and Cantor normal forms -/

/-- Rocq: `NaturalArith.cantor_denote_app`. -/
theorem cantor_denote_app : ∀ xs ys : List Ordinal.{u},
    cantorDenote (xs ++ ys) ≈ cantorDenote xs + cantorDenote ys
  | [], _ => equiv_symm (zero_add _)
  | _ :: xs, ys => equiv_trans (add_congr (equiv_refl _) (cantor_denote_app xs ys)) (add_assoc _ _ _)

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
  | _ :: xs, _, _, ⟨_, hseq⟩, _, y, .head _, hy =>
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
  | [], _ => equiv_symm (nadd_zero_l _)
  | _ :: xs, ys =>
    equiv_trans (nadd_congr (equiv_refl _) (cantor_denote_nadd_app xs ys)) (nadd_assoc _ _ _)

/-- Rocq: `NaturalArith.cantor_sequence_app1`. -/
theorem cantor_sequence_app1 : ∀ (xs : List Ordinal.{u}) (x : Ordinal.{u}) (ys : List Ordinal.{u}),
    CantorSequence x (xs ++ ys) → CantorSequence x xs
  | [], _, _, _ => trivial
  | _ :: xs, _, ys, ⟨hy, h⟩ => ⟨hy, cantor_sequence_app1 xs _ ys h⟩

/-! ### Natural sums of Cantor sequences, constructively

`cantor_denote_nadd_eq` below needs the excluded middle only to compare
adjacent exponents. When each exponent is known to be either below or equal to
its predecessor, closure under natural sum (`nadd_closed_con`) suffices: group
the leading run of equal exponents as `ω ^ y * k`, bound the rest below `ω ^ y`,
and apply `same_powers_le`. Without such decisions the identity is not
constructive, even for complete exponents (`cantor_denote_nadd_eq_WEM`). -/

/-- A Cantor sequence whose exponents are each known to be below or equal to
their predecessor. Rocq: `NaturalArith.cantor_sequence_dec`. -/
def CantorSequenceDec (x : Ordinal.{u}) : List Ordinal.{u} → Prop
  | [] => True
  | y :: ys => (y < x ∨ y ≈ x) ∧ CantorSequenceDec y ys

/-- Rocq: `NaturalArith.cantor_sequence_dec_weaken`. -/
theorem cantor_sequence_dec_weaken : ∀ (ls : List Ordinal.{u}) (x : Ordinal.{u}),
    CantorSequenceDec x ls → CantorSequence x ls
  | [], _, _ => trivial
  | _ :: ys, _, ⟨h, hd⟩ => ⟨h.elim le_of_lt Equiv.le, cantor_sequence_dec_weaken ys _ hd⟩

/-- Rocq: `NaturalArith.cantor_sequence_dec_EM`. -/
theorem cantor_sequence_dec_EM (em : ExcludedMiddle) : ∀ (ls : List Ordinal.{u}) (x : Ordinal.{u}),
    CantorSequence x ls → CantorSequenceDec x ls
  | [], _, _ => trivial
  | y :: ys, x, ⟨h, hs⟩ =>
    ⟨match order_trichotomy em y x with
      | .inl hlt => .inl hlt
      | .inr (.inl heq) => .inr heq
      | .inr (.inr hgt) => (lt_irrefl x (lt_of_lt_of_le hgt h)).elim,
     cantor_sequence_dec_EM em ys y hs⟩

/-- Rocq: `NaturalArith.mul_nat_below_power`. -/
theorem mul_nat_below_power {c z : Ordinal.{u}} (hc : Complete c) (hz : z < c) :
    ∀ k : Nat, ω ^ z * ofNat k < ω ^ c
  | 0 => lt_of_le_of_lt (mul_zero _).le (pow_pos ω c)
  | k + 1 => lt_of_le_of_lt (mul_succ _ _).le (lt_of_le_of_lt (add_nadd_le _ _)
      (nadd_closed_con c _ _ hc (mul_nat_below_power hc hz k) (pow_lt_pow_right omega_gt1 hz)))

/-- A Cantor sequence below `y` splits as `ω ^ y * k + r` with `r < ω ^ y`.
Rocq: `NaturalArith.cantor_dec_split`. -/
theorem cantor_dec_split : ∀ (xs : List Ordinal.{u}) (y : Ordinal.{u}),
    Complete y → Each Complete xs → CantorSequenceDec y xs →
    ∃ (k : Nat) (r : Ordinal.{u}), r < ω ^ y ∧ cantorDenote xs ≈ ω ^ y * ofNat k + r
  | [], y, _, _, _ =>
    ⟨0, 0, pow_pos ω y, equiv_symm (equiv_trans (add_zero _) (mul_zero _))⟩
  | z :: zs, y, hy, ⟨hz, hzs⟩, ⟨hzy, hd⟩ => by
    obtain ⟨k, r, hr, heq⟩ := cantor_dec_split zs z hz hzs hd
    match hzy with
    | .inl hlt =>
      have hzy' : ω ^ z < ω ^ y := pow_lt_pow_right omega_gt1 hlt
      refine ⟨0, cantorDenote (z :: zs), ?_,
        equiv_symm (equiv_trans (add_congr (mul_zero _) (equiv_refl _)) (zero_add _))⟩
      calc ω ^ z + cantorDenote zs ≤ ω ^ z ♯ cantorDenote zs := add_nadd_le _ _
        _ ≤ ω ^ z ♯ (ω ^ z * ofNat k ♯ r) :=
            nadd_le_nadd (le_refl _) (le_trans heq.le (add_nadd_le _ _))
        _ < ω ^ y := nadd_closed_con y _ _ hy hzy' (nadd_closed_con y _ _ hy
            (mul_nat_below_power hy hlt k) (lt_trans hr hzy'))
    | .inr heqz =>
      refine ⟨k + 1, r, lt_of_lt_of_le hr (pow_le_pow_right ω heqz.le), ?_⟩
      calc ω ^ z + cantorDenote zs ≈ ω ^ y + (ω ^ y * ofNat k + r) :=
            add_congr (pow_congr (equiv_refl ω) heqz) (equiv_trans heq
              (add_congr (mul_congr (pow_congr (equiv_refl ω) heqz) (equiv_refl _)) (equiv_refl r)))
        _ ≈ ω ^ y + ω ^ y * ofNat k + r := add_assoc _ _ _
        _ ≈ ω ^ y * ofNat (k + 1) + r := add_congr (equiv_symm (equiv_trans
            (mul_congr (equiv_refl _) (ofNat_add k 1))
            (equiv_trans (mul_add _ _ _) (add_congr (mul_one _) (equiv_refl _))))) (equiv_refl r)

/-- Rocq: `NaturalArith.nadd_power_cantor`. -/
theorem nadd_power_cantor {y : Ordinal.{u}} {xs : List Ordinal.{u}} (hy : Complete y)
    (hxs : Each Complete xs) (hd : CantorSequenceDec y xs) :
    ω ^ y ♯ cantorDenote xs ≤ ω ^ y + cantorDenote xs := by
  obtain ⟨k, r, hr, heq⟩ := cantor_dec_split xs y hy hxs hd
  refine le_trans (nadd_le_nadd (le_trans (mul_one _).ge (add_zero _).ge) heq.le)
    (le_trans (same_powers_le y (fun a b => nadd_closed_con y a b hy) _ 1 0 k r (le_refl _)
      (pow_pos ω y) hr) ?_)
  rw [Nat.add_comm 1 k]
  calc ω ^ y * ofNat (k + 1) + (0 ♯ r) ≤ ω ^ y * ofNat (k + 1) + r :=
        add_le_add (le_refl _) (nadd_zero_l r).le
    _ ≤ ω ^ y * 1 + ω ^ y * ofNat k + r :=
        add_le_add (le_trans (mul_le_mul_left _ (ofNat_add k 1).le) (mul_add _ _ _).le) (le_refl r)
    _ ≤ ω ^ y + ω ^ y * ofNat k + r := add_le_add (add_le_add (mul_one _).le (le_refl _)) (le_refl r)
    _ ≤ ω ^ y + (ω ^ y * ofNat k + r) := (add_assoc _ _ _).ge
    _ ≤ ω ^ y + cantorDenote xs := add_le_add (le_refl _) heq.ge

/-- Rocq: `NaturalArith.cantor_denote_nadd_eq_dec`. -/
theorem cantor_denote_nadd_eq_dec : ∀ (xs : List Ordinal.{u}) (x : Ordinal.{u}),
    Each Complete xs → CantorSequenceDec x xs → cantorDenote xs ≈ cantorDenoteNadd xs
  | [], _, _, _ => equiv_refl _
  | y :: ys, _, ⟨hy, hys⟩, ⟨_, hd⟩ =>
    equiv_trans (equiv_intro (add_nadd_le _ _) (nadd_power_cantor hy hys hd))
      (nadd_congr (equiv_refl _) (cantor_denote_nadd_eq_dec ys y hys hd))

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

/-- The ordinal with a child `a` and, if `P`, a child `b`. -/
private def optOrd (P : Prop) (a b : Ordinal.{u}) : Ordinal.{u} :=
  mk (ULift.{u} (Option (PLift P))) fun o => match o.down with
    | none => a
    | some _ => b

private theorem optOrd_complete {P : Prop} {a b : Ordinal.{u}} (hab : a ≤ b) (ha : Complete a)
    (hb : Complete b) : Complete (optOrd P a b) := by
  refine Complete.intro ?_ (.inl ⟨⟨none⟩⟩) ?_
  · rintro ⟨o₁⟩ ⟨o₂⟩
    cases o₁ with
    | none =>
      cases o₂ with
      | none => exact ⟨⟨none⟩, le_refl _, le_refl _⟩
      | some q => exact ⟨⟨some q⟩, hab, le_refl _⟩
    | some p =>
      cases o₂ with
      | none => exact ⟨⟨some p⟩, le_refl _, hab⟩
      | some _ => exact ⟨⟨some p⟩, le_refl _, le_refl _⟩
  · rintro ⟨o⟩
    cases o with
    | none => exact ha
    | some _ => exact hb

/-- The decisions cannot be dropped. Let `x` have the children `0` and, if
`P`, `1`; it is complete, and `x` is `1`, or `2` if `P`. In
`ω ^ 2 ♯ ω ^ x ≤ ω ^ 2 + ω ^ x`, the child `ω ♯ ω ^ x` of the left side must lie
below `ω ^ 2`, which refutes `P`, or below `ω ^ 2 + j` for some `j < ω ^ x`.
Such a `j` lies below `ω ^ (x i) * ω` for a child `i` of `x`: the child `1`
proves `P`; the child `0` makes `j` finite, which refutes `P`.
Rocq: `NaturalArith.cantor_denote_nadd_eq_WEM`. -/
theorem cantor_denote_nadd_eq_WEM
    (h : ∀ (xs : List Ordinal.{u}) (x : Ordinal.{u}), Each Complete xs → CantorSequence x xs →
      cantorDenote xs ≈ cantorDenoteNadd xs) : WeakExcludedMiddle := fun P => by
  let x : Ordinal.{u} := optOrd P 0 1
  let two : Ordinal.{u} := succ 1
  have hx2 : x ≤ two := le_intro fun ⟨o⟩ => by
    cases o with
    | none => exact succ_trans (zero_least _)
    | some _ => exact succ_lt _
  have hxc : Complete x := optOrd_complete (zero_least _) zero_complete (succ_complete zero_complete)
  have hA : ω ^ two ♯ ω ^ x ≤ ω ^ two + ω ^ x :=
    le_trans (nadd_le_nadd (le_refl _) (nadd_zero_r _).ge)
      (le_trans (h [two, x] two ⟨succ_complete (succ_complete zero_complete), hxc, trivial⟩
          ⟨le_refl two, hx2, trivial⟩).ge
        (add_le_add (le_refl _) (add_zero _).le))
  have hP2 : P → ω ^ two ≤ ω ^ x := fun p =>
    pow_le_pow_right ω (succ_least (index_lt x ⟨some ⟨p⟩⟩))
  have hw2 : ω < ω ^ two :=
    lt_of_le_of_lt (pow_one' omega_gt0).ge (pow_lt_pow_right omega_gt1 (succ_lt 1))
  -- under `P`, a finite `j` cannot pad `ω ^ 2` up to `ω ♯ ω ^ x`
  have hfin : ∀ j, j < ω → ω ♯ ω ^ x ≤ ω ^ two + j → ¬P := fun j hj hle p =>
    lt_irrefl ω (lt_of_le_of_lt (add_cancel_le (ω ^ two) (ω ^ two) ω j
      (le_trans (add_nadd_le _ _) (le_trans (nadd_comm _ _).le
        (le_trans (nadd_le_nadd (le_refl _) (hP2 p)) hle))) (le_refl _)) hj)
  have hlt : ω ♯ ω ^ x < ω ^ two + ω ^ x := lt_of_lt_of_le (nadd_increasing1 _ hw2) hA
  match add_lt hlt with
  | .inl h₁ =>
    exact .inr fun p => lt_irrefl (ω ^ two) (lt_of_le_of_lt (le_trans (hP2 p) (nadd_le2 _ _)) h₁)
  | .inr ⟨r, hr⟩ =>
    have hu : ω ^ x ≤ 1 ⊔ sup fun i : x => ω ^ x i * ω := by
      rw [← pow_unfold]
    match lub_lt (lt_of_lt_of_le (index_lt (ω ^ x) r) hu) with
    | .inl hj => exact .inr (hfin _ (lt_trans hj omega_gt1) hr)
    | .inr hs =>
      obtain ⟨⟨o⟩, hs⟩ := sup_lt hs
      cases o with
      | some p => exact .inl fun np => np p.down
      | none =>
        exact .inr (hfin _ (lt_of_lt_of_le hs (le_trans (mul_le_mul_right ω (pow_zero ω).le)
          (one_mul ω).le)) hr)

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

/-! ### The natural sum does not preserve completeness

The children of `u ♯ v` are `u i ♯ v` and `u ♯ v j`. A directed upper bound for
one of each kind must be of one of these two kinds, which compares the gap below
`u` with the gap below `v`. Let `u` have the children `0` and, if `P`, `1`, and
let `v` have the children `1` and, if `P`, `ω`. Both are complete. An upper
bound for `0 ♯ v` and `u ♯ 1` is a child indexed by a proof of `P`, or `0 ♯ v`
(which needs a child of `v` above `u`: `1` refutes `P`, `ω` needs `P`), or
`u ♯ 1` (which refutes `P`). -/

/-- Rocq: `NaturalArith.nadd_complete_directed`. -/
theorem nadd_complete_directed (u v : Ordinal.{u}) (h : Complete (u ♯ v)) (i : u) (j : v) :
    (∃ i', u i ♯ v ≤ u i' ♯ v ∧ u ♯ v j ≤ u i' ♯ v) ∨
    (∃ j', u i ♯ v ≤ u ♯ v j' ∧ u ♯ v j ≤ u ♯ v j') := by
  rw [nadd_unfold] at h
  match complete_directed h (Sum.inl i) (Sum.inr j) with
  | ⟨Sum.inl i', h₁, h₂⟩ => exact .inl ⟨i', h₁, h₂⟩
  | ⟨Sum.inr j', h₁, h₂⟩ => exact .inr ⟨j', h₁, h₂⟩

/-- The natural sum of complete ordinals need not be complete.
Rocq: `NaturalArith.nadd_complete_WEM`. -/
theorem nadd_complete_WEM
    (h : ∀ u v : Ordinal.{u}, Complete u → Complete v → Complete (u ♯ v)) :
    WeakExcludedMiddle := fun P => by
  let u : Ordinal.{u} := optOrd P 0 1
  let v : Ordinal.{u} := optOrd P 1 ω
  have hone : Complete (1 : Ordinal.{u}) := succ_complete zero_complete
  have hu : Complete u := optOrd_complete (zero_least _) zero_complete hone
  have hv : Complete v := optOrd_complete (le_of_lt omega_gt1) hone omega_complete
  have hu3 : u < ω := lt_of_le_of_lt (le_intro fun ⟨o⟩ => by
      cases o with
      | none => exact succ_trans (zero_least _)
      | some _ => exact succ_lt _) (index_lt ω ⟨2⟩)
  match nadd_complete_directed u v (h u v hu hv) ⟨none⟩ ⟨none⟩ with
  | .inl ⟨⟨some p⟩, _, _⟩ => exact .inl fun np => np p.down
  | .inl ⟨⟨none⟩, _, h₂⟩ =>
    -- `u ♯ 1 ≤ 0 ♯ v`, so `u < v`
    have huv : u < v := lt_of_lt_of_le
      (lt_of_le_of_lt (nadd_zero_r u).ge (nadd_increasing2 u (succ_lt 0)))
      (le_trans h₂ (nadd_zero_l v).le)
    obtain ⟨⟨o⟩, hp⟩ := lt_elim huv
    cases o with
    | some p => exact .inl fun np => np p.down
    | none =>
      exact .inr fun p => lt_irrefl 1 (lt_of_lt_of_le (index_lt u ⟨some ⟨p⟩⟩) hp)
  | .inr ⟨⟨some p⟩, _, _⟩ => exact .inl fun np => np p.down
  | .inr ⟨⟨none⟩, h₁, _⟩ =>
    -- `0 ♯ v ≤ u ♯ 1`, which is finite: refutes `P`
    exact .inr fun p => lt_irrefl ω (lt_of_lt_of_le (index_lt v ⟨some ⟨p⟩⟩)
      (le_trans (nadd_zero_l v).ge (le_trans h₁ (le_of_lt (lt_of_lt_of_le
        (nadd_closed_con 1 u 1 hone (lt_of_lt_of_le hu3 (pow_one' omega_gt0).ge)
          (lt_of_lt_of_le omega_gt1 (pow_one' omega_gt0).ge))
        (pow_one' omega_gt0).le)))))

/-- Natural sums of Cantor normal forms merge their exponents, given decisions
between adjacent exponents. Rocq: `NaturalArith.nadd_cantor_sequences_dec`. -/
theorem nadd_cantor_sequences_dec {xs ys zs : List Ordinal.{u}} (hm : MergeLists xs ys zs)
    (a b c : Ordinal.{u}) (hxs : Each Complete xs) (hys : Each Complete ys)
    (hzs : Each Complete zs) (ha : CantorSequenceDec a xs) (hb : CantorSequenceDec b ys)
    (hc : CantorSequenceDec c zs) : cantorDenote xs ♯ cantorDenote ys ≈ cantorDenote zs :=
  equiv_trans (nadd_congr (cantor_denote_nadd_eq_dec xs a hxs ha)
      (cantor_denote_nadd_eq_dec ys b hys hb))
    (equiv_trans (cantor_denote_nadd_merge hm) (equiv_symm (cantor_denote_nadd_eq_dec zs c hzs hc)))

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

/-! ## Tree selection -/

/-- Rocq: `NaturalArith.tree_selection`. -/
def treeSelection : Ordinal.{u} → Ordinal.{u}
  | mk A f => iteratedSmashSum (mk A fun a => treeSelection (f a))

/-- Rocq: `NaturalArith.tree_selection_unfold`. -/
theorem tree_selection_unfold (x : Ordinal.{u}) :
    treeSelection x = iteratedSmashSum (lim fun a : x => treeSelection (x a)) := by
  cases x; rfl

/-- Rocq: `NaturalArith.tree_selection_nonzero`. -/
theorem tree_selection_nonzero (x : Ordinal.{u}) : 0 < treeSelection x := by
  rw [tree_selection_unfold]; exact iteratedSmashSum_nonzero _

/-- Rocq: `NaturalArith.tree_selection_monotone`. -/
theorem tree_selection_monotone : ∀ x y : Ordinal.{u}, x ≤ y → treeSelection x ≤ treeSelection y
  | mk _ f, mk B g, h => iteratedSmashSum_monotone (le_intro fun a =>
    let ⟨b, hb⟩ := le_subord h a
    lt_intro (show (mk B fun b => treeSelection (g b)).Carrier from b)
      (tree_selection_monotone (f a) (g b) hb))

/-- Rocq: `NaturalArith.tree_selection_increasing`. -/
theorem tree_selection_increasing {x y : Ordinal.{u}} (h : x < y) : treeSelection x < treeSelection y := by
  obtain ⟨b, hb⟩ := lt_elim h
  rw [tree_selection_unfold y]
  exact lt_of_le_of_lt (tree_selection_monotone _ _ hb)
    (lt_intro (show (iteratedSmashSum (lim fun a : y => treeSelection (y a))).Carrier from [b])
      (nadd_zero_r _).ge)

/-- Rocq: `NaturalArith.tree_selection_scott_continuous`. -/
theorem tree_selection_scott_continuous : ScottContinuous (treeSelection : Ordinal.{u} → Ordinal.{u}) :=
  fun A f a₀ hd _ => by
    rw [tree_selection_unfold]
    refine limit_least fun xs => ?_
    have hbound : ∃ i, ∀ p, p ∈ xs → f p.1 ≤ f i := by
      induction xs with
      | nil => exact ⟨a₀, fun _ h => nomatch h⟩
      | cons p xs ih =>
        obtain ⟨i, hi⟩ := ih
        obtain ⟨k, hk₁, hk₂⟩ := hd i p.1
        exact ⟨k, fun q hq => match q, hq with
          | _, .head _ => hk₂
          | q, .tail _ hq => le_trans (hi q hq) hk₁⟩
    obtain ⟨i, hi⟩ := hbound
    have hqs : ∃ qs : List (f i).Carrier,
        smashList (lim fun a : sup f => treeSelection (sup f a)) xs ≤
          smashList (lim fun a : f i => treeSelection (f i a)) qs := by
      clear hd
      induction xs with
      | nil => exact ⟨[], le_refl _⟩
      | cons p xs ih =>
        obtain ⟨qs, hqs⟩ := ih fun q hq => hi q (.tail _ hq)
        obtain ⟨q, hq⟩ := lt_elim (lt_of_lt_of_le (index_lt (f p.1) p.2) (hi p (.head _)))
        exact ⟨q :: qs, nadd_le_nadd (tree_selection_monotone _ _ hq) hqs⟩
    obtain ⟨qs, hqs⟩ := hqs
    refine lt_of_lt_of_le ?_ (sup_le (fun i => treeSelection (f i)) i)
    rw [tree_selection_unfold (f i)]
    exact lt_intro (show (iteratedSmashSum (lim fun a : f i => treeSelection (f i a))).Carrier from qs) hqs

/-- Classically, tree selection is a normal function.
Rocq: `NaturalArith.normal_tree_selection`. -/
theorem normal_tree_selection (em : ExcludedMiddle) : NormalFunction (treeSelection : Ordinal.{u} → Ordinal.{u}) where
  monotone := tree_selection_monotone
  increasing _ _ _ h := tree_selection_increasing h
  continuous := tree_selection_scott_continuous
  complete _ _ := ord_complete em _
  nonzero := tree_selection_nonzero

/-- Rocq: `NaturalArith.powOmega_le_tree_selection`. -/
theorem powOmega_le_tree_selection (x : Ordinal.{u}) : ω ^ x ≤ treeSelection x := by
  induction x using ltRec with
  | ind x ih =>
    rw [pow_unfold]
    refine lub_least (succ_least (tree_selection_nonzero x)) (sup_least fun q => ?_)
    rw [mul_unfold]
    refine sup_least fun ⟨i⟩ => le_of_lt ?_
    have hrep : ∀ n : Nat, ω ^ x q * ofNat n ≤
        smashList (lim fun a : x => treeSelection (x a)) (List.replicate n q) := by
      intro n
      induction n with
      | zero => exact le_trans (mul_zero _).le (zero_least _)
      | succ n ihn =>
        calc ω ^ x q * ofNat (n + 1) ≤ ω ^ x q * ofNat n + ω ^ x q := (mul_succ _ _).le
          _ ≤ ω ^ x q * ofNat n ♯ ω ^ x q := add_nadd_le _ _
          _ ≤ smashList (lim fun a : x => treeSelection (x a)) (List.replicate n q) ♯ treeSelection (x q) :=
              nadd_le_nadd ihn (ih (x q) (index_lt x q))
          _ ≤ treeSelection (x q) ♯ smashList (lim fun a : x => treeSelection (x a)) (List.replicate n q) :=
              nadd_comm_le _ _
    rw [tree_selection_unfold]
    exact lt_of_le_of_lt (le_trans (mul_succ _ _).ge (hrep (i + 1)))
      (limit_lt (smashList (lim fun a : x => treeSelection (x a))) (List.replicate (i + 1) q))

/-- For complete `x`, the bound holds constructively: the only uses of
classical logic were to make the children of `x` directed and to add equal
powers, and completeness provides both (`nadd_add_same_powers_con`).
Rocq: `NaturalArith.tree_selection_le_powOmega_complete`. -/
theorem tree_selection_le_powOmega_complete (x : Ordinal.{u}) :
    Complete x → treeSelection x ≤ ω ^ x := by
  induction x using ltRec with
  | ind x ih =>
    intro hx
    rw [tree_selection_unfold]
    refine limit_least fun xs => ?_
    match xs with
    | [] => exact pow_pos ω x
    | o :: l =>
      have hbound : ∃ i, ∀ p, p ∈ o :: l → x p ≤ x i := by
        induction l with
        | nil => exact ⟨o, fun p hp => match hp with | .head _ => le_refl _ | .tail _ h => nomatch h⟩
        | cons a l ih' =>
          obtain ⟨i, hi⟩ := ih'
          obtain ⟨k, hk₁, hk₂⟩ := complete_directed hx i a
          exact ⟨k, fun p hp => match p, hp with
            | _, .head _ => le_trans (hi o (.head _)) hk₁
            | _, .tail _ (.head _) => hk₂
            | p, .tail _ (.tail _ h) => le_trans (hi p (.tail _ h)) hk₁⟩
      obtain ⟨i, hi⟩ := hbound
      have hsum : ∀ ys : List x.Carrier, (∀ p, p ∈ ys → x p ≤ x i) →
          smashList (lim fun a : x => treeSelection (x a)) ys ≤ ω ^ x i * ofNat ys.length := by
        intro ys
        induction ys with
        | nil => intro _; exact zero_least _
        | cons p ys ihys =>
          intro hys
          calc treeSelection (x p) ♯ smashList (lim fun a : x => treeSelection (x a)) ys
              ≤ ω ^ x i * (ω : Ordinal.{u}) ⟨1⟩ ♯ ω ^ x i * (ω : Ordinal.{u}) ⟨ys.length⟩ :=
                nadd_le_nadd (le_trans (ih (x p) (index_lt x p) (complete_subord hx p))
                  (le_trans (pow_le_pow_right ω (hys p (.head _))) (mul_one _).ge))
                  (ihys fun q hq => hys q (.tail _ hq))
            _ ≤ ω ^ x i * ofNat (1 + ys.length) :=
                nadd_add_same_powers_con (x i) 1 ys.length (complete_subord hx i)
            _ = ω ^ x i * ofNat (ys.length + 1) := by rw [Nat.add_comm]
      calc smashList _ (o :: l) ≤ ω ^ x i * ofNat (l.length + 1) := hsum (o :: l) hi
        _ < ω ^ x i * ω := mul_lt_mul_left (pow_pos ω _) (index_lt ω ⟨l.length + 1⟩)
        _ ≤ ω ^ x := pow_index_mul_omega_le x i

/-- Rocq: `NaturalArith.tree_selection_le_powOmega`. -/
theorem tree_selection_le_powOmega (em : ExcludedMiddle) (x : Ordinal.{u}) :
    treeSelection x ≤ ω ^ x :=
  tree_selection_le_powOmega_complete x (ord_complete em x)

/-- Rocq: `NaturalArith.tree_selection_eq_powOmega_complete`. -/
theorem tree_selection_eq_powOmega_complete (x : Ordinal.{u}) (hx : Complete x) :
    treeSelection x ≈ ω ^ x :=
  equiv_intro (tree_selection_le_powOmega_complete x hx) (powOmega_le_tree_selection x)

/-- Classically, tree selection is `x ↦ ω ^ x`.
Rocq: `NaturalArith.tree_selection_eq_powOmega`. -/
theorem tree_selection_eq_powOmega (em : ExcludedMiddle) (x : Ordinal.{u}) :
    treeSelection x ≈ ω ^ x :=
  tree_selection_eq_powOmega_complete x (ord_complete em x)

/-! `treeSelection` does not preserve completeness either. Let `a` have the
children `0` and, if `P`, `1` (so `a` is `1`, or `2` if `P`), and let `x` have
the children `a` and `2`; `x` is complete. The child `ts a ♯ (ts 2 ♯ 0)` of
`ts x` is a natural sum of `ω ^ a` and `ω ^ 2`, and an upper bound for its
children `0 ♯ ω ^ 2` and `ts a ♯ ω` is either `n ♯ ω ^ 2` for a child `n` of
`ts a` (one that is finite refutes `P`; the others need `P`), or `ts a ♯ y` for
some `y < ω ^ 2`, which refutes `¬P`. -/

/-- Rocq: `NaturalArith.tree_selection_finite_or`. -/
theorem tree_selection_finite_or {P : Prop} (f : ULift.{u} (Option (PLift P)) → Ordinal.{u})
    (hf : f ⟨none⟩ ≈ 0) :
    ∀ l : List (ULift.{u} (Option (PLift P))), P ∨ l.foldr (fun o y => treeSelection (f o) ♯ y) 0 < ω
  | [] => .inr omega_gt0
  | ⟨some p⟩ :: _ => .inl p.down
  | ⟨none⟩ :: l =>
    match tree_selection_finite_or f hf l with
    | .inl p => .inl p
    | .inr hl =>
      have h0 : treeSelection (f ⟨none⟩) < ω :=
        lt_of_le_of_lt (tree_selection_monotone _ _ hf.le)
          (lt_of_le_of_lt (le_trans (tree_selection_le_powOmega_complete 0 zero_complete)
            (pow_zero ω).le) omega_gt1)
      .inr (lt_of_lt_of_le (nadd_closed_con 1 _ _ (succ_complete zero_complete)
          (lt_of_lt_of_le h0 (pow_one' omega_gt0).ge) (lt_of_lt_of_le hl (pow_one' omega_gt0).ge))
        (pow_one' omega_gt0).le)

/-- Rocq: `NaturalArith.tree_selection_complete_WEM`. -/
theorem tree_selection_complete_WEM
    (h : ∀ x : Ordinal.{u}, Complete x → Complete (treeSelection x)) :
    WeakExcludedMiddle := fun P => by
  let a : Ordinal.{u} := optOrd P 0 1
  let two : Ordinal.{u} := succ 1
  let x : Ordinal.{u} := mk (ULift Bool) fun b => cond b.down a two
  have hone : Complete (1 : Ordinal.{u}) := succ_complete zero_complete
  have htwo : Complete two := succ_complete hone
  have ha : Complete a := optOrd_complete (zero_least _) zero_complete hone
  have ha2 : a ≤ two := le_intro fun ⟨o⟩ => by
    cases o with
    | none => exact succ_trans (zero_least _)
    | some _ => exact succ_lt _
  have hx : Complete x := by
    refine Complete.intro ?_ (.inl ⟨⟨true⟩⟩) ?_
    · rintro ⟨b₁⟩ ⟨b₂⟩
      refine ⟨⟨false⟩, ?_, ?_⟩
      · cases b₁ with
        | false => exact le_refl _
        | true => exact ha2
      · cases b₂ with
        | false => exact le_refl _
        | true => exact ha2
    · rintro ⟨b⟩
      cases b with
      | false => exact htwo
      | true => exact ha
  let A : Ordinal.{u} := treeSelection a
  let B : Ordinal.{u} := treeSelection two
  have hA : A ≈ ω ^ a := tree_selection_eq_powOmega_complete a ha
  have hB : B ≈ ω ^ two := tree_selection_eq_powOmega_complete two htwo
  have hw2 : ω < ω ^ two :=
    lt_of_le_of_lt (pow_one' omega_gt0).ge (pow_lt_pow_right omega_gt1 (succ_lt 1))
  have hcB : ∀ y, y < B → ω ♯ y < B := fun y hy =>
    lt_of_lt_of_le (nadd_closed_con two _ _ htwo hw2 (lt_of_lt_of_le hy hB.le)) hB.ge
  -- the child of `ts x` for the list `[a, 2]`
  have hc : Complete (A ♯ (B ♯ 0)) :=
    complete_subord (h x hx) (show (treeSelection x).Carrier from [⟨true⟩, ⟨false⟩])
  -- a child of `B ♯ 0` at least `ω`
  obtain ⟨j, hj⟩ := lt_elim (lt_of_lt_of_le hw2 (le_trans hB.ge (nadd_zero_r B).ge))
  match nadd_complete_directed A (B ♯ 0) hc (show (treeSelection a).Carrier from []) j with
  | .inl ⟨l, _, h₂⟩ =>
    -- an upper bound `n ♯ ω ^ 2` with `n` a child of `ts a`
    match tree_selection_finite_or (fun o => a o) (equiv_refl _) l with
    | .inl p => exact .inl fun np => np p
    | .inr hl =>
      exact .inr fun p => lt_irrefl (ω ♯ B) (calc
        ω ♯ B ≤ B ♯ ω := (nadd_comm _ _).le
        _ ≤ A ♯ (B ♯ 0) j := nadd_le_nadd (le_trans hB.le (le_trans
            (pow_le_pow_right ω (succ_least (index_lt a ⟨some ⟨p⟩⟩))) hA.ge)) hj
        _ ≤ A l ♯ (B ♯ 0) := h₂
        _ ≤ A l ♯ B := nadd_le_nadd (le_refl _) (nadd_zero_r B).le
        _ < ω ♯ B := nadd_increasing1 B hl)
  | .inr ⟨m, h₁, _⟩ =>
    -- an upper bound `ts a ♯ y` with `y < ω ^ 2`
    refine .inl fun np => ?_
    have hy : (B ♯ 0) m < B := lt_of_lt_of_le (index_lt (B ♯ 0) m) (nadd_zero_r B).le
    have ha1 : a ≤ 1 := le_intro fun ⟨o⟩ => by
      cases o with
      | none => exact succ_lt 0
      | some p => exact (np p.down).elim
    exact lt_irrefl B (lt_of_le_of_lt (calc
      B ≤ 0 ♯ (B ♯ 0) := le_trans (nadd_zero_r B).ge (nadd_zero_l _).ge
      _ ≤ A ♯ (B ♯ 0) m := h₁
      _ ≤ ω ♯ (B ♯ 0) m := nadd_le_nadd (le_trans hA.le
          (le_trans (pow_le_pow_right ω ha1) (pow_one' omega_gt0).le)) (le_refl _))
      (hcB _ hy))

/-- Consequently completeness is not invariant under `≈`: for complete `x`,
`treeSelection x` and `ω ^ x` are equivalent, and the second is complete.
(`complete_intensional_EM` gives the stronger conclusion from a simpler
witness.) Rocq: `NaturalArith.complete_intensional_WEM`. -/
theorem complete_intensional_WEM
    (h : ∀ x y : Ordinal.{u}, x ≈ y → Complete x → Complete y) : WeakExcludedMiddle :=
  tree_selection_complete_WEM fun x hx =>
    h _ _ (equiv_symm (tree_selection_eq_powOmega_complete x hx)) (pow_complete omega_gt0 omega_complete hx)

/-! ## Fixpoints of `treeSelection`

The least fixpoints of `treeSelection` and `x ↦ ω ^ x` coincide, as `ε 0`,
constructively. The iterates of `ω ^ ·` from `0` are complete, where the two
functions agree, and every prefixpoint of `treeSelection` is one of `ω ^ ·`,
because `ω ^ x ≤ treeSelection x` for all `x`; so no completeness hypothesis on
the competing prefixpoint is needed. More generally the least fixpoints above
any complete `x` coincide. -/

/-- Rocq: `NaturalArith.tree_selection_fix_complete`. -/
theorem tree_selection_fix_complete (x : Ordinal.{u}) (hx : Complete x) :
    fixOrd treeSelection x ≈ fixOrd powOmega x := by
  have hn : ∀ n : Nat,
      iterF treeSelection x n ≈ iterF powOmega x n ∧ Complete (iterF powOmega x n) := by
    intro n
    induction n with
    | zero => exact ⟨equiv_refl x, hx⟩
    | succ n ih =>
      exact ⟨equiv_trans (equiv_intro (tree_selection_monotone _ _ ih.1.le)
          (tree_selection_monotone _ _ ih.1.ge)) (tree_selection_eq_powOmega_complete _ ih.2),
        pow_complete omega_gt0 omega_complete ih.2⟩
  exact equiv_intro
    (sup_least fun ⟨n⟩ =>
      le_trans (hn n).1.le (sup_le (fun n : ULift.{u} Nat => iterF powOmega x n.down) ⟨n⟩))
    (sup_least fun ⟨n⟩ =>
      le_trans (hn n).1.ge (sup_le (fun n : ULift.{u} Nat => iterF treeSelection x n.down) ⟨n⟩))

/-- Rocq: `NaturalArith.tree_selection_fix`. -/
theorem tree_selection_fix (em : ExcludedMiddle) (x : Ordinal.{u}) :
    fixOrd treeSelection x ≈ fixOrd powOmega x :=
  tree_selection_fix_complete x (ord_complete em x)

/-- Rocq: `NaturalArith.tree_selection_ε0`. -/
theorem tree_selection_ε0 : treeSelection (ε 0 : Ordinal.{u}) ≈ ε 0 :=
  equiv_trans (tree_selection_eq_powOmega_complete _ (ε_complete zero_complete))
    (equiv_symm (ε_fixpoint 0))

/-- Rocq: `NaturalArith.tree_selection_ε0_least`. -/
theorem tree_selection_ε0_least (z : Ordinal.{u}) (hz : treeSelection z ≤ z) : ε 0 ≤ z :=
  ε0_least_expOmega_closed z (le_trans (powOmega_le_tree_selection z) hz)

/-! Without completeness the fixpoints differ. The prefixpoints of
`treeSelection` are closed under natural sum, but an ε-number need not be,
constructively. Take `B = ε 1`, `u` with the single child `B` if `P` (and none
otherwise), `A` the least ε-number above `u + 1`, and the ε-number `Z = A ⊔ B`.
Then `u ♯ ε 0 < Z` names a side: below `B`, refuted by `P` (then `u > B`), or
below `A`, refuted by `¬P` (then `u ≈ 0` and `A ≤ ε 0`). -/

/-- Rocq: `NaturalArith.tree_selection_prefixpoint_nadd_closed`. -/
theorem tree_selection_prefixpoint_nadd_closed (z : Ordinal.{u}) (hz : treeSelection z ≤ z)
    {x y : Ordinal.{u}} (hx : x < z) (hy : y < z) : x ♯ y < z := by
  obtain ⟨i, hi⟩ := lt_elim hx
  obtain ⟨j, hj⟩ := lt_elim hy
  have hinf : ∀ w : Ordinal.{u}, w ≤ treeSelection w :=
    increasing_inflationary fun _ _ h => tree_selection_increasing h
  refine lt_of_lt_of_le ?_ hz
  rw [tree_selection_unfold z]
  exact lt_intro (show (iteratedSmashSum (lim fun a : z => treeSelection (z a))).Carrier from [i, j])
    (nadd_monotone _ _ _ _ (le_trans hi (hinf _))
      (le_trans (le_trans hj (hinf _)) (nadd_zero_r _).ge))

/-- Rocq: `NaturalArith.tree_selection_epsilon_WEM`. -/
theorem tree_selection_epsilon_WEM
    (h : ∀ z : Ordinal.{u}, ω ^ z ≤ z → treeSelection z ≤ z) : WeakExcludedMiddle := fun P => by
  let B : Ordinal.{u} := ε 1
  let u : Ordinal.{u} := mk (ULift.{u} (PLift P)) fun _ => B
  let A : Ordinal.{u} := fixOrd powOmega (succ u)
  have hA : ω ^ A ≤ A := fixOrd_prefixpoint (f := powOmega) (pow_continuous ω) (succ u)
  have hB : ω ^ B ≤ B := (ε_fixpoint 1).ge
  have hZ : treeSelection (A ⊔ B) ≤ A ⊔ B :=
    h _ (le_trans (pow_lub ω A B).le
      (lub_least (le_trans hA (lub_le1 A B)) (le_trans hB (lub_le2 A B))))
  have hu : u < A ⊔ B :=
    lt_of_lt_of_le (lt_of_lt_of_le (succ_lt u) (fixOrd_above powOmega (succ u))) (lub_le1 A B)
  have hε : ε 0 < A ⊔ B := lt_of_lt_of_le (ε_increasing (succ_lt 0)) (lub_le2 A B)
  match lub_lt (tree_selection_prefixpoint_nadd_closed _ hZ hu hε) with
  | .inl hs =>
    -- below `A`: refuted by `¬P`
    refine .inl fun np => lt_irrefl A (lt_of_le_of_lt ?_ hs)
    refine le_trans (fixOrd_least powOmega_monotone' (succ u) (ε 0) (succ_least ?_)
      (ε_fixpoint 0).ge) (nadd_le2 u (ε 0))
    exact lt_of_le_of_lt (le_intro fun p => (np p.down.down).elim)
      (lt_of_lt_of_le (pow_pos ω _) (ε_fixpoint 0).ge)
  | .inr hs =>
    -- below `B`: refuted by `P`
    exact .inr fun p => lt_irrefl B (lt_of_lt_of_le (index_lt u ⟨⟨p⟩⟩)
      (le_trans (nadd_le1 u (ε 0)) (le_of_lt hs)))

/-- Rocq: `NaturalArith.tree_selection_fix_WEM`. -/
theorem tree_selection_fix_WEM
    (h : ∀ x : Ordinal.{u}, fixOrd treeSelection x ≤ fixOrd powOmega x) : WeakExcludedMiddle :=
  tree_selection_epsilon_WEM fun z hz =>
    le_trans (sup_le (fun n : ULift.{u} Nat => iterF treeSelection z n.down) ⟨1⟩)
      (le_trans (h z) (fixOrd_least powOmega_monotone' z z (le_refl z) hz))

end Ordinal

end ConstructiveOrdinals
