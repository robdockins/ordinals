/-!
# Axiom-free facts about natural numbers

Some lemmas in Lean core are proved with `simp` or `omega` and so depend on
`propext`. This file re-proves the ones the port needs without axioms.

They live in the namespace `ConstructiveOrdinals.Nat`, so inside
`namespace ConstructiveOrdinals` a reference such as `Nat.le_max_left` finds
these versions before the core ones.
-/

namespace ConstructiveOrdinals.Nat

theorem le_max_left (a b : Nat) : a ≤ Nat.max a b := by
  show a ≤ (if a ≤ b then b else a)
  by_cases h : a ≤ b
  · rw [ite_eq_left h]; exact h
  · rw [ite_eq_right h]; exact Nat.le_refl a

theorem le_max_right (a b : Nat) : b ≤ Nat.max a b := by
  show b ≤ (if a ≤ b then b else a)
  by_cases h : a ≤ b
  · rw [ite_eq_left h]; exact Nat.le_refl b
  · rw [ite_eq_right h]
    exact Nat.le_of_lt (Nat.lt_of_not_le h)

/-! ## Ring identities

Core proves these with `simp`, which uses `propext`. -/

protected theorem mul_assoc (a b : Nat) : ∀ c : Nat, a * b * c = a * (b * c)
  | 0 => rfl
  | c + 1 => by
    show a * b * c + a * b = a * (b * c + b)
    rw [_root_.Nat.mul_add, Nat.mul_assoc a b c]

protected theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [_root_.Nat.mul_comm, _root_.Nat.mul_add, _root_.Nat.mul_comm c a, _root_.Nat.mul_comm c b]

protected theorem mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← Nat.mul_assoc, _root_.Nat.mul_comm a b, Nat.mul_assoc]

protected theorem pow_add (a m : Nat) : ∀ n : Nat, a ^ (m + n) = a ^ m * a ^ n
  | 0 => (_root_.Nat.mul_one _).symm
  | n + 1 => by
    show a ^ (m + n) * a = a ^ m * (a ^ n * a)
    rw [Nat.pow_add a m n, Nat.mul_assoc]

/-! ## Subtraction and cancellation -/

protected theorem add_sub_cancel (n : Nat) : ∀ m : Nat, n + m - m = n
  | 0 => rfl
  | m + 1 => (_root_.Nat.succ_sub_succ (n + m) m).trans (Nat.add_sub_cancel n m)

protected theorem sub_add_cancel : ∀ {n m : Nat}, m ≤ n → n - m + m = n
  | n, 0, _ => rfl
  | 0, m + 1, h => absurd h (_root_.Nat.not_succ_le_zero m)
  | n + 1, m + 1, h => by
    show n + 1 - (m + 1) + m + 1 = n + 1
    rw [_root_.Nat.succ_sub_succ, Nat.sub_add_cancel (_root_.Nat.le_of_succ_le_succ h)]

protected theorem add_left_cancel : ∀ {n m k : Nat}, n + m = n + k → m = k
  | 0, m, k, h => (_root_.Nat.zero_add m).symm.trans (h.trans (_root_.Nat.zero_add k))
  | n + 1, m, k, h => by
    rw [_root_.Nat.add_right_comm n 1 m, _root_.Nat.add_right_comm n 1 k] at h
    exact Nat.add_left_cancel (_root_.Nat.succ.inj h)

protected theorem add_right_cancel {n m k : Nat} (h : n + m = k + m) : n = k := by
  rw [_root_.Nat.add_comm n m, _root_.Nat.add_comm k m] at h
  exact Nat.add_left_cancel h

/-! ## Division by repeated subtraction

The core `/` and `%` are irreducible, and the lemmas relating them to each
other use `propext`. These versions compute in the kernel (by repeated
subtraction, with fuel) and have axiom-free specifications. -/

/-- Quotient and remainder of `n` by `b`, with `fuel` bounding the number of
subtractions. -/
def divModAux (b : Nat) : Nat → Nat → Nat × Nat
  | 0, n => (0, n)
  | fuel + 1, n =>
    if b ≤ n then ((divModAux b fuel (n - b)).1 + 1, (divModAux b fuel (n - b)).2) else (0, n)

/-- Quotient of `n` by `b`. -/
def div (n b : Nat) : Nat := (divModAux b (n + 1) n).1

/-- Remainder of `n` by `b`. -/
def mod (n b : Nat) : Nat := (divModAux b (n + 1) n).2

private theorem divModAux_succ_pos {b fuel n : Nat} (h : b ≤ n) :
    divModAux b (fuel + 1) n = ((divModAux b fuel (n - b)).1 + 1, (divModAux b fuel (n - b)).2) :=
  ite_eq_left h

private theorem divModAux_succ_neg {b fuel n : Nat} (h : ¬ b ≤ n) : divModAux b (fuel + 1) n = (0, n) :=
  ite_eq_right h

private theorem divModAux_spec {b : Nat} (hb : 0 < b) : ∀ fuel n : Nat, n < fuel →
    (divModAux b fuel n).1 * b + (divModAux b fuel n).2 = n ∧ (divModAux b fuel n).2 < b
  | 0, _, h => absurd h (_root_.Nat.not_lt_zero _)
  | fuel + 1, n, h => by
    by_cases hbn : b ≤ n
    · rw [divModAux_succ_pos hbn]
      have hlt : n - b < fuel := by
        have h₁ : n - b + b = n := Nat.sub_add_cancel hbn
        refine _root_.Nat.lt_of_add_lt_add_right (?_ : n - b + b < fuel + b)
        rw [h₁]
        exact _root_.Nat.lt_of_lt_of_le h (_root_.Nat.add_le_add_left hb fuel)
      obtain ⟨h₁, h₂⟩ := divModAux_spec hb fuel (n - b) hlt
      refine ⟨?_, h₂⟩
      show ((divModAux b fuel (n - b)).1 + 1) * b + (divModAux b fuel (n - b)).2 = n
      rw [Nat.add_mul, _root_.Nat.one_mul, _root_.Nat.add_right_comm, h₁, Nat.sub_add_cancel hbn]
    · rw [divModAux_succ_neg hbn]
      show 0 * b + n = n ∧ n < b
      rw [_root_.Nat.zero_mul, _root_.Nat.zero_add]
      exact ⟨rfl, _root_.Nat.lt_of_not_le hbn⟩

theorem div_add_mod (n : Nat) {b : Nat} (hb : 0 < b) : div n b * b + mod n b = n :=
  (divModAux_spec hb (n + 1) n (_root_.Nat.lt_succ_self n)).1

theorem mod_lt (n : Nat) {b : Nat} (hb : 0 < b) : mod n b < b :=
  (divModAux_spec hb (n + 1) n (_root_.Nat.lt_succ_self n)).2

theorem div_mul_le (n : Nat) {b : Nat} (hb : 0 < b) : div n b * b ≤ n := by
  exact _root_.Nat.le_trans (_root_.Nat.le_add_right _ _) (_root_.Nat.le_of_eq (div_add_mod n hb))

theorem div_lt {n b : Nat} (hn : 0 < n) (hb : 1 < b) : div n b < n := by
  have h := div_mul_le n (_root_.Nat.lt_trans _root_.Nat.zero_lt_one hb)
  cases _root_.Nat.eq_zero_or_pos (div n b) with
  | inl h0 => rw [h0]; exact hn
  | inr hpos =>
    refine _root_.Nat.lt_of_lt_of_le ?_ h
    have := _root_.Nat.mul_lt_mul_of_pos_left hb hpos
    rw [_root_.Nat.mul_one] at this
    exact this

end ConstructiveOrdinals.Nat
