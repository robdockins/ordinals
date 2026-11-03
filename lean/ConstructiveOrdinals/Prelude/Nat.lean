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
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Nat.le_refl a

theorem le_max_right (a b : Nat) : b ≤ Nat.max a b := by
  show b ≤ (if a ≤ b then b else a)
  by_cases h : a ≤ b
  · rw [if_pos h]; exact Nat.le_refl b
  · rw [if_neg h]
    exact Nat.le_of_lt (Nat.lt_of_not_le h)

end ConstructiveOrdinals.Nat
