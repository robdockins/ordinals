import ConstructiveOrdinals.Operators

/-! Tests for `ord_rw` and `ord_mono`. -/

namespace ConstructiveOrdinals.Test
open Ordinal

universe u
variable {a b c d : Ordinal.{u}}

/-- `≈` under a function with a registered monotonicity lemma. -/
example (h : a ≈ b) : succ a ≤ succ b := by
  ord_rw [h]

/-- `≈` under a binder (pointwise `sup`). -/
example {A : Type u} (f : A → Ordinal.{u}) (h : ∀ x, f x ≈ c) :
    sup (fun x => succ (f x)) ≤ sup (fun _ : A => succ c) := by
  ord_mono
  exact (h _).le

/-- `≤` rewriting on the right of `≤` (covariant). -/
example (h : b ≤ c) (h' : a ≤ b) : a ≤ c := by
  ord_rw [← h]
  exact h'

/-- `<` goal, rewriting on the left with `≤` (contravariant: replace `a` by a larger one). -/
example (h : a ≤ b) (h' : b < c) : a < c := by
  ord_rw [h]
  exact h'

/-- `≈` goal with `≈` rewrite under two functions. -/
example (h : a ≈ b) : succ a ⊔ c ≈ succ b ⊔ c := by
  ord_rw [h]

/-- Rewriting in a hypothesis. -/
example (h : a ≈ b) (h' : succ a ≤ c) : succ b ≤ c := by
  ord_rw [h] at h'
  exact h'

/-- `↔` rewriting of the whole goal, without `propext`. -/
example (h : IsZero a) : a ≈ 0 := by
  ord_rw [← isZero_iff]
  exact h

/-- Equations are passed to `rw`. -/
example (x : Ordinal.{u}) : pred x ≤ sup x.size := by
  ord_rw [pred_unfold]

set_option linter.unusedVariables false in
/-- Wrong polarity: `a ≤ b` cannot replace `a` by `b` on the right of `≤`. -/
example (h : a ≤ b) (h' : c ≤ a) : c ≤ a := by
  fail_if_success ord_rw [h]
  exact h'

/-- …but `← h` can replace `b` by `a` there. -/
example (h : a ≤ b) (h' : c ≤ a) : c ≤ b := by
  ord_rw [← h]
  exact h'

end ConstructiveOrdinals.Test
