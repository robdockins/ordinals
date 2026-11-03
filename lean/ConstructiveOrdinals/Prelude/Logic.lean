/-!
# Non-constructive principles, as plain propositions

Rocq's `Stdlib.Logic.ClassicalFacts` and `ChoiceFacts` define classical
principles as propositions, so theorems can take them as explicit hypotheses
rather than assuming them as axioms. These are the Lean counterparts.

Lean's own `Classical.em` and `Classical.choice` are never used.
-/

namespace ConstructiveOrdinals

universe u

/-- The law of the excluded middle, as a hypothesis.
Rocq: `ClassicalFacts.excluded_middle`. -/
def ExcludedMiddle : Prop := ∀ P : Prop, P ∨ ¬P

/-- The weak law of the excluded middle, as a hypothesis.
Rocq: `ClassicalFacts.weak_excluded_middle`. -/
def WeakExcludedMiddle : Prop := ∀ P : Prop, ¬¬P ∨ ¬P

/-- Dependent functional choice for families in `Type u`, as a hypothesis.
Rocq: `ChoiceFacts.DependentFunctionalChoice`. -/
def DependentFunctionalChoice : Prop :=
  ∀ (A : Type u) (B : A → Type u) (R : ∀ x, B x → Prop),
    (∀ x, ∃ y, R x y) → ∃ f : (∀ x, B x), ∀ x, R x (f x)

end ConstructiveOrdinals
