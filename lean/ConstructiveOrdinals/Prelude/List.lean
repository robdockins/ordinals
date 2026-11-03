/-!
# Axiom-free facts about lists

Most list lemmas in Lean core are proved with `simp` and depend on `propext`.
These are the ones the port needs, proved without axioms. They live in the
namespace `ConstructiveOrdinals.List`, so inside `namespace ConstructiveOrdinals`
a reference such as `List.append_nil` finds these versions first.
-/

namespace ConstructiveOrdinals.List

universe u

variable {α : Type u}

theorem append_nil : ∀ xs : _root_.List α, xs ++ [] = xs
  | [] => rfl
  | x :: xs => congrArg (x :: ·) (append_nil xs)

theorem append_assoc : ∀ xs ys zs : _root_.List α, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | x :: xs, ys, zs => congrArg (x :: ·) (append_assoc xs ys zs)

theorem mem_append_left {a : α} : ∀ {xs : _root_.List α} (ys : _root_.List α), a ∈ xs → a ∈ xs ++ ys
  | _ :: _, _, .head _ => .head _
  | _ :: _, ys, .tail _ h => .tail _ (mem_append_left ys h)

theorem mem_append_right {a : α} : ∀ (xs : _root_.List α) {ys : _root_.List α}, a ∈ ys → a ∈ xs ++ ys
  | [], _, h => h
  | _ :: xs, _, h => .tail _ (mem_append_right xs h)

/-- Induction on lists from the right. Rocq: `List.rev_ind`. -/
theorem rev_ind (P : _root_.List α → Prop) (hnil : P [])
    (hsnoc : ∀ (x : α) (xs : _root_.List α), P xs → P (xs ++ [x])) (xs : _root_.List α) : P xs := by
  have key : ∀ (xs ys : _root_.List α), P ys → P (ys ++ xs) := by
    intro xs
    induction xs with
    | nil => intro ys h; rw [append_nil]; exact h
    | cons x xs ih =>
      intro ys h
      have := ih (ys ++ [x]) (hsnoc x ys h)
      rw [append_assoc] at this
      exact this
  exact key xs [] hnil

end ConstructiveOrdinals.List
