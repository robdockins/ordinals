import ConstructiveOrdinals.Fixpoints

/-!
# Reflecting ordinal operations into notation systems

Port of `Ordinal/Reflection.v`.

`Reflects A f P S x a` says that the syntactic object `a` (built from a
notation type `A`, with denotation `f` and well-formedness invariant `P`)
faithfully implements the ordinal-level object `x`, at the "shape" `S`. For
example, `Reflects A f P (.ord ==> .ord ==> .ord) (· + ·) add'` says that
`add'` is a correct addition algorithm on notations.

Lean has no universe cumulativity, so the ordinal-side interpretation of the
`prop` and `nat` shapes is wrapped in `ULift` to live alongside
`Ordinal.{u}`. Rocq needs no such wrapping.

The file also contains a small library of comparison results (`Ordering`),
which the notation systems use.
-/

namespace ConstructiveOrdinals

universe u v

/-- Shapes of the operations a notation system may reflect.
Rocq: `Reflection.Shape`. -/
inductive Shape : Type where
  | prop
  | nat
  | ord
  | prod (S T : Shape)
  | arrow (S T : Shape)

/-- Function shapes. Rocq: notation `S ==> T`. -/
scoped infixr:25 " ==> " => Shape.arrow

/-- The ordinal-side interpretation of a shape. Rocq: `Reflection.ordShape`. -/
@[reducible] def ordShape : Shape → Type (u + 1)
  | .prop => ULift.{u + 1} Prop
  | .nat => ULift.{u + 1} Nat
  | .ord => Ordinal.{u}
  | .prod S T => ordShape S × ordShape T
  | .arrow S T => ordShape S → ordShape T

/-- The notation-side interpretation of a shape over a notation type `X`.
Rocq: `Reflection.reflShape`. -/
@[reducible] def reflShape : Shape → Type → Type
  | .prop, _ => Prop
  | .nat, _ => Nat
  | .ord, X => X
  | .prod S T, X => reflShape S X × reflShape T X
  | .arrow S T, X => reflShape S X → reflShape T X

/-- `a` correctly reflects `x` at shape `S`. Rocq: `Reflection.reflects`. -/
def Reflects (A : Type) (f : A → Ordinal.{u}) (P : A → Prop) :
    (S : Shape) → ordShape.{u} S → reflShape S A → Prop
  | .prop, p, q => p.down ↔ q
  | .nat, n, m => n.down = m
  | .ord, x, a => x ≈ f a ∧ P a
  | .prod S T, x, a => Reflects A f P S x.1 a.1 ∧ Reflects A f P T x.2 a.2
  | .arrow S T, g, h => ∀ x a, Reflects A f P S x a → Reflects A f P T (g x) (h a)

/-- Rocq: `Reflection.reflects_app`. -/
theorem reflects_app {S T : Shape} {X : Type} {denote : X → Ordinal.{u}} {P : X → Prop}
    {f : ordShape.{u} (S ==> T)} {g : reflShape (S ==> T) X} {x : ordShape.{u} S}
    {y : reflShape S X} (hfg : Reflects X denote P (S ==> T) f g)
    (hxy : Reflects X denote P S x y) : Reflects X denote P T (f x) (g y) :=
  hfg x y hxy

open Ordinal in
/-- If a notation system denoting every ordinal it can represent (up to
normalization) has zero, successor and `ω ^ ·`, then its order type is at
least `ε 0`. Rocq: `Reflection.ε0_least_exp_closed`. -/
theorem ε0_least_exp_closed (X : Type) (denote : X → Ordinal.{0}) (P : X → Prop)
    (zeroX : X) (succX expOmegaX : X → X)
    (hnorm : ∀ x : X, ∃ x', denote x ≈ denote x' ∧ P x')
    (_hzero : Reflects X denote P .ord (0 : Ordinal.{0}) zeroX)
    (hsucc : Reflects X denote P (.ord ==> .ord) succ succX)
    (hexpOmega : Reflects X denote P (.ord ==> .ord) (fun x => ω ^ x) expOmegaX) :
    ε 0 ≤ mk X denote := by
  have hlimit : IsLimit (mk X denote) := ⟨⟨zeroX⟩, fun a => by
    obtain ⟨a', ha₁, ha₂⟩ := hnorm a
    obtain ⟨hs, _⟩ := hsucc (denote a') a' ⟨equiv_refl _, ha₂⟩
    exact ⟨succX a', lt_of_lt_of_le (lt_of_le_of_lt ha₁.le (succ_lt _)) hs.le⟩⟩
  refine ε0_least_expOmega_closed _ ?_
  calc ω ^ mk X denote ≤ ω ^ sup denote := pow_le_pow_right ω (limit_boundedSup hlimit).le
    _ ≤ sup fun x => ω ^ denote x := pow_continuous ω X denote zeroX
    _ ≤ mk X denote := sup_least fun x => by
        obtain ⟨x', hx₁, hx₂⟩ := hnorm x
        obtain ⟨he, _⟩ := hexpOmega (denote x') x' ⟨equiv_refl _, hx₂⟩
        exact le_trans (pow_le_pow_right ω hx₁.le) (le_trans he.le (index_le (mk X denote) _))

/-! ## Comparison results

Rocq's `ordering` (`LT`, `EQ`, `GT`) is Lean's `Ordering` (`lt`, `eq`, `gt`).
Rocq's `ordering_swap` is `Ordering.swap`, and its `lexCompare` (lexicographic
combination) is `Ordering.then`.

Rocq: `Reflection.ordering`, `Reflection.ordering_swap`,
`Reflection.lexCompare`.
-/

/-- The relation between two ordinals that a comparison result claims.
Rocq: `Reflection.ordering_correct`. -/
def OrderingCorrect : Ordering → Ordinal.{u} → Ordinal.{u} → Prop
  | .lt, a, b => a < b
  | .eq, a, b => a ≈ b
  | .gt, a, b => b < a

/-- Comparison of natural numbers by structural recursion, so that it
computes in the kernel. Rocq: `Reflection.nat_compare`. -/
def natCompare : Nat → Nat → Ordering
  | 0, 0 => .eq
  | _ + 1, 0 => .gt
  | 0, _ + 1 => .lt
  | x + 1, y + 1 => natCompare x y

/-- Rocq: `Reflection.nat_compare_correct`. -/
theorem natCompare_correct : ∀ x y : Nat,
    match natCompare x y with
    | .lt => x < y
    | .eq => x = y
    | .gt => y < x
  | 0, 0 => rfl
  | _ + 1, 0 => Nat.zero_lt_succ _
  | 0, _ + 1 => Nat.zero_lt_succ _
  | x + 1, y + 1 => by
    have ih := natCompare_correct x y
    show match natCompare x y with
      | .lt => x + 1 < y + 1
      | .eq => x + 1 = y + 1
      | .gt => y + 1 < x + 1
    revert ih
    cases natCompare x y with
    | lt => exact Nat.succ_lt_succ
    | eq => exact congrArg (· + 1)
    | gt => exact Nat.succ_lt_succ

/-- Rocq: `Reflection.ordering_correct_eq_mor`. -/
theorem OrderingCorrect.congr {o : Ordering} {a a' b b' : Ordinal.{u}} (ha : a ≈ a')
    (hb : b ≈ b') (h : OrderingCorrect o a b) : OrderingCorrect o a' b' :=
  match o, h with
  | .lt, h => Ordinal.lt_of_le_of_lt ha.ge (Ordinal.lt_of_lt_of_le h hb.le)
  | .eq, h => Ordinal.equiv_trans (Ordinal.equiv_symm ha) (Ordinal.equiv_trans h hb)
  | .gt, h => Ordinal.lt_of_le_of_lt hb.ge (Ordinal.lt_of_lt_of_le h ha.le)

end ConstructiveOrdinals
