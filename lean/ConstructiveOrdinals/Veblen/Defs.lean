import ConstructiveOrdinals.Fixpoints

/-!
# The Veblen hierarchy: definitions

Port of `Ordinal/VeblenDefs.v`.

`veblen f β` is the `β`-th function of the Veblen hierarchy over the base
function `f`. Its definition recurses on `β` and, inside that, on the
argument. Lean rejects the nested `fix` of the Rocq definition, so the inner
recursion is the separate function `veblenInner`, which is parameterised by
the outer recursive calls. `veblen_unroll` gives the same characteristic
equation as in Rocq, and `veblen` is then made irreducible, matching Rocq's
`Global Opaque veblen`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-- The inner recursion of `veblen`, on the argument, given the outer
recursive calls `outer a = veblen f (β a)`. -/
def veblenInner (f : Ordinal.{u} → Ordinal.{u}) {A : Type u}
    (outer : A → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk X h => f (mk X h) ⊔ sup fun a => fixOrd (outer a) (mk X fun x => veblenInner f outer (h x))

/-- The Veblen hierarchy over a base function `f`. Rocq: `VeblenDefs.veblen`. -/
def veblen (f : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | mk _ g => veblenInner f fun a => veblen f (g a)

/-- Rocq: `VeblenDefs.veblen_unroll`. -/
theorem veblen_unroll (f : Ordinal.{u} → Ordinal.{u}) (β y : Ordinal.{u}) :
    veblen f β y =
      f y ⊔ sup fun α : β => fixOrd (veblen f (β α)) (lim fun x : y => veblen f β (y x)) := by
  cases β; cases y; rfl

attribute [irreducible] veblen

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- Rocq: `VeblenDefs.veblen_monotone`. -/
@[ord_hint]
theorem veblen_monotone (hmono : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ (β x y : Ordinal.{u}), x ≤ y → veblen f β x ≤ veblen f β y
  | mk A g, x, y, h => by
    induction y using ltRec generalizing x with
    | ind y ih =>
      rw [veblen_unroll f _ x, veblen_unroll f _ y]
      refine lub_least (le_trans (hmono _ _ h) (lub_le1 _ _))
        (le_trans (sup_monotone fun a => ?_) (lub_le2 _ _))
      refine fixOrd_monotone (veblen_monotone hmono (g a)) (limit_least fun i => ?_)
      obtain ⟨j, hj⟩ := lt_elim (le_elim h i)
      exact lt_of_le_of_lt (ih (y j) (index_lt y j) (x i) hj)
        (limit_lt (fun x : y => veblen f (mk A g) (y x)) j)

/-- Rocq: `VeblenDefs.veblen_monotone_first`. -/
@[ord_hint]
theorem veblen_monotone_first (hmono : ∀ x y, x ≤ y → f x ≤ f y) (β : Ordinal.{u}) :
    ∀ α x : Ordinal.{u}, α ≤ β → veblen f α x ≤ veblen f β x := by
  induction β using ltRec with
  | ind β ihβ =>
    intro α x
    induction x using ltRec generalizing α with
    | ind x ihx =>
      intro hαβ
      rw [veblen_unroll f α, veblen_unroll f β]
      refine lub_least (lub_le1 _ _) (le_trans (sup_least fun c => ?_) (lub_le2 _ _))
      obtain ⟨i, hi⟩ := lt_elim (lt_of_lt_of_le (index_lt α c) hαβ)
      calc fixOrd (veblen f (α c)) (lim fun j : x => veblen f α (x j))
          ≤ fixOrd (veblen f (α c)) (lim fun j : x => veblen f β (x j)) :=
            fixOrd_monotone (veblen_monotone hmono (α c))
              (lim_monotone fun j => ihx (x j) (index_lt x j) α hαβ)
        _ ≤ fixOrd (veblen f (β i)) (lim fun j : x => veblen f β (x j)) :=
            fixOrd_monotone_func (fun z => ihβ (β i) (index_lt β i) (α c) z hi)
              (veblen_monotone hmono (β i)) _
        _ ≤ sup fun i : β => fixOrd (veblen f (β i)) (lim fun j : x => veblen f β (x j)) :=
            sup_le (fun i : β => fixOrd (veblen f (β i)) (lim fun j : x => veblen f β (x j))) i

/-- Rocq: `VeblenDefs.veblen_le_mor`. -/
@[ord_mono]
theorem veblen_le (hf : ∀ a b, a ≤ b → f a ≤ f b) {x y x₀ y₀ : Ordinal.{u}} (h : x ≤ y)
    (h₀ : x₀ ≤ y₀) : veblen f x x₀ ≤ veblen f y y₀ :=
  le_trans (veblen_monotone_first hf y x x₀ h) (veblen_monotone hf y x₀ y₀ h₀)

/-- Rocq: `VeblenDefs.veblen_eq_mor`. -/
theorem veblen_congr (hf : ∀ a b, a ≤ b → f a ≤ f b) {x y x₀ y₀ : Ordinal.{u}} (h : x ≈ y)
    (h₀ : x₀ ≈ y₀) : veblen f x x₀ ≈ veblen f y y₀ :=
  equiv_intro (veblen_le hf h.le h₀.le) (veblen_le hf h.ge h₀.ge)

/-- Rocq: `VeblenDefs.veblen_mono_func`. -/
theorem veblen_mono_func {f g : Ordinal.{u} → Ordinal.{u}} (hg : ∀ x y, x ≤ y → g x ≤ g y)
    (hfg : ∀ x, f x ≤ g x) (a : Ordinal.{u}) : ∀ x : Ordinal.{u}, veblen f a x ≤ veblen g a x := by
  induction a using ltRec with
  | ind a iha =>
    intro x
    induction x using ltRec with
    | ind x ihx =>
      rw [veblen_unroll f, veblen_unroll g]
      refine lub_least (le_trans (hfg x) (lub_le1 _ _))
        (le_trans (sup_monotone fun i => sup_monotone fun ⟨n⟩ => ?_) (lub_le2 _ _))
      show iterF (veblen f (a i)) (lim fun j : x => veblen f a (x j)) n ≤
        iterF (veblen g (a i)) (lim fun j : x => veblen g a (x j)) n
      induction n with
      | zero => exact lim_monotone fun j => ihx (x j) (index_lt x j)
      | succ n ih =>
        exact le_trans (iha (a i) (index_lt a i) _) (veblen_monotone hg (a i) _ _ ih)

/-! ## The Feferman–Schütte Γ function -/

/-- Γ enumerates the fixpoints of `b ↦ veblen powOmega b 0`.
Rocq: `VeblenDefs.Γ`. -/
def Γ (a : Ordinal.{u}) : Ordinal.{u} := enumFixpoints (fun b => veblen powOmega b 0) a

/-- Rocq: `VeblenDefs.Γ_monotone`. -/
theorem Γ_monotone {x y : Ordinal.{u}} (h : x ≤ y) : Γ x ≤ Γ y :=
  enumFixpoints_monotone (fun a b h => veblen_monotone_first powOmega_monotone' b a 0 h) x y h

/-- Rocq: `VeblenDefs.Γ_increasing`. -/
theorem Γ_increasing {x y : Ordinal.{u}} (h : x < y) : Γ x < Γ y :=
  enumFixpoints_increasing (fun a b h => veblen_monotone_first powOmega_monotone' b a 0 h) h

end Ordinal

end ConstructiveOrdinals
