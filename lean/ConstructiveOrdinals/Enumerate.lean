import ConstructiveOrdinals.Arith
import ConstructiveOrdinals.Classical

/-!
# Enumerating classes of ordinals

Port of `Ordinal/Enumerate.v`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-- `f` enumerates the class `P` if `f x` is the least element of `P` strictly
above every `f y` with `y < x`. Rocq: `Enumerate.enumerates`. -/
structure Enumerates (f : Ordinal.{u} → Ordinal.{u}) (P : Ordinal.{u} → Prop) : Prop where
  /-- Rocq: `enumerates_included`. -/
  included : ∀ x, P (f x)
  /-- Rocq: `enumerates_monotone`. -/
  monotone : ∀ x y, x ≤ y → f x ≤ f y
  /-- Rocq: `enumerates_increasing`. -/
  increasing : ∀ x y, x < y → f x < f y
  /-- Rocq: `enumerates_least`. -/
  least : ∀ x z, P z → (∀ y, y < x → f y < z) → f x ≤ z

/-- Rocq: `Enumerate.enumerates_range`. -/
theorem enumerates_range (em : ExcludedMiddle) {f : Ordinal.{u} → Ordinal.{u}}
    (hmono : ∀ x y, x ≤ y → f x ≤ f y) (hinc : ∀ x y, x < y → f x < f y) :
    Enumerates f fun x => ∃ y, x ≈ f y where
  included x := ⟨x, equiv_refl _⟩
  monotone := hmono
  increasing := hinc
  least x z := fun ⟨y, hy⟩ h => le_trans (match order_total em x y with
    | .inl hxy => hmono x y hxy
    | .inr hyx => (lt_irrefl z (lt_of_le_of_lt hy.le (h y hyx))).elim)
    hy.ge

/-- Rocq: `Enumerate.enumerates_equiv_pred`. -/
theorem Enumerates.of_iff {f : Ordinal.{u} → Ordinal.{u}} {P P' : Ordinal.{u} → Prop}
    (hp : ∀ x, P x ↔ P' x) (hf : Enumerates f P) : Enumerates f P' where
  included x := (hp _).1 (hf.included x)
  monotone := hf.monotone
  increasing := hf.increasing
  least x z hz h := hf.least x z ((hp z).2 hz) h

/-- Rocq: `Enumerate.enumerates_unique_aux`. -/
theorem enumerates_unique_aux {f g : Ordinal.{u} → Ordinal.{u}} {P : Ordinal.{u} → Prop}
    (hf : Enumerates f P) (hg : Enumerates g P) (x : Ordinal.{u}) : f x ≤ g x := by
  induction x using ltRec with
  | ind x ih =>
    exact hf.least x _ (hg.included x) fun y hy =>
      lt_of_le_of_lt (ih y hy) (hg.increasing y x hy)

/-- Enumerations of a class are unique. Rocq: `Enumerate.enumerates_unique`. -/
theorem enumerates_unique {f g : Ordinal.{u} → Ordinal.{u}} {P : Ordinal.{u} → Prop}
    (hf : Enumerates f P) (hg : Enumerates g P) (x : Ordinal.{u}) : f x ≈ g x :=
  equiv_intro (enumerates_unique_aux hf hg x) (enumerates_unique_aux hg hf x)

/-- If `f` enumerates `P`, then `f 0` is the least element of `P`.
Rocq: `Enumerate.enumerates_zero`. -/
theorem enumerates_zero {f : Ordinal.{u} → Ordinal.{u}} {P : Ordinal.{u} → Prop}
    (henum : Enumerates f P) (z : Ordinal.{u}) (hz : P z) : f 0 ≤ z :=
  henum.least 0 z hz fun y hy => (zero_lt y hy).elim

/-- If `f` enumerates `P`, then `f (succ x)` is the least element of `P`
strictly above `f x`. Rocq: `Enumerate.enumerates_succ`. -/
theorem enumerates_succ {f : Ordinal.{u} → Ordinal.{u}} {P : Ordinal.{u} → Prop}
    (henum : Enumerates f P) (x z : Ordinal.{u}) (hz : P z) (hx : f x < z) : f (succ x) ≤ z :=
  henum.least (succ x) z hz fun y hy =>
    lt_of_le_of_lt (henum.monotone y x ((lt_elim hy).elim fun _ h => h)) hx

/-- Classically, if `f` enumerates `P` then `f` is surjective onto `P`.
Rocq: `Enumerate.enumerates_surjective`. -/
theorem enumerates_surjective (em : ExcludedMiddle) {f : Ordinal.{u} → Ordinal.{u}}
    {P : Ordinal.{u} → Prop} (henum : Enumerates f P) (x : Ordinal.{u}) (hx : P x) :
    ∃ a, f a ≈ x := by
  obtain ⟨a, ha, hleast⟩ := ord_well_ordered em (fun z => x ≤ f z) x
    (increasing_inflationary henum.increasing x)
  refine ⟨a, equiv_intro (henum.least a x hx fun y hy => ?_) ha⟩
  match order_total em x (f y) with
  | .inl h => exact (lt_irrefl y (lt_of_lt_of_le hy (hleast y h))).elim
  | .inr h => exact h

/-- Classically, a monotone, increasing function that is surjective onto `P`
enumerates `P`. Rocq: `Enumerate.increasing_surjective_enumerates`. -/
theorem increasing_surjective_enumerates (em : ExcludedMiddle) {f : Ordinal.{u} → Ordinal.{u}}
    {P : Ordinal.{u} → Prop} (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (hinc : ∀ x y, x < y → f x < f y) (hsurj : ∀ x, P x → ∃ a, f a ≈ x)
    (hp : ∀ x, P (f x)) : Enumerates f P where
  included := hp
  monotone := hmono
  increasing := hinc
  least x z hz h := by
    obtain ⟨a, ha⟩ := hsurj z hz
    refine le_trans ?_ ha.le
    match order_total em x a with
    | .inl hxa => exact hmono x a hxa
    | .inr hax => exact (lt_irrefl z (lt_of_le_of_lt ha.ge (h a hax))).elim

/-- A class is unbounded if every member has a strictly larger member.
Rocq: `Enumerate.unbounded`. -/
def Unbounded (P : Ordinal.{u} → Prop) : Prop := ∀ x, P x → ∃ y, x < y ∧ P y

/-- Rocq: `Enumerate.enumerates_unbounded`. -/
theorem enumerates_unbounded (em : ExcludedMiddle) {f : Ordinal.{u} → Ordinal.{u}}
    {P : Ordinal.{u} → Prop} (henum : Enumerates f P) : Unbounded P := fun x hx =>
  let ⟨a, ha⟩ := enumerates_surjective em henum x hx
  ⟨f (succ a), lt_of_le_of_lt ha.ge (henum.increasing _ _ (succ_lt a)), henum.included _⟩

end Ordinal

end ConstructiveOrdinals
