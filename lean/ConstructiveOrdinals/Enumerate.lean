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

/-- `z ↦ c + z` enumerates the ordinals above `c`, constructively.
Rocq: `Enumerate.addOrd_enumerates`. -/
theorem add_enumerates (c : Ordinal.{u}) : Enumerates (fun z => c + z) fun z => c ≤ z where
  included x := le_add_right c x
  monotone _ _ h := add_le_add (le_refl c) h
  increasing _ _ h := add_lt_add_left c h
  least x z hz h := by
    rw [add_unfold]
    exact lub_least hz (sup_least fun i => succ_least (h _ (index_lt x i)))

/-- Left subtraction (`c ≤ z` gives `a` with `c + a ≈ z`) implies the excluded
middle, already for `c = truthOrd R` and `z = 1`.
Rocq: `Enumerate.addOrd_left_subtraction_EM`. -/
theorem left_subtraction_EM (h : ∀ c z : Ordinal.{u}, c ≤ z → ∃ a, c + a ≈ z) :
    ExcludedMiddle := fun R => by
  let c : Ordinal.{u} := truthOrd R
  obtain ⟨a, ha⟩ := h c 1 (le_intro fun _ => succ_lt 0)
  have h0 : 0 < c + a := lt_of_lt_of_le (succ_lt 0) ha.ge
  rw [add_unfold] at h0
  match lub_lt h0 with
  | .inl h => exact .inl ((lt_elim h).elim fun ⟨⟨hr⟩⟩ _ => hr)
  | .inr h =>
    obtain ⟨i, _⟩ := sup_lt h
    refine .inr fun hr => lt_irrefl (1 : Ordinal.{u}) (lt_of_lt_of_le ?_ ha.le)
    have hc1 : 1 ≤ c := le_intro fun _ => lt_intro (show c.Carrier from ⟨⟨hr⟩⟩) (le_refl _)
    refine lt_of_le_of_lt hc1 (lt_of_lt_of_le (succ_lt c)
      (le_trans (succ_monotone (le_add_right c (a i))) ?_))
    rw [add_unfold c a]
    exact le_trans (sup_le (fun i : a => succ (c + a i)) i) (lub_le2 _ _)

/-- Surjectivity of enumerations implies the excluded middle: for `z ↦ c + z`
it is left subtraction. Rocq: `Enumerate.enumerates_surjective_EM`. -/
theorem enumerates_surjective_EM
    (h : ∀ (f : Ordinal.{u} → Ordinal.{u}) (P : Ordinal.{u} → Prop),
      Enumerates f P → ∀ x, P x → ∃ a, f a ≈ x) : ExcludedMiddle :=
  left_subtraction_EM fun c z hcz => h _ _ (add_enumerates c) z hcz

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

/-! The function `z + [¬¬(0 < z)]` is monotone and increasing, but does not
reflect the order: `f 0 < f (truthOrd R)` holds as soon as `¬¬R`, while
`f 1 ≤ f (truthOrd R)` gives `R`. So enumerating the range of every monotone,
increasing function implies the excluded middle. -/

/-- Rocq: `Enumerate.g`. -/
private def rangeEMg (z : Ordinal.{u}) : Ordinal.{u} := truthOrd (¬¬(0 < z))

/-- Rocq: `Enumerate.f`. -/
private def rangeEMf (z : Ordinal.{u}) : Ordinal.{u} := z + rangeEMg z

/-- Rocq: `Enumerate.g_monotone`. -/
private theorem rangeEMg_monotone {x y : Ordinal.{u}} (h : x ≤ y) : rangeEMg x ≤ rangeEMg y :=
  le_intro fun ⟨⟨hx⟩⟩ => lt_intro (show (rangeEMg y).Carrier from
    ⟨⟨fun hy => hx fun h0 => hy (lt_of_lt_of_le h0 h)⟩⟩) (le_refl _)

/-- Rocq: `Enumerate.g_le_one`. -/
private theorem rangeEMg_le_one (x : Ordinal.{u}) : rangeEMg x ≤ 1 :=
  le_intro fun _ => succ_lt 0

/-- Rocq: `Enumerate.g_pos`. -/
private theorem rangeEMg_pos {x : Ordinal.{u}} (h : ¬¬(0 < x)) : 0 < rangeEMg x :=
  lt_intro (show (rangeEMg x).Carrier from ⟨⟨h⟩⟩) (le_refl _)

/-- Rocq: `Enumerate.f_monotone`. -/
private theorem rangeEMf_monotone (x y : Ordinal.{u}) (h : x ≤ y) : rangeEMf x ≤ rangeEMf y :=
  add_le_add h (rangeEMg_monotone h)

/-- Rocq: `Enumerate.f_le_succ`. -/
private theorem rangeEMf_le_succ (x : Ordinal.{u}) : rangeEMf x ≤ succ x :=
  le_trans (add_le_add (le_refl x) (rangeEMg_le_one x))
    (le_trans (add_succ x 0).le (succ_monotone (add_zero x).le))

/-- Rocq: `Enumerate.f_increasing`. -/
private theorem rangeEMf_increasing (x y : Ordinal.{u}) (h : x < y) : rangeEMf x < rangeEMf y :=
  lt_of_le_of_lt (rangeEMf_le_succ x) (lt_of_le_of_lt (succ_least h)
    (lt_of_le_of_lt (add_zero y).ge (add_lt_add_left y
      (rangeEMg_pos fun hn => hn (lt_of_le_of_lt (zero_least x) h)))))

/-- Enumerating the range of every monotone, increasing function implies the
excluded middle. Rocq: `Enumerate.enumerates_range_EM`. -/
theorem enumerates_range_EM
    (h : ∀ f : Ordinal.{u} → Ordinal.{u}, (∀ x y, x ≤ y → f x ≤ f y) →
      (∀ x y, x < y → f x < f y) → Enumerates f fun x => ∃ y, x ≈ f y) :
    ExcludedMiddle := by
  -- it suffices to show double-negation elimination
  suffices dne : ∀ R : Prop, ¬¬R → R from
    fun P => dne _ fun hn => hn (.inr fun hp => hn (.inl hp))
  intro R hR
  let w : Ordinal.{u} := truthOrd R
  have h0 : rangeEMf (0 : Ordinal.{u}) ≤ 0 :=
    le_trans (zero_add _).le (le_intro fun ⟨⟨hn⟩⟩ => (hn fun h0 => lt_irrefl 0 h0).elim)
  have hlt : rangeEMf 0 < rangeEMf w :=
    lt_of_le_of_lt h0 (lt_of_lt_of_le
      (rangeEMg_pos fun hn => hR fun hr => hn (lt_intro (show w.Carrier from ⟨⟨hr⟩⟩) (le_refl _)))
      (le_add_left w (rangeEMg w)))
  have hle : rangeEMf 1 ≤ rangeEMf w :=
    (h rangeEMf rangeEMf_monotone rangeEMf_increasing).least 1 (rangeEMf w) ⟨w, equiv_refl _⟩
      fun y hy => lt_of_le_of_lt (rangeEMf_monotone y 0 ((lt_elim hy).elim fun _ h => h)) hlt
  have h1 : succ (1 : Ordinal.{u}) ≤ succ w :=
    le_trans (le_trans (succ_monotone (add_zero 1).ge) (le_trans (add_succ 1 0).ge
      (add_le_add (le_refl 1) (succ_least (rangeEMg_pos fun hn => hn (succ_lt 0))))))
      (le_trans hle (rangeEMf_le_succ w))
  exact (lt_elim (lt_of_lt_of_le (succ_lt 0) (succ_cancel_le h1))).elim fun ⟨⟨hr⟩⟩ _ => hr

/-- Rocq: `Enumerate.increasing_surjective_enumerates_EM`. -/
theorem increasing_surjective_enumerates_EM
    (h : ∀ (f : Ordinal.{u} → Ordinal.{u}) (P : Ordinal.{u} → Prop),
      (∀ x y, x ≤ y → f x ≤ f y) → (∀ x y, x < y → f x < f y) →
      (∀ x, P x → ∃ a, f a ≈ x) → (∀ x, P (f x)) → Enumerates f P) :
    ExcludedMiddle :=
  enumerates_range_EM fun f hmono hinc =>
    h f _ hmono hinc (fun _ ⟨y, hy⟩ => ⟨y, equiv_symm hy⟩) fun x => ⟨x, equiv_refl _⟩

/-- A class is unbounded if every member has a strictly larger member.
Rocq: `Enumerate.unbounded`. -/
def Unbounded (P : Ordinal.{u} → Prop) : Prop := ∀ x, P x → ∃ y, x < y ∧ P y

/-- Unboundedness needs no classical reasoning: `f (succ x)` is above `x`.
Rocq: `Enumerate.enumerates_unbounded`. -/
theorem enumerates_unbounded {f : Ordinal.{u} → Ordinal.{u}}
    {P : Ordinal.{u} → Prop} (henum : Enumerates f P) : Unbounded P := fun x _ =>
  ⟨f (succ x), lt_of_le_of_lt (increasing_inflationary henum.increasing x)
    (henum.increasing _ _ (succ_lt x)), henum.included _⟩

end Ordinal

end ConstructiveOrdinals
