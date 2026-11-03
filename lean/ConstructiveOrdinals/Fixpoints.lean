import ConstructiveOrdinals.Arith
import ConstructiveOrdinals.Enumerate

/-!
# Fixpoints of ordinal functions

Port of `Ordinal/Fixpoints.v`: least fixpoints above a base by ω-iteration,
the enumeration of the fixpoints of a function, and the ε numbers.

The Rocq file states its first lemmas inside a section with hypotheses on `f`.
Each Lean lemma takes exactly the hypotheses its Rocq counterpart has after
the section is closed, as reported by Rocq's `Check`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- `n`-fold iteration of `f` starting at `base`. Rocq: `Fixpoints.iter_f`. -/
def iterF (f : Ordinal.{u} → Ordinal.{u}) (base : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => base
  | n + 1 => f (iterF f base n)

/-- Rocq: `Fixpoints.iter_f_monotone`. -/
theorem iterF_monotone (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ (i : Nat) (x y : Ordinal.{u}), x ≤ y → iterF f x i ≤ iterF f y i
  | 0, _, _, h => h
  | i + 1, x, y, h => hf _ _ (iterF_monotone hf i x y h)

/-- The least fixpoint of `f` above `base` (when `f` is continuous and
inflationary), reached by iterating `ω` times. Rocq: `Fixpoints.fixOrd`. -/
def fixOrd (f : Ordinal.{u} → Ordinal.{u}) (base : Ordinal.{u}) : Ordinal.{u} :=
  sup fun n : ULift.{u} Nat => iterF f base n.down

/-- Rocq: `Fixpoints.fixOrd_above`. -/
theorem fixOrd_above (f : Ordinal.{u} → Ordinal.{u}) (base : Ordinal.{u}) : base ≤ fixOrd f base :=
  sup_le (fun n : ULift.{u} Nat => iterF f base n.down) ⟨0⟩

/-- Rocq: `Fixpoints.iter_f_complete`. -/
theorem iterF_complete (n : Nat) (base : Ordinal.{u}) (hb : Complete base)
    (hf : ∀ x, Complete x → Complete (f x)) : Complete (iterF f base n) := by
  induction n with
  | zero => exact hb
  | succ n ih => exact hf _ ih

/-- Rocq: `Fixpoints.iter_f_index_monotone`. -/
theorem iterF_index_monotone {i j : Nat} (hf₁ : ∀ x, Complete x → x ≤ f x)
    (hf₂ : ∀ x, Complete x → Complete (f x)) (h : i ≤ j) (base : Ordinal.{u})
    (hb : Complete base) : iterF f base i ≤ iterF f base j := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (hf₁ _ (iterF_complete _ base hb hf₂))

/-- Rocq: `Fixpoints.directed_iter_f`. -/
theorem directed_iterF (base : Ordinal.{u}) (hf₁ : ∀ x, Complete x → x ≤ f x)
    (_hf₂ : ∀ x y, x ≤ y → f x ≤ f y) (hf₃ : ∀ x, Complete x → Complete (f x))
    (hb : Complete base) : Directed (ULift.{u} Nat) fun n => iterF f base n.down :=
  fun i j => ⟨⟨Nat.max i.down j.down⟩,
    iterF_index_monotone hf₁ hf₃ (Nat.le_max_left _ _) base hb,
    iterF_index_monotone hf₁ hf₃ (Nat.le_max_right _ _) base hb⟩

/-- Rocq: `Fixpoints.fixOrd_monotone`. -/
theorem fixOrd_monotone (hmono : ∀ x y, x ≤ y → f x ≤ f y) {x y : Ordinal.{u}} (h : x ≤ y) :
    fixOrd f x ≤ fixOrd f y :=
  sup_monotone fun n => iterF_monotone hmono n.down x y h

/-- Rocq: `Fixpoints.fixOrd_prefixpoint`. -/
theorem fixOrd_prefixpoint (hcont : StronglyContinuous f) (base : Ordinal.{u}) :
    f (fixOrd f base) ≤ fixOrd f base :=
  le_trans (hcont _ _ ⟨0⟩) (sup_least fun i =>
    sup_le (fun n : ULift.{u} Nat => iterF f base n.down) ⟨i.down + 1⟩)

/-- Rocq: `Fixpoints.fixOrd_fixpoint`. -/
theorem fixOrd_fixpoint (hcont : StronglyContinuous f) (hinf : ∀ x, x ≤ f x)
    (base : Ordinal.{u}) : fixOrd f base ≈ f (fixOrd f base) :=
  equiv_intro (hinf _) (fixOrd_prefixpoint hcont base)

/-- Rocq: `Fixpoints.fixOrd_least`. -/
theorem fixOrd_least (hmono : ∀ x y, x ≤ y → f x ≤ f y) (base z : Ordinal.{u})
    (h₁ : base ≤ z) (h₂ : f z ≤ z) : fixOrd f base ≤ z :=
  sup_least fun ⟨i⟩ => by
    induction i with
    | zero => exact h₁
    | succ i ih => exact le_trans (hmono _ _ ih) h₂

/-- Rocq: `Fixpoints.normal_fix_continuous`. -/
theorem normal_fix_continuous (hmono : ∀ x y, x ≤ y → f x ≤ f y) (hcont : StronglyContinuous f) :
    StronglyContinuous (fixOrd f) := fun A g a₀ =>
  sup_least fun ⟨i⟩ => by
    induction i with
    | zero => exact sup_monotone fun a => fixOrd_above f (g a)
    | succ i ih =>
      exact le_trans (hmono _ _ ih) (le_trans (hcont _ _ a₀)
        (sup_monotone fun a => fixOrd_prefixpoint hcont (g a)))

/-- Rocq: `Fixpoints.normal_fix_complete`. -/
theorem normal_fix_complete (base : Ordinal.{u}) (hb : Complete base)
    (hf₁ : ∀ x, Complete x → x ≤ f x) (hf₂ : ∀ x y, x ≤ y → f x ≤ f y)
    (hf₃ : ∀ x, Complete x → Complete (f x)) : Complete (fixOrd f base) := by
  refine sup_complete (fun n => iterF_complete _ base hb hf₃) (directed_iterF base hf₁ hf₂ hf₃ hb) ?_
  match complete_zeroDec hb with
  | .inr h => exact .inl ⟨⟨0⟩, h⟩
  | .inl hb₀ =>
    match complete_zeroDec (hf₃ base hb) with
    | .inr h => exact .inl ⟨⟨1⟩, h⟩
    | .inl hfb₀ =>
      refine .inr fun ⟨i⟩ => ?_
      induction i with
      | zero => exact hb₀
      | succ i ih => exact le_trans (hf₂ _ _ (le_trans ih (zero_least base))) hfb₀

/-- Rocq: `Fixpoints.iter_f_monotone_func`. -/
theorem iterF_monotone_func {f g : Ordinal.{u} → Ordinal.{u}} (hf : ∀ x, f x ≤ g x)
    (hg : ∀ x y, x ≤ y → g x ≤ g y) : ∀ (n : Nat) (x : Ordinal.{u}), iterF f x n ≤ iterF g x n
  | 0, _ => le_refl _
  | n + 1, x => le_trans (hf _) (hg _ _ (iterF_monotone_func hf hg n x))

/-- Rocq: `Fixpoints.fixOrd_monotone_func`. -/
theorem fixOrd_monotone_func {f g : Ordinal.{u} → Ordinal.{u}} (hf : ∀ x, f x ≤ g x)
    (hg : ∀ x y, x ≤ y → g x ≤ g y) (x : Ordinal.{u}) : fixOrd f x ≤ fixOrd g x :=
  sup_monotone fun n => iterF_monotone_func hf hg n.down x

/-! ## Enumerating fixpoints -/

/-- The enumeration of the fixpoints of `f`. Rocq: `Fixpoints.enum_fixpoints`. -/
def enumFixpoints (f : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk B g => fixOrd f (mk B fun b => enumFixpoints f (g b))

theorem enumFixpoints_unfold (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) :
    enumFixpoints f x = fixOrd f (mk x.Carrier fun b => enumFixpoints f (x b)) := by
  cases x; rfl

/-- Rocq: `Fixpoints.enum_fixpoints_monotone`. -/
theorem enumFixpoints_monotone (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ x y : Ordinal.{u}, x ≤ y → enumFixpoints f x ≤ enumFixpoints f y
  | x, mk C h, hxy => by
    rw [enumFixpoints_unfold f x, enumFixpoints_unfold f (mk C h)]
    refine fixOrd_monotone hf (le_intro fun b => ?_)
    obtain ⟨c, hc⟩ := le_subord hxy b
    exact lt_intro (show (mk C fun c => enumFixpoints f (h c)).Carrier from c)
      (enumFixpoints_monotone hf (x b) (h c) hc)

/-- Rocq: `Fixpoints.enum_fixpoints_increasing`. -/
theorem enumFixpoints_increasing (hf : ∀ x y, x ≤ y → f x ≤ f y) {x y : Ordinal.{u}} (h : x < y) :
    enumFixpoints f x < enumFixpoints f y := by
  obtain ⟨i, hi⟩ := lt_elim h
  refine lt_of_le_of_lt (enumFixpoints_monotone hf _ _ hi) (lt_of_lt_of_le
    (index_lt (mk y.Carrier fun b => enumFixpoints f (y b)) i) ?_)
  rw [enumFixpoints_unfold f y]
  exact fixOrd_above f _

/-- Rocq: `Fixpoints.enum_fixpoints_func_mono`. -/
theorem enumFixpoints_func_mono {f g : Ordinal.{u} → Ordinal.{u}}
    (hf : ∀ x y, x ≤ y → f x ≤ f y) (hg : ∀ x y, x ≤ y → g x ≤ g y) (hfg : ∀ x, f x ≤ g x) :
    ∀ x : Ordinal.{u}, enumFixpoints f x ≤ enumFixpoints g x
  | mk A q => by
    rw [enumFixpoints_unfold f, enumFixpoints_unfold g]
    exact le_trans (fixOrd_monotone hf (le_intro fun a =>
        lt_intro (show (mk A fun a => enumFixpoints g (q a)).Carrier from a)
          (enumFixpoints_func_mono hf hg hfg (q a))))
      (fixOrd_monotone_func hfg hg _)

/-- Rocq: `Fixpoints.enum_are_fixpoints`. -/
theorem enum_are_fixpoints (hcont : StronglyContinuous f) (hinf : ∀ x, x ≤ f x)
    (x : Ordinal.{u}) : enumFixpoints f x ≈ f (enumFixpoints f x) := by
  rw [enumFixpoints_unfold]
  exact fixOrd_fixpoint hcont hinf _

/-- Rocq: `Fixpoints.enum_fixpoints_zero`. -/
theorem enumFixpoints_zero (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    enumFixpoints f 0 ≈ fixOrd f 0 := by
  rw [enumFixpoints_unfold]
  exact equiv_intro (fixOrd_monotone hf (le_intro fun a => PEmpty.elim a))
    (fixOrd_monotone hf (zero_least _))

/-- Rocq: `Fixpoints.enum_fixpoints_succ`. -/
theorem enumFixpoints_succ (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) :
    enumFixpoints f (succ x) ≈ fixOrd f (succ (enumFixpoints f x)) := by
  rw [enumFixpoints_unfold]
  exact equiv_refl _

/-- Rocq: `Fixpoints.enum_fixpoints_cont`. -/
theorem enumFixpoints_cont (hmono : ∀ x y, x ≤ y → f x ≤ f y) (hinf : ∀ x, x ≤ f x)
    (hcont : StronglyContinuous f) : StronglyContinuous (enumFixpoints f) := fun A g a₀ => by
  rw [enumFixpoints_unfold f (sup g)]
  refine fixOrd_least hmono _ _ (le_intro fun p => ?_)
    (le_trans (hcont _ _ a₀) (sup_monotone fun a => (enum_are_fixpoints hcont hinf (g a)).ge))
  exact lt_of_lt_of_le (enumFixpoints_increasing hmono (index_lt (g p.1) p.2))
    (sup_le (fun a => enumFixpoints f (g a)) p.1)

/-- Rocq: `Fixpoints.enum_fixpoints_enumerates`. -/
theorem enumFixpoints_enumerates (hinf : ∀ x, x ≤ f x) (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (hcont : StronglyContinuous f) : Enumerates (enumFixpoints f) fun x => x ≈ f x where
  included := enum_are_fixpoints hcont hinf
  monotone := enumFixpoints_monotone hmono
  increasing _ _ := enumFixpoints_increasing hmono
  least x z hz₁ hz₂ := by
    rw [enumFixpoints_unfold]
    exact fixOrd_least hmono _ _ (le_intro fun a => hz₂ _ (index_lt x a)) hz₁.ge

/-- Rocq: `Fixpoints.enum_fixpoints_enumerates_range`. -/
theorem enumFixpoints_enumerates_range (hinf : ∀ x, x ≤ f x) (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (hcont : StronglyContinuous f) :
    Enumerates (enumFixpoints f) fun x => ∃ y, x ≈ enumFixpoints f y where
  included x := ⟨x, equiv_refl _⟩
  monotone := enumFixpoints_monotone hmono
  increasing _ _ := enumFixpoints_increasing hmono
  least x z := fun ⟨y, hy⟩ h => by
    rw [enumFixpoints_unfold]
    exact fixOrd_least hmono _ _ (le_intro fun a => h _ (index_lt x a))
      (le_trans (hmono _ _ hy.le) (le_trans (enum_are_fixpoints hcont hinf y).ge hy.ge))

/-- Rocq: `Fixpoints.enum_fixpoints_complete`. -/
theorem enumFixpoints_complete (hf₁ : ∀ x, Complete x → x ≤ f x)
    (hf₂ : ∀ x y, x ≤ y → f x ≤ f y) (hf₃ : ∀ x, Complete x → Complete (f x)) :
    ∀ x : Ordinal.{u}, Complete x → Complete (enumFixpoints f x)
  | mk B g, hc => by
    rw [enumFixpoints_unfold]
    refine normal_fix_complete _ (lim_complete
      (fun b => enumFixpoints_complete hf₁ hf₂ hf₃ (g b) (complete_subord hc b))
      (fun b₁ b₂ => ?_) hc.elim.2.1) hf₁ hf₂ hf₃
    obtain ⟨b', h₁, h₂⟩ := complete_directed hc b₁ b₂
    exact ⟨b', enumFixpoints_monotone hf₂ _ _ h₁, enumFixpoints_monotone hf₂ _ _ h₂⟩

/-! ## The ε numbers -/

/-- The ε numbers, which enumerate the fixpoints of `x ↦ ω ^ x`.
Rocq: `Fixpoints.ε`. -/
def ε (x : Ordinal.{u}) : Ordinal.{u} := enumFixpoints powOmega x

private theorem powOmega_monotone' : ∀ x y : Ordinal.{u}, x ≤ y → powOmega x ≤ powOmega y :=
  fun _ _ => powOmega_monotone

private theorem powOmega_inflationary : ∀ x : Ordinal.{u}, x ≤ powOmega x :=
  increasing_inflationary fun _ _ => powOmega_increasing

/-- Rocq: `Fixpoints.ε_monotone`. -/
theorem ε_monotone {x y : Ordinal.{u}} (h : x ≤ y) : ε x ≤ ε y :=
  enumFixpoints_monotone powOmega_monotone' x y h

/-- Rocq: `Fixpoints.ε_increasing`. -/
theorem ε_increasing {x y : Ordinal.{u}} (h : x < y) : ε x < ε y :=
  enumFixpoints_increasing powOmega_monotone' h

/-- Rocq: `Fixpoints.ε_continuous`. -/
theorem ε_continuous : StronglyContinuous (ε : Ordinal.{u} → Ordinal.{u}) :=
  enumFixpoints_cont powOmega_monotone' powOmega_inflationary (pow_continuous ω)

/-- Rocq: `Fixpoints.ε_fixpoint`. -/
theorem ε_fixpoint (x : Ordinal.{u}) : ε x ≈ ω ^ ε x :=
  enum_are_fixpoints (pow_continuous ω) powOmega_inflationary x

/-- Rocq: `Fixpoints.ε_enumerates`. -/
theorem ε_enumerates : Enumerates (ε : Ordinal.{u} → Ordinal.{u}) fun x => x ≈ ω ^ x :=
  enumFixpoints_enumerates powOmega_inflationary powOmega_monotone' (pow_continuous ω)

/-- Rocq: `Fixpoints.ε_complete`. -/
theorem ε_complete {x : Ordinal.{u}} (hx : Complete x) : Complete (ε x) :=
  enumFixpoints_complete (fun x _ => powOmega_inflationary x) powOmega_monotone'
    (fun _ h => pow_complete omega_gt0 omega_complete h) x hx

/-- `ε 0` is the least ordinal closed under `x ↦ ω ^ x`.
Rocq: `Fixpoints.ε0_least_expOmega_closed`. -/
theorem ε0_least_expOmega_closed (X : Ordinal.{u}) (h : ω ^ X ≤ X) : ε 0 ≤ X := by
  show enumFixpoints powOmega 0 ≤ X
  rw [enumFixpoints_unfold]
  exact fixOrd_least powOmega_monotone' _ X (le_intro fun a => PEmpty.elim a) h

/-- Rocq: `Fixpoints.KnuthUp_epsilon`. -/
theorem knuthUp_epsilon : knuthUp 2 (ω : Ordinal.{u}) ω ≈ ε 0 := by
  have hε : ω ^ ε (0 : Ordinal.{u}) ≤ ε 0 := (ε_fixpoint 0).ge
  refine equiv_intro ?_ ?_
  · show fold 1 (fun b => ω ^ b) ω ≤ ε 0
    exact fold_least (fun _ => ε 0)
      (fun _ => succ_least (lt_of_lt_of_le (pow_pos ω _) hε))
      (fun _ _ h => pow_le_pow_right ω h) (fun _ _ => hε) ω
  · show enumFixpoints powOmega 0 ≤ knuthUp 2 ω ω
    rw [enumFixpoints_unfold]
    exact fixOrd_least powOmega_monotone' _ _ (le_intro fun a => PEmpty.elim a)
      (knuthUp_omega_fix 1 ω Nat.zero_lt_one omega_gt0).le

end Ordinal

end ConstructiveOrdinals
