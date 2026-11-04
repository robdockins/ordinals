import ConstructiveOrdinals.Veblen.Defs
import ConstructiveOrdinals.Cantor

/-!
# Normal functions and the Veblen hierarchy, constructively

Port of `Ordinal/VeblenCon.v`.

This develops the theory of normal functions and the Veblen hierarchy without
the excluded middle. Classical hypotheses are replaced by completeness
assumptions.

`VeblenCon.v` reuses several names already used by `Enumerate.v` and
`Fixpoints.v`, for versions with different hypotheses (normal functions and
complete arguments). In Lean these live in the namespace `Ordinal.Con`, for
example `Con.Enumerates`. The declarations whose statements are identical to
earlier ones (`directed_iter_f`, `normal_fix_complete`, `enum_fixpoints_succ`
and `Γ`) are not repeated.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-- `s` preserves nonempty directed suprema of complete ordinals.
Rocq: `VeblenCon.scott_continuous`. -/
def ScottContinuous (s : Ordinal.{u} → Ordinal.{u}) : Prop :=
  ∀ (A : Type u) (f : A → Ordinal.{u}) (_ : A), Directed A f → (∀ a, Complete (f a)) →
    s (sup f) ≤ sup fun i => s (f i)

/-- Normal functions, in the constructive sense used throughout.
Rocq: `VeblenCon.normal_function`. -/
structure NormalFunction (f : Ordinal.{u} → Ordinal.{u}) : Prop where
  /-- Rocq: `normal_monotone`. -/
  monotone : ∀ x y, x ≤ y → f x ≤ f y
  /-- Rocq: `normal_increasing`. -/
  increasing : ∀ x y, Complete y → x < y → f x < f y
  /-- Rocq: `normal_continuous`. -/
  continuous : ScottContinuous f
  /-- Rocq: `normal_complete`. -/
  complete : ∀ x, Complete x → Complete (f x)
  /-- Rocq: `normal_nonzero`. -/
  nonzero : ∀ x, 0 < f x

attribute [ord_hint] NormalFunction.monotone NormalFunction.complete NormalFunction.nonzero

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- Rocq: `VeblenCon.normal_inflationary`. -/
theorem normal_inflationary (hf : NormalFunction f) : ∀ x : Ordinal.{u}, Complete x → x ≤ f x
  | mk X g, hc => le_intro fun i =>
    lt_of_le_of_lt (normal_inflationary hf (g i) (complete_subord hc i))
      (hf.increasing _ _ hc (index_lt (mk X g) i))

/-- Rocq: `VeblenCon.lim_normal_complete`. -/
theorem lim_normal_complete (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hx : Complete x) : Complete (lim fun i : x => f (x i)) :=
  lim_complete (fun i => hf.complete _ (complete_subord hx i))
    (directed_monotone x _ (fun _ _ h => hf.monotone _ _ h) hx) hx.elim.2.1

/-- Rocq: `VeblenCon.addOrd_normal`. -/
theorem add_normal {x : Ordinal.{u}} (h₀ : 0 < x) (hx : Complete x) :
    NormalFunction (fun y => x + y) where
  monotone _ _ h := add_le_add (le_refl x) h
  increasing _ _ _ h := add_lt_add_left x h
  continuous A g a₀ _ _ := add_continuous x A g a₀
  complete _ h := add_complete hx h
  nonzero y := lt_of_lt_of_le h₀ (le_add_right x y)

/-- Rocq: `VeblenCon.onePlus_complete`. -/
theorem onePlus_complete {x : Ordinal.{u}} (hx : Complete x) : Complete (1 + x) :=
  add_complete (succ_complete zero_complete) hx

/-- Rocq: `VeblenCon.onePlus_normal`. -/
@[ord_hint]
theorem onePlus_normal : NormalFunction (fun y : Ordinal.{u} => 1 + y) :=
  add_normal (succ_lt 0) (succ_complete zero_complete)

/-- Rocq: `VeblenCon.onePlus_nonzero`. -/
theorem onePlus_nonzero (x : Ordinal.{u}) : 0 < 1 + x :=
  lt_of_lt_of_le (succ_lt 0) (le_add_right 1 x)

/-- Rocq: `VeblenCon.onePlus_least`. -/
theorem onePlus_least (hinc : ∀ x y, x < y → f x < f y) (hnz : ∀ x, 0 < f x)
    (x : Ordinal.{u}) : 1 + x ≤ f x := by
  induction x using ltRec with
  | ind x ih =>
    rw [add_unfold]
    exact lub_least (succ_least (hnz x)) (sup_least fun i => succ_least
      (lt_of_le_of_lt (ih (x i) (index_lt x i)) (hinc _ _ (index_lt x i))))

/-- Rocq: `VeblenCon.onePlus_least_normal`. -/
theorem onePlus_least_normal (hf : NormalFunction f) (x : Ordinal.{u}) : Complete x → 1 + x ≤ f x := by
  induction x using ltRec with
  | ind x ih =>
    intro hx
    rw [add_unfold]
    exact lub_least (succ_least (hf.nonzero x)) (sup_least fun i => succ_least
      (lt_of_le_of_lt (ih (x i) (index_lt x i) (complete_subord hx i))
        (hf.increasing _ _ hx (index_lt x i))))

/-- Rocq: `VeblenCon.onePlus_finite`. -/
@[ord_hint]
theorem onePlus_finite (n : Nat) : ofNat.{u} n < 1 + ofNat n :=
  lt_of_lt_of_le (succ_lt _) (onePlus_finite_succ n).ge

/-- Rocq: `VeblenCon.powOmega_normal`. -/
@[ord_hint]
theorem powOmega_normal : NormalFunction (powOmega : Ordinal.{u} → Ordinal.{u}) where
  monotone := powOmega_monotone'
  increasing _ _ _ h := powOmega_increasing h
  continuous A g a₀ _ _ := pow_continuous ω A g a₀
  complete _ h := pow_complete omega_gt0 omega_complete h
  nonzero x := pow_pos ω x

/-- `f` enumerates the class `P`, in the constructive sense with completeness
side conditions. Compare `Ordinal.Enumerates`, which has none.
Rocq: `VeblenCon.enumerates`. -/
structure Con.Enumerates (f : Ordinal.{u} → Ordinal.{u}) (P : Ordinal.{u} → Prop) : Prop where
  /-- Rocq: `enumerates_included`. -/
  included : ∀ x, Complete x → P (f x)
  /-- Rocq: `enumerates_monotone`. -/
  monotone : ∀ x y, x ≤ y → f x ≤ f y
  /-- Rocq: `enumerates_increasing`. -/
  increasing : ∀ x y, Complete y → x < y → f x < f y
  /-- Rocq: `enumerates_least`. -/
  least : ∀ x z, Complete x → Complete z → P z → (∀ y, y < x → f y < z) → f x ≤ z

/-- `x` is a critical ordinal for `β` if it is a fixpoint of `veblen f α`
for every complete `α < β`. Rocq: `VeblenCon.critical_ordinal`. -/
def CriticalOrdinal (f : Ordinal.{u} → Ordinal.{u}) (β x : Ordinal.{u}) : Prop :=
  ∀ α, Complete α → α < β → x ≈ veblen f α x

/-- Rocq: `VeblenCon.strongly_critical_ordinal`. -/
def StronglyCriticalOrdinal (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) : Prop :=
  0 < β ∧ Complete β ∧ CriticalOrdinal f β β

/-! ## Fixpoints of normal functions -/

/-- Rocq: `VeblenCon.fixOrd_continuous`. -/
theorem fixOrd_continuous (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (hcomp : ∀ x, Complete x → Complete (f x)) (hcont : ScottContinuous f) :
    ScottContinuous (fixOrd f) := fun A g a₀ hd hg => by
  refine sup_least fun ⟨i⟩ => le_trans ?_ (sup_monotone fun a =>
    sup_le (fun n : ULift.{u} Nat => iterF f (g a) n.down) ⟨i⟩)
  show iterF f (sup g) i ≤ sup fun a => iterF f (g a) i
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    refine le_trans (hmono _ _ ih) (hcont A _ a₀ (fun a₁ a₂ => ?_)
      (fun a => iterF_complete i (g a) (hg a) hcomp))
    obtain ⟨a', h₁, h₂⟩ := hd a₁ a₂
    exact ⟨a', iterF_monotone hmono i _ _ h₁, iterF_monotone hmono i _ _ h₂⟩

/-- Rocq: `VeblenCon.normal_prefixpoint`. -/
theorem normal_prefixpoint (hf : NormalFunction f) (base : Ordinal.{u}) (hb : Complete base) :
    f (fixOrd f base) ≤ fixOrd f base :=
  le_trans (hf.continuous (ULift.{u} Nat) _ ⟨0⟩
      (directed_iterF base (normal_inflationary hf) hf.monotone hf.complete hb)
      (fun n => iterF_complete n.down base hb hf.complete))
    (sup_least fun i => sup_le (fun n : ULift.{u} Nat => iterF f base n.down) ⟨i.down + 1⟩)

/-- Rocq: `VeblenCon.normal_fixpoint`. -/
theorem normal_fixpoint (hf : NormalFunction f) (base : Ordinal.{u}) (hb : Complete base) :
    fixOrd f base ≈ f (fixOrd f base) :=
  equiv_intro (normal_inflationary hf _ (normal_fix_complete base hb (normal_inflationary hf)
      hf.monotone hf.complete))
    (normal_prefixpoint hf base hb)

/-- Rocq: `VeblenCon.normal_fix_least`. -/
theorem normal_fix_least (hf : NormalFunction f) (base z : Ordinal.{u}) (_hz : Complete z)
    (h₁ : base ≤ z) (h₂ : f z ≤ z) : fixOrd f base ≤ z :=
  fixOrd_least hf.monotone base z h₁ h₂

/-- Rocq: `VeblenCon.normal_fix_le_mor`. -/
theorem normal_fix_le (hf : NormalFunction f) {x y : Ordinal.{u}} (h : x ≤ y) :
    fixOrd f x ≤ fixOrd f y :=
  fixOrd_monotone hf.monotone h

/-- Rocq: `VeblenCon.normal_fix_eq_mor`. -/
theorem normal_fix_congr (hf : NormalFunction f) {x y : Ordinal.{u}} (h : x ≈ y) :
    fixOrd f x ≈ fixOrd f y :=
  equiv_intro (normal_fix_le hf h.le) (normal_fix_le hf h.ge)

/-- The base of `enumFixpoints f x` is complete when `x` is. -/
theorem enumFixpoints_base_complete (hf : NormalFunction f) {x : Ordinal.{u}} (hx : Complete x) :
    Complete (mk x.Carrier fun b => enumFixpoints f (x b)) :=
  lim_complete
    (fun b => enumFixpoints_complete (normal_inflationary hf) hf.monotone hf.complete _
      (complete_subord hx b))
    (fun b₁ b₂ =>
      let ⟨b', h₁, h₂⟩ := complete_directed hx b₁ b₂
      ⟨b', enumFixpoints_monotone hf.monotone _ _ h₁, enumFixpoints_monotone hf.monotone _ _ h₂⟩)
    hx.elim.2.1

/-- Rocq: `VeblenCon.enum_are_fixpoints`. -/
theorem Con.enum_are_fixpoints (hf : NormalFunction f) (x : Ordinal.{u}) (hx : Complete x) :
    enumFixpoints f x ≈ f (enumFixpoints f x) := by
  rw [enumFixpoints_unfold]
  exact normal_fixpoint hf _ (enumFixpoints_base_complete hf hx)

/-- Rocq: `VeblenCon.enum_fixpoints_zero`. -/
theorem Con.enum_fixpoints_zero (hf : NormalFunction f) : enumFixpoints f 0 ≈ fixOrd f 0 :=
  enumFixpoints_zero hf.monotone

/-- Rocq: `VeblenCon.enum_fixpoints_cont`. -/
theorem Con.enum_fixpoints_cont (hf : NormalFunction f) : ScottContinuous (enumFixpoints f) :=
  fun A g a₀ hd hg => by
    have hdir : Directed A fun a => enumFixpoints f (g a) := fun a₁ a₂ =>
      let ⟨a', h₁, h₂⟩ := hd a₁ a₂
      ⟨a', enumFixpoints_monotone hf.monotone _ _ h₁, enumFixpoints_monotone hf.monotone _ _ h₂⟩
    have hcomp : ∀ a, Complete (enumFixpoints f (g a)) := fun a =>
      enumFixpoints_complete (normal_inflationary hf) hf.monotone hf.complete _ (hg a)
    rw [enumFixpoints_unfold f (sup g)]
    refine normal_fix_least hf _ _ (sup_complete hcomp hdir (.inl ⟨a₀, lt_of_lt_of_le (hf.nonzero _)
      (Con.enum_are_fixpoints hf (g a₀) (hg a₀)).ge⟩)) (le_intro fun p => ?_)
      (le_trans (hf.continuous A _ a₀ hdir hcomp)
        (sup_monotone fun a => (Con.enum_are_fixpoints hf (g a) (hg a)).ge))
    exact lt_of_lt_of_le (enumFixpoints_increasing hf.monotone (index_lt (g p.1) p.2))
      (sup_le (fun a => enumFixpoints f (g a)) p.1)

/-- Rocq: `VeblenCon.enum_fixpoints_normal`. -/
@[ord_hint]
theorem enum_fixpoints_normal (hf : NormalFunction f) : NormalFunction (enumFixpoints f) where
  monotone := enumFixpoints_monotone hf.monotone
  increasing _ _ _ h := enumFixpoints_increasing hf.monotone h
  continuous := Con.enum_fixpoints_cont hf
  complete := enumFixpoints_complete (normal_inflationary hf) hf.monotone hf.complete
  nonzero x := by
    rw [enumFixpoints_unfold]
    exact lt_of_lt_of_le (hf.nonzero _)
      (sup_le (fun n : ULift.{u} Nat => iterF f (mk x.Carrier fun b => enumFixpoints f (x b)) n.down) ⟨1⟩)

/-- Rocq: `VeblenCon.enum_least`. -/
theorem enum_least (hf : NormalFunction f) (x z : Ordinal.{u}) (hz : Complete z) (hfz : f z ≤ z)
    (h : ∀ x', x' < x → enumFixpoints f x' < z) : enumFixpoints f x ≤ z := by
  rw [enumFixpoints_unfold]
  exact normal_fix_least hf _ z hz (le_intro fun a => h _ (index_lt x a)) hfz

/-- Rocq: `VeblenCon.enum_least'`. -/
theorem enum_least' (hf : NormalFunction f) (x z : Ordinal.{u}) (hx : Complete x) (hz : Complete z)
    (hfz : f z ≤ z) (h : ∀ x', Complete x' → x' < x → enumFixpoints f x' < z) :
    enumFixpoints f x ≤ z := by
  rw [enumFixpoints_unfold]
  exact normal_fix_least hf _ z hz
    (le_intro fun a => h _ (complete_subord hx a) (index_lt x a)) hfz

/-- Rocq: `VeblenCon.enum_fixpoints_func_mono`. -/
theorem Con.enum_fixpoints_func_mono {f g : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f)
    (hg : NormalFunction g) (hfg : ∀ x, Complete x → f x ≤ g x) :
    ∀ x : Ordinal.{u}, Complete x → enumFixpoints f x ≤ enumFixpoints g x
  | mk A q, hx => by
    rw [enumFixpoints_unfold f, enumFixpoints_unfold g]
    have hbase := enumFixpoints_base_complete hg hx
    refine le_trans (fixOrd_monotone hf.monotone (le_intro fun a =>
        lt_intro (show (mk A fun a => enumFixpoints g (q a)).Carrier from a)
          (Con.enum_fixpoints_func_mono hf hg hfg (q a) (complete_subord hx a))))
      (sup_monotone fun ⟨i⟩ => ?_)
    show iterF f (mk A fun a => enumFixpoints g (q a)) i ≤ iterF g (mk A fun a => enumFixpoints g (q a)) i
    induction i with
    | zero => exact le_refl _
    | succ i ih =>
      exact le_trans (hf.monotone _ _ ih) (hfg _ (iterF_complete i _ hbase hg.complete))

/-- Rocq: `VeblenCon.enum_fixpoints_func_mono'`. -/
theorem enum_fixpoints_func_mono' {f g : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f)
    (hg : NormalFunction g) (h : ∀ x, Complete x → fixOrd f x ≤ fixOrd g x) :
    ∀ x : Ordinal.{u}, Complete x → enumFixpoints f x ≤ enumFixpoints g x
  | mk A q, hx => by
    rw [enumFixpoints_unfold f, enumFixpoints_unfold g]
    exact le_trans (fixOrd_monotone hf.monotone (le_intro fun a =>
        lt_intro (show (mk A fun a => enumFixpoints g (q a)).Carrier from a)
          (enum_fixpoints_func_mono' hf hg h (q a) (complete_subord hx a))))
      (h _ (enumFixpoints_base_complete hg hx))

/-- Rocq: `VeblenCon.enum_fixpoint_le_mor`. -/
theorem enum_fixpoint_le (hf : NormalFunction f) {x y : Ordinal.{u}} (h : x ≤ y) :
    enumFixpoints f x ≤ enumFixpoints f y :=
  enumFixpoints_monotone hf.monotone x y h

/-- Rocq: `VeblenCon.enum_fixpoint_eq_mor`. -/
theorem enum_fixpoint_congr (hf : NormalFunction f) {x y : Ordinal.{u}} (h : x ≈ y) :
    enumFixpoints f x ≈ enumFixpoints f y :=
  equiv_intro (enum_fixpoint_le hf h.le) (enum_fixpoint_le hf h.ge)

/-- Rocq: `VeblenCon.ε_normal`. -/
@[ord_hint]
theorem ε_normal : NormalFunction (ε : Ordinal.{u} → Ordinal.{u}) :=
  enum_fixpoints_normal powOmega_normal

/-! ## The Veblen hierarchy over a normal function -/

section veblen

variable (hf : NormalFunction f)
include hf

omit hf in
/-- The base function is below every level of the hierarchy. -/
theorem f_le_veblen (β y : Ordinal.{u}) : f y ≤ veblen f β y := by
  rw [veblen_unroll]; exact lub_le1 _ _

/-- Rocq: `VeblenCon.veblen_nonzero`. -/
theorem veblen_nonzero (β y : Ordinal.{u}) : 0 < veblen f β y :=
  lt_of_lt_of_le (hf.nonzero y) (f_le_veblen β y)

/-- Rocq: `VeblenCon.veblen_inflationary`. -/
theorem veblen_inflationary (β x : Ordinal.{u}) (hx : Complete x) : x ≤ veblen f β x :=
  le_trans (normal_inflationary hf x hx) (f_le_veblen β x)

/-- `f y` is below each fixpoint iteration used in unrolling `veblen f β y`. -/
theorem f_le_fixOrd_veblen {y : Ordinal.{u}} (hy : Complete y) (β γ : Ordinal.{u}) :
    f y ≤ fixOrd (veblen f γ) (lim fun z : y => veblen f β (y z)) :=
  le_trans (hf.monotone _ _ (le_intro fun z =>
      lt_intro (show (lim fun z : y => veblen f β (y z)).Carrier from z)
        (veblen_inflationary hf β (y z) (complete_subord hy z))))
    (le_trans (f_le_veblen γ _) (sup_le (fun n : ULift.{u} Nat =>
      iterF (veblen f γ) (lim fun z : y => veblen f β (y z)) n.down) ⟨1⟩))

/-- Rocq: `VeblenCon.veblen_complete`. -/
theorem veblen_complete (hfc : ∀ x, Complete x → Complete (f x)) (β : Ordinal.{u}) :
    Complete β → ∀ x : Ordinal.{u}, Complete x → Complete (veblen f β x) := by
  induction β using ltRec with
  | ind β ihβ =>
    intro hβ x
    induction x using ltRec with
    | ind x ihx =>
      intro hx
      have hL : Complete (lim fun z : x => veblen f β (x z)) :=
        lim_complete (fun z => ihx (x z) (index_lt x z) (complete_subord hx z))
          (fun z₁ z₂ =>
            let ⟨z', h₁, h₂⟩ := complete_directed hx z₁ z₂
            ⟨z', veblen_monotone hf.monotone β _ _ h₁, veblen_monotone hf.monotone β _ _ h₂⟩)
          hx.elim.2.1
      have hsup : Complete (sup fun i : β => fixOrd (veblen f (β i))
          (lim fun z : x => veblen f β (x z))) := by
        refine sup_complete (fun i => normal_fix_complete _ hL
            (fun z hz => veblen_inflationary hf (β i) z hz) (veblen_monotone hf.monotone (β i))
            (fun z hz => ihβ (β i) (index_lt β i) (complete_subord hβ i) z hz))
          (fun b₁ b₂ => ?_) ?_
        · obtain ⟨b', h₁, h₂⟩ := complete_directed hβ b₁ b₂
          exact ⟨b',
            fixOrd_monotone_func (fun z => veblen_monotone_first hf.monotone _ _ z h₁)
              (veblen_monotone hf.monotone _) _,
            fixOrd_monotone_func (fun z => veblen_monotone_first hf.monotone _ _ z h₂)
              (veblen_monotone hf.monotone _) _⟩
        · match hβ.elim.2.1 with
          | .inl ⟨b⟩ => exact .inl ⟨b, lt_of_lt_of_le (hf.nonzero x) (f_le_fixOrd_veblen hf hx β _)⟩
          | .inr hn => exact .inr fun b => (hn ⟨b⟩).elim
      rw [veblen_unroll]
      match complete_zeroDec hβ with
      | .inl hβ₀ =>
        exact lub_complete1 (sup_least fun b => (le_subord hβ₀ b).elim fun e _ => PEmpty.elim e)
          (hfc x hx) hsup
      | .inr h₀ =>
        obtain ⟨b, _⟩ := lt_elim h₀
        exact lub_complete2 (le_trans (f_le_fixOrd_veblen hf hx β (β b))
          (sup_le (fun i : β => fixOrd (veblen f (β i)) (lim fun z : x => veblen f β (x z))) b))
          (hfc x hx) hsup

/-- Rocq: `VeblenCon.veblen_unroll_nonzero`. -/
theorem veblen_unroll_nonzero (β y : Ordinal.{u}) (hy : Complete y) (h₀ : 0 < β) :
    veblen f β y ≈
      boundedSup β fun α => fixOrd (veblen f α) (lim fun x : y => veblen f β (y x)) := by
  obtain ⟨b, _⟩ := lt_elim h₀
  rw [veblen_unroll]
  exact equiv_intro (lub_least (le_trans (f_le_fixOrd_veblen hf hy β (β b))
      (sup_le (fun i : β => fixOrd (veblen f (β i)) (lim fun x : y => veblen f β (y x))) b))
      (le_refl _))
    (lub_le2 _ _)

/-- Rocq: `VeblenCon.veblen_increasing0`. -/
theorem veblen_increasing0 (x y : Ordinal.{u}) (hy : Complete y) (h : x < y) :
    veblen f 0 x < veblen f 0 y := by
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (hf.increasing x y hy h) (f_le_veblen 0 y))
  rw [veblen_unroll]
  exact lub_least (le_refl _) (sup_least fun a => PEmpty.elim a)

/-- Rocq: `VeblenCon.veblen_increasing_nonzero`. -/
theorem veblen_increasing_nonzero (β : Ordinal.{u}) (h₀ : 0 < β) (x y : Ordinal.{u}) (h : x < y) :
    veblen f β x < veblen f β y := by
  obtain ⟨b, _⟩ := lt_elim h₀
  obtain ⟨q, hq⟩ := lt_elim h
  refine lt_of_le_of_lt (veblen_monotone hf.monotone β _ _ hq) ?_
  rw [veblen_unroll f β y]
  refine lt_of_lt_of_le (limit_lt (fun z : y => veblen f β (y z)) q)
    (le_trans (fixOrd_above (veblen f (β b)) _) (le_trans ?_ (lub_le2 _ _)))
  exact sup_le (fun i : β => fixOrd (veblen f (β i)) (lim fun z : y => veblen f β (y z))) b

/-- Rocq: `VeblenCon.veblen_increasing`. -/
theorem veblen_increasing (β : Ordinal.{u}) (hβ : Complete β) (x y : Ordinal.{u}) (hy : Complete y)
    (h : x < y) : veblen f β x < veblen f β y :=
  match complete_zeroDec hβ with
  | .inl hβ₀ =>
    lt_of_le_of_lt (veblen_monotone_first hf.monotone 0 β x hβ₀)
      (lt_of_lt_of_le (veblen_increasing0 hf x y hy h)
        (veblen_monotone_first hf.monotone β 0 y (zero_least β)))
  | .inr h₀ => veblen_increasing_nonzero hf β h₀ x y h

/-- Rocq: `VeblenCon.veblen_lt_lemma`. -/
theorem veblen_lt_lemma (β : Ordinal.{u}) (h₀ : 0 < β) (x q : Ordinal.{u}) (hx : Complete x)
    (h : q < veblen f β x) :
    ∃ a, a < β ∧ ∃ n, q < iterF (veblen f a) (lim fun i : x => veblen f β (x i)) n := by
  obtain ⟨b, hb⟩ := sup_lt (lt_of_lt_of_le h (veblen_unroll_nonzero hf β x hx h₀).le)
  obtain ⟨n, hn⟩ := sup_lt hb
  exact ⟨β b, index_lt β b, n.down, hn⟩

/-- `veblen f β` is normal once it is known to be continuous. -/
theorem veblen_normal_of_cont {β : Ordinal.{u}} (hβ : Complete β)
    (hc : ScottContinuous (veblen f β)) : NormalFunction (veblen f β) where
  monotone := veblen_monotone hf.monotone β
  increasing := veblen_increasing hf β hβ
  continuous := hc
  complete := veblen_complete hf hf.complete β hβ
  nonzero := veblen_nonzero hf β

/-- `lim (fun i => veblen f β (x i))` is complete. -/
theorem lim_veblen_complete {β x : Ordinal.{u}} (hβ : Complete β) (hx : Complete x) :
    Complete (lim fun i : x => veblen f β (x i)) :=
  lim_complete (fun i => veblen_complete hf hf.complete β hβ _ (complete_subord hx i))
    (fun i j =>
      let ⟨k, h₁, h₂⟩ := complete_directed hx i j
      ⟨k, veblen_monotone hf.monotone β _ _ h₁, veblen_monotone hf.monotone β _ _ h₂⟩)
    hx.elim.2.1

/-- Rocq: `VeblenCon.veblen_fixpoints_aux`. -/
theorem veblen_fixpoints_aux (β : Ordinal.{u}) (hβ : Complete β)
    (hcont : ∀ y, y < β → Complete y → ScottContinuous (veblen f y)) (α : Ordinal.{u}) :
    ∀ x, α < β → Complete α → Complete x → veblen f α (veblen f β x) ≤ veblen f β x := by
  induction α using ltRec with
  | ind α ihα =>
    intro x hαβ hα hx
    have h₀ : 0 < β := lt_of_le_of_lt (zero_least α) hαβ
    have hL := lim_veblen_complete hf hβ hx
    have hV := veblen_unroll_nonzero hf β x hx h₀
    have hnorm : ∀ b : β.Carrier, NormalFunction (veblen f (β b)) := fun b =>
      veblen_normal_of_cont hf (complete_subord hβ b) (hcont _ (index_lt β b) (complete_subord hβ b))
    rw [veblen_unroll f α]
    refine lub_least ?_ (sup_least fun y => ?_)
    · -- `f` of the fixpoint is below it, by continuity of `f`.
      obtain ⟨b₀, _⟩ := lt_elim h₀
      refine le_trans (hf.monotone _ _ hV.le) (le_trans (hf.continuous β.Carrier _ b₀ ?_ ?_)
        (le_trans (sup_monotone fun b => le_trans (f_le_veblen (β b) _)
          (normal_prefixpoint (hnorm b) _ hL)) hV.ge))
      · intro b₁ b₂
        obtain ⟨b', h₁, h₂⟩ := complete_directed hβ b₁ b₂
        exact ⟨b',
          fixOrd_monotone_func (fun z => veblen_monotone_first hf.monotone _ _ z h₁)
            (veblen_monotone hf.monotone _) _,
          fixOrd_monotone_func (fun z => veblen_monotone_first hf.monotone _ _ z h₂)
            (veblen_monotone hf.monotone _) _⟩
      · exact fun b => normal_fix_complete _ hL (normal_inflationary (hnorm b))
          (hnorm b).monotone (hnorm b).complete
    · -- Each iteration is bounded, by induction on `α`.
      refine fixOrd_least (veblen_monotone hf.monotone (α y)) _ _ (le_intro fun z => ?_)
        (ihα (α y) (index_lt α y) x (lt_trans (index_lt α y) hαβ) (complete_subord hα y) hx)
      obtain ⟨a', ha', n, hn⟩ := veblen_lt_lemma hf β h₀ x _ hx (index_lt (veblen f β x) z)
      obtain ⟨b₁, hb₁⟩ := lt_elim hαβ
      obtain ⟨b₂, hb₂⟩ := lt_elim ha'
      obtain ⟨w, hw₁, hw₂⟩ := complete_directed hβ b₁ b₂
      have hiter : veblen f β x z < iterF (veblen f (β w)) (lim fun i : x => veblen f β (x i)) n :=
        lt_of_lt_of_le hn (iterF_monotone_func
          (fun q => veblen_monotone_first hf.monotone _ _ q (le_trans hb₂ hw₂))
          (veblen_monotone hf.monotone _) n _)
      calc veblen f α (veblen f β x z)
          < veblen f α (iterF (veblen f (β w)) (lim fun i : x => veblen f β (x i)) n) :=
            veblen_increasing_nonzero hf α (lt_intro y (zero_least _)) _ _ hiter
        _ ≤ iterF (veblen f (β w)) (lim fun i : x => veblen f β (x i)) (n + 1) :=
            veblen_monotone_first hf.monotone _ _ _ (le_trans hb₁ hw₁)
        _ ≤ fixOrd (veblen f (β w)) (lim fun i : x => veblen f β (x i)) :=
            sup_le (fun m : ULift.{u} Nat =>
              iterF (veblen f (β w)) (lim fun i : x => veblen f β (x i)) m.down) ⟨n + 1⟩
        _ ≤ veblen f β x := le_trans (sup_le (fun b : β =>
              fixOrd (veblen f (β b)) (lim fun i : x => veblen f β (x i))) w) hV.ge

/-- Rocq: `VeblenCon.veblen_continuous`. -/
theorem veblen_continuous (β : Ordinal.{u}) : Complete β → ScottContinuous (veblen f β) := by
  induction β using ltRec with
  | ind β ih =>
    intro hc X h x₀ hd hh
    have hdir : Directed X fun i => veblen f β (h i) := fun i j =>
      let ⟨k, h₁, h₂⟩ := hd i j
      ⟨k, veblen_monotone hf.monotone β _ _ h₁, veblen_monotone hf.monotone β _ _ h₂⟩
    have hcomp : ∀ i, Complete (veblen f β (h i)) := fun i =>
      veblen_complete hf hf.complete β hc _ (hh i)
    rw [veblen_unroll f β (sup h)]
    refine lub_least (le_trans (hf.continuous X h x₀ hd hh)
      (sup_monotone fun i => f_le_veblen β (h i))) (sup_least fun a => ?_)
    refine normal_fix_least
      (veblen_normal_of_cont hf (complete_subord hc a) (ih (β a) (index_lt β a) (complete_subord hc a)))
      _ _ (sup_complete hcomp hdir (.inl ⟨x₀, veblen_nonzero hf β _⟩)) (le_intro fun p => ?_) ?_
    · exact lt_of_lt_of_le (veblen_increasing_nonzero hf β (lt_intro a (zero_least _)) _ _
        (index_lt (h p.1) p.2)) (sup_le (fun i => veblen f β (h i)) p.1)
    · exact le_trans (ih (β a) (index_lt β a) (complete_subord hc a) X _ x₀ hdir hcomp)
        (sup_monotone fun i => veblen_fixpoints_aux hf β hc (fun y hy hyc => ih y hy hyc) (β a)
          (h i) (index_lt β a) (complete_subord hc a) (hh i))

/-- Rocq: `VeblenCon.veblen_fixpoints`. -/
theorem veblen_fixpoints (α β x : Ordinal.{u}) (hα : Complete α) (hβ : Complete β)
    (hx : Complete x) (h : α < β) : veblen f α (veblen f β x) ≈ veblen f β x :=
  equiv_intro
    (veblen_fixpoints_aux hf β hβ (fun y _ hy => veblen_continuous hf y hy) α x h hα hx)
    (veblen_inflationary hf α _ (veblen_complete hf hf.complete β hβ x hx))

/-- Rocq: `VeblenCon.veblen_continuous_first`. -/
theorem veblen_continuous_first : StronglyContinuous fun β => veblen f β 0 := fun A g a => by
  show veblen f (sup g) 0 ≤ sup fun i => veblen f (g i) 0
  rw [veblen_unroll]
  refine lub_least (le_trans (f_le_veblen (g a) 0) (sup_le (fun i => veblen f (g i) 0) a))
    (sup_least fun p => ?_)
  refine le_trans ?_ (sup_le (fun i => veblen f (g i) 0) p.1)
  rw [veblen_unroll f (g p.1)]
  refine le_trans ?_ (le_trans (sup_le (fun α : g p.1 => fixOrd (veblen f (g p.1 α))
    (lim fun x : (0 : Ordinal.{u}).Carrier => veblen f (g p.1) ((0 : Ordinal.{u}) x))) p.2) (lub_le2 _ _))
  exact fixOrd_monotone (veblen_monotone hf.monotone _) (le_intro fun a => PEmpty.elim a)

/-- Rocq: `VeblenCon.veblen_normal`. -/
@[ord_hint]
theorem veblen_normal (β : Ordinal.{u}) (hβ : Complete β) : NormalFunction (veblen f β) :=
  veblen_normal_of_cont hf hβ (veblen_continuous hf β hβ)

/-- Rocq: `VeblenCon.veblen_increasing_first`. -/
theorem veblen_increasing_first (a β : Ordinal.{u}) (hβ : Complete β) (h : a < β) :
    veblen f a 0 < veblen f β 0 := by
  obtain ⟨b, hb⟩ := lt_elim h
  have hL0 : Complete (lim fun z : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) z)) :=
    lim_complete (fun z => PEmpty.elim z) (fun z => PEmpty.elim z) (.inr fun ⟨z⟩ => PEmpty.elim z)
  refine lt_of_le_of_lt (veblen_monotone_first hf.monotone _ _ 0 hb) ?_
  refine lt_of_lt_of_le (veblen_increasing hf _ (complete_subord hβ b) _ _
    (veblen_complete hf hf.complete _ (complete_subord hβ b) _ hL0) (veblen_nonzero hf _ _)) ?_
  rw [veblen_unroll f β]
  refine le_trans ?_ (lub_le2 _ _)
  refine le_trans ?_ (sup_le (fun i : β => fixOrd (veblen f (β i))
    (lim fun z : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) z))) b)
  exact sup_le (fun n : ULift.{u} Nat => iterF (veblen f (β b))
    (lim fun z : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) z)) n.down) ⟨2⟩

/-- Rocq: `VeblenCon.veblen_first_normal`. -/
@[ord_hint]
theorem veblen_first_normal : NormalFunction fun β => veblen f β 0 where
  monotone x y h := veblen_monotone_first hf.monotone y x 0 h
  increasing x y hy h := veblen_increasing_first hf x y hy h
  continuous A g a₀ _ _ := veblen_continuous_first hf A g a₀
  complete x hx := veblen_complete hf hf.complete x hx 0 zero_complete
  nonzero x := veblen_nonzero hf x 0

omit hf in
/-- Rocq: `VeblenCon.veblen_zero`. -/
theorem veblen_zero (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) : veblen f 0 x ≈ f x := by
  rw [veblen_unroll]
  exact equiv_intro (lub_least (le_refl _) (sup_least fun a => PEmpty.elim a)) (lub_le1 _ _)

/-- Rocq: `VeblenCon.veblen_succ`. -/
theorem veblen_succ (a : Ordinal.{u}) : ∀ x : Ordinal.{u}, Complete a →
    veblen f (succ a) x ≈ enumFixpoints (veblen f a) x
  | mk X g, ha => by
    have hm := veblen_monotone hf.monotone a
    rw [veblen_unroll, enumFixpoints_unfold]
    refine equiv_intro (lub_least ?_ (sup_least fun _ => fixOrd_monotone hm (le_intro fun z =>
        lt_intro (show (mk X fun z => enumFixpoints (veblen f a) (g z)).Carrier from z)
          (veblen_succ a (g z) ha).le))) ?_
    · refine le_trans (le_trans (hf.monotone _ _ (le_intro fun z =>
          lt_intro (show (mk X fun z => enumFixpoints (veblen f a) (g z)).Carrier from z)
            (increasing_inflationary (fun _ _ h => enumFixpoints_increasing hm h) (g z))))
        (f_le_veblen a _)) ?_
      exact sup_le (fun n : ULift.{u} Nat =>
        iterF (veblen f a) (mk X fun z => enumFixpoints (veblen f a) (g z)) n.down) ⟨1⟩
    · refine le_trans (fixOrd_monotone hm (le_intro fun z =>
        lt_intro (show (lim fun z : (mk X g).Carrier => veblen f (succ a) (mk X g z)).Carrier from z)
          (veblen_succ a (g z) ha).ge)) (le_trans ?_ (lub_le2 _ _))
      exact sup_le (fun i : (succ a).Carrier => fixOrd (veblen f (succ a i))
        (lim fun z : (mk X g).Carrier => veblen f (succ a) (mk X g z))) PUnit.unit

/-- An iteration bound used for limit levels: if `α < α'` (both complete,
indices of `β`), then `fixOrd (veblen f α) base ≤ veblen f α' y` whenever
`base ≤ veblen f α' y`. -/
private theorem fixOrd_le_veblen_of_lt {α α' y base : Ordinal.{u}} (hα : Complete α)
    (hα' : Complete α') (hy : Complete y) (hlt : α < α') (hbase : base ≤ veblen f α' y) :
    fixOrd (veblen f α) base ≤ veblen f α' y :=
  fixOrd_least (veblen_monotone hf.monotone α) _ _ hbase
    (veblen_fixpoints hf α α' y hα hα' hy hlt).le

/-- Rocq: `VeblenCon.veblen_limit_zero`. -/
theorem veblen_limit_zero (β : Ordinal.{u}) (hl : IsLimit β) (hβ : Complete β) :
    veblen f β 0 ≈ boundedSup β fun a => veblen f a 0 := by
  obtain ⟨⟨b₀⟩, hasc⟩ := hl
  rw [veblen_unroll]
  refine equiv_intro (lub_least ?_ (sup_least fun b => ?_)) (sup_least fun b => ?_)
  · exact le_trans (le_trans (veblen_zero f 0).ge (veblen_monotone_first hf.monotone _ 0 0
      (zero_least _))) (sup_le (fun i : β => veblen f (β i) 0) b₀)
  · obtain ⟨b', hb'⟩ := hasc b
    exact le_trans (fixOrd_le_veblen_of_lt hf (complete_subord hβ b) (complete_subord hβ b')
      zero_complete hb' (le_intro fun a => PEmpty.elim a)) (sup_le (fun i : β => veblen f (β i) 0) b')
  · refine le_trans ?_ (lub_le2 _ _)
    refine le_trans ?_ (sup_le (fun i : β => fixOrd (veblen f (β i))
      (lim fun x : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) x))) b)
    exact le_trans (veblen_monotone hf.monotone _ _ _ (zero_least _))
      (sup_le (fun n : ULift.{u} Nat => iterF (veblen f (β b))
        (lim fun x : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) x)) n.down) ⟨1⟩)

/-- Rocq: `VeblenCon.veblen_limit_succ`. -/
theorem veblen_limit_succ (β x : Ordinal.{u}) (hl : IsLimit β) (hβ : Complete β) (hx : Complete x) :
    veblen f β (succ x) ≈ boundedSup β fun a => veblen f a (succ (veblen f β x)) := by
  obtain ⟨⟨b₀⟩, hasc⟩ := hl
  have hS : Complete (succ (veblen f β x)) := succ_complete (veblen_complete hf hf.complete β hβ x hx)
  rw [veblen_unroll]
  refine equiv_intro (lub_least ?_ (sup_least fun b => ?_)) (sup_least fun b => ?_)
  · refine le_trans (le_trans (hf.monotone _ _ (succ_monotone (veblen_inflationary hf β x hx)))
      (f_le_veblen (β b₀) _)) ?_
    exact sup_le (fun i : β => veblen f (β i) (succ (veblen f β x))) b₀
  · obtain ⟨b', hb'⟩ := hasc b
    exact le_trans (fixOrd_le_veblen_of_lt hf (complete_subord hβ b) (complete_subord hβ b') hS hb'
      (veblen_inflationary hf _ _ hS)) (sup_le (fun i : β => veblen f (β i) (succ (veblen f β x))) b')
  · refine le_trans ?_ (lub_le2 _ _)
    refine le_trans ?_ (sup_le (fun i : β => fixOrd (veblen f (β i))
      (lim fun z : (succ x).Carrier => veblen f β (succ x z))) b)
    exact sup_le (fun n : ULift.{u} Nat => iterF (veblen f (β b))
      (lim fun z : (succ x).Carrier => veblen f β (succ x z)) n.down) ⟨1⟩

/-- Rocq: `VeblenCon.veblen_limit_limit`. -/
theorem veblen_limit_limit (β x : Ordinal.{u}) (hlβ : IsLimit β) (hlx : IsLimit x)
    (hβ : Complete β) (hx : Complete x) :
    veblen f β x ≈ boundedSup β fun a => veblen f a (boundedSup x fun y => veblen f β y) := by
  obtain ⟨⟨b₀⟩, hascβ⟩ := hlβ
  obtain ⟨⟨z₀⟩, hascx⟩ := hlx
  have hβ₀ : 0 < β := lt_intro b₀ (zero_least _)
  have hS : Complete (boundedSup x fun y => veblen f β y) :=
    sup_complete (fun z => veblen_complete hf hf.complete β hβ _ (complete_subord hx z))
      (fun i j =>
        let ⟨k, h₁, h₂⟩ := complete_directed hx i j
        ⟨k, veblen_monotone hf.monotone β _ _ h₁, veblen_monotone hf.monotone β _ _ h₂⟩)
      (.inl ⟨z₀, veblen_nonzero hf β _⟩)
  have hLS : (lim fun z : x => veblen f β (x z)) ≤ boundedSup x fun y => veblen f β y :=
    le_intro fun z =>
      let ⟨z', hz'⟩ := hascx z
      lt_of_lt_of_le (veblen_increasing_nonzero hf β hβ₀ _ _ hz')
        (sup_le (fun i : x => veblen f β (x i)) z')
  have hSL : (boundedSup x fun y => veblen f β y) ≤ lim fun z : x => veblen f β (x z) :=
    sup_least fun z => le_of_lt (limit_lt (fun z : x => veblen f β (x z)) z)
  rw [veblen_unroll]
  refine equiv_intro (lub_least ?_ (sup_least fun b => ?_)) (sup_least fun b => ?_)
  · refine le_trans (le_trans (hf.monotone _ _ (le_intro fun z => ?_)) (f_le_veblen (β b₀) _))
      (sup_le (fun i : β => veblen f (β i) (boundedSup x fun y => veblen f β y)) b₀)
    obtain ⟨z', hz'⟩ := hascx z
    exact lt_of_lt_of_le hz' (le_trans (veblen_inflationary hf β _ (complete_subord hx z'))
      (sup_le (fun i : x => veblen f β (x i)) z'))
  · obtain ⟨b', hb'⟩ := hascβ b
    exact le_trans (fixOrd_le_veblen_of_lt hf (complete_subord hβ b) (complete_subord hβ b') hS hb'
      (le_trans hLS (veblen_inflationary hf _ _ hS)))
      (sup_le (fun i : β => veblen f (β i) (boundedSup x fun y => veblen f β y)) b')
  · refine le_trans ?_ (lub_le2 _ _)
    refine le_trans ?_ (sup_le (fun i : β => fixOrd (veblen f (β i))
      (lim fun z : x => veblen f β (x z))) b)
    exact le_trans (veblen_monotone hf.monotone _ _ _ hSL)
      (sup_le (fun n : ULift.{u} Nat => iterF (veblen f (β b))
        (lim fun z : x => veblen f β (x z)) n.down) ⟨1⟩)

/-- For `β > 0`, `veblen f β` enumerates the `β`-critical ordinals.
Rocq: `VeblenCon.veblen_enumerates_critical`. -/
theorem veblen_enumerates_critical (β : Ordinal.{u}) (h₀ : 0 < β) (hc : Complete β) :
    Con.Enumerates (veblen f β) (CriticalOrdinal f β) where
  included x hx α hα hαβ := equiv_symm (veblen_fixpoints hf α β x hα hc hx hαβ)
  monotone := veblen_monotone hf.monotone β
  increasing := veblen_increasing hf β hc
  least x z hx hz hz₁ hz₂ := by
    rw [veblen_unroll]
    refine lub_least ?_ (sup_least fun i => fixOrd_least (veblen_monotone hf.monotone _) _ z
      (le_intro fun a => hz₂ _ (index_lt x a))
      (hz₁ (β i) (complete_subord hc i) (index_lt β i)).ge)
    have hz0 := equiv_trans (hz₁ 0 zero_complete h₀) (veblen_zero f z)
    exact le_trans (hf.monotone _ _ (le_intro fun a => lt_of_le_of_lt
      (veblen_inflationary hf β (x a) (complete_subord hx a)) (hz₂ _ (index_lt x a)))) hz0.ge

/-- Rocq: `VeblenCon.strongly_critical_fixpoint`. -/
theorem strongly_critical_fixpoint (β : Ordinal.{u}) (hc : Complete β) :
    StronglyCriticalOrdinal f β ↔ veblen f β 0 ≈ β := by
  refine ⟨fun ⟨h₀, _, h⟩ => equiv_intro ?_ (normal_inflationary (veblen_first_normal hf) β hc),
    fun h => ⟨lt_of_lt_of_le (veblen_nonzero hf β 0) h.le, hc, fun α hα hαβ => ?_⟩⟩
  · rw [veblen_unroll]
    refine lub_least ?_ (sup_least fun a => fixOrd_least (veblen_monotone hf.monotone _) _ β
      (le_intro fun z => PEmpty.elim z) (h (β a) (complete_subord hc a) (index_lt β a)).ge)
    exact le_trans (hf.monotone _ _ (zero_least β))
      (equiv_trans (h 0 zero_complete h₀) (veblen_zero f β)).ge
  · refine equiv_trans (equiv_symm h) (equiv_trans (equiv_symm
      (veblen_fixpoints hf α β 0 hα hc zero_complete hαβ)) ?_)
    exact equiv_intro (veblen_monotone hf.monotone α _ _ h.le) (veblen_monotone hf.monotone α _ _ h.ge)

end veblen

/-- Rocq: `VeblenCon.enumerates_equiv_pred`. -/
theorem Con.enumerates_equiv_pred {P P' : Ordinal.{u} → Prop} (hn : NormalFunction f)
    (hp : ∀ x, Complete x → (P x ↔ P' x)) (hf : Con.Enumerates f P) : Con.Enumerates f P' where
  included x hx := (hp _ (hn.complete x hx)).1 (hf.included x hx)
  monotone := hf.monotone
  increasing := hf.increasing
  least x z hx hz hz' h := hf.least x z hx hz ((hp z hz).2 hz') h

/-- Rocq: `VeblenCon.enum_fixpoints_enumerates`. -/
theorem Con.enum_fixpoints_enumerates (_hinf : ∀ x, Complete x → x ≤ f x)
    (hmono : ∀ x y, x ≤ y → f x ≤ f y) (hf : NormalFunction f) :
    Con.Enumerates (enumFixpoints f) fun x => x ≈ f x where
  included := Con.enum_are_fixpoints hf
  monotone := enumFixpoints_monotone hmono
  increasing _ _ _ h := enumFixpoints_increasing hmono h
  least x z _ _ hz₁ hz₂ := by
    rw [enumFixpoints_unfold]
    exact fixOrd_least hmono _ z (le_intro fun a => hz₂ _ (index_lt x a)) hz₁.ge

/-! ## The Feferman–Schütte Γ function

Rocq: `VeblenCon.Γ` is the same definition as `VeblenDefs.Γ`.
-/

/-- Rocq: `VeblenCon.Γ_fixpoints`. -/
theorem Γ_fixpoints (a : Ordinal.{u}) (ha : Complete a) : Γ a ≈ veblen powOmega (Γ a) 0 :=
  Con.enum_are_fixpoints (veblen_first_normal powOmega_normal) a ha

/-- Rocq: `VeblenCon.Γ_normal`. -/
theorem Γ_normal : NormalFunction (Γ : Ordinal.{u} → Ordinal.{u}) :=
  enum_fixpoints_normal (veblen_first_normal powOmega_normal)

/-- Γ₀ is the least fixpoint of `β ↦ veblen powOmega β 0`.
Rocq: `VeblenCon.Γ₀_least`. -/
theorem Γ₀_least (x : Ordinal.{u}) (h : veblen powOmega x 0 ≈ x) : Γ 0 ≤ x :=
  le_trans (Con.enum_fixpoints_zero (veblen_first_normal powOmega_normal)).le
    (fixOrd_least (veblen_first_normal powOmega_normal).monotone 0 x (zero_least x) h.le)

/-- Γ enumerates the strongly critical ordinals of `powOmega`.
Rocq: `VeblenCon.Γ_enumerates`. -/
theorem Γ_enumerates : Con.Enumerates (Γ : Ordinal.{u} → Ordinal.{u})
    (StronglyCriticalOrdinal powOmega) :=
  Con.enumerates_equiv_pred Γ_normal
    (fun x hx => ⟨fun h => (strongly_critical_fixpoint powOmega_normal x hx).2 (equiv_symm h),
      fun h => equiv_symm ((strongly_critical_fixpoint powOmega_normal x hx).1 h)⟩)
    (Con.enum_fixpoints_enumerates (normal_inflationary (veblen_first_normal powOmega_normal))
      (veblen_first_normal powOmega_normal).monotone (veblen_first_normal powOmega_normal))

end Ordinal

end ConstructiveOrdinals
