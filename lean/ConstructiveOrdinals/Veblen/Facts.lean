import ConstructiveOrdinals.Veblen.Constructive
import ConstructiveOrdinals.Reflection

/-!
# Further facts about Veblen functions

Port of `Ordinal/VeblenFacts.v`: the Veblen hierarchy over `1 + x`
(`veblen_onePlus`), comparison lemmas for Veblen terms used by the notation
systems, relations between the hierarchies over `f`, `f ∘ (1 + ·)` and the
fixpoints of `f`, and (classically) decompositions of fixpoints.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- Rocq: `VeblenFacts.veblen_onePlus_complete`. -/
theorem veblen_onePlus_complete {a x : Ordinal.{u}} (ha : Complete a) (hx : Complete x) :
    Complete (veblen (fun y => 1 + y) a x) :=
  veblen_complete onePlus_normal (fun _ h => onePlus_complete h) a ha x hx

/-- Rocq: `VeblenFacts.onePlus_veblen`. -/
theorem onePlus_veblen (hf : NormalFunction f) {x y : Ordinal.{u}} (h₀ : 0 < x) (hx : Complete x)
    (hy : Complete y) : 1 + veblen f x y ≈ veblen f x y :=
  equiv_intro
    (le_trans (onePlus_least_normal hf _ (veblen_complete hf hf.complete x hx y hy))
      (le_trans (veblen_zero f _).ge (veblen_fixpoints hf 0 x y zero_complete hx hy h₀).le))
    (le_add_left 1 _)

/-- Rocq: `VeblenFacts.finite_veblen`. -/
theorem finite_veblen (hf : NormalFunction f) {x y : Ordinal.{u}} (h₀ : 0 < x) (hx : Complete x)
    (hy : Complete y) : ∀ n : Nat, ofNat n + veblen f x y ≈ veblen f x y
  | 0 => zero_add _
  | n + 1 =>
    equiv_trans (add_congr (ofNat_add n 1) (equiv_refl _))
      (equiv_trans (equiv_symm (add_assoc _ _ _))
        (equiv_trans (add_congr (equiv_refl 1) (finite_veblen hf h₀ hx hy n))
          (onePlus_veblen hf h₀ hx hy)))

/-- Rocq: `VeblenFacts.finite_veblen_lt`. -/
theorem finite_veblen_lt (hf : NormalFunction f) {x y : Ordinal.{u}} (h₀ : 0 < x) (hx : Complete x)
    (hy : Complete y) (n : Nat) : ofNat n < veblen f x y :=
  lt_of_lt_of_le (succ_lt _) (le_trans (succ_le_add_one _)
    (le_trans (add_le_add (le_refl _) (succ_least (veblen_nonzero hf x y)))
      (finite_veblen hf h₀ hx hy n).le))

/-- Rocq: `VeblenFacts.finite_veblen_le`. -/
theorem finite_veblen_le (hf : NormalFunction f) {x y : Ordinal.{u}} (h₀ : 0 < x) (hx : Complete x)
    (hy : Complete y) (n : Nat) : ofNat n ≤ veblen f x y :=
  le_trans (le_add_right _ _) (finite_veblen hf h₀ hx hy n).le

/-- `b * n + b ≤ b + b * n` for finite `n`. -/
private theorem mul_ofNat_add_le (b : Ordinal.{u}) (n : Nat) : b * ofNat n + b ≤ b + b * ofNat n :=
  calc b * ofNat n + b ≤ b * ofNat (n + 1) := (mul_succ b _).ge
    _ ≤ b * (1 + ofNat n) := mul_le_mul_left b (ofNat_add n 1).le
    _ ≤ b * 1 + b * ofNat n := (mul_add b 1 _).le
    _ ≤ b + b * ofNat n := add_le_add (mul_one b).le (le_refl _)

/-- The Veblen hierarchy over `1 + x` is `ω ^ a + x`.
Rocq: `VeblenFacts.veblen_onePlus`. -/
theorem veblen_onePlus : ∀ a : Ordinal.{u}, Complete a → ∀ x : Ordinal.{u}, Complete x →
    veblen (fun y => 1 + y) a x ≈ ω ^ a + x
  | mk A g, ha, x, hx => by
    have hm : ∀ b, ∀ u v : Ordinal.{u}, u ≤ v → veblen (fun y => 1 + y) b u ≤ veblen (fun y => 1 + y) b v :=
      fun b => veblen_monotone onePlus_normal.monotone b
    have hωa : Complete (ω ^ mk A g) := pow_complete omega_gt0 omega_complete ha
    induction x using ltRec with
    | ind x ihx =>
      refine equiv_intro ?_ ?_
      · rw [veblen_unroll]
        refine lub_least (add_le_add (succ_least (pow_pos ω _)) (le_refl x)) (sup_least fun i => ?_)
        refine fixOrd_least (hm _) _ _ (le_intro fun z => ?_) ?_
        · exact lt_of_le_of_lt (ihx (x z) (index_lt x z) (complete_subord hx z)).le
            (add_lt_add_left _ (index_lt x z))
        · have hc : Complete (ω ^ mk A g + x) := add_complete hωa hx
          calc veblen (fun y => 1 + y) (g i) (ω ^ mk A g + x)
              ≤ ω ^ g i + (ω ^ mk A g + x) :=
                (veblen_onePlus (g i) (complete_subord ha i) _ hc).le
            _ ≤ ω ^ g i + ω ^ mk A g + x := (add_assoc _ _ _).le
            _ ≤ ω ^ mk A g + x :=
                add_le_add (pow_add_collapse ha (index_lt (mk A g) i)) (le_refl x)
      · rw [add_unfold]
        refine lub_least ?_ (sup_least fun z => succ_least ?_)
        · rw [pow_unfold]
          refine lub_least (succ_least (veblen_nonzero onePlus_normal _ _)) (sup_least fun i => ?_)
          rw [mul_unfold]
          refine sup_least fun ⟨n⟩ => ?_
          have hgi := complete_subord ha i
          have claim : ∀ n : Nat, ω ^ g i * ofNat n ≤
              iterF (veblen (fun y => 1 + y) (g i)) (lim fun z : x => veblen (fun y => 1 + y) (mk A g) (x z)) n := by
            intro n
            induction n with
            | zero => exact le_trans (mul_zero _).le (zero_least _)
            | succ n ih =>
              calc ω ^ g i * ofNat (n + 1) ≤ ω ^ g i * ofNat n + ω ^ g i := (mul_succ _ _).le
                _ ≤ ω ^ g i + ω ^ g i * ofNat n := mul_ofNat_add_le _ n
                _ ≤ veblen (fun y => 1 + y) (g i) (ω ^ g i * ofNat n) :=
                    (veblen_onePlus (g i) hgi _ (mul_complete
                      (pow_complete omega_gt0 omega_complete hgi) _ (ofNat_complete n))).ge
                _ ≤ _ := hm _ _ _ ih
          calc ω ^ g i * ofNat n + ω ^ g i ≤ ω ^ g i * ofNat (n + 1) := (mul_succ _ _).ge
            _ ≤ fixOrd (veblen (fun y => 1 + y) (g i))
                  (lim fun z : x => veblen (fun y => 1 + y) (mk A g) (x z)) :=
                le_trans (claim (n + 1)) (sup_le (fun m : ULift.{u} Nat =>
                  iterF (veblen (fun y => 1 + y) (g i))
                    (lim fun z : x => veblen (fun y => 1 + y) (mk A g) (x z)) m.down) ⟨n + 1⟩)
            _ ≤ veblen (fun y => 1 + y) (mk A g) x := by
                rw [veblen_unroll (fun y => 1 + y) (mk A g) x]
                exact le_trans (sup_le (fun i : (mk A g).Carrier =>
                  fixOrd (veblen (fun y => 1 + y) (mk A g i))
                    (lim fun z : x => veblen (fun y => 1 + y) (mk A g) (x z))) i) (lub_le2 _ _)
        · exact lt_of_le_of_lt (ihx (x z) (index_lt x z) (complete_subord hx z)).ge
            (veblen_increasing onePlus_normal _ ha _ _ hx (index_lt x z))

/-- Rocq: `VeblenFacts.veblen_fixpoint_zero`. -/
theorem veblen_fixpoint_zero (hf : NormalFunction f) {a x : Ordinal.{u}} (h₀ : 0 < a)
    (ha : Complete a) (hx : Complete x) : f (veblen f a x) ≤ veblen f a x :=
  le_trans (veblen_zero f _).ge (veblen_fixpoints hf 0 a x zero_complete ha hx h₀).le

/-- Rocq: `VeblenFacts.veblen_monotone_full`. -/
theorem veblen_monotone_full {f g : Ordinal.{u} → Ordinal.{u}} (hg : ∀ x y, x ≤ y → g x ≤ g y)
    (hfg : ∀ x, f x ≤ g x) (b : Ordinal.{u}) :
    ∀ (y a x : Ordinal.{u}), a ≤ b → x ≤ y → veblen f a x ≤ veblen g b y := by
  induction b using ltRec with
  | ind b ihb =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      intro a x hab hxy
      rw [veblen_unroll f a x, veblen_unroll g b y]
      refine lub_least (le_trans (le_trans (hfg x) (hg _ _ hxy)) (lub_le1 _ _))
        (sup_least fun ai => ?_)
      obtain ⟨bi, hbi⟩ := le_subord hab ai
      refine le_trans ?_ (le_trans (sup_le (fun i : b => fixOrd (veblen g (b i))
        (lim fun z : y => veblen g b (y z))) bi) (lub_le2 _ _))
      refine sup_monotone fun ⟨m⟩ => ?_
      show iterF (veblen f (a ai)) (lim fun z : x => veblen f a (x z)) m ≤
        iterF (veblen g (b bi)) (lim fun z : y => veblen g b (y z)) m
      induction m with
      | zero =>
        exact le_intro fun xi =>
          let ⟨yi, h⟩ := le_subord hxy xi
          lt_intro (show (lim fun z : y => veblen g b (y z)).Carrier from yi)
            (ihy (y yi) (index_lt y yi) a (x xi) hab h)
      | succ m ih => exact ihb (b bi) (index_lt b bi) _ _ _ hbi ih

/-- Rocq: `VeblenFacts.veblen_monotone_func`. -/
theorem veblen_monotone_func {f g : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f)
    (hg : NormalFunction g) (h : ∀ i, Complete i → f i ≤ g i) :
    ∀ a x : Ordinal.{u}, Complete a → Complete x → veblen f a x ≤ veblen g a x
  | mk A k, x, ha, hx => by
    induction x using ltRec with
    | ind x ihx =>
      rw [veblen_unroll f, veblen_unroll g]
      refine lub_least (le_trans (h x hx) (lub_le1 _ _)) (le_trans (sup_monotone fun i =>
        sup_monotone fun ⟨n⟩ => ?_) (lub_le2 _ _))
      have hki := complete_subord ha i
      show iterF (veblen f (k i)) (lim fun z : x => veblen f (mk A k) (x z)) n ≤
        iterF (veblen g (k i)) (lim fun z : x => veblen g (mk A k) (x z)) n
      induction n with
      | zero => exact lim_monotone fun z => ihx (x z) (index_lt x z) (complete_subord hx z)
      | succ n ih =>
        exact le_trans (veblen_monotone_func hf hg h (k i) _ hki
            (iterF_complete n _ (lim_veblen_complete hf ha hx)
              (fun z hz => veblen_complete hf hf.complete (k i) hki z hz)))
          (veblen_monotone hg.monotone (k i) _ _ ih)

/-- Rocq: `VeblenFacts.veblen_onePlus_le_mor`. -/
theorem veblen_onePlus_le {x y x₀ y₀ : Ordinal.{u}} (h : x ≤ y) (h₀ : x₀ ≤ y₀) :
    veblen (fun y => 1 + y) x x₀ ≤ veblen (fun y => 1 + y) y y₀ :=
  veblen_le (fun _ _ h => add_le_add (le_refl 1) h) h h₀

/-- Rocq: `VeblenFacts.veblen_onePlus_eq_mor`. -/
theorem veblen_onePlus_congr {x y x₀ y₀ : Ordinal.{u}} (h : x ≈ y) (h₀ : x₀ ≈ y₀) :
    veblen (fun y => 1 + y) x x₀ ≈ veblen (fun y => 1 + y) y y₀ :=
  veblen_congr (fun _ _ h => add_le_add (le_refl 1) h) h h₀

/-- Rocq: `VeblenFacts.veblen_expOmega_le_mor`. -/
theorem veblen_expOmega_le {x y x₀ y₀ : Ordinal.{u}} (h : x ≤ y) (h₀ : x₀ ≤ y₀) :
    veblen (fun y => ω ^ y) x x₀ ≤ veblen (fun y => ω ^ y) y y₀ :=
  veblen_le (fun _ _ h => pow_le_pow_right ω h) h h₀

/-- Rocq: `VeblenFacts.veblen_expOmega_eq_mor`. -/
theorem veblen_expOmega_congr {x y x₀ y₀ : Ordinal.{u}} (h : x ≈ y) (h₀ : x₀ ≈ y₀) :
    veblen (fun y => ω ^ y) x x₀ ≈ veblen (fun y => ω ^ y) y y₀ :=
  veblen_congr (fun _ _ h => pow_le_pow_right ω h) h h₀

/-- Rocq: `VeblenFacts.veblen_additively_closed`. -/
theorem veblen_additively_closed {a b : Ordinal.{u}} (ha : Complete a) (hb : Complete b) :
    AdditivelyClosed (veblen (fun y => ω ^ y) a b) :=
  match complete_zeroDec ha with
  | .inl ha₀ =>
    (powOmega_additively_closed hb).congr (equiv_intro
      (f_le_veblen a b)
      (le_trans (veblen_monotone_first powOmega_normal.monotone 0 a b ha₀) (veblen_zero _ b).le))
  | .inr h₀ =>
    have hV := veblen_complete powOmega_normal powOmega_normal.complete a ha b hb
    (powOmega_additively_closed hV).congr (equiv_trans (equiv_symm (veblen_zero _ _))
      (veblen_fixpoints powOmega_normal 0 a b zero_complete ha hb h₀))

/-- Rocq: `VeblenFacts.Γ_additively_closed`. -/
theorem Γ_additively_closed {a : Ordinal.{u}} (ha : Complete a) : AdditivelyClosed (Γ a) :=
  (veblen_additively_closed (Γ_normal.complete a ha) zero_complete).congr
    (equiv_symm (Γ_fixpoints a ha))

section normal

variable (hf : NormalFunction f)
include hf

/-- Rocq: `VeblenFacts.veblen_collapse`. -/
theorem veblen_collapse (a b c : Ordinal.{u}) (ha : Complete a) (_hb : Complete b)
    (hc : Complete c) (hac : a < c) (hbc : b ≤ c) (hcc : veblen f c 0 ≤ c) : veblen f a b ≤ c :=
  le_trans (veblen_monotone hf.monotone a _ _
      (le_trans hbc (normal_inflationary (veblen_first_normal hf) c hc)))
    (le_trans (veblen_fixpoints hf a c 0 ha hc zero_complete hac).le hcc)

/-- Rocq: `VeblenFacts.veblen_collapse'`. -/
theorem veblen_collapse' (a b c : Ordinal.{u}) (ha : Complete a) (_hb : Complete b)
    (hc : Complete c) (hac : a < c) (hbc : b < c) (hcc : veblen f c 0 ≤ c) : veblen f a b < c :=
  lt_of_lt_of_le (veblen_increasing hf a ha _ _ (veblen_complete hf hf.complete c hc 0 zero_complete)
      (lt_of_lt_of_le hbc (normal_inflationary (veblen_first_normal hf) c hc)))
    (le_trans (veblen_fixpoints hf a c 0 ha hc zero_complete hac).le hcc)

/-- Rocq: `VeblenFacts.veblen_subterm1`. -/
theorem veblen_subterm1 (a a' b : Ordinal.{u}) (ha : Complete a) (ha' : Complete a')
    (hb : Complete b) (h₀ : 0 < b) (h : a ≤ a') : a < veblen f a' b :=
  lt_of_le_of_lt (le_trans (normal_inflationary (veblen_first_normal hf) a ha)
      (veblen_monotone_first hf.monotone a' a 0 h))
    (veblen_increasing hf a' ha' 0 b hb h₀)

/-- Rocq: `VeblenFacts.veblen_shrink_lemma`. -/
theorem veblen_shrink_lemma (a b : Ordinal.{u}) (ha : Complete a) (hb : Complete b)
    (ha₀ : a < veblen f a 0) (hb₀ : b < veblen f b 0) :
    veblen f a b < veblen f (veblen f a b) 0 :=
  have hV := veblen_complete hf hf.complete a ha b hb
  lt_of_lt_of_le
    (veblen_increasing hf a ha _ _ (veblen_complete hf hf.complete _ hV 0 zero_complete)
      (lt_of_lt_of_le hb₀ (veblen_monotone_first hf.monotone _ _ 0
        (veblen_inflationary hf a b hb))))
    (veblen_fixpoints hf a _ 0 ha hV zero_complete
      (lt_of_lt_of_le ha₀ (veblen_monotone hf.monotone a _ _ (zero_least b)))).le

/-- Rocq: `VeblenFacts.veblen_subterm_zero`. -/
theorem veblen_subterm_zero (a b c : Ordinal.{u}) (ha : Complete a) (_hb : Complete b)
    (hc : Complete c) (hac : a < c) (hbc : b < veblen f c 0) : veblen f a b < veblen f c 0 :=
  lt_of_lt_of_le (veblen_increasing hf a ha _ _ (veblen_complete hf hf.complete c hc 0 zero_complete) hbc)
    (veblen_fixpoints hf a c 0 ha hc zero_complete hac).le

/-- Rocq: `VeblenFacts.veblen_subterm1_zero_nest`. -/
theorem veblen_subterm1_zero_nest (a b c : Ordinal.{u}) (ha : Complete a) (hb : Complete b)
    (hc : Complete c) (hac : a < c) (hbc : b < c) : veblen f a b < veblen f c 0 :=
  veblen_subterm_zero hf a b c ha hb hc hac
    (lt_of_lt_of_le hbc (normal_inflationary (veblen_first_normal hf) c hc))

/-- Rocq: `VeblenFacts.veblen_increasing'`. -/
theorem veblen_increasing' (a b c d : Ordinal.{u}) (ha : Complete a) (hd : Complete d)
    (hab : a ≤ b) (hcd : c < d) : veblen f a c < veblen f b d :=
  lt_of_lt_of_le (veblen_increasing hf a ha c d hd hcd) (veblen_monotone_first hf.monotone b a d hab)

end normal

/-- Rocq: `VeblenFacts.ordering_correct_normal`. -/
theorem ordering_correct_normal {x y : Ordinal.{u}} {o : Ordering} (hf : NormalFunction f)
    (hx : Complete x) (hy : Complete y) (h : OrderingCorrect o x y) : OrderingCorrect o (f x) (f y) :=
  match o, h with
  | .lt, h => hf.increasing x y hy h
  | .eq, h => equiv_intro (hf.monotone _ _ h.le) (hf.monotone _ _ h.ge)
  | .gt, h => hf.increasing y x hx h

/-- Comparing two Veblen terms reduces to comparing their components.
Rocq: `VeblenFacts.veblen_compare_correct`. -/
theorem veblen_compare_correct (hf : NormalFunction f) (oab oxy oxVby oVaxy : Ordering)
    (a b x y : Ordinal.{u}) (ha : Complete a) (hb : Complete b) (hx : Complete x)
    (hy : Complete y) (hoab : OrderingCorrect oab a b) (hoxy : OrderingCorrect oxy x y)
    (hoxVby : OrderingCorrect oxVby x (veblen f b y))
    (hoVaxy : OrderingCorrect oVaxy (veblen f a x) y) :
    OrderingCorrect (match oab with
      | .lt => oxVby
      | .eq => oxy
      | .gt => oVaxy) (veblen f a x) (veblen f b y) := by
  have hVb := veblen_complete hf hf.complete b hb y hy
  have hVa := veblen_complete hf hf.complete a ha x hx
  have hm := hf.monotone
  match oab, hoab with
  | .lt, hoab =>
    match oxVby, hoxVby with
    | .lt, h =>
      exact lt_of_lt_of_le (veblen_increasing hf a ha _ _ hVb h)
        (veblen_fixpoints hf a b y ha hb hy hoab).le
    | .eq, h =>
      exact equiv_trans (equiv_intro (veblen_monotone hm a _ _ h.le) (veblen_monotone hm a _ _ h.ge))
        (veblen_fixpoints hf a b y ha hb hy hoab)
    | .gt, h => exact lt_of_lt_of_le h (veblen_inflationary hf a x hx)
  | .eq, hoab =>
    match oxy, hoxy with
    | .lt, h =>
      exact lt_of_lt_of_le (veblen_increasing hf a ha x y hy h)
        (veblen_monotone_first hm b a y hoab.le)
    | .eq, h =>
      exact equiv_trans (equiv_intro (veblen_monotone hm a _ _ h.le) (veblen_monotone hm a _ _ h.ge))
        (equiv_intro (veblen_monotone_first hm b a y hoab.le) (veblen_monotone_first hm a b y hoab.ge))
    | .gt, h =>
      exact lt_of_le_of_lt (veblen_monotone_first hm a b y hoab.ge) (veblen_increasing hf a ha y x hx h)
  | .gt, hoab =>
    match oVaxy, hoVaxy with
    | .lt, h => exact lt_of_lt_of_le h (veblen_inflationary hf b y hy)
    | .eq, h =>
      exact equiv_symm (equiv_trans (equiv_intro (veblen_monotone hm b _ _ h.ge)
        (veblen_monotone hm b _ _ h.le)) (veblen_fixpoints hf b a x hb ha hx hoab))
    | .gt, h =>
      exact lt_of_lt_of_le (veblen_increasing hf b hb _ _ hVa h)
        (veblen_fixpoints hf b a x hb ha hx hoab).le

/-- Rocq: `VeblenFacts.compose_normal`. -/
theorem compose_normal {f g : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f)
    (hg : NormalFunction g) : NormalFunction fun x => f (g x) where
  monotone _ _ h := hf.monotone _ _ (hg.monotone _ _ h)
  increasing x y hy h := hf.increasing _ _ (hg.complete y hy) (hg.increasing x y hy h)
  continuous A h a hd hc :=
    le_trans (hf.monotone _ _ (hg.continuous A h a hd hc))
      (hf.continuous A (fun i => g (h i)) a
        (fun a₁ a₂ =>
          let ⟨a', h₁, h₂⟩ := hd a₁ a₂
          ⟨a', hg.monotone _ _ h₁, hg.monotone _ _ h₂⟩)
        (fun i => hg.complete _ (hc i)))
  complete x hx := hf.complete _ (hg.complete x hx)
  nonzero x := hf.nonzero (g x)

/-- Rocq: `VeblenFacts.veblen_first_onePlus_normal`. -/
@[ord_hint]
theorem veblen_first_onePlus_normal (hf : NormalFunction f) :
    NormalFunction fun i => veblen f (1 + i) 0 :=
  compose_normal (veblen_first_normal hf) onePlus_normal

/-- Rocq: `VeblenFacts.veblen_func_onePlus_lemma`. -/
theorem veblen_func_onePlus_lemma (hf : NormalFunction f) (a : Ordinal.{u}) :
    ∀ x b y : Ordinal.{u}, Complete a → Complete x → Complete b → Complete y → 0 < b →
      a ≤ b → x ≤ y → veblen (fun i => f (1 + i)) a x ≤ veblen f b y := by
  have hF : ∀ u v : Ordinal.{u}, u ≤ v → f (1 + u) ≤ f (1 + v) :=
    fun _ _ h => hf.monotone _ _ (add_le_add (le_refl 1) h)
  induction a using ltRec with
  | ind a iha =>
    intro x
    induction x using ltRec with
    | ind x ihx =>
      intro b y ha hx hb hy hb₀ hab hxy
      have hV := veblen_complete hf hf.complete b hb y hy
      have h1V : f (1 + veblen f b y) ≤ veblen f b y :=
        le_trans (hf.monotone _ _ (onePlus_veblen hf hb₀ hb hy).le) (veblen_fixpoint_zero hf hb₀ hb hy)
      rw [veblen_unroll (fun i => f (1 + i)) a x]
      refine lub_least (le_trans (hF _ _ (le_trans hxy (veblen_inflationary hf b y hy))) h1V)
        (sup_least fun i => fixOrd_least (veblen_monotone hF _) _ _ (le_intro fun z => ?_) ?_)
      · exact lt_of_le_of_lt (ihx (x z) (index_lt x z) b (x z) ha (complete_subord hx z) hb
          (complete_subord hx z) hb₀ hab (le_refl _))
          (veblen_increasing hf b hb _ _ hy (lt_of_lt_of_le (index_lt x z) hxy))
      · match complete_zeroDec (complete_subord ha i) with
        | .inl hi₀ =>
          exact le_trans (veblen_monotone_first hF 0 (a i) _ hi₀)
            (le_trans (veblen_zero _ _).le h1V)
        | .inr hi₀ =>
          have hai := complete_subord ha i
          exact le_trans (iha (a i) (index_lt a i) _ (a i) _ hai hV hai hV hi₀ (le_refl _) (le_refl _))
            (veblen_fixpoints hf (a i) b y hai hb hy (lt_of_lt_of_le (index_lt a i) hab)).le

/-- Rocq: `VeblenFacts.veblen_func_onePlus`. -/
theorem veblen_func_onePlus (hf : NormalFunction f) (a x : Ordinal.{u}) (ha : Complete a)
    (hx : Complete x) (h₀ : 0 < a) : veblen (fun i => f (1 + i)) a x ≈ veblen f a x :=
  equiv_intro (veblen_func_onePlus_lemma hf a x a x ha hx ha hx h₀ (le_refl a) (le_refl x))
    (veblen_monotone_func hf (compose_normal hf onePlus_normal)
      (fun i _ => hf.monotone _ _ (le_add_left 1 i)) a x ha hx)

/-- `a + x ≤ veblen f a x` for `a > 0`. -/
private theorem add_le_veblen (hf : NormalFunction f) {a : Ordinal.{u}} (_h₀ : 0 < a)
    (ha : Complete a) (x : Ordinal.{u}) : Complete x → a + x ≤ veblen f a x := by
  induction x using ltRec with
  | ind x ih =>
    intro hx
    rw [add_unfold]
    exact lub_least (le_trans (normal_inflationary (veblen_first_normal hf) a ha)
      (veblen_monotone hf.monotone a 0 x (zero_least x))) (sup_least fun i => succ_least
        (lt_of_le_of_lt (ih (x i) (index_lt x i) (complete_subord hx i))
          (veblen_increasing hf a ha _ _ hx (index_lt x i))))

/-- Rocq: `VeblenFacts.veblen_fax`. -/
theorem veblen_fax (hf : NormalFunction f) (a x : Ordinal.{u}) (ha : Complete a) (hx : Complete x) :
    f (a + x) ≤ veblen f a x :=
  match complete_zeroDec ha with
  | .inl ha₀ =>
    le_trans (hf.monotone _ _ (le_trans (add_le_add ha₀ (le_refl x)) (zero_add x).le))
      (f_le_veblen a x)
  | .inr h₀ =>
    le_trans (hf.monotone _ _ (add_le_veblen hf h₀ ha x hx)) (veblen_fixpoint_zero hf h₀ ha hx)

/-- The hierarchy over the fixpoints of `f` is the hierarchy over `f`,
shifted by one. Rocq: `VeblenFacts.veblen_enum_fixpoints`. -/
theorem veblen_enum_fixpoints (hf : NormalFunction f) (a : Ordinal.{u}) :
    ∀ x : Ordinal.{u}, Complete a → Complete x →
      veblen f (1 + a) x ≈ veblen (enumFixpoints f) a x := by
  have hE := enum_fixpoints_normal hf
  induction a using ltRec with
  | ind a iha =>
    intro x
    induction x using ltRec with
    | ind x ihx =>
      intro ha hx
      have h1a : Complete (1 + a) := onePlus_complete ha
      have h1a₀ : 0 < 1 + a := onePlus_nonzero a
      have hVE := veblen_complete hE hE.complete a ha x hx
      have hVf := veblen_complete hf hf.complete _ h1a x hx
      refine equiv_intro ?_ ?_
      · rw [veblen_unroll f (1 + a) x]
        refine lub_least (le_trans (hf.monotone _ _ (normal_inflationary hE x hx))
          (le_trans (Con.enum_are_fixpoints hf x hx).ge (f_le_veblen a x)))
          (sup_least fun j => ?_)
        have hc := complete_subord h1a j
        refine normal_fix_least (veblen_normal hf _ hc) _ _ hVE (le_intro fun z => ?_) ?_
        · exact lt_of_le_of_lt (ihx (x z) (index_lt x z) ha (complete_subord hx z)).le
            (veblen_increasing hE a ha _ _ hx (index_lt x z))
        · match add_lt (index_lt (1 + a) j) with
          | .inl hc₁ =>
            obtain ⟨_, hc₀⟩ := lt_elim hc₁
            refine le_trans (le_trans (veblen_monotone_first hf.monotone 0 _ _ hc₀)
              (veblen_zero f _).le) ?_
            match complete_zeroDec ha with
            | .inl ha₀ =>
              exact le_trans (hf.monotone _ _ (le_trans (veblen_monotone_first hE.monotone 0 a x ha₀)
                (veblen_zero _ x).le))
                (le_trans (Con.enum_are_fixpoints hf x hx).ge (f_le_veblen a x))
            | .inr a₀ =>
              exact le_trans (hf.monotone _ _ (normal_inflationary hE _ hVE))
                (le_trans (Con.enum_are_fixpoints hf _ hVE).ge (le_trans (veblen_zero _ _).ge
                  (veblen_fixpoints hE 0 a x zero_complete ha hx a₀).le))
          | .inr ⟨i, hci⟩ =>
            have hai := complete_subord ha i
            exact le_trans (veblen_monotone_first hf.monotone _ _ _ hci)
              (le_trans (iha (a i) (index_lt a i) _ hai hVE).le
                (veblen_fixpoints hE (a i) a x hai ha hx (index_lt a i)).le)
      · have key : ∀ x' : Ordinal.{u}, Complete x' → enumFixpoints f x' ≤ veblen f (1 + a) x' := by
          intro x'
          induction x' using ltRec with
          | ind x' ih =>
            intro hx'
            exact enum_least' hf x' _ hx' (veblen_complete hf hf.complete _ h1a x' hx')
              (veblen_fixpoint_zero hf h1a₀ h1a hx')
              fun x'' hc hlt => lt_of_le_of_lt (ih x'' hlt hc) (veblen_increasing hf _ h1a _ _ hx' hlt)
        rw [veblen_unroll (enumFixpoints f) a x]
        refine lub_least (key x hx) (sup_least fun i => ?_)
        have hai := complete_subord ha i
        refine normal_fix_least (veblen_normal hE (a i) hai) _ _ hVf (le_intro fun z => ?_)
          (le_trans (iha (a i) (index_lt a i) _ hai hVf).ge
            (veblen_fixpoints hf (1 + a i) (1 + a) x (onePlus_complete hai) h1a hx
              (add_lt_add_left 1 (index_lt a i))).le)
        exact lt_of_le_of_lt (ihx (x z) (index_lt x z) ha (complete_subord hx z)).ge
          (veblen_increasing hf _ h1a _ _ hx (index_lt x z))

/-- Rocq: `VeblenFacts.veblen_powOmega_epsilon`. -/
theorem veblen_powOmega_epsilon (a x : Ordinal.{u}) (ha : Complete a) (hx : Complete x) :
    veblen powOmega (1 + a) x ≈ veblen ε a x :=
  veblen_enum_fixpoints powOmega_normal a x ha hx

/-- Γ, presented as enumerating the fixpoints of `b ↦ veblen ε b 0`.
Rocq: `VeblenFacts.Γalt`. -/
theorem Γalt (x : Ordinal.{u}) : Complete x → Γ x ≈ enumFixpoints (fun b => veblen ε b 0) x := by
  have hn₁ := veblen_first_normal powOmega_normal.{u}
  have hn₂ := veblen_first_normal ε_normal.{u}
  induction x using ltRec with
  | ind x ih =>
    intro hx
    have hZ := (enum_fixpoints_normal hn₂).complete x hx
    have hΓ := Γ_normal.complete x hx
    refine equiv_intro ?_ ?_
    · refine enum_least' hn₁ x _ hx hZ ?_ fun x' hc hlt => lt_of_le_of_lt (ih x' hlt hc).le
        (enumFixpoints_increasing hn₂.monotone hlt)
      exact le_trans (veblen_monotone_first powOmega_normal.monotone _ _ 0 (le_add_left 1 _))
        (le_trans (veblen_powOmega_epsilon _ 0 hZ zero_complete).le
          (Con.enum_are_fixpoints hn₂ x hx).ge)
    · refine enum_least' hn₂ x _ hx hΓ ?_ fun x' hc hlt => lt_of_le_of_lt (ih x' hlt hc).ge
        (Γ_increasing hlt)
      exact le_trans (veblen_powOmega_epsilon _ 0 hΓ zero_complete).ge
        (le_trans (veblen_monotone_first powOmega_normal.monotone _ _ 0
          (le_trans (onePlus_least_normal hn₁ _ hΓ) (Γ_fixpoints x hx).ge)) (Γ_fixpoints x hx).ge)

/-- Rocq: `VeblenFacts.normal_ord_decompose'`. -/
theorem normal_ord_decompose' (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hx : Complete x)
    (h₀ : 0 < x) (hmono : ∀ x y, x ≤ y → f x ≤ f y) (hcont : ScottContinuous f) :
    f x ≈ sup fun i : x => f (succ (x i)) := by
  obtain ⟨x', _⟩ := lt_elim h₀
  refine equiv_intro (le_trans (hmono _ _ (le_intro fun i => lt_of_lt_of_le (succ_lt (x i))
      (sup_le (fun i : x => succ (x i)) i)))
    (hcont x.Carrier _ x' (directed_monotone x _ (fun _ _ h => succ_monotone h) hx)
      (fun a => succ_complete (complete_subord hx a))))
    (sup_least fun i => hmono _ _ (succ_least (index_lt x i)))

/-- Rocq: `VeblenFacts.normal_ord_decompose`. -/
theorem normal_ord_decompose (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hx : Complete x)
    (h₀ : 0 < x) (hf : NormalFunction f) : f x ≈ sup fun i : x => f (succ (x i)) :=
  normal_ord_decompose' x f hx h₀ hf.monotone hf.continuous

/-- Rocq: `VeblenFacts.veblen_addx_le`. -/
theorem veblen_addx_le (f : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u}) (hf : NormalFunction f)
    (ha : Complete a) : Complete x → veblen f a 0 + x ≤ veblen f a x := by
  induction x using ltRec with
  | ind x ih =>
    intro hx
    rw [add_unfold]
    exact lub_least (veblen_monotone hf.monotone a 0 x (zero_least x)) (sup_least fun i => succ_least
      (lt_of_le_of_lt (ih (x i) (index_lt x i) (complete_subord hx i))
        (veblen_increasing hf a ha _ _ hx (index_lt x i))))

/-- Rocq: `VeblenFacts.veblen_expOrd_add`. -/
theorem veblen_expOrd_add (a x : Ordinal.{u}) (ha : Complete a) :
    Complete x → ω ^ (a + x) ≤ veblen (fun y => ω ^ a + y) x 0 := by
  have hg : NormalFunction fun y => ω ^ a + y :=
    add_normal (pow_pos ω a) (pow_complete omega_gt0 omega_complete ha)
  induction x using ltRec with
  | ind x ih =>
    intro hx
    match complete_zeroDec ha with
    | .inl ha₀ =>
      calc ω ^ (a + x) ≤ ω ^ x := pow_le_pow_right ω (le_trans (add_le_add ha₀ (le_refl x)) (zero_add x).le)
        _ ≤ ω ^ x + 0 := le_add_right _ 0
        _ ≤ veblen (fun y => 1 + y) x 0 := (veblen_onePlus x hx 0 zero_complete).ge
        _ ≤ veblen (fun y => ω ^ a + y) x 0 :=
            veblen_monotone_func onePlus_normal hg
              (fun i _ => add_le_add (succ_least (pow_pos ω a)) (le_refl i)) x 0 hx zero_complete
    | .inr a₀ =>
      match complete_zeroDec hx with
      | .inl hx₀ =>
        exact le_trans (pow_le_pow_right ω (le_trans (add_le_add (le_refl a) hx₀) (add_zero a).le))
          (le_trans (le_add_right _ 0) (f_le_veblen x 0))
      | .inr x₀ =>
        have hn : NormalFunction fun y => powOmega (a + y) :=
          compose_normal powOmega_normal (add_normal a₀ ha)
        have hV := veblen_complete hg hg.complete x hx 0 zero_complete
        refine le_trans (normal_ord_decompose x _ hx x₀ hn).le (sup_least fun i => ?_)
        have hxi := complete_subord hx i
        have claim : ∀ j : Nat, ω ^ (a + x i) * ofNat j ≤ veblen (fun y => ω ^ a + y) x 0 := by
          intro j
          induction j with
          | zero => exact le_trans (mul_zero _).le (zero_least _)
          | succ j ihj =>
            calc ω ^ (a + x i) * ofNat (j + 1) ≤ ω ^ (a + x i) * ofNat j + ω ^ (a + x i) :=
                  (mul_succ _ _).le
              _ ≤ ω ^ (a + x i) + ω ^ (a + x i) * ofNat j := mul_ofNat_add_le _ j
              _ ≤ veblen (fun y => ω ^ a + y) (x i) 0 + veblen (fun y => ω ^ a + y) x 0 :=
                  add_le_add (ih (x i) (index_lt x i) hxi) ihj
              _ ≤ veblen (fun y => ω ^ a + y) (x i) (veblen (fun y => ω ^ a + y) x 0) :=
                  veblen_addx_le _ (x i) _ hg hxi hV
              _ ≤ veblen (fun y => ω ^ a + y) x 0 :=
                  (veblen_fixpoints hg (x i) x 0 hxi hx zero_complete (index_lt x i)).le
        calc powOmega (a + succ (x i)) ≤ ω ^ succ (a + x i) := pow_le_pow_right ω (add_succ a (x i)).le
          _ ≤ ω ^ (a + x i) * ω := (pow_succ (a + x i) omega_gt0).le
          _ ≤ sup fun j : (ω : Ordinal.{u}).Carrier => ω ^ (a + x i) * ω j := (mul_limit _ omega_limit).le
          _ ≤ veblen (fun y => ω ^ a + y) x 0 := sup_least fun j => claim j.down

/-- Classically, a fixpoint-closed limit below the next fixpoint is itself an
enumerated fixpoint. Rocq: `VeblenFacts.enum_fixpoint_decompose`. -/
theorem enum_fixpoint_decompose (em : ExcludedMiddle) (hf : NormalFunction f) (x : Ordinal.{u})
    (hl : IsLimit x) (h₁ : f x ≤ x) (h₂ : x < enumFixpoints f x) :
    ∃ a, x ≈ enumFixpoints f a ∧ a < x := by
  have hx := ord_complete em x
  have h₂' := lt_of_lt_of_le h₂ (normal_ord_decompose x _ hx ((isLimit_iff x).1 hl).1
    (enum_fixpoints_normal hf)).le
  obtain ⟨a₀, ha₀⟩ := sup_lt h₂'
  obtain ⟨a, ⟨hax, ha⟩, hleast⟩ := ord_well_ordered em (fun a => a < x ∧ x ≤ enumFixpoints f a)
    (succ (x a₀)) ⟨limit_unreachable hl (x a₀) (index_lt x a₀), le_of_lt ha₀⟩
  have hle : enumFixpoints f a ≤ x := by
    rw [enumFixpoints_unfold]
    refine normal_fix_least hf _ x hx (le_intro fun q => ?_) h₁
    match order_total em x (enumFixpoints f (a q)) with
    | .inl h =>
      exact (lt_irrefl (a q) (lt_of_lt_of_le (index_lt a q)
        (hleast (a q) ⟨lt_trans (index_lt a q) hax, h⟩))).elim
    | .inr h => exact h
  exact ⟨a, equiv_intro ha hle, hax⟩

/-- Classically, a limit `x` with `f x ≤ x < veblen f x 0` is a Veblen term
with smaller components. Rocq: `VeblenFacts.veblen_decompose`. -/
theorem veblen_decompose (em : ExcludedMiddle) (hf : NormalFunction f) (x : Ordinal.{u})
    (hl : IsLimit x) (h₁ : x < veblen f x 0) (h₂ : f x ≤ x) :
    ∃ a b, x ≈ veblen f a b ∧ 0 < a ∧ a < x ∧ b < x := by
  have hx := ord_complete em x
  have hx₀ : 0 < x := lt_of_lt_of_le (hf.nonzero x) h₂
  obtain ⟨a, ⟨ha₀, b₀, hb₀, hab₀⟩, hleast⟩ := ord_well_ordered em
    (fun a => 0 < a ∧ ∃ b, b < x ∧ x ≤ veblen f a b) x ⟨hx₀, 0, hx₀, le_of_lt h₁⟩
  obtain ⟨b, ⟨hb, hab⟩, hbleast⟩ := ord_well_ordered em
    (fun b => b < x ∧ x ≤ veblen f a b) b₀ ⟨hb₀, hab₀⟩
  have hle : veblen f a b ≤ x := by
    rw [veblen_unroll]
    refine lub_least (le_trans (hf.monotone _ _ (le_of_lt hb)) h₂) (sup_least fun i => ?_)
    refine normal_fix_least (veblen_normal hf _ (ord_complete em _)) _ x hx
      (le_intro fun q => ?_) ?_
    · match order_total em x (veblen f a (b q)) with
      | .inl h =>
        exact (lt_irrefl (b q) (lt_of_lt_of_le (index_lt b q)
          (hbleast (b q) ⟨lt_trans (index_lt b q) hb, h⟩))).elim
      | .inr h => exact h
    · match order_total em (a i) 0 with
      | .inl hi₀ =>
        exact le_trans (veblen_monotone_first hf.monotone 0 _ x hi₀) (le_trans (veblen_zero f x).le h₂)
      | .inr hi₀ =>
        obtain ⟨⟨q₀⟩, _⟩ := id hl
        refine le_trans (veblen_monotone hf.monotone _ _ _ (limit_boundedSup hl).le)
          (le_trans (veblen_continuous hf _ (ord_complete em _) x.Carrier x.size q₀
            (ord_directed em _ _) (fun _ => ord_complete em _)) (sup_least fun q => ?_))
        match order_total em (veblen f (a i) (x q)) x with
        | .inl h => exact h
        | .inr h =>
          exact (lt_irrefl a (lt_of_le_of_lt (hleast (a i) ⟨hi₀, x q, index_lt x q, le_of_lt h⟩)
            (index_lt a i))).elim
  have hax : a < x := by
    match order_total em x a with
    | .inr h => exact h
    | .inl h =>
      exact (lt_irrefl x (lt_of_lt_of_le h₁ (le_trans (veblen_monotone_first hf.monotone a x 0 h)
        (le_trans (veblen_monotone hf.monotone a 0 b (zero_least b)) hle)))).elim
  exact ⟨a, b, equiv_intro hab hle, ha₀, hax, hb⟩

end Ordinal

end ConstructiveOrdinals
