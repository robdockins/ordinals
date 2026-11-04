import ConstructiveOrdinals.Notation.CantorDecomposition
import ConstructiveOrdinals.Veblen.Facts
import ConstructiveOrdinals.Prelude.Relations

/-!
# Veblen forms over `1 + ·` and `ε`: a notation system for Γ₀

Port of `Ordinal/Notation/VWNotation.v`.

`V a x` denotes `veblen (1 + ·) a x` and `W a x` denotes `veblen ε a x`.
The normal forms denote exactly the ordinals below `Γ 0`. As in
`Notation/V`, normalization is presented as a confluent, strongly
normalizing rewriting system with unique normal forms. The system has a Cantor
decomposition, so it supports Cantor arithmetic and natural sums, and with
the excluded middle it has a notation for every ordinal below `Γ 0`.

Lean notes:

- Rocq's `VF_compare` has an inner `fix` on its second argument, for each of
  the two constructors of the first argument. These are the separate functions
  `compareV` and `compareW`.
- `VF_isZero` returns `x = Z` or `0 < x`, as a `PSum`.
- `W_epsilon` is stated earlier than in Rocq, because the collapse lemmas use
  it.
-/

namespace ConstructiveOrdinals.VWNotation

open Ordinal

/-- Veblen forms over `1 + ·` and `ε`. Rocq: `Notation.VWNotation.VForm`. -/
inductive VForm : Type where
  | Z : VForm
  | V : VForm → VForm → VForm
  | W : VForm → VForm → VForm

namespace VForm

/-- Rocq: `Notation.VWNotation.VF_denote`. -/
def denote : VForm → Ordinal.{0}
  | Z => 0
  | V a x => veblen (fun y => 1 + y) (denote a) (denote x)
  | W a x => veblen ε (denote a) (denote x)

instance : Sized VForm := ⟨denote⟩

end VForm

/-- The ordinal of all forms. Rocq: `Notation.VWNotation.VF`. -/
def VF : Ordinal.{0} := mk VForm VForm.denote

namespace VForm

/-- Rocq: `Notation.VWNotation.VF_complete`. -/
theorem complete : ∀ x : VForm, Complete (denote x)
  | Z => zero_complete
  | V a x => veblen_complete onePlus_normal onePlus_normal.complete _ (complete a) _ (complete x)
  | W a x => veblen_complete ε_normal ε_normal.complete _ (complete a) _ (complete x)

/-- Rocq: `Notation.VWNotation.VF_size`. -/
def size : VForm → Nat
  | Z => 0
  | V x y => size x + size y + 1
  | W x y => size x + size y + 1

/-- Rocq: `Notation.VWNotation.VF_isZero`. -/
def isZero : (x : VForm) → PSum (x = Z) (0 < denote x)
  | Z => .inl rfl
  | V _ _ => .inr (veblen_nonzero onePlus_normal _ _)
  | W _ _ => .inr (veblen_nonzero ε_normal _ _)

/-- Values of `veblen ε` are ε-numbers.
Rocq: `Notation.VWNotation.W_epsilon`. -/
theorem W_epsilon (x y : Ordinal.{0}) (hx : Complete x) (hy : Complete y) :
    ω ^ veblen ε x y ≈ veblen ε x y := by
  -- `veblen ε x y` is a value of `ε`
  have h : ∃ s, veblen ε x y ≈ ε s := by
    cases complete_zeroDec hx with
    | inl h =>
      exact ⟨y, equiv_trans (veblen_congr ε_normal.monotone (equiv_intro h (zero_least _))
        (equiv_refl y)) (veblen_zero ε y)⟩
    | inr h =>
      exact ⟨veblen ε x y, equiv_trans (equiv_symm (veblen_fixpoints ε_normal 0 x y
        zero_complete hx hy h)) (veblen_zero ε _)⟩
  obtain ⟨s, hs⟩ := h
  exact equiv_trans (pow_congr (equiv_refl ω) hs) (equiv_trans (equiv_symm (ε_fixpoint s))
    (equiv_symm hs))

/-- Rocq: `Notation.VWNotation.V_collapse`. -/
theorem V_collapse (a b x : VForm) (h : denote a < denote b) :
    denote (V a (V b x)) ≈ denote (V b x) :=
  veblen_fixpoints onePlus_normal _ _ _ (complete a) (complete b) (complete x) h

/-- Rocq: `Notation.VWNotation.W_collapse`. -/
theorem W_collapse (a b x : VForm) (h : denote a < denote b) :
    denote (W a (W b x)) ≈ denote (W b x) :=
  veblen_fixpoints ε_normal _ _ _ (complete a) (complete b) (complete x) h

/-- Rocq: `Notation.VWNotation.VW_collapse2`. -/
theorem VW_collapse2 (b c : VForm) : denote (V (W b c) Z) ≈ denote (W b c) :=
  equiv_trans (veblen_onePlus _ (complete (W b c)) _ zero_complete)
    (equiv_trans (add_zero _) (W_epsilon _ _ (complete b) (complete c)))

/-- Rocq: `Notation.VWNotation.VW_collapse`. -/
theorem VW_collapse (a b c : VForm) (h : denote a < denote (W b c)) :
    denote (V a (W b c)) ≈ denote (W b c) :=
  equiv_intro
    (veblen_collapse onePlus_normal _ _ _ (complete a) (complete (W b c)) (complete (W b c)) h
      (le_refl _) (VW_collapse2 b c).le)
    (veblen_inflationary onePlus_normal _ _ (complete (W b c)))

/-! ## Comparison -/

/-- Compare `V a x'` with a form, given the comparisons with `a` and with
`x'`. The inner `fix` of Rocq's `VF_compare`, first case. -/
def compareV (x' : VForm) (recA recX : VForm → Ordering) : VForm → Ordering
  | Z => .gt
  | V b y' =>
    match recA b with
    | .lt => recX (V b y')
    | .eq => recX y'
    | .gt => compareV x' recA recX y'
  | W b y' =>
    match recA (W b y') with
    | .lt => recX (W b y')
    | .eq =>
      match isZero x' with
      | .inl _ => .eq
      | .inr _ => .gt
    | .gt => .gt

/-- Compare `W a x'` with a form, given the comparisons with `a` and with
`x'`. The inner `fix` of Rocq's `VF_compare`, second case. -/
def compareW (recA recX : VForm → Ordering) : VForm → Ordering
  | Z => .gt
  | V b y' =>
    match compareW recA recX b with
    | .lt => .lt
    | .eq =>
      match isZero y' with
      | .inl _ => .eq
      | .inr _ => .lt
    | .gt => compareW recA recX y'
  | W b y' =>
    match recA b with
    | .lt => recX (W b y')
    | .eq => recX y'
    | .gt => compareW recA recX y'

/-- Rocq: `Notation.VWNotation.VF_compare`. -/
def compare : VForm → VForm → Ordering
  | Z, Z => .eq
  | Z, V _ _ => .lt
  | Z, W _ _ => .lt
  | V a x', y => compareV x' (compare a) (compare x') y
  | W a x', y => compareW (compare a) (compare x') y

/-- Rocq: `Notation.VWNotation.VW_compare_eq`. -/
theorem VW_compare_eq (a x b y : VForm) :
    compare (V a x) (W b y) =
      match compare a (W b y) with
      | .lt => compare x (W b y)
      | .eq =>
        match isZero x with
        | .inl _ => .eq
        | .inr _ => .gt
      | .gt => .gt := rfl

/-- Rocq: `Notation.VWNotation.WV_compare_eq`. -/
theorem WV_compare_eq (a x b y : VForm) :
    compare (W a x) (V b y) =
      match compare (W a x) b with
      | .lt => .lt
      | .eq =>
        match isZero y with
        | .inl _ => .eq
        | .inr _ => .lt
      | .gt => compare (W a x) y := rfl

/-- `veblen_compare_correct` with the comparison result as a plain `match`. -/
private theorem veblen_cmp {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f)
    {a b x y : Ordinal.{0}} (ha : Complete a) (hb : Complete b) (hx : Complete x)
    (hy : Complete y) (o oxVby oxy oVaxy : Ordering) (hab : OrderingCorrect o a b)
    (h₁ : OrderingCorrect oxVby x (veblen f b y)) (h₂ : OrderingCorrect oxy x y)
    (h₃ : OrderingCorrect oVaxy (veblen f a x) y) :
    OrderingCorrect (match (generalizing := false) o with
      | .lt => oxVby
      | .eq => oxy
      | .gt => oVaxy) (veblen f a x) (veblen f b y) := by
  cases o with
  | lt => exact veblen_compare_correct hf .lt oxy oxVby oVaxy a b x y ha hb hx hy hab h₂ h₁ h₃
  | eq => exact veblen_compare_correct hf .eq oxy oxVby oVaxy a b x y ha hb hx hy hab h₂ h₁ h₃
  | gt => exact veblen_compare_correct hf .gt oxy oxVby oVaxy a b x y ha hb hx hy hab h₂ h₁ h₃

/-- `a ≤ veblen (1 + ·) a x`. -/
private theorem le_V (a x : VForm) : denote a ≤ denote (V a x) :=
  le_trans (normal_inflationary (veblen_first_normal onePlus_normal) _ (complete a))
    (veblen_monotone onePlus_normal.monotone _ _ _ (zero_least _))

/-- Rocq: `Notation.VWNotation.VF_compare_correct`. -/
theorem compare_correct : ∀ x y : VForm, OrderingCorrect (compare x y) (denote x) (denote y) := by
  intro x
  induction x with
  | Z =>
    intro y
    cases y with
    | Z => exact equiv_refl _
    | V _ _ => exact veblen_nonzero onePlus_normal _ _
    | W _ _ => exact veblen_nonzero ε_normal _ _
  | V a x iha ihx =>
    intro y
    induction y with
    | Z => exact veblen_nonzero onePlus_normal _ _
    | V b y _ ihy =>
      exact veblen_cmp onePlus_normal (complete a) (complete b) (complete x) (complete y)
        (compare a b) _ _ _ (iha b) (ihx (V b y)) (ihx y) ihy
    | W b y _ _ =>
      rw [VW_compare_eq]
      have hab := iha (W b y)
      revert hab
      cases compare a (W b y) with
      | lt =>
        intro hab
        have hx := ihx (W b y)
        revert hx
        cases compare x (W b y) with
        | lt =>
          exact fun hx => veblen_collapse' onePlus_normal _ _ _ (complete a) (complete x)
            (complete (W b y)) hab hx (VW_collapse2 b y).le
        | eq =>
          exact fun hx => equiv_intro
            (veblen_collapse onePlus_normal _ _ _ (complete a) (complete x) (complete (W b y))
              hab hx.le (VW_collapse2 b y).le)
            (le_trans hx.ge (veblen_inflationary onePlus_normal _ _ (complete x)))
        | gt =>
          exact fun hx => lt_of_lt_of_le hx (veblen_inflationary onePlus_normal _ _ (complete x))
      | eq =>
        intro hab
        match isZero x with
        | .inl hx =>
          subst hx
          exact equiv_trans (veblen_congr onePlus_normal.monotone hab (equiv_refl _))
            (VW_collapse2 b y)
        | .inr hx =>
          exact lt_of_le_of_lt hab.ge (veblen_subterm1 onePlus_normal _ _ _ (complete a)
            (complete a) (complete x) hx (le_refl _))
      | gt => exact fun hab => lt_of_lt_of_le hab (le_V a x)
  | W a x iha ihx =>
    intro y
    induction y with
    | Z => exact veblen_nonzero ε_normal _ _
    | V b y ihb ihy =>
      rw [WV_compare_eq]
      revert ihb
      cases compare (W a x) b with
      | lt => exact fun hb => lt_of_lt_of_le hb (le_V b y)
      | eq =>
        intro hb
        match isZero y with
        | .inl hy =>
          subst hy
          exact equiv_trans (equiv_symm (VW_collapse2 a x))
            (veblen_congr onePlus_normal.monotone hb (equiv_refl _))
        | .inr hy =>
          exact lt_of_le_of_lt hb.le (veblen_subterm1 onePlus_normal _ _ _ (complete b)
            (complete b) (complete y) hy (le_refl _))
      | gt =>
        intro hb
        revert ihy
        cases compare (W a x) y with
        | lt => exact fun hy => lt_of_lt_of_le hy (veblen_inflationary onePlus_normal _ _ (complete y))
        | eq =>
          exact fun hy => equiv_intro
            (le_trans hy.le (veblen_inflationary onePlus_normal _ _ (complete y)))
            (veblen_collapse onePlus_normal _ _ _ (complete b) (complete y) (complete (W a x))
              hb hy.ge (VW_collapse2 a x).le)
        | gt =>
          exact fun hy => veblen_collapse' onePlus_normal _ _ _ (complete b) (complete y)
            (complete (W a x)) hb hy (VW_collapse2 a x).le
    | W b y _ ihy =>
      exact veblen_cmp ε_normal (complete a) (complete b) (complete x) (complete y)
        (compare a b) _ _ _ (iha b) (ihx (W b y)) (ihx y) ihy

/-- The order on forms is decidable. Rocq: `Notation.VWNotation.VF_decide_order`. -/
def decideOrder (x y : VForm) : PSum (sz x < sz y) (sz y ≤ sz x) :=
  match compare x y, compare_correct x y with
  | .lt, h => .inl h
  | .eq, h => .inr h.ge
  | .gt, h => .inr (le_of_lt h)

/-- Rocq: `Notation.VWNotation.VF_lt_correct`. -/
theorem lt_correct (x y : VForm) : compare x y = .lt ↔ denote x < denote y := by
  have h := compare_correct x y
  revert h
  cases compare x y with
  | lt => exact fun h => ⟨fun _ => h, fun _ => rfl⟩
  | eq => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h' h.ge)).elim⟩
  | gt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_trans h' h)).elim⟩

/-- Rocq: `Notation.VWNotation.VF_le_correct`. -/
theorem le_correct (x y : VForm) : compare y x ≠ .lt ↔ denote x ≤ denote y := by
  have h := compare_correct y x
  revert h
  cases compare y x with
  | lt => exact fun h => ⟨fun h' => absurd rfl h', fun h' => (lt_irrefl _ (lt_of_lt_of_le h h')).elim⟩
  | eq => exact fun h => ⟨fun _ => h.ge, fun _ h' => nomatch h'⟩
  | gt => exact fun h => ⟨fun _ => le_of_lt h, fun _ h' => nomatch h'⟩

/-! ## Normal forms -/

/-- Rocq: `Notation.VWNotation.VF_isNormal`. -/
def IsNormal : VForm → Prop
  | Z => True
  | V a b => IsNormal a ∧ IsNormal b ∧
    match b with
    | Z =>
      match a with
      | Z => True
      | V _ _ => True
      | W _ _ => False
    | V x _ => denote x ≤ denote a
    | W c d => denote (W c d) ≤ denote a
  | W a b => IsNormal a ∧ IsNormal b ∧
    match b with
    | Z => True
    | V _ _ => True
    | W x _ => denote x ≤ denote a

/-- Both arguments are below the whole term.
Rocq: `Notation.VWNotation.VF_subterm_shrink`. -/
def SubtermShrink : VForm → Prop
  | Z => True
  | V a b => denote a < denote (V a b) ∧ denote b < denote (V a b)
  | W a b => denote a < denote (W a b) ∧ denote b < denote (W a b)

/-- Rocq: `Notation.VWNotation.VF_normal_subterm_shrink`. -/
theorem normal_subterm_shrink : ∀ x : VForm, IsNormal x → SubtermShrink x
  | Z, _ => trivial
  | V a b, h => by
    have iha := normal_subterm_shrink a h.1
    have ihb := normal_subterm_shrink b h.2.1
    refine ⟨?_, ?_⟩
    · cases b with
      | Z =>
        match a, h, iha with
        | Z, _, _ => exact veblen_nonzero onePlus_normal _ _
        | V c d, _, iha =>
          exact veblen_subterm1_zero_nest onePlus_normal _ _ _ (complete c) (complete d)
            (complete (V c d)) iha.1 iha.2
        | W _ _, h, _ => exact h.2.2.elim
      | V c d =>
        exact veblen_subterm1 onePlus_normal _ _ _ (complete a) (complete a) (complete (V c d))
          (veblen_nonzero onePlus_normal _ _) (le_refl _)
      | W c d =>
        exact veblen_subterm1 onePlus_normal _ _ _ (complete a) (complete a) (complete (W c d))
          (veblen_nonzero ε_normal _ _) (le_refl _)
    · cases b with
      | Z => exact veblen_nonzero onePlus_normal _ _
      | V c d =>
        exact veblen_increasing' onePlus_normal _ _ _ _ (complete c) (complete (V c d)) h.2.2
          ihb.2
      | W c d =>
        exact lt_of_le_of_lt h.2.2 (veblen_subterm1 onePlus_normal _ _ _ (complete a)
          (complete a) (complete (W c d)) (veblen_nonzero ε_normal _ _) (le_refl _))
  | W a b, h => by
    have iha := normal_subterm_shrink a h.1
    have ihb := normal_subterm_shrink b h.2.1
    refine ⟨?_, ?_⟩
    · cases b with
      | Z =>
        match a, iha with
        | Z, _ => exact veblen_nonzero ε_normal _ _
        | V c d, iha =>
          exact lt_of_le_of_lt
            (veblen_monotone_func onePlus_normal ε_normal
              (fun i hi => onePlus_least_normal ε_normal i hi) _ _ (complete c) (complete d))
            (veblen_subterm1_zero_nest ε_normal _ _ _ (complete c) (complete d)
              (complete (V c d)) iha.1 iha.2)
        | W c d, iha =>
          exact veblen_subterm1_zero_nest ε_normal _ _ _ (complete c) (complete d)
            (complete (W c d)) iha.1 iha.2
      | V c d =>
        exact veblen_subterm1 ε_normal _ _ _ (complete a) (complete a) (complete (V c d))
          (veblen_nonzero onePlus_normal _ _) (le_refl _)
      | W c d =>
        exact veblen_subterm1 ε_normal _ _ _ (complete a) (complete a) (complete (W c d))
          (veblen_nonzero ε_normal _ _) (le_refl _)
    · cases b with
      | Z => exact veblen_nonzero ε_normal _ _
      | V c d =>
        exact veblen_collapse' onePlus_normal _ _ _ (complete c) (complete d) (complete (W a (V c d)))
          (lt_of_lt_of_le ihb.1 (veblen_inflationary ε_normal _ _ (complete (V c d))))
          (lt_of_lt_of_le ihb.2 (veblen_inflationary ε_normal _ _ (complete (V c d))))
          (VW_collapse2 a (V c d)).le
      | W c d =>
        exact veblen_increasing' ε_normal _ _ _ _ (complete c) (complete (W c d)) h.2.2 ihb.2

/-- `x ≤ y` is decidable, by comparison. -/
private def leDec (x y : VForm) : Decidable (denote x ≤ denote y) :=
  match compare x y, compare_correct x y with
  | .lt, h => isTrue (le_of_lt h)
  | .eq, h => isTrue h.le
  | .gt, h => isFalse fun h' => lt_irrefl _ (lt_of_lt_of_le h h')

/-- Normality is decidable. Rocq: `Notation.VWNotation.VF_isNormal_dec`. -/
def isNormalDec : (x : VForm) → Decidable (IsNormal x)
  | Z => isTrue trivial
  | V a b =>
    match isNormalDec a with
    | isFalse ha => isFalse fun h => ha h.1
    | isTrue ha =>
      match isNormalDec b with
      | isFalse hb => isFalse fun h => hb h.2.1
      | isTrue hb =>
        match b, hb with
        | Z, hb =>
          match a, ha with
          | Z, ha => isTrue ⟨ha, hb, trivial⟩
          | V _ _, ha => isTrue ⟨ha, hb, trivial⟩
          | W _ _, _ => isFalse fun h => h.2.2
        | V c _, hb =>
          match leDec c a with
          | isTrue h => isTrue ⟨ha, hb, h⟩
          | isFalse h => isFalse fun h' => h h'.2.2
        | W c d, hb =>
          match leDec (W c d) a with
          | isTrue h => isTrue ⟨ha, hb, h⟩
          | isFalse h => isFalse fun h' => h h'.2.2
  | W a b =>
    match isNormalDec a with
    | isFalse ha => isFalse fun h => ha h.1
    | isTrue ha =>
      match isNormalDec b with
      | isFalse hb => isFalse fun h => hb h.2.1
      | isTrue hb =>
        match b, hb with
        | Z, hb => isTrue ⟨ha, hb, trivial⟩
        | V _ _, hb => isTrue ⟨ha, hb, trivial⟩
        | W c _, hb =>
          match leDec c a with
          | isTrue h => isTrue ⟨ha, hb, h⟩
          | isFalse h => isFalse fun h' => h h'.2.2

instance : DecidablePred IsNormal := isNormalDec

/-! ## Normalization by rewriting -/

/-- Rocq: `Notation.VWNotation.redex`. -/
inductive Redex : VForm → VForm → Prop
  | V {a b x : VForm} : compare a b = .lt → Redex (V a (V b x)) (V b x)
  | W {a b x : VForm} : compare a b = .lt → Redex (W a (W b x)) (W b x)
  | VW {a b c : VForm} : compare a (W b c) = .lt → Redex (V a (W b c)) (W b c)
  | VW2 {b c : VForm} : Redex (V (W b c) Z) (W b c)

/-- Rocq: `Notation.VWNotation.redex_sound`. -/
theorem redex_sound {x y : VForm} : Redex x y → denote x ≈ denote y
  | .V h => V_collapse _ _ _ ((lt_correct _ _).1 h)
  | .W h => W_collapse _ _ _ ((lt_correct _ _).1 h)
  | .VW h => VW_collapse _ _ _ ((lt_correct _ _).1 h)
  | .VW2 => VW_collapse2 _ _

/-- Rocq: `Notation.VWNotation.one_step_reduce`. -/
inductive OneStepReduce : VForm → VForm → Prop
  | redex {x y : VForm} : Redex x y → OneStepReduce x y
  | vcong1 {x x' y : VForm} : OneStepReduce x x' → OneStepReduce (V x y) (V x' y)
  | vcong2 {x y y' : VForm} : OneStepReduce y y' → OneStepReduce (V x y) (V x y')
  | wcong1 {x x' y : VForm} : OneStepReduce x x' → OneStepReduce (W x y) (W x' y)
  | wcong2 {x y y' : VForm} : OneStepReduce y y' → OneStepReduce (W x y) (W x y')

/-- Rocq: `Notation.VWNotation.one_step_reduce_sound`. -/
theorem one_step_reduce_sound {x y : VForm} : OneStepReduce x y → denote x ≈ denote y
  | .redex h => redex_sound h
  | .vcong1 h => veblen_onePlus_congr (one_step_reduce_sound h) (equiv_refl _)
  | .vcong2 h => veblen_onePlus_congr (equiv_refl _) (one_step_reduce_sound h)
  | .wcong1 h => veblen_congr ε_normal.monotone (one_step_reduce_sound h) (equiv_refl _)
  | .wcong2 h => veblen_congr ε_normal.monotone (equiv_refl _) (one_step_reduce_sound h)

/-- Rocq: `Notation.VWNotation.step_reduce_sound`. -/
theorem step_reduce_sound {x y : VForm} :
    ClosReflTrans OneStepReduce x y → denote x ≈ denote y
  | .step h => one_step_reduce_sound h
  | .refl _ => equiv_refl _
  | .trans h₁ h₂ => equiv_trans (step_reduce_sound h₁) (step_reduce_sound h₂)

private theorem not_reduce_Z : ¬ ∃ z, OneStepReduce Z z := fun ⟨_, h⟩ => by
  cases h with
  | redex h => cases h

/-- Rocq: `Notation.VWNotation.VF_notIsNormal_reduce`. -/
theorem notIsNormal_reduce : ∀ x : VForm, ¬ IsNormal x ↔ ∃ z, OneStepReduce x z := by
  intro x
  induction x with
  | Z => exact ⟨fun h => absurd trivial h, fun h => absurd h not_reduce_Z⟩
  | V a b iha ihb =>
    match isNormalDec a with
    | isFalse ha =>
      exact ⟨fun _ => let ⟨z, h⟩ := iha.1 ha; ⟨V z b, .vcong1 h⟩, fun _ h => ha h.1⟩
    | isTrue ha =>
      match isNormalDec b with
      | isFalse hb =>
        exact ⟨fun _ => let ⟨z, h⟩ := ihb.1 hb; ⟨V a z, .vcong2 h⟩, fun _ h => hb h.2.1⟩
      | isTrue hb =>
        constructor
        · intro hn
          cases b with
          | Z =>
            cases a with
            | Z => exact absurd ⟨ha, hb, trivial⟩ hn
            | V _ _ => exact absurd ⟨ha, hb, trivial⟩ hn
            | W c d => exact ⟨W c d, .redex .VW2⟩
          | V c d =>
            match decideOrder a c with
            | .inl h => exact ⟨V c d, .redex (.V ((lt_correct _ _).2 h))⟩
            | .inr h => exact absurd ⟨ha, hb, h⟩ hn
          | W c d =>
            match decideOrder a (W c d) with
            | .inl h => exact ⟨W c d, .redex (.VW ((lt_correct _ _).2 h))⟩
            | .inr h => exact absurd ⟨ha, hb, h⟩ hn
        · rintro ⟨z, hz⟩ hn
          cases hz with
          | redex h =>
            cases h with
            | V h => exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h) hn.2.2)
            | VW h => exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h) hn.2.2)
            | VW2 => exact hn.2.2
          | vcong1 h => exact iha.2 ⟨_, h⟩ ha
          | vcong2 h => exact ihb.2 ⟨_, h⟩ hb
  | W a b iha ihb =>
    match isNormalDec a with
    | isFalse ha =>
      exact ⟨fun _ => let ⟨z, h⟩ := iha.1 ha; ⟨W z b, .wcong1 h⟩, fun _ h => ha h.1⟩
    | isTrue ha =>
      match isNormalDec b with
      | isFalse hb =>
        exact ⟨fun _ => let ⟨z, h⟩ := ihb.1 hb; ⟨W a z, .wcong2 h⟩, fun _ h => hb h.2.1⟩
      | isTrue hb =>
        constructor
        · intro hn
          cases b with
          | Z => exact absurd ⟨ha, hb, trivial⟩ hn
          | V _ _ => exact absurd ⟨ha, hb, trivial⟩ hn
          | W c d =>
            match decideOrder a c with
            | .inl h => exact ⟨W c d, .redex (.W ((lt_correct _ _).2 h))⟩
            | .inr h => exact absurd ⟨ha, hb, h⟩ hn
        · rintro ⟨z, hz⟩ hn
          cases hz with
          | redex h =>
            cases h with
            | W h => exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h) hn.2.2)
          | wcong1 h => exact iha.2 ⟨_, h⟩ ha
          | wcong2 h => exact ihb.2 ⟨_, h⟩ hb

/-- Rocq: `Notation.VWNotation.VF_isNormal_no_reduce`. -/
theorem isNormal_no_reduce (x : VForm) : IsNormal x ↔ ¬ ∃ z, OneStepReduce x z :=
  match isNormalDec x with
  | isTrue h => ⟨fun _ hr => (notIsNormal_reduce x).2 hr h, fun _ => h⟩
  | isFalse h => ⟨fun h' => absurd h' h, fun hr => absurd ((notIsNormal_reduce x).1 h) hr⟩

/-- Two normal forms with the same head symbol and denotation have
equivalent arguments. -/
private theorem same_head {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f) {a b x y : VForm}
    (hx : denote x < veblen f (denote a) (denote x)) (hy : denote y < veblen f (denote b) (denote y))
    (h : veblen f (denote a) (denote x) ≈ veblen f (denote b) (denote y)) :
    denote a ≈ denote b ∧ denote x ≈ denote y := by
  have hab : denote a ≈ denote b := by
    have hc := compare_correct a b
    revert hc
    cases compare a b with
    | lt =>
      intro hc
      refine (lt_irrefl (veblen f (denote a) (denote x)) ?_).elim
      calc veblen f (denote a) (denote x)
          < veblen f (denote a) (veblen f (denote b) (denote y)) :=
            veblen_increasing hf _ (complete a) _ _
              (veblen_complete hf hf.complete _ (complete b) _ (complete y))
              (lt_of_lt_of_le hx h.le)
        _ ≈ veblen f (denote b) (denote y) :=
            veblen_fixpoints hf _ _ _ (complete a) (complete b) (complete y) hc
        _ ≈ veblen f (denote a) (denote x) := equiv_symm h
    | eq => exact id
    | gt =>
      intro hc
      refine (lt_irrefl (veblen f (denote b) (denote y)) ?_).elim
      calc veblen f (denote b) (denote y)
          < veblen f (denote b) (veblen f (denote a) (denote x)) :=
            veblen_increasing hf _ (complete b) _ _
              (veblen_complete hf hf.complete _ (complete a) _ (complete x))
              (lt_of_lt_of_le hy h.ge)
        _ ≈ veblen f (denote a) (denote x) :=
            veblen_fixpoints hf _ _ _ (complete b) (complete a) (complete x) hc
        _ ≈ veblen f (denote b) (denote y) := h
  refine ⟨hab, ?_⟩
  have hc := compare_correct x y
  revert hc
  cases compare x y with
  | lt =>
    exact fun hc => (lt_irrefl _ (lt_of_lt_of_le (veblen_increasing' hf _ _ _ _ (complete a)
      (complete y) hab.le hc) h.ge)).elim
  | eq => exact id
  | gt =>
    exact fun hc => (lt_irrefl _ (lt_of_lt_of_le (veblen_increasing' hf _ _ _ _ (complete b)
      (complete x) hab.ge hc) h.le)).elim

/-- A normal `V` form and a `W` form never denote the same ordinal. -/
private theorem V_ne_W {a x b y : VForm} (hx : IsNormal (V a x))
    (h : denote (V a x) ≈ denote (W b y)) : False := by
  refine lt_irrefl (denote (V a x)) ?_
  calc denote (V a x)
      < denote (V (V a x) Z) := (normal_subterm_shrink (V (V a x) Z) ⟨hx, trivial, trivial⟩).1
    _ ≤ denote (V (W b y) Z) := veblen_monotone_first onePlus_normal.monotone _ _ _ h.le
    _ ≈ denote (W b y) := VW_collapse2 b y
    _ ≈ denote (V a x) := equiv_symm h

/-- Rocq: `Notation.VWNotation.VF_normal_forms_unique`. -/
theorem normal_forms_unique : ∀ x y : VForm, IsNormal x → IsNormal y →
    denote x ≈ denote y → x = y
  | Z, Z, _, _, _ => rfl
  | Z, V _ _, _, _, h =>
    absurd (lt_of_lt_of_le (veblen_nonzero onePlus_normal _ _) h.ge) (lt_irrefl 0)
  | Z, W _ _, _, _, h => absurd (lt_of_lt_of_le (veblen_nonzero ε_normal _ _) h.ge) (lt_irrefl 0)
  | V _ _, Z, _, _, h =>
    absurd (lt_of_lt_of_le (veblen_nonzero onePlus_normal _ _) h.le) (lt_irrefl 0)
  | W _ _, Z, _, _, h => absurd (lt_of_lt_of_le (veblen_nonzero ε_normal _ _) h.le) (lt_irrefl 0)
  | V a x, V b y, hx, hy, h => by
    obtain ⟨hab, hxy⟩ := same_head onePlus_normal (normal_subterm_shrink _ hx).2
      (normal_subterm_shrink _ hy).2 h
    rw [normal_forms_unique a b hx.1 hy.1 hab, normal_forms_unique x y hx.2.1 hy.2.1 hxy]
  | W a x, W b y, hx, hy, h => by
    obtain ⟨hab, hxy⟩ := same_head ε_normal (normal_subterm_shrink _ hx).2
      (normal_subterm_shrink _ hy).2 h
    rw [normal_forms_unique a b hx.1 hy.1 hab, normal_forms_unique x y hx.2.1 hy.2.1 hxy]
  | V _ _, W _ _, hx, _, h => (V_ne_W hx h).elim
  | W _ _, V _ _, _, hy, h => (V_ne_W hy (equiv_symm h)).elim

/-- Build `V a b`, absorbing `a` where the result would not be normal.
Rocq: `Notation.VWNotation.Vnorm`. -/
def vnorm (a : VForm) : VForm → VForm
  | Z =>
    match a with
    | W c d => W c d
    | Z => V Z Z
    | V c d => V (V c d) Z
  | V x y =>
    match compare a x with
    | .lt => V x y
    | .eq => V a (V x y)
    | .gt => V a (V x y)
  | W x y =>
    match compare a (W x y) with
    | .lt => W x y
    | .eq => V a (W x y)
    | .gt => V a (W x y)

/-- Build `W a b`, absorbing `a` where the result would not be normal.
Rocq: `Notation.VWNotation.Wnorm`. -/
def wnorm (a : VForm) : VForm → VForm
  | Z => W a Z
  | V x y => W a (V x y)
  | W x y =>
    match compare a x with
    | .lt => W x y
    | .eq => W a (W x y)
    | .gt => W a (W x y)

/-- Rocq: `Notation.VWNotation.VF_normalize`. -/
def normalize : VForm → VForm
  | Z => Z
  | V a b => vnorm (normalize a) (normalize b)
  | W a b => wnorm (normalize a) (normalize b)

/-- Rocq: `Notation.VWNotation.Vnorm_isNormal`. -/
theorem vnorm_isNormal (a : VForm) : ∀ b : VForm, IsNormal a → IsNormal b → IsNormal (vnorm a b)
  | Z, ha, _ =>
    match a, ha with
    | W _ _, ha => ha
    | Z, _ => ⟨trivial, trivial, trivial⟩
    | V _ _, ha => ⟨ha, trivial, trivial⟩
  | V x y, ha, hb => by
    have hc := compare_correct a x
    show IsNormal (match compare a x with
      | .lt => V x y
      | .eq => V a (V x y)
      | .gt => V a (V x y))
    revert hc
    cases compare a x with
    | lt => exact fun _ => hb
    | eq => exact fun hc => ⟨ha, hb, hc.ge⟩
    | gt => exact fun hc => ⟨ha, hb, le_of_lt hc⟩
  | W x y, ha, hb => by
    have hc := compare_correct a (W x y)
    show IsNormal (match compare a (W x y) with
      | .lt => W x y
      | .eq => V a (W x y)
      | .gt => V a (W x y))
    revert hc
    cases compare a (W x y) with
    | lt => exact fun _ => hb
    | eq => exact fun hc => ⟨ha, hb, hc.ge⟩
    | gt => exact fun hc => ⟨ha, hb, le_of_lt hc⟩

/-- Rocq: `Notation.VWNotation.Wnorm_isNormal`. -/
theorem wnorm_isNormal (a : VForm) : ∀ b : VForm, IsNormal a → IsNormal b → IsNormal (wnorm a b)
  | Z, ha, hb => ⟨ha, hb, trivial⟩
  | V _ _, ha, hb => ⟨ha, hb, trivial⟩
  | W x y, ha, hb => by
    have hc := compare_correct a x
    show IsNormal (match compare a x with
      | .lt => W x y
      | .eq => W a (W x y)
      | .gt => W a (W x y))
    revert hc
    cases compare a x with
    | lt => exact fun _ => hb
    | eq => exact fun hc => ⟨ha, hb, hc.ge⟩
    | gt => exact fun hc => ⟨ha, hb, le_of_lt hc⟩

/-- Rocq: `Notation.VWNotation.Vnorm_reduce`. -/
theorem vnorm_reduce (a : VForm) : ∀ b : VForm, ClosReflTrans OneStepReduce (V a b) (vnorm a b)
  | Z =>
    match a with
    | W _ _ => .step (.redex .VW2)
    | Z => .refl _
    | V _ _ => .refl _
  | V x y => by
    show ClosReflTrans OneStepReduce _ (match compare a x with
      | .lt => V x y
      | .eq => V a (V x y)
      | .gt => V a (V x y))
    cases hc : compare a x with
    | lt => exact .step (.redex (.V hc))
    | eq => exact .refl _
    | gt => exact .refl _
  | W x y => by
    show ClosReflTrans OneStepReduce _ (match compare a (W x y) with
      | .lt => W x y
      | .eq => V a (W x y)
      | .gt => V a (W x y))
    cases hc : compare a (W x y) with
    | lt => exact .step (.redex (.VW hc))
    | eq => exact .refl _
    | gt => exact .refl _

/-- Rocq: `Notation.VWNotation.Wnorm_reduce`. -/
theorem wnorm_reduce (a : VForm) : ∀ b : VForm, ClosReflTrans OneStepReduce (W a b) (wnorm a b)
  | Z => .refl _
  | V _ _ => .refl _
  | W x y => by
    show ClosReflTrans OneStepReduce _ (match compare a x with
      | .lt => W x y
      | .eq => W a (W x y)
      | .gt => W a (W x y))
    cases hc : compare a x with
    | lt => exact .step (.redex (.W hc))
    | eq => exact .refl _
    | gt => exact .refl _

/-- Rocq: `Notation.VWNotation.VF_normalize_isNormal`. -/
theorem normalize_isNormal : ∀ x : VForm, IsNormal (normalize x)
  | Z => trivial
  | V a b => vnorm_isNormal _ _ (normalize_isNormal a) (normalize_isNormal b)
  | W a b => wnorm_isNormal _ _ (normalize_isNormal a) (normalize_isNormal b)

/-- Rocq: `Notation.VWNotation.reduce_many_Vcong1`. -/
theorem reduce_many_Vcong1 {x x' : VForm} (y : VForm) :
    ClosReflTrans OneStepReduce x x' → ClosReflTrans OneStepReduce (V x y) (V x' y)
  | .step h => .step (.vcong1 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (reduce_many_Vcong1 y h₁) (reduce_many_Vcong1 y h₂)

/-- Rocq: `Notation.VWNotation.reduce_many_Vcong2`. -/
theorem reduce_many_Vcong2 (x : VForm) {y y' : VForm} :
    ClosReflTrans OneStepReduce y y' → ClosReflTrans OneStepReduce (V x y) (V x y')
  | .step h => .step (.vcong2 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (reduce_many_Vcong2 x h₁) (reduce_many_Vcong2 x h₂)

/-- Rocq: `Notation.VWNotation.reduce_many_Wcong1`. -/
theorem reduce_many_Wcong1 {x x' : VForm} (y : VForm) :
    ClosReflTrans OneStepReduce x x' → ClosReflTrans OneStepReduce (W x y) (W x' y)
  | .step h => .step (.wcong1 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (reduce_many_Wcong1 y h₁) (reduce_many_Wcong1 y h₂)

/-- Rocq: `Notation.VWNotation.reduce_many_Wcong2`. -/
theorem reduce_many_Wcong2 (x : VForm) {y y' : VForm} :
    ClosReflTrans OneStepReduce y y' → ClosReflTrans OneStepReduce (W x y) (W x y')
  | .step h => .step (.wcong2 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (reduce_many_Wcong2 x h₁) (reduce_many_Wcong2 x h₂)

/-- Rocq: `Notation.VWNotation.VF_normalize_reduce`. -/
theorem normalize_reduce : ∀ x : VForm, ClosReflTrans OneStepReduce x (normalize x)
  | Z => .refl _
  | V a b => .trans (reduce_many_Vcong1 b (normalize_reduce a))
      (.trans (reduce_many_Vcong2 _ (normalize_reduce b)) (vnorm_reduce _ _))
  | W a b => .trans (reduce_many_Wcong1 b (normalize_reduce a))
      (.trans (reduce_many_Wcong2 _ (normalize_reduce b)) (wnorm_reduce _ _))

/-- Rocq: `Notation.VWNotation.Vnorm_equal`. -/
theorem vnorm_equal (a : VForm) : ∀ b : VForm, IsNormal a → IsNormal b →
    denote (vnorm a b) ≈ denote (V a b)
  | Z, _, _ =>
    match a with
    | W c d => equiv_symm (VW_collapse2 c d)
    | Z => equiv_refl _
    | V _ _ => equiv_refl _
  | V x y, _, _ => by
    have hc := compare_correct a x
    show denote (match compare a x with
      | .lt => V x y
      | .eq => V a (V x y)
      | .gt => V a (V x y)) ≈ _
    revert hc
    cases compare a x with
    | lt => exact fun hc => equiv_symm (V_collapse a x y hc)
    | eq => exact fun _ => equiv_refl _
    | gt => exact fun _ => equiv_refl _
  | W x y, _, _ => by
    have hc := compare_correct a (W x y)
    show denote (match compare a (W x y) with
      | .lt => W x y
      | .eq => V a (W x y)
      | .gt => V a (W x y)) ≈ _
    revert hc
    cases compare a (W x y) with
    | lt => exact fun hc => equiv_symm (VW_collapse a x y hc)
    | eq => exact fun _ => equiv_refl _
    | gt => exact fun _ => equiv_refl _

/-- Rocq: `Notation.VWNotation.Wnorm_equal`. -/
theorem wnorm_equal (a : VForm) : ∀ b : VForm, IsNormal a → IsNormal b →
    denote (wnorm a b) ≈ denote (W a b)
  | Z, _, _ => equiv_refl _
  | V _ _, _, _ => equiv_refl _
  | W x y, _, _ => by
    have hc := compare_correct a x
    show denote (match compare a x with
      | .lt => W x y
      | .eq => W a (W x y)
      | .gt => W a (W x y)) ≈ _
    revert hc
    cases compare a x with
    | lt => exact fun hc => equiv_symm (W_collapse a x y hc)
    | eq => exact fun _ => equiv_refl _
    | gt => exact fun _ => equiv_refl _

/-- Rocq: `Notation.VWNotation.VF_normalize_equal`. -/
theorem normalize_equal : ∀ x : VForm, denote (normalize x) ≈ denote x
  | Z => equiv_refl _
  | V a b => equiv_trans (vnorm_equal _ _ (normalize_isNormal a) (normalize_isNormal b))
      (veblen_onePlus_congr (normalize_equal a) (normalize_equal b))
  | W a b => equiv_trans (wnorm_equal _ _ (normalize_isNormal a) (normalize_isNormal b))
      (veblen_congr ε_normal.monotone (normalize_equal a) (normalize_equal b))

/-- Reduction is confluent. Rocq: `Notation.VWNotation.reduce_confluent`. -/
theorem reduce_confluent {a b c : VForm} (hb : ClosReflTrans OneStepReduce a b)
    (hc : ClosReflTrans OneStepReduce a c) :
    ∃ d, ClosReflTrans OneStepReduce b d ∧ ClosReflTrans OneStepReduce c d ∧
      ¬ ∃ z, OneStepReduce d z := by
  have hbc : normalize b = normalize c :=
    normal_forms_unique _ _ (normalize_isNormal b) (normalize_isNormal c)
      (equiv_trans (normalize_equal b) (equiv_trans (equiv_symm (step_reduce_sound hb))
        (equiv_trans (step_reduce_sound hc) (equiv_symm (normalize_equal c)))))
  exact ⟨normalize b, normalize_reduce b, hbc ▸ normalize_reduce c,
    (isNormal_no_reduce _).1 (normalize_isNormal b)⟩

/-- `x` reduces to the normal form `y`. Rocq: `Notation.VWNotation.normalizes`. -/
inductive Normalizes : VForm → VForm → Prop
  | normal {x : VForm} : (¬ ∃ y, OneStepReduce x y) → Normalizes x x
  | step {x y z : VForm} : OneStepReduce x y → Normalizes y z → Normalizes x z

/-- Rocq: `Notation.VWNotation.redex_size`. -/
theorem redex_size {x y : VForm} : Redex x y → size y < size x
  | .V (a := a) (b := b) (x := x) _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size b + size x + 1) (size a))
  | .W (a := a) (b := b) (x := x) _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size b + size x + 1) (size a))
  | .VW (a := a) (b := b) (c := c) _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size b + size c + 1) (size a))
  | .VW2 => Nat.lt_succ_self _

/-- Rocq: `Notation.VWNotation.one_step_reduce_size`. -/
theorem one_step_reduce_size {x y : VForm} : OneStepReduce x y → size y < size x
  | .redex h => redex_size h
  | .vcong1 h => Nat.succ_lt_succ (Nat.add_lt_add_right (one_step_reduce_size h) _)
  | .vcong2 h => Nat.succ_lt_succ (Nat.add_lt_add_left (one_step_reduce_size h) _)
  | .wcong1 h => Nat.succ_lt_succ (Nat.add_lt_add_right (one_step_reduce_size h) _)
  | .wcong2 h => Nat.succ_lt_succ (Nat.add_lt_add_left (one_step_reduce_size h) _)

/-- Reduction is strongly normalizing.
Rocq: `Notation.VWNotation.strongly_normalizing`. -/
theorem strongly_normalizing (x : VForm) : ∃ y, Normalizes x y := by
  suffices h : ∀ n x, size x < n → ∃ y, Normalizes x y from h _ x (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun x h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx
    match isNormalDec x with
    | isTrue h => exact ⟨x, .normal ((isNormal_no_reduce x).1 h)⟩
    | isFalse h =>
      obtain ⟨y, hy⟩ := (notIsNormal_reduce x).1 h
      obtain ⟨z, hz⟩ := ih y (Nat.lt_of_lt_of_le (one_step_reduce_size hy) (Nat.le_of_lt_succ hx))
      exact ⟨z, .step hy hz⟩

/-- Rocq: `Notation.VWNotation.normalizes_correct`. -/
theorem normalizes_correct {x y : VForm} : Normalizes x y → denote x ≈ denote y ∧ IsNormal y
  | .normal h => ⟨equiv_refl _, (isNormal_no_reduce _).2 h⟩
  | .step h₁ h₂ =>
    let ih := normalizes_correct h₂
    ⟨equiv_trans (one_step_reduce_sound h₁) ih.1, ih.2⟩

/-- Rocq: `Notation.VWNotation.normalizes_iff`. -/
theorem normalizes_iff (x y : VForm) :
    denote x ≈ denote y ↔ ∃ z, Normalizes x z ∧ Normalizes y z := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := strongly_normalizing x
    obtain ⟨z', hz'⟩ := strongly_normalizing y
    have e : z = z' :=
      normal_forms_unique _ _ (normalizes_correct hz).2 (normalizes_correct hz').2
        (equiv_trans (equiv_symm (normalizes_correct hz).1)
          (equiv_trans h (normalizes_correct hz').1))
    exact ⟨z, hz, e ▸ hz'⟩
  · rintro ⟨z, hz₁, hz₂⟩
    exact equiv_trans (normalizes_correct hz₁).1 (equiv_symm (normalizes_correct hz₂).1)

/-! ## Cantor decomposition and arithmetic -/

open CantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_decompose`. -/
def decompose : VForm → List VForm
  | Z => []
  | V a b => a :: decompose b
  | W a b => [W a b]

/-- Rocq: `Notation.VWNotation.VF_recompose`. -/
def recompose : List VForm → VForm
  | [] => Z
  | [x] =>
    match x with
    | Z => V Z Z
    | V c d => V (V c d) Z
    | W c d => W c d
  | x :: x' :: xs' => V x (recompose (x' :: xs'))

/-- Rocq: `Notation.VWNotation.VF_decompose_correct`. -/
theorem decompose_correct : ∀ x : VForm, IsNormal x →
    Each IsNormal (decompose x) ∧ CantorOrdered denote (decompose x) ∧
      denote x ≈ cantorDenote denote (decompose x)
  | Z, _ => ⟨trivial, trivial, equiv_refl _⟩
  | V a b, h =>
    let ih := decompose_correct b h.2.1
    ⟨⟨h.1, ih.1⟩,
      ⟨match b, h with
        | Z, _ => trivial
        | V _ _, h => h.2.2
        | W _ _, h => h.2.2, ih.2.1⟩,
      equiv_trans (veblen_onePlus _ (complete a) _ (complete b))
        (add_congr (equiv_refl _) ih.2.2)⟩
  | W a b, h =>
    ⟨⟨h, trivial⟩, ⟨trivial, trivial⟩,
      equiv_trans (equiv_symm (W_epsilon _ _ (complete a) (complete b))) (equiv_symm (add_zero _))⟩

/-- Rocq: `Notation.VWNotation.VF_recompose_correct`. -/
theorem recompose_correct : ∀ xs : List VForm, Each IsNormal xs → CantorOrdered denote xs →
    IsNormal (recompose xs) ∧ cantorDenote denote xs ≈ denote (recompose xs)
  | [], _, _ => ⟨trivial, equiv_refl _⟩
  | [x], hP, _ =>
    match x, hP with
    | Z, _ => ⟨⟨trivial, trivial, trivial⟩,
        equiv_symm (veblen_onePlus _ zero_complete _ zero_complete)⟩
    | V c d, hP => ⟨⟨hP.1, trivial, trivial⟩,
        equiv_symm (veblen_onePlus _ (complete (V c d)) _ zero_complete)⟩
    | W c d, hP => ⟨hP.1, equiv_trans (add_zero _) (W_epsilon _ _ (complete c) (complete d))⟩
  | x :: x' :: xs', hP, hord => by
    have ih := recompose_correct (x' :: xs') hP.2 hord.2
    refine ⟨⟨hP.1, ih.1, ?_⟩, equiv_trans (add_congr (equiv_refl _) ih.2)
      (equiv_symm (veblen_onePlus _ (complete x) _ (complete _)))⟩
    have hx' : denote x' ≤ denote x := hord.1
    cases xs' with
    | nil =>
      cases x' with
      | Z => exact zero_least _
      | V _ _ => exact hx'
      | W _ _ => exact hx'
    | cons _ _ => exact hx'

/-- Rocq: `Notation.VWNotation.VF_has_cantor_decomposition`. -/
def hasCantorDecomposition : HasCantorDecomposition denote IsNormal where
  compare := compare
  decompose := decompose
  recompose := recompose
  complete := complete
  compare_correct x y _ _ := compare_correct x y
  decompose_correct := decompose_correct
  recompose_correct := recompose_correct

/-- Rocq: `Notation.VWNotation.VF_succ`. -/
def succ : VForm → VForm := cantorSucc hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_add`. -/
def add : VForm → VForm → VForm := cantorAdd hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_mul`. -/
def mul : VForm → VForm → VForm := cantorMul hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_exp`. -/
def exp : VForm → VForm → VForm := cantorExp hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_one`. -/
def one : VForm := V Z Z

/-- Rocq: `Notation.VWNotation.VF_expOmega`. -/
def expOmega (x : VForm) : VForm := vnorm x Z

/-- Rocq: `Notation.VWNotation.VF_epsilon`. -/
def epsilon (x : VForm) : VForm := wnorm Z x

/-- Rocq: `Notation.VWNotation.VF_reflects_zero`. -/
theorem reflects_zero : Reflects VForm denote IsNormal .ord 0 Z := ⟨equiv_refl _, trivial⟩

/-- Rocq: `Notation.VWNotation.VF_reflects_one`. -/
theorem reflects_one : Reflects VForm denote IsNormal .ord 1 one :=
  ⟨equiv_symm (equiv_trans (veblen_onePlus _ zero_complete _ zero_complete)
      (equiv_trans (add_zero _) (pow_zero ω))), trivial, trivial, trivial⟩

/-- Rocq: `Notation.VWNotation.VF_succ_reflects`. -/
theorem succ_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Ordinal.succ succ :=
  cantor_succ_reflects hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_add_reflects`. -/
theorem add_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· + ·) add :=
  cantor_add_reflects hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_mul_reflects`. -/
theorem mul_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· * ·) mul :=
  cantor_mul_reflects hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_exp_reflects`. -/
theorem exp_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ^ ·) exp :=
  cantor_exp_reflects hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_epsilon_correct`. -/
theorem epsilon_correct (x : VForm) (hx : IsNormal x) : denote (epsilon x) ≈ ε (denote x) :=
  equiv_trans (wnorm_equal Z x trivial hx) (veblen_zero ε _)

/-- Rocq: `Notation.VWNotation.VF_epsilon_reflects`. -/
theorem epsilon_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) ε epsilon :=
  fun _ a ⟨hxa, ha⟩ =>
    ⟨equiv_trans (equiv_intro (ε_monotone hxa.le) (ε_monotone hxa.ge))
        (equiv_symm (epsilon_correct a ha)),
      wnorm_isNormal Z a trivial ha⟩

/-- Rocq: `Notation.VWNotation.VF_reflects_veblen`. -/
theorem reflects_veblen : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (veblen ε) wnorm :=
  fun _ a ⟨hxa, ha⟩ _ b ⟨hyb, hb⟩ =>
    ⟨equiv_trans (veblen_congr ε_normal.monotone hxa hyb) (equiv_symm (wnorm_equal a b ha hb)),
      wnorm_isNormal a b ha hb⟩

/-- `Γ 0` is complete. -/
private theorem Γ0_complete : Complete (Γ (0 : Ordinal.{0})) := Γ_normal.complete 0 zero_complete

/-- Rocq: `Notation.VWNotation.VF_below_Γ₀`. -/
theorem below_Γ₀ : ∀ x : VForm, denote x < Γ 0
  | Z => Γ_normal.nonzero 0
  | V a x =>
    veblen_collapse' onePlus_normal _ _ _ (complete a) (complete x) Γ0_complete
      (below_Γ₀ a) (below_Γ₀ x)
      (le_trans (veblen_monotone_func onePlus_normal powOmega_normal
          (fun i hi => onePlus_least_normal powOmega_normal i hi) _ _ Γ0_complete zero_complete)
        (Γ_fixpoints 0 zero_complete).ge)
  | W a x =>
    veblen_collapse' ε_normal _ _ _ (complete a) (complete x) Γ0_complete
      (below_Γ₀ a) (below_Γ₀ x)
      (le_trans (veblen_monotone_first ε_normal.monotone _ _ _ (Γalt 0 zero_complete).le)
        (le_trans (Con.enum_are_fixpoints (veblen_first_normal ε_normal) 0 zero_complete).ge
          (Γalt 0 zero_complete).ge))

/-- Rocq: `Notation.VWNotation.VF_limit`. -/
theorem VF_limit : IsLimit VF :=
  ⟨⟨Z⟩, fun a => ⟨V a (V Z Z),
    calc denote a
        ≤ ω ^ denote a := normal_inflationary powOmega_normal _ (complete a)
      _ ≈ ω ^ denote a + 0 := equiv_symm (add_zero _)
      _ < ω ^ denote a + denote (V Z Z) :=
          add_lt_add_left _ (veblen_nonzero onePlus_normal _ _)
      _ ≈ denote (V a (V Z Z)) := equiv_symm (veblen_onePlus _ (complete a) _ (complete _))⟩⟩

/-- `VF` is closed under `veblen ε · 0`. Rocq: `Notation.VWNotation.VF_veblen_closed`. -/
theorem VF_veblen_closed : veblen ε VF 0 ≤ VF :=
  calc veblen ε VF 0
      ≤ veblen ε (sup denote) 0 :=
        veblen_monotone_first ε_normal.monotone _ _ _ (limit_boundedSup VF_limit).le
    _ ≤ sup fun x => veblen ε (denote x) 0 := veblen_continuous_first ε_normal VForm denote Z
    _ ≤ VF := sup_least fun x => index_le VF (W x Z)

/-- Rocq: `Notation.VWNotation.VF_is_complete`. -/
theorem VF_is_complete : Complete VF :=
  ⟨fun a₁ a₂ =>
    match decideOrder a₁ a₂ with
    | .inl h => ⟨a₂, le_of_lt h, le_refl _⟩
    | .inr h => ⟨a₁, le_refl _, h⟩,
    .inl ⟨Z⟩, complete⟩

/-- The forms have order type `Γ 0`. Rocq: `Notation.VWNotation.VF_Γ₀`. -/
theorem VF_Γ₀ : VF ≈ Γ 0 :=
  equiv_intro (le_intro fun x => below_Γ₀ x)
    (le_trans (Γalt 0 zero_complete).le (le_trans
      (Con.enum_fixpoints_zero (veblen_first_normal ε_normal)).le
      (normal_fix_least (veblen_first_normal ε_normal) 0 VF VF_is_complete (zero_least _)
        VF_veblen_closed)))

/-! ## Interpolants -/

/-- `veblen (1 + ·)` is reflected by `vnorm`. -/
private theorem reflects_vnorm :
    Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (veblen fun y => 1 + y) vnorm :=
  fun _ a ⟨hxa, ha⟩ _ b ⟨hyb, hb⟩ =>
    ⟨equiv_trans (veblen_onePlus_congr hxa hyb) (equiv_symm (vnorm_equal a b ha hb)),
      vnorm_isNormal a b ha hb⟩

private theorem onePlus_has_interpolants : ∀ b, Complete b →
    HasInterpolants denote IsNormal b → HasInterpolants denote IsNormal (1 + b) := fun b _ hb =>
  onePlus_interpolants Z reflects_zero (add one) (fun x a h => add_reflects 1 one reflects_one x a h)
    b hb

/-- Rocq: `Notation.VWNotation.expOrd_interpolants`. -/
theorem expOrd_interpolants (b : Ordinal.{0}) (hb₁ : Complete b)
    (hb₂ : HasInterpolants denote IsNormal b) : HasInterpolants denote IsNormal (ω ^ b) :=
  (has_interpolants_eq_mor (equiv_trans (veblen_onePlus b hb₁ 0 zero_complete) (add_zero _))).1
    (veblen_interpolants_first hasCantorDecomposition (fun y => 1 + y) onePlus_normal
      onePlus_has_interpolants vnorm reflects_vnorm b hb₁ hb₂)

/-- Rocq: `Notation.VWNotation.ε_interpolants`. -/
theorem ε_interpolants (b : Ordinal.{0}) (hb₁ : Complete b)
    (hb₂ : HasInterpolants denote IsNormal b) : HasInterpolants denote IsNormal (ε b) :=
  enum_fix_has_interpolants hasCantorDecomposition powOmega powOmega_normal.complete
    (fun b hb₁ hb₂ => expOrd_interpolants b hb₁ hb₂) powOmega_normal.monotone
    (normal_inflationary powOmega_normal) (fun x => wnorm Z x)
    (fun _ a ⟨hxa, ha⟩ =>
      ⟨equiv_trans (equiv_intro (ε_monotone hxa.le) (ε_monotone hxa.ge))
          (equiv_symm (epsilon_correct a ha)),
        wnorm_isNormal Z a trivial ha⟩)
    b hb₁ hb₂

/-- Rocq: `Notation.VWNotation.VF_has_all_interpolants`. -/
theorem has_all_interpolants : HasAllInterpolants denote IsNormal := by
  intro x
  induction x with
  | Z =>
    exact fun _ => (has_interpolants_unfold _).2 fun i hi =>
      (lt_irrefl i (lt_of_lt_of_le hi (zero_least i))).elim
  | V a b iha ihb =>
    exact fun h => veblen_interpolants hasCantorDecomposition (fun y => 1 + y) onePlus_normal
      onePlus_has_interpolants vnorm reflects_vnorm a (denote b) h.1 (iha h.1) (complete b)
      (ihb h.2.1)
  | W a b iha ihb =>
    exact fun h => veblen_interpolants hasCantorDecomposition ε ε_normal
      (fun b hb₁ hb₂ => ε_interpolants b hb₁ hb₂) wnorm reflects_veblen a (denote b) h.1
      (iha h.1) (complete b) (ihb h.2.1)

/-- Rocq: `Notation.VWNotation.VF_nadd`. -/
def nadd : VForm → VForm → VForm := cantorNadd hasCantorDecomposition

/-- Rocq: `Notation.VWNotation.VF_reflects_nadd`. -/
theorem reflects_nadd : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ♯ ·) nadd :=
  cantor_nadd_reflects hasCantorDecomposition has_all_interpolants

/-- With the excluded middle, every ordinal below `Γ 0` has a normal form.
Rocq: `Notation.VWNotation.VW_has_enough_notations`. -/
theorem has_enough_notations (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < Γ 0 → ∃ v : VForm, sz v ≈ x := by
  intro x hx
  obtain ⟨a, ha⟩ := lt_elim (lt_of_lt_of_le hx VF_Γ₀.ge)
  obtain ⟨c, _, hc⟩ := has_interpolants_has_enough_notations em has_all_interpolants
    (normalize a) x (normalize_isNormal a) (le_trans ha (normalize_equal a).ge)
  exact ⟨c, hc⟩

/-- The same statement as `VW_has_enough_notations`.
Rocq: `Notation.VWNotation.VW_has_enough_notations'`. -/
theorem has_enough_notations' (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < Γ 0 → ∃ v : VForm, sz v ≈ x :=
  has_enough_notations em

/-! ## Sample computations -/

/-- `ε 0 < ε 1`, and `ω ^ ε 0 = ε 0` (checked by kernel reduction). -/
theorem sample_compare : compare (epsilon Z) (epsilon one) = .lt ∧
    compare (expOmega (epsilon Z)) (epsilon Z) = .eq := ⟨rfl, rfl⟩

end VForm

end ConstructiveOrdinals.VWNotation
