import ConstructiveOrdinals.Notation.CantorDecomposition
import ConstructiveOrdinals.Notation.CantorProduct
import ConstructiveOrdinals.AckermannTower
import ConstructiveOrdinals.Prelude.Relations

/-!
# A notation system for the large Ackermann ordinal

Port of `Ordinal/Notation/ATowerNotation.v`.

`V n a x` denotes `veblen (T n) a x`, where `T n = ackermannTower (1 + ·) n`
is the Ackermann tower over `1 + ·` at the level denoted by the form `n`.
The normal forms denote exactly the ordinals below the large Ackermann
ordinal. The development follows `Notation/ATowerFin`, whose levels are
natural numbers. Here the levels are forms themselves, compared with the same
comparison function.

Lean notes:

- Rocq's `VF_compare` has an inner `fix` on its second argument. It is the
  separate function `compareInner`, parameterised by the outer recursive
  calls.
- The inner `match` of Rocq's `VF_isNormal` on a `V` argument is the predicate
  `NormalTail`, and its dependence on the comparison of levels is summarised by
  `normalTail_V_iff`.
- `VF_compare_eq'` (the `EQ` case of the comparison) is stated for the port,
  alongside Rocq's `VF_compare_lt` and `VF_compare_gt`.
-/

namespace ConstructiveOrdinals.ATowerNotation

open Ordinal

/-- The Ackermann tower over `1 + ·` at level `o`. -/
abbrev T (o : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := ackermannTower (fun y => 1 + y) o

theorem T_normal {o : Ordinal.{0}} (h : Complete o) : NormalFunction (T o) :=
  ackermann_tower_normal _ o onePlus_normal h

/-- `T` is monotone in the level, pointwise. -/
theorem T_level_le {o o' : Ordinal.{0}} (h : o ≤ o') (x : Ordinal.{0}) : T o x ≤ T o' x :=
  ackermann_tower_monotone _ onePlus_normal.monotone _ _ _ _ h (le_refl x)

theorem T_mono (o : Ordinal.{0}) : ∀ x y, x ≤ y → T o x ≤ T o y := fun _ _ h =>
  ackermann_tower_monotone _ onePlus_normal.monotone _ _ _ _ (le_refl o) h

/-- `veblen (T o)` is monotone in the level. -/
theorem veblen_level_le {o o' : Ordinal.{0}} (h : o ≤ o') {a b x y : Ordinal.{0}} (hab : a ≤ b)
    (hxy : x ≤ y) : veblen (T o) a x ≤ veblen (T o') b y :=
  veblen_monotone_full (T_mono o') (T_level_le h) b y a x hab hxy

theorem veblen_level_congr {o o' : Ordinal.{0}} (h : o ≈ o') {a b x y : Ordinal.{0}} (hab : a ≈ b)
    (hxy : x ≈ y) : veblen (T o) a x ≈ veblen (T o') b y :=
  equiv_intro (veblen_level_le h.le hab.le hxy.le) (veblen_level_le h.ge hab.ge hxy.ge)

/-- Forms. Rocq: `Notation.ATowerNotation.VForm`. -/
inductive VForm : Type where
  | Z : VForm
  | V : VForm → VForm → VForm → VForm

namespace VForm

/-- Rocq: `Notation.ATowerNotation.VF_size`. -/
def size : VForm → Nat
  | Z => 0
  | V n x y => size n + size x + size y + 1

/-- Rocq: `Notation.ATowerNotation.VF_denote`. -/
def denote : VForm → Ordinal.{0}
  | Z => 0
  | V n a x => veblen (T (denote n)) (denote a) (denote x)

instance : Sized VForm := ⟨denote⟩

end VForm

/-- The ordinal of all forms. Rocq: `Notation.ATowerNotation.VF`. -/
def VF : Ordinal.{0} := mk VForm VForm.denote

namespace VForm

/-- Rocq: `Notation.ATowerNotation.VF_complete`. -/
theorem complete : ∀ x : VForm, Complete (denote x)
  | Z => zero_complete
  | V n a x => veblen_complete (T_normal (complete n)) (T_normal (complete n)).complete _
      (complete a) _ (complete x)

/-- `veblen (T n)` for a form `n` is normal. -/
theorem TV_normal (n : VForm) : NormalFunction (T (denote n)) := T_normal (complete n)

/-- Rocq: `Notation.ATowerNotation.VF_isZero`. -/
def isZero : (x : VForm) → PSum (x = Z) (0 < denote x)
  | Z => .inl rfl
  | V n _ _ => .inr (veblen_nonzero (TV_normal n) _ _)

/-- Values of `veblen (T o)` are values of `T o`. -/
private theorem tower_value {o : Ordinal.{0}} (ho : Complete o) {x y : Ordinal.{0}}
    (hx : Complete x) (hy : Complete y) : ∃ s, Complete s ∧ veblen (T o) x y ≈ T o s := by
  cases complete_zeroDec hx with
  | inl h =>
    exact ⟨y, hy, equiv_trans (veblen_congr (T_normal ho).monotone (equiv_intro h (zero_least _))
      (equiv_refl y)) (veblen_zero (T o) y)⟩
  | inr h =>
    exact ⟨veblen (T o) x y, veblen_complete (T_normal ho) (T_normal ho).complete _ hx _ hy,
      equiv_trans (equiv_symm (veblen_fixpoints (T_normal ho) 0 x y zero_complete hx hy h))
        (veblen_zero (T o) _)⟩

/-- Values of a higher level of the tower are fixpoints of `veblen (T o') · 0`
for lower levels `o'`. -/
theorem tower_fix {o o' : Ordinal.{0}} (ho : Complete o) (ho' : Complete o') (h : o' < o)
    {x y : Ordinal.{0}} (hx : Complete x) (hy : Complete y) :
    veblen (T o') (veblen (T o) x y) 0 ≤ veblen (T o) x y := by
  obtain ⟨s, hs, hv⟩ := tower_value ho hx hy
  exact le_trans (veblen_monotone_first (T_normal ho').monotone _ _ _ hv.le)
    (le_trans (ackermann_tower_fixpoint _ o o' s onePlus_normal ho ho' hs h) hv.ge)

/-- Rocq: `Notation.ATowerNotation.V_collapse`. -/
theorem V_collapse (n a b x : VForm) (h : denote a < denote b) :
    denote (V n a (V n b x)) ≈ denote (V n b x) :=
  veblen_fixpoints (TV_normal n) _ _ _ (complete a) (complete b) (complete x) h

/-- Rocq: `Notation.ATowerNotation.Vmn_collapse`. -/
theorem Vmn_collapse (n m a b c : VForm) (hmn : denote m < denote n)
    (h : denote a < denote (V n b c)) : denote (V m a (V n b c)) ≈ denote (V n b c) :=
  equiv_intro
    (veblen_collapse (TV_normal m) _ _ _ (complete a) (complete (V n b c)) (complete (V n b c)) h
      (le_refl _) (tower_fix (complete n) (complete m) hmn (complete b) (complete c)))
    (veblen_inflationary (TV_normal m) _ _ (complete (V n b c)))

/-- Rocq: `Notation.ATowerNotation.Vmn_collapse2`. -/
theorem Vmn_collapse2 (n m b c : VForm) (hmn : denote m < denote n) :
    denote (V m (V n b c) Z) ≈ denote (V n b c) :=
  equiv_intro (tower_fix (complete n) (complete m) hmn (complete b) (complete c))
    (normal_inflationary (veblen_first_normal (TV_normal m)) _ (complete (V n b c)))

/-! ## Comparison -/

/-- Compare `V m a x'` with a form, given the comparisons with `m`, `a` and
`x'`. The inner `fix` of Rocq's `VF_compare`. -/
def compareInner (x' : VForm) (recM recA recX : VForm → Ordering) : VForm → Ordering
  | Z => .gt
  | V n b y' =>
    match recM n with
    | .lt =>
      match recA (V n b y') with
      | .lt => recX (V n b y')
      | .eq =>
        match isZero x' with
        | .inl _ => .eq
        | .inr _ => .gt
      | .gt => .gt
    | .eq =>
      match recA b with
      | .lt => recX (V n b y')
      | .eq => recX y'
      | .gt => compareInner x' recM recA recX y'
    | .gt =>
      match compareInner x' recM recA recX b with
      | .lt => .lt
      | .eq =>
        match isZero y' with
        | .inl _ => .eq
        | .inr _ => .lt
      | .gt => compareInner x' recM recA recX y'

/-- Rocq: `Notation.ATowerNotation.VF_compare`. -/
def compare : VForm → VForm → Ordering
  | Z, Z => .eq
  | Z, V _ _ _ => .lt
  | V m a x', y => compareInner x' (compare m) (compare a) (compare x') y

/-- The unfolding of `compare` on two `V` forms. -/
private theorem compare_VV (m a x n b y : VForm) :
    compare (V m a x) (V n b y) =
      match compare m n with
      | .lt =>
        match compare a (V n b y) with
        | .lt => compare x (V n b y)
        | .eq =>
          match isZero x with
          | .inl _ => .eq
          | .inr _ => .gt
        | .gt => .gt
      | .eq =>
        match compare a b with
        | .lt => compare x (V n b y)
        | .eq => compare x y
        | .gt => compare (V m a x) y
      | .gt =>
        match compare (V m a x) b with
        | .lt => .lt
        | .eq =>
          match isZero y with
          | .inl _ => .eq
          | .inr _ => .lt
        | .gt => compare (V m a x) y := rfl

/-- Rocq: `Notation.ATowerNotation.VF_compare_lt`. -/
theorem VF_compare_lt (m n a x b y : VForm) (h : compare m n = .lt) :
    compare (V m a x) (V n b y) =
      match compare a (V n b y) with
      | .lt => compare x (V n b y)
      | .eq =>
        match isZero x with
        | .inl _ => .eq
        | .inr _ => .gt
      | .gt => .gt := by
  rw [compare_VV, h]

/-- The `EQ` case of the comparison of two `V` forms. -/
theorem VF_compare_eq' (m n a x b y : VForm) (h : compare m n = .eq) :
    compare (V m a x) (V n b y) =
      match compare a b with
      | .lt => compare x (V n b y)
      | .eq => compare x y
      | .gt => compare (V m a x) y := by
  rw [compare_VV, h]

/-- Rocq: `Notation.ATowerNotation.VF_compare_gt`. -/
theorem VF_compare_gt (m n a x b y : VForm) (h : compare m n = .gt) :
    compare (V m a x) (V n b y) =
      match compare (V m a x) b with
      | .lt => .lt
      | .eq =>
        match isZero y with
        | .inl _ => .eq
        | .inr _ => .lt
      | .gt => compare (V m a x) y := by
  rw [compare_VV, h]

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

/-- `a ≤ veblen (T m) a x`. -/
private theorem le_V (m a x : VForm) : denote a ≤ denote (V m a x) :=
  le_trans (normal_inflationary (veblen_first_normal (TV_normal m)) _ (complete a))
    (veblen_monotone (TV_normal m).monotone _ _ _ (zero_least _))

/-- Rocq: `Notation.ATowerNotation.VF_compare_correct`. -/
theorem compare_correct : ∀ x y : VForm, OrderingCorrect (compare x y) (denote x) (denote y) := by
  intro x
  induction x with
  | Z =>
    intro y
    cases y with
    | Z => exact equiv_refl _
    | V n _ _ => exact veblen_nonzero (TV_normal n) _ _
  | V m a x ihm iha ihx =>
    intro y
    induction y with
    | Z => exact veblen_nonzero (TV_normal m) _ _
    | V n b y _ ihb ihy =>
      have hmn := ihm n
      revert hmn
      cases hc : compare m n with
      | lt =>
        intro hmn
        rw [VF_compare_lt m n a x b y hc]
        have hab := iha (V n b y)
        revert hab
        cases compare a (V n b y) with
        | lt =>
          intro hab
          have hfix := tower_fix (complete n) (complete m) hmn (complete b) (complete y)
          have hx := ihx (V n b y)
          revert hx
          cases compare x (V n b y) with
          | lt =>
            exact fun hx => veblen_collapse' (TV_normal m) _ _ _ (complete a) (complete x)
              (complete (V n b y)) hab hx hfix
          | eq =>
            exact fun hx => equiv_intro
              (veblen_collapse (TV_normal m) _ _ _ (complete a) (complete x)
                (complete (V n b y)) hab hx.le hfix)
              (le_trans hx.ge (veblen_inflationary (TV_normal m) _ _ (complete x)))
          | gt =>
            exact fun hx => lt_of_lt_of_le hx (veblen_inflationary (TV_normal m) _ _ (complete x))
        | eq =>
          intro hab
          match isZero x with
          | .inl hx =>
            subst hx
            exact equiv_trans (veblen_congr (TV_normal m).monotone hab (equiv_refl _))
              (Vmn_collapse2 n m b y hmn)
          | .inr hx =>
            exact lt_of_le_of_lt hab.ge (veblen_subterm1 (TV_normal m) _ _ _ (complete a)
              (complete a) (complete x) hx (le_refl _))
        | gt => exact fun hab => lt_of_lt_of_le hab (le_V m a x)
      | eq =>
        intro hmn
        rw [VF_compare_eq' m n a x b y hc]
        have hlev : ∀ {p q : Ordinal.{0}}, veblen (T (denote n)) p q ≈ veblen (T (denote m)) p q :=
          fun {_ _} => veblen_level_congr (equiv_symm hmn) (equiv_refl _) (equiv_refl _)
        exact OrderingCorrect.congr (equiv_refl _) (equiv_symm hlev)
          (veblen_cmp (TV_normal m) (complete a) (complete b) (complete x) (complete y)
            (compare a b) _ _ _ (iha b) (OrderingCorrect.congr (equiv_refl _) hlev (ihx (V n b y)))
            (ihx y) ihy)
      | gt =>
        intro hmn
        rw [VF_compare_gt m n a x b y hc]
        revert ihb
        cases compare (V m a x) b with
        | lt => exact fun hb => lt_of_lt_of_le hb (le_V n b y)
        | eq =>
          intro hb
          match isZero y with
          | .inl hy =>
            subst hy
            exact equiv_trans (equiv_symm (Vmn_collapse2 m n a x hmn))
              (veblen_congr (TV_normal n).monotone hb (equiv_refl _))
          | .inr hy =>
            exact lt_of_le_of_lt hb.le (veblen_subterm1 (TV_normal n) _ _ _ (complete b)
              (complete b) (complete y) hy (le_refl _))
        | gt =>
          intro hb
          have hfix := tower_fix (complete m) (complete n) hmn (complete a) (complete x)
          revert ihy
          cases compare (V m a x) y with
          | lt =>
            exact fun hy => lt_of_lt_of_le hy (veblen_inflationary (TV_normal n) _ _ (complete y))
          | eq =>
            exact fun hy => equiv_intro
              (le_trans hy.le (veblen_inflationary (TV_normal n) _ _ (complete y)))
              (veblen_collapse (TV_normal n) _ _ _ (complete b) (complete y) (complete (V m a x))
                hb hy.ge hfix)
          | gt =>
            exact fun hy => veblen_collapse' (TV_normal n) _ _ _ (complete b) (complete y)
              (complete (V m a x)) hb hy hfix

/-- The order on forms is decidable. Rocq: `Notation.ATowerNotation.VF_decide_order`. -/
def decideOrder (x y : VForm) : PSum (sz x < sz y) (sz y ≤ sz x) :=
  match compare x y, compare_correct x y with
  | .lt, h => .inl h
  | .eq, h => .inr h.ge
  | .gt, h => .inr (le_of_lt h)

/-- Rocq: `Notation.ATowerNotation.VF_lt_correct`. -/
theorem lt_correct (x y : VForm) : compare x y = .lt ↔ denote x < denote y := by
  have h := compare_correct x y
  revert h
  cases compare x y with
  | lt => exact fun h => ⟨fun _ => h, fun _ => rfl⟩
  | eq => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h' h.ge)).elim⟩
  | gt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_trans h' h)).elim⟩

/-- Rocq: `Notation.ATowerNotation.VF_eq_correct`. -/
theorem eq_correct (x y : VForm) : compare x y = .eq ↔ denote x ≈ denote y := by
  have h := compare_correct x y
  revert h
  cases compare x y with
  | lt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h h'.ge)).elim⟩
  | eq => exact fun h => ⟨fun _ => h, fun _ => rfl⟩
  | gt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h h'.le)).elim⟩

/-- Rocq: `Notation.ATowerNotation.VF_le_correct`. -/
theorem le_correct (x y : VForm) : compare y x ≠ .lt ↔ denote x ≤ denote y := by
  have h := compare_correct y x
  revert h
  cases compare y x with
  | lt => exact fun h => ⟨fun h' => absurd rfl h', fun h' => (lt_irrefl _ (lt_of_lt_of_le h h')).elim⟩
  | eq => exact fun h => ⟨fun _ => h.ge, fun _ h' => nomatch h'⟩
  | gt => exact fun h => ⟨fun _ => le_of_lt h, fun _ h' => nomatch h'⟩

/-- Rocq: `Notation.ATowerNotation.VF_compare_refl`. -/
theorem compare_refl (x : VForm) : compare x x = .eq := (eq_correct x x).2 (equiv_refl _)

/-! ## Normal forms -/

/-- The condition on the second argument `b` of a normal form `V m a b`. The
inner `match` of Rocq's `VF_isNormal`. -/
def NormalTail (m a : VForm) : VForm → Prop
  | Z =>
    match a with
    | Z => True
    | V n _ _ => denote n ≤ denote m
  | V n x y =>
    match compare m n with
    | .lt => denote (V n x y) ≤ denote a
    | .eq => denote x ≤ denote a
    | .gt => True

/-- Rocq: `Notation.ATowerNotation.VF_isNormal`. -/
def IsNormal : VForm → Prop
  | Z => True
  | V m a b => IsNormal m ∧ IsNormal a ∧ IsNormal b ∧ NormalTail m a b

theorem normalTail_V_iff (m n a x y : VForm) :
    NormalTail m a (V n x y) ↔
      (denote m < denote n → denote (V n x y) ≤ denote a) ∧
        (denote m ≈ denote n → denote x ≤ denote a) := by
  show (match compare m n with
    | .lt => denote (V n x y) ≤ denote a
    | .eq => denote x ≤ denote a
    | .gt => True) ↔ _
  have hc := compare_correct m n
  revert hc
  cases compare m n with
  | lt =>
    intro hc
    exact ⟨fun t => ⟨fun _ => t, fun e => (lt_irrefl _ (lt_of_lt_of_le hc e.ge)).elim⟩,
      fun t => t.1 hc⟩
  | eq =>
    intro hc
    exact ⟨fun t => ⟨fun h => (lt_irrefl _ (lt_of_lt_of_le h hc.ge)).elim, fun _ => t⟩,
      fun t => t.2 hc⟩
  | gt =>
    intro hc
    exact ⟨fun _ => ⟨fun h => (lt_irrefl _ (lt_trans hc h)).elim,
      fun e => (lt_irrefl _ (lt_of_lt_of_le hc e.le)).elim⟩, fun _ => trivial⟩

/-- All three arguments are below the whole term.
Rocq: `Notation.ATowerNotation.subterm_shrink`. -/
def SubtermShrink : VForm → Prop
  | Z => True
  | V m a b => denote m < denote (V m a b) ∧ denote a < denote (V m a b) ∧
      denote b < denote (V m a b)

/-- Rocq: `Notation.ATowerNotation.shrink_lemma1`. -/
theorem shrink_lemma1 : ∀ x : VForm, denote x < T (denote x) 0
  | Z => ackermann_tower_nonzero _ _ _ onePlus_normal
  | V m a x => by
    have hV := complete (V m a x)
    have hT := (T_normal hV).complete 0 zero_complete
    have hm : denote m < denote (V m a x) :=
      lt_of_lt_of_le (shrink_lemma1 m) (le_trans (veblen_zero (T (denote m)) 0).ge
        (veblen_monotone_full (T_mono _) (fun _ => le_refl _) _ _ _ _ (zero_least _)
          (zero_least _)))
    refine veblen_collapse' (TV_normal m) _ _ _ (complete a) (complete x) hT ?_ ?_
      (ackermann_tower_fixpoint _ _ _ 0 onePlus_normal hV (complete m) zero_complete hm)
    · exact lt_of_lt_of_le (shrink_lemma1 a) (T_level_le (le_V m a x) 0)
    · exact lt_of_lt_of_le (shrink_lemma1 x)
        (T_level_le (veblen_inflationary (TV_normal m) _ _ (complete x)) 0)

/-- Rocq: `Notation.ATowerNotation.normal_subterm_shrink`. -/
theorem normal_subterm_shrink : ∀ x : VForm, IsNormal x → SubtermShrink x
  | Z, _ => trivial
  | V m a b, h => by
    have iha := normal_subterm_shrink a h.2.1
    have ihb := normal_subterm_shrink b h.2.2.1
    refine ⟨?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (shrink_lemma1 m) (le_trans (veblen_zero (T (denote m)) 0).ge
        (veblen_monotone_full (T_mono _) (fun _ => le_refl _) _ _ _ _ (zero_least _)
          (zero_least _)))
    · cases b with
      | Z =>
        match a, h, iha with
        | Z, _, _ => exact veblen_nonzero (TV_normal m) _ _
        | V n c d, h, iha =>
          exact lt_of_le_of_lt (veblen_level_le h.2.2.2 (le_refl _) (le_refl _))
            (veblen_subterm1_zero_nest (TV_normal m) _ _ _ (complete c) (complete d)
              (complete (V n c d)) iha.2.1 iha.2.2)
      | V n c d =>
        exact veblen_subterm1 (TV_normal m) _ _ _ (complete a) (complete a) (complete (V n c d))
          (veblen_nonzero (TV_normal n) _ _) (le_refl _)
    · cases b with
      | Z => exact veblen_nonzero (TV_normal m) _ _
      | V n c d =>
        have ht := (normalTail_V_iff m n a c d).1 h.2.2.2
        have hc := compare_correct m n
        revert hc
        cases compare m n with
        | lt =>
          exact fun hmn => lt_of_le_of_lt (ht.1 hmn) (veblen_subterm1 (TV_normal m) _ _ _
            (complete a) (complete a) (complete (V n c d)) (veblen_nonzero (TV_normal n) _ _)
            (le_refl _))
        | eq =>
          exact fun hmn => lt_of_le_of_lt (veblen_level_le hmn.ge (le_refl _) (le_refl _))
            (veblen_increasing' (TV_normal m) _ _ _ _ (complete c) (complete (V n c d))
              (ht.2 hmn) ihb.2.2)
        | gt =>
          exact fun hnm => veblen_collapse' (TV_normal n) _ _ _ (complete c) (complete d)
            (complete (V m a (V n c d)))
            (lt_of_lt_of_le ihb.2.1 (veblen_inflationary (TV_normal m) _ _ (complete (V n c d))))
            (lt_of_lt_of_le ihb.2.2 (veblen_inflationary (TV_normal m) _ _ (complete (V n c d))))
            (tower_fix (complete m) (complete n) hnm (complete a) (complete (V n c d)))

/-- `x ≤ y` is decidable, by comparison. -/
private def leDec (x y : VForm) : Decidable (denote x ≤ denote y) :=
  match compare x y, compare_correct x y with
  | .lt, h => isTrue (le_of_lt h)
  | .eq, h => isTrue h.le
  | .gt, h => isFalse fun h' => lt_irrefl _ (lt_of_lt_of_le h h')

private def normalTailDec (m a : VForm) : (b : VForm) → Decidable (NormalTail m a b)
  | Z =>
    match a with
    | Z => isTrue trivial
    | V n _ _ => leDec n m
  | V n x y => by
    show Decidable (match compare m n with
      | .lt => denote (V n x y) ≤ denote a
      | .eq => denote x ≤ denote a
      | .gt => True)
    cases compare m n with
    | lt => exact leDec (V n x y) a
    | eq => exact leDec x a
    | gt => exact isTrue trivial

/-- Normality is decidable. Rocq: `Notation.ATowerNotation.VF_isNormal_dec`. -/
def isNormalDec : (x : VForm) → Decidable (IsNormal x)
  | Z => isTrue trivial
  | V m a b =>
    match isNormalDec m with
    | isFalse hm => isFalse fun h => hm h.1
    | isTrue hm =>
      match isNormalDec a with
      | isFalse ha => isFalse fun h => ha h.2.1
      | isTrue ha =>
        match isNormalDec b with
        | isFalse hb => isFalse fun h => hb h.2.2.1
        | isTrue hb =>
          match normalTailDec m a b with
          | isTrue h => isTrue ⟨hm, ha, hb, h⟩
          | isFalse h => isFalse fun h' => h h'.2.2.2

instance : DecidablePred IsNormal := isNormalDec

/-! ## Normalization by rewriting -/

/-- Rocq: `Notation.ATowerNotation.redex`. -/
inductive Redex : VForm → VForm → Prop
  | V {m n a b x : VForm} : compare m n = .eq → compare a b = .lt →
      Redex (V m a (V n b x)) (V n b x)
  | Vmn1 {m n a b c : VForm} : compare m n = .lt → compare a (V n b c) = .lt →
      Redex (V m a (V n b c)) (V n b c)
  | Vmn2 {m n b c : VForm} : compare m n = .lt → Redex (V m (V n b c) Z) (V n b c)

/-- Rocq: `Notation.ATowerNotation.redex_sound`. -/
theorem redex_sound {x y : VForm} : Redex x y → denote x ≈ denote y
  | .V (n := n) (a := a) (b := b) (x := x) hmn h =>
    equiv_trans (veblen_level_congr ((eq_correct _ _).1 hmn) (equiv_refl _) (equiv_refl _))
      (V_collapse n a b x ((lt_correct _ _).1 h))
  | .Vmn1 hmn h => Vmn_collapse _ _ _ _ _ ((lt_correct _ _).1 hmn) ((lt_correct _ _).1 h)
  | .Vmn2 hmn => Vmn_collapse2 _ _ _ _ ((lt_correct _ _).1 hmn)

/-- Rocq: `Notation.ATowerNotation.one_step_reduce`. -/
inductive OneStepReduce : VForm → VForm → Prop
  | redex {x y : VForm} : Redex x y → OneStepReduce x y
  | cong0 {n n' x y : VForm} : OneStepReduce n n' → OneStepReduce (V n x y) (V n' x y)
  | cong1 {n x x' y : VForm} : OneStepReduce x x' → OneStepReduce (V n x y) (V n x' y)
  | cong2 {n x y y' : VForm} : OneStepReduce y y' → OneStepReduce (V n x y) (V n x y')

/-- Rocq: `Notation.ATowerNotation.one_step_reduce_sound`. -/
theorem one_step_reduce_sound {x y : VForm} : OneStepReduce x y → denote x ≈ denote y
  | .redex h => redex_sound h
  | .cong0 h => veblen_level_congr (one_step_reduce_sound h) (equiv_refl _) (equiv_refl _)
  | .cong1 (n := n) h =>
    veblen_congr (TV_normal n).monotone (one_step_reduce_sound h) (equiv_refl _)
  | .cong2 (n := n) h =>
    veblen_congr (TV_normal n).monotone (equiv_refl _) (one_step_reduce_sound h)

/-- Rocq: `Notation.ATowerNotation.step_reduce_sound`. -/
theorem step_reduce_sound {x y : VForm} :
    ClosReflTrans OneStepReduce x y → denote x ≈ denote y
  | .step h => one_step_reduce_sound h
  | .refl _ => equiv_refl _
  | .trans h₁ h₂ => equiv_trans (step_reduce_sound h₁) (step_reduce_sound h₂)

/-- Two normal forms at equivalent levels with the same denotation have
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

/-- A normal `V m a x` never denotes the same as `V n b y` when `m < n`. -/
private theorem ne_of_level_lt {m n a x b y : VForm} (hmn : denote m < denote n)
    (hx : IsNormal (V m a x)) (h : denote (V m a x) ≈ denote (V n b y)) : False := by
  have hs := normal_subterm_shrink _ hx
  refine lt_irrefl (denote (V m a x)) ?_
  calc denote (V m a x)
      < veblen (T (denote m)) (denote a) (denote (V n b y)) :=
        veblen_increasing (TV_normal m) _ (complete a) _ _ (complete (V n b y))
          (lt_of_lt_of_le hs.2.2 h.le)
    _ ≈ denote (V n b y) := Vmn_collapse n m a b y hmn (lt_of_lt_of_le hs.2.1 h.le)
    _ ≈ denote (V m a x) := equiv_symm h

/-- Rocq: `Notation.ATowerNotation.normal_forms_unique`. -/
theorem normal_forms_unique : ∀ x y : VForm, IsNormal x → IsNormal y →
    denote x ≈ denote y → x = y
  | Z, Z, _, _, _ => rfl
  | Z, V n _ _, _, _, h =>
    absurd (lt_of_lt_of_le (veblen_nonzero (TV_normal n) _ _) h.ge) (lt_irrefl 0)
  | V m _ _, Z, _, _, h =>
    absurd (lt_of_lt_of_le (veblen_nonzero (TV_normal m) _ _) h.le) (lt_irrefl 0)
  | V m a x, V n b y, hx, hy, h => by
    have hmn : denote m ≈ denote n := by
      have hc := compare_correct m n
      revert hc
      cases compare m n with
      | lt => exact fun hc => (ne_of_level_lt hc hx h).elim
      | eq => exact id
      | gt => exact fun hc => (ne_of_level_lt hc hy (equiv_symm h)).elim
    have e := normal_forms_unique m n hx.1 hy.1 hmn
    subst e
    obtain ⟨hab, hxy⟩ := same_head (TV_normal m) (normal_subterm_shrink _ hx).2.2
      (normal_subterm_shrink _ hy).2.2 h
    rw [normal_forms_unique a b hx.2.1 hy.2.1 hab, normal_forms_unique x y hx.2.2.1 hy.2.2.1 hxy]

/-- `1 + x`, computed by adding a leading `V Z Z`.
Rocq: `Notation.ATowerNotation.VF_onePlus`. -/
def onePlus : VForm → VForm
  | Z => V Z Z Z
  | V Z Z x' => V Z Z (onePlus x')
  | V Z (V c d e) x' => V Z (V c d e) x'
  | V (V k l o) a x' => V (V k l o) a x'

/-- `T 0` is normal. -/
private theorem T0_normal : NormalFunction (T 0) := T_normal zero_complete

/-- Rocq: `Notation.ATowerNotation.VF_onePlus_equal`. -/
theorem onePlus_equal : ∀ x : VForm, denote (onePlus x) ≈ 1 + denote x
  | Z => equiv_trans (veblen_zero (T 0) 0) (ackermann_tower_zero _ 0)
  | V Z Z x' =>
    equiv_trans (veblen_zero (T 0) _) (equiv_trans (ackermann_tower_zero _ _)
      (add_congr (equiv_refl 1) (equiv_trans (onePlus_equal x')
        (equiv_symm (equiv_trans (veblen_zero (T 0) _) (ackermann_tower_zero _ _))))))
  | V Z (V c d e) x' =>
    equiv_symm (onePlus_veblen T0_normal (veblen_nonzero (TV_normal c) _ _)
      (complete (V c d e)) (complete x'))
  | V (V k l o) a x' => by
    -- `V (V k l o) a x'` is a fixpoint of `veblen (T 0) · 0`
    have hV := complete (V (V k l o) a x')
    have h₀ : (0 : Ordinal.{0}) < denote (V k l o) := veblen_nonzero (TV_normal k) _ _
    refine equiv_symm (equiv_intro ?_ (le_add_left _ _))
    calc 1 + denote (V (V k l o) a x')
        ≤ 1 + veblen (T 0) (denote (V (V k l o) a x')) 0 :=
          add_le_add (le_refl 1) (normal_inflationary (veblen_first_normal T0_normal) _ hV)
      _ ≈ veblen (T 0) (denote (V (V k l o) a x')) 0 :=
          onePlus_veblen T0_normal (veblen_nonzero (TV_normal (V k l o)) _ _) hV zero_complete
      _ ≤ denote (V (V k l o) a x') :=
          tower_fix (complete (V k l o)) zero_complete h₀ (complete a) (complete x')

/-- Rocq: `Notation.ATowerNotation.VF_onePlus_normal`. -/
theorem onePlus_isNormal : ∀ x : VForm, IsNormal x → IsNormal (onePlus x)
  | Z, _ => ⟨trivial, trivial, trivial, trivial⟩
  | V Z Z x', h => by
    refine ⟨trivial, trivial, onePlus_isNormal x' h.2.2.1, ?_⟩
    have tl : ∀ y, NormalTail Z Z (V Z Z y) := fun y =>
      (normalTail_V_iff Z Z Z Z y).2 ⟨fun h => absurd h (lt_irrefl _), fun _ => le_refl _⟩
    cases x' with
    | Z => exact tl Z
    | V k c d =>
      cases k with
      | Z =>
        cases c with
        | Z => exact tl _
        | V _ _ _ => exact h.2.2.2
      | V _ _ _ => exact h.2.2.2
  | V Z (V _ _ _) _, h => h
  | V (V _ _ _) _ _, h => h

/-- Rocq: `Notation.ATowerNotation.one_step_cong_helper0`. -/
theorem one_step_cong_helper0 (n x y : VForm) :
    (∃ z, OneStepReduce n z) → ∃ z, OneStepReduce (V n x y) z := fun ⟨z, h⟩ =>
  ⟨V z x y, .cong0 h⟩

/-- Rocq: `Notation.ATowerNotation.one_step_cong_helper1`. -/
theorem one_step_cong_helper1 (n x y : VForm) :
    (∃ z, OneStepReduce x z) → ∃ z, OneStepReduce (V n x y) z := fun ⟨z, h⟩ =>
  ⟨V n z y, .cong1 h⟩

/-- Rocq: `Notation.ATowerNotation.one_step_cong_helper2`. -/
theorem one_step_cong_helper2 (n x y : VForm) :
    (∃ z, OneStepReduce y z) → ∃ z, OneStepReduce (V n x y) z := fun ⟨z, h⟩ =>
  ⟨V n x z, .cong2 h⟩

/-- Rocq: `Notation.ATowerNotation.multi_reduce_conj0`. -/
theorem multi_reduce_conj0 {m m' : VForm} (x y : VForm) :
    ClosReflTrans OneStepReduce m m' → ClosReflTrans OneStepReduce (V m x y) (V m' x y)
  | .step h => .step (.cong0 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (multi_reduce_conj0 x y h₁) (multi_reduce_conj0 x y h₂)

/-- Rocq: `Notation.ATowerNotation.multi_reduce_conj1`. -/
theorem multi_reduce_conj1 (m : VForm) {x x' : VForm} (y : VForm) :
    ClosReflTrans OneStepReduce x x' → ClosReflTrans OneStepReduce (V m x y) (V m x' y)
  | .step h => .step (.cong1 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (multi_reduce_conj1 m y h₁) (multi_reduce_conj1 m y h₂)

/-- Rocq: `Notation.ATowerNotation.multi_reduce_conj2`. -/
theorem multi_reduce_conj2 (m x : VForm) {y y' : VForm} :
    ClosReflTrans OneStepReduce y y' → ClosReflTrans OneStepReduce (V m x y) (V m x y')
  | .step h => .step (.cong2 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (multi_reduce_conj2 m x h₁) (multi_reduce_conj2 m x h₂)

private theorem not_reduce_Z : ¬ ∃ z, OneStepReduce Z z := fun ⟨_, h⟩ => by
  cases h with
  | redex h => cases h

/-- Rocq: `Notation.ATowerNotation.VF_notIsNormal_redex`. -/
theorem notIsNormal_redex : ∀ x : VForm, ¬ IsNormal x ↔ ∃ y, OneStepReduce x y := by
  intro x
  induction x with
  | Z => exact ⟨fun h => absurd trivial h, fun h => absurd h not_reduce_Z⟩
  | V m a b ihm iha ihb =>
    match isNormalDec m with
    | isFalse hm => exact ⟨fun _ => one_step_cong_helper0 m a b (ihm.1 hm), fun _ h => hm h.1⟩
    | isTrue hm =>
    match isNormalDec a with
    | isFalse ha => exact ⟨fun _ => one_step_cong_helper1 m a b (iha.1 ha), fun _ h => ha h.2.1⟩
    | isTrue ha =>
    match isNormalDec b with
    | isFalse hb =>
      exact ⟨fun _ => one_step_cong_helper2 m a b (ihb.1 hb), fun _ h => hb h.2.2.1⟩
    | isTrue hb =>
      constructor
      · intro hn
        cases b with
        | Z =>
          cases a with
          | Z => exact absurd ⟨hm, ha, hb, trivial⟩ hn
          | V n c d =>
            match decideOrder m n with
            | .inl h => exact ⟨V n c d, .redex (.Vmn2 ((lt_correct _ _).2 h))⟩
            | .inr h => exact absurd ⟨hm, ha, hb, h⟩ hn
        | V n c d =>
          have hc := compare_correct m n
          revert hc
          cases hmn : compare m n with
          | lt =>
            intro hc
            match decideOrder a (V n c d) with
            | .inl h => exact ⟨V n c d, .redex (.Vmn1 hmn ((lt_correct _ _).2 h))⟩
            | .inr h => exact absurd ⟨hm, ha, hb, (normalTail_V_iff m n a c d).2
                ⟨fun _ => h, fun e => (lt_irrefl _ (lt_of_lt_of_le hc e.ge)).elim⟩⟩ hn
          | eq =>
            intro hc
            match decideOrder a c with
            | .inl h => exact ⟨V n c d, .redex (.V hmn ((lt_correct _ _).2 h))⟩
            | .inr h => exact absurd ⟨hm, ha, hb, (normalTail_V_iff m n a c d).2
                ⟨fun h' => (lt_irrefl _ (lt_of_lt_of_le h' hc.ge)).elim, fun _ => h⟩⟩ hn
          | gt =>
            intro hc
            exact absurd ⟨hm, ha, hb, (normalTail_V_iff m n a c d).2
              ⟨fun h' => (lt_irrefl _ (lt_trans hc h')).elim,
                fun e => (lt_irrefl _ (lt_of_lt_of_le hc e.le)).elim⟩⟩ hn
      · rintro ⟨z, hz⟩ hn
        cases hz with
        | redex h =>
          cases h with
          | V hmn h =>
            exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h)
              (((normalTail_V_iff _ _ _ _ _).1 hn.2.2.2).2 ((eq_correct _ _).1 hmn)))
          | Vmn1 hmn h =>
            exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h)
              (((normalTail_V_iff _ _ _ _ _).1 hn.2.2.2).1 ((lt_correct _ _).1 hmn)))
          | Vmn2 hmn => exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 hmn) hn.2.2.2)
        | cong0 h => exact ihm.2 ⟨_, h⟩ hm
        | cong1 h => exact iha.2 ⟨_, h⟩ ha
        | cong2 h => exact ihb.2 ⟨_, h⟩ hb

/-- Rocq: `Notation.ATowerNotation.VF_isNormal_no_redex`. -/
theorem isNormal_no_redex (x : VForm) : IsNormal x ↔ ¬ ∃ y, OneStepReduce x y :=
  match isNormalDec x with
  | isTrue h => ⟨fun _ hr => (notIsNormal_redex x).2 hr h, fun _ => h⟩
  | isFalse h => ⟨fun h' => absurd h' h, fun hr => absurd ((notIsNormal_redex x).1 h) hr⟩

/-- Build `V m a b`, absorbing `a` where the result would not be normal.
Rocq: `Notation.ATowerNotation.Vnorm`. -/
def vnorm (m a : VForm) : VForm → VForm
  | Z =>
    match a with
    | Z => V m Z Z
    | V n c d =>
      match compare m n with
      | .lt => V n c d
      | .eq => V m (V n c d) Z
      | .gt => V m (V n c d) Z
  | V n x y =>
    match compare m n with
    | .lt =>
      match compare a (V n x y) with
      | .lt => V n x y
      | .eq => V m a (V n x y)
      | .gt => V m a (V n x y)
    | .eq =>
      match compare a x with
      | .lt => V n x y
      | .eq => V m a (V n x y)
      | .gt => V m a (V n x y)
    | .gt => V m a (V n x y)

/-- Rocq: `Notation.ATowerNotation.Vnorm_reduce`. -/
theorem vnorm_reduce (m a : VForm) : ∀ b : VForm,
    ClosReflTrans OneStepReduce (V m a b) (vnorm m a b)
  | Z =>
    match a with
    | Z => .refl _
    | V n c d => by
      show ClosReflTrans OneStepReduce _ (match compare m n with
        | .lt => V n c d
        | .eq => V m (V n c d) Z
        | .gt => V m (V n c d) Z)
      cases hmn : compare m n with
      | lt => exact .step (.redex (.Vmn2 hmn))
      | eq => exact .refl _
      | gt => exact .refl _
  | V n x y => by
    show ClosReflTrans OneStepReduce _ (match compare m n with
      | .lt =>
        match compare a (V n x y) with
        | .lt => V n x y
        | .eq => V m a (V n x y)
        | .gt => V m a (V n x y)
      | .eq =>
        match compare a x with
        | .lt => V n x y
        | .eq => V m a (V n x y)
        | .gt => V m a (V n x y)
      | .gt => V m a (V n x y))
    cases hmn : compare m n with
    | lt =>
      cases hc : compare a (V n x y) with
      | lt => exact .step (.redex (.Vmn1 hmn hc))
      | eq => exact .refl _
      | gt => exact .refl _
    | eq =>
      cases hc : compare a x with
      | lt => exact .step (.redex (.V hmn hc))
      | eq => exact .refl _
      | gt => exact .refl _
    | gt => exact .refl _

/-- Rocq: `Notation.ATowerNotation.Vnorm_normal`. -/
theorem vnorm_normal (m a b : VForm) (hm : IsNormal m) (ha : IsNormal a) (hb : IsNormal b) :
    IsNormal (vnorm m a b) := by
  cases b with
  | Z =>
    cases a with
    | Z => exact ⟨hm, trivial, trivial, trivial⟩
    | V n c d =>
      show IsNormal (match compare m n with
        | .lt => V n c d
        | .eq => V m (V n c d) Z
        | .gt => V m (V n c d) Z)
      have hc := compare_correct m n
      revert hc
      cases compare m n with
      | lt => exact fun _ => ha
      | eq => exact fun hc => ⟨hm, ha, trivial, hc.ge⟩
      | gt => exact fun hc => ⟨hm, ha, trivial, le_of_lt hc⟩
  | V n x y =>
    show IsNormal (match compare m n with
      | .lt =>
        match compare a (V n x y) with
        | .lt => V n x y
        | .eq => V m a (V n x y)
        | .gt => V m a (V n x y)
      | .eq =>
        match compare a x with
        | .lt => V n x y
        | .eq => V m a (V n x y)
        | .gt => V m a (V n x y)
      | .gt => V m a (V n x y))
    have hmn := compare_correct m n
    revert hmn
    cases compare m n with
    | lt =>
      intro hmn
      have hc := compare_correct a (V n x y)
      have ht : denote (V n x y) ≤ denote a → NormalTail m a (V n x y) := fun h =>
        (normalTail_V_iff m n a x y).2
          ⟨fun _ => h, fun e => (lt_irrefl _ (lt_of_lt_of_le hmn e.ge)).elim⟩
      revert hc
      cases compare a (V n x y) with
      | lt => exact fun _ => hb
      | eq => exact fun hc => ⟨hm, ha, hb, ht hc.ge⟩
      | gt => exact fun hc => ⟨hm, ha, hb, ht (le_of_lt hc)⟩
    | eq =>
      intro hmn
      have hc := compare_correct a x
      have ht : denote x ≤ denote a → NormalTail m a (V n x y) := fun h =>
        (normalTail_V_iff m n a x y).2
          ⟨fun h' => (lt_irrefl _ (lt_of_lt_of_le h' hmn.ge)).elim, fun _ => h⟩
      revert hc
      cases compare a x with
      | lt => exact fun _ => hb
      | eq => exact fun hc => ⟨hm, ha, hb, ht hc.ge⟩
      | gt => exact fun hc => ⟨hm, ha, hb, ht (le_of_lt hc)⟩
    | gt =>
      intro hnm
      exact ⟨hm, ha, hb, (normalTail_V_iff m n a x y).2
        ⟨fun h' => (lt_irrefl _ (lt_trans hnm h')).elim,
          fun e => (lt_irrefl _ (lt_of_lt_of_le hnm e.le)).elim⟩⟩

/-- Rocq: `Notation.ATowerNotation.Vnorm_equal`. -/
theorem vnorm_equal (m a b : VForm) (_ha : IsNormal a) (_hb : IsNormal b) :
    denote (vnorm m a b) ≈ denote (V m a b) :=
  equiv_symm (step_reduce_sound (vnorm_reduce m a b))

/-- Rocq: `Notation.ATowerNotation.VF_normalize`. -/
def normalize : VForm → VForm
  | Z => Z
  | V m a b => vnorm (normalize m) (normalize a) (normalize b)

/-- Rocq: `Notation.ATowerNotation.VF_normalize_isNormal`. -/
theorem normalize_isNormal : ∀ x : VForm, IsNormal (normalize x)
  | Z => trivial
  | V m a b => vnorm_normal _ _ _ (normalize_isNormal m) (normalize_isNormal a)
      (normalize_isNormal b)

/-- Rocq: `Notation.ATowerNotation.VF_normalize_reduce`. -/
theorem normalize_reduce : ∀ x : VForm, ClosReflTrans OneStepReduce x (normalize x)
  | Z => .refl _
  | V m a b => .trans (multi_reduce_conj0 a b (normalize_reduce m))
      (.trans (multi_reduce_conj1 _ b (normalize_reduce a))
        (.trans (multi_reduce_conj2 _ _ (normalize_reduce b)) (vnorm_reduce _ _ _)))

/-- Rocq: `Notation.ATowerNotation.VF_normalize_equal`. -/
theorem normalize_equal (x : VForm) : denote (normalize x) ≈ denote x :=
  equiv_symm (step_reduce_sound (normalize_reduce x))

/-- Reduction is confluent. Rocq: `Notation.ATowerNotation.reduce_confluent`. -/
theorem reduce_confluent {a b c : VForm} (hb : ClosReflTrans OneStepReduce a b)
    (hc : ClosReflTrans OneStepReduce a c) :
    ∃ d, ClosReflTrans OneStepReduce b d ∧ ClosReflTrans OneStepReduce c d ∧
      ¬ ∃ z, OneStepReduce d z := by
  have hbc : normalize b = normalize c :=
    normal_forms_unique _ _ (normalize_isNormal b) (normalize_isNormal c)
      (equiv_trans (normalize_equal b) (equiv_trans (equiv_symm (step_reduce_sound hb))
        (equiv_trans (step_reduce_sound hc) (equiv_symm (normalize_equal c)))))
  exact ⟨normalize b, normalize_reduce b, hbc ▸ normalize_reduce c,
    (isNormal_no_redex _).1 (normalize_isNormal b)⟩

/-- `x` reduces to the normal form `y`. Rocq: `Notation.ATowerNotation.normalizes`. -/
inductive Normalizes : VForm → VForm → Prop
  | normal {x : VForm} : (¬ ∃ y, OneStepReduce x y) → Normalizes x x
  | step {x y z : VForm} : OneStepReduce x y → Normalizes y z → Normalizes x z

/-- Rocq: `Notation.ATowerNotation.redex_size`. -/
theorem redex_size {x y : VForm} : Redex x y → size y < size x
  | .V (m := m) (a := a) (n := n) (b := b) (x := x) _ _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size n + size b + size x + 1) (size m + size a))
  | .Vmn1 (m := m) (a := a) (n := n) (b := b) (c := c) _ _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size n + size b + size c + 1) (size m + size a))
  | .Vmn2 (m := m) (n := n) (b := b) (c := c) _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size n + size b + size c + 1) (size m))

/-- Rocq: `Notation.ATowerNotation.one_step_reduce_size`. -/
theorem one_step_reduce_size {x y : VForm} : OneStepReduce x y → size y < size x
  | .redex h => redex_size h
  | .cong0 h =>
    Nat.succ_lt_succ (Nat.add_lt_add_right (Nat.add_lt_add_right (one_step_reduce_size h) _) _)
  | .cong1 h =>
    Nat.succ_lt_succ (Nat.add_lt_add_right (Nat.add_lt_add_left (one_step_reduce_size h) _) _)
  | .cong2 h => Nat.succ_lt_succ (Nat.add_lt_add_left (one_step_reduce_size h) _)

/-- Reduction is strongly normalizing.
Rocq: `Notation.ATowerNotation.strongly_normalizing`. -/
theorem strongly_normalizing (x : VForm) : ∃ y, Normalizes x y := by
  suffices h : ∀ n x, size x < n → ∃ y, Normalizes x y from h _ x (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun x h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx
    match isNormalDec x with
    | isTrue h => exact ⟨x, .normal ((isNormal_no_redex x).1 h)⟩
    | isFalse h =>
      obtain ⟨y, hy⟩ := (notIsNormal_redex x).1 h
      obtain ⟨z, hz⟩ := ih y (Nat.lt_of_lt_of_le (one_step_reduce_size hy) (Nat.le_of_lt_succ hx))
      exact ⟨z, .step hy hz⟩

/-- Rocq: `Notation.ATowerNotation.normalizes_correct`. -/
theorem normalizes_correct {x y : VForm} : Normalizes x y → denote x ≈ denote y ∧ IsNormal y
  | .normal h => ⟨equiv_refl _, (isNormal_no_redex _).2 h⟩
  | .step h₁ h₂ =>
    let ih := normalizes_correct h₂
    ⟨equiv_trans (one_step_reduce_sound h₁) ih.1, ih.2⟩

/-- Rocq: `Notation.ATowerNotation.normalizes_iff`. -/
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

/-- Level `0` of the tower is `1 + ·` up to equivalence.
Rocq: `Notation.ATowerNotation.veblen_ack0`. -/
theorem veblen_ack0 (x y : Ordinal.{0}) (hx : Complete x) (hy : Complete y) :
    veblen (T 0) x y ≈ ω ^ x + y :=
  equiv_trans
    (equiv_intro
      (veblen_monotone_func T0_normal onePlus_normal
        (fun i _ => (ackermann_tower_zero _ i).le) _ _ hx hy)
      (veblen_monotone_func onePlus_normal T0_normal
        (fun i _ => (ackermann_tower_zero _ i).ge) _ _ hx hy))
    (veblen_onePlus x hx y hy)

/-- Values of the higher levels of the tower are ε-numbers.
Rocq: `Notation.ATowerNotation.veblen_tower_epsilon`. -/
theorem veblen_tower_epsilon (n x y : Ordinal.{0}) (hn : Complete n) (hx : Complete x)
    (hy : Complete y) (h₀ : 0 < n) : ω ^ veblen (T n) x y ≈ veblen (T n) x y := by
  have hc := veblen_complete (T_normal hn) (T_normal hn).complete _ hx _ hy
  refine equiv_intro ?_ (normal_inflationary powOmega_normal _ hc)
  calc ω ^ veblen (T n) x y
      ≈ veblen (T 0) (veblen (T n) x y) 0 :=
        equiv_symm (equiv_trans (veblen_ack0 _ _ hc zero_complete) (add_zero _))
    _ ≤ veblen (T n) x y := tower_fix hn zero_complete h₀ hx hy

/-! ## Cantor decomposition and arithmetic -/

open CantorDecomposition Interpolants

/-- Rocq: `Notation.ATowerNotation.VF_decompose`. -/
def decompose : VForm → List VForm
  | Z => []
  | V Z a b => a :: decompose b
  | V (V k l o) a b => [V (V k l o) a b]

/-- Rocq: `Notation.ATowerNotation.VF_recompose`. -/
def recompose : List VForm → VForm
  | [] => Z
  | [x] =>
    match x with
    | Z => V Z Z Z
    | V Z c d => V Z (V Z c d) Z
    | V (V k l o) c d => V (V k l o) c d
  | x :: x' :: xs' => V Z x (recompose (x' :: xs'))

/-- Rocq: `Notation.ATowerNotation.VF_decompose_correct`. -/
theorem decompose_correct : ∀ x : VForm, IsNormal x →
    Each IsNormal (decompose x) ∧ CantorOrdered denote (decompose x) ∧
      denote x ≈ cantorDenote denote (decompose x)
  | Z, _ => ⟨trivial, trivial, equiv_refl _⟩
  | V Z a b, h =>
    let ih := decompose_correct b h.2.2.1
    ⟨⟨h.2.1, ih.1⟩,
      ⟨match b, h with
        | Z, _ => trivial
        | V Z _ _, h => ((normalTail_V_iff _ _ _ _ _).1 h.2.2.2).2 (equiv_refl _)
        | V (V k _ _) _ _, h => ((normalTail_V_iff _ _ _ _ _).1 h.2.2.2).1
            (veblen_nonzero (TV_normal k) _ _),
        ih.2.1⟩,
      equiv_trans (veblen_ack0 _ _ (complete a) (complete b))
        (add_congr (equiv_refl _) ih.2.2)⟩
  | V (V k l o) a b, h =>
    ⟨⟨h, trivial⟩, ⟨trivial, trivial⟩,
      equiv_trans (equiv_symm (veblen_tower_epsilon _ _ _ (complete (V k l o)) (complete a)
        (complete b) (veblen_nonzero (TV_normal k) _ _))) (equiv_symm (add_zero _))⟩

/-- Rocq: `Notation.ATowerNotation.VF_recompose_correct`. -/
theorem recompose_correct : ∀ xs : List VForm, Each IsNormal xs → CantorOrdered denote xs →
    IsNormal (recompose xs) ∧ cantorDenote denote xs ≈ denote (recompose xs)
  | [], _, _ => ⟨trivial, equiv_refl _⟩
  | [x], hP, _ =>
    match x, hP with
    | Z, _ => ⟨⟨trivial, trivial, trivial, trivial⟩,
        equiv_symm (veblen_ack0 _ _ zero_complete zero_complete)⟩
    | V Z c d, hP => ⟨⟨trivial, hP.1, trivial, le_refl _⟩,
        equiv_symm (veblen_ack0 _ _ (complete (V Z c d)) zero_complete)⟩
    | V (V k l o) c d, hP => ⟨hP.1, equiv_trans (add_zero _)
        (veblen_tower_epsilon _ _ _ (complete (V k l o)) (complete c) (complete d)
          (veblen_nonzero (TV_normal k) _ _))⟩
  | x :: x' :: xs', hP, hord => by
    have ih := recompose_correct (x' :: xs') hP.2 hord.2
    refine ⟨⟨trivial, hP.1, ih.1, ?_⟩, equiv_trans (add_congr (equiv_refl _) ih.2)
      (equiv_symm (veblen_ack0 _ _ (complete x) (complete _)))⟩
    have hx' : denote x' ≤ denote x := hord.1
    have eq0 : ∀ c d, denote c ≤ denote x → NormalTail Z x (V Z c d) := fun c d h =>
      (normalTail_V_iff Z Z x c d).2 ⟨fun h' => absurd h' (lt_irrefl _), fun _ => h⟩
    cases xs' with
    | nil =>
      cases x' with
      | Z => exact eq0 Z Z (zero_least _)
      | V k c d =>
        cases k with
        | Z => exact eq0 _ Z hx'
        | V k' l' o' =>
          exact (normalTail_V_iff Z (V k' l' o') x c d).2
            ⟨fun _ => hx', fun e => (lt_irrefl _ (lt_of_lt_of_le
              (veblen_nonzero (TV_normal k') _ _) e.ge)).elim⟩
    | cons _ _ => exact eq0 _ _ hx'

/-- Rocq: `Notation.ATowerNotation.VF_has_cantor_decomposition`. -/
def hasCantorDecomposition : HasCantorDecomposition denote IsNormal where
  compare := compare
  decompose := decompose
  recompose := recompose
  complete := complete
  compare_correct x y _ _ := compare_correct x y
  decompose_correct := decompose_correct
  recompose_correct := recompose_correct

/-- Rocq: `Notation.ATowerNotation.VF_succ`. -/
def succ : VForm → VForm := cantorSucc hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_add`. -/
def add : VForm → VForm → VForm := cantorAdd hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_mul`. -/
def mul : VForm → VForm → VForm := cantorMul hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_exp`. -/
def exp : VForm → VForm → VForm := cantorExp hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_succ_reflects`. -/
theorem succ_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Ordinal.succ succ :=
  cantor_succ_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_add_reflects`. -/
theorem add_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· + ·) add :=
  cantor_add_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_mul_reflects`. -/
theorem mul_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· * ·) mul :=
  cantor_mul_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_exp_reflects`. -/
theorem exp_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ^ ·) exp :=
  cantor_exp_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_ackermann_reflects`. -/
theorem ackermann_reflects :
    Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord ==> .ord)
      (fun n => veblen (T n)) vnorm :=
  fun _ m ⟨hnm, hm⟩ _ a ⟨hxa, ha⟩ _ b ⟨hyb, hb⟩ =>
    ⟨equiv_trans (veblen_level_congr hnm hxa hyb) (equiv_symm (vnorm_equal m a b ha hb)),
      vnorm_normal m a b hm ha hb⟩

/-- `veblen (T n)` is reflected by `vnorm n`, for a normal level `n`. -/
private theorem ackermann_reflects' {n : VForm} (hn : IsNormal n) :
    Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (veblen (T (denote n))) (vnorm n) :=
  ackermann_reflects (denote n) n ⟨equiv_refl _, hn⟩

/-- `1 + ·` preserves interpolants. -/
private theorem onePlus_has_interpolants (b : Ordinal.{0}) (hb : HasInterpolants denote IsNormal b) :
    HasInterpolants denote IsNormal (1 + b) :=
  onePlus_interpolants Z ⟨equiv_refl _, trivial⟩ (add (V Z Z Z))
    (fun x a h => add_reflects 1 (V Z Z Z)
      ⟨equiv_symm (equiv_trans (veblen_zero (T 0) 0) (equiv_trans (ackermann_tower_zero _ 0)
          (add_zero 1))), trivial, trivial, trivial, trivial⟩ x a h) b hb

/-- Rocq: `Notation.ATowerNotation.ackermann_tower_has_interpolants`. -/
theorem ackermann_tower_has_interpolants : ∀ (n : VForm) (b : Ordinal.{0}), IsNormal n →
    HasInterpolants denote IsNormal (denote n) → Complete b →
    HasInterpolants denote IsNormal b → HasInterpolants denote IsNormal (T (denote n) b) := by
  intro n
  -- induction on the denotation of `n`
  suffices H : ∀ (o : Ordinal.{0}) (n : VForm), denote n ≤ o → ∀ b : Ordinal.{0}, IsNormal n →
      HasInterpolants denote IsNormal (denote n) → Complete b →
      HasInterpolants denote IsNormal b → HasInterpolants denote IsNormal (T (denote n) b) from
    H _ n (le_refl _)
  intro o
  refine ltRec (motive := fun o => ∀ (n : VForm), denote n ≤ o → ∀ b : Ordinal.{0}, IsNormal n →
      HasInterpolants denote IsNormal (denote n) → Complete b →
      HasInterpolants denote IsNormal b → HasInterpolants denote IsNormal (T (denote n) b))
    (fun o ihn => ?_) o
  intro n hno b
  refine ltRec (motive := fun b => IsNormal n → HasInterpolants denote IsNormal (denote n) →
      Complete b → HasInterpolants denote IsNormal b →
      HasInterpolants denote IsNormal (T (denote n) b))
    (fun b ihb hn₁ hn₂ hb₁ hb₂ => (has_interpolants_unfold _).2 fun i hi => ?_) b
  dsimp only [T] at hi ⊢
  rw [ackermann_tower_unroll] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ :=
      (has_interpolants_unfold _).1 (onePlus_has_interpolants b hb₂) i hi
    refine ⟨y, hy₁, hy₂, ?_, hy₄⟩
    rw [ackermann_tower_unroll]
    exact lt_of_lt_of_le hy₃ (lub_le1 _ _)
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    have hTn := T_normal (complete n)
    -- the limit of `T n` below `b`
    have hb' : HasInterpolants denote IsNormal (lim fun x : b => T (denote n) (b x)) := by
      refine (has_interpolants_unfold _).2 fun i₀ hi₀ => ?_
      obtain ⟨z, hz⟩ := lt_elim hi₀
      obtain ⟨z', hz'₁, hz'₂, hz'₃, hz'₄⟩ :=
        (has_interpolants_unfold _).1 hb₂ (b z) (index_lt b z)
      have hw : denote (vnorm n Z z') ≈ T (denote n) (denote z') :=
        equiv_trans (vnorm_equal n Z z' trivial hz'₁) (veblen_zero _ _)
      obtain ⟨q, hq⟩ := lt_elim hz'₃
      exact ⟨vnorm n Z z', vnorm_normal n Z z' hn₁ trivial hz'₁,
        le_trans hz (le_trans (T_mono _ _ _ hz'₂) hw.ge),
        lt_intro (show (lim fun x : b => T (denote n) (b x)).Carrier from q)
          (le_trans hw.le (T_mono _ _ _ hq)),
        (has_interpolants_eq_mor hw).2 (ihb (denote z') hz'₃ hn₁ hn₂ (complete z') hz'₄)⟩
    have hb'c : Complete (lim fun x : b => T (denote n) (b x)) :=
      lim_complete (fun x => hTn.complete _ (complete_subord hb₁ x))
        (directed_monotone b _ (fun x y hxy => T_mono _ _ _ hxy) hb₁)
        (cast (complete_unfold b) hb₁).2.1
    obtain ⟨q, hq₁, hq₂, hq₃, hq₄⟩ :=
      (has_interpolants_unfold _).1 hn₂ ((denote n) j) (index_lt (denote n) j)
    have hTq := TV_normal q
    have hfix := fix_has_interpolants (fun d => veblen (T (denote q)) d 0)
      (veblen_first_normal hTq).complete
      (fun d hd₁ hd₂ => veblen_interpolants_first hasCantorDecomposition.complete (T (denote q)) hTq
        (fun b' hb'₁ hb'₂ => ihn (denote q) (lt_of_lt_of_le hq₃ hno) q (le_refl _) b' hq₁ hq₄
          hb'₁ hb'₂)
        (vnorm q) (ackermann_reflects' hq₁) d hd₁ hd₂) _ hb'c hb'
    have hi' : i < fixOrd (fun d => veblen (T (denote q)) d 0)
        (lim fun x : b => T (denote n) (b x)) :=
      lt_of_lt_of_le hi (fixOrd_monotone_func
        (fun d => veblen_level_le hq₂ (le_refl d) (le_refl 0))
        (fun x y hxy => veblen_monotone_first hTq.monotone _ _ _ hxy) _)
    obtain ⟨k, hk₁, hk₂, hk₃, hk₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
    refine ⟨k, hk₁, hk₂, ?_, hk₄⟩
    obtain ⟨z, hz⟩ := lt_elim hq₃
    rw [ackermann_tower_unroll]
    refine lt_of_lt_of_le hk₃ (le_trans ?_ (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun a' : (denote n).Carrier =>
      fixOrd (fun d => veblen (T ((denote n) a')) d 0) (lim fun x : b => T (denote n) (b x))) z)
    exact fixOrd_monotone_func (fun d => veblen_level_le hz (le_refl d) (le_refl 0))
      (fun x y hxy => veblen_monotone_first (T_normal (complete_subord (complete n) z)).monotone
        _ _ _ hxy) _

/-- Rocq: `Notation.ATowerNotation.VF_has_all_interpolants`. -/
theorem has_all_interpolants : HasAllInterpolants denote IsNormal := by
  intro x
  induction x with
  | Z =>
    exact fun _ => (has_interpolants_unfold _).2 fun i hi =>
      (lt_irrefl i (lt_of_lt_of_le hi (zero_least i))).elim
  | V n a b ihn iha ihb =>
    exact fun h => veblen_interpolants hasCantorDecomposition.complete (T (denote n)) (TV_normal n)
      (fun c hc₁ hc₂ => ackermann_tower_has_interpolants n c h.1 (ihn h.1) hc₁ hc₂) (vnorm n)
      (ackermann_reflects' h.1) a (denote b) h.2.1 (iha h.2.1) (complete b) (ihb h.2.2.1)

/-- Rocq: `Notation.ATowerNotation.VF_nadd`. -/
def nadd : VForm → VForm → VForm := cantorNadd hasCantorDecomposition

/-- Rocq: `Notation.ATowerNotation.VF_reflects_nadd`. -/
theorem reflects_nadd : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ♯ ·) nadd :=
  cantor_nadd_reflects hasCantorDecomposition

/-- The natural product, computed on Cantor normal forms.
Rocq: `Notation.ATowerNotation.VF_nmul`. -/
def nmul : VForm → VForm → VForm := CantorProduct.cantorNmul hasCantorDecomposition

/-- Constructively, using interpolants. Rocq: `Notation.ATowerNotation.VF_reflects_nmul`. -/
theorem reflects_nmul :
    Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) NaturalProduct.nmul nmul :=
  CantorProduct.cantor_nmul_reflects hasCantorDecomposition has_all_interpolants

/-! ## Order type -/

private theorem T_first_normal : NormalFunction fun a : Ordinal.{0} => T a 0 :=
  ackermann_tower_normal_first _ onePlus_normal

/-- Rocq: `Notation.ATowerNotation.LAO_complete`. -/
theorem LAO_complete : Complete (LargeAckermannOrdinal.{0}) :=
  normal_fix_complete 0 zero_complete (normal_inflationary T_first_normal)
    T_first_normal.monotone T_first_normal.complete

/-- `LAO ≈ T LAO 0`. -/
private theorem LAO_fixpoint : LargeAckermannOrdinal.{0} ≈ T LargeAckermannOrdinal 0 :=
  normal_fixpoint T_first_normal 0 zero_complete

/-- Rocq: `Notation.ATowerNotation.VF_below_LAO`. -/
theorem below_LAO : ∀ x : VForm, denote x < LargeAckermannOrdinal
  | Z => lt_of_lt_of_le (ackermann_tower_nonzero _ _ _ onePlus_normal) LAO_fixpoint.ge
  | V m a x =>
    veblen_collapse' (TV_normal m) _ _ _ (complete a) (complete x) LAO_complete
      (below_LAO a) (below_LAO x)
      (le_trans (veblen_monotone_first (TV_normal m).monotone _ _ _ LAO_fixpoint.le)
        (le_trans (ackermann_tower_fixpoint _ _ _ 0 onePlus_normal LAO_complete (complete m)
          zero_complete (below_LAO m)) LAO_fixpoint.ge))

/-- Rocq: `Notation.ATowerNotation.VF_is_complete`. -/
theorem VF_is_complete : Complete VF :=
  ⟨fun a₁ a₂ =>
    match decideOrder a₁ a₂ with
    | .inl h => ⟨a₂, le_of_lt h, le_refl _⟩
    | .inr h => ⟨a₁, le_refl _, h⟩,
    .inl ⟨Z⟩, complete⟩

end VForm

open VForm in
/-- The forms have order type the large Ackermann ordinal.
Rocq: `Notation.ATowerNotation.VF_LAO`. -/
theorem VF_LAO : VF ≈ LargeAckermannOrdinal := by
  refine equiv_intro (le_intro fun x => below_LAO x) ?_
  refine normal_fix_least T_first_normal 0 VF VF_is_complete (zero_least _) ?_
  refine le_trans (normal_ord_decompose VF (fun i => T i 0) VF_is_complete
    (lt_intro (show VF.Carrier from Z) (zero_least _)) T_first_normal).le (sup_least fun x => ?_)
  have hs := succ_reflects (denote (normalize x)) (normalize x)
    ⟨equiv_refl _, normalize_isNormal x⟩
  refine le_trans ?_ (index_le VF (V (VForm.succ (normalize x)) Z Z))
  show T (Ordinal.succ (denote x)) 0 ≤ veblen (T (denote (VForm.succ (normalize x)))) 0 0
  refine le_trans ?_ (veblen_zero _ 0).ge
  exact T_level_le (le_trans (succ_monotone (normalize_equal x).ge) hs.1.le) 0

namespace VForm

open CantorDecomposition Interpolants

/-- With the excluded middle, every ordinal below the large Ackermann ordinal
has a normal form. Rocq: `Notation.ATowerNotation.VF_has_enough_notations`. -/
theorem has_enough_notations (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < LargeAckermannOrdinal → ∃ v : VForm, sz v ≈ x := by
  intro x hx
  obtain ⟨a, ha⟩ := lt_elim (lt_of_lt_of_le hx VF_LAO.ge)
  obtain ⟨c, _, hc⟩ := has_interpolants_has_enough_notations em has_all_interpolants
    (normalize a) x (normalize_isNormal a) (le_trans ha (normalize_equal a).ge)
  exact ⟨c, hc⟩

/-! ## Sample computations -/

/-- Levels compare as forms (checked by kernel reduction). -/
theorem sample_compare : compare (V (V Z Z Z) Z Z) (V (V (V Z Z Z) Z Z) Z Z) = .lt ∧
    compare (vnorm Z (V (V Z Z Z) Z Z) Z) (V (V Z Z Z) Z Z) = .eq := ⟨rfl, rfl⟩

end VForm

end ConstructiveOrdinals.ATowerNotation
