import ConstructiveOrdinals.Notation.CantorDecomposition
import ConstructiveOrdinals.AckermannTower
import ConstructiveOrdinals.Prelude.Relations

/-!
# A notation system for the small Ackermann ordinal

Port of `Ordinal/Notation/ATowerFinNotation.v`.

`V n a x` denotes `veblen (T n) a x`, where `T n = ackermannTowerFin (1 + ·) n`
is the `n`th level of the finite Ackermann tower over `1 + ·`. The normal forms
denote exactly the ordinals below the small Ackermann ordinal. As in
`Notation/V` and `Notation/VW`, normalization is a confluent, strongly
normalizing rewriting system, and the system has a Cantor decomposition, so it
supports Cantor arithmetic and natural sums. With the excluded middle, it has
a notation for every ordinal below the small Ackermann ordinal.

Lean notes:

- Rocq's `VF_compare` has an inner `fix` on its second argument. It is the
  separate function `compareInner`, parameterised by the outer recursive
  calls.
- The inner `match` of Rocq's `VF_isNormal` on a `V` argument is the predicate
  `NormalTail`. Its dependence on `nat_compare` is summarised by
  `normalTail_V_iff`.
-/

namespace ConstructiveOrdinals.ATowerFinNotation

open Ordinal

/-- The `n`th level of the finite Ackermann tower over `1 + ·`. -/
abbrev T (n : Nat) : Ordinal.{0} → Ordinal.{0} := ackermannTowerFin (fun y => 1 + y) n

theorem T_normal (n : Nat) : NormalFunction (T n) :=
  ackermann_tower_fin_normal n _ onePlus_normal

/-- Forms. Rocq: `Notation.ATowerFinNotation.VForm`. -/
inductive VForm : Type where
  | Z : VForm
  | V : Nat → VForm → VForm → VForm

namespace VForm

/-- Rocq: `Notation.ATowerFinNotation.VF_size`. -/
def size : VForm → Nat
  | Z => 0
  | V _ x y => size x + size y + 1

/-- Rocq: `Notation.ATowerFinNotation.VF_denote`. -/
def denote : VForm → Ordinal.{0}
  | Z => 0
  | V n a x => veblen (T n) (denote a) (denote x)

instance : Sized VForm := ⟨denote⟩

end VForm

/-- The ordinal of all forms. Rocq: `Notation.ATowerFinNotation.VF`. -/
def VF : Ordinal.{0} := mk VForm VForm.denote

namespace VForm

/-- Rocq: `Notation.ATowerFinNotation.VF_complete`. -/
theorem complete : ∀ x : VForm, Complete (denote x)
  | Z => zero_complete
  | V n a x => veblen_complete (T_normal n) (T_normal n).complete _ (complete a) _ (complete x)

/-- Rocq: `Notation.ATowerFinNotation.VF_isZero`. -/
def isZero : (x : VForm) → PSum (x = Z) (0 < denote x)
  | Z => .inl rfl
  | V n _ _ => .inr (veblen_nonzero (T_normal n) _ _)

/-- Values of `veblen (T n)` are values of `T n`. -/
private theorem tower_value (n : Nat) {x y : Ordinal.{0}} (hx : Complete x) (hy : Complete y) :
    ∃ s, Complete s ∧ veblen (T n) x y ≈ T n s := by
  cases complete_zeroDec hx with
  | inl h =>
    exact ⟨y, hy, equiv_trans (veblen_congr (T_normal n).monotone (equiv_intro h (zero_least _))
      (equiv_refl y)) (veblen_zero (T n) y)⟩
  | inr h =>
    exact ⟨veblen (T n) x y, veblen_complete (T_normal n) (T_normal n).complete _ hx _ hy,
      equiv_trans (equiv_symm (veblen_fixpoints (T_normal n) 0 x y zero_complete hx hy h))
        (veblen_zero (T n) _)⟩

/-- Values of a higher level of the tower are fixpoints of `veblen (T m) · 0`
for lower levels `m`. -/
theorem tower_fix {m n : Nat} (hmn : m < n) {x y : Ordinal.{0}} (hx : Complete x)
    (hy : Complete y) : veblen (T m) (veblen (T n) x y) 0 ≤ veblen (T n) x y := by
  obtain ⟨s, hs, h⟩ := tower_value n hx hy
  exact le_trans (veblen_monotone_first (T_normal m).monotone _ _ _ h.le)
    (le_trans (ackermann_tower_fin_fixpoints n _ m s onePlus_normal hmn hs) h.ge)

/-- Rocq: `Notation.ATowerFinNotation.V_collapse`. -/
theorem V_collapse (n : Nat) (a b x : VForm) (h : denote a < denote b) :
    denote (V n a (V n b x)) ≈ denote (V n b x) :=
  veblen_fixpoints (T_normal n) _ _ _ (complete a) (complete b) (complete x) h

/-- Rocq: `Notation.ATowerFinNotation.Vmn_collapse`. -/
theorem Vmn_collapse (n m : Nat) (a b c : VForm) (hmn : m < n) (h : denote a < denote (V n b c)) :
    denote (V m a (V n b c)) ≈ denote (V n b c) :=
  equiv_intro
    (veblen_collapse (T_normal m) _ _ _ (complete a) (complete (V n b c)) (complete (V n b c)) h
      (le_refl _) (tower_fix hmn (complete b) (complete c)))
    (veblen_inflationary (T_normal m) _ _ (complete (V n b c)))

/-- Rocq: `Notation.ATowerFinNotation.Vmn_collapse2`. -/
theorem Vmn_collapse2 (n m : Nat) (b c : VForm) (hmn : m < n) :
    denote (V m (V n b c) Z) ≈ denote (V n b c) :=
  equiv_intro (tower_fix hmn (complete b) (complete c))
    (normal_inflationary (veblen_first_normal (T_normal m)) _ (complete (V n b c)))

/-! ## Comparison -/

/-- Compare `V m a x'` with a form, given the comparisons with `a` and with
`x'`. The inner `fix` of Rocq's `VF_compare`. -/
def compareInner (m : Nat) (x' : VForm) (recA recX : VForm → Ordering) : VForm → Ordering
  | Z => .gt
  | V n b y' =>
    match natCompare m n with
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
      | .gt => compareInner m x' recA recX y'
    | .gt =>
      match compareInner m x' recA recX b with
      | .lt => .lt
      | .eq =>
        match isZero y' with
        | .inl _ => .eq
        | .inr _ => .lt
      | .gt => compareInner m x' recA recX y'

/-- Rocq: `Notation.ATowerFinNotation.VF_compare`. -/
def compare : VForm → VForm → Ordering
  | Z, Z => .eq
  | Z, V _ _ _ => .lt
  | V m a x', y => compareInner m x' (compare a) (compare x') y

theorem natCompare_of_lt {m n : Nat} (h : m < n) : natCompare m n = .lt := by
  have hc := natCompare_correct m n
  revert hc
  cases natCompare m n with
  | lt => exact fun _ => rfl
  | eq => exact fun hc => absurd (hc ▸ h) (Nat.lt_irrefl _)
  | gt => exact fun hc => absurd (Nat.lt_trans h hc) (Nat.lt_irrefl _)

theorem natCompare_self (m : Nat) : natCompare m m = .eq := by
  have hc := natCompare_correct m m
  revert hc
  cases natCompare m m with
  | lt => exact fun hc => absurd hc (Nat.lt_irrefl _)
  | eq => exact fun _ => rfl
  | gt => exact fun hc => absurd hc (Nat.lt_irrefl _)

theorem natCompare_of_gt {m n : Nat} (h : n < m) : natCompare m n = .gt := by
  have hc := natCompare_correct m n
  revert hc
  cases natCompare m n with
  | lt => exact fun hc => absurd (Nat.lt_trans h hc) (Nat.lt_irrefl _)
  | eq => exact fun hc => absurd (hc ▸ h) (Nat.lt_irrefl _)
  | gt => exact fun _ => rfl

/-- Rocq: `Notation.ATowerFinNotation.VF_compare_lt`. -/
theorem VF_compare_lt (m n : Nat) (a x b y : VForm) (h : m < n) :
    compare (V m a x) (V n b y) =
      match compare a (V n b y) with
      | .lt => compare x (V n b y)
      | .eq =>
        match isZero x with
        | .inl _ => .eq
        | .inr _ => .gt
      | .gt => .gt := by
  show (match natCompare m n with
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
      | .gt => compare (V m a x) y) = _
  rw [natCompare_of_lt h]

/-- Rocq: `Notation.ATowerFinNotation.VF_compare_eq`. -/
theorem VF_compare_eq (m : Nat) (a x b y : VForm) :
    compare (V m a x) (V m b y) =
      match compare a b with
      | .lt => compare x (V m b y)
      | .eq => compare x y
      | .gt => compare (V m a x) y := by
  show (match natCompare m m with
    | .lt =>
      match compare a (V m b y) with
      | .lt => compare x (V m b y)
      | .eq =>
        match isZero x with
        | .inl _ => .eq
        | .inr _ => .gt
      | .gt => .gt
    | .eq =>
      match compare a b with
      | .lt => compare x (V m b y)
      | .eq => compare x y
      | .gt => compare (V m a x) y
    | .gt =>
      match compare (V m a x) b with
      | .lt => .lt
      | .eq =>
        match isZero y with
        | .inl _ => .eq
        | .inr _ => .lt
      | .gt => compare (V m a x) y) = _
  rw [natCompare_self m]

/-- Rocq: `Notation.ATowerFinNotation.VF_compare_gt`. -/
theorem VF_compare_gt (m n : Nat) (a x b y : VForm) (h : n < m) :
    compare (V m a x) (V n b y) =
      match compare (V m a x) b with
      | .lt => .lt
      | .eq =>
        match isZero y with
        | .inl _ => .eq
        | .inr _ => .lt
      | .gt => compare (V m a x) y := by
  show (match natCompare m n with
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
      | .gt => compare (V m a x) y) = _
  rw [natCompare_of_gt h]

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
private theorem le_V (m : Nat) (a x : VForm) : denote a ≤ denote (V m a x) :=
  le_trans (normal_inflationary (veblen_first_normal (T_normal m)) _ (complete a))
    (veblen_monotone (T_normal m).monotone _ _ _ (zero_least _))

/-- Rocq: `Notation.ATowerFinNotation.VF_compare_correct`. -/
theorem compare_correct : ∀ x y : VForm, OrderingCorrect (compare x y) (denote x) (denote y) := by
  intro x
  induction x with
  | Z =>
    intro y
    cases y with
    | Z => exact equiv_refl _
    | V n _ _ => exact veblen_nonzero (T_normal n) _ _
  | V m a x iha ihx =>
    intro y
    induction y with
    | Z => exact veblen_nonzero (T_normal m) _ _
    | V n b y ihb ihy =>
      have hmn := natCompare_correct m n
      revert hmn
      cases natCompare m n with
      | lt =>
        intro hmn
        rw [VF_compare_lt m n a x b y hmn]
        have hab := iha (V n b y)
        revert hab
        cases compare a (V n b y) with
        | lt =>
          intro hab
          have hx := ihx (V n b y)
          revert hx
          cases compare x (V n b y) with
          | lt =>
            exact fun hx => veblen_collapse' (T_normal m) _ _ _ (complete a) (complete x)
              (complete (V n b y)) hab hx (tower_fix hmn (complete b) (complete y))
          | eq =>
            exact fun hx => equiv_intro
              (veblen_collapse (T_normal m) _ _ _ (complete a) (complete x) (complete (V n b y))
                hab hx.le (tower_fix hmn (complete b) (complete y)))
              (le_trans hx.ge (veblen_inflationary (T_normal m) _ _ (complete x)))
          | gt =>
            exact fun hx => lt_of_lt_of_le hx (veblen_inflationary (T_normal m) _ _ (complete x))
        | eq =>
          intro hab
          match isZero x with
          | .inl hx =>
            subst hx
            exact equiv_trans (veblen_congr (T_normal m).monotone hab (equiv_refl _))
              (Vmn_collapse2 n m b y hmn)
          | .inr hx =>
            exact lt_of_le_of_lt hab.ge (veblen_subterm1 (T_normal m) _ _ _ (complete a)
              (complete a) (complete x) hx (le_refl _))
        | gt => exact fun hab => lt_of_lt_of_le hab (le_V m a x)
      | eq =>
        intro hmn
        subst hmn
        rw [VF_compare_eq]
        exact veblen_cmp (T_normal m) (complete a) (complete b) (complete x) (complete y)
          (compare a b) _ _ _ (iha b) (ihx (V m b y)) (ihx y) ihy
      | gt =>
        intro hmn
        rw [VF_compare_gt m n a x b y hmn]
        revert ihb
        cases compare (V m a x) b with
        | lt => exact fun hb => lt_of_lt_of_le hb (le_V n b y)
        | eq =>
          intro hb
          match isZero y with
          | .inl hy =>
            subst hy
            exact equiv_trans (equiv_symm (Vmn_collapse2 m n a x hmn))
              (veblen_congr (T_normal n).monotone hb (equiv_refl _))
          | .inr hy =>
            exact lt_of_le_of_lt hb.le (veblen_subterm1 (T_normal n) _ _ _ (complete b)
              (complete b) (complete y) hy (le_refl _))
        | gt =>
          intro hb
          revert ihy
          cases compare (V m a x) y with
          | lt =>
            exact fun hy => lt_of_lt_of_le hy (veblen_inflationary (T_normal n) _ _ (complete y))
          | eq =>
            exact fun hy => equiv_intro
              (le_trans hy.le (veblen_inflationary (T_normal n) _ _ (complete y)))
              (veblen_collapse (T_normal n) _ _ _ (complete b) (complete y) (complete (V m a x))
                hb hy.ge (tower_fix hmn (complete a) (complete x)))
          | gt =>
            exact fun hy => veblen_collapse' (T_normal n) _ _ _ (complete b) (complete y)
              (complete (V m a x)) hb hy (tower_fix hmn (complete a) (complete x))

/-- The order on forms is decidable. Rocq: `Notation.ATowerFinNotation.VF_decide_order`. -/
def decideOrder (x y : VForm) : PSum (sz x < sz y) (sz y ≤ sz x) :=
  match compare x y, compare_correct x y with
  | .lt, h => .inl h
  | .eq, h => .inr h.ge
  | .gt, h => .inr (le_of_lt h)

/-- Rocq: `Notation.ATowerFinNotation.VF_lt_correct`. -/
theorem lt_correct (x y : VForm) : compare x y = .lt ↔ denote x < denote y := by
  have h := compare_correct x y
  revert h
  cases compare x y with
  | lt => exact fun h => ⟨fun _ => h, fun _ => rfl⟩
  | eq => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h' h.ge)).elim⟩
  | gt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_trans h' h)).elim⟩

/-- Rocq: `Notation.ATowerFinNotation.VF_le_correct`. -/
theorem le_correct (x y : VForm) : compare y x ≠ .lt ↔ denote x ≤ denote y := by
  have h := compare_correct y x
  revert h
  cases compare y x with
  | lt => exact fun h => ⟨fun h' => absurd rfl h', fun h' => (lt_irrefl _ (lt_of_lt_of_le h h')).elim⟩
  | eq => exact fun h => ⟨fun _ => h.ge, fun _ h' => nomatch h'⟩
  | gt => exact fun h => ⟨fun _ => le_of_lt h, fun _ h' => nomatch h'⟩

/-! ## Normal forms -/

/-- The condition on the second argument `b` of a normal form `V m a b`. The
inner `match` of Rocq's `VF_isNormal`. -/
def NormalTail (m : Nat) (a : VForm) : VForm → Prop
  | Z =>
    match a with
    | Z => True
    | V n _ _ => n ≤ m
  | V n x y =>
    match natCompare m n with
    | .lt => denote (V n x y) ≤ denote a
    | .eq => denote x ≤ denote a
    | .gt => True

/-- Rocq: `Notation.ATowerFinNotation.VF_isNormal`. -/
def IsNormal : VForm → Prop
  | Z => True
  | V m a b => IsNormal a ∧ IsNormal b ∧ NormalTail m a b

theorem normalTail_V_iff (m n : Nat) (a x y : VForm) :
    NormalTail m a (V n x y) ↔
      (m < n → denote (V n x y) ≤ denote a) ∧ (m = n → denote x ≤ denote a) := by
  show (match natCompare m n with
    | .lt => denote (V n x y) ≤ denote a
    | .eq => denote x ≤ denote a
    | .gt => True) ↔ _
  have hc := natCompare_correct m n
  revert hc
  cases natCompare m n with
  | lt =>
    intro hc
    exact ⟨fun t => ⟨fun _ => t, fun e => absurd (e ▸ hc) (Nat.lt_irrefl _)⟩, fun t => t.1 hc⟩
  | eq =>
    intro hc
    exact ⟨fun t => ⟨fun h => absurd (hc ▸ h) (Nat.lt_irrefl _), fun _ => t⟩, fun t => t.2 hc⟩
  | gt =>
    intro hc
    exact ⟨fun _ => ⟨fun h => absurd (Nat.lt_trans hc h) (Nat.lt_irrefl _),
      fun e => absurd (e ▸ hc) (Nat.lt_irrefl _)⟩, fun _ => trivial⟩

/-- Both arguments are below the whole term.
Rocq: `Notation.ATowerFinNotation.subterm_shrink`. -/
def SubtermShrink : VForm → Prop
  | Z => True
  | V m a b => denote a < denote (V m a b) ∧ denote b < denote (V m a b)

/-- `m < n`, `m = n` or `n < m`. -/
private theorem nat_trichotomy (m n : Nat) : m < n ∨ m = n ∨ n < m := by
  have hc := natCompare_correct m n
  revert hc
  cases natCompare m n with
  | lt => exact .inl
  | eq => exact fun h => .inr (.inl h)
  | gt => exact fun h => .inr (.inr h)

/-- Rocq: `Notation.ATowerFinNotation.normal_subterm_shrink`. -/
theorem normal_subterm_shrink : ∀ x : VForm, IsNormal x → SubtermShrink x
  | Z, _ => trivial
  | V m a b, h => by
    have iha := normal_subterm_shrink a h.1
    have ihb := normal_subterm_shrink b h.2.1
    refine ⟨?_, ?_⟩
    · cases b with
      | Z =>
        match a, h, iha with
        | Z, _, _ => exact veblen_nonzero (T_normal m) _ _
        | V n c d, h, iha =>
          exact lt_of_le_of_lt
            (veblen_monotone_func (T_normal n) (T_normal m)
              (fun i hi => ackermann_tower_fin_monotone _ n m i i onePlus_normal h.2.2 (le_refl _) hi)
              _ _ (complete c) (complete d))
            (veblen_subterm1_zero_nest (T_normal m) _ _ _ (complete c) (complete d)
              (complete (V n c d)) iha.1 iha.2)
      | V n c d =>
        exact veblen_subterm1 (T_normal m) _ _ _ (complete a) (complete a) (complete (V n c d))
          (veblen_nonzero (T_normal n) _ _) (le_refl _)
    · cases b with
      | Z => exact veblen_nonzero (T_normal m) _ _
      | V n c d =>
        have ht := (normalTail_V_iff m n a c d).1 h.2.2
        match nat_trichotomy m n with
        | .inl hmn =>
          exact lt_of_le_of_lt (ht.1 hmn) (veblen_subterm1 (T_normal m) _ _ _ (complete a)
            (complete a) (complete (V n c d)) (veblen_nonzero (T_normal n) _ _) (le_refl _))
        | .inr (.inl e) =>
          subst e
          exact veblen_increasing' (T_normal m) _ _ _ _ (complete c) (complete (V m c d))
            (ht.2 rfl) ihb.2
        | .inr (.inr hnm) =>
          exact veblen_collapse' (T_normal n) _ _ _ (complete c) (complete d)
            (complete (V m a (V n c d)))
            (lt_of_lt_of_le ihb.1 (veblen_inflationary (T_normal m) _ _ (complete (V n c d))))
            (lt_of_lt_of_le ihb.2 (veblen_inflationary (T_normal m) _ _ (complete (V n c d))))
            (tower_fix hnm (complete a) (complete (V n c d)))

/-- `x ≤ y` is decidable, by comparison. -/
private def leDec (x y : VForm) : Decidable (denote x ≤ denote y) :=
  match compare x y, compare_correct x y with
  | .lt, h => isTrue (le_of_lt h)
  | .eq, h => isTrue h.le
  | .gt, h => isFalse fun h' => lt_irrefl _ (lt_of_lt_of_le h h')

private def normalTailDec (m : Nat) (a : VForm) : (b : VForm) → Decidable (NormalTail m a b)
  | Z =>
    match a with
    | Z => isTrue trivial
    | V n _ _ => Nat.decLe n m
  | V n x y => by
    show Decidable (match natCompare m n with
      | .lt => denote (V n x y) ≤ denote a
      | .eq => denote x ≤ denote a
      | .gt => True)
    cases natCompare m n with
    | lt => exact leDec (V n x y) a
    | eq => exact leDec x a
    | gt => exact isTrue trivial

/-- Normality is decidable. Rocq: `Notation.ATowerFinNotation.VF_isNormal_dec`. -/
def isNormalDec : (x : VForm) → Decidable (IsNormal x)
  | Z => isTrue trivial
  | V m a b =>
    match isNormalDec a with
    | isFalse ha => isFalse fun h => ha h.1
    | isTrue ha =>
      match isNormalDec b with
      | isFalse hb => isFalse fun h => hb h.2.1
      | isTrue hb =>
        match normalTailDec m a b with
        | isTrue h => isTrue ⟨ha, hb, h⟩
        | isFalse h => isFalse fun h' => h h'.2.2

instance : DecidablePred IsNormal := isNormalDec

/-! ## Normalization by rewriting -/

/-- Rocq: `Notation.ATowerFinNotation.redex`. -/
inductive Redex : VForm → VForm → Prop
  | V {n : Nat} {a b x : VForm} : compare a b = .lt → Redex (V n a (V n b x)) (V n b x)
  | Vmn1 {m n : Nat} {a b c : VForm} : m < n → compare a (V n b c) = .lt →
      Redex (V m a (V n b c)) (V n b c)
  | Vmn2 {m n : Nat} {b c : VForm} : m < n → Redex (V m (V n b c) Z) (V n b c)

/-- Rocq: `Notation.ATowerFinNotation.redex_sound`. -/
theorem redex_sound {x y : VForm} : Redex x y → denote x ≈ denote y
  | .V h => V_collapse _ _ _ _ ((lt_correct _ _).1 h)
  | .Vmn1 hmn h => Vmn_collapse _ _ _ _ _ hmn ((lt_correct _ _).1 h)
  | .Vmn2 hmn => Vmn_collapse2 _ _ _ _ hmn

/-- Rocq: `Notation.ATowerFinNotation.one_step_reduce`. -/
inductive OneStepReduce : VForm → VForm → Prop
  | redex {x y : VForm} : Redex x y → OneStepReduce x y
  | cong1 {n : Nat} {x x' y : VForm} : OneStepReduce x x' → OneStepReduce (V n x y) (V n x' y)
  | cong2 {n : Nat} {x y y' : VForm} : OneStepReduce y y' → OneStepReduce (V n x y) (V n x y')

/-- Rocq: `Notation.ATowerFinNotation.one_step_reduce_sound`. -/
theorem one_step_reduce_sound {x y : VForm} : OneStepReduce x y → denote x ≈ denote y
  | .redex h => redex_sound h
  | .cong1 (n := n) h => veblen_congr (T_normal n).monotone (one_step_reduce_sound h) (equiv_refl _)
  | .cong2 (n := n) h => veblen_congr (T_normal n).monotone (equiv_refl _) (one_step_reduce_sound h)

/-- Rocq: `Notation.ATowerFinNotation.step_reduce_sound`. -/
theorem step_reduce_sound {x y : VForm} :
    ClosReflTrans OneStepReduce x y → denote x ≈ denote y
  | .step h => one_step_reduce_sound h
  | .refl _ => equiv_refl _
  | .trans h₁ h₂ => equiv_trans (step_reduce_sound h₁) (step_reduce_sound h₂)

/-- `1 + x`, computed by adding a leading `V 0 Z`.
Rocq: `Notation.ATowerFinNotation.VF_onePlus`. -/
def onePlus : VForm → VForm
  | Z => V 0 Z Z
  | V 0 Z x' => V 0 Z (onePlus x')
  | V 0 (V k c d) x' => V 0 (V k c d) x'
  | V (n + 1) a x' => V (n + 1) a x'

/-- Rocq: `Notation.ATowerFinNotation.VF_onePlus_equal`. -/
theorem onePlus_equal : ∀ x : VForm, denote (onePlus x) ≈ 1 + denote x
  | Z => veblen_zero (T 0) 0
  | V 0 Z x' =>
    equiv_trans (veblen_zero (T 0) _) (equiv_trans (add_congr (equiv_refl 1) (onePlus_equal x'))
      (add_congr (equiv_refl 1) (equiv_symm (veblen_zero (T 0) _))))
  | V 0 (V k c d) x' =>
    equiv_symm (onePlus_veblen (T_normal 0) (veblen_nonzero (T_normal k) _ _)
      (complete (V k c d)) (complete x'))
  | V (n + 1) a x' =>
    match isZero a with
    | .inl ha => by
      subst ha
      -- `veblen (T (n + 1)) 0 x' ≈ T (n + 1) x'` is a fixpoint of `veblen (T n) · 0`
      have he := Con.enum_are_fixpoints (veblen_first_normal (T_normal n)) (denote x') (complete x')
      have h0 := veblen_zero (T (n + 1)) (denote x')
      exact equiv_symm (equiv_trans (add_congr (equiv_refl 1) (equiv_trans h0 he))
        (equiv_trans (onePlus_veblen (T_normal n)
          (veblen_nonzero (T_normal (n + 1)) 0 (denote x') |> fun h => lt_of_lt_of_le h h0.le)
          ((T_normal (n + 1)).complete _ (complete x')) zero_complete)
          (equiv_symm (equiv_trans h0 he))))
    | .inr ha => equiv_symm (onePlus_veblen (T_normal (n + 1)) ha (complete a) (complete x'))

/-- Rocq: `Notation.ATowerFinNotation.VF_onePlus_normal`. -/
theorem onePlus_isNormal : ∀ x : VForm, IsNormal x → IsNormal (onePlus x)
  | Z, _ => ⟨trivial, trivial, trivial⟩
  | V 0 Z x', h => by
    refine ⟨trivial, onePlus_isNormal x' h.2.1, ?_⟩
    cases x' with
    | Z => exact (normalTail_V_iff 0 0 Z Z Z).2 ⟨fun h => absurd h (Nat.lt_irrefl _), fun _ => le_refl _⟩
    | V k c d =>
      cases k with
      | zero =>
        cases c with
        | Z => exact (normalTail_V_iff 0 0 Z Z _).2 ⟨fun h => absurd h (Nat.lt_irrefl _),
            fun _ => le_refl _⟩
        | V _ _ _ => exact h.2.2
      | succ _ => exact h.2.2
  | V 0 (V _ _ _) _, h => h
  | V (_ + 1) _ _, h => h

/-- Rocq: `Notation.ATowerFinNotation.one_step_cong_helper1`. -/
theorem one_step_cong_helper1 (n : Nat) (x y : VForm) :
    (∃ z, OneStepReduce x z) → ∃ z, OneStepReduce (V n x y) z := fun ⟨z, h⟩ =>
  ⟨V n z y, .cong1 h⟩

/-- Rocq: `Notation.ATowerFinNotation.one_step_cong_helper2`. -/
theorem one_step_cong_helper2 (n : Nat) (x y : VForm) :
    (∃ z, OneStepReduce y z) → ∃ z, OneStepReduce (V n x y) z := fun ⟨z, h⟩ =>
  ⟨V n x z, .cong2 h⟩

/-- Rocq: `Notation.ATowerFinNotation.multi_reduce_conj1`. -/
theorem multi_reduce_conj1 (m : Nat) {x x' : VForm} (y : VForm) :
    ClosReflTrans OneStepReduce x x' → ClosReflTrans OneStepReduce (V m x y) (V m x' y)
  | .step h => .step (.cong1 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (multi_reduce_conj1 m y h₁) (multi_reduce_conj1 m y h₂)

/-- Rocq: `Notation.ATowerFinNotation.multi_reduce_conj2`. -/
theorem multi_reduce_conj2 (m : Nat) (x : VForm) {y y' : VForm} :
    ClosReflTrans OneStepReduce y y' → ClosReflTrans OneStepReduce (V m x y) (V m x y')
  | .step h => .step (.cong2 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (multi_reduce_conj2 m x h₁) (multi_reduce_conj2 m x h₂)

private theorem not_reduce_Z : ¬ ∃ z, OneStepReduce Z z := fun ⟨_, h⟩ => by
  cases h with
  | redex h => cases h

/-- Rocq: `Notation.ATowerFinNotation.VF_notIsNormal_redex`. -/
theorem notIsNormal_redex : ∀ x : VForm, ¬ IsNormal x ↔ ∃ y, OneStepReduce x y := by
  intro x
  induction x with
  | Z => exact ⟨fun h => absurd trivial h, fun h => absurd h not_reduce_Z⟩
  | V m a b iha ihb =>
    match isNormalDec a with
    | isFalse ha => exact ⟨fun _ => one_step_cong_helper1 m a b (iha.1 ha), fun _ h => ha h.1⟩
    | isTrue ha =>
      match isNormalDec b with
      | isFalse hb => exact ⟨fun _ => one_step_cong_helper2 m a b (ihb.1 hb), fun _ h => hb h.2.1⟩
      | isTrue hb =>
        constructor
        · intro hn
          cases b with
          | Z =>
            cases a with
            | Z => exact absurd ⟨ha, hb, trivial⟩ hn
            | V n c d =>
              match Nat.decLe n m with
              | isTrue h => exact absurd ⟨ha, hb, h⟩ hn
              | isFalse h => exact ⟨V n c d, .redex (.Vmn2 (Nat.lt_of_not_le h))⟩
          | V n c d =>
            match nat_trichotomy m n with
            | .inl hmn =>
              match decideOrder a (V n c d) with
              | .inl h => exact ⟨V n c d, .redex (.Vmn1 hmn ((lt_correct _ _).2 h))⟩
              | .inr h => exact absurd ⟨ha, hb, (normalTail_V_iff m n a c d).2
                  ⟨fun _ => h, fun e => absurd (e ▸ hmn) (Nat.lt_irrefl _)⟩⟩ hn
            | .inr (.inl e) =>
              subst e
              match decideOrder a c with
              | .inl h => exact ⟨V m c d, .redex (.V ((lt_correct _ _).2 h))⟩
              | .inr h => exact absurd ⟨ha, hb, (normalTail_V_iff m m a c d).2
                  ⟨fun h' => absurd h' (Nat.lt_irrefl _), fun _ => h⟩⟩ hn
            | .inr (.inr hnm) =>
              exact absurd ⟨ha, hb, (normalTail_V_iff m n a c d).2
                ⟨fun h' => absurd (Nat.lt_trans hnm h') (Nat.lt_irrefl _),
                  fun e => absurd (e ▸ hnm) (Nat.lt_irrefl _)⟩⟩ hn
        · rintro ⟨z, hz⟩ hn
          cases hz with
          | redex h =>
            cases h with
            | V h =>
              exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h)
                (((normalTail_V_iff _ _ _ _ _).1 hn.2.2).2 rfl))
            | Vmn1 hmn h =>
              exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h)
                (((normalTail_V_iff _ _ _ _ _).1 hn.2.2).1 hmn))
            | Vmn2 hmn => exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hmn hn.2.2)
          | cong1 h => exact iha.2 ⟨_, h⟩ ha
          | cong2 h => exact ihb.2 ⟨_, h⟩ hb

/-- Rocq: `Notation.ATowerFinNotation.VF_isNormal_no_redex`. -/
theorem isNormal_no_redex (x : VForm) : IsNormal x ↔ ¬ ∃ y, OneStepReduce x y :=
  match isNormalDec x with
  | isTrue h => ⟨fun _ hr => (notIsNormal_redex x).2 hr h, fun _ => h⟩
  | isFalse h => ⟨fun h' => absurd h' h, fun hr => absurd ((notIsNormal_redex x).1 h) hr⟩

/-- Build `V m a b`, absorbing `a` where the result would not be normal.
Rocq: `Notation.ATowerFinNotation.Vnorm`. -/
def vnorm (m : Nat) (a : VForm) : VForm → VForm
  | Z =>
    match a with
    | Z => V m Z Z
    | V n c d =>
      match natCompare m n with
      | .lt => V n c d
      | .eq => V m (V n c d) Z
      | .gt => V m (V n c d) Z
  | V n x y =>
    match natCompare m n with
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

/-- Rocq: `Notation.ATowerFinNotation.Vnorm_reduce`. -/
theorem vnorm_reduce (m : Nat) (a : VForm) : ∀ b : VForm,
    ClosReflTrans OneStepReduce (V m a b) (vnorm m a b)
  | Z =>
    match a with
    | Z => .refl _
    | V n c d => by
      show ClosReflTrans OneStepReduce _ (match natCompare m n with
        | .lt => V n c d
        | .eq => V m (V n c d) Z
        | .gt => V m (V n c d) Z)
      have hc := natCompare_correct m n
      revert hc
      cases natCompare m n with
      | lt => exact fun hmn => .step (.redex (.Vmn2 hmn))
      | eq => exact fun _ => .refl _
      | gt => exact fun _ => .refl _
  | V n x y => by
    show ClosReflTrans OneStepReduce _ (match natCompare m n with
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
    have hmn := natCompare_correct m n
    revert hmn
    cases natCompare m n with
    | lt =>
      intro hmn
      cases hc : compare a (V n x y) with
      | lt => exact .step (.redex (.Vmn1 hmn hc))
      | eq => exact .refl _
      | gt => exact .refl _
    | eq =>
      intro hmn
      subst hmn
      cases hc : compare a x with
      | lt => exact .step (.redex (.V hc))
      | eq => exact .refl _
      | gt => exact .refl _
    | gt => exact fun _ => .refl _

/-- Rocq: `Notation.ATowerFinNotation.Vnorm_normal`. -/
theorem vnorm_normal (m : Nat) (a b : VForm) (ha : IsNormal a) (hb : IsNormal b) :
    IsNormal (vnorm m a b) := by
  cases b with
  | Z =>
    cases a with
    | Z => exact ⟨trivial, trivial, trivial⟩
    | V n c d =>
      show IsNormal (match natCompare m n with
        | .lt => V n c d
        | .eq => V m (V n c d) Z
        | .gt => V m (V n c d) Z)
      have hc := natCompare_correct m n
      revert hc
      cases natCompare m n with
      | lt => exact fun _ => ha
      | eq => exact fun hc => ⟨ha, trivial, hc ▸ Nat.le_refl _⟩
      | gt => exact fun hc => ⟨ha, trivial, Nat.le_of_lt hc⟩
  | V n x y =>
    show IsNormal (match natCompare m n with
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
    have hmn := natCompare_correct m n
    revert hmn
    cases natCompare m n with
    | lt =>
      intro hmn
      have hc := compare_correct a (V n x y)
      have ht : denote (V n x y) ≤ denote a → NormalTail m a (V n x y) := fun h =>
        (normalTail_V_iff m n a x y).2 ⟨fun _ => h, fun e => absurd (e ▸ hmn) (Nat.lt_irrefl _)⟩
      revert hc
      cases compare a (V n x y) with
      | lt => exact fun _ => hb
      | eq => exact fun hc => ⟨ha, hb, ht hc.ge⟩
      | gt => exact fun hc => ⟨ha, hb, ht (le_of_lt hc)⟩
    | eq =>
      intro hmn
      subst hmn
      have hc := compare_correct a x
      have ht : denote x ≤ denote a → NormalTail m a (V m x y) := fun h =>
        (normalTail_V_iff m m a x y).2 ⟨fun h' => absurd h' (Nat.lt_irrefl _), fun _ => h⟩
      revert hc
      cases compare a x with
      | lt => exact fun _ => hb
      | eq => exact fun hc => ⟨ha, hb, ht hc.ge⟩
      | gt => exact fun hc => ⟨ha, hb, ht (le_of_lt hc)⟩
    | gt =>
      intro hnm
      exact ⟨ha, hb, (normalTail_V_iff m n a x y).2
        ⟨fun h' => absurd (Nat.lt_trans hnm h') (Nat.lt_irrefl _),
          fun e => absurd (e ▸ hnm) (Nat.lt_irrefl _)⟩⟩

/-- Rocq: `Notation.ATowerFinNotation.Vnorm_equal`. -/
theorem vnorm_equal (m : Nat) (a b : VForm) (_ha : IsNormal a) (_hb : IsNormal b) :
    denote (vnorm m a b) ≈ denote (V m a b) :=
  equiv_symm (step_reduce_sound (vnorm_reduce m a b))

/-- Rocq: `Notation.ATowerFinNotation.VF_normalize`. -/
def normalize : VForm → VForm
  | Z => Z
  | V m a b => vnorm m (normalize a) (normalize b)

/-- Rocq: `Notation.ATowerFinNotation.VF_normalize_isNormal`. -/
theorem normalize_isNormal : ∀ x : VForm, IsNormal (normalize x)
  | Z => trivial
  | V m a b => vnorm_normal m _ _ (normalize_isNormal a) (normalize_isNormal b)

/-- Rocq: `Notation.ATowerFinNotation.VF_normalize_reduce`. -/
theorem normalize_reduce : ∀ x : VForm, ClosReflTrans OneStepReduce x (normalize x)
  | Z => .refl _
  | V m a b => .trans (multi_reduce_conj1 m b (normalize_reduce a))
      (.trans (multi_reduce_conj2 m _ (normalize_reduce b)) (vnorm_reduce _ _ _))

/-- Rocq: `Notation.ATowerFinNotation.VF_normalize_equal`. -/
theorem normalize_equal (x : VForm) : denote (normalize x) ≈ denote x :=
  equiv_symm (step_reduce_sound (normalize_reduce x))

/-- Two normal forms with the same tower level and denotation have equivalent
arguments. -/
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

/-- A normal `V m a x` never denotes the same as `V n b y` with `m < n`. -/
private theorem ne_of_level_lt {m n : Nat} {a x b y : VForm} (hmn : m < n) (hx : IsNormal (V m a x))
    (h : denote (V m a x) ≈ denote (V n b y)) : False := by
  have hs := normal_subterm_shrink _ hx
  refine lt_irrefl (denote (V m a x)) ?_
  calc denote (V m a x)
      < veblen (T m) (denote a) (denote (V n b y)) :=
        veblen_increasing (T_normal m) _ (complete a) _ _ (complete (V n b y))
          (lt_of_lt_of_le hs.2 h.le)
    _ ≈ denote (V n b y) := Vmn_collapse n m a b y hmn (lt_of_lt_of_le hs.1 h.le)
    _ ≈ denote (V m a x) := equiv_symm h

/-- Rocq: `Notation.ATowerFinNotation.normal_forms_unique`. -/
theorem normal_forms_unique : ∀ x y : VForm, IsNormal x → IsNormal y →
    denote x ≈ denote y → x = y
  | Z, Z, _, _, _ => rfl
  | Z, V n _ _, _, _, h =>
    absurd (lt_of_lt_of_le (veblen_nonzero (T_normal n) _ _) h.ge) (lt_irrefl 0)
  | V m _ _, Z, _, _, h =>
    absurd (lt_of_lt_of_le (veblen_nonzero (T_normal m) _ _) h.le) (lt_irrefl 0)
  | V m a x, V n b y, hx, hy, h => by
    have e : m = n := by
      match nat_trichotomy m n with
      | .inl hmn => exact (ne_of_level_lt hmn hx h).elim
      | .inr (.inl e) => exact e
      | .inr (.inr hnm) => exact (ne_of_level_lt hnm hy (equiv_symm h)).elim
    subst e
    obtain ⟨hab, hxy⟩ := same_head (T_normal m) (normal_subterm_shrink _ hx).2
      (normal_subterm_shrink _ hy).2 h
    rw [normal_forms_unique a b hx.1 hy.1 hab, normal_forms_unique x y hx.2.1 hy.2.1 hxy]

/-- Reduction is confluent. Rocq: `Notation.ATowerFinNotation.reduce_confluent`. -/
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

/-- `x` reduces to the normal form `y`. Rocq: `Notation.ATowerFinNotation.normalizes`. -/
inductive Normalizes : VForm → VForm → Prop
  | normal {x : VForm} : (¬ ∃ y, OneStepReduce x y) → Normalizes x x
  | step {x y z : VForm} : OneStepReduce x y → Normalizes y z → Normalizes x z

/-- Rocq: `Notation.ATowerFinNotation.redex_size`. -/
theorem redex_size {x y : VForm} : Redex x y → size y < size x
  | .V (a := a) (b := b) (x := x) _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size b + size x + 1) (size a))
  | .Vmn1 (a := a) (b := b) (c := c) _ _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size b + size c + 1) (size a))
  | .Vmn2 _ => Nat.lt_succ_self _

/-- Rocq: `Notation.ATowerFinNotation.one_step_reduce_size`. -/
theorem one_step_reduce_size {x y : VForm} : OneStepReduce x y → size y < size x
  | .redex h => redex_size h
  | .cong1 h => Nat.succ_lt_succ (Nat.add_lt_add_right (one_step_reduce_size h) _)
  | .cong2 h => Nat.succ_lt_succ (Nat.add_lt_add_left (one_step_reduce_size h) _)

/-- Reduction is strongly normalizing.
Rocq: `Notation.ATowerFinNotation.strongly_normalizing`. -/
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

/-- Rocq: `Notation.ATowerFinNotation.normalizes_correct`. -/
theorem normalizes_correct {x y : VForm} : Normalizes x y → denote x ≈ denote y ∧ IsNormal y
  | .normal h => ⟨equiv_refl _, (isNormal_no_redex _).2 h⟩
  | .step h₁ h₂ =>
    let ih := normalizes_correct h₂
    ⟨equiv_trans (one_step_reduce_sound h₁) ih.1, ih.2⟩

/-- Rocq: `Notation.ATowerFinNotation.normalizes_iff`. -/
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

/-- Values of the higher levels of the tower are ε-numbers.
Rocq: `Notation.ATowerFinNotation.veblen_tower_epsilon`. -/
theorem veblen_tower_epsilon (n : Nat) (x y : Ordinal.{0}) (hx : Complete x) (hy : Complete y)
    (hn : 0 < n) : ω ^ veblen (T n) x y ≈ veblen (T n) x y := by
  have hc := veblen_complete (T_normal n) (T_normal n).complete _ hx _ hy
  refine equiv_intro ?_ (normal_inflationary powOmega_normal _ hc)
  calc ω ^ veblen (T n) x y
      ≈ veblen (T 0) (veblen (T n) x y) 0 :=
        equiv_symm (equiv_trans (veblen_onePlus _ hc _ zero_complete) (add_zero _))
    _ ≤ veblen (T n) x y := tower_fix hn hx hy

/-! ## Cantor decomposition and arithmetic -/

open CantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_decompose`. -/
def decompose : VForm → List VForm
  | Z => []
  | V 0 a b => a :: decompose b
  | V (k + 1) a b => [V (k + 1) a b]

/-- Rocq: `Notation.ATowerFinNotation.VF_recompose`. -/
def recompose : List VForm → VForm
  | [] => Z
  | [x] =>
    match x with
    | Z => V 0 Z Z
    | V 0 c d => V 0 (V 0 c d) Z
    | V (k + 1) c d => V (k + 1) c d
  | x :: x' :: xs' => V 0 x (recompose (x' :: xs'))

/-- Rocq: `Notation.ATowerFinNotation.VF_decompose_correct`. -/
theorem decompose_correct : ∀ x : VForm, IsNormal x →
    Each IsNormal (decompose x) ∧ CantorOrdered denote (decompose x) ∧
      denote x ≈ cantorDenote denote (decompose x)
  | Z, _ => ⟨trivial, trivial, equiv_refl _⟩
  | V 0 a b, h =>
    let ih := decompose_correct b h.2.1
    ⟨⟨h.1, ih.1⟩,
      ⟨match b, h with
        | Z, _ => trivial
        | V 0 _ _, h => ((normalTail_V_iff _ _ _ _ _).1 h.2.2).2 rfl
        | V (_ + 1) _ _, h => ((normalTail_V_iff _ _ _ _ _).1 h.2.2).1 (Nat.zero_lt_succ _),
        ih.2.1⟩,
      equiv_trans (veblen_onePlus _ (complete a) _ (complete b))
        (add_congr (equiv_refl _) ih.2.2)⟩
  | V (k + 1) a b, h =>
    ⟨⟨h, trivial⟩, ⟨trivial, trivial⟩,
      equiv_trans (equiv_symm (veblen_tower_epsilon (k + 1) _ _ (complete a) (complete b)
        (Nat.zero_lt_succ _))) (equiv_symm (add_zero _))⟩

/-- Rocq: `Notation.ATowerFinNotation.VF_recompose_correct`. -/
theorem recompose_correct : ∀ xs : List VForm, Each IsNormal xs → CantorOrdered denote xs →
    IsNormal (recompose xs) ∧ cantorDenote denote xs ≈ denote (recompose xs)
  | [], _, _ => ⟨trivial, equiv_refl _⟩
  | [x], hP, _ =>
    match x, hP with
    | Z, _ => ⟨⟨trivial, trivial, trivial⟩,
        equiv_symm (veblen_onePlus _ zero_complete _ zero_complete)⟩
    | V 0 c d, hP => ⟨⟨hP.1, trivial, Nat.le_refl 0⟩,
        equiv_symm (veblen_onePlus _ (complete (V 0 c d)) _ zero_complete)⟩
    | V (k + 1) c d, hP => ⟨hP.1, equiv_trans (add_zero _)
        (veblen_tower_epsilon (k + 1) _ _ (complete c) (complete d) (Nat.zero_lt_succ _))⟩
  | x :: x' :: xs', hP, hord => by
    have ih := recompose_correct (x' :: xs') hP.2 hord.2
    refine ⟨⟨hP.1, ih.1, ?_⟩, equiv_trans (add_congr (equiv_refl _) ih.2)
      (equiv_symm (veblen_onePlus _ (complete x) _ (complete _)))⟩
    have hx' : denote x' ≤ denote x := hord.1
    have eq0 : ∀ c d, denote c ≤ denote x → NormalTail 0 x (V 0 c d) := fun c d h =>
      (normalTail_V_iff 0 0 x c d).2 ⟨fun h' => absurd h' (Nat.lt_irrefl _), fun _ => h⟩
    cases xs' with
    | nil =>
      cases x' with
      | Z => exact eq0 Z Z (zero_least _)
      | V k c d =>
        cases k with
        | zero => exact eq0 _ Z hx'
        | succ k =>
          exact (normalTail_V_iff 0 (k + 1) x c d).2
            ⟨fun _ => hx', fun e => Nat.noConfusion e⟩
    | cons _ _ => exact eq0 _ _ hx'

/-- Rocq: `Notation.ATowerFinNotation.VF_has_cantor_decomposition`. -/
def hasCantorDecomposition : HasCantorDecomposition denote IsNormal where
  compare := compare
  decompose := decompose
  recompose := recompose
  complete := complete
  compare_correct x y _ _ := compare_correct x y
  decompose_correct := decompose_correct
  recompose_correct := recompose_correct

/-- Rocq: `Notation.ATowerFinNotation.VF_succ`. -/
def succ : VForm → VForm := cantorSucc hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_add`. -/
def add : VForm → VForm → VForm := cantorAdd hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_mul`. -/
def mul : VForm → VForm → VForm := cantorMul hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_exp`. -/
def exp : VForm → VForm → VForm := cantorExp hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_succ_reflects`. -/
theorem succ_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Ordinal.succ succ :=
  cantor_succ_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_add_reflects`. -/
theorem add_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· + ·) add :=
  cantor_add_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_mul_reflects`. -/
theorem mul_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· * ·) mul :=
  cantor_mul_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_exp_reflects`. -/
theorem exp_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ^ ·) exp :=
  cantor_exp_reflects hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_ackermann_reflects`. -/
theorem ackermann_reflects (n : Nat) :
    Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (veblen (T n)) (vnorm n) :=
  fun _ a ⟨hxa, ha⟩ _ b ⟨hyb, hb⟩ =>
    ⟨equiv_trans (veblen_congr (T_normal n).monotone hxa hyb)
        (equiv_symm (vnorm_equal n a b ha hb)),
      vnorm_normal n a b ha hb⟩

/-- Each level of the tower preserves interpolants. -/
private theorem tower_interpolants : ∀ (n : Nat) (b : Ordinal.{0}), Complete b →
    HasInterpolants denote IsNormal b → HasInterpolants denote IsNormal (T n b)
  | 0, b, _, hb =>
    onePlus_interpolants Z ⟨equiv_refl _, trivial⟩ (add (succ Z))
      (fun x a h => add_reflects 1 (succ Z) (succ_reflects 0 Z ⟨equiv_refl _, trivial⟩) x a h)
      b hb
  | n + 1, b, hb₁, hb₂ =>
    enum_fix_has_interpolants hasCantorDecomposition (fun x => veblen (T n) x 0)
      (veblen_first_normal (T_normal n)).complete
      (fun b hb₁ hb₂ => veblen_interpolants_first hasCantorDecomposition (T n) (T_normal n)
        (tower_interpolants n) (vnorm n) (ackermann_reflects n) b hb₁ hb₂)
      (veblen_first_normal (T_normal n)).monotone
      (normal_inflationary (veblen_first_normal (T_normal n))) (vnorm (n + 1) Z)
      (fun _ a ⟨hxa, ha⟩ =>
        ⟨equiv_trans (enum_fixpoint_congr (veblen_first_normal (T_normal n)) hxa)
            (equiv_trans (equiv_symm (veblen_zero (T (n + 1)) (denote a)))
              (equiv_symm (vnorm_equal (n + 1) Z a trivial ha))),
          vnorm_normal (n + 1) Z a trivial ha⟩)
      b hb₁ hb₂

/-- Rocq: `Notation.ATowerFinNotation.VF_has_all_interpolants`. -/
theorem has_all_interpolants : HasAllInterpolants denote IsNormal := by
  intro x
  induction x with
  | Z =>
    exact fun _ => (has_interpolants_unfold _).2 fun i hi =>
      (lt_irrefl i (lt_of_lt_of_le hi (zero_least i))).elim
  | V n a b iha ihb =>
    exact fun h => veblen_interpolants hasCantorDecomposition (T n) (T_normal n)
      (tower_interpolants n) (vnorm n) (ackermann_reflects n) a (denote b) h.1 (iha h.1)
      (complete b) (ihb h.2.1)

/-- Rocq: `Notation.ATowerFinNotation.VF_nadd`. -/
def nadd : VForm → VForm → VForm := cantorNadd hasCantorDecomposition

/-- Rocq: `Notation.ATowerFinNotation.VF_reflects_nadd`. -/
theorem reflects_nadd : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ♯ ·) nadd :=
  cantor_nadd_reflects hasCantorDecomposition has_all_interpolants

/-! ## Order type -/

/-- The small Ackermann ordinal is complete. -/
private theorem SAO_complete : Complete (SmallAckermannOrdinal.{0}) :=
  sup_complete (fun i => (T_normal i.down).complete 0 zero_complete)
    (fun a₁ a₂ => ⟨⟨Nat.max a₁.down a₂.down⟩,
      ackermann_tower_fin_monotone _ _ _ 0 0 onePlus_normal (Nat.le_max_left _ _) (le_refl _)
        zero_complete,
      ackermann_tower_fin_monotone _ _ _ 0 0 onePlus_normal (Nat.le_max_right _ _) (le_refl _)
        zero_complete⟩)
    (.inl ⟨⟨0⟩, lt_of_lt_of_le (succ_lt 0) (add_zero 1).ge⟩)

/-- Rocq: `Notation.ATowerFinNotation.VF_below_SAO`. -/
theorem below_SAO : ∀ x : VForm, denote x < SmallAckermannOrdinal
  | Z => lt_of_lt_of_le (lt_of_lt_of_le (succ_lt 0) (add_zero 1).ge)
      (sup_le (fun n : (ω : Ordinal.{0}).Carrier => T n.down 0) ⟨0⟩)
  | V n a x => by
    refine veblen_collapse' (T_normal n) _ _ _ (complete a) (complete x) SAO_complete
      (below_SAO a) (below_SAO x) ?_
    refine le_trans (veblen_continuous_first (T_normal n) _ _ ⟨0⟩) (sup_least fun i => ?_)
    let k := Nat.max i.down n
    refine le_trans ?_ (sup_le (fun n : (ω : Ordinal.{0}).Carrier => T n.down 0) ⟨k + 1⟩)
    calc veblen (T n) (T i.down 0) 0
        ≤ veblen (T k) (T i.down 0) 0 :=
          veblen_monotone_func (T_normal n) (T_normal k)
            (fun j hj => ackermann_tower_fin_monotone _ n k j j onePlus_normal
              (Nat.le_max_right _ _) (le_refl _) hj)
            _ _ ((T_normal _).complete 0 zero_complete) zero_complete
      _ ≤ veblen (T k) (T (k + 1) 0) 0 :=
          veblen_monotone_first (T_normal k).monotone _ _ _
            (ackermann_tower_fin_monotone _ _ _ 0 0 onePlus_normal
              (Nat.le_succ_of_le (Nat.le_max_left _ _)) (le_refl _) zero_complete)
      _ ≈ T (k + 1) 0 := equiv_symm (Con.enum_are_fixpoints (veblen_first_normal (T_normal k)) 0
          zero_complete)

end VForm

open VForm in
/-- The forms have order type the small Ackermann ordinal.
Rocq: `Notation.ATowerFinNotation.VF_SAO`. -/
theorem VF_SAO : VF ≈ SmallAckermannOrdinal :=
  equiv_intro (le_intro fun x => below_SAO x)
    (sup_least fun i =>
      le_trans (veblen_zero (T i.down) 0).ge (index_le VF (V i.down Z Z)))

namespace VForm

open CantorDecomposition

/-- With the excluded middle, every ordinal below the small Ackermann ordinal
has a normal form. Rocq: `Notation.ATowerFinNotation.VF_has_enough_notations`. -/
theorem has_enough_notations (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < SmallAckermannOrdinal → ∃ v : VForm, sz v ≈ x := by
  intro x hx
  obtain ⟨a, ha⟩ := lt_elim (lt_of_lt_of_le hx VF_SAO.ge)
  obtain ⟨c, _, hc⟩ := has_interpolants_has_enough_notations em has_all_interpolants
    (normalize a) x (normalize_isNormal a) (le_trans ha (normalize_equal a).ge)
  exact ⟨c, hc⟩

/-! ## Sample computations -/

/-- `T 1 0 < T 2 0`, and `ω ^ T 2 0 = T 2 0` (checked by kernel reduction). -/
theorem sample_compare : compare (V 1 Z Z) (V 2 Z Z) = .lt ∧
    compare (vnorm 0 (V 2 Z Z) Z) (V 2 Z Z) = .eq := ⟨rfl, rfl⟩

end VForm

end ConstructiveOrdinals.ATowerFinNotation
