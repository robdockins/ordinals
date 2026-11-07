import ConstructiveOrdinals.Notation.CantorDecomposition
import ConstructiveOrdinals.Veblen.Facts
import ConstructiveOrdinals.Prelude.Relations

/-!
# Veblen forms: a second notation system for ε₀

Port of `Ordinal/Notation/VNotation.v`.

A form `V a x` denotes `φ a x`, where `φ = veblen (1 + ·)` is the Veblen
hierarchy over `1 + ·`. Since `φ a x ≈ ω ^ a + x`, these are Cantor normal
forms in disguise and denote exactly the ordinals below `ε 0`.

The file develops a rewriting presentation of normalization (`OneStepReduce`
is confluent and strongly normalizing, and normal forms are unique), shows
that the system has a Cantor decomposition, and derives arithmetic, natural
sums and the enough-notations theorem from `Notation/CantorDecomposition`.

Lean notes:

- Rocq's `VF_compare` has an inner `fix` on its second argument. It becomes
  the separate function `compareInner`, parameterised by the outer recursive
  calls.
- The decision procedure `VF_isNormal_dec` is `isNormalDec`, a `Decidable`
  instance.
-/

namespace ConstructiveOrdinals.VNotation

open Ordinal

/-- Veblen forms. Rocq: `Notation.VNotation.VForm`. -/
inductive VForm : Type where
  | Z : VForm
  | V : VForm → VForm → VForm

namespace VForm

/-- Rocq: `Notation.VNotation.VF_denote`. -/
def denote : VForm → Ordinal.{0}
  | Z => 0
  | V a x => veblen (fun y => 1 + y) (denote a) (denote x)

instance : Sized VForm := ⟨denote⟩

end VForm

/-- The ordinal of all Veblen forms. Rocq: `Notation.VNotation.VF`. -/
def VF : Ordinal.{0} := mk VForm VForm.denote

namespace VForm

/-- Rocq: `Notation.VNotation.VF_size`. -/
def size : VForm → Nat
  | Z => 0
  | V x y => size x + size y + 1

/-- A form is normal when the first arguments of nested `V`s are
non-increasing. Rocq: `Notation.VNotation.VF_normal`. -/
def IsNormal : VForm → Prop
  | Z => True
  | V a x => IsNormal a ∧ IsNormal x ∧
    match x with
    | Z => True
    | V b _ => denote b ≤ denote a

/-- Rocq: `Notation.VNotation.VF_complete`. -/
theorem complete : ∀ x : VForm, Complete (denote x)
  | Z => zero_complete
  | V a x => veblen_complete onePlus_normal onePlus_normal.complete _ (complete a) _ (complete x)

/-- Rocq: `Notation.VNotation.veblen_onePlus_complete`. -/
theorem veblen_onePlus_complete (a x : Ordinal.{0}) (ha : Complete a) (hx : Complete x) :
    Complete (veblen (fun y => 1 + y) a x) :=
  veblen_complete onePlus_normal onePlus_normal.complete _ ha _ hx

private theorem shrink_zero : ∀ a : VForm, denote a < veblen (fun y => 1 + y) (denote a) 0
  | Z => veblen_nonzero onePlus_normal _ _
  | V a x => veblen_shrink_lemma onePlus_normal _ _ (complete a) (complete x)
      (shrink_zero a) (shrink_zero x)

/-- Rocq: `Notation.VNotation.VF_denote_shrink1`. -/
theorem denote_shrink1 (a x : VForm) : denote a < denote (V a x) :=
  lt_of_lt_of_le (shrink_zero a) (veblen_monotone onePlus_normal.monotone _ _ _ (zero_least _))

/-- Rocq: `Notation.VNotation.VF_denote_le2`. -/
theorem denote_le2 (x a : VForm) : denote x ≤ denote (V a x) :=
  veblen_inflationary onePlus_normal _ _ (complete x)

/-- Rocq: `Notation.VNotation.VF_denote_shrink2`. -/
theorem denote_shrink2 : ∀ x a : VForm, IsNormal (V a x) → denote x < denote (V a x)
  | Z, _, _ => veblen_nonzero onePlus_normal _ _
  | V b y, _, h =>
    veblen_increasing' onePlus_normal _ _ _ _ (complete b) (complete (V b y)) h.2.2
      (denote_shrink2 y b h.2.1)

/-- Rocq: `Notation.VNotation.VNotation_below_ε₀`. -/
theorem below_ε₀ : ∀ x : VForm, denote x < ε 0
  | Z => lt_of_lt_of_le (pow_pos ω _) (ε_fixpoint 0).ge
  | V a x =>
    lt_of_le_of_lt (veblen_onePlus _ (complete a) _ (complete x)).le
      (epsilon_additively_closed zero_complete _ _
        (lt_of_lt_of_le (pow_lt_pow_right omega_gt1 (below_ε₀ a)) (ε_fixpoint 0).ge)
        (below_ε₀ x))

/-! ## Comparison -/

/-- Compare `V a x'` with a form, given the comparisons with `a` and with `x'`.
The inner `fix` of Rocq's `VF_compare`. -/
def compareInner (recA recX : VForm → Ordering) : VForm → Ordering
  | Z => .gt
  | V b y' =>
    match recA b with
    | .lt => recX (V b y')
    | .eq => recX y'
    | .gt => compareInner recA recX y'

/-- Comparison of Veblen forms. It is correct on all forms, normal or not.
Rocq: `Notation.VNotation.VF_compare`. -/
def compare : VForm → VForm → Ordering
  | Z, Z => .eq
  | Z, V _ _ => .lt
  | V a x', y => compareInner (compare a) (compare x') y

/-- Rocq: `Notation.VNotation.VF_compare_correct`. -/
theorem compare_correct : ∀ x y : VForm, OrderingCorrect (compare x y) (denote x) (denote y) := by
  have mono := onePlus_normal.monotone
  intro x
  induction x with
  | Z =>
    intro y
    cases y with
    | Z => exact equiv_refl _
    | V _ _ => exact veblen_nonzero onePlus_normal _ _
  | V a x iha ihx =>
    intro y
    induction y with
    | Z => exact veblen_nonzero onePlus_normal _ _
    | V b y _ ihy =>
      show OrderingCorrect (match compare a b with
        | .lt => compare x (V b y)
        | .eq => compare x y
        | .gt => compare (V a x) y) _ _
      have hab := iha b
      revert hab
      cases compare a b with
      | lt =>
        intro hab
        have hfix := veblen_fixpoints onePlus_normal _ _ _ (complete a) (complete b) (complete y) hab
        have hx := ihx (V b y)
        revert hx
        cases compare x (V b y) with
        | lt =>
          exact fun hx => lt_of_lt_of_le
            (veblen_increasing onePlus_normal _ (complete a) _ _ (complete (V b y)) hx) hfix.le
        | eq => exact fun hx => equiv_trans (veblen_congr mono (equiv_refl _) hx) hfix
        | gt => exact fun hx => lt_of_lt_of_le hx (denote_le2 x a)
      | eq =>
        intro hab
        have hx := ihx y
        revert hx
        cases compare x y with
        | lt =>
          exact fun hx => lt_of_lt_of_le
            (veblen_increasing onePlus_normal _ (complete a) _ _ (complete y) hx)
            (veblen_monotone_first mono _ _ _ hab.le)
        | eq => exact fun hx => veblen_congr mono hab hx
        | gt =>
          exact fun hx => lt_of_lt_of_le
            (veblen_increasing onePlus_normal _ (complete b) _ _ (complete x) hx)
            (veblen_monotone_first mono _ _ _ hab.ge)
      | gt =>
        intro hab
        have hfix := veblen_fixpoints onePlus_normal _ _ _ (complete b) (complete a) (complete x) hab
        revert ihy
        cases compare (V a x) y with
        | lt => exact fun hy => lt_of_lt_of_le hy (denote_le2 y b)
        | eq => exact fun hy => equiv_symm (equiv_trans (veblen_congr mono (equiv_refl _)
            (equiv_symm hy)) hfix)
        | gt =>
          exact fun hy => lt_of_lt_of_le
            (veblen_increasing onePlus_normal _ (complete b) _ _ (complete (V a x)) hy) hfix.le

/-- Rocq: `Notation.VNotation.VF_lt_correct`. -/
theorem lt_correct (x y : VForm) : compare x y = .lt ↔ denote x < denote y := by
  have h := compare_correct x y
  revert h
  cases compare x y with
  | lt => exact fun h => ⟨fun _ => h, fun _ => rfl⟩
  | eq => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h' h.ge)).elim⟩
  | gt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_trans h' h)).elim⟩

/-- Rocq: `Notation.VNotation.VF_le_correct`. -/
theorem le_correct (x y : VForm) : compare y x ≠ .lt ↔ denote x ≤ denote y := by
  have h := compare_correct y x
  revert h
  cases compare y x with
  | lt => exact fun h => ⟨fun h' => absurd rfl h', fun h' => (lt_irrefl _ (lt_of_lt_of_le h h')).elim⟩
  | eq => exact fun h => ⟨fun _ => h.ge, fun _ h' => nomatch h'⟩
  | gt => exact fun h => ⟨fun _ => le_of_lt h, fun _ h' => nomatch h'⟩

/-- The order on Veblen forms is decidable. Rocq: `Notation.VNotation.V_decide_order`. -/
def decideOrder (x y : VForm) : PSum (sz x < sz y) (sz y ≤ sz x) :=
  match compare x y, compare_correct x y with
  | .lt, h => .inl h
  | .eq, h => .inr h.ge
  | .gt, h => .inr (le_of_lt h)

/-! ## Normalization by rewriting -/

/-- Rocq: `Notation.VNotation.redex`. -/
inductive Redex : VForm → VForm → Prop
  | mk {a b x : VForm} : compare a b = .lt → Redex (V a (V b x)) (V b x)

/-- Rocq: `Notation.VNotation.redex_sound`. -/
theorem redex_sound {x y : VForm} : Redex x y → denote x ≈ denote y
  | .mk (a := a) (b := b) (x := x) h =>
    veblen_fixpoints onePlus_normal _ _ _ (complete a) (complete b) (complete x)
      ((lt_correct a b).1 h)

/-- Rocq: `Notation.VNotation.one_step_reduce`. -/
inductive OneStepReduce : VForm → VForm → Prop
  | redex {x y : VForm} : Redex x y → OneStepReduce x y
  | vcong1 {x x' y : VForm} : OneStepReduce x x' → OneStepReduce (V x y) (V x' y)
  | vcong2 {x y y' : VForm} : OneStepReduce y y' → OneStepReduce (V x y) (V x y')

/-- Rocq: `Notation.VNotation.one_step_reduce_sound`. -/
theorem one_step_reduce_sound {x y : VForm} : OneStepReduce x y → denote x ≈ denote y
  | .redex h => redex_sound h
  | .vcong1 h => veblen_onePlus_congr (one_step_reduce_sound h) (equiv_refl _)
  | .vcong2 h => veblen_onePlus_congr (equiv_refl _) (one_step_reduce_sound h)

/-- Rocq: `Notation.VNotation.step_reduce_sound`. -/
theorem step_reduce_sound {x y : VForm} :
    ClosReflTrans OneStepReduce x y → denote x ≈ denote y
  | .step h => one_step_reduce_sound h
  | .refl _ => equiv_refl _
  | .trans h₁ h₂ => equiv_trans (step_reduce_sound h₁) (step_reduce_sound h₂)

/-- Normality is decidable. Rocq: `Notation.VNotation.VF_isNormal_dec`. -/
def isNormalDec : (x : VForm) → Decidable (IsNormal x)
  | Z => isTrue trivial
  | V a Z =>
    match isNormalDec a with
    | isTrue ha => isTrue ⟨ha, trivial, trivial⟩
    | isFalse ha => isFalse fun h => ha h.1
  | V a (V b y) =>
    match isNormalDec a with
    | isFalse ha => isFalse fun h => ha h.1
    | isTrue ha =>
      match isNormalDec (V b y) with
      | isFalse hx => isFalse fun h => hx h.2.1
      | isTrue hx =>
        match compare b a, compare_correct b a with
        | .lt, h => isTrue ⟨ha, hx, le_of_lt h⟩
        | .eq, h => isTrue ⟨ha, hx, h.le⟩
        | .gt, h => isFalse fun hn => lt_irrefl _ (lt_of_le_of_lt hn.2.2 h)

instance : DecidablePred IsNormal := isNormalDec

private theorem not_reduce_Z : ¬ ∃ z, OneStepReduce Z z := fun ⟨_, h⟩ => by
  cases h with
  | redex h => cases h

/-- Rocq: `Notation.VNotation.VF_notIsNormal_reduce`. -/
theorem notIsNormal_reduce : ∀ x : VForm, ¬ IsNormal x ↔ ∃ z, OneStepReduce x z := by
  intro x
  induction x with
  | Z => exact ⟨fun h => absurd trivial h, fun h => absurd h not_reduce_Z⟩
  | V a x iha ihx =>
    match isNormalDec a with
    | isFalse ha =>
      exact ⟨fun _ => let ⟨z, h⟩ := iha.1 ha; ⟨V z x, .vcong1 h⟩, fun _ h => ha h.1⟩
    | isTrue ha =>
      match isNormalDec x with
      | isFalse hx =>
        exact ⟨fun _ => let ⟨z, h⟩ := ihx.1 hx; ⟨V a z, .vcong2 h⟩, fun _ h => hx h.2.1⟩
      | isTrue hx =>
        constructor
        · intro hn
          cases x with
          | Z => exact absurd ⟨ha, hx, trivial⟩ hn
          | V b y =>
            match decideOrder a b with
            | .inl hab => exact ⟨V b y, .redex (.mk ((lt_correct a b).2 hab))⟩
            | .inr hba => exact absurd ⟨ha, hx, hba⟩ hn
        · rintro ⟨z, hz⟩ hn
          cases hz with
          | redex h =>
            cases h with
            | mk h => exact lt_irrefl _ (lt_of_lt_of_le ((lt_correct _ _).1 h) hn.2.2)
          | vcong1 h => exact iha.2 ⟨_, h⟩ ha
          | vcong2 h => exact ihx.2 ⟨_, h⟩ hx

/-- Rocq: `Notation.VNotation.VF_normal_no_reduce`. -/
theorem normal_no_reduce (x : VForm) : IsNormal x ↔ ¬ ∃ z, OneStepReduce x z :=
  match isNormalDec x with
  | isTrue h => ⟨fun _ hr => (notIsNormal_reduce x).2 hr h, fun _ => h⟩
  | isFalse h => ⟨fun h' => absurd h' h, fun hr => absurd ((notIsNormal_reduce x).1 h) hr⟩

/-- `V a x` and `V b y` with `a < b`, both normal, cannot denote the same
ordinal. -/
private theorem ne_of_first_lt {a b x y : VForm} (hn : IsNormal (V a x)) (hab : denote a < denote b)
    (h : denote (V a x) ≈ denote (V b y)) : False := by
  refine lt_irrefl (denote (V a x)) ?_
  calc denote (V a x)
      < veblen (fun y => 1 + y) (denote a) (denote (V b y)) :=
        veblen_increasing onePlus_normal _ (complete a) _ _ (complete (V b y))
          (lt_of_lt_of_le (denote_shrink2 x a hn) h.le)
    _ ≈ denote (V b y) := veblen_fixpoints onePlus_normal _ _ _ (complete a) (complete b)
          (complete y) hab
    _ ≈ denote (V a x) := equiv_symm h

/-- `V a x` and `V a' y` with `a ≈ a'` and `x < y` cannot denote the same
ordinal. -/
private theorem ne_of_second_lt {a b x y : VForm} (hab : denote a ≈ denote b)
    (hxy : denote x < denote y) (h : denote (V a x) ≈ denote (V b y)) : False := by
  refine lt_irrefl (denote (V a x)) ?_
  calc denote (V a x)
      ≤ veblen (fun y => 1 + y) (denote b) (denote x) :=
        veblen_monotone_first onePlus_normal.monotone _ _ _ hab.le
    _ < denote (V b y) := veblen_increasing onePlus_normal _ (complete b) _ _ (complete y) hxy
    _ ≈ denote (V a x) := equiv_symm h

/-- Rocq: `Notation.VNotation.V_normal_forms_unique`. -/
theorem normal_forms_unique : ∀ x y : VForm, IsNormal x → IsNormal y →
    denote x ≈ denote y → x = y
  | Z, Z, _, _, _ => rfl
  | Z, V _ _, _, _, h => absurd (lt_of_lt_of_le (veblen_nonzero onePlus_normal _ _) h.ge) (lt_irrefl 0)
  | V _ _, Z, _, _, h => absurd (lt_of_lt_of_le (veblen_nonzero onePlus_normal _ _) h.le) (lt_irrefl 0)
  | V a x, V b y, hx, hy, h => by
    have hab : denote a ≈ denote b := by
      have hc := compare_correct a b
      revert hc
      cases compare a b with
      | lt => exact fun hc => (ne_of_first_lt hx hc h).elim
      | eq => exact id
      | gt => exact fun hc => (ne_of_first_lt hy hc (equiv_symm h)).elim
    have hxy : denote x ≈ denote y := by
      have hc := compare_correct x y
      revert hc
      cases compare x y with
      | lt => exact fun hc => (ne_of_second_lt hab hc h).elim
      | eq => exact id
      | gt => exact fun hc => (ne_of_second_lt (equiv_symm hab) hc (equiv_symm h)).elim
    rw [normal_forms_unique a b hx.1 hy.1 hab, normal_forms_unique x y hx.2.1 hy.2.1 hxy]

/-- Build `V a x`, absorbing `a` when `x = V b y` with `a < b`.
Rocq: `Notation.VNotation.Vnorm`. -/
def vnorm (a : VForm) : VForm → VForm
  | Z => V a Z
  | V b y =>
    match compare a b with
    | .gt => V a (V b y)
    | .eq => V a (V b y)
    | .lt => V b y

/-- Rocq: `Notation.VNotation.Vnorm_normal`. -/
theorem vnorm_normal (a : VForm) : ∀ x : VForm, IsNormal a → IsNormal x → IsNormal (vnorm a x)
  | Z, ha, _ => ⟨ha, trivial, trivial⟩
  | V b y, ha, hx => by
    have hc := compare_correct a b
    show IsNormal (match compare a b with
      | .gt => V a (V b y)
      | .eq => V a (V b y)
      | .lt => V b y)
    revert hc
    cases compare a b with
    | gt => exact fun hc => ⟨ha, hx, le_of_lt hc⟩
    | eq => exact fun hc => ⟨ha, hx, hc.ge⟩
    | lt => exact fun _ => hx

/-- Rocq: `Notation.VNotation.Vnorm_V`. -/
theorem vnorm_V (a : VForm) : ∀ x : VForm, denote (V a x) ≈ denote (vnorm a x)
  | Z => equiv_refl _
  | V b y => by
    have hc := compare_correct a b
    show _ ≈ denote (match compare a b with
      | .gt => V a (V b y)
      | .eq => V a (V b y)
      | .lt => V b y)
    revert hc
    cases compare a b with
    | gt => exact fun _ => equiv_refl _
    | eq => exact fun _ => equiv_refl _
    | lt =>
      exact fun hc => veblen_fixpoints onePlus_normal _ _ _ (complete a) (complete b)
        (complete y) hc

/-- Rocq: `Notation.VNotation.Vnorm_reduce`. -/
theorem vnorm_reduce (a : VForm) : ∀ x : VForm, ClosReflTrans OneStepReduce (V a x) (vnorm a x)
  | Z => .refl _
  | V b y => by
    show ClosReflTrans OneStepReduce _ (match compare a b with
      | .gt => V a (V b y)
      | .eq => V a (V b y)
      | .lt => V b y)
    cases hc : compare a b with
    | gt => exact .refl _
    | eq => exact .refl _
    | lt => exact .step (.redex (.mk hc))

/-- Rocq: `Notation.VNotation.Vnormalize`. -/
def normalize : VForm → VForm
  | Z => Z
  | V a y => vnorm (normalize a) (normalize y)

/-- Rocq: `Notation.VNotation.Vnormalize_normal`. -/
theorem normalize_normal : ∀ x : VForm, IsNormal (normalize x)
  | Z => trivial
  | V a y => vnorm_normal _ _ (normalize_normal a) (normalize_normal y)

/-- Rocq: `Notation.VNotation.Vnormalize_equal`. -/
theorem normalize_equal : ∀ x : VForm, denote (normalize x) ≈ denote x
  | Z => equiv_refl _
  | V a y => equiv_trans (equiv_symm (vnorm_V _ _))
      (veblen_onePlus_congr (normalize_equal a) (normalize_equal y))

/-- Rocq: `Notation.VNotation.reduce_many_Vcong1`. -/
theorem reduce_many_Vcong1 {x x' : VForm} (y : VForm) :
    ClosReflTrans OneStepReduce x x' → ClosReflTrans OneStepReduce (V x y) (V x' y)
  | .step h => .step (.vcong1 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (reduce_many_Vcong1 y h₁) (reduce_many_Vcong1 y h₂)

/-- Rocq: `Notation.VNotation.reduce_many_Vcong2`. -/
theorem reduce_many_Vcong2 (x : VForm) {y y' : VForm} :
    ClosReflTrans OneStepReduce y y' → ClosReflTrans OneStepReduce (V x y) (V x y')
  | .step h => .step (.vcong2 h)
  | .refl _ => .refl _
  | .trans h₁ h₂ => .trans (reduce_many_Vcong2 x h₁) (reduce_many_Vcong2 x h₂)

/-- Rocq: `Notation.VNotation.VF_normalize_reduce`. -/
theorem normalize_reduce : ∀ x : VForm, ClosReflTrans OneStepReduce x (normalize x)
  | Z => .refl _
  | V a y => .trans (reduce_many_Vcong1 y (normalize_reduce a))
      (.trans (reduce_many_Vcong2 _ (normalize_reduce y)) (vnorm_reduce _ _))

/-- Reduction is confluent. Rocq: `Notation.VNotation.reduce_confluent`. -/
theorem reduce_confluent {a b c : VForm} (hb : ClosReflTrans OneStepReduce a b)
    (hc : ClosReflTrans OneStepReduce a c) :
    ∃ d, ClosReflTrans OneStepReduce b d ∧ ClosReflTrans OneStepReduce c d ∧
      ¬ ∃ z, OneStepReduce d z := by
  have hbc : normalize b = normalize c :=
    normal_forms_unique _ _ (normalize_normal b) (normalize_normal c)
      (equiv_trans (normalize_equal b) (equiv_trans (equiv_symm (step_reduce_sound hb))
        (equiv_trans (step_reduce_sound hc) (equiv_symm (normalize_equal c)))))
  exact ⟨normalize b, normalize_reduce b, hbc ▸ normalize_reduce c,
    (normal_no_reduce _).1 (normalize_normal b)⟩

/-- `x` reduces to the normal form `y`. Rocq: `Notation.VNotation.normalizes`. -/
inductive Normalizes : VForm → VForm → Prop
  | normal {x : VForm} : (¬ ∃ y, OneStepReduce x y) → Normalizes x x
  | step {x y z : VForm} : OneStepReduce x y → Normalizes y z → Normalizes x z

/-- Rocq: `Notation.VNotation.redex_size`. -/
theorem redex_size {x y : VForm} : Redex x y → size y < size x
  | .mk (a := a) (b := b) (x := x) _ =>
    Nat.lt_succ_of_le (Nat.le_add_left (size b + size x + 1) (size a))

/-- Rocq: `Notation.VNotation.one_step_reduce_size`. -/
theorem one_step_reduce_size {x y : VForm} : OneStepReduce x y → size y < size x
  | .redex h => redex_size h
  | .vcong1 h => Nat.succ_lt_succ (Nat.add_lt_add_right (one_step_reduce_size h) _)
  | .vcong2 h => Nat.succ_lt_succ (Nat.add_lt_add_left (one_step_reduce_size h) _)

/-- Reduction is strongly normalizing.
Rocq: `Notation.VNotation.strongly_normalizing`. -/
theorem strongly_normalizing (x : VForm) : ∃ y, Normalizes x y := by
  suffices h : ∀ n x, size x < n → ∃ y, Normalizes x y from h _ x (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun x h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx
    match isNormalDec x with
    | isTrue h => exact ⟨x, .normal ((normal_no_reduce x).1 h)⟩
    | isFalse h =>
      obtain ⟨y, hy⟩ := (notIsNormal_reduce x).1 h
      obtain ⟨z, hz⟩ := ih y (Nat.lt_of_lt_of_le (one_step_reduce_size hy) (Nat.le_of_lt_succ hx))
      exact ⟨z, .step hy hz⟩

/-- Rocq: `Notation.VNotation.normalizes_correct`. -/
theorem normalizes_correct {x y : VForm} : Normalizes x y → denote x ≈ denote y ∧ IsNormal y
  | .normal h => ⟨equiv_refl _, (normal_no_reduce _).2 h⟩
  | .step h₁ h₂ =>
    let ih := normalizes_correct h₂
    ⟨equiv_trans (one_step_reduce_sound h₁) ih.1, ih.2⟩

/-- Rocq: `Notation.VNotation.normalizes_iff`. -/
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

open CantorDecomposition Interpolants

/-- Rocq: `Notation.VNotation.VF_decompose`. -/
def decompose : VForm → List VForm
  | Z => []
  | V a b => a :: decompose b

/-- Rocq: `Notation.VNotation.VF_recompose`. -/
def recompose : List VForm → VForm
  | [] => Z
  | x :: xs' => V x (recompose xs')

/-- Rocq: `Notation.VNotation.VF_decompose_correct`. -/
theorem decompose_correct : ∀ x : VForm, IsNormal x →
    Each IsNormal (decompose x) ∧ CantorOrdered denote (decompose x) ∧
      denote x ≈ cantorDenote denote (decompose x)
  | Z, _ => ⟨trivial, trivial, equiv_refl _⟩
  | V a b, h =>
    let ih := decompose_correct b h.2.1
    ⟨⟨h.1, ih.1⟩,
      ⟨match b, h with
        | Z, _ => trivial
        | V _ _, h => h.2.2, ih.2.1⟩,
      equiv_trans (veblen_onePlus _ (complete a) _ (complete b))
        (add_congr (equiv_refl _) ih.2.2)⟩

/-- Rocq: `Notation.VNotation.VF_recompose_correct`. -/
theorem recompose_correct : ∀ xs : List VForm, Each IsNormal xs → CantorOrdered denote xs →
    IsNormal (recompose xs) ∧ cantorDenote denote xs ≈ denote (recompose xs)
  | [], _, _ => ⟨trivial, equiv_refl _⟩
  | x :: xs, hP, hord =>
    let ih := recompose_correct xs hP.2 hord.2
    ⟨⟨hP.1, ih.1,
        match xs, hord with
        | [], _ => trivial
        | _ :: _, hord => hord.1⟩,
      equiv_trans (add_congr (equiv_refl _) ih.2)
        (equiv_symm (veblen_onePlus _ (complete x) _ (complete _)))⟩

/-- Rocq: `Notation.VNotation.VF_has_cantor_decomposition`. -/
def hasCantorDecomposition : HasCantorDecomposition denote IsNormal where
  compare := compare
  decompose := decompose
  recompose := recompose
  complete := complete
  compare_correct x y _ _ := compare_correct x y
  decompose_correct := decompose_correct
  recompose_correct := recompose_correct

/-- Rocq: `Notation.VNotation.VF_succ`. -/
def succ : VForm → VForm := cantorSucc hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_add`. -/
def add : VForm → VForm → VForm := cantorAdd hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_mul`. -/
def mul : VForm → VForm → VForm := cantorMul hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_exp`. -/
def exp : VForm → VForm → VForm := cantorExp hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_one`. -/
def one : VForm := V Z Z

/-- Rocq: `Notation.VNotation.VF_expOmega`. -/
def expOmega (x : VForm) : VForm := vnorm x Z

/-- Rocq: `Notation.VNotation.VF_reflects_zero`. -/
theorem reflects_zero : Reflects VForm denote IsNormal .ord 0 Z := ⟨equiv_refl _, trivial⟩

/-- Rocq: `Notation.VNotation.VF_reflects_one`. -/
theorem reflects_one : Reflects VForm denote IsNormal .ord 1 one :=
  ⟨equiv_symm (equiv_trans (veblen_onePlus _ zero_complete _ zero_complete)
      (equiv_trans (add_zero _) (pow_zero ω))), trivial, trivial, trivial⟩

/-- Rocq: `Notation.VNotation.VF_succ_reflects`. -/
theorem succ_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Ordinal.succ succ :=
  cantor_succ_reflects hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_add_reflects`. -/
theorem add_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· + ·) add :=
  cantor_add_reflects hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_mul_reflects`. -/
theorem mul_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· * ·) mul :=
  cantor_mul_reflects hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_exp_reflects`. -/
theorem exp_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ^ ·) exp :=
  cantor_exp_reflects hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_reflects_expOmega`. -/
theorem reflects_expOmega :
    Reflects VForm denote IsNormal (.ord ==> .ord) (fun x => ω ^ x) expOmega :=
  fun _ a ⟨hxa, ha⟩ =>
    ⟨equiv_symm (equiv_trans (veblen_onePlus _ (complete a) _ zero_complete)
        (equiv_trans (add_zero _) (pow_congr (equiv_refl ω) (equiv_symm hxa)))),
      ha, trivial, trivial⟩

end VForm

open VForm in
/-- The Veblen forms have order type `ε 0`. Rocq: `Notation.VNotation.VF_ε₀`. -/
theorem VF_ε₀ : VF ≈ ε 0 :=
  equiv_intro (le_intro fun x => below_ε₀ x)
    (ε0_least_exp_closed VForm denote IsNormal Z VForm.succ expOmega
      (fun x => ⟨normalize x, equiv_symm (normalize_equal x), normalize_normal x⟩)
      reflects_zero succ_reflects reflects_expOmega)

namespace VForm

open CantorDecomposition Interpolants

/-- Rocq: `Notation.VNotation.VF_has_all_interpolants`. -/
theorem has_all_interpolants : HasAllInterpolants denote IsNormal := by
  have hg₂ : ∀ b, Complete b → HasInterpolants denote IsNormal b →
      HasInterpolants denote IsNormal (1 + b) := fun b _ hb =>
    onePlus_interpolants Z reflects_zero (add one) (fun x a h => add_reflects 1 one reflects_one x a h) b hb
  have hvr : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (veblen fun y => 1 + y) vnorm :=
    fun _ a ⟨hxa, ha⟩ _ b ⟨hyb, hb⟩ =>
      ⟨equiv_trans (veblen_onePlus_congr hxa hyb) (vnorm_V a b), vnorm_normal a b ha hb⟩
  intro x
  induction x with
  | Z =>
    exact fun _ => (has_interpolants_unfold _).2 fun i hi =>
      (lt_irrefl i (lt_of_lt_of_le hi (zero_least i))).elim
  | V a b iha ihb =>
    exact fun h => veblen_interpolants hasCantorDecomposition.complete (fun y => 1 + y) onePlus_normal hg₂
      vnorm hvr a (denote b) h.1 (iha h.1) (complete b) (ihb h.2.1)

/-- Rocq: `Notation.VNotation.VF_nadd`. -/
def nadd : VForm → VForm → VForm := cantorNadd hasCantorDecomposition

/-- Rocq: `Notation.VNotation.VF_reflects_nadd`. -/
theorem reflects_nadd : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ♯ ·) nadd :=
  cantor_nadd_reflects hasCantorDecomposition

/-- With the excluded middle, every ordinal below `ε 0` has a Veblen form.
Rocq: `Notation.VNotation.VF_has_enough_notations`. -/
theorem has_enough_notations (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < ε 0 → ∃ c : VForm, sz c ≈ x := by
  intro x hx
  obtain ⟨a, ha⟩ := lt_elim (lt_of_lt_of_le hx VF_ε₀.ge)
  obtain ⟨c, _, hc⟩ := has_interpolants_has_enough_notations em has_all_interpolants
    (normalize a) x (normalize_normal a) (le_trans ha (normalize_equal a).ge)
  exact ⟨c, hc⟩

/-- Rocq: `Notation.VNotation.VF_has_enough_notations'`. -/
theorem has_enough_notations' (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < ε 0 → ∃ c : VForm, x ≈ sz c := fun x hx =>
  let ⟨c, hc⟩ := has_enough_notations em x hx
  ⟨c, equiv_symm hc⟩

/-! ## Sample computations -/

/-- `ω ^ ω` and `ω + ω` compare correctly (checked by kernel reduction). -/
theorem sample_compare : compare (expOmega (expOmega one)) (add (expOmega one) (expOmega one)) = .gt :=
  rfl

end VForm

end ConstructiveOrdinals.VNotation
