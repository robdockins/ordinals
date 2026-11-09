import ConstructiveOrdinals.Cantor
import ConstructiveOrdinals.Reflection
import ConstructiveOrdinals.Classical

/-!
# Cantor normal forms: a notation system for ε₀

Port of `Ordinal/Notation/CantorNotation.v`.

A Cantor form `sum [x₁, …, xₙ]` denotes `ω ^ x₁ + ⋯ + ω ^ xₙ`. There are no
natural-number coefficients: repeated terms stand for multiples. A form is
*normal* when its exponents are non-increasing and its subterms are normal.

The development proves that comparison, addition, multiplication and
exponentiation on normal forms are correct, that normal forms denote exactly
the ordinals below `ε 0`, and that "every ordinal below `ε 0` has a normal
form" is equivalent to the excluded middle.

Lean notes:

- `CantorForm` is a nested inductive type (`List CantorForm`), as in Rocq.
  Recursive functions on it are written as a pair of mutually recursive
  functions, one on forms and one on lists of forms, instead of Rocq's inner
  `fix` or `fold_right`. Proofs about them are mutually recursive theorems in
  the same shape.
- The Rocq canonical structures `CF` and `CNF` are the ordinals `CF` and `CNF`
  together with `Sized` instances on `CantorForm` and `CantorNormalForm`.
- A `match` on a comparison result inside a statement (`match cantorCompare a
  b with LT => … | EQ => … | GT => … end`) is written `OrderingCorrect`, which
  is the same proposition by definition (`Defs.ordering_correct`).
-/

namespace ConstructiveOrdinals.CantorNotation

open Ordinal

/-- Cantor forms: `sum xs` denotes the sum of `ω ^ x` over `x ∈ xs`.
Rocq: `Notation.CantorNotation.CantorForm`. -/
inductive CantorForm : Type where
  | sum : List CantorForm → CantorForm

namespace CantorForm

mutual
/-- The ordinal denoted by a Cantor form. Rocq: `Notation.CantorNotation.CF_denote`. -/
def denote : CantorForm → Ordinal.{0}
  | sum xs => denoteList xs

/-- `ω ^ x₁ + (ω ^ x₂ + ⋯ + 0)`, the Rocq `fold_right` in `CF_denote`. -/
def denoteList : List CantorForm → Ordinal.{0}
  | [] => 0
  | x :: xs => ω ^ denote x + denoteList xs
end

instance : Sized CantorForm := ⟨denote⟩

theorem denote_sum (xs : List CantorForm) : denote (sum xs) = denoteList xs := rfl

theorem denote_cons (x : CantorForm) (xs : List CantorForm) :
    denote (sum (x :: xs)) = ω ^ denote x + denote (sum xs) := rfl

end CantorForm

/-- The ordinal of all Cantor forms. Rocq: `Notation.CantorNotation.CF`. -/
def CF : Ordinal.{0} := mk CantorForm CantorForm.denote

namespace CantorForm

mutual
/-- A Cantor form is normal when its exponents are non-increasing and its
subterms are normal. Rocq: `Notation.CantorNotation.cantorIsNormal`. -/
def IsNormal : CantorForm → Prop
  | sum [] => True
  | sum (x :: xs) => IsNormal x ∧ IsNormalSeq x xs

/-- The terms after `x` are normal and non-increasing, starting at most at `x`.
The inner `check` of Rocq's `cantorIsNormal`. -/
def IsNormalSeq (x : CantorForm) : List CantorForm → Prop
  | [] => True
  | x' :: xs' => IsNormal x' ∧ denote x' ≤ denote x ∧ IsNormalSeq x' xs'
end

theorem IsNormal.head {x : CantorForm} {xs : List CantorForm} (h : IsNormal (sum (x :: xs))) :
    IsNormal x := h.1

theorem IsNormal.tail {x : CantorForm} :
    ∀ {xs : List CantorForm}, IsNormal (sum (x :: xs)) → IsNormal (sum xs)
  | [], _ => trivial
  | _ :: _, h => ⟨h.2.1, h.2.2.2⟩

theorem IsNormal.head_le {x y : CantorForm} {xs : List CantorForm}
    (h : IsNormal (sum (x :: y :: xs))) : denote y ≤ denote x := h.2.2.1

end CantorForm

/-- Normal Cantor forms. Rocq: `Notation.CantorNotation.CantorNormalForm`. -/
def CantorNormalForm : Type := { cf : CantorForm // cf.IsNormal }

namespace CantorNormalForm

/-- Rocq: `Notation.CantorNotation.CNF_denote`. -/
def denote (x : CantorNormalForm) : Ordinal.{0} := x.1.denote

instance : Sized CantorNormalForm := ⟨denote⟩

end CantorNormalForm

/-- The ordinal of all Cantor normal forms. Rocq: `Notation.CantorNotation.CNF`. -/
def CNF : Ordinal.{0} := mk CantorNormalForm CantorNormalForm.denote

namespace CantorForm

mutual
/-- Lexicographic comparison of Cantor forms. It is correct on normal forms.
Rocq: `Notation.CantorNotation.cantorCompare`. -/
def compare : CantorForm → CantorForm → Ordering
  | sum xs, sum ys => compareList xs ys

/-- The inner `cantorSumCompare` of Rocq's `cantorCompare`. -/
def compareList : List CantorForm → List CantorForm → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => lexCompare (compare x y) (compareList xs ys)
end

mutual
/-- Rocq: `Notation.CantorNotation.cantorCompare_swap`. -/
theorem compare_swap : ∀ x y : CantorForm, compare x y = (compare y x).swap
  | sum xs, sum ys => compareList_swap xs ys

theorem compareList_swap : ∀ xs ys : List CantorForm, compareList xs ys = (compareList ys xs).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    show lexCompare (compare x y) (compareList xs ys)
      = (lexCompare (compare y x) (compareList ys xs)).swap
    rw [compare_swap x y, compareList_swap xs ys, lexCompare_swap]
end

mutual
/-- Rocq: `Notation.CantorNotation.CantorForm_complete`. -/
theorem denote_complete : ∀ x : CantorForm, Complete (denote x)
  | sum xs => denoteList_complete xs

theorem denoteList_complete : ∀ xs : List CantorForm, Complete (denoteList xs)
  | [] => zero_complete
  | x :: xs => add_complete (pow_complete omega_gt0 omega_complete (denote_complete x))
      (denoteList_complete xs)
end

mutual
/-- Every Cantor form is smaller than `ω` to its power. This is what places
all Cantor forms below `ε 0`. Rocq: `Notation.CantorNotation.CF_denote_shrink`. -/
theorem denote_shrink : ∀ x : CantorForm, denote x < ω ^ denote x
  | sum xs => denoteList_shrink xs

theorem denoteList_shrink : ∀ xs : List CantorForm, denoteList xs < ω ^ denoteList xs
  | [] => pow_pos ω 0
  | x :: xs =>
    powOmega_additively_closed (denoteList_complete (x :: xs)) _ _
      (pow_lt_pow_right omega_gt1 (lt_of_lt_of_le (denote_shrink x) (le_add_right _ _)))
      (lt_of_lt_of_le (denoteList_shrink xs) (pow_le_pow_right ω (le_add_left _ _)))
end

mutual
/-- Rocq: `Notation.CantorNotation.CF_below_epsilon`. -/
theorem below_epsilon : ∀ x : CantorForm, denote x < ε 0
  | sum xs => denoteList_below_epsilon xs

theorem denoteList_below_epsilon : ∀ xs : List CantorForm, denoteList xs < ε 0
  | [] => lt_of_lt_of_le (pow_pos ω _) (ε_fixpoint 0).ge
  | x :: xs =>
    epsilon_additively_closed zero_complete _ _
      (lt_of_lt_of_le (pow_lt_pow_right omega_gt1 (below_epsilon x)) (ε_fixpoint 0).ge)
      (denoteList_below_epsilon xs)
end

end CantorForm

namespace CantorNormalForm

open CantorForm

/-- Rocq: `Notation.CantorNotation.CantorNormalForm_lt`. -/
def Lt (x y : CantorNormalForm) : Prop := CantorForm.compare x.1 y.1 = .lt

/-- Rocq: `Notation.CantorNotation.CantorNormalForm_le`. -/
def Le (x y : CantorNormalForm) : Prop := CantorForm.compare x.1 y.1 ≠ .gt

end CantorNormalForm

namespace CantorForm

/-- If `c` is smaller than `a`, then so is everything after `c` in a normal
sum: `ω ^ a` bounds the rest of the sum.
Rocq: `Notation.CantorNotation.CNF_compare_correct_lemma`. -/
theorem compare_correct_lemma (a : CantorForm) :
    ∀ (lsb : List CantorForm) (c : CantorForm), IsNormal (sum (c :: lsb)) → IsNormal a →
      IsNormal c → denote c < denote a → denoteList lsb < ω ^ denote a
  | [], _, _, _, _, _ => pow_pos ω _
  | b :: lsb, _, h, ha, _, hca =>
    powOmega_additively_closed (denote_complete a) _ _
      (pow_lt_pow_right omega_gt1 (lt_of_le_of_lt h.head_le hca))
      (compare_correct_lemma a lsb b h.tail ha h.tail.head
        (lt_of_le_of_lt h.head_le hca))

end CantorForm

/-- `a < b + a` when `a` is complete, `a ≤ b` and `0 < b`: a strict version of
`le_add_left`. Rocq: `Notation.CantorNotation.addOrd_lt2`. -/
theorem lt_add_left {a b : Ordinal.{0}} (ha : Complete a) (hab : a ≤ b) (hb : 0 < b) : a < b + a :=
  match complete_zeroDec ha with
  | .inl h => lt_of_le_of_lt h (lt_of_lt_of_le hb (le_add_right b a))
  | .inr h =>
    let ⟨a₀, _⟩ := lt_elim h
    lt_of_le_of_lt (le_trans hab (le_add_right b (a a₀))) (add_lt_add_left b (index_lt a a₀))

namespace CantorForm

mutual
/-- Comparison is correct on normal forms.
Rocq: `Notation.CantorNotation.CNF_compare_correct`. -/
theorem compare_correct : ∀ a b : CantorForm, IsNormal a → IsNormal b →
    OrderingCorrect (compare a b) (denote a) (denote b)
  | sum xs, sum ys, ha, hb => compareList_correct xs ys ha hb

theorem compareList_correct : ∀ xs ys : List CantorForm, IsNormal (sum xs) → IsNormal (sum ys) →
    OrderingCorrect (compareList xs ys) (denoteList xs) (denoteList ys)
  | [], [], _, _ => equiv_refl _
  | [], _ :: _, _, _ => lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)
  | _ :: _, [], _, _ => lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)
  | a :: lsa, c :: lsb, ha, hc => by
    have hac := compare_correct a c ha.head hc.head
    have hl := compareList_correct lsa lsb ha.tail hc.tail
    show OrderingCorrect (lexCompare (compare a c) (compareList lsa lsb))
      (ω ^ denote a + denoteList lsa) (ω ^ denote c + denoteList lsb)
    revert hac
    cases compare a c with
    | lt =>
      intro hac
      exact lt_of_lt_of_le
        (powOmega_additively_closed (denote_complete c) _ _ (pow_lt_pow_right omega_gt1 hac)
          (compare_correct_lemma c lsa a ha hc.head ha.head hac))
        (le_add_right _ _)
    | gt =>
      intro hac
      exact lt_of_lt_of_le
        (powOmega_additively_closed (denote_complete a) _ _ (pow_lt_pow_right omega_gt1 hac)
          (compare_correct_lemma a lsb c hc ha.head hc.head hac))
        (le_add_right _ _)
    | eq =>
      intro hac
      revert hl
      cases compareList lsa lsb with
      | lt =>
        intro hl
        exact lt_of_le_of_lt (add_le_add (pow_le_pow_right ω hac.le) (le_refl _))
          (add_lt_add_left _ hl)
      | eq => exact fun hl => add_congr (pow_congr (equiv_refl ω) hac) hl
      | gt =>
        intro hl
        exact lt_of_le_of_lt (add_le_add (pow_le_pow_right ω hac.ge) (le_refl _))
          (add_lt_add_left _ hl)
end

end CantorForm

namespace CantorNormalForm

open CantorForm

/-- Rocq: `Notation.CantorNotation.CNF_lt_reflects`. -/
theorem lt_reflects : Reflects CantorNormalForm denote (fun _ => True) (.ord ==> .ord ==> .prop)
    (fun x y => ULift.up (x < y)) Lt := by
  intro x a ⟨hxa, _⟩ y b ⟨hyb, _⟩
  show x < y ↔ CantorForm.compare a.1 b.1 = .lt
  have h := compare_correct a.1 b.1 a.2 b.2
  revert h
  cases CantorForm.compare a.1 b.1 with
  | lt => exact fun h => ⟨fun _ => rfl, fun _ => lt_of_le_of_lt hxa.le (lt_of_lt_of_le h hyb.ge)⟩
  | eq =>
    refine fun h => ⟨fun hxy => absurd ?_ (lt_irrefl x), fun h' => (nomatch h')⟩
    exact lt_of_lt_of_le hxy (le_trans hyb.le (le_trans h.ge hxa.ge))
  | gt =>
    refine fun h => ⟨fun hxy => absurd ?_ (lt_irrefl x), fun h' => (nomatch h')⟩
    exact lt_trans hxy (lt_of_le_of_lt hyb.le (lt_of_lt_of_le h hxa.ge))

/-- Rocq: `Notation.CantorNotation.CNF_le_reflects`. -/
theorem le_reflects : Reflects CantorNormalForm denote (fun _ => True) (.ord ==> .ord ==> .prop)
    (fun x y => ULift.up (x ≤ y)) Le := by
  intro x a ⟨hxa, _⟩ y b ⟨hyb, _⟩
  show x ≤ y ↔ CantorForm.compare a.1 b.1 ≠ .gt
  have h := compare_correct a.1 b.1 a.2 b.2
  revert h
  cases CantorForm.compare a.1 b.1 with
  | lt => exact fun h => ⟨fun _ h' => (nomatch h'),
      fun _ => le_trans hxa.le (le_trans (le_of_lt h) hyb.ge)⟩
  | eq => exact fun h => ⟨fun _ h' => (nomatch h'), fun _ => le_trans hxa.le (le_trans h.le hyb.ge)⟩
  | gt =>
    refine fun h => ⟨fun hxy => absurd ?_ (lt_irrefl x), fun h' => absurd rfl h'⟩
    exact lt_of_le_of_lt hxy (lt_of_le_of_lt hyb.le (lt_of_lt_of_le h hxa.ge))

/-- The order on normal forms is decidable.
Rocq: `Notation.CantorNotation.CNF_decide_order`. -/
def decideOrder (x y : CantorNormalForm) : PSum (sz x < sz y) (sz y ≤ sz x) :=
  match CantorForm.compare x.1 y.1, compare_correct x.1 y.1 x.2 y.2 with
  | .lt, h => .inl h
  | .eq, h => .inr h.ge
  | .gt, h => .inr (le_of_lt h)

end CantorNormalForm

namespace CantorForm

/-- Rocq: `Notation.CantorNotation.CF_subterm_head`. -/
theorem subterm_head (a : CantorForm) (xs : List CantorForm) : a ◃ sum (a :: xs) :=
  lt_of_lt_of_le (denote_shrink a) (le_add_right _ _)

/-- Rocq: `Notation.CantorNotation.CF_subterm_tail`. -/
theorem subterm_tail : ∀ (a : CantorForm) (xs : List CantorForm),
    IsNormal (sum (a :: xs)) → sum xs ◃ sum (a :: xs)
  | _a, [], _ => lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)
  | _, b :: xs, h =>
    lt_of_lt_of_le (add_lt_add_left _ (subterm_tail b xs h.tail))
      (add_le_add (pow_le_pow_right ω h.head_le) (le_refl _))

/-- A sum starting with a strictly smaller exponent is strictly smaller than
one starting with a larger exponent, so their denotations differ. -/
private theorem ne_of_head_lt {a c : CantorForm} {xs ys : List CantorForm}
    (hn : IsNormal (sum (a :: xs))) (hac : denote a < denote c)
    (h : denote (sum (a :: xs)) ≈ denote (sum (c :: ys))) : False := by
  refine lt_irrefl (ω ^ denote a + denoteList xs) ?_
  calc ω ^ denote a + denoteList xs
      < ω ^ denote a + (ω ^ denote c + denoteList ys) :=
        add_lt_add_left _ (lt_of_lt_of_le (subterm_tail a xs hn) h.le)
    _ ≈ (ω ^ denote a + ω ^ denote c) + denoteList ys := add_assoc _ _ _
    _ ≤ ω ^ denote c + denoteList ys :=
        add_le_add (pow_add_collapse (denote_complete c) hac) (le_refl _)
    _ ≈ ω ^ denote a + denoteList xs := equiv_symm h

mutual
/-- Normal forms are unique. Rocq: `Notation.CantorNotation.CF_normal_forms_unique`. -/
theorem normal_forms_unique : ∀ x y : CantorForm, IsNormal x → IsNormal y →
    denote x ≈ denote y → x = y
  | sum xs, sum ys, hx, hy, h => congrArg sum (normalList_unique xs ys hx hy h)

theorem normalList_unique : ∀ xs ys : List CantorForm, IsNormal (sum xs) → IsNormal (sum ys) →
    denoteList xs ≈ denoteList ys → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h =>
    absurd (lt_of_lt_of_le (lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)) h.ge) (lt_irrefl 0)
  | _ :: _, [], _, _, h =>
    absurd (lt_of_lt_of_le (lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)) h.le) (lt_irrefl 0)
  | a :: xs, c :: ys, hx, hy, h => by
    have hac : denote a ≈ denote c := by
      have hc := compare_correct a c hx.head hy.head
      revert hc
      cases compare a c with
      | lt => exact fun hc => (ne_of_head_lt hx hc h).elim
      | eq => exact id
      | gt => exact fun hc => (ne_of_head_lt hy hc (equiv_symm h)).elim
    have h₁ := normal_forms_unique a c hx.head hy.head hac
    have h₂ := normalList_unique xs ys hx.tail hy.tail
      (add_cancel h (pow_congr (equiv_refl ω) hac))
    rw [h₁, h₂]
end

end CantorForm

/-! ## Normalization -/

namespace CantorForm

/-- Put `ω ^ x` in front of the normal sum `r`, dropping it if it is smaller
than the leading term of `r`. This is the step shared by Rocq's `normalize`
and `cantorSum_add`, which both write it out inline. -/
def push (x : CantorForm) : List CantorForm → List CantorForm
  | [] => [x]
  | z :: zs =>
    match compare x z with
    | .lt => z :: zs
    | .eq => x :: z :: zs
    | .gt => x :: z :: zs

theorem push_normal (x : CantorForm) :
    ∀ r : List CantorForm, IsNormal x → IsNormal (sum r) → IsNormal (sum (push x r))
  | [], hx, _ => ⟨hx, trivial⟩
  | z :: zs, hx, hr => by
    have h := compare_correct x z hx hr.head
    show IsNormal (sum (match compare x z with
      | .lt => z :: zs
      | .eq => x :: z :: zs
      | .gt => x :: z :: zs))
    revert h
    cases compare x z with
    | lt => exact fun _ => hr
    | eq => exact fun h => ⟨hx, hr.1, h.ge, hr.2⟩
    | gt => exact fun h => ⟨hx, hr.1, le_of_lt h, hr.2⟩

theorem push_correct (x : CantorForm) :
    ∀ r : List CantorForm, IsNormal x → IsNormal (sum r) →
      denoteList (push x r) ≈ ω ^ denote x + denoteList r
  | [], _, _ => equiv_refl _
  | z :: zs, hx, hr => by
    have h := compare_correct x z hx hr.head
    show denoteList (match compare x z with
      | .lt => z :: zs
      | .eq => x :: z :: zs
      | .gt => x :: z :: zs) ≈ _
    revert h
    cases compare x z with
    | lt =>
      refine fun h => equiv_intro (le_add_left _ _) ?_
      calc ω ^ denote x + (ω ^ denote z + denoteList zs)
          ≈ (ω ^ denote x + ω ^ denote z) + denoteList zs := add_assoc _ _ _
        _ ≤ ω ^ denote z + denoteList zs :=
            add_le_add (pow_add_collapse (denote_complete z) h) (le_refl _)
    | eq => exact fun _ => equiv_refl _
    | gt => exact fun _ => equiv_refl _

mutual
/-- Compute an equivalent normal form. Rocq: `Notation.CantorNotation.normalize`. -/
def normalize : CantorForm → CantorForm
  | sum [] => sum []
  | sum (x :: xs) => sum (normalizeSeq (normalize x) xs)

/-- Normalize `ω ^ x + xs`, where `x` is already normal. The inner
`normalizeSeq` of Rocq's `normalize`. -/
def normalizeSeq (x : CantorForm) : List CantorForm → List CantorForm
  | [] => [x]
  | y :: ys => push x (normalizeSeq (normalize y) ys)
end

mutual
/-- Rocq: `Notation.CantorNotation.normalize_is_normal`. -/
theorem normalize_is_normal : ∀ x : CantorForm, IsNormal (normalize x)
  | sum [] => trivial
  | sum (x :: xs) => normalizeSeq_normal (normalize x) xs (normalize_is_normal x)

theorem normalizeSeq_normal (x : CantorForm) :
    ∀ xs : List CantorForm, IsNormal x → IsNormal (sum (normalizeSeq x xs))
  | [], hx => ⟨hx, trivial⟩
  | y :: ys, hx =>
    push_normal x _ hx (normalizeSeq_normal (normalize y) ys (normalize_is_normal y))
end

mutual
/-- Rocq: `Notation.CantorNotation.normalize_is_equal`. -/
theorem normalize_is_equal : ∀ x : CantorForm, denote x ≈ denote (normalize x)
  | sum [] => equiv_refl _
  | sum (x :: xs) =>
    calc ω ^ denote x + denoteList xs
        ≈ ω ^ denote (normalize x) + denoteList xs :=
          add_congr (pow_congr (equiv_refl ω) (normalize_is_equal x)) (equiv_refl _)
      _ ≈ denoteList (normalizeSeq (normalize x) xs) :=
          normalizeSeq_equal (normalize x) xs (normalize_is_normal x)

theorem normalizeSeq_equal (x : CantorForm) :
    ∀ xs : List CantorForm, IsNormal x → ω ^ denote x + denoteList xs ≈ denoteList (normalizeSeq x xs)
  | [], _ => equiv_refl _
  | y :: ys, hx =>
    calc ω ^ denote x + (ω ^ denote y + denoteList ys)
        ≈ ω ^ denote x + (ω ^ denote (normalize y) + denoteList ys) :=
          add_congr (equiv_refl _)
            (add_congr (pow_congr (equiv_refl ω) (normalize_is_equal y)) (equiv_refl _))
      _ ≈ ω ^ denote x + denoteList (normalizeSeq (normalize y) ys) :=
          add_congr (equiv_refl _) (normalizeSeq_equal (normalize y) ys (normalize_is_normal y))
      _ ≈ denoteList (push x (normalizeSeq (normalize y) ys)) :=
          equiv_symm (push_correct x _ hx
            (normalizeSeq_normal (normalize y) ys (normalize_is_normal y)))
end

/-- Every Cantor form has an equivalent normal form.
Rocq: `Notation.CantorNotation.CF_normalize`. -/
def toCNF (x : CantorForm) : CantorNormalForm := ⟨normalize x, normalize_is_normal x⟩

/-- Rocq: `Notation.CantorNotation.CF_normalize_equal`. -/
theorem toCNF_equal (x : CantorForm) : denote x ≈ (toCNF x).denote := normalize_is_equal x

end CantorForm

/-- Cantor forms and Cantor normal forms have the same order type.
Rocq: `Notation.CantorNotation.CF_CNF`. -/
theorem CF_CNF : CF ≈ CNF :=
  equiv_intro (le_intro fun x => lt_intro (CantorForm.toCNF x) (CantorForm.toCNF_equal x).le)
    (le_intro fun x => lt_intro x.1 (le_refl _))

/-! ## Constants -/

namespace CantorForm

/-- Rocq: `Notation.CantorNotation.CF_zero`. -/
def zero : CantorForm := sum []

/-- Rocq: `Notation.CantorNotation.CF_one`. -/
def one : CantorForm := sum [zero]

/-- Rocq: `Notation.CantorNotation.CF_omega`. -/
def omega : CantorForm := sum [one]

/-- Rocq: `Notation.CantorNotation.CF_zero_normal`. -/
theorem zero_normal : IsNormal zero := trivial

/-- Rocq: `Notation.CantorNotation.CF_one_normal`. -/
theorem one_normal : IsNormal one := ⟨trivial, trivial⟩

/-- Rocq: `Notation.CantorNotation.CF_omega_normal`. -/
theorem omega_normal : IsNormal omega := ⟨⟨trivial, trivial⟩, trivial⟩

end CantorForm

namespace CantorNormalForm

open CantorForm

/-- Rocq: `Notation.CantorNotation.CNF_zero`. -/
def zero : CantorNormalForm := ⟨CantorForm.zero, zero_normal⟩

/-- Rocq: `Notation.CantorNotation.CNF_one`. -/
def one : CantorNormalForm := ⟨CantorForm.one, one_normal⟩

/-- Rocq: `Notation.CantorNotation.CNF_omega`. -/
def omega : CantorNormalForm := ⟨CantorForm.omega, omega_normal⟩

/-- Rocq: `Notation.CantorNotation.CNF_reflects_zero`. -/
theorem reflects_zero : Reflects CantorNormalForm denote (fun _ => True) .ord 0 zero :=
  ⟨equiv_refl _, trivial⟩

/-- Rocq: `Notation.CantorNotation.CNF_reflects_one`. -/
theorem reflects_one : Reflects CantorNormalForm denote (fun _ => True) .ord 1 one :=
  ⟨equiv_symm (equiv_trans (add_zero _) (pow_zero ω)), trivial⟩

/-- Rocq: `Notation.CantorNotation.CNF_reflects_omega`. -/
theorem reflects_omega : Reflects CantorNormalForm denote (fun _ => True) .ord ω omega :=
  ⟨equiv_symm (equiv_trans (add_zero _) (equiv_trans
      (pow_congr (equiv_refl ω) (equiv_trans (add_zero _) (pow_zero ω))) (pow_one' omega_gt0))),
    trivial⟩

end CantorNormalForm

/-! ## Finite forms -/

namespace CantorForm

/-- The natural number a form denotes, if it is visibly finite.
Rocq: `Notation.CantorNotation.cantorIsFinite`. -/
def isFinite : CantorForm → Option Nat
  | sum [] => some 0
  | sum (sum [] :: xs) => some (xs.length + 1)
  | sum (sum (_ :: _) :: _) => none

/-- A normal sequence of terms at most `c ≈ 0` denotes its length. -/
private theorem denoteList_zeros : ∀ (c : CantorForm) (xs : List CantorForm),
    denote c ≈ 0 → IsNormalSeq c xs → denoteList xs ≈ ofNat xs.length
  | _, [], _, _ => equiv_refl _
  | _, b :: xs, hc, h =>
    have hb : denote b ≈ 0 := equiv_intro (le_trans h.2.1 hc.le) (zero_least _)
    calc ω ^ denote b + denoteList xs
        ≈ ω ^ 0 + ofNat xs.length :=
          add_congr (pow_congr (equiv_refl ω) hb) (denoteList_zeros b xs hb h.2.2)
      _ ≈ 1 + ofNat xs.length := add_congr (pow_zero ω) (equiv_refl _)
      _ ≈ ofNat (xs.length + 1) := equiv_symm (ofNat_add _ 1)

/-- Rocq: `Notation.CantorNotation.cantorIsFinite_fin`. -/
theorem isFinite_fin : ∀ (x : CantorForm) (n : Nat),
    IsNormal x → isFinite x = some n → denote x ≈ ofNat n
  | sum [], _, _, h => by cases h; exact equiv_refl _
  | sum (sum [] :: xs), _, hx, h => by
    cases h
    exact calc ω ^ (0 : Ordinal.{0}) + denoteList xs
        ≈ 1 + ofNat xs.length :=
          add_congr (pow_zero ω) (denoteList_zeros (sum []) xs (equiv_refl _) hx.2)
      _ ≈ ofNat (xs.length + 1) := equiv_symm (ofNat_add _ 1)
  | sum (sum (_ :: _) :: _), _, _, h => nomatch h

/-- Rocq: `Notation.CantorNotation.cantorIsFinite_inf`. -/
theorem isFinite_inf : ∀ x : CantorForm, isFinite x = none → 1 + denote x ≈ denote x
  | sum [], h => nomatch h
  | sum (sum [] :: _), h => nomatch h
  | sum (sum (c :: cs) :: xs), _ => by
    have he : 1 ≤ denote (sum (c :: cs)) := le_trans (succ_least (pow_pos ω _)) (le_add_right _ _)
    have h₁ : 1 < ω ^ denote (sum (c :: cs)) :=
      lt_of_lt_of_le omega_gt1
        (le_trans (pow_one' omega_gt0).ge (pow_le_pow_right ω he))
    exact calc 1 + (ω ^ denote (sum (c :: cs)) + denoteList xs)
        ≈ (1 + ω ^ denote (sum (c :: cs))) + denoteList xs := add_assoc _ _ _
      _ ≈ ω ^ denote (sum (c :: cs)) + denoteList xs :=
          add_congr (equiv_intro
            (additively_closed_collapse (powOmega_additively_closed (denote_complete _)) h₁)
            (le_add_left _ _)) (equiv_refl _)

/-! ## Addition -/

/-- Addition of normal sums: append, then drop the terms on the left that are
smaller than the leading term on the right.
Rocq: `Notation.CantorNotation.cantorSum_add`. -/
def addList : List CantorForm → List CantorForm → List CantorForm
  | [], ys => ys
  | x :: xs, ys => push x (addList xs ys)

/-- Rocq: `Notation.CantorNotation.cantorSum_add_normal`. -/
theorem addList_normal : ∀ xs ys : List CantorForm,
    IsNormal (sum xs) → IsNormal (sum ys) → IsNormal (sum (addList xs ys))
  | [], _, _, hy => hy
  | x :: xs, ys, hx, hy => push_normal x _ hx.head (addList_normal xs ys hx.tail hy)

/-- Rocq: `Notation.CantorNotation.cantorSum_add_correct`. -/
theorem addList_correct : ∀ xs ys : List CantorForm, IsNormal (sum xs) → IsNormal (sum ys) →
    denote (sum xs) + denote (sum ys) ≈ denote (sum (addList xs ys))
  | [], _, _, _ => zero_add _
  | x :: xs, ys, hx, hy =>
    calc (ω ^ denote x + denoteList xs) + denoteList ys
        ≈ ω ^ denote x + (denoteList xs + denoteList ys) := equiv_symm (add_assoc _ _ _)
      _ ≈ ω ^ denote x + denoteList (addList xs ys) :=
          add_congr (equiv_refl _) (addList_correct xs ys hx.tail hy)
      _ ≈ denoteList (push x (addList xs ys)) :=
          equiv_symm (push_correct x _ hx.head (addList_normal xs ys hx.tail hy))

/-- Rocq: `Notation.CantorNotation.CF_add`. -/
def add : CantorForm → CantorForm → CantorForm
  | sum xs, sum ys => sum (addList xs ys)

/-- Rocq: `Notation.CantorNotation.CF_add_normal`. -/
theorem add_normal : ∀ {x y : CantorForm}, IsNormal x → IsNormal y → IsNormal (add x y)
  | sum xs, sum ys => addList_normal xs ys

/-- Rocq: `Notation.CantorNotation.CF_add_correct`. -/
theorem add_correct : ∀ x y : CantorForm, IsNormal x → IsNormal y →
    denote x + denote y ≈ denote (add x y)
  | sum xs, sum ys => addList_correct xs ys

end CantorForm

namespace CantorNormalForm

open CantorForm

/-- Rocq: `Notation.CantorNotation.CNF_add`. -/
def add (x y : CantorNormalForm) : CantorNormalForm := ⟨x.1.add y.1, add_normal x.2 y.2⟩

/-- Rocq: `Notation.CantorNotation.CNF_add_reflects`. -/
theorem add_reflects : Reflects CantorNormalForm denote (fun _ => True) (.ord ==> .ord ==> .ord)
    (· + ·) add := by
  intro x a ⟨hxa, _⟩ y b ⟨hyb, _⟩
  exact ⟨equiv_trans (add_congr hxa hyb) (add_correct a.1 b.1 a.2 b.2), trivial⟩

end CantorNormalForm

/-! ## Multiplication -/

namespace CantorForm

/-- `x * ω ^ e`, which is `ω ^ (x₁ + e)` for `x₁` the leading exponent of `x`,
apart from special cases for empty sums.
Rocq: `Notation.CantorNotation.CF_mul_single`. -/
def mulSingle : CantorForm → CantorForm → CantorForm
  | sum [], _ => sum []
  | sum (x₁ :: xs), sum [] => sum (x₁ :: xs)
  | sum (x₁ :: _), sum (e :: es) => sum [add x₁ (sum (e :: es))]

/-- The Rocq `fold_right` in `CF_mul`: the sum of `x * ω ^ y` over `y ∈ ys`. -/
def mulList (x : CantorForm) : List CantorForm → CantorForm
  | [] => zero
  | y :: ys => add (mulSingle x y) (mulList x ys)

/-- Multiplication of normal forms: a sum of partial products, one for each
term on the right. Rocq: `Notation.CantorNotation.CF_mul`. -/
def mul (x : CantorForm) : CantorForm → CantorForm
  | sum ys => mulList x ys

/-- Rocq: `Notation.CantorNotation.CF_mul_single_normal`. -/
theorem mulSingle_normal : ∀ x e : CantorForm, IsNormal x → IsNormal e → IsNormal (mulSingle x e)
  | sum [], _, _, _ => trivial
  | sum (_ :: _), sum [], hx, _ => hx
  | sum (_ :: _), sum (_ :: _), hx, he => ⟨add_normal hx.head he, trivial⟩

theorem mulList_normal (x : CantorForm) :
    ∀ ys : List CantorForm, IsNormal x → IsNormal (sum ys) → IsNormal (mulList x ys)
  | [], _, _ => trivial
  | y :: ys, hx, hy => add_normal (mulSingle_normal x y hx hy.head) (mulList_normal x ys hx hy.tail)

/-- Rocq: `Notation.CantorNotation.CF_mul_normal`. -/
theorem mul_normal : ∀ {x y : CantorForm}, IsNormal x → IsNormal y → IsNormal (mul x y)
  | x, sum ys, hx, hy => mulList_normal x ys hx hy

private theorem firstTerm_dominates_aux (x : CantorForm) : ∀ (c : CantorForm) (xs : List CantorForm),
    IsNormalSeq c xs → denote c ≤ denote x → denoteList xs ≤ ω ^ denote x * ofNat xs.length
  | _, [], _, _ => zero_least _
  | _, b :: xs, h, hc =>
    have hb : denote b ≤ denote x := le_trans h.2.1 hc
    le_trans (add_le_add (pow_le_pow_right ω hb) (firstTerm_dominates_aux x b xs h.2.2 hb))
      (add_mul_ofNat_le _ _)

/-- In a normal sum, the first term dominates the rest: the rest is at most
`ω ^ x * n` for `n` its length.
Rocq: `Notation.CantorNotation.cantorFirstTerm_dominates`. -/
theorem firstTerm_dominates (x : CantorForm) (xs : List CantorForm)
    (h : IsNormal (sum (x :: xs))) : denote (sum xs) ≤ ω ^ denote x * ofNat xs.length :=
  firstTerm_dominates_aux x x xs h.2 (le_refl _)

/-- Rocq: `Notation.CantorNotation.CF_mul_single_correct`. -/
theorem mulSingle_correct : ∀ x e : CantorForm, IsNormal x → IsNormal e →
    denote (mulSingle x e) ≈ denote x * ω ^ denote e
  | sum [], _, _, _ => equiv_symm (zero_mul _)
  | sum (_ :: _), sum [], _, _ =>
    equiv_symm (equiv_trans (mul_congr (equiv_refl _) (pow_zero ω)) (mul_one _))
  | sum (c :: xs), sum (e :: es), hx, he => by
    have he₀ : 0 < denote (sum (e :: es)) := lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)
    refine equiv_trans (add_zero _) (equiv_trans
      (pow_congr (equiv_refl ω) (equiv_symm (add_correct c _ hx.head he))) ?_)
    refine equiv_trans (pow_add ω _ _) (equiv_intro ?_ ?_)
    · exact mul_le_mul_right _ (le_add_right _ _)
    · exact pow_omega_collapse _ _ ⟨xs.length⟩ (firstTerm_dominates c xs hx) _
        (denote_complete _) he₀

theorem mulList_correct (x : CantorForm) : ∀ ys : List CantorForm, IsNormal x → IsNormal (sum ys) →
    denote (mulList x ys) ≈ denote x * denoteList ys
  | [], _, _ => equiv_symm (mul_zero _)
  | y :: ys, hx, hy =>
    calc denote (add (mulSingle x y) (mulList x ys))
        ≈ denote (mulSingle x y) + denote (mulList x ys) :=
          equiv_symm (add_correct _ _ (mulSingle_normal x y hx hy.head)
            (mulList_normal x ys hx hy.tail))
      _ ≈ denote x * ω ^ denote y + denote x * denoteList ys :=
          add_congr (mulSingle_correct x y hx hy.head) (mulList_correct x ys hx hy.tail)
      _ ≈ denote x * (ω ^ denote y + denoteList ys) := equiv_symm (mul_add _ _ _)

/-- Rocq: `Notation.CantorNotation.CF_mul_correct`. -/
theorem mul_correct : ∀ x y : CantorForm, IsNormal x → IsNormal y →
    denote (mul x y) ≈ denote x * denote y
  | x, sum ys => mulList_correct x ys

end CantorForm

namespace CantorNormalForm

open CantorForm

/-- Rocq: `Notation.CantorNotation.CNF_mul`. -/
def mul (x y : CantorNormalForm) : CantorNormalForm := ⟨x.1.mul y.1, mul_normal x.2 y.2⟩

/-- Rocq: `Notation.CantorNotation.CNF_mul_reflects`. -/
theorem mul_reflects : Reflects CantorNormalForm denote (fun _ => True) (.ord ==> .ord ==> .ord)
    (· * ·) mul := by
  intro x a ⟨hxa, _⟩ y b ⟨hyb, _⟩
  exact ⟨equiv_trans (mul_congr hxa hyb) (equiv_symm (mul_correct a.1 b.1 a.2 b.2)), trivial⟩

end CantorNormalForm

/-! ## Exponentiation -/

namespace CantorForm

/-- The form `n`: `n` copies of `ω ^ 0`. Rocq: `Notation.CantorNotation.CF_nat`. -/
def nat (n : Nat) : CantorForm := sum (List.replicate n zero)

private theorem replicate_zero_normal : ∀ n : Nat, IsNormalSeq zero (List.replicate n zero)
  | 0 => trivial
  | n + 1 => ⟨trivial, le_refl _, replicate_zero_normal n⟩

/-- Rocq: `Notation.CantorNotation.CF_nat_normal`. -/
theorem nat_normal : ∀ n : Nat, IsNormal (nat n)
  | 0 => trivial
  | n + 1 => ⟨trivial, replicate_zero_normal n⟩

/-- Rocq: `Notation.CantorNotation.CF_nat_correct`. -/
theorem nat_correct : ∀ n : Nat, denote (nat n) ≈ ofNat n
  | 0 => equiv_refl _
  | n + 1 =>
    calc ω ^ (0 : Ordinal.{0}) + denote (nat n)
        ≈ 1 + ofNat n := add_congr (pow_zero ω) (nat_correct n)
      _ ≈ ofNat (n + 1) := equiv_symm (ofNat_add n 1)

/-- `x ^ (ω ^ e)`, by cases on the shape of `x` and on whether `e` is finite.
Rocq: `Notation.CantorNotation.CF_exp_single`. -/
def expSingle : CantorForm → CantorForm → CantorForm
  -- 0 ^ (ω ^ e) = 1
  | sum [], _ => one
  -- 1 ^ (ω ^ e) = 1
  | sum [sum []], _ => one
  -- finite `x = n > 1`
  | sum (sum [] :: c :: xs), e =>
    match isFinite e with
    -- n ^ (ω ^ 0) = n
    | some 0 => sum (sum [] :: c :: xs)
    -- n ^ (ω ^ (1 + m)) = ω ^ (ω ^ m) for finite m
    | some (m + 1) => sum [sum [nat m]]
    -- n ^ (ω ^ e) = ω ^ (ω ^ e) for e ≥ ω
    | none => sum [sum [e]]
  -- infinite `x = ω ^ x₁ + b`, with x₁ ≥ 1
  | sum (sum (l :: ls) :: xs), e =>
    match isFinite e with
    -- x ^ (ω ^ 0) = x
    | some 0 => sum (sum (l :: ls) :: xs)
    -- (ω ^ x₁ + b) ^ (ω ^ e) = ω ^ (x₁ * ω ^ e) for e > 0
    | some (_ + 1) => sum [mul (sum (l :: ls)) (sum [e])]
    | none => sum [mul (sum (l :: ls)) (sum [e])]

/-- The Rocq `fold_right` in `CF_exp`: the product of `x ^ (ω ^ y)` over
`y ∈ ys`. -/
def expList (x : CantorForm) : List CantorForm → CantorForm
  | [] => one
  | y :: ys => mul (expSingle x y) (expList x ys)

/-- Exponentiation of normal forms: `x ^ y` is the product of `x ^ (ω ^ y)`
over the terms `ω ^ y` of `y`. Rocq: `Notation.CantorNotation.CF_exp`. -/
def exp (x : CantorForm) : CantorForm → CantorForm
  | sum ys => expList x ys

/-- Rocq: `Notation.CantorNotation.CF_exp_single_normal`. -/
theorem expSingle_normal (e : CantorForm) : ∀ x : CantorForm, IsNormal x → IsNormal e →
    IsNormal (expSingle x e)
  | sum [], _, _ => one_normal
  | sum [sum []], _, _ => one_normal
  | sum (sum [] :: c :: xs), hx, he => by
    show IsNormal (match isFinite e with
      | some 0 => sum (sum [] :: c :: xs)
      | some (m + 1) => sum [sum [nat m]]
      | none => sum [sum [e]])
    cases isFinite e with
    | none => exact ⟨⟨he, trivial⟩, trivial⟩
    | some n => cases n with
      | zero => exact hx
      | succ m => exact ⟨⟨nat_normal m, trivial⟩, trivial⟩
  | sum (sum (l :: ls) :: xs), hx, he => by
    show IsNormal (match isFinite e with
      | some 0 => sum (sum (l :: ls) :: xs)
      | some (_ + 1) => sum [mul (sum (l :: ls)) (sum [e])]
      | none => sum [mul (sum (l :: ls)) (sum [e])])
    cases isFinite e with
    | none => exact ⟨mul_normal hx.head ⟨he, trivial⟩, trivial⟩
    | some n => cases n with
      | zero => exact hx
      | succ _ => exact ⟨mul_normal hx.head ⟨he, trivial⟩, trivial⟩

theorem expList_normal (x : CantorForm) :
    ∀ ys : List CantorForm, IsNormal x → IsNormal (sum ys) → IsNormal (expList x ys)
  | [], _, _ => one_normal
  | y :: ys, hx, hy => mul_normal (expSingle_normal y x hx hy.head) (expList_normal x ys hx hy.tail)

/-- Rocq: `Notation.CantorNotation.CF_exp_normal`. -/
theorem exp_normal : ∀ {x y : CantorForm}, IsNormal x → IsNormal y → IsNormal (exp x y)
  | x, sum ys, hx, hy => expList_normal x ys hx hy

/-- `denote one ≈ 1`. -/
theorem one_equiv : denote one ≈ 1 := equiv_trans (add_zero _) (pow_zero ω)

/-- `x ^ (ω ^ e) ≈ x` when `e ≈ 0` and `0 < x`. -/
private theorem pow_powOmega_zero {x e : Ordinal.{0}} (hx : 0 < x) (he : e ≈ 0) :
    x ≈ x ^ ω ^ e :=
  equiv_symm (equiv_trans (pow_congr (equiv_refl x)
    (equiv_trans (pow_congr (equiv_refl ω) he) (pow_zero ω))) (pow_one' hx))

/-- Rocq: `Notation.CantorNotation.CF_exp_single_correct`. -/
theorem expSingle_correct (x e : CantorForm) (hx : IsNormal x) (he : IsNormal e) :
    denote (expSingle x e) ≈ denote x ^ ω ^ denote e := by
  match x, hx with
  | sum [], _ =>
    refine equiv_trans one_equiv (equiv_intro (succ_least (pow_pos 0 _)) ?_)
    rw [pow_unfold]
    exact lub_least (le_refl 1) (sup_least fun _ => le_trans (mul_zero _).le (zero_least 1))
  | sum [sum []], _ =>
    exact equiv_trans one_equiv (equiv_symm (equiv_trans
      (pow_congr one_equiv (equiv_refl _)) (one_pow _)))
  | sum (sum [] :: c :: xs), hx =>
    have hN : 1 < ω (⟨(c :: xs).length + 1⟩ : ULift Nat) :=
      ofNat_increasing (Nat.succ_lt_succ (Nat.succ_pos _))
    have hxN : denote (sum (sum [] :: c :: xs)) ≈ ofNat ((c :: xs).length + 1) :=
      isFinite_fin _ _ hx rfl
    show denote (match isFinite e with
      | some 0 => sum (sum [] :: c :: xs)
      | some (m + 1) => sum [sum [nat m]]
      | none => sum [sum [e]]) ≈ _
    cases hfin : isFinite e with
    | none =>
      exact equiv_symm (equiv_trans (pow_congr hxN (equiv_refl _)) (equiv_trans
        (expNatToOmegaInf _ _ hN (equiv_symm (isFinite_inf e hfin)))
        (equiv_symm (equiv_trans (add_zero _) (pow_congr (equiv_refl ω) (add_zero _))))))
    | some n =>
      cases n with
      | zero =>
        exact pow_powOmega_zero (lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _))
          (isFinite_fin e 0 he hfin)
      | succ m =>
        have hm : denote e ≈ 1 + ofNat m := equiv_trans (isFinite_fin e _ he hfin) (ofNat_add m 1)
        exact equiv_symm (equiv_trans (pow_congr hxN (pow_congr (equiv_refl ω) hm)) (equiv_trans
          (expNatToOmegaPow _ _ hN)
          (equiv_symm (equiv_trans (add_zero _) (pow_congr (equiv_refl ω)
            (equiv_trans (add_zero _) (pow_congr (equiv_refl ω) (nat_correct m))))))))
  | sum (sum (l :: ls) :: xs), hx =>
    have main : 0 < denote e →
        denote (sum [mul (sum (l :: ls)) (sum [e])]) ≈ denote (sum (sum (l :: ls) :: xs)) ^ ω ^ denote e := by
      intro he₀
      refine equiv_trans (add_zero _) (equiv_trans (pow_congr (equiv_refl ω)
        (equiv_trans (mul_correct _ _ hx.head ⟨he, trivial⟩)
          (mul_congr (equiv_refl _) (add_zero _)))) ?_)
      refine equiv_trans (pow_mul ω _ _) (equiv_intro ?_ ?_)
      · exact pow_le_pow_left (le_add_right _ _) _
      · refine expToOmega_collapse_tower _ _ ⟨xs.length⟩ ?_ (firstTerm_dominates _ xs hx) _ he₀
        have h₁ : 1 ≤ denote (sum (l :: ls)) := le_trans (succ_least (pow_pos ω _)) (le_add_right _ _)
        calc ofNat xs.length + 1 ≈ ofNat (1 + xs.length) := equiv_symm (ofNat_add 1 xs.length)
          _ ≤ ω := le_of_lt (index_lt ω ⟨1 + xs.length⟩)
          _ ≤ ω ^ 1 := (pow_one' omega_gt0).ge
          _ ≤ ω ^ denote (sum (l :: ls)) := pow_le_pow_right ω h₁
    show denote (match isFinite e with
      | some 0 => sum (sum (l :: ls) :: xs)
      | some (_ + 1) => sum [mul (sum (l :: ls)) (sum [e])]
      | none => sum [mul (sum (l :: ls)) (sum [e])]) ≈ _
    cases hfin : isFinite e with
    | none =>
      exact main (lt_of_lt_of_le (lt_of_lt_of_le (succ_lt 0) (le_add_right 1 _))
        (isFinite_inf e hfin).le)
    | some n =>
      cases n with
      | zero =>
        exact pow_powOmega_zero (lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _))
          (isFinite_fin e 0 he hfin)
      | succ k =>
        exact main (lt_of_lt_of_le (lt_of_le_of_lt (zero_least _) (succ_lt (ofNat k)))
          (isFinite_fin e _ he hfin).ge)

theorem expList_correct (x : CantorForm) : ∀ ys : List CantorForm, IsNormal x → IsNormal (sum ys) →
    denote (expList x ys) ≈ denote x ^ denoteList ys
  | [], _, _ => equiv_trans one_equiv (equiv_symm (pow_zero _))
  | y :: ys, hx, hy =>
    calc denote (mul (expSingle x y) (expList x ys))
        ≈ denote (expSingle x y) * denote (expList x ys) :=
          mul_correct _ _ (expSingle_normal y x hx hy.head) (expList_normal x ys hx hy.tail)
      _ ≈ denote x ^ ω ^ denote y * denote x ^ denoteList ys :=
          mul_congr (expSingle_correct x y hx hy.head) (expList_correct x ys hx hy.tail)
      _ ≈ denote x ^ (ω ^ denote y + denoteList ys) := equiv_symm (pow_add _ _ _)

/-- Rocq: `Notation.CantorNotation.CF_exp_correct`. -/
theorem exp_correct : ∀ x y : CantorForm, IsNormal x → IsNormal y →
    denote (exp x y) ≈ denote x ^ denote y
  | x, sum ys => expList_correct x ys

end CantorForm

namespace CantorNormalForm

open CantorForm

/-- Rocq: `Notation.CantorNotation.CNF_exp`. -/
def exp (x y : CantorNormalForm) : CantorNormalForm := ⟨x.1.exp y.1, exp_normal x.2 y.2⟩

/-- Rocq: `Notation.CantorNotation.CNF_exp_reflects`. -/
theorem exp_reflects : Reflects CantorNormalForm denote (fun _ => True) (.ord ==> .ord ==> .ord)
    (· ^ ·) exp := by
  intro x a ⟨hxa, _⟩ y b ⟨hyb, _⟩
  exact ⟨equiv_trans (pow_congr hxa hyb) (equiv_symm (exp_correct a.1 b.1 a.2 b.2)), trivial⟩

/-- No operation on normal forms computes `x ↑↑ y`: otherwise `ω ↑↑ ω = ε 0`
would have a normal form. Rocq: `Notation.CantorNotation.CNF_reflects_KnuthUp2_impossible`. -/
theorem reflects_knuthUp2_impossible :
    ¬ ∃ f, Reflects CantorNormalForm denote (fun _ => True) (.ord ==> .ord ==> .ord)
      (knuthUp 2) f := fun ⟨f, hf⟩ =>
  let h := (hf ω omega reflects_omega ω omega reflects_omega).1
  lt_irrefl (ε 0) (lt_of_le_of_lt (le_trans knuthUp_epsilon.ge h.le)
    (below_epsilon (f omega omega).1))

end CantorNormalForm

/-! ## Order type -/

namespace CantorForm

private theorem discriminateList : ∀ xs : List CantorForm, IsNormal (sum xs) →
    IsZero (denoteList xs) ∨ IsSucc (denoteList xs) ∨ IsLimit (denoteList xs)
  | [], _ => .inl fun ⟨e⟩ => nomatch e
  | [c], h =>
    match CantorNormalForm.decideOrder CantorNormalForm.zero ⟨c, h.head⟩ with
    | .inl hc =>
      -- `0 < c`, so `ω ^ c` is a limit
      have h₁ : 1 < ω ^ denote c :=
        lt_of_lt_of_le omega_gt1 (le_trans (pow_one' omega_gt0).ge
          (pow_le_pow_right ω (succ_least hc)))
      .inr (.inr ((isLimit_iff _).2 ⟨lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _),
        fun i hi => ⟨i + 1,
          lt_of_le_of_lt (le_add_right i 0) (lt_of_lt_of_le (succ_lt _) (add_succ i 0).ge),
          lt_of_lt_of_le (powOmega_additively_closed (denote_complete c) i 1
            (lt_of_lt_of_le hi (add_zero _).le) h₁) (le_add_right _ _)⟩⟩))
    | .inr hc =>
      -- `c ≈ 0`, so `ω ^ c + 0 ≈ 1`
      .inr (.inl ((isSucc_iff _).2 ⟨0, equiv_trans (add_zero _) (equiv_trans
        (pow_congr (equiv_refl ω) (equiv_intro hc (zero_least _))) (pow_zero ω))⟩))
  | _ :: b :: l, h =>
    match discriminateList (b :: l) h.tail with
    | .inl hz =>
      absurd (lt_of_lt_of_le (lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _))
        ((isZero_iff _).1 hz).le) (lt_irrefl 0)
    | .inr (.inl hs) => .inr (.inl (successor_add _ hs))
    | .inr (.inr hl) => .inr (.inr (limit_add _ hl))

/-- Every normal form denotes zero, a successor or a limit.
Rocq: `Notation.CantorNotation.CF_discriminate`. -/
theorem discriminate : ∀ c : CantorForm, IsNormal c →
    IsZero (denote c) ∨ IsSucc (denote c) ∨ IsLimit (denote c)
  | sum xs, h => discriminateList xs h

end CantorForm

namespace CantorNormalForm

open CantorForm

/-- Rocq: `Notation.CantorNotation.CNF_discriminate`. -/
theorem discriminate (c : CantorNormalForm) :
    IsZero (sz c) ∨ IsSucc (sz c) ∨ IsLimit (sz c) :=
  CantorForm.discriminate c.1 c.2

end CantorNormalForm

open CantorNormalForm in
/-- Rocq: `Notation.CantorNotation.CNF_limit`. -/
theorem CNF_limit : IsLimit CNF :=
  ⟨⟨zero⟩, fun a => ⟨add a one,
    calc a.denote < a.denote + 1 :=
          lt_of_le_of_lt (le_add_right _ 0) (lt_of_lt_of_le (succ_lt _) (add_succ _ 0).ge)
      _ ≤ a.denote + one.denote := add_le_add (le_refl _) CantorForm.one_equiv.ge
      _ ≈ (add a one).denote := CantorForm.add_correct _ _ a.2 CantorForm.one_normal⟩⟩

open CantorNormalForm in
/-- `CNF` is closed under `ω ^ ·`. Rocq: `Notation.CantorNotation.CNF_expOmega_fixpoint`. -/
theorem CNF_expOmega_fixpoint : ω ^ CNF ≤ CNF :=
  calc ω ^ CNF ≤ ω ^ sup CantorNormalForm.denote := pow_le_pow_right ω (limit_boundedSup CNF_limit).le
    _ ≤ sup fun x => ω ^ x.denote := pow_continuous ω CantorNormalForm CantorNormalForm.denote zero
    _ ≤ CNF := sup_least fun x =>
        le_trans (exp_reflects ω omega reflects_omega x.denote x ⟨equiv_refl _, trivial⟩).1.le
          (index_le CNF (exp omega x))

/-- The Cantor normal forms have order type `ε 0`. Rocq: `Notation.CantorNotation.CNF_is_ε0`. -/
theorem CNF_is_ε0 : CNF ≈ ε 0 :=
  equiv_intro (le_intro fun x => CantorForm.below_epsilon x.1)
    (ε0_least_expOmega_closed CNF CNF_expOmega_fixpoint)

/-! ## Enough notations and the excluded middle -/

namespace CantorNormalForm

open CantorForm

/-- With the excluded middle, every ordinal below `ε 0` has a Cantor normal
form. Rocq: `Notation.CantorNotation.CNF_has_enough_notations`. -/
theorem has_enough_notations (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < ε 0 → ∃ c : CantorNormalForm, x ≈ sz c := by
  intro x
  refine ltRec (motive := fun x => x < ε 0 → ∃ c : CantorNormalForm, x ≈ sz c) (fun x ih hx => ?_) x
  obtain ⟨ls, hseq, hls⟩ := cantor_decomposition em x
  suffices h : ∀ l, CantorSequence x l → cantorDenote l ≤ x →
      ∃ c : CantorNormalForm, cantorDenote l ≈ sz c by
    obtain ⟨c, hc⟩ := h ls hseq hls.le
    exact ⟨c, equiv_trans (equiv_symm hls) hc⟩
  intro l
  induction l with
  | nil => exact fun _ _ => ⟨zero, equiv_refl _⟩
  | cons a l ihl =>
    intro hseq hle
    have hax : a < x := by
      cases order_total em x a with
      | inr h => exact h
      | inl h =>
        refine absurd (lt_of_le_of_lt (ε0_least_expOmega_closed x ?_) hx) (lt_irrefl _)
        exact le_trans (pow_le_pow_right ω h) (le_trans (le_add_right _ _) hle)
    obtain ⟨ac, hac⟩ := ih a hax (lt_trans hax hx)
    obtain ⟨cls, hcls⟩ := ihl (hseq.2.mono hseq.1) (le_trans (le_add_left _ _) hle)
    exact ⟨add (exp omega ac) cls, (add_reflects (ω ^ a) (exp omega ac)
      (exp_reflects ω omega reflects_omega a ac ⟨hac, trivial⟩) _ cls ⟨hcls, trivial⟩).1⟩

/-- `1 < ε 0`. -/
private theorem one_lt_epsilon : (1 : Ordinal.{0}) < ε 0 :=
  lt_of_le_of_lt (pow_zero ω).ge (lt_of_lt_of_le
    (pow_lt_pow_right omega_gt1 (lt_of_lt_of_le (pow_pos ω _) (ε_fixpoint 0).ge)) (ε_fixpoint 0).ge)

/-- Conversely, enough normal forms give the excluded middle, since their
order is decidable. Rocq: `Notation.CantorNotation.CNF_has_enough_notations_is_classical`. -/
theorem has_enough_notations_is_classical
    (h : ∀ x : Ordinal.{0}, x < ε 0 → ∃ c : CantorNormalForm, x ≈ sz c) : ExcludedMiddle :=
  zero_dec_EM fun x hx =>
    let ⟨c, hc⟩ := h x (lt_of_le_of_lt hx one_lt_epsilon)
    match decideOrder zero c with
    | .inl h₀ => .inr (lt_of_lt_of_le h₀ hc.ge)
    | .inr h₀ => .inl (le_trans hc.le h₀)

/-- Even for complete ordinals, enough normal forms give the excluded middle.
Rocq: `Notation.CantorNotation.CNF_has_enough_notations_is_classical_for_complete_ordinals`. -/
theorem has_enough_notations_is_classical_for_complete_ordinals
    (h : ∀ x : Ordinal.{0}, Complete x → x < ε 0 → ∃ c : CantorNormalForm, x ≈ sz c) :
    ExcludedMiddle :=
  succ_limit_dec_EM fun x hx₀ hxω hxc =>
    have hω : ω < ε 0 :=
      lt_of_le_of_lt (pow_one' omega_gt0).ge (lt_of_lt_of_le
        (pow_lt_pow_right omega_gt1 one_lt_epsilon) (ε_fixpoint 0).ge)
    let ⟨c, hc⟩ := h x hxc (lt_of_le_of_lt hxω hω)
    match discriminate c with
    | .inl hz => absurd (lt_of_lt_of_le hx₀ (le_trans hc.le ((isZero_iff _).1 hz).le)) (lt_irrefl 0)
    | .inr (.inl hs) => .inl (hs.congr (equiv_symm hc))
    | .inr (.inr hl) => .inr (hl.congr (equiv_symm hc))

end CantorNormalForm

/-! ## Sample computations

These are checked by kernel reduction (`rfl`). -/

namespace CantorForm

/-- `1 + ω = ω`. -/
theorem sample_one_add_omega : add one omega = omega := rfl

/-- `ω < ω + 1`. -/
theorem sample_omega_lt : compare omega (add omega one) = .lt := rfl

/-- `2 ^ ω = ω`. -/
theorem sample_two_pow_omega : compare (exp (nat 2) omega) omega = .eq := rfl

/-- `ω * 2 = ω + ω`, and `2 * ω = ω`. -/
theorem sample_mul : compare (mul omega (nat 2)) (add omega omega) = .eq ∧
    compare (mul (nat 2) omega) omega = .eq := ⟨rfl, rfl⟩

end CantorForm

end ConstructiveOrdinals.CantorNotation
