import ConstructiveOrdinals.Cantor
import ConstructiveOrdinals.Reflection
import ConstructiveOrdinals.NaturalArith
import ConstructiveOrdinals.Veblen.Constructive
import ConstructiveOrdinals.Classical
import ConstructiveOrdinals.Prelude.List

/-!
# Cantor arithmetic for notation systems with Cantor decompositions

Port of `Ordinal/Notation/CantorDecomposition.v`.

A notation system `A` (with denotation `f` and well-formedness predicate `P`)
*has a Cantor decomposition* when it can compare its terms and convert each
term to and from the list of exponents of its Cantor normal form. Every such
system supports zero, successor, addition, multiplication and
exponentiation, computed on Cantor normal forms.

The second half of the file studies *interpolants*: a term has all
interpolants when every ordinal below it is bounded by a smaller term, and so
on recursively. With the excluded middle, this is equivalent to the system
having a notation for every ordinal below each of its terms. With all
interpolants, a system with a Cantor decomposition also supports the natural
(Hessenberg) sum.

Lean notes:

- Rocq's `Section cantor_arithmetic` variables `A f P X` become explicit
  arguments; `f` and `P` are implicit when `X` determines them, as with Rocq's
  `Implicit Arguments`. Each declaration takes exactly the section variables
  that Rocq's `Check` reports.
- The inner `match` of Rocq's `cantor_ordered` is the predicate `HeadLe`.
-/

namespace ConstructiveOrdinals.CantorDecomposition

open Ordinal

variable {A : Type}

/-- `ω ^ f x₁ + ω ^ f x₂ + ⋯`. Rocq: `Notation.CantorDecomposition.cantor_denote`. -/
def cantorDenote (f : A → Ordinal.{0}) : List A → Ordinal.{0}
  | [] => 0
  | x :: xs => ω ^ f x + cantorDenote f xs

/-- The head of the list, if any, is at most `b`. The inner `match` of Rocq's
`cantor_ordered`. -/
def HeadLe (f : A → Ordinal.{0}) (b : Ordinal.{0}) : List A → Prop
  | [] => True
  | x :: _ => f x ≤ b

/-- The list is non-increasing. Rocq: `Notation.CantorDecomposition.cantor_ordered`. -/
def CantorOrdered (f : A → Ordinal.{0}) : List A → Prop
  | [] => True
  | x₁ :: xs₁ => HeadLe f (f x₁) xs₁ ∧ CantorOrdered f xs₁

theorem HeadLe.mono {f : A → Ordinal.{0}} {b b' : Ordinal.{0}} (h : b ≤ b') :
    ∀ {xs : List A}, HeadLe f b xs → HeadLe f b' xs
  | [], _ => trivial
  | _ :: _, hx => le_trans hx h

/-- A notation system with a Cantor decomposition.
Rocq: `Notation.CantorDecomposition.has_cantor_decomposition`. -/
structure HasCantorDecomposition (f : A → Ordinal.{0}) (P : A → Prop) : Type where
  /-- Comparison of terms. Rocq field `cantor_decomp_compare`. -/
  compare : A → A → Ordering
  /-- The exponents of the Cantor normal form. Rocq field `cantor_decompose`. -/
  decompose : A → List A
  /-- The term with the given Cantor normal form. Rocq field `cantor_recompose`. -/
  recompose : List A → A
  /-- Rocq field `cantor_decomp_complete`. -/
  complete : ∀ x, Complete (f x)
  /-- Rocq field `cantor_decomp_compare_correct`. -/
  compare_correct : ∀ x y, P x → P y → OrderingCorrect (compare x y) (f x) (f y)
  /-- Rocq field `cantor_decompose_correct`. -/
  decompose_correct : ∀ x, P x →
    Each P (decompose x) ∧ CantorOrdered f (decompose x) ∧ f x ≈ cantorDenote f (decompose x)
  /-- Rocq field `cantor_recompose_correct`. -/
  recompose_correct : ∀ xs, Each P xs → CantorOrdered f xs →
    P (recompose xs) ∧ cantorDenote f xs ≈ f (recompose xs)

/-- Rocq: `Notation.CantorDecomposition.each_app`. -/
theorem each_app (P : A → Prop) : ∀ xs ys : List A, Each P (xs ++ ys) ↔ Each P xs ∧ Each P ys
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: xs, ys =>
    ⟨fun h => ⟨⟨h.1, ((each_app P xs ys).1 h.2).1⟩, ((each_app P xs ys).1 h.2).2⟩,
      fun h => ⟨h.1.1, (each_app P xs ys).2 ⟨h.1.2, h.2⟩⟩⟩

section cantor_arithmetic

variable {f : A → Ordinal.{0}} {P : A → Prop} (X : HasCantorDecomposition f P)

/-! ## Zero, successor and finite numbers -/

include X in
/-- Rocq: `Notation.CantorDecomposition.cantor_denote_complete`. -/
theorem cantor_denote_complete : ∀ xs : List A, Complete (cantorDenote f xs)
  | [] => zero_complete
  | x :: xs =>
    add_complete (pow_complete omega_gt0 omega_complete (X.complete x)) (cantor_denote_complete xs)

/-- Rocq: `Notation.CantorDecomposition.cantor_zero`. -/
def cantorZero : A := X.recompose []

theorem cantorZero_spec : P (cantorZero X) ∧ f (cantorZero X) ≈ 0 :=
  let h := X.recompose_correct [] trivial trivial
  ⟨h.1, equiv_symm h.2⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_zero_reflects`. -/
theorem cantor_zero_reflects : Reflects A f P .ord 0 (cantorZero X) :=
  ⟨equiv_symm (cantorZero_spec X).2, (cantorZero_spec X).1⟩

/-- `ω ^ z + 0 ≈ 1` when `z ≈ 0`. -/
theorem powOmega_add_zero_of_zero {z : Ordinal.{0}} (h : z ≈ 0) : ω ^ z + 0 ≈ 1 :=
  equiv_trans (add_zero _) (equiv_trans (pow_congr (equiv_refl ω) h) (pow_zero ω))

/-- Rocq: `Notation.CantorDecomposition.cantor_succ_list`. -/
def cantorSuccList (xs : List A) : List A := xs ++ [X.recompose []]

/-- Rocq: `Notation.CantorDecomposition.cantor_succ`. -/
def cantorSucc (x : A) : A := X.recompose (cantorSuccList X (X.decompose x))

private theorem ordered_append_zero {z : A} (hz : f z ≈ 0) :
    ∀ xs : List A, CantorOrdered f xs → CantorOrdered f (xs ++ [z])
  | [], _ => ⟨trivial, trivial⟩
  | [_], _ => ⟨le_trans hz.le (zero_least _), trivial, trivial⟩
  | _ :: y :: xs, h => ⟨h.1, ordered_append_zero hz (y :: xs) h.2⟩

private theorem denote_append_zero {z : A} (hz : f z ≈ 0) :
    ∀ xs : List A, cantorDenote f (xs ++ [z]) ≈ succ (cantorDenote f xs)
  | [] => powOmega_add_zero_of_zero hz
  | _ :: xs =>
    equiv_trans (add_congr (equiv_refl _) (denote_append_zero hz xs)) (add_succ _ _)

/-- Rocq: `Notation.CantorDecomposition.cantor_succ_reflects`. -/
theorem cantor_succ_reflects : Reflects A f P (.ord ==> .ord) succ (cantorSucc X) := by
  intro x a ⟨hxa, ha⟩
  obtain ⟨hP, hord, hden⟩ := X.decompose_correct a ha
  obtain ⟨hz₁, hz₂⟩ := cantorZero_spec X
  obtain ⟨h₁, h₂⟩ := X.recompose_correct (cantorSuccList X (X.decompose a))
    ((each_app P _ _).2 ⟨hP, hz₁, trivial⟩) (ordered_append_zero hz₂ _ hord)
  exact ⟨equiv_trans (succ_congruence (equiv_trans hxa hden))
    (equiv_trans (equiv_symm (denote_append_zero hz₂ _)) h₂), h₁⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_nat`. -/
def cantorNat (n : Nat) : A := X.recompose (List.replicate n (cantorZero X))

private theorem replicate_ordered (a : A) : ∀ n : Nat, CantorOrdered f (List.replicate n a)
  | 0 => trivial
  | 1 => ⟨trivial, trivial⟩
  | n + 2 => ⟨le_refl _, replicate_ordered a (n + 1)⟩

private theorem replicate_each {a : A} (ha : P a) : ∀ n : Nat, Each P (List.replicate n a)
  | 0 => trivial
  | n + 1 => ⟨ha, replicate_each ha n⟩

private theorem denote_replicate_zero {z : A} (hz : f z ≈ 0) :
    ∀ n : Nat, cantorDenote f (List.replicate n z) ≈ ofNat n
  | 0 => equiv_refl _
  | n + 1 =>
    equiv_trans (add_congr (equiv_trans (pow_congr (equiv_refl ω) hz) (pow_zero ω))
      (denote_replicate_zero hz n)) (onePlus_finite_succ n)

/-- Rocq: `Notation.CantorDecomposition.cantor_nat_correct`. -/
theorem cantor_nat_correct (n : Nat) : f (cantorNat X n) ≈ ofNat n ∧ P (cantorNat X n) :=
  let h := X.recompose_correct (List.replicate n (cantorZero X))
    (replicate_each (cantorZero_spec X).1 n) (replicate_ordered _ n)
  ⟨equiv_trans (equiv_symm h.2) (denote_replicate_zero (cantorZero_spec X).2 n), h.1⟩

/-! ## Addition -/

/-- Rocq: `Notation.CantorDecomposition.cantor_add_loop`. -/
def cantorAddLoop : List A → A → List A → List A
  | [], y, ys => y :: ys
  | x :: xs', y, ys =>
    match X.compare x y with
    | .lt => y :: ys
    | .eq => x :: cantorAddLoop xs' y ys
    | .gt => x :: cantorAddLoop xs' y ys

/-- Rocq: `Notation.CantorDecomposition.cantor_add_list`. -/
def cantorAddList (xs : List A) : List A → List A
  | [] => xs
  | y :: ys' => cantorAddLoop X xs y ys'

/-- Rocq: `Notation.CantorDecomposition.cantor_add`. -/
def cantorAdd (x y : A) : A :=
  X.recompose (cantorAddList X (X.decompose x) (X.decompose y))

private theorem addLoop_prop {y : A} {ys : List A} (hy : Each P (y :: ys)) :
    ∀ xs : List A, Each P xs → Each P (cantorAddLoop X xs y ys)
  | [], _ => hy
  | x :: xs, hx => by
    show Each P (match X.compare x y with
      | .lt => y :: ys
      | .eq => x :: cantorAddLoop X xs y ys
      | .gt => x :: cantorAddLoop X xs y ys)
    cases X.compare x y with
    | lt => exact hy
    | eq => exact ⟨hx.1, addLoop_prop hy xs hx.2⟩
    | gt => exact ⟨hx.1, addLoop_prop hy xs hx.2⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_add_prop`. -/
theorem cantor_add_prop : ∀ xs ys : List A, Each P xs → Each P ys → Each P (cantorAddList X xs ys)
  | _, [], hx, _ => hx
  | xs, _ :: _, hx, hy => addLoop_prop X hy xs hx

/-- Ordering facts for `cantorAddLoop`: the result is ordered, and its head is
bounded by any common bound of `y` and the head of `xs`. -/
private theorem addLoop_ordered {y : A} {ys : List A} (hPy : P y)
    (hy : CantorOrdered f (y :: ys)) : ∀ xs : List A, Each P xs → CantorOrdered f xs →
      CantorOrdered f (cantorAddLoop X xs y ys) ∧
        ∀ b, f y ≤ b → HeadLe f b xs → HeadLe f b (cantorAddLoop X xs y ys)
  | [], _, _ => ⟨hy, fun _ hb _ => hb⟩
  | x :: xs, hP, hx => by
    have hc := X.compare_correct x y hP.1 hPy
    show CantorOrdered f (match X.compare x y with
        | .lt => y :: ys
        | .eq => x :: cantorAddLoop X xs y ys
        | .gt => x :: cantorAddLoop X xs y ys) ∧
      ∀ b, f y ≤ b → HeadLe f b (x :: xs) → HeadLe f b (match X.compare x y with
        | .lt => y :: ys
        | .eq => x :: cantorAddLoop X xs y ys
        | .gt => x :: cantorAddLoop X xs y ys)
    have ih := addLoop_ordered hPy hy xs hP.2 hx.2
    revert hc
    cases X.compare x y with
    | lt => exact fun _ => ⟨hy, fun _ hb _ => hb⟩
    | eq => exact fun hc => ⟨⟨ih.2 _ hc.ge hx.1, ih.1⟩, fun _ _ h => h⟩
    | gt => exact fun hc => ⟨⟨ih.2 _ (le_of_lt hc) hx.1, ih.1⟩, fun _ _ h => h⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_add_ordered`. -/
theorem cantor_add_ordered : ∀ xs ys : List A, CantorOrdered f xs → CantorOrdered f ys →
    Each P xs → Each P ys → CantorOrdered f (cantorAddList X xs ys)
  | _, [], hx, _, _, _ => hx
  | xs, _ :: _, hx, hy, hPx, hPy => (addLoop_ordered X hPy.1 hy xs hPx hx).1

include X in
/-- An ordered list whose terms are all below `f y` is absorbed by a sum
starting with `ω ^ f y`. -/
private theorem absorb {y : A} (Y : Ordinal.{0}) :
    ∀ (xs : List A) (b : Ordinal.{0}), b < f y → HeadLe f b xs → CantorOrdered f xs →
      cantorDenote f xs + (ω ^ f y + Y) ≤ ω ^ f y + Y
  | [], _, _, _, _ => (zero_add _).le
  | x :: xs, _, hb, hx, hord =>
    calc (ω ^ f x + cantorDenote f xs) + (ω ^ f y + Y)
        ≈ ω ^ f x + (cantorDenote f xs + (ω ^ f y + Y)) := equiv_symm (add_assoc _ _ _)
      _ ≤ ω ^ f x + (ω ^ f y + Y) :=
          add_le_add (le_refl _) (absorb Y xs (f x) (lt_of_le_of_lt hx hb) hord.1 hord.2)
      _ ≈ (ω ^ f x + ω ^ f y) + Y := add_assoc _ _ _
      _ ≤ ω ^ f y + Y :=
          add_le_add (pow_add_collapse (X.complete y) (lt_of_le_of_lt hx hb)) (le_refl _)

private theorem addLoop_correct {y : A} {ys : List A} (hPy : P y) :
    ∀ xs : List A, CantorOrdered f xs → Each P xs →
      cantorDenote f (cantorAddLoop X xs y ys) ≈ cantorDenote f xs + cantorDenote f (y :: ys)
  | [], _, _ => equiv_symm (zero_add _)
  | x :: xs, hx, hP => by
    have hc := X.compare_correct x y hP.1 hPy
    show cantorDenote f (match X.compare x y with
      | .lt => y :: ys
      | .eq => x :: cantorAddLoop X xs y ys
      | .gt => x :: cantorAddLoop X xs y ys) ≈ _
    have ih := addLoop_correct (ys := ys) hPy xs hx.2 hP.2
    revert hc
    cases X.compare x y with
    | lt =>
      exact fun hc => equiv_intro (le_add_left _ _)
        (absorb X _ (x :: xs) (f x) hc (le_refl _) hx)
    | eq => exact fun _ => equiv_trans (add_congr (equiv_refl _) ih) (add_assoc _ _ _)
    | gt => exact fun _ => equiv_trans (add_congr (equiv_refl _) ih) (add_assoc _ _ _)

/-- Rocq: `Notation.CantorDecomposition.cantor_add_list_correct`. -/
theorem cantor_add_list_correct : ∀ xs ys : List A, CantorOrdered f xs → CantorOrdered f ys →
    Each P xs → Each P ys →
    cantorDenote f (cantorAddList X xs ys) ≈ cantorDenote f xs + cantorDenote f ys
  | _, [], _, _, _, _ => equiv_symm (add_zero _)
  | xs, _ :: _, hx, _, hPx, hPy => addLoop_correct X hPy.1 xs hx hPx

/-- A binary operation on Cantor normal forms that preserves well-formedness
and computes `op` reflects `op`. -/
private theorem reflects_of_list {op : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}
    (opL : List A → List A → List A)
    (hcong : ∀ {a a' b b' : Ordinal.{0}}, a ≈ a' → b ≈ b' → op a b ≈ op a' b')
    (hprop : ∀ xs ys, Each P xs → Each P ys → CantorOrdered f xs → CantorOrdered f ys →
      Each P (opL xs ys) ∧ CantorOrdered f (opL xs ys))
    (hcorrect : ∀ xs ys, Each P xs → Each P ys → CantorOrdered f xs → CantorOrdered f ys →
      cantorDenote f (opL xs ys) ≈ op (cantorDenote f xs) (cantorDenote f ys)) :
    Reflects A f P (.ord ==> .ord ==> .ord) op
      (fun x y => X.recompose (opL (X.decompose x) (X.decompose y))) := by
  intro x a ⟨hxa, ha⟩ y b ⟨hyb, hb⟩
  obtain ⟨ha₁, ha₂, ha₃⟩ := X.decompose_correct a ha
  obtain ⟨hb₁, hb₂, hb₃⟩ := X.decompose_correct b hb
  obtain ⟨hp₁, hp₂⟩ := hprop _ _ ha₁ hb₁ ha₂ hb₂
  obtain ⟨h₁, h₂⟩ := X.recompose_correct _ hp₁ hp₂
  exact ⟨equiv_trans (hcong (equiv_trans hxa ha₃) (equiv_trans hyb hb₃))
    (equiv_trans (equiv_symm (hcorrect _ _ ha₁ hb₁ ha₂ hb₂)) h₂), h₁⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_add_reflects`. -/
theorem cantor_add_reflects : Reflects A f P (.ord ==> .ord ==> .ord) (· + ·) (cantorAdd X) :=
  reflects_of_list X (cantorAddList X) add_congr
    (fun xs ys hPx hPy hx hy => ⟨cantor_add_prop X xs ys hPx hPy,
      cantor_add_ordered X xs ys hx hy hPx hPy⟩)
    (fun xs ys hPx hPy hx hy => cantor_add_list_correct X xs ys hx hy hPx hPy)

/-! ## Successor test and classification -/

/-- If the list ends in a zero term, the list without it.
Rocq: `Notation.CantorDecomposition.cantor_list_pred`. -/
def cantorListPred : List A → Option (List A)
  | [] => none
  | [x] =>
    match X.decompose x with
    | [] => some []
    | _ :: _ => none
  | x :: x' :: xs' =>
    match cantorListPred (x' :: xs') with
    | none => none
    | some zs => some (x :: zs)

private theorem denote_pos {x : A} {xs : List A} : 0 < cantorDenote f (x :: xs) :=
  lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)

/-- `1 < ω ^ a` when `0 < a`. -/
private theorem one_lt_powOmega {a : Ordinal.{0}} (h : 0 < a) : 1 < ω ^ a :=
  lt_of_lt_of_le omega_gt1 (le_trans (pow_one' omega_gt0).ge (pow_le_pow_right ω (succ_least h)))

/-- Rocq: `Notation.CantorDecomposition.cantor_list_pred_correct`. -/
theorem cantor_list_pred_correct : ∀ xs : List A, Each P xs → CantorOrdered f xs →
    match cantorListPred X xs with
    | none => SuccUnreachable (cantorDenote f xs)
    | some xs' => cantorDenote f xs ≈ succ (cantorDenote f xs') ∧ Each P xs' ∧
        match xs with
        | [] => False
        | x :: _ => CantorOrdered f (x :: xs')
  | [], _, _ => zero_succ_unreachable
  | [x], hP, _ => by
    obtain ⟨_, _, hden⟩ := X.decompose_correct x hP.1
    show match (match X.decompose x with
        | [] => some []
        | _ :: _ => none) with
      | none => SuccUnreachable (cantorDenote f [x])
      | some xs' => cantorDenote f [x] ≈ succ (cantorDenote f xs') ∧ Each P xs' ∧
          CantorOrdered f (x :: xs')
    revert hden
    cases X.decompose x with
    | nil => exact fun hden => ⟨powOmega_add_zero_of_zero hden, trivial, trivial, trivial⟩
    | cons d ds =>
      exact fun hden => limit_unreachable ((additively_closed_limit
        (one_lt_powOmega (lt_of_lt_of_le denote_pos hden.ge))
        (powOmega_additively_closed (X.complete x))).congr (equiv_symm (add_zero _)))
  | x :: x' :: xs', hP, hord => by
    have ih := cantor_list_pred_correct (x' :: xs') hP.2 hord.2
    show match (match cantorListPred X (x' :: xs') with
        | none => none
        | some zs => some (x :: zs)) with
      | none => SuccUnreachable (cantorDenote f (x :: x' :: xs'))
      | some xs'' => cantorDenote f (x :: x' :: xs') ≈ succ (cantorDenote f xs'') ∧
          Each P xs'' ∧ CantorOrdered f (x :: xs'')
    revert ih
    cases cantorListPred X (x' :: xs') with
    | none =>
      exact fun ih => limit_unreachable (limit_add _ (unreachable_limit denote_pos ih))
    | some zs =>
      intro ih
      exact ⟨equiv_trans (add_congr (equiv_refl _) ih.1) (add_succ _ _), ⟨hP.1, ih.2.1⟩,
        le_refl _, ih.2.2.1.mono hord.1, ih.2.2.2⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_succ_test`. -/
def cantorSuccTest (x : A) : Option A :=
  match cantorListPred X (X.decompose x) with
  | none => none
  | some xs' => some (X.recompose xs')

/-- The `some` case of `cantor_list_pred_correct` gives an ordered list. -/
private theorem pred_ordered {xs xs' : List A}
    (h : match xs with
      | [] => False
      | x :: _ => CantorOrdered f (x :: xs')) : CantorOrdered f xs' :=
  match xs, h with
  | _ :: _, h => h.2

/-- Rocq: `Notation.CantorDecomposition.cantor_succ_test_correct`. -/
theorem cantor_succ_test_correct (x : A) (hx : P x) :
    match cantorSuccTest X x with
    | none => SuccUnreachable (f x)
    | some x' => P x' ∧ succ (f x') ≈ f x := by
  obtain ⟨hP, hord, hden⟩ := X.decompose_correct x hx
  have h := cantor_list_pred_correct X _ hP hord
  show match (match cantorListPred X (X.decompose x) with
      | none => none
      | some xs' => some (X.recompose xs')) with
    | none => SuccUnreachable (f x)
    | some x' => P x' ∧ succ (f x') ≈ f x
  revert h
  cases cantorListPred X (X.decompose x) with
  | none => exact fun h => h.congr (equiv_symm hden)
  | some l =>
    intro h
    obtain ⟨hl₁, hl₂⟩ := X.recompose_correct l h.2.1 (pred_ordered h.2.2)
    exact ⟨hl₁, equiv_trans (succ_congruence (equiv_symm hl₂))
      (equiv_trans (equiv_symm h.1) (equiv_symm hden))⟩

/-- Decide whether a term denotes a successor, zero or a limit.
Rocq: `Notation.CantorDecomposition.cantor_decide`. -/
def cantorDecide (x : A) (hx : P x) :
    PSum (PSum { x' : A // P x' ∧ f x ≈ succ (f x') } (f x ≈ 0)) (IsLimit (f x)) :=
  aux (X.decompose x) (X.decompose_correct x hx).1 (X.decompose_correct x hx).2.1
    (X.decompose_correct x hx).2.2
where
  aux (ds : List A) (hP : Each P ds) (hord : CantorOrdered f ds) (hden : f x ≈ cantorDenote f ds) :
      PSum (PSum { x' : A // P x' ∧ f x ≈ succ (f x') } (f x ≈ 0)) (IsLimit (f x)) := by
    have h := cantor_list_pred_correct X ds hP hord
    revert h
    cases cantorListPred X ds with
    | some l =>
      intro h
      have hl := X.recompose_correct l h.2.1 (pred_ordered h.2.2)
      exact .inl (.inl ⟨X.recompose l, hl.1,
        equiv_trans hden (equiv_trans h.1 (succ_congruence hl.2))⟩)
    | none =>
      intro h
      cases ds with
      | nil => exact .inl (.inr hden)
      | cons _ _ => exact .inr ((unreachable_limit denote_pos h).congr (equiv_symm hden))

/-- Rocq: `Notation.CantorDecomposition.cantor_list_is_finite`. -/
def cantorListIsFinite : List A → Option Nat
  | [] => some 0
  | x :: xs =>
    match X.decompose x with
    | [] => some (xs.length + 1)
    | _ :: _ => none

omit X in
/-- Rocq: `Notation.CantorDecomposition.leading_zero_finite`. -/
theorem leading_zero_finite : ∀ (xs : List A) (x : A), CantorOrdered f (x :: xs) → f x ≈ 0 →
    cantorDenote f (x :: xs) ≈ ofNat (xs.length + 1)
  | [], _, _, hx => powOmega_add_zero_of_zero hx
  | y :: xs, _, hord, hx =>
    have hy : f y ≈ 0 := equiv_intro (le_trans hord.1 hx.le) (zero_least _)
    equiv_trans (add_congr (equiv_trans (pow_congr (equiv_refl ω) hx) (pow_zero ω))
      (leading_zero_finite xs y hord.2 hy)) (onePlus_finite_succ _)

/-- Rocq: `Notation.CantorDecomposition.cantor_list_is_finite_correct`. -/
theorem cantor_list_is_finite_correct : ∀ xs : List A, Each P xs → CantorOrdered f xs →
    match cantorListIsFinite X xs with
    | some n => cantorDenote f xs ≈ ofNat n
    | none => ∃ a b, xs = a :: b ∧ 0 < f a
  | [], _, _ => equiv_refl _
  | x :: xs, hP, hord => by
    obtain ⟨_, _, hden⟩ := X.decompose_correct x hP.1
    show match (match X.decompose x with
        | [] => some (xs.length + 1)
        | _ :: _ => none) with
      | some n => cantorDenote f (x :: xs) ≈ ofNat n
      | none => ∃ a b, x :: xs = a :: b ∧ 0 < f a
    revert hden
    cases X.decompose x with
    | nil => exact fun hden => leading_zero_finite xs x hord hden
    | cons _ _ => exact fun hden => ⟨x, xs, rfl, lt_of_lt_of_le denote_pos hden.ge⟩

/-! ## Multiplication -/

/-- `x * ω ^ e`, which is `ω ^ (x₁ + e)` for `x₁` the leading exponent of `x`,
apart from special cases for empty sums.
Rocq: `Notation.CantorDecomposition.cantor_mul_single`. -/
def cantorMulSingle : List A → List A → List A
  | [], _ => []
  | x₁ :: xs, [] => x₁ :: xs
  | x₁ :: _, e :: es => [X.recompose (cantorAddList X (X.decompose x₁) (e :: es))]

/-- Rocq: `Notation.CantorDecomposition.cantor_mul_single_prop_ordered`. -/
theorem cantor_mul_single_prop_ordered : ∀ x e : List A, Each P x → Each P e →
    CantorOrdered f x → CantorOrdered f e →
    Each P (cantorMulSingle X x e) ∧ CantorOrdered f (cantorMulSingle X x e)
  | [], _, _, _, _, _ => ⟨trivial, trivial⟩
  | _ :: _, [], hPx, _, hx, _ => ⟨hPx, hx⟩
  | x₁ :: _, _ :: _, hPx, hPe, _, he =>
    let d := X.decompose_correct x₁ hPx.1
    ⟨⟨(X.recompose_correct _ (cantor_add_prop X _ _ d.1 hPe)
        (cantor_add_ordered X _ _ d.2.1 he d.1 hPe)).1, trivial⟩, trivial, trivial⟩

omit X in
/-- An ordered list is bounded by its first term times its length. -/
private theorem dominates {b : Ordinal.{0}} : ∀ xs : List A, HeadLe f b xs → CantorOrdered f xs →
    cantorDenote f xs ≤ ω ^ b * ofNat xs.length
  | [], _, _ => zero_least _
  | _ :: xs, hb, hord =>
    le_trans (add_le_add (pow_le_pow_right ω hb) (dominates xs (hord.1.mono hb) hord.2))
      (add_mul_ofNat_le _ _)

/-- Rocq: `Notation.CantorDecomposition.cantor_mul_single_correct`. -/
theorem cantor_mul_single_correct : ∀ x e : List A, Each P x → Each P e →
    CantorOrdered f x → CantorOrdered f e →
    cantorDenote f (cantorMulSingle X x e) ≈ cantorDenote f x * ω ^ cantorDenote f e
  | [], _, _, _, _, _ => equiv_symm (zero_mul _)
  | _ :: _, [], _, _, _, _ =>
    equiv_symm (equiv_trans (mul_congr (equiv_refl _) (pow_zero ω)) (mul_one _))
  | x₁ :: xs, e :: es, hPx, hPe, hx, he => by
    obtain ⟨d₁, d₂, d₃⟩ := X.decompose_correct x₁ hPx.1
    have hr := X.recompose_correct _ (cantor_add_prop X _ _ d₁ hPe)
      (cantor_add_ordered X _ _ d₂ he d₁ hPe)
    have hfr : f (X.recompose (cantorAddList X (X.decompose x₁) (e :: es))) ≈
        f x₁ + cantorDenote f (e :: es) :=
      equiv_trans (equiv_symm hr.2) (equiv_trans
        (cantor_add_list_correct X _ _ d₂ he d₁ hPe) (add_congr (equiv_symm d₃) (equiv_refl _)))
    refine equiv_trans (add_zero _) (equiv_trans (pow_congr (equiv_refl ω) hfr)
      (equiv_trans (pow_add ω _ _) (equiv_intro ?_ ?_)))
    · exact mul_le_mul_right _ (le_add_right _ _)
    · exact pow_omega_collapse _ _ ⟨xs.length⟩ (dominates xs hx.1 hx.2) _
        (cantor_denote_complete X _) denote_pos

/-- Rocq: `Notation.CantorDecomposition.cantor_mul_list`. -/
def cantorMulList (xs : List A) : List A → List A
  | [] => []
  | y :: ys => cantorAddList X (cantorMulSingle X xs (X.decompose y)) (cantorMulList xs ys)

/-- Rocq: `Notation.CantorDecomposition.cantor_mul_list_prop_ordered`. -/
theorem cantor_mul_list_prop_ordered (xs : List A) : ∀ ys : List A, Each P xs → Each P ys →
    CantorOrdered f xs → CantorOrdered f ys →
    Each P (cantorMulList X xs ys) ∧ CantorOrdered f (cantorMulList X xs ys)
  | [], _, _, _, _ => ⟨trivial, trivial⟩
  | y :: ys, hPx, hPy, hx, hy => by
    obtain ⟨d₁, d₂, _⟩ := X.decompose_correct y hPy.1
    obtain ⟨m₁, m₂⟩ := cantor_mul_single_prop_ordered X xs _ hPx d₁ hx d₂
    obtain ⟨l₁, l₂⟩ := cantor_mul_list_prop_ordered xs ys hPx hPy.2 hx hy.2
    exact ⟨cantor_add_prop X _ _ m₁ l₁, cantor_add_ordered X _ _ m₂ l₂ m₁ l₁⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_mul_list_correct`. -/
theorem cantor_mul_list_correct (xs : List A) : ∀ ys : List A, Each P xs → Each P ys →
    CantorOrdered f xs → CantorOrdered f ys →
    cantorDenote f (cantorMulList X xs ys) ≈ cantorDenote f xs * cantorDenote f ys
  | [], _, _, _, _ => equiv_symm (mul_zero _)
  | y :: ys, hPx, hPy, hx, hy => by
    obtain ⟨d₁, d₂, d₃⟩ := X.decompose_correct y hPy.1
    obtain ⟨m₁, m₂⟩ := cantor_mul_single_prop_ordered X xs _ hPx d₁ hx d₂
    obtain ⟨l₁, l₂⟩ := cantor_mul_list_prop_ordered X xs ys hPx hPy.2 hx hy.2
    exact equiv_trans (cantor_add_list_correct X _ _ m₂ l₂ m₁ l₁)
      (equiv_trans (add_congr
        (equiv_trans (cantor_mul_single_correct X xs _ hPx d₁ hx d₂)
          (mul_congr (equiv_refl _) (pow_congr (equiv_refl ω) (equiv_symm d₃))))
        (cantor_mul_list_correct xs ys hPx hPy.2 hx hy.2))
      (equiv_symm (mul_add _ _ _)))

/-- Rocq: `Notation.CantorDecomposition.cantor_mul`. -/
def cantorMul (x y : A) : A :=
  X.recompose (cantorMulList X (X.decompose x) (X.decompose y))

/-- Rocq: `Notation.CantorDecomposition.cantor_mul_reflects`. -/
theorem cantor_mul_reflects : Reflects A f P (.ord ==> .ord ==> .ord) (· * ·) (cantorMul X) :=
  reflects_of_list X (cantorMulList X) mul_congr
    (fun xs ys hPx hPy hx hy => cantor_mul_list_prop_ordered X xs ys hPx hPy hx hy)
    (fun xs ys hPx hPy hx hy => cantor_mul_list_correct X xs ys hPx hPy hx hy)

/-! ## Exponentiation -/

/-- `x ^ (ω ^ e)`, by cases on whether `x` and `e` are finite.
Rocq: `Notation.CantorDecomposition.cantor_exp_single`. -/
def cantorExpSingle (x e : List A) : List A :=
  match x with
  -- 0 ^ (ω ^ e) = 1
  | [] => [cantorZero X]
  | x₁ :: xs =>
    match cantorListIsFinite X (x₁ :: xs) with
    -- does not happen
    | some 0 => [cantorZero X]
    -- 1 ^ (ω ^ e) = 1
    | some 1 => [cantorZero X]
    | some (_ + 2) =>
      match cantorListIsFinite X e with
      -- n ^ (ω ^ 0) = n
      | some 0 => x
      -- n ^ (ω ^ (1 + m)) = ω ^ (ω ^ m) for finite n > 1, finite m
      | some (m + 1) => [X.recompose [cantorNat X m]]
      -- n ^ (ω ^ e) = ω ^ (ω ^ e) for e ≥ ω, finite n > 1
      | none => [X.recompose [X.recompose e]]
    | none =>
      match e with
      -- x ^ (ω ^ 0) = x
      | [] => x
      -- (ω ^ x₁ + b) ^ (ω ^ e) = ω ^ (x₁ * ω ^ e) when x₁ ≥ 1, e > 0
      | _ :: _ => [X.recompose (cantorMulSingle X (X.decompose x₁) e)]


omit X in
/-- `0 ^ y ≈ 1`: in this development, `x ^ y` is `1` joined with the
`x ^ y' * x` for `y' < y`. -/
theorem zero_pow_equiv (y : Ordinal.{0}) : (0 : Ordinal.{0}) ^ y ≈ 1 := by
  refine equiv_intro ?_ (succ_least (pow_pos 0 y))
  rw [pow_unfold]
  exact lub_least (le_refl 1) (sup_least fun _ => le_trans (mul_zero _).le (zero_least 1))

omit X in
/-- `x ≈ x ^ (ω ^ e)` when `e ≈ 0` and `0 < x`. -/
private theorem pow_powOmega_zero {x e : Ordinal.{0}} (hx : 0 < x) (he : e ≈ 0) :
    x ≈ x ^ ω ^ e :=
  equiv_symm (equiv_trans (pow_congr (equiv_refl x)
    (equiv_trans (pow_congr (equiv_refl ω) he) (pow_zero ω))) (pow_one' hx))

/-- `[r]` for `r` a well-formed term. -/
private theorem singleton_spec {r : A} (hr : P r) : Each P [r] ∧ CantorOrdered f [r] :=
  ⟨⟨hr, trivial⟩, trivial, trivial⟩

/-- Well-formedness and correctness of `cantorExpSingle`, proved together
since they follow the same case analysis. -/
private theorem exp_single_spec : ∀ x e : List A, Each P x → Each P e →
    CantorOrdered f x → CantorOrdered f e →
    Each P (cantorExpSingle X x e) ∧ CantorOrdered f (cantorExpSingle X x e) ∧
      cantorDenote f (cantorExpSingle X x e) ≈ cantorDenote f x ^ ω ^ cantorDenote f e
  | [], e, _, _, _, _ =>
    ⟨(singleton_spec (f := f) (cantorZero_spec X).1).1, (singleton_spec (f := f) (cantorZero_spec X).1).2,
      equiv_trans (powOmega_add_zero_of_zero (cantorZero_spec X).2)
        (equiv_symm (zero_pow_equiv _))⟩
  | x₁ :: xs, e, hPx, hPe, hx, he => by
    obtain ⟨d₁, d₂, d₃⟩ := X.decompose_correct x₁ hPx.1
    show (fun v => Each P v ∧ CantorOrdered f v ∧
        cantorDenote f v ≈ cantorDenote f (x₁ :: xs) ^ ω ^ cantorDenote f e)
      (match (match X.decompose x₁ with
          | [] => some (xs.length + 1)
          | _ :: _ => none) with
        | some 0 => [cantorZero X]
        | some 1 => [cantorZero X]
        | some (_ + 2) =>
          match cantorListIsFinite X e with
          | some 0 => x₁ :: xs
          | some (m + 1) => [X.recompose [cantorNat X m]]
          | none => [X.recompose [X.recompose e]]
        | none =>
          match (generalizing := false) e with
          | [] => x₁ :: xs
          | _ :: _ => [X.recompose (cantorMulSingle X (X.decompose x₁) e)])
    revert d₁ d₂ d₃
    cases X.decompose x₁ with
    | nil =>
      intro _ _ d₃
      cases xs with
      | nil =>
        -- `x = 1`
        exact ⟨(singleton_spec (f := f) (cantorZero_spec X).1).1, (singleton_spec (f := f) (cantorZero_spec X).1).2,
          equiv_trans (powOmega_add_zero_of_zero (cantorZero_spec X).2) (equiv_symm
            (equiv_trans (pow_congr (powOmega_add_zero_of_zero d₃) (equiv_refl _)) (one_pow _)))⟩
      | cons y ys =>
        -- `x = n > 1`
        have hN : cantorDenote f (x₁ :: y :: ys) ≈ ω (⟨(y :: ys).length + 1⟩ : ULift Nat) :=
          leading_zero_finite (y :: ys) x₁ hx d₃
        have hN₁ : 1 < ω (⟨(y :: ys).length + 1⟩ : ULift Nat) :=
          ofNat_increasing (Nat.succ_lt_succ (Nat.succ_pos _))
        have hfe := cantor_list_is_finite_correct X e hPe he
        revert hfe
        cases cantorListIsFinite X e with
        | none =>
          rintro ⟨a, b, rfl, ha⟩
          have r₁ := X.recompose_correct (a :: b) hPe he
          have r₂ := X.recompose_correct _ (singleton_spec (f := f) r₁.1).1 (singleton_spec (f := f) r₁.1).2
          have he₁ : cantorDenote f (a :: b) ≈ 1 + cantorDenote f (a :: b) :=
            equiv_symm (equiv_trans (add_assoc _ _ _) (add_congr (equiv_intro
              (additively_closed_collapse (powOmega_additively_closed (X.complete a))
                (one_lt_powOmega ha)) (le_add_left _ _)) (equiv_refl _)))
          refine ⟨(singleton_spec (f := f) r₂.1).1, (singleton_spec (f := f) r₂.1).2, ?_⟩
          exact equiv_trans (add_zero _) (equiv_trans
            (pow_congr (equiv_refl ω) (equiv_trans (equiv_symm r₂.2) (equiv_trans (add_zero _)
              (pow_congr (equiv_refl ω) (equiv_symm r₁.2)))))
            (equiv_symm (equiv_trans (pow_congr hN (equiv_refl _))
              (expNatToOmegaInf _ _ hN₁ he₁))))
        | some n =>
          cases n with
          | zero => exact fun h => ⟨hPx, hx, pow_powOmega_zero denote_pos h⟩
          | succ m =>
            intro h
            have hm := cantor_nat_correct X m
            have r := X.recompose_correct _ (singleton_spec (f := f) hm.2).1 (singleton_spec (f := f) hm.2).2
            refine ⟨(singleton_spec (f := f) r.1).1, (singleton_spec (f := f) r.1).2, ?_⟩
            exact equiv_trans (add_zero _) (equiv_trans
              (pow_congr (equiv_refl ω) (equiv_trans (equiv_symm r.2) (equiv_trans (add_zero _)
                (pow_congr (equiv_refl ω) hm.1))))
              (equiv_symm (equiv_trans (pow_congr hN (pow_congr (equiv_refl ω)
                (equiv_trans h (ofNat_add m 1)))) (expNatToOmegaPow _ _ hN₁))))
    | cons d ds =>
      intro d₁ d₂ d₃
      have hx₁ : 0 < f x₁ := lt_of_lt_of_le denote_pos d₃.ge
      cases e with
      | nil => exact ⟨hPx, hx, pow_powOmega_zero denote_pos (equiv_refl _)⟩
      | cons e es =>
        have hm := cantor_mul_single_prop_ordered X _ _ d₁ hPe d₂ he
        have r := X.recompose_correct _ hm.1 hm.2
        refine ⟨(singleton_spec (f := f) r.1).1, (singleton_spec (f := f) r.1).2, ?_⟩
        refine equiv_trans (add_zero _) (equiv_trans (pow_congr (equiv_refl ω)
          (equiv_trans (equiv_symm r.2) (equiv_trans
            (cantor_mul_single_correct X _ _ d₁ hPe d₂ he)
            (mul_congr (equiv_symm d₃) (equiv_refl _))))) ?_)
        refine equiv_trans (pow_mul ω _ _) (equiv_intro ?_ ?_)
        · exact pow_le_pow_left (le_add_right _ _) _
        · refine expToOmega_collapse_tower _ _ ⟨xs.length⟩ ?_ (dominates xs hx.1 hx.2) _
            (cantor_denote_complete X _) denote_pos
          calc ofNat xs.length + 1 ≈ ofNat (1 + xs.length) := equiv_symm (ofNat_add 1 xs.length)
            _ ≤ ω := le_of_lt (index_lt ω ⟨1 + xs.length⟩)
            _ ≤ ω ^ 1 := (pow_one' omega_gt0).ge
            _ ≤ ω ^ f x₁ := pow_le_pow_right ω (succ_least hx₁)

/-- Rocq: `Notation.CantorDecomposition.cantor_exp_single_prop_ordered`. -/
theorem cantor_exp_single_prop_ordered (x e : List A) (hPx : Each P x) (hPe : Each P e)
    (hx : CantorOrdered f x) (he : CantorOrdered f e) :
    Each P (cantorExpSingle X x e) ∧ CantorOrdered f (cantorExpSingle X x e) :=
  ⟨(exp_single_spec X x e hPx hPe hx he).1, (exp_single_spec X x e hPx hPe hx he).2.1⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_exp_single_correct`. -/
theorem cantor_exp_single_correct (x e : List A) (hPx : Each P x) (hPe : Each P e)
    (hx : CantorOrdered f x) (he : CantorOrdered f e) :
    cantorDenote f (cantorExpSingle X x e) ≈ cantorDenote f x ^ ω ^ cantorDenote f e :=
  (exp_single_spec X x e hPx hPe hx he).2.2

/-- Rocq: `Notation.CantorDecomposition.cantor_exp_list`. -/
def cantorExpList (xs : List A) : List A → List A
  | [] => [cantorZero X]
  | y :: ys => cantorMulList X (cantorExpSingle X xs (X.decompose y)) (cantorExpList xs ys)

/-- Rocq: `Notation.CantorDecomposition.cantor_exp_list_prop_ordered`. -/
theorem cantor_exp_list_prop_ordered (xs : List A) : ∀ ys : List A, Each P xs → Each P ys →
    CantorOrdered f xs → CantorOrdered f ys →
    Each P (cantorExpList X xs ys) ∧ CantorOrdered f (cantorExpList X xs ys)
  | [], _, _, _, _ => singleton_spec (cantorZero_spec X).1
  | y :: ys, hPx, hPy, hx, hy => by
    obtain ⟨d₁, d₂, _⟩ := X.decompose_correct y hPy.1
    obtain ⟨m₁, m₂⟩ := cantor_exp_single_prop_ordered X xs _ hPx d₁ hx d₂
    obtain ⟨l₁, l₂⟩ := cantor_exp_list_prop_ordered xs ys hPx hPy.2 hx hy.2
    exact cantor_mul_list_prop_ordered X _ _ m₁ l₁ m₂ l₂

/-- Rocq: `Notation.CantorDecomposition.cantor_exp_list_correct`. -/
theorem cantor_exp_list_correct (xs : List A) : ∀ ys : List A, Each P xs → Each P ys →
    CantorOrdered f xs → CantorOrdered f ys →
    cantorDenote f (cantorExpList X xs ys) ≈ cantorDenote f xs ^ cantorDenote f ys
  | [], _, _, _, _ =>
    equiv_trans (powOmega_add_zero_of_zero (cantorZero_spec X).2) (equiv_symm (pow_zero _))
  | y :: ys, hPx, hPy, hx, hy => by
    obtain ⟨d₁, d₂, d₃⟩ := X.decompose_correct y hPy.1
    obtain ⟨m₁, m₂⟩ := cantor_exp_single_prop_ordered X xs _ hPx d₁ hx d₂
    obtain ⟨l₁, l₂⟩ := cantor_exp_list_prop_ordered X xs ys hPx hPy.2 hx hy.2
    exact equiv_trans (cantor_mul_list_correct X _ _ m₁ l₁ m₂ l₂)
      (equiv_trans (mul_congr
        (equiv_trans (cantor_exp_single_correct X xs _ hPx d₁ hx d₂)
          (pow_congr (equiv_refl _) (pow_congr (equiv_refl ω) (equiv_symm d₃))))
        (cantor_exp_list_correct xs ys hPx hPy.2 hx hy.2))
      (equiv_symm (pow_add _ _ _)))

/-- Rocq: `Notation.CantorDecomposition.cantor_exp`. -/
def cantorExp (x y : A) : A :=
  X.recompose (cantorExpList X (X.decompose x) (X.decompose y))

/-- Rocq: `Notation.CantorDecomposition.cantor_exp_reflects`. -/
theorem cantor_exp_reflects : Reflects A f P (.ord ==> .ord ==> .ord) (· ^ ·) (cantorExp X) :=
  reflects_of_list X (cantorExpList X) pow_congr
    (fun xs ys hPx hPy hx hy => cantor_exp_list_prop_ordered X xs ys hPx hPy hx hy)
    (fun xs ys hPx hPy hx hy => cantor_exp_list_correct X xs ys hPx hPy hx hy)


/-! ## Interpolants -/

/-- `z` has interpolants when every `i < z` is bounded by a well-formed term
below `z` that itself has interpolants. The recursion is on the
accessibility of `z`. Rocq: `Notation.CantorDecomposition.has_interpolants_rec`. -/
def HasInterpolantsRec (f : A → Ordinal.{0}) (P : A → Prop) {z : Ordinal.{0}}
    (h : Acc (· < ·) z) : Prop :=
  Acc.rec (motive := fun _ _ => Prop)
    (fun z _ ih => ∀ i, i < z → ∃ (y : A) (hlt : f y < z), P y ∧ i ≤ f y ∧ ih (f y) hlt) h

omit X in
/-- The accessibility proof does not matter. In Lean this holds by definitional
proof irrelevance. Rocq: `Notation.CantorDecomposition.has_interpolants_rec_H_irrelevant`. -/
theorem has_interpolants_rec_H_irrelevant (z : Ordinal.{0}) (H1 H2 : Acc (· < ·) z) :
    HasInterpolantsRec f P H1 → HasInterpolantsRec f P H2 := id

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_interpolants_rec_eq_mor`. -/
theorem has_interpolants_rec_eq_mor (x y : Ordinal.{0}) (H1 : Acc (· < ·) x)
    (H2 : Acc (· < ·) y) (hxy : x ≈ y) :
    HasInterpolantsRec f P H1 → HasInterpolantsRec f P H2 := by
  cases H1 with
  | intro _ h1 =>
    cases H2 with
    | intro _ h2 =>
      intro hx i hi
      obtain ⟨z, hz, hPz, hiz, hrec⟩ := hx i (lt_of_lt_of_le hi hxy.ge)
      exact ⟨z, lt_of_lt_of_le hz hxy.le, hPz, hiz, hrec⟩

/-- Rocq: `Notation.CantorDecomposition.has_interpolants`. -/
def HasInterpolants (f : A → Ordinal.{0}) (P : A → Prop) (z : Ordinal.{0}) : Prop :=
  HasInterpolantsRec f P (lt_wf.apply z)

omit X in
private theorem has_interpolants_rec_unfold {z : Ordinal.{0}} (H : Acc (· < ·) z) :
    HasInterpolantsRec f P H ↔
      ∀ i, i < z → ∃ y : A, P y ∧ i ≤ f y ∧ f y < z ∧ HasInterpolants f P (f y) := by
  cases H with
  | intro _ h =>
    show (∀ i, i < z → ∃ (y : A) (hlt : f y < z), P y ∧ i ≤ f y ∧
        HasInterpolantsRec f P (h (f y) hlt)) ↔ _
    exact ⟨fun hz i hi => let ⟨y, hlt, hPy, hiy, hrec⟩ := hz i hi; ⟨y, hPy, hiy, hlt, hrec⟩,
      fun hz i hi => let ⟨y, hPy, hiy, hlt, hrec⟩ := hz i hi; ⟨y, hlt, hPy, hiy, hrec⟩⟩

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_interpolants_unfold`. -/
theorem has_interpolants_unfold (z : Ordinal.{0}) :
    HasInterpolants f P z ↔
      ∀ i, i < z → ∃ y : A, P y ∧ i ≤ f y ∧ f y < z ∧ HasInterpolants f P (f y) :=
  has_interpolants_rec_unfold _

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_interpolants_eq_mor`. -/
theorem has_interpolants_eq_mor {x y : Ordinal.{0}} (h : x ≈ y) :
    HasInterpolants f P x ↔ HasInterpolants f P y :=
  ⟨has_interpolants_rec_eq_mor x y _ _ h, has_interpolants_rec_eq_mor y x _ _ (equiv_symm h)⟩

/-- Every well-formed term has interpolants.
Rocq: `Notation.CantorDecomposition.has_all_interpolants`. -/
def HasAllInterpolants (f : A → Ordinal.{0}) (P : A → Prop) : Prop :=
  ∀ a, P a → HasInterpolants f P (f a)

/-- Every ordinal below a well-formed term has a notation.
Rocq: `Notation.CantorDecomposition.has_enough_notations`. -/
def HasEnoughNotations (f : A → Ordinal.{0}) (P : A → Prop) : Prop :=
  ∀ (a : A) (x : Ordinal.{0}), P a → x ≤ f a → ∃ b, P b ∧ f b ≈ x

omit X in
/-- Induction on the denotation of a term. -/
private theorem measure_ind (f : A → Ordinal.{0}) {motive : A → Prop}
    (h : ∀ a, (∀ b, f b < f a → motive b) → motive a) (a : A) : motive a :=
  ltRec (motive := fun o => ∀ a, f a ≤ o → motive a)
    (fun _ ih a ha => h a fun b hb => ih (f b) (lt_of_lt_of_le hb ha) b (le_refl _))
    (f a) a (le_refl _)

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_enough_notations_has_all_interpolants`. -/
theorem has_enough_notations_has_all_interpolants (H : HasEnoughNotations f P) :
    HasAllInterpolants f P :=
  measure_ind f fun a ih ha => (has_interpolants_unfold _).2 fun i hi =>
    let ⟨x, hx₁, hx₂⟩ := H a i ha (le_of_lt hi)
    have hxa : f x < f a := lt_of_le_of_lt hx₂.le hi
    ⟨x, hx₁, hx₂.ge, hxa, ih x hxa hx₁⟩

include X in
/-- Enough notations give the excluded middle, since comparison with zero is
decidable. Rocq: `Notation.CantorDecomposition.has_enough_notations_EM`. -/
theorem has_enough_notations_EM (H : HasEnoughNotations f P) : ExcludedMiddle := fun Q => by
  obtain ⟨hn₁, hn₂⟩ := cantor_nat_correct X 1
  obtain ⟨z, hz₁, hz₂⟩ := H (cantorNat X 1) (truthOrd.{0} Q) hn₂
    (le_trans (le_intro fun _ => succ_lt 0) hn₁.ge)
  obtain ⟨hzero₁, hzero₂⟩ := cantorZero_spec X
  have hc := X.compare_correct (cantorZero X) z hzero₁ hz₁
  revert hc
  cases X.compare (cantorZero X) z with
  | lt =>
    intro hc
    exact (lt_elim (lt_of_le_of_lt hzero₂.ge (lt_of_lt_of_le hc hz₂.le))).elim
      fun b _ => .inl b.down.down
  | eq =>
    exact fun hc => .inr fun q => lt_irrefl 0 (lt_of_lt_of_le
      (index_lt (truthOrd.{0} Q) ⟨⟨q⟩⟩) (le_trans hz₂.ge (le_trans hc.ge hzero₂.le)))
  | gt =>
    exact fun hc => (lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le hc hzero₂.le) (zero_least _))).elim

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_interpolants_has_enough_notations`. -/
theorem has_interpolants_has_enough_notations (em : ExcludedMiddle)
    (Hinterp : HasAllInterpolants f P) : HasEnoughNotations f P := by
  intro a i ha hi
  let Q := fun o => ∃ v : A, P v ∧ i ≤ f v ∧ o ≈ f v
  obtain ⟨z, ⟨v, hv₁, hv₂, hv₃⟩, hz⟩ := ord_well_ordered em Q (f a) ⟨a, ha, hi, equiv_refl _⟩
  refine ⟨v, hv₁, equiv_intro ?_ hv₂⟩
  cases order_total em (f v) i with
  | inl h => exact h
  | inr h =>
    obtain ⟨q, hq₁, hq₂, hq₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp v hv₁) i h
    exact (lt_irrefl z (lt_of_le_of_lt (hz (f q) ⟨q, hq₁, hq₂, equiv_refl _⟩)
      (lt_of_lt_of_le hq₃ hv₃.ge))).elim

include X in
/-- With the excluded middle, having all interpolants is the same as having
enough notations.
Rocq: `Notation.CantorDecomposition.has_all_interpolants_EM_iff_has_enough_notations`. -/
theorem has_all_interpolants_EM_iff_has_enough_notations :
    (HasAllInterpolants f P ∧ ExcludedMiddle) ↔ HasEnoughNotations f P :=
  ⟨fun ⟨h, em⟩ => has_interpolants_has_enough_notations em h,
    fun h => ⟨has_enough_notations_has_all_interpolants h, has_enough_notations_EM X h⟩⟩

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_interpolants_lub`. -/
theorem has_interpolants_lub (p q : Ordinal.{0}) (hp : HasInterpolants f P p)
    (hq : HasInterpolants f P q) : HasInterpolants f P (p ⊔ q) :=
  (has_interpolants_unfold _).2 fun i hi =>
    match lub_lt hi with
    | .inl hi =>
      let ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hp i hi
      ⟨y, hy₁, hy₂, lt_of_lt_of_le hy₃ (lub_le1 p q), hy₄⟩
    | .inr hi =>
      let ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hq i hi
      ⟨y, hy₁, hy₂, lt_of_lt_of_le hy₃ (lub_le2 p q), hy₄⟩

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_interpolants_sup`. -/
theorem has_interpolants_sup (B : Type) (g : B → Ordinal.{0})
    (hg : ∀ b, HasInterpolants f P (g b)) : HasInterpolants f P (sup g) :=
  (has_interpolants_unfold _).2 fun i hi =>
    let ⟨b, hi⟩ := sup_lt hi
    let ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 (hg b) i hi
    ⟨y, hy₁, hy₂, lt_of_lt_of_le hy₃ (sup_le g b), hy₄⟩

omit X in
/-- Rocq: `Notation.CantorDecomposition.has_interpolants_add`. -/
theorem has_interpolants_add (add : A → A → A)
    (hadd : Reflects A f P (.ord ==> .ord ==> .ord) (· + ·) add) (p : A) :
    ∀ q : Ordinal.{0}, P p → HasInterpolants f P (f p) → HasInterpolants f P q →
      HasInterpolants f P (f p + q) := by
  intro q
  refine ltRec (motive := fun q => P p → HasInterpolants f P (f p) → HasInterpolants f P q →
    HasInterpolants f P (f p + q)) (fun q ih hp₁ hp₂ hq => ?_) q
  rw [add_unfold]
  refine has_interpolants_lub _ _ hp₂ ((has_interpolants_unfold _).2 fun i hi => ?_)
  obtain ⟨q', hi⟩ := sup_lt hi
  obtain ⟨_, hi⟩ := lt_elim hi
  obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hq (q q') (index_lt q q')
  obtain ⟨hadd₁, hadd₂⟩ := hadd (f p) p ⟨equiv_refl _, hp₁⟩ (f y) y ⟨equiv_refl _, hy₁⟩
  refine ⟨add p y, hadd₂, le_trans hi (le_trans (add_le_add (le_refl _) hy₂) hadd₁.le), ?_,
    (has_interpolants_eq_mor hadd₁).1 (ih (f y) hy₃ hp₁ hp₂ hy₄)⟩
  obtain ⟨q'', hq''⟩ := lt_elim hy₃
  exact lt_of_le_of_lt hadd₁.ge (lt_of_lt_of_le (succ_lt _)
    (le_trans (succ_monotone (add_le_add (le_refl _) hq''))
      (sup_le (fun i : q => succ (f p + q i)) q'')))

section fix_interpolants

variable (g : Ordinal.{0} → Ordinal.{0})

omit X in
/-- Rocq: `Notation.CantorDecomposition.iter_has_interpolants`. -/
theorem iter_has_interpolants (hg₁ : ∀ b, Complete b → Complete (g b))
    (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b)) :
    ∀ (m : Nat) (b : Ordinal.{0}), Complete b → HasInterpolants f P b →
      HasInterpolants f P (iterF g b m)
  | 0, _, _, hb => hb
  | m + 1, b, hb₁, hb₂ =>
    hg₂ _ (iterF_complete m b hb₁ hg₁) (iter_has_interpolants hg₁ hg₂ m b hb₁ hb₂)

omit X in
/-- Rocq: `Notation.CantorDecomposition.fix_has_interpolants`. -/
theorem fix_has_interpolants (hg₁ : ∀ b, Complete b → Complete (g b))
    (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b))
    (b : Ordinal.{0}) (hb₁ : Complete b) (hb₂ : HasInterpolants f P b) :
    HasInterpolants f P (fixOrd g b) :=
  has_interpolants_sup _ _ fun n => iter_has_interpolants g hg₁ hg₂ n.down b hb₁ hb₂

include X in
/-- Rocq: `Notation.CantorDecomposition.enum_fix_has_interpolants`. -/
theorem enum_fix_has_interpolants (hg₁ : ∀ b, Complete b → Complete (g b))
    (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b))
    (hg₃ : ∀ x y, x ≤ y → g x ≤ g y) (hg₄ : ∀ x, Complete x → x ≤ g x)
    (enum_gr : A → A) (hgr : Reflects A f P (.ord ==> .ord) (enumFixpoints g) enum_gr) :
    ∀ b : Ordinal.{0}, Complete b → HasInterpolants f P b →
      HasInterpolants f P (enumFixpoints g b) := by
  intro b
  refine ltRec (motive := fun b => Complete b → HasInterpolants f P b →
    HasInterpolants f P (enumFixpoints g b)) (fun b ih hb₁ hb₂ => ?_) b
  rw [enumFixpoints_unfold]
  refine fix_has_interpolants g hg₁ hg₂ _ ?_ ((has_interpolants_unfold _).2 fun i hi => ?_)
  · exact lim_complete (fun a => enumFixpoints_complete hg₄ hg₃ hg₁ _ (complete_subord hb₁ a))
      (directed_monotone b _ (fun x y hxy => enumFixpoints_monotone hg₃ _ _ hxy) hb₁)
      (cast (complete_unfold b) hb₁).2.1
  obtain ⟨k, hi⟩ := lt_elim hi
  obtain ⟨br, hbr₁, hbr₂, hbr₃, hbr₄⟩ := (has_interpolants_unfold _).1 hb₂ (b k) (index_lt b k)
  obtain ⟨h₁, h₂⟩ := hgr (f br) br ⟨equiv_refl _, hbr₁⟩
  obtain ⟨b', hb'⟩ := lt_elim hbr₃
  exact ⟨enum_gr br, h₂, le_trans hi (le_trans (enumFixpoints_monotone hg₃ _ _ hbr₂) h₁.le),
    lt_intro (show (mk b.Carrier fun b' => enumFixpoints g (b b')).Carrier from b')
      (le_trans h₁.ge (enumFixpoints_monotone hg₃ _ _ hb')),
    (has_interpolants_eq_mor h₁).1 (ih (f br) hbr₃ (X.complete br) hbr₄)⟩

end fix_interpolants

omit X in
/-- Rocq: `Notation.CantorDecomposition.onePlus_interpolants`. -/
theorem onePlus_interpolants (zr : A) (hzr : Reflects A f P .ord 0 zr) (pr : A → A)
    (hpr : Reflects A f P (.ord ==> .ord) (fun x => 1 + x) pr) :
    ∀ b : Ordinal.{0}, HasInterpolants f P b → HasInterpolants f P (1 + b) := by
  intro b
  refine ltRec (motive := fun b => HasInterpolants f P b → HasInterpolants f P (1 + b))
    (fun b ih hb => (has_interpolants_unfold _).2 fun i hi => ?_) b
  rw [add_unfold] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨_, hi⟩ := lt_elim hi
    refine ⟨zr, hzr.2, le_trans hi hzr.1.le,
      lt_of_le_of_lt hzr.1.ge (lt_of_lt_of_le (succ_lt 0) (le_add_right _ _)),
      (has_interpolants_unfold _).2 fun i' hi' => ?_⟩
    exact (lt_irrefl i' (lt_of_lt_of_le (lt_of_lt_of_le hi' hzr.1.ge) (zero_least _))).elim
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    obtain ⟨_, hi⟩ := lt_elim hi
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hb (b j) (index_lt b j)
    obtain ⟨hp₁, hp₂⟩ := hpr (f y) y ⟨equiv_refl _, hy₁⟩
    exact ⟨pr y, hp₂, le_trans hi (le_trans (add_le_add (le_refl _) hy₂) hp₁.le),
      lt_of_le_of_lt hp₁.ge (add_lt_add_left 1 hy₃), (has_interpolants_eq_mor hp₁).1 (ih _ hy₃ hy₄)⟩

section veblen_interpolants

variable (g : Ordinal.{0} → Ordinal.{0}) (hg₁ : NormalFunction g)
  (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b))
  (vr : A → A → A) (hvr : Reflects A f P (.ord ==> .ord ==> .ord) (veblen g) vr)

include X hg₁ hg₂ hvr in
/-- Rocq: `Notation.CantorDecomposition.veblen_interpolants`. -/
theorem veblen_interpolants : ∀ (a : A) (b : Ordinal.{0}), P a → HasInterpolants f P (f a) →
    Complete b → HasInterpolants f P b → HasInterpolants f P (veblen g (f a) b) := by
  have mono := hg₁.monotone
  intro a
  refine measure_ind f (motive := fun a => ∀ b : Ordinal.{0}, P a → HasInterpolants f P (f a) →
    Complete b → HasInterpolants f P b → HasInterpolants f P (veblen g (f a) b))
    (fun a iha => ?_) a
  intro b
  refine ltRec (motive := fun b => P a → HasInterpolants f P (f a) →
    Complete b → HasInterpolants f P b → HasInterpolants f P (veblen g (f a) b))
    (fun b ihb ha₁ ha₂ hb₁ hb₂ => (has_interpolants_unfold _).2 fun i hi => ?_) b
  rw [veblen_unroll] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 (hg₂ b hb₁ hb₂) i hi
    refine ⟨y, hy₁, hy₂, ?_, hy₄⟩
    rw [veblen_unroll]
    exact lt_of_lt_of_le hy₃ (lub_le1 _ _)
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    -- the limit of `veblen g (f a)` below `b`
    have hb' : HasInterpolants f P (lim fun x : b => veblen g (f a) (b x)) := by
      refine (has_interpolants_unfold _).2 fun i₀ hi₀ => ?_
      obtain ⟨k, hi₀⟩ := lt_elim hi₀
      obtain ⟨q, hq₁, hq₂, hq₃, hq₄⟩ := (has_interpolants_unfold _).1 hb₂ (b k) (index_lt b k)
      obtain ⟨hv₁, hv₂⟩ := hvr (f a) a ⟨equiv_refl _, ha₁⟩ (f q) q ⟨equiv_refl _, hq₁⟩
      obtain ⟨k', hk'⟩ := lt_elim hq₃
      exact ⟨vr a q, hv₂, le_trans hi₀ (le_trans (veblen_monotone mono _ _ _ hq₂) hv₁.le),
        lt_intro (show (lim fun x : b => veblen g (f a) (b x)).Carrier from k')
          (le_trans hv₁.ge (veblen_monotone mono _ _ _ hk')),
        (has_interpolants_eq_mor hv₁).1 (ihb (f q) hq₃ ha₁ ha₂ (X.complete q) hq₄)⟩
    have hb'c : Complete (lim fun x : b => veblen g (f a) (b x)) :=
      lim_complete (fun x => veblen_complete hg₁ hg₁.complete _ (X.complete a) _
          (complete_subord hb₁ x))
        (directed_monotone b _ (fun x y hxy => veblen_monotone mono _ _ _ hxy) hb₁)
        (cast (complete_unfold b) hb₁).2.1
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ :=
      (has_interpolants_unfold _).1 ha₂ ((f a) j) (index_lt (f a) j)
    have hi' : i < fixOrd (veblen g (f y)) (lim fun x : b => veblen g (f a) (b x)) :=
      lt_of_lt_of_le hi (fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hy₂)
        (fun x y hxy => veblen_monotone mono _ _ _ hxy) _)
    have hfix := fix_has_interpolants (veblen g (f y))
      (fun x hx => (veblen_normal hg₁ _ (X.complete y)).complete x hx)
      (fun x hx₁ hx₂ => iha y hy₃ x hy₁ hy₄ hx₁ hx₂) _ hb'c hb'
    obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
    refine ⟨z, hz₁, hz₂, ?_, hz₄⟩
    obtain ⟨zq, hzq⟩ := lt_elim hy₃
    rw [veblen_unroll]
    refine lt_of_lt_of_le hz₃ (le_trans ?_ (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun α : (f a).Carrier =>
      fixOrd (veblen g ((f a) α)) (lim fun x : b => veblen g (f a) (b x))) zq)
    exact fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hzq)
      (fun x y hxy => veblen_monotone mono _ _ _ hxy) _

include X hg₁ hg₂ hvr in
/-- Rocq: `Notation.CantorDecomposition.veblen_interpolants_first`. -/
theorem veblen_interpolants_first (a : Ordinal.{0}) (_ha₁ : Complete a)
    (ha₂ : HasInterpolants f P a) : HasInterpolants f P (veblen g a 0) := by
  have mono := hg₁.monotone
  have h0 : HasInterpolants f P 0 :=
    (has_interpolants_unfold _).2 fun j hj =>
      (lt_irrefl j (lt_of_lt_of_le hj (zero_least j))).elim
  refine (has_interpolants_unfold _).2 fun i hi => ?_
  rw [veblen_unroll] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 (hg₂ 0 zero_complete h0) i hi
    refine ⟨y, hy₁, hy₂, ?_, hy₄⟩
    rw [veblen_unroll]
    exact lt_of_lt_of_le hy₃ (lub_le1 _ _)
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    obtain ⟨k, hk₁, hk₂, hk₃, hk₄⟩ := (has_interpolants_unfold _).1 ha₂ (a j) (index_lt a j)
    have hL : (lim fun x : (0 : Ordinal.{0}).Carrier => veblen g a ((0 : Ordinal.{0}) x)) ≤ 0 :=
      le_intro fun x => nomatch x
    have hi' : i < fixOrd (veblen g (f k)) 0 :=
      lt_of_lt_of_le hi (le_trans (fixOrd_monotone (veblen_monotone mono _) hL)
        (fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hk₂)
          (fun x y hxy => veblen_monotone mono _ _ _ hxy) _))
    have hfix := fix_has_interpolants (veblen g (f k))
      (fun x hx => veblen_complete hg₁ hg₁.complete _ (X.complete k) x hx)
      (fun x hx₁ hx₂ => veblen_interpolants X g hg₁ hg₂ vr hvr k x hk₁ hk₄ hx₁ hx₂) 0
      zero_complete h0
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
    refine ⟨y, hy₁, hy₂, ?_, hy₄⟩
    obtain ⟨q, hq⟩ := lt_elim hk₃
    rw [veblen_unroll]
    refine lt_of_lt_of_le hy₃ (le_trans ?_ (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun α : a.Carrier =>
      fixOrd (veblen g (a α)) (lim fun x : (0 : Ordinal.{0}).Carrier =>
        veblen g a ((0 : Ordinal.{0}) x))) q)
    exact le_trans (fixOrd_monotone (veblen_monotone mono _) (zero_least _))
      (fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hq)
        (fun x y hxy => veblen_monotone mono _ _ _ hxy) _)

end veblen_interpolants


/-! ## Natural sums -/

section reflects_nadd

variable (Hinterp : HasAllInterpolants f P)

omit X in
include Hinterp in
/-- Rocq: `Notation.CantorDecomposition.add_nadd_assoc2'`. -/
theorem add_nadd_assoc2' (x : Ordinal.{0}) : ∀ (y : Ordinal.{0}) (z : A), P z →
    (∀ q, P q → f q ≤ f z → x ♯ f q ≤ x + f q) → (x + y) ♯ f z ≤ x + (y ♯ f z) := by
  intro y
  refine ltRec (motive := fun y => ∀ z : A, P z → (∀ q, P q → f q ≤ f z → x ♯ f q ≤ x + f q) →
    (x + y) ♯ f z ≤ x + (y ♯ f z)) (fun y ihy => ?_) y
  intro z
  refine measure_ind f (motive := fun z => P z → (∀ q, P q → f q ≤ f z → x ♯ f q ≤ x + f q) →
    (x + y) ♯ f z ≤ x + (y ♯ f z)) (fun z ihz hz H => ?_) z
  refine nadd_least2 ?_ ?_
  · rw [add_unfold x y]
    intro i
    cases i with
    | inl i =>
      exact lt_of_lt_of_le (nadd_increasing1 _ (index_lt x i))
        (le_trans (H z hz (le_refl _)) (add_le_add (le_refl _) (nadd_le2 _ _)))
    | inr p =>
      obtain ⟨j, _⟩ := p
      exact lt_of_le_of_lt (ihy (y j) (index_lt y j) z hz H)
        (add_lt_add_left x (nadd_increasing1 _ (index_lt y j)))
  · intro j
    obtain ⟨q, hq₁, hq₂, hq₃, _⟩ :=
      (has_interpolants_unfold _).1 (Hinterp z hz) ((f z) j) (index_lt (f z) j)
    exact lt_of_le_of_lt (le_trans (nadd_monotone _ _ _ _ (le_refl _) hq₂)
        (ihz q hq₃ hq₁ fun q' hq'₁ hq'₂ => H q' hq'₁ (le_trans hq'₂ (le_of_lt hq₃))))
      (add_lt_add_left x (nadd_increasing2 _ hq₃))

/-- `[a]` denotes `ω ^ f a`. -/
private theorem single_spec {a : A} (ha : P a) :
    P (X.recompose [a]) ∧ ω ^ f a ≈ f (X.recompose [a]) :=
  let h := X.recompose_correct [a] ⟨ha, trivial⟩ ⟨trivial, trivial⟩
  ⟨h.1, equiv_trans (equiv_symm (add_zero _)) h.2⟩

omit X in
/-- `ω ^ b * n < ω ^ a` when `b < a`. -/
private theorem powOmega_mul_ofNat_lt {a b : Ordinal.{0}} (h : b < a) (n : Nat) :
    ω ^ b * ofNat n < ω ^ a :=
  let ⟨j, hj⟩ := lt_elim h
  lt_of_le_of_lt (mul_le_mul_right _ (pow_le_pow_right ω hj))
    (lt_of_lt_of_le (mul_lt_mul_left (pow_pos ω _) (index_lt ω ⟨n⟩))
      (pow_index_mul_omega_le a j))

omit X in
/-- The tail of an ordered list is smaller than the whole list. -/
private theorem tail_lt : ∀ (h : A) (qs : List A), CantorOrdered f (h :: qs) →
    cantorDenote f qs < cantorDenote f (h :: qs)
  | _, [], _ => denote_pos
  | _, q :: qs, hord =>
    lt_of_lt_of_le (add_lt_add_left _ (tail_lt q qs hord.2))
      (add_le_add (pow_le_pow_right ω hord.1) (le_refl _))

section nadd_closed

variable (a : A) (Ha : P a)
  (Hnadd_closed_ind : ∀ a' : A, P a' → f a' ≤ f a → ∀ x y : A, P x → P y →
    f x < ω ^ f a' → f y < ω ^ f a' → f x ♯ f y < ω ^ f a')

include X Hinterp Ha Hnadd_closed_ind in
/-- Rocq: `Notation.CantorDecomposition.nadd_closed_technical1`. -/
theorem nadd_closed_technical1 (n : Nat) : ∀ q r : A, P q → P r → f r < ω ^ f a →
    f q ≤ ω ^ f a * succ (ofNat n) → f r ♯ f q < ω ^ f a + f q := by
  intro q
  refine measure_ind f (motive := fun q => ∀ r : A, P q → P r → f r < ω ^ f a →
    f q ≤ ω ^ f a * succ (ofNat n) → f r ♯ f q < ω ^ f a + f q)
    (fun q ihq r hq₁ hr₁ hr₂ hq₂ => ?_) q
  obtain ⟨ha₁, ha₂⟩ := single_spec X Ha
  -- either `ω ^ a ≤ q` or `q < ω ^ a`
  have H : ω ^ f a ≤ f q ∨ f q < ω ^ f a := by
    have hc := X.compare_correct _ q ha₁ hq₁
    revert hc
    cases X.compare (X.recompose [a]) q with
    | lt => exact fun hc => .inl (le_trans ha₂.le (le_of_lt hc))
    | eq => exact fun hc => .inl (le_trans ha₂.le hc.le)
    | gt => exact fun hc => .inr (lt_of_lt_of_le hc ha₂.ge)
  cases H with
  | inr H =>
    exact lt_of_lt_of_le (Hnadd_closed_ind a Ha (le_refl _) r q hr₁ hq₁ hr₂ H) (le_add_right _ _)
  | inl H =>
    -- write `q = ω ^ a + q'`
    have hq' : ∃ q', P q' ∧ f q' < f q ∧ f q ≈ ω ^ f a + f q' := by
      obtain ⟨hqs₁, hqs₂, hqs₃⟩ := X.decompose_correct q hq₁
      revert hqs₁ hqs₂ hqs₃
      cases X.decompose q with
      | nil =>
        exact fun _ _ hqs₃ =>
          (lt_irrefl _ (lt_of_lt_of_le (pow_pos ω _) (le_trans H hqs₃.le))).elim
      | cons h qs =>
        intro hqs₁ hqs₂ hqs₃
        have hh : f h ≈ f a := by
          have hc := X.compare_correct h a hqs₁.1 Ha
          revert hc
          cases X.compare h a with
          | lt =>
            intro hc
            refine (lt_irrefl (ω ^ f a) (lt_of_le_of_lt (le_trans H hqs₃.le) ?_)).elim
            exact lt_of_le_of_lt (dominates (b := f h) (h :: qs) (le_refl _) hqs₂)
              (powOmega_mul_ofNat_lt hc _)
          | eq => exact id
          | gt =>
            intro hc
            exact (lt_irrefl (f q) (lt_of_le_of_lt hq₂ (lt_of_lt_of_le
              (powOmega_mul_ofNat_lt hc (n + 1)) (le_trans (le_add_right _ _) hqs₃.ge)))).elim
        obtain ⟨hr₁', hr₂'⟩ := X.recompose_correct qs hqs₁.2 hqs₂.2
        exact ⟨X.recompose qs, hr₁',
          lt_of_le_of_lt hr₂'.ge (lt_of_lt_of_le (tail_lt h qs hqs₂) hqs₃.ge),
          equiv_trans hqs₃ (add_congr (pow_congr (equiv_refl ω) hh) hr₂')⟩
    obtain ⟨q', hq'₁, hq'₂, hq'₃⟩ := hq'
    -- `ω ^ a ♯ s ≤ ω ^ a + s` for `s ≤ r`
    have Hs : ∀ s, P s → f s ≤ f r → ω ^ f a ♯ f s ≤ ω ^ f a + f s := by
      intro s
      refine measure_ind f (motive := fun s => P s → f s ≤ f r → ω ^ f a ♯ f s ≤ ω ^ f a + f s)
        (fun s ihs hs₁ hs₂ => nadd_least3 ?_ ?_) s
      · intro i hi
        obtain ⟨z, hz₁, hz₂, hz₃, _⟩ :=
          (has_interpolants_unfold _).1 (Hinterp _ ha₁) i (lt_of_lt_of_le hi ha₂.le)
        exact lt_of_le_of_lt (nadd_monotone _ _ _ _ hz₂ (le_refl _))
          (lt_of_lt_of_le (Hnadd_closed_ind a Ha (le_refl _) z s hz₁ hs₁
            (lt_of_lt_of_le hz₃ ha₂.ge) (lt_of_le_of_lt hs₂ hr₂)) (le_add_right _ _))
      · intro j hj
        obtain ⟨t, ht₁, ht₂, ht₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp s hs₁) j hj
        exact lt_of_le_of_lt (le_trans (nadd_monotone _ _ _ _ (le_refl _) ht₂)
            (ihs t ht₃ ht₁ (le_trans (le_of_lt ht₃) hs₂)))
          (add_lt_add_left _ ht₃)
    calc f r ♯ f q
        ≈ f r ♯ (ω ^ f a + f q') := nadd_congr (equiv_refl _) hq'₃
      _ ≈ (ω ^ f a + f q') ♯ f r := nadd_comm _ _
      _ ≤ ω ^ f a + (f q' ♯ f r) := add_nadd_assoc2' Hinterp _ _ r hr₁ Hs
      _ ≈ ω ^ f a + (f r ♯ f q') := add_congr (equiv_refl _) (nadd_comm _ _)
      _ < ω ^ f a + f q := add_lt_add_left _ (lt_of_lt_of_le
          (ihq q' hq'₂ r hq'₁ hr₁ hr₂ (le_trans (le_of_lt hq'₂) hq₂)) hq'₃.ge)

include X Hinterp Ha Hnadd_closed_ind in
/-- Rocq: `Notation.CantorDecomposition.nadd_closed_technical2`. -/
theorem nadd_closed_technical2 : ∀ (m n : Nat) (q : A), P q → f q ≤ ω ^ f a * succ (ofNat n) →
    ω ^ f a * ofNat m ♯ f q ≤ ω ^ f a * ofNat m + f q := by
  obtain ⟨ha₁, ha₂⟩ := single_spec X Ha
  intro m
  induction m with
  | zero =>
    intro n q
    refine measure_ind f (motive := fun q => P q → f q ≤ ω ^ f a * succ (ofNat n) →
      ω ^ f a * ofNat 0 ♯ f q ≤ ω ^ f a * ofNat 0 + f q)
      (fun q ihq hq₁ hq₂ => nadd_least3 ?_ ?_) q
    · exact fun i hi => (lt_irrefl i (lt_of_lt_of_le hi (le_trans (mul_zero _).le
        (zero_least i)))).elim
    · intro j hj
      obtain ⟨t, ht₁, ht₂, ht₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp q hq₁) j hj
      exact lt_of_le_of_lt (le_trans (nadd_monotone _ _ _ _ (le_refl _) ht₂)
          (ihq t ht₃ ht₁ (le_trans (le_of_lt ht₃) hq₂)))
        (add_lt_add_left _ ht₃)
  | succ m ihm =>
    intro n q
    refine measure_ind f (motive := fun q => P q → f q ≤ ω ^ f a * succ (ofNat n) →
      ω ^ f a * ofNat (m + 1) ♯ f q ≤ ω ^ f a * ofNat (m + 1) + f q)
      (fun q ihq hq₁ hq₂ => nadd_least3 ?_ ?_) q
    · intro i hi
      have hi := lt_of_lt_of_le hi (mul_succ _ _).le
      rw [add_unfold] at hi
      match lub_lt hi with
      | .inl hi =>
        exact lt_of_lt_of_le (nadd_increasing1 _ hi) (le_trans (ihm n q hq₁ hq₂)
          (add_le_add (mul_le_mul_left _ (le_of_lt (succ_lt _))) (le_refl _)))
      | .inr hi =>
        obtain ⟨r, hi⟩ := sup_lt hi
        obtain ⟨_, hi⟩ := lt_elim hi
        obtain ⟨s, hs₁, hs₂, hs₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp _ ha₁)
          ((ω ^ f a) r) (lt_of_lt_of_le (index_lt _ r) ha₂.le)
        calc i ♯ f q
            ≤ (ω ^ f a * ofNat m + f s) ♯ f q :=
              nadd_monotone _ _ _ _ (le_trans hi (add_le_add (le_refl _) hs₂)) (le_refl _)
          _ ≤ ω ^ f a * ofNat m + (f s ♯ f q) :=
              add_nadd_assoc2' Hinterp _ _ q hq₁ fun q' hq'₁ hq'₂ =>
                ihm n q' hq'₁ (le_trans hq'₂ hq₂)
          _ < ω ^ f a * ofNat m + (ω ^ f a + f q) :=
              add_lt_add_left _ (nadd_closed_technical1 X Hinterp a Ha Hnadd_closed_ind n q s
                hq₁ hs₁ (lt_of_lt_of_le hs₃ ha₂.ge) hq₂)
          _ ≈ (ω ^ f a * ofNat m + ω ^ f a) + f q := add_assoc _ _ _
          _ ≈ ω ^ f a * ofNat (m + 1) + f q := add_congr (equiv_symm (mul_succ _ _)) (equiv_refl _)
    · intro j hj
      obtain ⟨t, ht₁, ht₂, ht₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp q hq₁) j hj
      exact lt_of_le_of_lt (le_trans (nadd_monotone _ _ _ _ (le_refl _) ht₂)
          (ihq t ht₃ ht₁ (le_trans (le_of_lt ht₃) hq₂)))
        (add_lt_add_left _ ht₃)


omit X in
/-- `n + 1` copies of `a` denote `ω ^ a * (n + 1)`. -/
private theorem denote_replicate (a : A) : ∀ n : Nat,
    cantorDenote f (List.replicate (n + 1) a) ≈ ω ^ f a * succ (ofNat n)
  | 0 => equiv_trans (add_zero _) (equiv_symm (mul_one _))
  | n + 1 =>
    calc ω ^ f a + cantorDenote f (List.replicate (n + 1) a)
        ≈ ω ^ f a * 1 + ω ^ f a * succ (ofNat n) :=
          add_congr (equiv_symm (mul_one _)) (denote_replicate a n)
      _ ≈ ω ^ f a * (1 + ofNat (n + 1)) := equiv_symm (mul_add _ _ _)
      _ ≈ ω ^ f a * ofNat (n + 1 + 1) := mul_congr (equiv_refl _) (equiv_symm (ofNat_add _ 1))

include X Hinterp Ha Hnadd_closed_ind in
/-- The common step of the two halves of `nadd_add_same_powers_step`. -/
private theorem same_powers_aux (m n : Nat) (x : Ordinal.{0}) (t : A) (ht₁ : P t)
    (ht₂ : f t < ω ^ f a) (hx : x ≤ ω ^ f a * ofNat m + f t) :
    x ♯ ω ^ f a * succ (ofNat n) < ω ^ f a * ofNat (n + 2 + m) := by
  obtain ⟨hR₁, hR₂⟩ := X.recompose_correct (List.replicate (n + 1) a)
    (replicate_each Ha _) (replicate_ordered a _)
  have hR : ω ^ f a * succ (ofNat n) ≈ f (X.recompose (List.replicate (n + 1) a)) :=
    equiv_trans (equiv_symm (denote_replicate a n)) hR₂
  have ht₃ : f t ≤ ω ^ f a * succ (ofNat (n + 1)) :=
    le_trans (le_of_lt ht₂) (le_trans (mul_one _).ge
      (mul_le_mul_left _ (succ_monotone (zero_least _))))
  calc x ♯ ω ^ f a * succ (ofNat n)
      ≤ (ω ^ f a * ofNat m + f t) ♯ f (X.recompose (List.replicate (n + 1) a)) :=
        nadd_monotone _ _ _ _ hx hR.le
    _ ≤ ω ^ f a * ofNat m + (f t ♯ f (X.recompose (List.replicate (n + 1) a))) :=
        add_nadd_assoc2' Hinterp _ _ _ hR₁ fun q hq₁ hq₂ =>
          nadd_closed_technical2 X Hinterp a Ha Hnadd_closed_ind m n q hq₁ (le_trans hq₂ hR.ge)
    _ < ω ^ f a * ofNat m + ω ^ f a * ofNat (n + 2) := by
        refine add_lt_add_left _ ?_
        calc f t ♯ f (X.recompose (List.replicate (n + 1) a))
            ≈ ω ^ f a * ofNat (n + 1) ♯ f t :=
              equiv_trans (nadd_comm _ _) (nadd_congr (equiv_symm hR) (equiv_refl _))
          _ ≤ ω ^ f a * ofNat (n + 1) + f t :=
              nadd_closed_technical2 X Hinterp a Ha Hnadd_closed_ind (n + 1) (n + 1) t ht₁ ht₃
          _ < ω ^ f a * ofNat (n + 1) + ω ^ f a := add_lt_add_left _ ht₂
          _ ≈ ω ^ f a * ofNat (n + 2) := equiv_symm (mul_succ _ _)
    _ ≈ ω ^ f a * ofNat (n + 2 + m) :=
        equiv_trans (equiv_symm (mul_add _ _ _)) (mul_congr (equiv_refl _) (equiv_symm (ofNat_add _ _)))

include X Hinterp Ha in
/-- An element below `ω ^ a * (m + 1)` lies below `ω ^ a * m`, or below
`ω ^ a * m + t` for some well-formed `t < ω ^ a`. -/
private theorem below_mul_succ (m : Nat) (i : Ordinal.{0}) (hi : i < ω ^ f a * succ (ofNat m)) :
    i < ω ^ f a * ofNat m ∨ ∃ t, P t ∧ f t < ω ^ f a ∧ i ≤ ω ^ f a * ofNat m + f t := by
  obtain ⟨ha₁, ha₂⟩ := single_spec X Ha
  have hi := lt_of_lt_of_le hi (mul_succ _ _).le
  rw [add_unfold] at hi
  match lub_lt hi with
  | .inl hi => exact .inl hi
  | .inr hi =>
    obtain ⟨r, hi⟩ := sup_lt hi
    obtain ⟨_, hi⟩ := lt_elim hi
    obtain ⟨t, ht₁, ht₂, ht₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp _ ha₁)
      ((ω ^ f a) r) (lt_of_lt_of_le (index_lt _ r) ha₂.le)
    exact .inr ⟨t, ht₁, lt_of_lt_of_le ht₃ ha₂.ge, le_trans hi (add_le_add (le_refl _) ht₂)⟩

include X Hinterp Ha Hnadd_closed_ind in
/-- Rocq: `Notation.CantorDecomposition.nadd_add_same_powers_step`. -/
theorem nadd_add_same_powers_step : ∀ m n : Nat,
    ω ^ f a * ofNat (m + 1) ♯ ω ^ f a * ofNat (n + 1) ≤ ω ^ f a * ofNat (m + n + 2) := by
  intro m
  induction m with
  | zero =>
    intro n
    induction n with
    | zero =>
      refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
      · match below_mul_succ X Hinterp a Ha 0 i hi with
        | .inl hi =>
          exact (lt_irrefl i (lt_of_lt_of_le hi (le_trans (mul_zero _).le (zero_least i)))).elim
        | .inr ⟨t, ht₁, ht₂, hi⟩ =>
          exact same_powers_aux X Hinterp a Ha Hnadd_closed_ind 0 0 i t ht₁ ht₂ hi
      · match below_mul_succ X Hinterp a Ha 0 j hj with
        | .inl hj =>
          exact (lt_irrefl j (lt_of_lt_of_le hj (le_trans (mul_zero _).le (zero_least j)))).elim
        | .inr ⟨t, ht₁, ht₂, hj⟩ =>
          exact lt_of_le_of_lt (nadd_comm _ _).le
            (same_powers_aux X Hinterp a Ha Hnadd_closed_ind 0 0 j t ht₁ ht₂ hj)
    | succ n ihn =>
      refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
      · match below_mul_succ X Hinterp a Ha 0 i hi with
        | .inl hi =>
          exact (lt_irrefl i (lt_of_lt_of_le hi (le_trans (mul_zero _).le (zero_least i)))).elim
        | .inr ⟨t, ht₁, ht₂, hi⟩ =>
          have e : 0 + (n + 1) + 2 = n + 1 + 2 + 0 := Nat.zero_add _ ▸ rfl
          rw [e]
          exact same_powers_aux X Hinterp a Ha Hnadd_closed_ind 0 (n + 1) i t ht₁ ht₂ hi
      · match below_mul_succ X Hinterp a Ha (n + 1) j hj with
        | .inl hj =>
          exact lt_of_lt_of_le (nadd_increasing2 _ hj) (le_trans ihn
            (mul_le_mul_left _ (ofNat_monotone (Nat.le_succ _))))
        | .inr ⟨t, ht₁, ht₂, hj⟩ =>
          have e : 0 + (n + 1) + 2 = 0 + 2 + (n + 1) := Nat.add_right_comm _ _ _
          rw [e]
          exact lt_of_le_of_lt (nadd_comm _ _).le
            (same_powers_aux X Hinterp a Ha Hnadd_closed_ind (n + 1) 0 j t ht₁ ht₂ hj)
  | succ m ihm =>
    intro n
    induction n with
    | zero =>
      refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
      · match below_mul_succ X Hinterp a Ha (m + 1) i hi with
        | .inl hi =>
          exact lt_of_lt_of_le (nadd_increasing1 _ hi) (le_trans (ihm 0)
            (mul_le_mul_left _ (ofNat_monotone (Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.le_succ m) 0) 2))))
        | .inr ⟨t, ht₁, ht₂, hi⟩ =>
          have e : m + 1 + 0 + 2 = 0 + 2 + (m + 1) :=
            (Nat.add_assoc _ _ _).trans (Nat.add_comm _ _)
          rw [e]
          exact same_powers_aux X Hinterp a Ha Hnadd_closed_ind (m + 1) 0 i t ht₁ ht₂ hi
      · match below_mul_succ X Hinterp a Ha 0 j hj with
        | .inl hj =>
          exact (lt_irrefl j (lt_of_lt_of_le hj (le_trans (mul_zero _).le (zero_least j)))).elim
        | .inr ⟨t, ht₁, ht₂, hj⟩ =>
          have e : m + 1 + 0 + 2 = m + 1 + 2 + 0 := Nat.add_right_comm _ _ _
          rw [e]
          exact lt_of_le_of_lt (nadd_comm _ _).le
            (same_powers_aux X Hinterp a Ha Hnadd_closed_ind 0 (m + 1) j t ht₁ ht₂ hj)
    | succ n ihn =>
      refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
      · match below_mul_succ X Hinterp a Ha (m + 1) i hi with
        | .inl hi =>
          exact lt_of_lt_of_le (nadd_increasing1 _ hi) (le_trans (ihm (n + 1))
            (mul_le_mul_left _ (ofNat_monotone (Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.le_succ m) (n + 1)) 2))))
        | .inr ⟨t, ht₁, ht₂, hi⟩ =>
          have e : m + 1 + (n + 1) + 2 = n + 1 + 2 + (m + 1) :=
            (Nat.add_assoc _ _ _).trans (Nat.add_comm _ _)
          rw [e]
          exact same_powers_aux X Hinterp a Ha Hnadd_closed_ind (m + 1) (n + 1) i t ht₁ ht₂ hi
      · match below_mul_succ X Hinterp a Ha (n + 1) j hj with
        | .inl hj =>
          exact lt_of_lt_of_le (nadd_increasing2 _ hj) (le_trans ihn
            (mul_le_mul_left _ (ofNat_monotone (Nat.le_succ _))))
        | .inr ⟨t, ht₁, ht₂, hj⟩ =>
          have e : m + 1 + (n + 1) + 2 = m + 1 + 2 + (n + 1) := Nat.add_right_comm _ _ _
          rw [e]
          exact lt_of_le_of_lt (nadd_comm _ _).le
            (same_powers_aux X Hinterp a Ha Hnadd_closed_ind (n + 1) (m + 1) j t ht₁ ht₂ hj)

end nadd_closed

include X Hinterp in
/-- Natural sums of terms below `ω ^ a` stay below `ω ^ a`.
Rocq: `Notation.CantorDecomposition.nadd_closed`. -/
theorem nadd_closed : ∀ a : A, P a → ∀ x y : A, P x → P y → f x < ω ^ f a → f y < ω ^ f a →
    f x ♯ f y < ω ^ f a := by
  intro a
  refine measure_ind f (motive := fun a => P a → ∀ x y : A, P x → P y → f x < ω ^ f a →
    f y < ω ^ f a → f x ♯ f y < ω ^ f a) (fun a iha ha x y _ _ hx hy => ?_) a
  have hx' := hx
  have hy' := hy
  rw [pow_unfold] at hx' hy'
  match lub_lt hx' with
  | .inl hx' =>
    obtain ⟨_, hx'⟩ := lt_elim hx'
    exact lt_of_le_of_lt (le_trans (nadd_monotone _ _ _ _ hx' (le_refl _)) (nadd_zero_l _).le) hy
  | .inr hx' =>
    match lub_lt hy' with
    | .inl hy' =>
      obtain ⟨_, hy'⟩ := lt_elim hy'
      exact lt_of_le_of_lt (le_trans (nadd_monotone _ _ _ _ (le_refl _) hy') (nadd_zero_r _).le) hx
    | .inr hy' =>
      obtain ⟨i, hx'⟩ := sup_lt hx'
      obtain ⟨j, hy'⟩ := sup_lt hy'
      obtain ⟨k, hk₁, hk₂⟩ := complete_directed (X.complete a) i j
      rw [mul_unfold] at hx' hy'
      obtain ⟨⟨m⟩, hx'⟩ := sup_lt hx'
      obtain ⟨⟨n⟩, hy'⟩ := sup_lt hy'
      obtain ⟨q, hq₁, hq₂, hq₃, _⟩ :=
        (has_interpolants_unfold _).1 (Hinterp a ha) ((f a) k) (index_lt (f a) k)
      have hW : ∀ c : (f a).Carrier, (f a) c ≤ (f a) k → ∀ p : Nat,
          ω ^ (f a) c * ofNat p + ω ^ (f a) c ≤ ω ^ f q * ofNat (p + 1) := fun c hc p =>
        le_trans (add_le_add (mul_le_mul_right _ (pow_le_pow_right ω (le_trans hc hq₂)))
          (pow_le_pow_right ω (le_trans hc hq₂))) (mul_succ _ _).ge
      calc f x ♯ f y
          < ω ^ f q * ofNat (m + 1) ♯ f y := nadd_increasing1 _ (lt_of_lt_of_le hx' (hW i hk₁ m))
        _ ≤ ω ^ f q * ofNat (m + 1) ♯ ω ^ f q * ofNat (n + 1) :=
            nadd_monotone _ _ _ _ (le_refl _) (le_trans (le_of_lt hy') (hW j hk₂ n))
        _ ≤ ω ^ f q * ofNat (m + n + 2) :=
            nadd_add_same_powers_step X Hinterp q hq₁
              (fun a' ha'₁ ha'₂ => iha a' (lt_of_le_of_lt ha'₂ hq₃) ha'₁) m n
        _ ≤ ω ^ f a := le_of_lt (powOmega_mul_ofNat_lt hq₃ _)

omit X in
/-- Rocq: `Notation.CantorDecomposition.cantor_denote_app`. -/
theorem cantor_denote_app (f : A → Ordinal.{0}) : ∀ xs ys : List A,
    cantorDenote f (xs ++ ys) ≈ cantorDenote f xs + cantorDenote f ys
  | [], _ => equiv_symm (zero_add _)
  | _ :: xs, ys =>
    equiv_trans (add_congr (equiv_refl _) (cantor_denote_app f xs ys)) (add_assoc _ _ _)

include X Hinterp in
/-- Rocq: `Notation.CantorDecomposition.cantor_denote_nadd_add`. -/
theorem cantor_denote_nadd_add : ∀ (xs : List A) (b : A), Each P xs → (∀ a, a ∈ xs → f b ≤ f a) →
    ∀ q, P q → f q ≤ ω ^ f b → cantorDenote f xs ♯ f q ≤ cantorDenote f xs + f q := by
  intro xs
  induction xs using List.rev_ind with
  | hnil => exact fun _ _ _ q _ _ => le_trans (nadd_zero_l _).le (zero_add (f q)).ge
  | hsnoc x xs ih =>
    intro b hP hb q hq₁ hq₂
    obtain ⟨hPxs, hPx, _⟩ := (each_app P xs [x]).1 hP
    obtain ⟨hx₁, hx₂⟩ := single_spec X hPx
    have hbx : f b ≤ f x := hb x (List.mem_append_right xs (List.Mem.head []))
    -- `ω ^ x ♯ q ≤ ω ^ x + q`
    have inner : ∀ q, P q → f q ≤ ω ^ f b → ω ^ f x ♯ f q ≤ ω ^ f x + f q := by
      intro q
      refine measure_ind f (motive := fun q => P q → f q ≤ ω ^ f b →
        ω ^ f x ♯ f q ≤ ω ^ f x + f q) (fun q ihq hq₁ hq₂ => nadd_least3 ?_ ?_) q
      · intro i hi
        obtain ⟨z, hz₁, hz₂, hz₃, _⟩ :=
          (has_interpolants_unfold _).1 (Hinterp _ hx₁) i (lt_of_lt_of_le hi hx₂.le)
        exact lt_of_le_of_lt (nadd_monotone _ _ _ _ hz₂ (le_refl _))
          (nadd_closed_technical1 X Hinterp x hPx
            (fun a' ha' _ => nadd_closed X Hinterp a' ha') 0 q z hq₁ hz₁
            (lt_of_lt_of_le hz₃ hx₂.ge)
            (le_trans hq₂ (le_trans (pow_le_pow_right ω hbx) (mul_one _).ge)))
      · intro j hj
        obtain ⟨y, hy₁, hy₂, hy₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp q hq₁) j hj
        exact lt_of_le_of_lt (le_trans (nadd_monotone _ _ _ _ (le_refl _) hy₂)
            (ihq y hy₃ hy₁ (le_trans (le_of_lt hy₃) hq₂)))
          (add_lt_add_left _ hy₃)
    have happ : cantorDenote f (xs ++ [x]) ≈ cantorDenote f xs + ω ^ f x :=
      equiv_trans (cantor_denote_app f xs [x]) (add_congr (equiv_refl _) (add_zero _))
    calc cantorDenote f (xs ++ [x]) ♯ f q
        ≈ (cantorDenote f xs + ω ^ f x) ♯ f q := nadd_congr happ (equiv_refl _)
      _ ≤ cantorDenote f xs + (ω ^ f x ♯ f q) :=
          add_nadd_assoc2' Hinterp _ _ q hq₁ fun q' hq'₁ hq'₂ =>
            ih b hPxs (fun a ha => hb a (List.mem_append_left [x] ha)) q' hq'₁ (le_trans hq'₂ hq₂)
      _ ≤ cantorDenote f xs + (ω ^ f x + f q) := add_le_add (le_refl _) (inner q hq₁ hq₂)
      _ ≈ (cantorDenote f xs + ω ^ f x) + f q := add_assoc _ _ _
      _ ≈ cantorDenote f (xs ++ [x]) + f q := add_congr (equiv_symm happ) (equiv_refl _)

/-- `ω ^ f x₁ ♯ ω ^ f x₂ ♯ ⋯`, the natural-sum analogue of `cantorDenote`.
Rocq: `Notation.CantorDecomposition.cantor_denote_nadd`. -/
def cantorDenoteNadd (f : A → Ordinal.{0}) : List A → Ordinal.{0}
  | [] => 0
  | x :: xs => ω ^ f x ♯ cantorDenoteNadd f xs

omit X in
/-- Rocq: `Notation.CantorDecomposition.cantor_denote_nadd_app`. -/
theorem cantor_denote_nadd_app (f : A → Ordinal.{0}) : ∀ xs ys : List A,
    cantorDenoteNadd f (xs ++ ys) ≈ cantorDenoteNadd f xs ♯ cantorDenoteNadd f ys
  | [], _ => equiv_symm (nadd_zero_l _)
  | _ :: xs, ys =>
    equiv_trans (nadd_congr (equiv_refl _) (cantor_denote_nadd_app f xs ys)) (nadd_assoc _ _ _)

omit X in
private theorem ordered_append_left : ∀ xs ys : List A, CantorOrdered f (xs ++ ys) →
    CantorOrdered f xs
  | [], _, _ => trivial
  | [_], _, _ => ⟨trivial, trivial⟩
  | _ :: b :: xs, ys, h => ⟨h.1, ordered_append_left (b :: xs) ys h.2⟩

omit X in
private theorem ordered_mem_le : ∀ (l : List A) (a : A), CantorOrdered f (a :: l) →
    ∀ c, c ∈ l → f c ≤ f a
  | [], _, _, _, h => nomatch h
  | b :: l, _, h, c, hc => by
    cases hc with
    | head => exact h.1
    | tail _ hc => exact le_trans (ordered_mem_le l b h.2 c hc) h.1

omit X in
private theorem ordered_last_le (x : A) : ∀ xs : List A, CantorOrdered f (xs ++ [x]) →
    ∀ a, a ∈ xs → f x ≤ f a
  | [], _, _, h => nomatch h
  | c :: xs, h, a, ha => by
    cases ha with
    | head => exact ordered_mem_le (xs ++ [x]) c h x (List.mem_append_right xs (List.Mem.head []))
    | tail _ ha => exact ordered_last_le x xs h.2 a ha

include X Hinterp in
/-- For an ordered list, the ordinary and the natural sum of its terms agree.
Rocq: `Notation.CantorDecomposition.cantor_denote_nadd_eq`. -/
theorem cantor_denote_nadd_eq : ∀ xs : List A, Each P xs → CantorOrdered f xs →
    cantorDenote f xs ≈ cantorDenoteNadd f xs := by
  intro xs
  induction xs using List.rev_ind with
  | hnil => exact fun _ _ => equiv_refl _
  | hsnoc x xs ih =>
    intro hP hord
    obtain ⟨hPxs, hPx, _⟩ := (each_app P xs [x]).1 hP
    obtain ⟨hx₁, hx₂⟩ := single_spec X hPx
    have ih := ih hPxs (ordered_append_left xs [x] hord)
    refine equiv_trans (cantor_denote_app f xs [x]) (equiv_trans ?_
      (equiv_symm (cantor_denote_nadd_app f xs [x])))
    refine equiv_trans (add_congr ih (add_zero _)) (equiv_trans ?_
      (nadd_congr (equiv_refl _) (equiv_symm (nadd_zero_r _))))
    refine equiv_intro (add_nadd_le _ _) ?_
    calc cantorDenoteNadd f xs ♯ ω ^ f x
        ≈ cantorDenote f xs ♯ f (X.recompose [x]) := nadd_congr (equiv_symm ih) hx₂
      _ ≤ cantorDenote f xs + f (X.recompose [x]) :=
          cantor_denote_nadd_add X Hinterp xs x hPxs (ordered_last_le x xs hord) _ hx₁ hx₂.ge
      _ ≈ cantorDenoteNadd f xs + ω ^ f x := add_congr ih (equiv_symm hx₂)

/-- The inner `fix` of Rocq's `cantor_nadd_list`, on the second list, for a
first list `x :: xs'`; `rec` is the outer recursive call on `xs'`. -/
def cantorNaddInner (x : A) (xs' : List A) (rec : List A → List A) : List A → List A
  | [] => x :: xs'
  | y :: ys' =>
    match X.compare x y with
    | .lt => y :: cantorNaddInner x xs' rec ys'
    | .eq => x :: rec (y :: ys')
    | .gt => x :: rec (y :: ys')

/-- Merge two ordered lists of exponents.
Rocq: `Notation.CantorDecomposition.cantor_nadd_list`. -/
def cantorNaddList : List A → List A → List A
  | [], ys => ys
  | x :: xs', ys => cantorNaddInner X x xs' (cantorNaddList xs') ys

/-- What `cantor_nadd_list_correct` proves, plus a bound on the head of the
result used in the induction. -/
private abbrev NaddSpec (xs ys r : List A) : Prop :=
  Each P r ∧ CantorOrdered f r ∧
    cantorDenoteNadd f r ≈ cantorDenoteNadd f xs ♯ cantorDenoteNadd f ys ∧
    ∀ b, HeadLe f b xs → HeadLe f b ys → HeadLe f b r

private theorem naddInner_spec (x : A) (xs' : List A)
    (ih : ∀ ys, Each P xs' → Each P ys → CantorOrdered f xs' → CantorOrdered f ys →
      NaddSpec (f := f) (P := P) xs' ys (cantorNaddList X xs' ys)) :
    ∀ ys, Each P (x :: xs') → Each P ys → CantorOrdered f (x :: xs') → CantorOrdered f ys →
      NaddSpec (f := f) (P := P) (x :: xs') ys (cantorNaddInner X x xs' (cantorNaddList X xs') ys)
  | [], hPx, _, hx, _ => ⟨hPx, hx, equiv_symm (nadd_zero_r _), fun _ hb _ => hb⟩
  | y :: ys', hPx, hPy, hx, hy => by
    have hc := X.compare_correct x y hPx.1 hPy.1
    show NaddSpec (f := f) (P := P) (x :: xs') (y :: ys') (match X.compare x y with
      | .lt => y :: cantorNaddInner X x xs' (cantorNaddList X xs') ys'
      | .eq => x :: cantorNaddList X xs' (y :: ys')
      | .gt => x :: cantorNaddList X xs' (y :: ys'))
    have hle : ∀ (h : f y ≤ f x), NaddSpec (f := f) (P := P) (x :: xs') (y :: ys')
        (x :: cantorNaddList X xs' (y :: ys')) := fun h =>
      let ⟨e, o, d, hd⟩ := ih (y :: ys') hPx.2 hPy hx.2 hy
      ⟨⟨hPx.1, e⟩, ⟨hd (f x) hx.1 h, o⟩,
        equiv_trans (nadd_congr (equiv_refl _) d) (nadd_assoc _ _ _), fun _ hb _ => hb⟩
    revert hc
    cases X.compare x y with
    | lt =>
      intro hc
      obtain ⟨e, o, d, hd⟩ := naddInner_spec x xs' ih ys' hPx hPy.2 hx hy.2
      refine ⟨⟨hPy.1, e⟩, ⟨hd (f y) (le_of_lt hc) hy.1, o⟩, ?_, fun _ _ hb => hb⟩
      calc ω ^ f y ♯ cantorDenoteNadd f (cantorNaddInner X x xs' (cantorNaddList X xs') ys')
          ≈ ω ^ f y ♯ (cantorDenoteNadd f (x :: xs') ♯ cantorDenoteNadd f ys') :=
            nadd_congr (equiv_refl _) d
        _ ≈ (ω ^ f y ♯ cantorDenoteNadd f (x :: xs')) ♯ cantorDenoteNadd f ys' := nadd_assoc _ _ _
        _ ≈ (cantorDenoteNadd f (x :: xs') ♯ ω ^ f y) ♯ cantorDenoteNadd f ys' :=
            nadd_congr (nadd_comm _ _) (equiv_refl _)
        _ ≈ cantorDenoteNadd f (x :: xs') ♯ (ω ^ f y ♯ cantorDenoteNadd f ys') :=
            equiv_symm (nadd_assoc _ _ _)
    | eq => exact fun hc => hle hc.ge
    | gt => exact fun hc => hle (le_of_lt hc)

private theorem nadd_spec : ∀ xs ys : List A, Each P xs → Each P ys → CantorOrdered f xs →
    CantorOrdered f ys → NaddSpec (f := f) (P := P) xs ys (cantorNaddList X xs ys)
  | [], _, _, hPy, _, hy => ⟨hPy, hy, equiv_symm (nadd_zero_l _), fun _ _ hb => hb⟩
  | x :: xs', ys, hPx, hPy, hx, hy =>
    naddInner_spec X x xs' (fun ys => nadd_spec xs' ys) ys hPx hPy hx hy

/-- Rocq: `Notation.CantorDecomposition.cantor_nadd_list_correct`. -/
theorem cantor_nadd_list_correct (xs ys : List A) (hPx : Each P xs) (hPy : Each P ys)
    (hx : CantorOrdered f xs) (hy : CantorOrdered f ys) :
    Each P (cantorNaddList X xs ys) ∧ CantorOrdered f (cantorNaddList X xs ys) ∧
      cantorDenoteNadd f (cantorNaddList X xs ys) ≈
        cantorDenoteNadd f xs ♯ cantorDenoteNadd f ys :=
  let ⟨e, o, d, _⟩ := nadd_spec X xs ys hPx hPy hx hy
  ⟨e, o, d⟩

/-- Rocq: `Notation.CantorDecomposition.cantor_nadd`. -/
def cantorNadd (x y : A) : A :=
  X.recompose (cantorNaddList X (X.decompose x) (X.decompose y))

include Hinterp in
/-- Rocq: `Notation.CantorDecomposition.cantor_nadd_correct`. -/
theorem cantor_nadd_correct (x y : A) (hx : P x) (hy : P y) :
    P (cantorNadd X x y) ∧ f (cantorNadd X x y) ≈ f x ♯ f y := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := X.decompose_correct x hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := X.decompose_correct y hy
  obtain ⟨h₁, h₂, h₃⟩ := cantor_nadd_list_correct X _ _ hx₁ hy₁ hx₂ hy₂
  obtain ⟨h₄, h₅⟩ := X.recompose_correct _ h₁ h₂
  refine ⟨h₄, equiv_trans (equiv_symm h₅) (equiv_trans
    (cantor_denote_nadd_eq X Hinterp _ h₁ h₂) (equiv_trans h₃ ?_))⟩
  exact nadd_congr
    (equiv_trans (equiv_symm (cantor_denote_nadd_eq X Hinterp _ hx₁ hx₂)) (equiv_symm hx₃))
    (equiv_trans (equiv_symm (cantor_denote_nadd_eq X Hinterp _ hy₁ hy₂)) (equiv_symm hy₃))

include Hinterp in
/-- With all interpolants, a notation system with a Cantor decomposition
computes natural sums. Rocq: `Notation.CantorDecomposition.cantor_nadd_reflects`. -/
theorem cantor_nadd_reflects : Reflects A f P (.ord ==> .ord ==> .ord) (· ♯ ·) (cantorNadd X) := by
  intro x a ⟨hxa, ha⟩ y b ⟨hyb, hb⟩
  obtain ⟨h₁, h₂⟩ := cantor_nadd_correct X Hinterp a b ha hb
  exact ⟨equiv_trans (nadd_congr hxa hyb) (equiv_symm h₂), h₁⟩

end reflects_nadd

end cantor_arithmetic

end ConstructiveOrdinals.CantorDecomposition
