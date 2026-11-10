import ConstructiveOrdinals.Cantor
import ConstructiveOrdinals.Reflection
import ConstructiveOrdinals.NaturalArith
import ConstructiveOrdinals.Veblen.Constructive
import ConstructiveOrdinals.Classical
import ConstructiveOrdinals.Notation.Interpolants
import ConstructiveOrdinals.Prelude.List

/-!
# Cantor arithmetic for notation systems with Cantor decompositions

Port of `Ordinal/Notation/CantorDecomposition.v`.

A notation system `A` (with denotation `f` and well-formedness predicate `P`)
*has a Cantor decomposition* when it can compare its terms and convert each
term to and from the list of exponents of its Cantor normal form. Every such
system supports zero, successor, addition, multiplication and
exponentiation, computed on Cantor normal forms.

It also computes the natural (Hessenberg) sum by merging Cantor normal forms;
the comparison of terms decides each step, so this needs neither interpolants
(`Notation/Interpolants.lean`) nor the excluded middle. With the excluded
middle, having all interpolants is equivalent to having a notation for every
ordinal below each term (`has_all_interpolants_EM_iff_has_enough_notations`).

Lean notes:

- Rocq's `Section cantor_arithmetic` variables `A f P X` become explicit
  arguments; `f` and `P` are implicit when `X` determines them, as with Rocq's
  `Implicit Arguments`. Each declaration takes exactly the section variables
  that Rocq's `Check` reports.
- The inner `match` of Rocq's `cantor_ordered` is the predicate `HeadLe`.
-/

namespace ConstructiveOrdinals.CantorDecomposition

open Ordinal Interpolants

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
            denote_pos
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


/-! ## Interpolants and the excluded middle -/

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

include X in
/-- With the excluded middle, having all interpolants is the same as having
enough notations.
Rocq: `Notation.CantorDecomposition.has_all_interpolants_EM_iff_has_enough_notations`. -/
theorem has_all_interpolants_EM_iff_has_enough_notations :
    (HasAllInterpolants f P ∧ ExcludedMiddle) ↔ HasEnoughNotations f P :=
  ⟨fun ⟨h, em⟩ => has_interpolants_has_enough_notations em h,
    fun h => ⟨has_enough_notations_has_all_interpolants h, has_enough_notations_EM X h⟩⟩

/-! ## Reflecting the natural sum

Natural sums of notations are computed by merging Cantor normal forms. The
comparison of notations decides each step of a normal form, which is all that
`Ordinal.cantor_denote_nadd_eq_dec` needs, so the reflection requires neither
interpolants nor the excluded middle. -/

section reflects_nadd_con

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
/-- Rocq: `Notation.CantorDecomposition.cantor_denote_map`. -/
theorem cantor_denote_map (f : A → Ordinal.{0}) : ∀ xs : List A,
    cantorDenote f xs = Ordinal.cantorDenote (xs.map f)
  | [] => rfl
  | x :: xs => congrArg (ω ^ f x + ·) (cantor_denote_map f xs)

omit X in
/-- Rocq: `Notation.CantorDecomposition.cantor_denote_nadd_map`. -/
theorem cantor_denote_nadd_map (f : A → Ordinal.{0}) : ∀ xs : List A,
    cantorDenoteNadd f xs = Ordinal.cantorDenoteNadd (xs.map f)
  | [] => rfl
  | x :: xs => congrArg (ω ^ f x ♯ ·) (cantor_denote_nadd_map f xs)

include X in
/-- Rocq: `Notation.CantorDecomposition.each_complete_map`. -/
theorem each_complete_map : ∀ xs : List A, Each Complete (xs.map f)
  | [] => trivial
  | x :: xs => ⟨X.complete x, each_complete_map xs⟩

include X in
/-- The comparison of notations decides each step of the sequence.
Rocq: `Notation.CantorDecomposition.cantor_ordered_dec`. -/
theorem cantor_ordered_dec : ∀ (xs : List A) (x : A), Each P (x :: xs) →
    CantorOrdered f (x :: xs) → CantorSequenceDec (f x) (xs.map f)
  | [], _, _, _ => trivial
  | y :: ys, x, ⟨hx, hy, hys⟩, ⟨hxy, hord⟩ => by
    refine ⟨?_, cantor_ordered_dec ys y ⟨hy, hys⟩ hord⟩
    have hc := X.compare_correct y x hy hx
    revert hc
    cases X.compare y x with
    | lt => exact fun hc => .inl hc
    | eq => exact fun hc => .inr hc
    | gt => exact fun hc => (lt_irrefl (f x) (lt_of_lt_of_le hc hxy)).elim

include X in
/-- For an ordered list, the ordinary and the natural sum of its terms agree.
Rocq: `Notation.CantorDecomposition.cantor_denote_nadd_eq`. -/
theorem cantor_denote_nadd_eq : ∀ xs : List A, Each P xs → CantorOrdered f xs →
    cantorDenote f xs ≈ cantorDenoteNadd f xs
  | [], _, _ => equiv_refl _
  | x :: xs, hP, hord => by
    rw [cantor_denote_map, cantor_denote_nadd_map]
    exact Ordinal.cantor_denote_nadd_eq_dec ((x :: xs).map f) (f x) (each_complete_map X _)
      ⟨.inr (equiv_refl _), cantor_ordered_dec X xs x hP hord⟩

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

/-- Rocq: `Notation.CantorDecomposition.cantor_nadd_correct`. -/
theorem cantor_nadd_correct (x y : A) (hx : P x) (hy : P y) :
    P (cantorNadd X x y) ∧ f (cantorNadd X x y) ≈ f x ♯ f y := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := X.decompose_correct x hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := X.decompose_correct y hy
  obtain ⟨h₁, h₂, h₃⟩ := cantor_nadd_list_correct X _ _ hx₁ hy₁ hx₂ hy₂
  obtain ⟨h₄, h₅⟩ := X.recompose_correct _ h₁ h₂
  refine ⟨h₄, equiv_trans (equiv_symm h₅) (equiv_trans
    (cantor_denote_nadd_eq X _ h₁ h₂) (equiv_trans h₃ ?_))⟩
  exact nadd_congr
    (equiv_trans (equiv_symm (cantor_denote_nadd_eq X _ hx₁ hx₂)) (equiv_symm hx₃))
    (equiv_trans (equiv_symm (cantor_denote_nadd_eq X _ hy₁ hy₂)) (equiv_symm hy₃))

/-- A notation system with a Cantor decomposition computes natural sums. Rocq: `Notation.CantorDecomposition.cantor_nadd_reflects`. -/
theorem cantor_nadd_reflects : Reflects A f P (.ord ==> .ord ==> .ord) (· ♯ ·) (cantorNadd X) := by
  intro x a ⟨hxa, ha⟩ y b ⟨hyb, hb⟩
  obtain ⟨h₁, h₂⟩ := cantor_nadd_correct X a b ha hb
  exact ⟨equiv_trans (nadd_congr hxa hyb) (equiv_symm h₂), h₁⟩

end reflects_nadd_con

end cantor_arithmetic

/-! ## Transfer along a bijection of normal forms

A Cantor decomposition transfers to any notation system whose normal forms
correspond to the original ones, preserving denotations. -/

section cantor_transfer

variable {B : Type}

/-- Rocq: `Notation.CantorDecomposition.transfer_each`. -/
theorem transfer_each {P : A → Prop} {Q : B → Prop} (h : A → B) (H : ∀ a, P a → Q (h a)) :
    ∀ xs : List A, Each P xs → Each Q (xs.map h)
  | [], _ => trivial
  | x :: xs, ⟨hx, hxs⟩ => ⟨H x hx, transfer_each h H xs hxs⟩

/-- Rocq: `Notation.CantorDecomposition.transfer_cantor_denote`. -/
theorem transfer_cantor_denote {f : A → Ordinal.{0}} {g : B → Ordinal.{0}} {P : A → Prop}
    (h : A → B) (H : ∀ a, P a → g (h a) ≈ f a) :
    ∀ xs : List A, Each P xs → cantorDenote g (xs.map h) ≈ cantorDenote f xs
  | [], _ => equiv_refl _
  | x :: xs, ⟨hx, hxs⟩ =>
    add_congr (pow_congr (equiv_refl _) (H x hx)) (transfer_cantor_denote h H xs hxs)

/-- Rocq: `Notation.CantorDecomposition.transfer_cantor_ordered`. -/
theorem transfer_cantor_ordered {f : A → Ordinal.{0}} {g : B → Ordinal.{0}} {P : A → Prop}
    (h : A → B) (H : ∀ a, P a → g (h a) ≈ f a) :
    ∀ xs : List A, Each P xs → CantorOrdered f xs → CantorOrdered g (xs.map h)
  | [], _, _ => trivial
  | [_], _, _ => ⟨trivial, trivial⟩
  | x :: y :: ys, ⟨hx, hy, hys⟩, ⟨hxy, hrest⟩ =>
    ⟨le_trans (H y hy).le (le_trans hxy (H x hx).ge),
      transfer_cantor_ordered h H (y :: ys) ⟨hy, hys⟩ hrest⟩

/-- The transferred Cantor decomposition. Rocq's section variables `to` and
`from` are `to` and `back` here (`from` is a Lean keyword).
Rocq: `Notation.CantorDecomposition.cantor_transfer`. -/
def cantorTransfer {f : A → Ordinal.{0}} {g : B → Ordinal.{0}} {P : A → Prop} {Q : B → Prop}
    (to : A → B) (back : B → A) (hto : ∀ a, P a → Q (to a) ∧ g (to a) ≈ f a)
    (hfrom : ∀ b, Q b → P (back b) ∧ f (back b) ≈ g b) (hg : ∀ b, Complete (g b))
    (X : HasCantorDecomposition f P) : HasCantorDecomposition g Q where
  compare x y := X.compare (back x) (back y)
  decompose x := (X.decompose (back x)).map to
  recompose xs := to (X.recompose (xs.map back))
  complete := hg
  compare_correct x y hx hy :=
    OrderingCorrect.congr (hfrom x hx).2 (hfrom y hy).2
      (X.compare_correct _ _ (hfrom x hx).1 (hfrom y hy).1)
  decompose_correct x hx :=
    let ⟨px, ex⟩ := hfrom x hx
    let ⟨h1, h2, h3⟩ := X.decompose_correct _ px
    ⟨transfer_each to (fun a ha => (hto a ha).1) _ h1,
      transfer_cantor_ordered to (fun a ha => (hto a ha).2) _ h1 h2,
      equiv_trans (equiv_symm ex)
        (equiv_trans h3 (equiv_symm (transfer_cantor_denote to (fun a ha => (hto a ha).2) _ h1)))⟩
  recompose_correct xs hxs hord :=
    let HP := transfer_each back (fun b hb => (hfrom b hb).1) xs hxs
    let HO := transfer_cantor_ordered back (fun b hb => (hfrom b hb).2) xs hxs hord
    let ⟨h1, h2⟩ := X.recompose_correct _ HP HO
    let ⟨h3, h4⟩ := hto _ h1
    ⟨h3, equiv_trans (equiv_symm (transfer_cantor_denote back (fun b hb => (hfrom b hb).2) xs hxs))
      (equiv_trans h2 (equiv_symm h4))⟩

end cantor_transfer

end ConstructiveOrdinals.CantorDecomposition
