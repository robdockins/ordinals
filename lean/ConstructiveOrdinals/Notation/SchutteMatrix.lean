import ConstructiveOrdinals.Notation.CantorDecomposition
import ConstructiveOrdinals.Schutte.ColumnFacts
import ConstructiveOrdinals.Prelude.Relations

/-!
# Schütte matrices: a notation system for the large Veblen ordinal

Port of `Ordinal/Notation/SchutteMatrix.v`.

A form `N [(b₁, a₁), …, (bₙ, aₙ)]` denotes the Schütte matrix
`schutteMatrix (1 + ·) [(b₁, a₁), …, (bₙ, aₙ)] 0`: column indices are
themselves forms. A form is *proper* when the column indices strictly
decrease, and *normal* when moreover it is sparse (no zero arguments) and
each argument is smaller than the whole term. Normal forms denote exactly
the ordinals below the large Veblen ordinal. Comparison runs the matrix
comparison of `Schutte/ColumnFacts`, and is correct on proper forms.
Normalization is a strongly normalizing rewriting system on proper forms, and
the system has a Cantor decomposition, all interpolants, and (with the
excluded middle) a unique notation for every ordinal below the large Veblen
ordinal.

Lean notes:

- As in `Notation/SchutteStack`, Rocq's well-founded, dependently typed
  comparison (`check_lt`, `matrix_compare`, `VF_compare_loop`) becomes plain
  functions over explicit fuel (`checkLt`, `matrixCompare`, `compareFuel`)
  with separate correctness lemmas.
- Maps over the matrix entries are the mutually recursive `matrixDenote`,
  `MatrixProper`, `IsNormalList` and `normalizeMatrix`.
- `∃!` is spelled out as existence plus uniqueness.
-/

namespace ConstructiveOrdinals.SchutteMatrixNotation

open Ordinal

universe u

/-- Forms. Rocq: `Notation.SchutteMatrix.VForm`. -/
inductive VForm : Type where
  | Z : VForm
  | N : List (VForm × VForm) → VForm

namespace VForm

mutual
/-- Rocq: `Notation.SchutteMatrix.VF_termSize`. -/
def termSize : VForm → Nat
  | Z => 0
  | N l => matrixSize l + 1

/-- Rocq: `Notation.SchutteMatrix.VF_matrixSize`. -/
def matrixSize : List (VForm × VForm) → Nat
  | [] => 0
  | (b, a) :: xs => termSize b + termSize a + matrixSize xs + 1
end

mutual
/-- Rocq: `Notation.SchutteMatrix.VF_denote`. -/
def denote : VForm → Ordinal.{0}
  | Z => 0
  | N l => schutteMatrix (fun y => 1 + y) (matrixDenote l) 0

/-- Rocq: `Notation.SchutteMatrix.matrix_denote`. -/
def matrixDenote : List (VForm × VForm) → List (Ordinal.{0} × Ordinal.{0})
  | [] => []
  | (b, a) :: xs => (denote b, denote a) :: matrixDenote xs
end

instance : Sized VForm := ⟨denote⟩

mutual
private theorem induction_aux (P : VForm → Prop) (hZ : P Z)
    (hN : ∀ xs, Each (fun x => P x.1 ∧ P x.2) xs → P (N xs)) : ∀ x, P x
  | Z => hZ
  | N xs => hN xs (induction_list P hZ hN xs)

private theorem induction_list (P : VForm → Prop) (hZ : P Z)
    (hN : ∀ xs, Each (fun x => P x.1 ∧ P x.2) xs → P (N xs)) :
    ∀ xs : List (VForm × VForm), Each (fun x => P x.1 ∧ P x.2) xs
  | [] => trivial
  | (b, a) :: xs => ⟨⟨induction_aux P hZ hN b, induction_aux P hZ hN a⟩, induction_list P hZ hN xs⟩
end

/-- Rocq: `Notation.SchutteMatrix.VForm_induction`. -/
theorem induction' (P : VForm → Prop) (hZ : P Z)
    (hN : ∀ xs, Each (fun x => P x.1 ∧ P x.2) xs → P (N xs)) : ∀ x, P x :=
  induction_aux P hZ hN

theorem each_matrixDenote (P : Ordinal.{0} × Ordinal.{0} → Prop) :
    ∀ xs : List (VForm × VForm), Each P (matrixDenote xs) ↔ Each (fun x => P (denote x.1, denote x.2)) xs
  | [] => Iff.rfl
  | (_, _) :: xs => ⟨fun h => ⟨h.1, (each_matrixDenote P xs).1 h.2⟩,
      fun h => ⟨h.1, (each_matrixDenote P xs).2 h.2⟩⟩

mutual
/-- Rocq: `Notation.SchutteMatrix.VForm_complete`. -/
theorem complete : ∀ x : VForm, Complete (denote x)
  | Z => zero_complete
  | N l => (schutte_matrix_normal _ _ (all_complete l) onePlus_normal).complete 0 zero_complete

/-- Rocq: `Notation.SchutteMatrix.VForm_all_complete`. -/
theorem all_complete : ∀ xs : List (VForm × VForm), AllComplete (matrixDenote xs)
  | [] => trivial
  | (b, a) :: xs => ⟨complete b, complete a, all_complete xs⟩
end

/-- Rocq: `Notation.SchutteMatrix.VForm_each_complete`. -/
theorem each_complete : ∀ xs : List (VForm × VForm),
    Each (fun x => Complete (denote x.1) ∧ Complete (denote x.2)) xs
  | [] => trivial
  | (b, a) :: xs => ⟨⟨complete b, complete a⟩, each_complete xs⟩

/-- The matrix function of a form's list is normal. -/
theorem matrix_normal (l : List (VForm × VForm)) {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f) :
    NormalFunction (schutteMatrix f (matrixDenote l)) :=
  schutte_matrix_normal _ _ (all_complete l) hf

/-- Rocq: `Notation.SchutteMatrix.VF_matrixSize_app`. -/
theorem matrixSize_app : ∀ xs ys : List (VForm × VForm),
    matrixSize (xs ++ ys) = matrixSize xs + matrixSize ys
  | [], ys => (Nat.zero_add _).symm
  | (b, a) :: xs, ys => by
    show termSize b + termSize a + matrixSize (xs ++ ys) + 1 =
      termSize b + termSize a + matrixSize xs + 1 + matrixSize ys
    rw [matrixSize_app xs ys, Nat.add_right_comm (termSize b + termSize a + matrixSize xs) 1,
      ← Nat.add_assoc (termSize b + termSize a)]

/-- Every entry of a matrix is smaller than the form built from it. -/
theorem each_lt_termSize : ∀ l : List (VForm × VForm),
    Each (fun x => termSize x.1 < termSize (N l) ∧ termSize x.2 < termSize (N l)) l
  | [] => trivial
  | (b, a) :: xs =>
    have hle : termSize (N xs) ≤ termSize (N ((b, a) :: xs)) :=
      Nat.succ_le_succ (Nat.le_succ_of_le (Nat.le_add_left _ _))
    ⟨⟨Nat.lt_succ_of_le (Nat.le_succ_of_le (Nat.le_trans (Nat.le_add_right _ (termSize a))
        (Nat.le_add_right _ _))),
      Nat.lt_succ_of_le (Nat.le_succ_of_le (Nat.le_trans (Nat.le_add_left _ (termSize b))
        (Nat.le_add_right _ _)))⟩,
      (each_lt_termSize xs).imp fun _ h => ⟨Nat.lt_of_lt_of_le h.1 hle, Nat.lt_of_lt_of_le h.2 hle⟩⟩

mutual
/-- Column indices strictly decrease, recursively.
Rocq: `Notation.SchutteMatrix.VF_proper`. -/
def IsProper : VForm → Prop
  | Z => True
  | N l => MatrixProper l

/-- Rocq: `Notation.SchutteMatrix.VF_matrix_proper`. -/
def MatrixProper : List (VForm × VForm) → Prop
  | [] => True
  | (b₁, a₁) :: xs => IsProper b₁ ∧ IsProper a₁ ∧
    match xs with
    | [] => True
    | (b₂, _) :: _ => denote b₂ < denote b₁ ∧ MatrixProper xs
end

/-- Rocq: `Notation.SchutteMatrix.VF_proper_eq`. -/
theorem proper_eq (x : VForm) :
    IsProper x = match x with
      | Z => True
      | N l => MatrixProper l := by
  cases x <;> rfl

theorem MatrixProper.tail : ∀ {p : VForm × VForm} {xs : List (VForm × VForm)},
    MatrixProper (p :: xs) → MatrixProper xs
  | _, [], _ => trivial
  | _, _ :: _, h => h.2.2.2

/-- Rocq: `Notation.SchutteMatrix.VForm_bounded`. -/
theorem bounded : ∀ x : VForm, denote x < LargeVeblenOrdinal :=
  induction' _ LVO_nonzero fun xs ih =>
    matrix_E_unreachable _ _ 0 _ onePlus_normal LVO_complete zero_complete (all_complete xs)
      ((each_matrixDenote _ xs).2 ih) LVO_nonzero
      (le_trans (schutte_column_monotoneβ _ _ 1 0 _ onePlus_normal.monotone LVO_alt.le)
        (le_trans (normal_fixpoint (schutte_column_normalβ _ onePlus_normal) 0 zero_complete).ge
          LVO_alt.ge))

end VForm

/-- The ordinal of all forms. Rocq: `Notation.SchutteMatrix.VF`. -/
def VF : Ordinal.{0} := mk VForm VForm.denote

namespace VForm

/-- Rocq: `Notation.SchutteMatrix.LVO_proper_VForm`. -/
theorem LVO_proper_VForm (x : Ordinal.{0}) (hx : x < LargeVeblenOrdinal) :
    ∃ y : VForm, IsProper y ∧ x ≤ denote y := by
  obtain ⟨⟨k⟩, hk⟩ := sup_lt (lt_of_lt_of_le hx LVO_alt.le)
  replace hk := le_of_lt hk
  clear hx
  induction k generalizing x with
  | zero => exact ⟨Z, trivial, hk⟩
  | succ k ih =>
    obtain ⟨y, hy₁, hy₂⟩ := ih _ (le_refl _)
    refine ⟨N [(y, N [])], ⟨hy₁, trivial, trivial⟩, le_trans hk ?_⟩
    exact schutte_column_monotone_full _ _ _ _ _ _ _ _ onePlus_normal.monotone onePlus_normal.monotone
      (fun _ => le_refl _) hy₂ (add_zero 1).ge (le_refl 0)

/-- Rocq: `Notation.SchutteMatrix.VForm_le_LVO`. -/
theorem le_LVO : LargeVeblenOrdinal ≤ VF :=
  le_intro fun a =>
    let ⟨y, _, hy⟩ := LVO_proper_VForm _ (index_lt _ a)
    lt_of_le_of_lt hy (index_lt VF y)

end VForm

/-- The forms have order type the large Veblen ordinal.
Rocq: `Notation.SchutteMatrix.VF_LVO`. -/
theorem VF_LVO : VF ≈ LargeVeblenOrdinal :=
  equiv_intro (limit_least fun x => VForm.bounded x) VForm.le_LVO

namespace VForm

/-! ## Active subterms and sparse matrices -/

/-- `a` is the last nonzero argument of the matrix.
Rocq: `Notation.SchutteMatrix.active_subterm`. -/
inductive ActiveSubterm : List (VForm × VForm) → VForm → Prop
  | last {b a : VForm} {xs : List (VForm × VForm)} : a ≠ Z → Each (fun x => x.2 = Z) xs →
      ActiveSubterm ((b, a) :: xs) a
  | later {z : VForm} {x : VForm × VForm} {xs : List (VForm × VForm)} : ActiveSubterm xs z →
      ActiveSubterm (x :: xs) z

/-- Rocq: `Notation.SchutteMatrix.active_subterm_nonzero`. -/
theorem active_subterm_nonzero {xs : List (VForm × VForm)} {a : VForm} : ActiveSubterm xs a → a ≠ Z
  | .last h _ => h
  | .later h => active_subterm_nonzero h

/-- Rocq: `Notation.SchutteMatrix.active_subterm_all_zeros`. -/
theorem active_subterm_all_zeros : ∀ {xs : List (VForm × VForm)} {a : VForm},
    Each (fun x => x.2 = Z) xs → ActiveSubterm xs a → False
  | _ :: _, _, h, .last ha _ => ha h.1
  | _ :: _, _, h, .later ha => active_subterm_all_zeros h.2 ha

/-- Rocq: `Notation.SchutteMatrix.active_subterm_unique`. -/
theorem active_subterm_unique : ∀ {xs : List (VForm × VForm)} {a b : VForm},
    ActiveSubterm xs a → ActiveSubterm xs b → a = b
  | _ :: _, _, _, .last _ _, .last _ _ => rfl
  | _ :: _, _, _, .last _ h, .later hb => (active_subterm_all_zeros h hb).elim
  | _ :: _, _, _, .later ha, .last _ h => (active_subterm_all_zeros h ha).elim
  | _ :: _, _, _, .later ha, .later hb => active_subterm_unique ha hb

/-- Rocq: `Notation.SchutteMatrix.VF_matrix_proper_correct`. -/
theorem matrix_proper_correct : ∀ xs : List (VForm × VForm),
    MatrixProper xs ↔ Each (fun x => IsProper x.1 ∧ IsProper x.2) xs ∧
      SchutteMatrixProper (matrixDenote xs) LargeVeblenOrdinal LargeVeblenOrdinal
  | [] => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | (b, a) :: xs => by
    -- the tail is proper with first index below `b`
    have key : ∀ (hb : denote b < LargeVeblenOrdinal),
        (match xs with
          | [] => True
          | (b₂, _) :: _ => denote b₂ < denote b ∧ MatrixProper xs) ↔
        (Each (fun x => IsProper x.1 ∧ IsProper x.2) xs ∧
          SchutteMatrixProper (matrixDenote xs) (denote b) LargeVeblenOrdinal) := by
      intro hb
      cases xs with
      | nil => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
      | cons p xs' =>
        obtain ⟨b₂, a₂⟩ := p
        have ih := matrix_proper_correct ((b₂, a₂) :: xs')
        constructor
        · rintro ⟨h₁, h₂⟩
          obtain ⟨he, hs⟩ := ih.1 h₂
          exact ⟨he, h₁, hs.2.1, hs.2.2⟩
        · rintro ⟨he, hs⟩
          exact ⟨hs.1, ih.2 ⟨he, lt_trans hs.1 hb, hs.2.1, hs.2.2⟩⟩
    constructor
    · rintro ⟨hb, ha, h⟩
      obtain ⟨he, hs⟩ := (key (bounded b)).1 h
      exact ⟨⟨⟨hb, ha⟩, he⟩, bounded b, bounded a, hs⟩
    · rintro ⟨⟨⟨hb, ha⟩, he⟩, _, _, hs⟩
      exact ⟨hb, ha, (key (bounded b)).2 ⟨he, hs⟩⟩

/-- Rocq: `Notation.SchutteMatrix.ordering_swap_inv`. -/
theorem ordering_swap_inv (o : Ordering) : o.swap.swap = o := by cases o <;> rfl

theorem N_pos (l : List (VForm × VForm)) : 0 < denote (N l) :=
  lt_of_lt_of_le (lt_of_lt_of_le (succ_lt 0) (le_add_right 1 0))
    (schutte_matrix_base _ _ 0 onePlus_normal (all_complete l))

/-- Rocq: `Notation.SchutteMatrix.VF_nonzero`. -/
theorem VF_nonzero : ∀ x : VForm, 0 < denote x ↔ x ≠ Z
  | Z => ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h⟩
  | N l => ⟨fun _ h => VForm.noConfusion h, fun _ => N_pos l⟩

/-- Every argument is nonzero. Rocq: `Notation.SchutteMatrix.is_sparse`. -/
def IsSparse : List (VForm × VForm) → Prop
  | [] => True
  | (_, a) :: xs => a ≠ Z ∧ IsSparse xs

/-- Drop the entries with zero arguments. Rocq: `Notation.SchutteMatrix.make_sparse`. -/
def makeSparse : List (VForm × VForm) → List (VForm × VForm)
  | [] => []
  | (_, Z) :: xs => makeSparse xs
  | (b, N l) :: xs => (b, N l) :: makeSparse xs

/-- Rocq: `Notation.SchutteMatrix.make_sparse_is_sparse`. -/
theorem make_sparse_is_sparse : ∀ xs : List (VForm × VForm), IsSparse (makeSparse xs)
  | [] => trivial
  | (_, Z) :: xs => make_sparse_is_sparse xs
  | (_, N _) :: xs => ⟨fun h => VForm.noConfusion h, make_sparse_is_sparse xs⟩

/-- Rocq: `Notation.SchutteMatrix.make_sparse_size`. -/
theorem make_sparse_size : ∀ xs : List (VForm × VForm), matrixSize (makeSparse xs) ≤ matrixSize xs
  | [] => Nat.le_refl 0
  | (_, Z) :: xs => Nat.le_succ_of_le (Nat.le_trans (make_sparse_size xs) (Nat.le_add_left _ _))
  | (_, N _) :: xs => Nat.succ_le_succ (Nat.add_le_add_left (make_sparse_size xs) _)

/-- Rocq: `Notation.SchutteMatrix.make_sparse_proper_one`. -/
theorem make_sparse_proper_one : ∀ (xs : List (VForm × VForm)) (b a : VForm),
    MatrixProper ((b, a) :: xs) → MatrixProper ((b, a) :: makeSparse xs)
  | [], _, _, h => h
  | (b', Z) :: xs, b, a, h => by
    have ih := make_sparse_proper_one xs b' Z h.2.2.2
    show IsProper b ∧ IsProper a ∧ _
    refine ⟨h.1, h.2.1, ?_⟩
    show match makeSparse xs with
      | [] => True
      | (b₂, _) :: _ => denote b₂ < denote b ∧ MatrixProper (makeSparse xs)
    revert ih
    cases makeSparse xs with
    | nil => exact fun _ => trivial
    | cons q ms =>
      obtain ⟨b'', a''⟩ := q
      intro ih
      exact ⟨lt_trans ih.2.2.1 h.2.2.1, ih.2.2.2⟩
  | (b', N l) :: xs, b, a, h =>
    ⟨h.1, h.2.1, h.2.2.1, make_sparse_proper_one xs b' (N l) h.2.2.2⟩

/-- Rocq: `Notation.SchutteMatrix.make_sparse_proper`. -/
theorem make_sparse_proper : ∀ xs : List (VForm × VForm), MatrixProper xs → MatrixProper (makeSparse xs)
  | [], h => h
  | (_, Z) :: xs, h => make_sparse_proper xs h.tail
  | (b, N l) :: xs, h => make_sparse_proper_one xs b (N l) h

/-- Rocq: `Notation.SchutteMatrix.make_sparse_eq`. -/
theorem make_sparse_eq : ∀ (xs : List (VForm × VForm)) (f : Ordinal.{0} → Ordinal.{0}), NormalFunction f →
    schutteMatrix f (matrixDenote (makeSparse xs)) 0 ≈ schutteMatrix f (matrixDenote xs) 0
  | [], _, _ => equiv_refl _
  | (b, Z) :: xs, f, hf =>
    equiv_trans (make_sparse_eq xs f hf)
      (equiv_symm (schutte_matrix_zero_arg [] (matrixDenote xs) (denote b) f 0 hf.monotone (complete b)))
  | (b, N _) :: xs, f, hf =>
    make_sparse_eq xs _ (schutte_column_normal _ _ f (complete b) (complete _) hf)

/-- Rocq: `Notation.SchutteMatrix.active_subterm_sparse`. -/
theorem active_subterm_sparse : ∀ (xs : List (VForm × VForm)) (x : VForm), IsSparse xs →
    (ActiveSubterm xs x ↔ ∃ l b, xs = l ++ [(b, x)])
  | [], _, _ => ⟨fun h => (nomatch h), fun ⟨l, _, h⟩ => by cases l <;> cases h⟩
  | (b, a) :: xs, x, hs => by
    constructor
    · intro h
      cases h with
      | last _ hz =>
        cases xs with
        | nil => exact ⟨[], b, rfl⟩
        | cons q _ => exact absurd hz.1 hs.2.1
      | later h =>
        obtain ⟨l, b', e⟩ := (active_subterm_sparse xs x hs.2).1 h
        exact ⟨(b, a) :: l, b', by rw [e]; rfl⟩
    · rintro ⟨l, b', e⟩
      cases l with
      | nil =>
        injection e with e₁ e₂
        injection e₁ with _ e₃
        subst e₃ e₂
        exact .last hs.1 trivial
      | cons p l =>
        injection e with _ e₂
        exact .later ((active_subterm_sparse xs x hs.2).2 ⟨l, b', e₂⟩)

/-- Rocq: `Notation.SchutteMatrix.is_sparse_app`. -/
theorem is_sparse_app : ∀ xs ys : List (VForm × VForm), IsSparse (xs ++ ys) ↔ IsSparse xs ∧ IsSparse ys
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | (_, _) :: xs, ys =>
    ⟨fun h => ⟨⟨h.1, ((is_sparse_app xs ys).1 h.2).1⟩, ((is_sparse_app xs ys).1 h.2).2⟩,
      fun h => ⟨h.1.1, (is_sparse_app xs ys).2 ⟨h.1.2, h.2⟩⟩⟩

/-- Rocq: `Notation.SchutteMatrix.matrix_denote_app`. -/
theorem matrix_denote_app : ∀ xs ys : List (VForm × VForm),
    matrixDenote (xs ++ ys) = matrixDenote xs ++ matrixDenote ys
  | [], _ => rfl
  | (b, a) :: xs, ys => congrArg ((denote b, denote a) :: ·) (matrix_denote_app xs ys)

/-- Rocq: `Notation.SchutteMatrix.matrix_trivial_dec`. -/
def matrixTrivialDec : (xs : List (VForm × VForm)) →
    PSum (TrivialMatrix (matrixDenote xs)) (NontrivialMatrix (matrixDenote xs))
  | [] => .inl trivial
  | (_, Z) :: xs =>
    match matrixTrivialDec xs with
    | .inl h => .inl ⟨equiv_refl 0, h⟩
    | .inr h => .inr (.inr h)
  | (_, N l) :: _ => .inr (.inl (N_pos l))


/-! ## Comparison -/

/-- Compare a matrix with the term `ytop` it is checked against.
Rocq: `Notation.SchutteMatrix.check_lt`. -/
def checkLt (cmp : VForm → VForm → Ordering) : List (VForm × VForm) → VForm → Ordering
  | [], _ => .lt
  | (_, a) :: xs, ytop =>
    match cmp a ytop with
    | .lt => checkLt cmp xs ytop
    | .eq =>
      match matrixTrivialDec xs with
      | .inl _ => .eq
      | .inr _ => .gt
    | .gt => .gt

/-- Compare two sparse matrices, denoting `xtop` and `ytop`.
Rocq: `Notation.SchutteMatrix.matrix_compare`. -/
def matrixCompare (cmp : VForm → VForm → Ordering) (xtop : VForm) :
    List (VForm × VForm) → List (VForm × VForm) → VForm → Ordering
  | [], [], _ => .eq
  | [], _ :: _, _ => .lt
  | _ :: _, [], _ => .gt
  | (xb, xa) :: xs, (yb, ya) :: ys, ytop =>
    match cmp xb yb with
    | .lt => checkLt cmp ((xb, xa) :: xs) ytop
    | .eq =>
      match cmp xa ya with
      | .lt => checkLt cmp xs ytop
      | .eq => matrixCompare cmp xtop xs ys ytop
      | .gt => (checkLt cmp ys xtop).swap
    | .gt => (checkLt cmp ((yb, ya) :: ys) xtop).swap

/-- Comparison with explicit fuel. Rocq: `Notation.SchutteMatrix.VF_compare_loop`. -/
def compareFuel : Nat → VForm → VForm → Ordering
  | 0, _, _ => .eq
  | _ + 1, Z, Z => .eq
  | _ + 1, Z, N _ => .lt
  | _ + 1, N _, Z => .gt
  | k + 1, N xs, N ys =>
    matrixCompare (compareFuel k) (N xs) (makeSparse xs) (makeSparse ys) (N ys)

/-- Rocq: `Notation.SchutteMatrix.VF_compare`. -/
def compare (x y : VForm) : Ordering := compareFuel (termSize x + termSize y + 1) x y

theorem checkLt_correct (cmp : VForm → VForm → Ordering) (ytop : VForm) :
    ∀ xs : List (VForm × VForm),
      Each (fun p => OrderingCorrect (cmp p.2 ytop) (denote p.2) (denote ytop)) xs →
      ConfirmLt (checkLt cmp xs ytop) (matrixDenote xs) (denote ytop)
  | [], _ => .nil _
  | (b, a) :: xs, h => by
    show ConfirmLt (match cmp a ytop with
      | .lt => checkLt cmp xs ytop
      | .eq =>
        match matrixTrivialDec xs with
        | .inl _ => .eq
        | .inr _ => .gt
      | .gt => .gt) ((denote b, denote a) :: matrixDenote xs) (denote ytop)
    have hc : OrderingCorrect (cmp a ytop) (denote a) (denote ytop) := h.1
    revert hc
    cases cmp a ytop with
    | lt => exact fun hc => .lt _ _ _ _ _ hc (checkLt_correct cmp ytop xs h.2)
    | eq =>
      intro hc
      cases matrixTrivialDec xs with
      | inl ht => exact .eq1 _ _ _ _ hc ht
      | inr ht => exact .eq2 _ _ _ _ hc ht
    | gt => exact fun hc => .gt _ _ _ _ hc

/-- Matrices whose head columns agree up to `≈` give the same values. -/
theorem matrix_head_congr {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f)
    (m : List (Ordinal.{0} × Ordinal.{0})) {β β' α α' : Ordinal.{0}} (hβ : β ≈ β') (hα : α ≈ α')
    (x : Ordinal.{0}) : schutteMatrix (schutteColumn f β α) m x ≈ schutteMatrix (schutteColumn f β' α') m x :=
  have mono : ∀ γ δ : Ordinal.{0}, ∀ a b, a ≤ b → schutteColumn f γ δ a ≤ schutteColumn f γ δ b :=
    fun _ _ _ _ hab => schutte_column_monotone f _ _ _ _ _ hf.monotone (le_refl _) hab
  equiv_intro
    (schutte_matrix_monotone_func m _ _ x (mono β α) (mono β' α')
      (fun z => schutte_column_monotone_full f f _ _ z _ _ z hf.monotone hf.monotone (fun _ => le_refl _)
        hβ.le hα.le (le_refl z)))
    (schutte_matrix_monotone_func m _ _ x (mono β' α') (mono β α)
      (fun z => schutte_column_monotone_full f f _ _ z _ _ z hf.monotone hf.monotone (fun _ => le_refl _)
        hβ.ge hα.ge (le_refl z)))

theorem matrixCompare_correct (cmp : VForm → VForm → Ordering) (xtop ytop : VForm) :
    ∀ (xs ys : List (VForm × VForm)) (f : Ordinal.{0} → Ordinal.{0}), NormalFunction f →
      Each (fun p => OrderingCorrect (cmp p.2 ytop) (denote p.2) (denote ytop)) xs →
      Each (fun q => OrderingCorrect (cmp q.2 xtop) (denote q.2) (denote xtop)) ys →
      Each (fun p => Each (fun q => OrderingCorrect (cmp p.1 q.1) (denote p.1) (denote q.1) ∧
        OrderingCorrect (cmp p.2 q.2) (denote p.2) (denote q.2)) ys) xs →
      IsSparse xs → IsSparse ys →
      denote xtop ≈ schutteMatrix f (matrixDenote xs) 0 →
      denote ytop ≈ schutteMatrix f (matrixDenote ys) 0 →
      SchutteMatrixCompare (matrixCompare cmp xtop xs ys ytop) f (matrixDenote xs) (matrixDenote ys)
  | [], [], f, _, _, _, _, _, _, _, _ => .nil_nil f
  | [], (_, ya) :: _, f, _, _, _, _, _, hspy, _, _ => .nil_left f _ _ _ ((VF_nonzero ya).2 hspy.1)
  | (_, xa) :: _, [], f, _, _, _, _, hspx, _, _, _ => .nil_right f _ _ _ ((VF_nonzero xa).2 hspx.1)
  | (xb, xa) :: xs, (yb, ya) :: ys, f, hf, hx, hy, hxy, hspx, hspy, hxeq, hyeq => by
    show SchutteMatrixCompare (match cmp xb yb with
      | .lt => checkLt cmp ((xb, xa) :: xs) ytop
      | .eq =>
        match cmp xa ya with
        | .lt => checkLt cmp xs ytop
        | .eq => matrixCompare cmp xtop xs ys ytop
        | .gt => (checkLt cmp ys xtop).swap
      | .gt => (checkLt cmp ((yb, ya) :: ys) xtop).swap) f
      ((denote xb, denote xa) :: matrixDenote xs) ((denote yb, denote ya) :: matrixDenote ys)
    have hb : OrderingCorrect (cmp xb yb) (denote xb) (denote yb) := hxy.1.1.1
    revert hb
    cases cmp xb yb with
    | lt =>
      exact fun hb => .index_lt _ f _ _ _ _ _ _ hb ((VF_nonzero ya).2 hspy.1)
        (ConfirmLt.congr hyeq (checkLt_correct cmp ytop ((xb, xa) :: xs) hx))
    | eq =>
      intro hb
      have hc : OrderingCorrect (cmp xa ya) (denote xa) (denote ya) := hxy.1.1.2
      revert hc
      cases cmp xa ya with
      | lt =>
        exact fun hc => .arg_lt _ f _ _ _ _ _ _ hb hc
          (ConfirmLt.congr hyeq (checkLt_correct cmp ytop xs hx.2))
      | eq =>
        intro hc
        have hf' := schutte_column_normal _ _ f (complete xb) (complete xa) hf
        exact .eq _ f _ _ _ _ _ _ hb hc
          (matrixCompare_correct cmp xtop ytop xs ys _ hf' hx.2 hy.2 (hxy.2.imp fun _ h => h.2)
            hspx.2 hspy.2 hxeq
            (equiv_trans hyeq (matrix_head_congr hf _ (equiv_symm hb) (equiv_symm hc) 0)))
      | gt =>
        intro hc
        refine .arg_gt _ f _ _ _ _ _ _ hb hc ?_
        rw [ordering_swap_inv]
        exact ConfirmLt.congr hxeq (checkLt_correct cmp xtop ys hy.2)
    | gt =>
      intro hb
      refine .index_gt _ f _ _ _ _ _ _ hb ((VF_nonzero xa).2 hspx.1) ?_
      rw [ordering_swap_inv]
      exact ConfirmLt.congr hxeq (checkLt_correct cmp xtop ((yb, ya) :: ys) hy)

private theorem make_sparse_each {Q : VForm × VForm → Prop} :
    ∀ xs : List (VForm × VForm), Each Q xs → Each Q (makeSparse xs)
  | [], _ => trivial
  | (_, Z) :: xs, h => make_sparse_each xs h.2
  | (_, N _) :: xs, h => ⟨h.1, make_sparse_each xs h.2⟩

private theorem each_and {α : Type} {P Q : α → Prop} :
    ∀ xs : List α, Each P xs → Each Q xs → Each (fun x => P x ∧ Q x) xs
  | [], _, _ => trivial
  | _ :: xs, hp, hq => ⟨⟨hp.1, hq.1⟩, each_and xs hp.2 hq.2⟩

private theorem each_mem {α : Type} {P : α → Prop} : ∀ {xs : List α} {x : α}, Each P xs → x ∈ xs → P x
  | _ :: _, _, h, .head _ => h.1
  | _ :: _, _, h, .tail _ hx => each_mem h.2 hx

theorem compareFuel_correct : ∀ (fuel : Nat) (x y : VForm), termSize x + termSize y < fuel →
    IsProper x → IsProper y → OrderingCorrect (compareFuel fuel x y) (denote x) (denote y)
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, Z, Z, _, _, _ => equiv_refl _
  | _ + 1, Z, N l, _, _, _ => N_pos l
  | _ + 1, N l, Z, _, _, _ => N_pos l
  | k + 1, N xs, N ys, h, hpx, hpy => by
    have hk : termSize (N xs) + termSize (N ys) ≤ k := Nat.le_of_lt_succ h
    have hk' : termSize (N ys) + termSize (N xs) ≤ k := Nat.add_comm _ _ ▸ hk
    have hxs := make_sparse_each xs (each_and xs (each_lt_termSize xs) ((matrix_proper_correct xs).1 hpx).1)
    have hys := make_sparse_each ys (each_and ys (each_lt_termSize ys) ((matrix_proper_correct ys).1 hpy).1)
    have hmx := make_sparse_eq xs _ onePlus_normal
    have hmy := make_sparse_eq ys _ onePlus_normal
    have sc := matrixCompare_correct (compareFuel k) (N xs) (N ys) (makeSparse xs) (makeSparse ys)
      (fun y => 1 + y) onePlus_normal
      (hxs.imp fun p hp => compareFuel_correct k _ _
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hp.1.2 _) hk) hp.2.2 hpy)
      (hys.imp fun q hq => compareFuel_correct k _ _
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hq.1.2 _) hk') hq.2.2 hpx)
      (hxs.imp fun p hp => hys.imp fun q hq =>
        ⟨compareFuel_correct k p.1 q.1 (Nat.lt_of_lt_of_le (Nat.add_lt_add hp.1.1 hq.1.1) hk) hp.2.1 hq.2.1,
          compareFuel_correct k p.2 q.2 (Nat.lt_of_lt_of_le (Nat.add_lt_add hp.1.2 hq.1.2) hk) hp.2.2 hq.2.2⟩)
      (make_sparse_is_sparse xs) (make_sparse_is_sparse ys) (equiv_symm hmx) (equiv_symm hmy)
    exact OrderingCorrect.congr hmx hmy
      (schutte_matrix_compare_correct sc _ _ _ _ onePlus_normal (all_complete _) (all_complete _)
        ((matrix_proper_correct _).1 (make_sparse_proper xs hpx)).2
        ((matrix_proper_correct _).1 (make_sparse_proper ys hpy)).2)

/-- Rocq: `Notation.SchutteMatrix.VF_compare_correct`. -/
theorem compare_correct (x y : VForm) (hx : IsProper x) (hy : IsProper y) :
    OrderingCorrect (compare x y) (denote x) (denote y) :=
  compareFuel_correct _ x y (Nat.lt_succ_self _) hx hy

/-- Rocq: `Notation.SchutteMatrix.VF_dec_order`. -/
def decOrder (x y : VForm) (hx : IsProper x) (hy : IsProper y) :
    PSum (PSum (denote x < denote y) (denote x ≈ denote y)) (denote y < denote x) :=
  match compare x y, compare_correct x y hx hy with
  | .lt, h => .inl (.inl h)
  | .eq, h => .inl (.inr h)
  | .gt, h => .inr h

/-- Rocq: `Notation.SchutteMatrix.VF_dec_lt_ge`. -/
def decLtGe (x y : VForm) (hx : IsProper x) (hy : IsProper y) :
    PSum (denote x < denote y) (denote y ≤ denote x) :=
  match decOrder x y hx hy with
  | .inl (.inl h) => .inl h
  | .inl (.inr h) => .inr h.ge
  | .inr h => .inr (le_of_lt h)

/-- Decide the ordering condition on the tail of a proper matrix. -/
private def tailDec (b : VForm) (hb : IsProper b) : (xs : List (VForm × VForm)) → MatrixProper xs →
    Decidable (match xs with
      | [] => True
      | (b₂, _) :: _ => denote b₂ < denote b ∧ MatrixProper xs)
  | [], _ => isTrue trivial
  | (b₂, _) :: _, h =>
    match decLtGe b₂ b h.1 hb with
    | .inl hlt => isTrue ⟨hlt, h⟩
    | .inr hge => isFalse fun h' => lt_irrefl _ (lt_of_lt_of_le h'.1 hge)

mutual
/-- Properness is decidable. Rocq: `Notation.SchutteMatrix.VF_dec_proper`. -/
def properDec : (x : VForm) → Decidable (IsProper x)
  | Z => isTrue trivial
  | N l => matrixProperDec l

/-- Matrix properness is decidable. -/
def matrixProperDec : (l : List (VForm × VForm)) → Decidable (MatrixProper l)
  | [] => isTrue trivial
  | (b, a) :: xs =>
    match properDec b, properDec a, matrixProperDec xs with
    | isFalse hb, _, _ => isFalse fun h => hb h.1
    | isTrue _, isFalse ha, _ => isFalse fun h => ha h.2.1
    | isTrue _, isTrue _, isFalse hxs => isFalse fun h => hxs h.tail
    | isTrue hb, isTrue ha, isTrue hxs =>
      match tailDec b hb xs hxs with
      | isTrue ht => isTrue ⟨hb, ha, ht⟩
      | isFalse ht => isFalse fun h => ht h.2.2
end

/-- Rocq: `Notation.SchutteMatrix.VF_dec_proper_order`. -/
def decProperOrder (x y : VForm) :
    PSum (PSum (PSum (PSum (¬IsProper x) (¬IsProper y)) (denote x < denote y)) (denote x ≈ denote y))
      (denote y < denote x) :=
  match properDec x, properDec y with
  | isFalse hx, _ => .inl (.inl (.inl (.inl hx)))
  | isTrue _, isFalse hy => .inl (.inl (.inl (.inr hy)))
  | isTrue hx, isTrue hy =>
    match decOrder x y hx hy with
    | .inl (.inl h) => .inl (.inl (.inr h))
    | .inl (.inr h) => .inl (.inr h)
    | .inr h => .inr h

/-- Rocq: `Notation.SchutteMatrix.VF_matrix_proper_app`. -/
theorem matrix_proper_app : ∀ xs ys : List (VForm × VForm), MatrixProper (xs ++ ys) → MatrixProper xs
  | [], _, _ => trivial
  | [(_, _)], _, h => ⟨h.1, h.2.1, trivial⟩
  | (_, _) :: (b₂, a₂) :: xs, ys, h => ⟨h.1, h.2.1, h.2.2.1, matrix_proper_app ((b₂, a₂) :: xs) ys h.2.2.2⟩

theorem matrix_proper_mem {l : List (VForm × VForm)} {p : VForm × VForm} (h : MatrixProper l) (hp : p ∈ l) :
    IsProper p.1 ∧ IsProper p.2 :=
  each_mem (P := fun x => IsProper x.1 ∧ IsProper x.2) ((matrix_proper_correct l).1 h).1 hp

/-- Rocq: `Notation.SchutteMatrix.matrix_index_lt'`. -/
theorem matrix_index_lt' : ∀ (m n : List (VForm × VForm)) (b a : VForm),
    MatrixProper (n ++ m) → (b, a) ∈ m → 0 < denote a →
    denote b < schutteMatrix (schutteMatrix (fun y => 1 + y) (matrixDenote n)) (matrixDenote m) 0
  | (b₀, a₀) :: m, n, b, a, hp, hmem, ha => by
    have hg := matrix_normal n onePlus_normal
    have hp' : MatrixProper (n ++ (b₀, a₀) :: m) := hp
    rw [show n ++ (b₀, a₀) :: m = (n ++ [(b₀, a₀)]) ++ m from (List.append_assoc n [(b₀, a₀)] m).symm] at hp'
    cases hmem with
    | head =>
      have hX := schutte_matrix_base (matrixDenote m) _ 0
        (schutte_column_normal _ _ _ (complete b₀) (complete a₀) hg) (all_complete m)
      refine lt_of_lt_of_le ?_ hX
      have hpn := matrix_proper_app _ _ hp'
      have hb : IsProper b₀ := (matrix_proper_mem hpn (List.mem_append_right n (.head _))).1
      have hD : denote (N (n ++ [(b₀, a₀)])) =
          schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote n)) (denote b₀) (denote a₀) 0 := by
        show schutteMatrix _ (matrixDenote (n ++ [(b₀, a₀)])) 0 = _
        rw [matrix_denote_app, schutte_matrix_app]
        rfl
      -- an index at least its own column value would reach the large Veblen ordinal
      have hfix : ∀ X, X ≤ denote b₀ →
          schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote n)) (denote b₀) (denote a₀) 0 ≤ X →
          False := fun X hXb hX =>
        have hcol : schutteColumn (fun y => 1 + y) (denote b₀) 1 0 ≤ denote b₀ :=
          le_trans (schutte_column_monotone _ _ _ _ _ _ onePlus_normal.monotone
              (succ_least ha : 1 ≤ denote a₀) (le_refl 0))
            (le_trans (schutte_column_monotone_func' (denote b₀) (denote a₀) 0 _ _ onePlus_normal hg
                (fun z hz => onePlus_least_normal hg z hz) (complete b₀) (complete a₀) zero_complete)
              (le_trans hX hXb))
        lt_irrefl _ (lt_of_le_of_lt (le_trans LVO_alt.le
          (normal_fix_least (schutte_column_normalβ _ onePlus_normal) 0 _ (complete b₀) (zero_least _) hcol))
          (bounded b₀))
      match decOrder b₀ (N (n ++ [(b₀, a₀)])) hb hpn with
      | .inl (.inl h) => exact hD ▸ h
      | .inl (.inr h) => exact (hfix _ (le_refl _) (hD ▸ h.ge)).elim
      | .inr h => exact (hfix _ (le_refl _) (hD ▸ le_of_lt h)).elim
    | tail _ hmem =>
      have hg' := schutte_column_normal _ _ _ (complete b₀) (complete a₀) hg
      refine lt_of_lt_of_le (matrix_index_lt' m (n ++ [(b₀, a₀)]) b a hp' hmem ha) ?_
      exact schutte_matrix_monotone_func (matrixDenote m) _ _ 0
        (matrix_normal _ onePlus_normal).monotone hg'.monotone fun z => by
          show schutteMatrix _ (matrixDenote (n ++ [(b₀, a₀)])) z ≤ _
          rw [matrix_denote_app, schutte_matrix_app]
          exact le_refl _

/-- Rocq: `Notation.SchutteMatrix.matrix_index_lt`. -/
theorem matrix_index_lt (m : List (VForm × VForm)) (b a : VForm) (hp : MatrixProper m) (hmem : (b, a) ∈ m)
    (ha : 0 < denote a) : denote b < schutteMatrix (fun y => 1 + y) (matrixDenote m) 0 :=
  matrix_index_lt' m [] b a hp hmem ha

/-! ## Normal forms -/

theorem nontrivial_of_sparse : ∀ (l : List (VForm × VForm)), IsSparse l → l ≠ [] →
    NontrivialMatrix (matrixDenote l)
  | [], _, h => absurd rfl h
  | (_, a) :: _, hs, _ => .inl ((VF_nonzero a).2 hs.1)

/-- Rocq: `Notation.SchutteMatrix.sparse_subterm_lt`. -/
theorem sparse_subterm_lt : ∀ (l : List (VForm × VForm)) (b x : VForm) (f : Ordinal.{0} → Ordinal.{0}),
    NormalFunction f → IsSparse (l ++ [(b, x)]) →
    Each (fun z => denote z.2 < schutteMatrix f (matrixDenote (l ++ [(b, x)])) 0) l
  | [], _, _, _, _, _ => trivial
  | (b', a) :: l, b, x, f, hf, hs =>
    ⟨nontrivial_matrix_member_lt [] _ f _ _ hf trivial (complete b') (complete a) (all_complete _)
        (nontrivial_of_sparse _ hs.2 (fun h => by cases l <;> cases h)),
      sparse_subterm_lt l b x _ (schutte_column_normal _ _ f (complete b') (complete a) hf) hs.2⟩

/-- A nonempty list ends in some element. -/
private theorem exists_last {α : Type} : ∀ l : List α, l ≠ [] → ∃ l' a, l = l' ++ [a]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: l, _ =>
    let ⟨l', c, e⟩ := exists_last (b :: l) (fun h => nomatch h)
    ⟨a :: l', c, congrArg (a :: ·) e⟩

/-- Rocq: `Notation.SchutteMatrix.active_subterm_lt`. -/
theorem active_subterm_lt (xs : List (VForm × VForm)) (hs : IsSparse xs)
    (hact : ∀ x, ActiveSubterm xs x → denote x < denote (N xs)) :
    Each (fun x => denote x.2 < denote (N xs)) xs := by
  match xs, hs, hact with
  | [], _, _ => exact trivial
  | p :: ps, hs, hact =>
    obtain ⟨l, ⟨b, a⟩, e⟩ := exists_last (p :: ps) (fun h => nomatch h)
    rw [e] at hs hact ⊢
    have ha : ActiveSubterm (l ++ [(b, a)]) a := (active_subterm_sparse _ a hs).2 ⟨l, b, rfl⟩
    exact (CantorDecomposition.each_app _ _ _).2
      ⟨sparse_subterm_lt l b a _ onePlus_normal hs, hact a ha, trivial⟩

mutual
/-- Sparse, proper, normal entries, and every argument below the whole term.
Rocq: `Notation.SchutteMatrix.VF_normal`. -/
def IsNormal : VForm → Prop
  | Z => True
  | N l => IsSparse l ∧ MatrixProper l ∧ IsNormalList l ∧ Each (fun x => denote x.2 < denote (N l)) l

/-- Each entry is normal. -/
def IsNormalList : List (VForm × VForm) → Prop
  | [] => True
  | (b, a) :: xs => IsNormal b ∧ IsNormal a ∧ IsNormalList xs
end

theorem isNormalList_iff : ∀ l : List (VForm × VForm),
    IsNormalList l ↔ Each (fun x => IsNormal x.1 ∧ IsNormal x.2) l
  | [] => Iff.rfl
  | (_, _) :: xs => ⟨fun h => ⟨⟨h.1, h.2.1⟩, (isNormalList_iff xs).1 h.2.2⟩,
      fun h => ⟨h.1.1, h.1.2, (isNormalList_iff xs).2 h.2⟩⟩

theorem isNormal_N (l : List (VForm × VForm)) :
    IsNormal (N l) ↔ IsSparse l ∧ MatrixProper l ∧ Each (fun x => IsNormal x.1 ∧ IsNormal x.2) l ∧
      Each (fun x => denote x.2 < denote (N l)) l :=
  ⟨fun h => ⟨h.1, h.2.1, (isNormalList_iff l).1 h.2.2.1, h.2.2.2⟩,
    fun h => ⟨h.1, h.2.1, (isNormalList_iff l).2 h.2.2.1, h.2.2.2⟩⟩

/-- Rocq: `Notation.SchutteMatrix.VF_normal_proper`. -/
theorem normal_proper : ∀ x : VForm, IsNormal x → IsProper x
  | Z, _ => trivial
  | N _, h => h.2.1

/-- Rocq: `Notation.SchutteMatrix.active_subterm_le`. -/
theorem active_subterm_le {xs : List (VForm × VForm)} {x : VForm} (h : ActiveSubterm xs x) :
    ∀ f : Ordinal.{0} → Ordinal.{0}, NormalFunction f → denote x ≤ schutteMatrix f (matrixDenote xs) 0 := by
  induction h with
  | @last b a xs _ _ =>
    intro f hf
    exact le_trans (schutte_column_inflationary1 _ _ 0 f (normal_inflationary hf) (complete a) zero_complete)
      (schutte_matrix_base _ _ 0 (schutte_column_normal _ _ f (complete b) (complete a) hf) (all_complete xs))
  | @later z p xs _ ih =>
    intro f hf
    obtain ⟨b, a⟩ := p
    exact ih _ (schutte_column_normal _ _ f (complete b) (complete a) hf)

theorem active_subterm_lt' {xs : List (VForm × VForm)} {q : Ordinal.{0}}
    (h : Each (fun x => denote x.2 < q) xs) : ∀ x, ActiveSubterm xs x → denote x < q := by
  intro x hx
  induction hx with
  | last _ _ => exact h.1
  | later _ ih => exact ih h.2

/-- Rocq: `Notation.SchutteMatrix.VF_normal_alt`. -/
theorem normal_alt (l : List (VForm × VForm)) :
    IsNormal (N l) ↔ IsSparse l ∧ MatrixProper l ∧ Each (fun x => IsNormal x.1 ∧ IsNormal x.2) l ∧
      ∀ x, ActiveSubterm l x → denote x < denote (N l) :=
  ⟨fun h => let h := (isNormal_N l).1 h; ⟨h.1, h.2.1, h.2.2.1, active_subterm_lt' h.2.2.2⟩,
    fun h => (isNormal_N l).2 ⟨h.1, h.2.1, h.2.2.1, active_subterm_lt l h.1 h.2.2.2⟩⟩

/-- Rocq: `Notation.SchutteMatrix.dec_prod`. -/
def decProd {P Q : Prop} (dp : Decidable P) (dq : P → Decidable Q) : Decidable (P ∧ Q) :=
  match dp with
  | isFalse h => isFalse fun h' => h h'.1
  | isTrue h =>
    match dq h with
    | isFalse h' => isFalse fun h'' => h' h''.2
    | isTrue h' => isTrue ⟨h, h'⟩

/-- Rocq: `Notation.SchutteMatrix.dec_each`. -/
def decEach {α : Type} (P : α → Prop) : (xs : List α) → (∀ x, x ∈ xs → Decidable (P x)) →
    Decidable (Each P xs)
  | [], _ => isTrue trivial
  | x :: xs, d =>
    match d x (.head _) with
    | isFalse h => isFalse fun h' => h h'.1
    | isTrue h =>
      match decEach P xs (fun y hy => d y (.tail _ hy)) with
      | isFalse h' => isFalse fun h'' => h' h''.2
      | isTrue h' => isTrue ⟨h, h'⟩

/-- Rocq: `Notation.SchutteMatrix.VF_dec_is_sparse`. -/
def isSparseDec : (l : List (VForm × VForm)) → Decidable (IsSparse l)
  | [] => isTrue trivial
  | (_, Z) :: _ => isFalse fun h => h.1 rfl
  | (_, N _) :: xs =>
    match isSparseDec xs with
    | isTrue h => isTrue ⟨fun e => VForm.noConfusion e, h⟩
    | isFalse h => isFalse fun h' => h h'.2

mutual
/-- Normality is decidable. Rocq: `Notation.SchutteMatrix.VF_dec_normal`. -/
def isNormalDec : (x : VForm) → Decidable (IsNormal x)
  | Z => isTrue trivial
  | N l =>
    decProd (isSparseDec l) fun _ =>
    decProd (matrixProperDec l) fun hp =>
    decProd (isNormalListDec l) fun _ =>
    decEach _ l fun x hx =>
      match decLtGe x.2 (N l) (matrix_proper_mem hp hx).2 hp with
      | .inl h => isTrue h
      | .inr h => isFalse fun h' => lt_irrefl _ (lt_of_lt_of_le h' h)

/-- `IsNormalList` is decidable. -/
def isNormalListDec : (l : List (VForm × VForm)) → Decidable (IsNormalList l)
  | [] => isTrue trivial
  | (b, a) :: xs =>
    match isNormalDec b, isNormalDec a, isNormalListDec xs with
    | isFalse hb, _, _ => isFalse fun h => hb h.1
    | isTrue _, isFalse ha, _ => isFalse fun h => ha h.2.1
    | isTrue _, isTrue _, isFalse hxs => isFalse fun h => hxs h.2.2
    | isTrue hb, isTrue ha, isTrue hxs => isTrue ⟨hb, ha, hxs⟩
end

instance : DecidablePred IsNormal := isNormalDec

/-- `f 0` is below any matrix with a nonzero leading argument. -/
private theorem base_lt_matrix {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f) (b a : VForm)
    (m : List (VForm × VForm)) (ha : a ≠ Z) : f 0 < schutteMatrix f (matrixDenote ((b, a) :: m)) 0 :=
  lt_of_lt_of_le (hf.increasing _ _ (add_complete (complete a) zero_complete)
      (lt_of_lt_of_le ((VF_nonzero a).2 ha) (add_zero _).ge))
    (le_trans (schutte_column_le_f _ _ 0 f hf.monotone)
      (schutte_matrix_base _ _ 0 (schutte_column_normal _ _ f (complete b) (complete a) hf)
        (all_complete m)))

/-- Rocq: `Notation.SchutteMatrix.matrix_denote_eq_unique`. -/
theorem matrix_denote_eq_unique : ∀ (xs ys : List (VForm × VForm)) (f : Ordinal.{0} → Ordinal.{0})
    (p q : Ordinal.{0}), NormalFunction f →
    schutteMatrix f (matrixDenote xs) 0 ≈ schutteMatrix f (matrixDenote ys) 0 →
    IsSparse xs → IsSparse ys →
    SchutteMatrixProper (matrixDenote xs) p (schutteMatrix f (matrixDenote xs) 0) →
    SchutteMatrixProper (matrixDenote ys) q (schutteMatrix f (matrixDenote ys) 0) →
    Each (fun x => IsProper x.1 ∧ IsProper x.2) xs →
    Each (fun x => IsProper x.1 ∧ IsProper x.2) ys →
    Forall₂ (fun x y => denote x.1 ≈ denote y.1 ∧ denote x.2 ≈ denote y.2) xs ys
  | [], [], _, _, _, _, _, _, _, _, _, _, _ => .nil
  | [], (yb, ya) :: ys, _, _, _, hf, heq, _, hys, _, _, _, _ =>
    absurd (lt_of_lt_of_le (base_lt_matrix hf yb ya ys hys.1) heq.ge) (lt_irrefl _)
  | (xb, xa) :: xs, [], _, _, _, hf, heq, hxs, _, _, _, _, _ =>
    absurd (lt_of_lt_of_le (base_lt_matrix hf xb xa xs hxs.1) heq.le) (lt_irrefl _)
  | (xb, xa) :: xs, (yb, ya) :: ys, f, p, q, hf, heq, hxs₁, hys₁, hxs₂, hys₂, hxs₃, hys₃ => by
    have hxa := complete xa
    have hya := complete ya
    -- the column indices agree
    have hb : denote xb ≈ denote yb := by
      match decOrder xb yb hxs₃.1.1 hys₃.1.1 with
      | .inl (.inr h) => exact h
      | .inl (.inl h) =>
        exact absurd (lt_of_lt_of_le (schutte_matrix_lt1 _ f _ _ _ _ _ 0 hf
          (all_complete xs) (complete _) hxa (all_complete ys) (complete _) hya zero_complete
          (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq.le hxs₂.2.2)
          ((VF_nonzero ya).2 hys₁.1) h (lt_of_lt_of_le hxs₂.2.1 heq.le)) heq.ge) (lt_irrefl _)
      | .inr h =>
        exact absurd (lt_of_lt_of_le (schutte_matrix_lt1 _ f _ _ _ _ _ 0 hf
          (all_complete ys) (complete _) hya (all_complete xs) (complete _) hxa zero_complete
          (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq.ge hys₂.2.2)
          ((VF_nonzero xa).2 hxs₁.1) h (lt_of_lt_of_le hys₂.2.1 heq.ge)) heq.le) (lt_irrefl _)
    -- the arguments agree
    have ha : denote xa ≈ denote ya := by
      match decOrder xa ya hxs₃.1.2 hys₃.1.2 with
      | .inl (.inr h) => exact h
      | .inl (.inl h) =>
        exact absurd (lt_of_le_of_lt (matrix_head_congr hf (matrixDenote xs) hb (equiv_refl _) 0).le
          (lt_of_lt_of_le (schutte_matrix_lt2 _ f _ _ _ _ 0 hf
            (all_complete xs) (complete yb) hxa (all_complete ys) hya zero_complete ⟨_, hys₂.2.2⟩
            (schutte_matrix_proper_monotone _ _ _ _ _ hb.le heq.le hxs₂.2.2) h) heq.ge))
          (lt_irrefl _)
      | .inr h =>
        exact absurd (lt_of_le_of_lt (matrix_head_congr hf (matrixDenote ys) (equiv_symm hb) (equiv_refl _) 0).le
          (lt_of_lt_of_le (schutte_matrix_lt2 _ f _ _ _ _ 0 hf
            (all_complete ys) (complete xb) hya (all_complete xs) hxa zero_complete ⟨_, hxs₂.2.2⟩
            (schutte_matrix_proper_monotone _ _ _ _ _ hb.ge heq.ge hys₂.2.2) h) heq.le))
          (lt_irrefl _)
    have hcong := matrix_head_congr hf (matrixDenote ys) (equiv_symm hb) (equiv_symm ha) 0
    exact .cons ⟨hb, ha⟩ (matrix_denote_eq_unique xs ys _ (denote xb) (denote yb)
      (schutte_column_normal _ _ f (complete xb) hxa hf) (equiv_trans heq hcong)
      hxs₁.2 hys₁.2 hxs₂.2.2
      (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) hcong.le hys₂.2.2) hxs₃.2 hys₃.2)

private theorem matrix_proper_below : ∀ (l : List (VForm × VForm)) (p q : Ordinal.{0}),
    Each (fun x => denote x.2 < q) l → SchutteMatrixProper (matrixDenote l) p LargeVeblenOrdinal →
    SchutteMatrixProper (matrixDenote l) p q
  | [], _, _, _, _ => trivial
  | (_, _) :: l, _, q, he, hs => ⟨hs.1, he.1, matrix_proper_below l _ q he.2 hs.2.2⟩

/-- Rocq: `Notation.SchutteMatrix.VF_normal_schutte_matrix_proper`. -/
theorem normal_schutte_matrix_proper (l : List (VForm × VForm)) (h : IsNormal (N l)) :
    SchutteMatrixProper (matrixDenote l) LargeVeblenOrdinal (denote (N l)) :=
  matrix_proper_below l _ _ h.2.2.2 ((matrix_proper_correct l).1 h.2.1).2

private theorem eq_of_forall₂ {P : VForm → Prop} (hP : ∀ x, P x ↔ ∀ y, IsNormal x → IsNormal y → denote x ≈ denote y → x = y) :
    ∀ (xs ys : List (VForm × VForm)), Each (fun x => P x.1 ∧ P x.2) xs →
      Each (fun x => IsNormal x.1 ∧ IsNormal x.2) xs → Each (fun x => IsNormal x.1 ∧ IsNormal x.2) ys →
      Forall₂ (fun x y => denote x.1 ≈ denote y.1 ∧ denote x.2 ≈ denote y.2) xs ys → xs = ys
  | [], [], _, _, _, _ => rfl
  | (b, a) :: xs, (b', a') :: ys, ih, hx, hy, .cons ⟨h₁, h₂⟩ h => by
    have e₁ : b = b' := (hP b).1 ih.1.1 b' hx.1.1 hy.1.1 h₁
    have e₂ : a = a' := (hP a).1 ih.1.2 a' hx.1.2 hy.1.2 h₂
    rw [e₁, e₂, eq_of_forall₂ hP xs ys ih.2 hx.2 hy.2 h]

/-- Rocq: `Notation.SchutteMatrix.VF_normal_form_unique`. -/
theorem normal_form_unique (x : VForm) :
    ∀ y, IsNormal x → IsNormal y → denote x ≈ denote y → x = y := by
  refine induction' (fun x => ∀ y, IsNormal x → IsNormal y → denote x ≈ denote y → x = y) ?_ ?_ x
  · intro y _ _ heq
    cases y with
    | Z => rfl
    | N yl => exact absurd (lt_of_lt_of_le (N_pos yl) heq.ge) (lt_irrefl _)
  · intro xl ih y hx hy heq
    cases y with
    | Z => exact absurd (lt_of_lt_of_le (N_pos xl) heq.le) (lt_irrefl _)
    | N yl =>
      have hx' := (isNormal_N xl).1 hx
      have hy' := (isNormal_N yl).1 hy
      have hf := matrix_denote_eq_unique xl yl _ _ _ onePlus_normal heq hx'.1 hy'.1
        (normal_schutte_matrix_proper xl hx) (normal_schutte_matrix_proper yl hy)
        (hx'.2.2.1.imp fun p hp => ⟨normal_proper _ hp.1, normal_proper _ hp.2⟩)
        (hy'.2.2.1.imp fun p hp => ⟨normal_proper _ hp.1, normal_proper _ hp.2⟩)
      exact congrArg N (eq_of_forall₂ (fun _ => Iff.rfl) xl yl ih hx'.2.2.1 hy'.2.2.1 hf)

/-! ## Normalization by rewriting -/

/-- Rocq: `Notation.SchutteMatrix.redex`. -/
inductive Redex : VForm → VForm → Prop
  | zero (m n : List (VForm × VForm)) (b : VForm) : Redex (N (m ++ (b, Z) :: n)) (N (m ++ n))
  | fixpoint {l : List (VForm × VForm)} {x : VForm} : ActiveSubterm l x → MatrixProper l →
      compare (N l) x = .eq → Redex (N l) x

theorem active_subterm_proper : ∀ {l : List (VForm × VForm)} {x : VForm},
    ActiveSubterm l x → MatrixProper l → IsProper x
  | _, _, .last _ _, hp => hp.2.1
  | _, _, .later h, hp => active_subterm_proper h hp.tail

theorem active_subterm_each {Q : VForm → Prop} : ∀ {l : List (VForm × VForm)} {x : VForm},
    ActiveSubterm l x → Each (fun p => Q p.2) l → Q x
  | _, _, .last _ _, h => h.1
  | _, _, .later hx, h => active_subterm_each hx h.2

/-- Rocq: `Notation.SchutteMatrix.redex_sound`. -/
theorem redex_sound {x y : VForm} : Redex x y → denote x ≈ denote y
  | .zero m n b => by
    show schutteMatrix _ (matrixDenote (m ++ (b, Z) :: n)) 0 ≈ schutteMatrix _ (matrixDenote (m ++ n)) 0
    rw [matrix_denote_app, matrix_denote_app]
    exact schutte_matrix_zero_arg (matrixDenote m) (matrixDenote n) (denote b) _ 0
      onePlus_normal.monotone (complete b)
  | .fixpoint (l := l) (x := x) hx hp h => by
    have hc := compare_correct (N l) x hp (active_subterm_proper hx hp)
    rw [h] at hc
    exact hc

private theorem active_lt_size {l : List (VForm × VForm)} {x : VForm} (h : ActiveSubterm l x) :
    termSize x < termSize (N l) := by
  induction h with
  | @last b a xs _ _ => exact (each_lt_termSize ((b, a) :: xs)).1.2
  | @later z p xs _ ih =>
    obtain ⟨b, a⟩ := p
    exact Nat.lt_of_lt_of_le ih (Nat.succ_le_succ (Nat.le_succ_of_le (Nat.le_add_left _ _)))

/-- Rocq: `Notation.SchutteMatrix.redex_size`. -/
theorem redex_size {x y : VForm} : Redex x y → termSize y < termSize x
  | .zero m n b => by
    show matrixSize (m ++ n) + 1 < matrixSize (m ++ (b, Z) :: n) + 1
    rw [matrixSize_app, matrixSize_app]
    exact Nat.succ_lt_succ (Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_add_left _ _)) _)
  | .fixpoint h _ _ => active_lt_size h

/-- Rocq: `Notation.SchutteMatrix.one_step_reduce`. -/
inductive OneStepReduce : VForm → VForm → Prop
  | redex {x y : VForm} : Redex x y → OneStepReduce x y
  | cong_arg {x x' : VForm} (b : VForm) (l₁ l₂ : List (VForm × VForm)) : OneStepReduce x x' →
      OneStepReduce (N (l₁ ++ (b, x) :: l₂)) (N (l₁ ++ (b, x') :: l₂))
  | cong_idx {x x' : VForm} (a : VForm) (l₁ l₂ : List (VForm × VForm)) : OneStepReduce x x' →
      OneStepReduce (N (l₁ ++ (x, a) :: l₂)) (N (l₁ ++ (x', a) :: l₂))

/-- Rocq: `Notation.SchutteMatrix.one_step_reduce_sound`. -/
theorem one_step_reduce_sound {x y : VForm} : OneStepReduce x y → denote x ≈ denote y
  | .redex h => redex_sound h
  | .cong_arg (x := x) (x' := x') b l₁ l₂ h => by
    have ih := one_step_reduce_sound h
    show schutteMatrix _ (matrixDenote (l₁ ++ (b, x) :: l₂)) 0 ≈
      schutteMatrix _ (matrixDenote (l₁ ++ (b, x') :: l₂)) 0
    rw [matrix_denote_app, matrix_denote_app, schutte_matrix_app, schutte_matrix_app]
    exact matrix_head_congr (matrix_normal l₁ onePlus_normal) _ (equiv_refl _) ih 0
  | .cong_idx (x := x) (x' := x') a l₁ l₂ h => by
    have ih := one_step_reduce_sound h
    show schutteMatrix _ (matrixDenote (l₁ ++ (x, a) :: l₂)) 0 ≈
      schutteMatrix _ (matrixDenote (l₁ ++ (x', a) :: l₂)) 0
    rw [matrix_denote_app, matrix_denote_app, schutte_matrix_app, schutte_matrix_app]
    exact matrix_head_congr (matrix_normal l₁ onePlus_normal) _ ih (equiv_refl _) 0

/-- Rocq: `Notation.SchutteMatrix.one_step_reduce_size`. -/
theorem one_step_reduce_size {x y : VForm} : OneStepReduce x y → termSize y < termSize x
  | .redex h => redex_size h
  | .cong_arg (x := x) (x' := x') b l₁ l₂ h => by
    show matrixSize (l₁ ++ (b, x') :: l₂) + 1 < matrixSize (l₁ ++ (b, x) :: l₂) + 1
    rw [matrixSize_app, matrixSize_app]
    exact Nat.succ_lt_succ (Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.add_lt_add_right
      (Nat.add_lt_add_left (one_step_reduce_size h) _) _)) _)
  | .cong_idx (x := x) (x' := x') a l₁ l₂ h => by
    show matrixSize (l₁ ++ (x', a) :: l₂) + 1 < matrixSize (l₁ ++ (x, a) :: l₂) + 1
    rw [matrixSize_app, matrixSize_app]
    exact Nat.succ_lt_succ (Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.add_lt_add_right
      (Nat.add_lt_add_right (one_step_reduce_size h) _) _)) _)

/-- Rocq: `Notation.SchutteMatrix.step_reduce_sound`. -/
theorem step_reduce_sound {x y : VForm} :
    ClosReflTrans OneStepReduce x y → denote x ≈ denote y
  | .step h => one_step_reduce_sound h
  | .refl _ => equiv_refl _
  | .trans h₁ h₂ => equiv_trans (step_reduce_sound h₁) (step_reduce_sound h₂)

/-- Rocq: `Notation.SchutteMatrix.VF_dec_active_subterm`. -/
def activeSubtermDec : (xs : List (VForm × VForm)) →
    PSum { y // ActiveSubterm xs y } (Each (fun x => x.2 = Z) xs)
  | [] => .inr trivial
  | (_, a) :: xs =>
    match activeSubtermDec xs with
    | .inl ⟨y, h⟩ => .inl ⟨y, .later h⟩
    | .inr h =>
      match a with
      | Z => .inr ⟨rfl, h⟩
      | N l => .inl ⟨N l, .last (fun h => VForm.noConfusion h) h⟩

/-- Comparison returns `eq` exactly on equivalent proper forms. Stated for the port. -/
theorem eq_correct (x y : VForm) (hx : IsProper x) (hy : IsProper y) :
    compare x y = .eq ↔ denote x ≈ denote y := by
  have h := compare_correct x y hx hy
  revert h
  cases compare x y with
  | lt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h h'.ge)).elim⟩
  | eq => exact fun h => ⟨fun _ => h, fun _ => rfl⟩
  | gt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h h'.le)).elim⟩

private theorem exists_zero : ∀ l : List (VForm × VForm), ¬ IsSparse l →
    ∃ l₁ b l₂, l = l₁ ++ (b, Z) :: l₂
  | [], h => absurd trivial h
  | (b, Z) :: l, _ => ⟨[], b, l, rfl⟩
  | (b, N m) :: l, h =>
    let ⟨l₁, b', l₂, e⟩ := exists_zero l fun hs => h ⟨fun e => VForm.noConfusion e, hs⟩
    ⟨(b, N m) :: l₁, b', l₂, congrArg _ e⟩

private theorem find_reducible : ∀ l : List (VForm × VForm),
    Each (fun p => (IsProper p.1 → (¬ IsNormal p.1 ↔ ∃ y, OneStepReduce p.1 y)) ∧
      (IsProper p.2 → (¬ IsNormal p.2 ↔ ∃ y, OneStepReduce p.2 y))) l →
    Each (fun p => IsProper p.1 ∧ IsProper p.2) l →
    ¬ Each (fun p => IsNormal p.1 ∧ IsNormal p.2) l →
    ∃ l₁ l₂ b a, l = l₁ ++ (b, a) :: l₂ ∧ ((∃ y, OneStepReduce b y) ∨ ∃ y, OneStepReduce a y)
  | [], _, _, h => absurd trivial h
  | (b, a) :: l, ih, hp, h =>
    match isNormalDec b, isNormalDec a with
    | isFalse hb, _ => ⟨[], l, b, a, rfl, .inl ((ih.1.1 hp.1.1).1 hb)⟩
    | isTrue _, isFalse ha => ⟨[], l, b, a, rfl, .inr ((ih.1.2 hp.1.2).1 ha)⟩
    | isTrue hb, isTrue ha =>
      let ⟨l₁, l₂, b', a', e, hr⟩ := find_reducible l ih.2 hp.2 fun h' => h ⟨⟨hb, ha⟩, h'⟩
      ⟨(b, a) :: l₁, l₂, b', a', congrArg _ e, hr⟩

/-- Rocq: `Notation.SchutteMatrix.VF_notIsNormal_redex`. -/
theorem notIsNormal_redex (x : VForm) : IsProper x → (¬ IsNormal x ↔ ∃ y, OneStepReduce x y) := by
  refine induction' (fun x => IsProper x → (¬ IsNormal x ↔ ∃ y, OneStepReduce x y)) ?_ ?_ x
  · exact fun _ => ⟨fun h => absurd trivial h, fun ⟨_, h⟩ => by cases h with | redex h => cases h⟩
  · intro xs ih hp
    have hpe := ((matrix_proper_correct xs).1 hp).1
    constructor
    · intro hn
      match isSparseDec xs with
      | isFalse hs =>
        obtain ⟨l₁, b, l₂, e⟩ := exists_zero xs hs
        subst e
        exact ⟨N (l₁ ++ l₂), .redex (.zero l₁ l₂ b)⟩
      | isTrue hs =>
        have hfinish : ¬ Each (fun p => IsNormal p.1 ∧ IsNormal p.2) xs → ∃ y, OneStepReduce (N xs) y :=
          fun h => by
            obtain ⟨l₁, l₂, b, a, e, hr⟩ := find_reducible xs ih hpe h
            subst e
            match hr with
            | .inl ⟨y, hy⟩ => exact ⟨_, .cong_idx a l₁ l₂ hy⟩
            | .inr ⟨y, hy⟩ => exact ⟨_, .cong_arg b l₁ l₂ hy⟩
        match activeSubtermDec xs with
        | .inl ⟨x, hx⟩ =>
          have hpx := active_subterm_proper hx hp
          match decOrder (N xs) x hp hpx with
          | .inl (.inr heq) => exact ⟨x, .redex (.fixpoint hx hp ((eq_correct _ _ hp hpx).2 heq))⟩
          | .inl (.inl hlt) =>
            exact absurd (lt_of_lt_of_le hlt (active_subterm_le hx _ onePlus_normal)) (lt_irrefl _)
          | .inr hgt =>
            exact hfinish fun heach => hn ((normal_alt xs).2 ⟨hs, hp, heach,
              fun y hy => active_subterm_unique hx hy ▸ hgt⟩)
        | .inr hz =>
          exact hfinish fun heach => hn ((normal_alt xs).2 ⟨hs, hp, heach,
            fun y hy => (active_subterm_all_zeros hz hy).elim⟩)
    · rintro ⟨y, hy⟩ hn
      cases hy with
      | redex r =>
        cases r with
        | zero l₁ l₂ b => exact ((is_sparse_app _ _).1 hn.1).2.1 rfl
        | fixpoint hx hp' hc =>
          exact lt_irrefl _ (lt_of_lt_of_le (((normal_alt _).1 hn).2.2.2 _ hx)
            ((eq_correct (N _) _ hp' (active_subterm_proper hx hp')).1 hc).le)
      | @cong_arg x x' b l₁ l₂ h =>
        have hm : (b, x) ∈ l₁ ++ (b, x) :: l₂ := List.mem_append_right l₁ (.head _)
        exact (each_mem ih hm).2 (each_mem hpe hm).2 |>.2 ⟨_, h⟩
          (each_mem (P := fun p => IsNormal p.1 ∧ IsNormal p.2) ((isNormal_N _).1 hn).2.2.1 hm).2
      | @cong_idx x x' a l₁ l₂ h =>
        have hm : (x, a) ∈ l₁ ++ (x, a) :: l₂ := List.mem_append_right l₁ (.head _)
        exact (each_mem ih hm).1 (each_mem hpe hm).1 |>.2 ⟨_, h⟩
          (each_mem (P := fun p => IsNormal p.1 ∧ IsNormal p.2) ((isNormal_N _).1 hn).2.2.1 hm).1

/-- Rocq: `Notation.SchutteMatrix.VF_normal_no_redex`. -/
theorem normal_no_redex (x : VForm) (hp : IsProper x) : IsNormal x ↔ ¬ ∃ y, OneStepReduce x y :=
  match isNormalDec x with
  | isTrue h => ⟨fun _ hr => (notIsNormal_redex x hp).2 hr h, fun _ => h⟩
  | isFalse h => ⟨fun h' => absurd h' h, fun hr => absurd ((notIsNormal_redex x hp).1 h) hr⟩

private theorem matrix_proper_drop : ∀ (m : List (VForm × VForm)) (b a : VForm) (n : List (VForm × VForm)),
    MatrixProper (m ++ (b, a) :: n) → MatrixProper (m ++ n)
  | [], _, _, _, h => h.tail
  | [(_, _)], _, _, [], h => ⟨h.1, h.2.1, trivial⟩
  | [(_, _)], _, _, (_, _) :: _, h => ⟨h.1, h.2.1, lt_trans h.2.2.2.2.2.1 h.2.2.1, h.2.2.2.2.2.2⟩
  | (_, _) :: (b₂, a₂) :: m, b, a, n, h => ⟨h.1, h.2.1, h.2.2.1, matrix_proper_drop ((b₂, a₂) :: m) b a n h.2.2.2⟩

private theorem matrix_proper_replace : ∀ (l₁ l₂ : List (VForm × VForm)) {b a b' a' : VForm},
    (IsProper b → IsProper b') → (IsProper a → IsProper a') → denote b' ≈ denote b →
    MatrixProper (l₁ ++ (b, a) :: l₂) → MatrixProper (l₁ ++ (b', a') :: l₂)
  | [], [], _, _, _, _, hb, ha, _, h => ⟨hb h.1, ha h.2.1, trivial⟩
  | [], (_, _) :: _, _, _, _, _, hb, ha, he, h => ⟨hb h.1, ha h.2.1, lt_of_lt_of_le h.2.2.1 he.ge, h.2.2.2⟩
  | [(_, _)], l₂, _, _, _, _, hb, ha, he, h =>
    ⟨h.1, h.2.1, lt_of_le_of_lt he.le h.2.2.1, matrix_proper_replace [] l₂ hb ha he h.2.2.2⟩
  | (_, _) :: (b₂, a₂) :: l₁, l₂, _, _, _, _, hb, ha, he, h =>
    ⟨h.1, h.2.1, h.2.2.1, matrix_proper_replace ((b₂, a₂) :: l₁) l₂ hb ha he h.2.2.2⟩

/-- Rocq: `Notation.SchutteMatrix.redex_proper`. -/
theorem redex_proper {x y : VForm} : Redex x y → IsProper x → IsProper y
  | .zero m n b, hp => matrix_proper_drop m b Z n hp
  | .fixpoint hx _ _, hp => active_subterm_proper hx hp

/-- Rocq: `Notation.SchutteMatrix.one_step_reduce_proper`. -/
theorem one_step_reduce_proper {x y : VForm} : OneStepReduce x y → IsProper x → IsProper y
  | .redex h, hp => redex_proper h hp
  | .cong_arg _ l₁ l₂ h, hp =>
    matrix_proper_replace l₁ l₂ id (one_step_reduce_proper h) (equiv_refl _) hp
  | .cong_idx _ l₁ l₂ h, hp =>
    matrix_proper_replace l₁ l₂ (one_step_reduce_proper h) id (equiv_symm (one_step_reduce_sound h)) hp

/-- `x` reduces to the normal form `y`. Rocq: `Notation.SchutteMatrix.normalizes`. -/
inductive Normalizes : VForm → VForm → Prop
  | normal {x : VForm} : (¬ ∃ y, OneStepReduce x y) → Normalizes x x
  | step {x y z : VForm} : OneStepReduce x y → Normalizes y z → Normalizes x z

/-- Rocq: `Notation.SchutteMatrix.normalizes_eq`. -/
theorem normalizes_eq {x y : VForm} : Normalizes x y → denote x ≈ denote y
  | .normal _ => equiv_refl _
  | .step h₁ h₂ => equiv_trans (one_step_reduce_sound h₁) (normalizes_eq h₂)

/-- Rocq: `Notation.SchutteMatrix.normalizes_normal`. -/
theorem normalizes_normal {x y : VForm} : IsProper x → Normalizes x y → IsNormal y
  | hp, .normal h => (normal_no_redex _ hp).2 h
  | hp, .step h₁ h₂ => normalizes_normal (one_step_reduce_proper h₁ hp) h₂

/-- Every proper form has a unique normal form, reached by reduction.
Rocq: `Notation.SchutteMatrix.strongly_normalizing`. -/
theorem strongly_normalizing (x : VForm) (hp : IsProper x) :
    ∃ y, Normalizes x y ∧ ∀ y', Normalizes x y' → y' = y := by
  suffices h : ∀ n x, termSize x < n → IsProper x → ∃ y, Normalizes x y ∧ ∀ y', Normalizes x y' → y' = y from
    h _ x (Nat.lt_succ_self _) hp
  intro n
  induction n with
  | zero => exact fun x h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx hp
    match isNormalDec x with
    | isTrue h =>
      refine ⟨x, .normal ((normal_no_redex x hp).1 h), fun y' hy' => ?_⟩
      cases hy' with
      | normal _ => rfl
      | step h₁ _ => exact absurd ⟨_, h₁⟩ ((normal_no_redex x hp).1 h)
    | isFalse h =>
      obtain ⟨y, hy⟩ := (notIsNormal_redex x hp).1 h
      have hpy := one_step_reduce_proper hy hp
      obtain ⟨z, hz, _⟩ :=
        ih y (Nat.lt_of_lt_of_le (one_step_reduce_size hy) (Nat.le_of_lt_succ hx)) hpy
      refine ⟨z, .step hy hz, fun q hq => normal_form_unique _ _ (normalizes_normal hp hq)
        (normalizes_normal hpy hz) ?_⟩
      exact equiv_trans (equiv_symm (normalizes_eq hq))
        (equiv_trans (one_step_reduce_sound hy) (normalizes_eq hz))

/-- The argument of the last entry. Rocq: `Notation.SchutteMatrix.find_active_subterm`. -/
def findActiveSubterm : List (VForm × VForm) → Option VForm
  | [] => none
  | [(_, a)] => some a
  | _ :: q :: xs => findActiveSubterm (q :: xs)

/-- Rocq: `Notation.SchutteMatrix.find_active_subterm_correct`. -/
theorem find_active_subterm_correct : ∀ (l : List (VForm × VForm)) (x : VForm), IsSparse l →
    (findActiveSubterm l = some x ↔ ActiveSubterm l x)
  | [], _, _ => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | [(_, a)], x, hs =>
    ⟨fun h => by injection h with h; subst h; exact .last hs.1 trivial,
      fun h => match h with
        | .last _ _ => rfl
        | .later h => nomatch h⟩
  | (_, _) :: (b', a') :: xs, x, hs =>
    have ih := find_active_subterm_correct ((b', a') :: xs) x hs.2
    ⟨fun h => .later (ih.1 h),
      fun h => match h with
        | .last _ hz => absurd hz.1 hs.2.1
        | .later h => ih.2 h⟩

/-- Normalize a matrix whose entries are already normal.
Rocq: `Notation.SchutteMatrix.Nnorm`. -/
def Nnorm (l : List (VForm × VForm)) : VForm :=
  match findActiveSubterm (makeSparse l) with
  | none => N (makeSparse l)
  | some x =>
    match compare x (N (makeSparse l)) with
    | .lt => N (makeSparse l)
    | .eq => x
    | .gt => x

/-- Rocq: `Notation.SchutteMatrix.Nnorm_eq`. -/
theorem Nnorm_eq (l : List (VForm × VForm)) (hp : MatrixProper l) : denote (Nnorm l) ≈ denote (N l) := by
  have hms : denote (N (makeSparse l)) ≈ denote (N l) := make_sparse_eq l _ onePlus_normal
  have hpl : MatrixProper (makeSparse l) := make_sparse_proper l hp
  show denote (match findActiveSubterm (makeSparse l) with
    | none => N (makeSparse l)
    | some x =>
      match compare x (N (makeSparse l)) with
      | .lt => N (makeSparse l)
      | .eq => x
      | .gt => x) ≈ _
  cases h : findActiveSubterm (makeSparse l) with
  | none => exact hms
  | some v =>
    have hv := (find_active_subterm_correct _ v (make_sparse_is_sparse l)).1 h
    have hc := compare_correct v (N (makeSparse l)) (active_subterm_proper hv hpl) hpl
    show denote (
    match compare v (N (makeSparse l)) with
      | .lt => N (makeSparse l)
      | .eq => v
      | .gt => v) ≈ _
    revert hc
    cases compare v (N (makeSparse l)) with
    | lt => exact fun _ => hms
    | eq => exact fun hc => equiv_trans hc hms
    | gt => exact fun hc => absurd (lt_of_lt_of_le hc (active_subterm_le hv _ onePlus_normal)) (lt_irrefl _)

/-- Rocq: `Notation.SchutteMatrix.Nnorm_normal`. -/
theorem Nnorm_normal (l : List (VForm × VForm)) (hl : Each (fun x => IsNormal x.1 ∧ IsNormal x.2) l)
    (hp : MatrixProper l) : IsNormal (Nnorm l) := by
  have hpl : MatrixProper (makeSparse l) := make_sparse_proper l hp
  have hs := make_sparse_is_sparse l
  have he := make_sparse_each l hl
  show IsNormal (match findActiveSubterm (makeSparse l) with
    | none => N (makeSparse l)
    | some x =>
      match compare x (N (makeSparse l)) with
      | .lt => N (makeSparse l)
      | .eq => x
      | .gt => x)
  cases h : findActiveSubterm (makeSparse l) with
  | none =>
    refine (normal_alt _).2 ⟨hs, hpl, he, fun x hx => ?_⟩
    have h' := (find_active_subterm_correct _ x hs).2 hx
    rw [h] at h'
    exact nomatch h'
  | some v =>
    have hv := (find_active_subterm_correct _ v hs).1 h
    have hvn : IsNormal v := active_subterm_each (Q := IsNormal) hv (he.imp fun _ h => h.2)
    have hc := compare_correct v (N (makeSparse l)) (normal_proper _ hvn) hpl
    show IsNormal (
    match compare v (N (makeSparse l)) with
      | .lt => N (makeSparse l)
      | .eq => v
      | .gt => v)
    revert hc
    cases compare v (N (makeSparse l)) with
    | lt => exact fun hc => (normal_alt _).2 ⟨hs, hpl, he, fun y hy => active_subterm_unique hv hy ▸ hc⟩
    | eq => exact fun _ => hvn
    | gt => exact fun _ => hvn

mutual
/-- Rocq: `Notation.SchutteMatrix.VF_normalize`. -/
def normalize : VForm → VForm
  | Z => Z
  | N l => Nnorm (normalizeMatrix l)

/-- Normalize each entry of a matrix. -/
def normalizeMatrix : List (VForm × VForm) → List (VForm × VForm)
  | [] => []
  | (b, a) :: xs => (normalize b, normalize a) :: normalizeMatrix xs
end

mutual
/-- Rocq: `Notation.SchutteMatrix.VF_normalize_correct`. -/
theorem normalize_correct : ∀ x : VForm, IsProper x → denote (normalize x) ≈ denote x ∧ IsNormal (normalize x)
  | Z, _ => ⟨equiv_refl _, trivial⟩
  | N l, hp =>
    have h := normalizeMatrix_correct l hp
    ⟨equiv_trans (Nnorm_eq _ h.2.1) (h.1 _ onePlus_normal), Nnorm_normal _ h.2.2 h.2.1⟩

/-- Normalizing the entries preserves the matrix value and properness. -/
theorem normalizeMatrix_correct : ∀ l : List (VForm × VForm), MatrixProper l →
    (∀ f : Ordinal.{0} → Ordinal.{0}, NormalFunction f →
      schutteMatrix f (matrixDenote (normalizeMatrix l)) 0 ≈ schutteMatrix f (matrixDenote l) 0) ∧
    MatrixProper (normalizeMatrix l) ∧ Each (fun x => IsNormal x.1 ∧ IsNormal x.2) (normalizeMatrix l)
  | [], _ => ⟨fun _ _ => equiv_refl _, trivial, trivial⟩
  | [(b, a)], hp =>
    have hb := normalize_correct b hp.1
    have ha := normalize_correct a hp.2.1
    ⟨fun _ hf => matrix_head_congr hf [] hb.1 ha.1 0,
      ⟨normal_proper _ hb.2, normal_proper _ ha.2, trivial⟩, ⟨⟨hb.2, ha.2⟩, trivial⟩⟩
  | (b, a) :: (b₂, a₂) :: xs, hp =>
    have hb := normalize_correct b hp.1
    have ha := normalize_correct a hp.2.1
    have hb₂ := normalize_correct b₂ hp.2.2.2.1
    have ih := normalizeMatrix_correct ((b₂, a₂) :: xs) hp.2.2.2
    ⟨fun f hf => equiv_trans
        (ih.1 _ (schutte_column_normal _ _ f (complete _) (complete _) hf))
        (matrix_head_congr hf _ hb.1 ha.1 0),
      ⟨normal_proper _ hb.2, normal_proper _ ha.2,
        lt_of_le_of_lt hb₂.1.le (lt_of_lt_of_le hp.2.2.1 hb.1.ge), ih.2.1⟩,
      ⟨⟨hb.2, ha.2⟩, ih.2.2⟩⟩
end

/-! ## Cantor decomposition -/

/-- Columns respect `≈` in every argument. -/
theorem column_congr {f : Ordinal.{0} → Ordinal.{0}} (hf : ∀ a b, a ≤ b → f a ≤ f b)
    {β β' α α' x x' : Ordinal.{0}} (hβ : β ≈ β') (hα : α ≈ α') (hx : x ≈ x') :
    schutteColumn f β α x ≈ schutteColumn f β' α' x' :=
  equiv_intro
    (schutte_column_monotone_full f f _ _ _ _ _ _ hf hf (fun _ => le_refl _) hβ.le hα.le hx.le)
    (schutte_column_monotone_full f f _ _ _ _ _ _ hf hf (fun _ => le_refl _) hβ.ge hα.ge hx.ge)

/-- The column at index one of `1 + ·` is `ω ^ α + x`. -/
theorem column_one (α x : Ordinal.{0}) (hα : Complete α) (hx : Complete x) :
    schutteColumn (fun y => 1 + y) 1 α x ≈ ω ^ α + x :=
  equiv_trans (schutte_column_veblen α x _ onePlus_normal hα hx) (veblen_onePlus α hα x hx)

/-- `N [(Z, a)]` denotes `1 + a`. -/
theorem denote_Za (a : VForm) : denote (N [(Z, a)]) ≈ 1 + denote a :=
  equiv_trans (schutte_column0 _ _ 0) (add_congr (equiv_refl 1) (add_zero _))

/-- Rocq: `Notation.SchutteMatrix.expOmega_denote`. -/
theorem expOmega_denote (x : VForm) : ω ^ denote x ≈ denote (N [(N [], x)]) :=
  equiv_symm (equiv_trans (column_congr onePlus_normal.monotone (add_zero 1) (equiv_refl _) (equiv_refl 0))
    (equiv_trans (column_one _ 0 (complete x) zero_complete) (add_zero _)))

/-- `N [(N [], a), (b, x)]` denotes `ω ^ a + x` when `b` denotes zero. -/
theorem denote_two (a b x : VForm) (hb : denote b ≈ 0) :
    denote (N [(N [], a), (b, x)]) ≈ ω ^ denote a + denote x := by
  have hm : ∀ γ δ : Ordinal.{0}, ∀ u v, u ≤ v →
      schutteColumn (fun y => 1 + y) γ δ u ≤ schutteColumn (fun y => 1 + y) γ δ v :=
    fun _ _ _ _ h => schutte_column_monotone _ _ _ _ _ _ onePlus_normal.monotone (le_refl _) h
  show schutteColumn (schutteColumn (fun y => 1 + y) (1 + 0) (denote a)) (denote b) (denote x) 0 ≈ _
  refine equiv_trans (equiv_intro
    (schutte_column_monotone_full _ _ _ _ _ _ _ _ (hm _ _) (hm _ _)
      (fun z => (column_congr onePlus_normal.monotone (add_zero 1) (equiv_refl _) (equiv_refl z)).le)
      hb.le (le_refl _) (le_refl _))
    (schutte_column_monotone_full _ _ _ _ _ _ _ _ (hm _ _) (hm _ _)
      (fun z => (column_congr onePlus_normal.monotone (add_zero 1) (equiv_refl _) (equiv_refl z)).ge)
      hb.ge (le_refl _) (le_refl _))) ?_
  refine equiv_trans (schutte_column0 _ _ 0) ?_
  exact equiv_trans (equiv_intro (hm _ _ _ _ (add_zero _).le) (hm _ _ _ _ (add_zero _).ge))
    (column_one _ _ (complete a) (complete x))

/-- A form whose leading index is not `Z` or `N []` has index above one. -/
theorem one_lt_index (b' a' : VForm) (lb : List (VForm × VForm)) (ha' : a' ≠ Z) :
    1 < denote (N ((b', a') :: lb)) :=
  have hN := schutte_column_normal_arg (denote b') _ (complete b') onePlus_normal
  lt_of_le_of_lt (le_trans (add_zero 1).ge (onePlus_least_normal hN 0 zero_complete))
    (lt_of_lt_of_le (hN.increasing 0 _ (complete a') ((VF_nonzero a').2 ha'))
      (schutte_matrix_base _ _ 0 (schutte_column_normal _ _ _ (complete b') (complete a') onePlus_normal)
        (all_complete lb)))

/-- Rocq: `Notation.SchutteMatrix.schutte_matrix_epsilon`. -/
theorem schutte_matrix_epsilon (b a : VForm) (l : List (VForm × VForm)) (ha : 0 < denote a)
    (hb : 1 < denote b) : ω ^ denote (N ((b, a) :: l)) ≤ denote (N ((b, a) :: l)) := by
  have hf' := schutte_column_normal (denote b) (denote a) _ (complete b) (complete a) onePlus_normal
  refine schutte_matrix_fixpoint1 (matrixDenote l) 0 _ Ordinal.powOmega (all_complete l) zero_complete hf'
    powOmega_normal fun z hz => ?_
  have hg := schutte_column_normal (denote b) 0 _ (complete b) zero_complete onePlus_normal
  have ht := hf'.complete z hz
  calc ω ^ schutteColumn _ (denote b) (denote a) z
      ≤ ω ^ schutteColumn _ (denote b) (denote a) z + 0 := (add_zero _).ge
    _ ≈ veblen (fun y => 1 + y) (schutteColumn _ (denote b) (denote a) z) 0 :=
        equiv_symm (veblen_onePlus _ ht _ zero_complete)
    _ ≤ veblen (schutteColumn (fun y => 1 + y) (denote b) 0)
          (schutteColumn _ (denote b) (denote a) z) 0 :=
        veblen_monotone_func onePlus_normal hg
          (fun i _ => (schutte_column_arg0 _ i _ onePlus_normal.monotone).ge) _ _ ht zero_complete
    _ ≈ schutteColumn (schutteColumn (fun y => 1 + y) (denote b) 0) 1
          (schutteColumn _ (denote b) (denote a) z) 0 :=
        equiv_symm (schutte_column_veblen _ 0 _ hg ht zero_complete)
    _ ≤ schutteColumn _ (denote b) (denote a) z :=
        schutte_column_fixpoint _ _ z _ 1 0 (complete b) (complete a) onePlus_normal hb ha
          (ofNat_complete 1) zero_complete hz

/-- Rocq: `Notation.SchutteMatrix.VF_decompose`. -/
def decompose : VForm → List VForm
  | Z => []
  | N [] => [Z]
  | N ((Z, a) :: _) => Z :: decompose a
  | N [(N [], a)] => [a]
  | N ((N [], a) :: (_, x) :: _) => a :: decompose x
  | N ((N (k :: ks), a) :: l) => [N ((N (k :: ks), a) :: l)]

/-- Rocq: `Notation.SchutteMatrix.VF_recompose`. -/
def recompose : List VForm → VForm
  | [] => Z
  | [x] =>
    match x with
    | Z => N []
    | N [] => N [(N [], N [])]
    | N ((Z, a) :: l) => N [(N [], N ((Z, a) :: l))]
    | N ((N [], a) :: l) => N [(N [], N ((N [], a) :: l))]
    | N ((N (k :: ks), a) :: l) => N ((N (k :: ks), a) :: l)
  | Z :: x' :: xs' => N [(Z, recompose (x' :: xs'))]
  | N l :: x' :: xs' => N [(N [], N l), (Z, recompose (x' :: xs'))]

private theorem le_zero_of_lt_one {x : Ordinal.{0}} (h : x < 1) : x ≤ 0 :=
  let ⟨_, h⟩ := lt_elim h
  h

private theorem not_lt_zero' {x : Ordinal.{0}} (h : x < 0) : False :=
  lt_irrefl _ (lt_of_lt_of_le h (zero_least _))

open CantorDecomposition in
/-- Rocq: `Notation.SchutteMatrix.VF_decompose_correct`. -/
theorem decompose_correct : ∀ x : VForm, IsNormal x →
    Each IsNormal (decompose x) ∧ CantorOrdered denote (decompose x) ∧
      denote x ≈ cantorDenote denote (decompose x)
  | Z, _ => ⟨trivial, trivial, equiv_refl _⟩
  | N [], _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
      add_congr (equiv_symm (pow_zero ω)) (equiv_refl _)⟩
  | N ((Z, _) :: (_, _) :: _), h => (not_lt_zero' h.2.1.2.2.1).elim
  | N [(Z, a)], h => by
    have h' := (isNormal_N _).1 h
    have ih := decompose_correct a h'.2.2.1.1.2
    have hx1 := denote_Za a
    refine ⟨⟨trivial, ih.1⟩, ⟨?_, ih.2.1⟩,
      equiv_trans hx1 (add_congr (equiv_symm (pow_zero ω)) ih.2.2)⟩
    -- the leading exponent of `a` is zero, or else `1 + a ≈ a`
    have hlt : denote a < denote (N [(Z, a)]) := h'.2.2.2.1
    revert ih
    cases decompose a with
    | nil => exact fun _ => trivial
    | cons d ds =>
      intro ih
      cases d with
      | Z => exact le_refl _
      | N ld =>
        refine (lt_irrefl _ (lt_of_lt_of_le hlt (le_trans hx1.le ?_))).elim
        calc 1 + denote a
            ≈ 1 + (ω ^ denote (N ld) + cantorDenote denote ds) := add_congr (equiv_refl 1) ih.2.2
          _ ≈ (1 + ω ^ denote (N ld)) + cantorDenote denote ds := add_assoc _ _ _
          _ ≤ ω ^ denote (N ld) + cantorDenote denote ds :=
              add_le_add (additively_closed_collapse (powOmega_additively_closed (complete _))
                (lt_of_le_of_lt (pow_zero ω).ge (pow_lt_pow_right omega_gt1 (N_pos ld)))) (le_refl _)
          _ ≈ denote a := equiv_symm ih.2.2
  | N [(N [], a)], h =>
    ⟨⟨((isNormal_N _).1 h).2.2.1.1.2, trivial⟩, ⟨trivial, trivial⟩,
      equiv_trans (equiv_symm (expOmega_denote a)) (equiv_symm (add_zero _))⟩
  | N ((N [], _) :: (_, _) :: (_, _) :: _), h =>
    (not_lt_zero' (lt_of_lt_of_le h.2.1.2.2.2.2.2.1
      (le_zero_of_lt_one (lt_of_lt_of_le h.2.1.2.2.1 (add_zero 1).le)))).elim
  | N [(N [], a), (b, x)], h => by
    have h' := (isNormal_N _).1 h
    have ih := decompose_correct x h'.2.2.1.2.1.2
    have hb : denote b ≈ 0 :=
      equiv_intro (le_zero_of_lt_one (lt_of_lt_of_le h'.2.1.2.2.1 (add_zero 1).le)) (zero_least _)
    have hxy := denote_two a b x hb
    have ha := h'.2.2.1.1.2
    refine ⟨⟨ha, ih.1⟩, ⟨?_, ih.2.1⟩, equiv_trans hxy (add_congr (equiv_refl _) ih.2.2)⟩
    have hlt : denote x < denote (N [(N [], a), (b, x)]) := h'.2.2.2.2.1
    revert ih
    cases decompose x with
    | nil => exact fun _ => trivial
    | cons d ds =>
      intro ih
      match decOrder d a (normal_proper _ ih.1.1) (normal_proper _ ha) with
      | .inl (.inl h) => exact le_of_lt h
      | .inl (.inr h) => exact h.le
      | .inr hgt =>
        refine (lt_irrefl _ (lt_of_lt_of_le hlt (le_trans hxy.le ?_))).elim
        calc ω ^ denote a + denote x
            ≈ ω ^ denote a + (ω ^ denote d + cantorDenote denote ds) := add_congr (equiv_refl _) ih.2.2
          _ ≈ (ω ^ denote a + ω ^ denote d) + cantorDenote denote ds := add_assoc _ _ _
          _ ≤ ω ^ denote d + cantorDenote denote ds :=
              add_le_add (pow_add_collapse (complete d) hgt) (le_refl _)
          _ ≈ denote x := equiv_symm ih.2.2
  | N ((N ((b', a') :: lb), a) :: l), h =>
    have h' := (isNormal_N _).1 h
    have hb := (isNormal_N _).1 h'.2.2.1.1.1
    ⟨⟨h, trivial⟩, ⟨trivial, trivial⟩,
      equiv_intro (le_trans (normal_inflationary powOmega_normal _ (complete _)) (add_zero _).ge)
        (le_trans (add_zero _).le (schutte_matrix_epsilon _ a l ((VF_nonzero a).2 h'.1.1)
          (one_lt_index b' a' lb hb.1.1)))⟩

theorem recompose_ne_Z : ∀ (x : VForm) (xs : List VForm), recompose (x :: xs) ≠ Z
  | Z, [] => fun h => VForm.noConfusion h
  | N [], [] => fun h => VForm.noConfusion h
  | N ((Z, _) :: _), [] => fun h => VForm.noConfusion h
  | N ((N [], _) :: _), [] => fun h => VForm.noConfusion h
  | N ((N (_ :: _), _) :: _), [] => fun h => VForm.noConfusion h
  | Z, _ :: _ => fun h => VForm.noConfusion h
  | N _, _ :: _ => fun h => VForm.noConfusion h

/-- The tail of an ordered list is below the list. -/
private theorem cantor_tail_lt (h : VForm) :
    ∀ qs : List VForm, CantorDecomposition.CantorOrdered denote (h :: qs) →
      CantorDecomposition.cantorDenote denote qs < CantorDecomposition.cantorDenote denote (h :: qs)
  | [], _ => lt_of_lt_of_le (pow_pos ω _) (le_add_right _ _)
  | q :: qs, hord =>
    lt_of_lt_of_le (add_lt_add_left _ (cantor_tail_lt q qs hord.2))
      (add_le_add (pow_le_pow_right ω hord.1) (le_refl _))

theorem one_normal : IsNormal (N []) := ⟨trivial, trivial, trivial, trivial⟩

/-- `x < ω ^ x` for the normal forms that `recompose` wraps. -/
private theorem lt_powOmega_wrap (x : VForm) (hx : IsNormal x) (hlt : denote x < ω ^ denote x) (hx0 : x ≠ Z) :
    IsNormal (N [(N [], x)]) ∧ ω ^ denote x + 0 ≈ denote (N [(N [], x)]) :=
  ⟨⟨⟨hx0, trivial⟩, ⟨trivial, normal_proper x hx, trivial⟩, ⟨one_normal, hx, trivial⟩,
      ⟨lt_of_lt_of_le hlt (expOmega_denote x).le, trivial⟩⟩,
    equiv_trans (add_zero _) (expOmega_denote x)⟩

open CantorDecomposition in
/-- Rocq: `Notation.SchutteMatrix.VF_recompose_correct`. -/
theorem recompose_correct : ∀ xs : List VForm, Each IsNormal xs → CantorOrdered denote xs →
    IsNormal (recompose xs) ∧ cantorDenote denote xs ≈ denote (recompose xs)
  | [], _, _ => ⟨trivial, equiv_refl _⟩
  | [x], hP, _ =>
    match x, hP with
    | Z, _ => ⟨one_normal, add_congr (pow_zero ω) (equiv_refl _)⟩
    | N [], hP => lt_powOmega_wrap _ hP.1
        (lt_of_le_of_lt (add_zero 1).le (lt_of_lt_of_le omega_gt1 (le_trans (pow_one' omega_gt0).ge
          (pow_le_pow_right ω (add_zero 1).ge))))
        (fun h => VForm.noConfusion h)
    | N [(Z, a)], hP =>
      have h' := (isNormal_N _).1 hP.1
      have h1 := denote_Za a
      lt_powOmega_wrap _ hP.1 (lt_of_le_of_lt h1.le (lt_of_le_of_lt
          (le_trans (add_le_add (le_refl 1) (normal_inflationary powOmega_normal _ (complete a)))
            (additively_closed_collapse (powOmega_additively_closed (complete a))
              (lt_of_le_of_lt (pow_zero ω).ge (pow_lt_pow_right omega_gt1 ((VF_nonzero a).2 h'.1.1)))))
          (pow_lt_pow_right omega_gt1 h'.2.2.2.1)))
        (fun h => VForm.noConfusion h)
    | N ((Z, _) :: (_, _) :: _), hP => (not_lt_zero' hP.1.2.1.2.2.1).elim
    | N [(N [], a)], hP =>
      have h' := (isNormal_N _).1 hP.1
      lt_powOmega_wrap _ hP.1 (lt_of_le_of_lt (expOmega_denote a).ge (pow_lt_pow_right omega_gt1 h'.2.2.2.1))
        (fun h => VForm.noConfusion h)
    | N [(N [], a), (b, y)], hP =>
      have h' := (isNormal_N _).1 hP.1
      have hb : denote b ≈ 0 :=
        equiv_intro (le_zero_of_lt_one (lt_of_lt_of_le h'.2.1.2.2.1 (add_zero 1).le)) (zero_least _)
      lt_powOmega_wrap _ hP.1 (lt_of_le_of_lt (denote_two a b y hb).le
          (powOmega_additively_closed (complete _) _ _ (pow_lt_pow_right omega_gt1 h'.2.2.2.1)
            (lt_of_lt_of_le h'.2.2.2.2.1 (normal_inflationary powOmega_normal _ (complete _)))))
        (fun h => VForm.noConfusion h)
    | N ((N [], _) :: (_, _) :: (_, _) :: _), hP =>
      (not_lt_zero' (lt_of_lt_of_le hP.1.2.1.2.2.2.2.2.1
        (le_zero_of_lt_one (lt_of_lt_of_le hP.1.2.1.2.2.1 (add_zero 1).le)))).elim
    | N ((N ((b', a') :: lb), a) :: l), hP =>
      have h' := (isNormal_N _).1 hP.1
      have hb := (isNormal_N _).1 h'.2.2.1.1.1
      ⟨hP.1, equiv_intro
        (le_trans (add_zero _).le (schutte_matrix_epsilon _ a l ((VF_nonzero a).2 h'.1.1)
          (one_lt_index b' a' lb hb.1.1)))
        (le_trans (normal_inflationary powOmega_normal _ (complete _)) (add_zero _).ge)⟩
  | x :: x' :: xs', hP, hord => by
    have ih := recompose_correct (x' :: xs') hP.2 hord.2
    have hr := recompose_ne_Z x' xs'
    cases x with
    | Z =>
      -- all the terms are zero, so the sum is finite
      have hx' : denote x' ≈ 0 := equiv_intro hord.1 (zero_least _)
      have hfin := leading_zero_finite (f := denote) xs' x' hord.2 hx'
      have h1 := denote_Za (recompose (x' :: xs'))
      refine ⟨⟨⟨hr, trivial⟩, ⟨trivial, normal_proper _ ih.1, trivial⟩, ⟨trivial, ih.1, trivial⟩, ?_, trivial⟩, ?_⟩
      · refine lt_of_lt_of_le ?_ h1.ge
        refine lt_of_le_of_lt (equiv_trans (equiv_symm ih.2) hfin).le
          (lt_of_lt_of_le ?_ (add_le_add (le_refl 1) (equiv_trans (equiv_symm ih.2) hfin).ge))
        exact lt_of_lt_of_le (succ_lt _) (onePlus_finite_succ _).ge
      · exact equiv_trans (add_congr (pow_zero ω) ih.2) (equiv_symm h1)
    | N l =>
      have h2 := denote_two (N l) Z (recompose (x' :: xs')) (equiv_refl 0)
      have hr₀ := (VF_nonzero _).2 hr
      refine ⟨⟨⟨fun h => VForm.noConfusion h, hr, trivial⟩,
          ⟨trivial, normal_proper _ hP.1, N_pos [], trivial, normal_proper _ ih.1, trivial⟩,
          ⟨one_normal, hP.1, trivial, ih.1, trivial⟩, ?_, ?_, trivial⟩,
        equiv_trans (add_congr (equiv_refl _) ih.2) (equiv_symm h2)⟩
      · exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans
          (normal_inflationary powOmega_normal _ (complete _)) (add_zero _).ge) (add_lt_add_left _ hr₀))
          h2.ge
      · exact lt_of_lt_of_le (lt_of_le_of_lt ih.2.ge (lt_of_lt_of_le
          (cantor_tail_lt (N l) (x' :: xs') hord) (add_le_add (le_refl _) ih.2.le))) h2.ge

open CantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_has_cantor_decomposition`. -/
def hasCantorDecomposition : HasCantorDecomposition denote IsNormal where
  compare := compare
  decompose := decompose
  recompose := recompose
  complete := complete
  compare_correct x y hx hy := compare_correct x y (normal_proper x hx) (normal_proper y hy)
  decompose_correct := decompose_correct
  recompose_correct := recompose_correct

/-- Rocq: `Notation.SchutteMatrix.VF_succ`. -/
def succ : VForm → VForm := cantorSucc hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_add`. -/
def add : VForm → VForm → VForm := cantorAdd hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_mul`. -/
def mul : VForm → VForm → VForm := cantorMul hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_exp`. -/
def exp : VForm → VForm → VForm := cantorExp hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_succ_reflects`. -/
theorem succ_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Ordinal.succ succ :=
  cantor_succ_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_add_reflects`. -/
theorem add_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· + ·) add :=
  cantor_add_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_mul_reflects`. -/
theorem mul_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· * ·) mul :=
  cantor_mul_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_exp_reflects`. -/
theorem exp_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ^ ·) exp :=
  cantor_exp_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_one`. -/
def one : VForm := N []

/-- Rocq: `Notation.SchutteMatrix.VF_two`. -/
def two : VForm := N [(Z, one)]

/-- Rocq: `Notation.SchutteMatrix.VF_three`. -/
def three : VForm := N [(Z, two)]

/-- Rocq: `Notation.SchutteMatrix.VF_omega`. -/
def omega : VForm := N [(one, one)]

/-- Rocq: `Notation.SchutteMatrix.VF_SAO`. -/
def SAO : VForm := N [(two, omega)]

/-- Rocq: `Notation.SchutteMatrix.VF_LAO`. -/
def LAO : VForm := N [(three, one)]

/-- Rocq: `Notation.SchutteMatrix.VF_SVO`. -/
def SVO : VForm := N [(omega, one)]

/-- Rocq: `Notation.SchutteMatrix.VF_nat`. -/
def nat : Nat → VForm
  | 0 => Z
  | 1 => N []
  | n + 2 => N [(Z, nat (n + 1))]

/-- Rocq: `Notation.SchutteMatrix.VF_nat_eq`. -/
theorem nat_eq : ∀ n : Nat, denote (nat n) ≈ ofNat n
  | 0 => equiv_refl _
  | 1 => add_zero 1
  | n + 2 => equiv_trans (denote_Za _) (equiv_trans (add_congr (equiv_refl 1) (nat_eq (n + 1)))
      (onePlus_finite_succ (n + 1)))

/-- Rocq: `Notation.SchutteMatrix.VF_nat_normal`. -/
theorem nat_normal : ∀ n : Nat, IsNormal (nat n)
  | 0 => trivial
  | 1 => one_normal
  | n + 2 => ⟨⟨by cases n <;> exact fun h => VForm.noConfusion h, trivial⟩,
      ⟨trivial, normal_proper _ (nat_normal (n + 1)), trivial⟩, ⟨trivial, nat_normal (n + 1), trivial⟩,
      ⟨lt_of_le_of_lt (nat_eq (n + 1)).le (lt_of_lt_of_le (succ_lt _) (nat_eq (n + 2)).ge), trivial⟩⟩

/-- Rocq: `Notation.SchutteMatrix.VF_natOrdSize_reflects`. -/
theorem natOrdSize_reflects (n : Nat) : Reflects VForm denote IsNormal .ord (ofNat n) (nat n) :=
  ⟨equiv_symm (nat_eq n), nat_normal n⟩

theorem omega_eq : denote omega ≈ ω :=
  equiv_trans (column_congr onePlus_normal.monotone (add_zero 1) (add_zero 1) (equiv_refl 0))
    (equiv_trans (column_one 1 0 (ofNat_complete 1) zero_complete)
      (equiv_trans (add_zero _) (pow_one' omega_gt0)))

/-- Rocq: `Notation.SchutteMatrix.VF_SVO_eq`. -/
theorem SVO_eq : denote SVO ≈ SmallVeblenOrdinal :=
  equiv_trans (column_congr onePlus_normal.monotone omega_eq (add_zero 1) (equiv_refl 0))
    (equiv_symm SVO_alt)

/-- Rocq: `Notation.SchutteMatrix.VF_SmallVeblenOrdinal`. -/
theorem SmallVeblenOrdinal_reflects : Reflects VForm denote IsNormal .ord SmallVeblenOrdinal SVO :=
  ⟨equiv_symm SVO_eq, by decide⟩

/-! ## Interpolants -/

theorem has_interpolants_zero : HasInterpolants denote IsNormal 0 :=
  (has_interpolants_unfold _).2 fun i hi => (lt_irrefl i (lt_of_lt_of_le hi (zero_least i))).elim

/-- Induction on the denotation of a form. -/
private theorem measure_ind {motive : VForm → Prop}
    (h : ∀ a, (∀ b, denote b < denote a → motive b) → motive a) (a : VForm) : motive a :=
  ltRec (motive := fun o => ∀ a, denote a ≤ o → motive a)
    (fun _ ih a ha => h a fun b hb => ih (denote b) (lt_of_lt_of_le hb ha) b (le_refl _))
    (denote a) a (le_refl _)

private abbrev HI : Ordinal.{0} → Prop := HasInterpolants denote IsNormal

/-- Columns over pointwise equivalent monotone functions are equivalent. -/
private theorem col_congr {g g' : Ordinal.{0} → Ordinal.{0}} (hg : ∀ a b, a ≤ b → g a ≤ g b)
    (hg' : ∀ a b, a ≤ b → g' a ≤ g' b) (h : ∀ z, g z ≈ g' z) (β α x : Ordinal.{0}) :
    schutteColumn g β α x ≈ schutteColumn g' β α x :=
  equiv_intro
    (schutte_column_monotone_func g g' β α x α x hg hg' (fun z => (h z).le) (le_refl _) (le_refl _))
    (schutte_column_monotone_func g' g β α x α x hg' hg (fun z => (h z).ge) (le_refl _) (le_refl _))

/-- Matrices over pointwise equivalent monotone functions are equivalent. -/
private theorem matrix_func_congr {g g' : Ordinal.{0} → Ordinal.{0}} (hg : ∀ a b, a ≤ b → g a ≤ g b)
    (hg' : ∀ a b, a ≤ b → g' a ≤ g' b) (h : ∀ z, g z ≈ g' z) (m : List (Ordinal.{0} × Ordinal.{0}))
    (x : Ordinal.{0}) : schutteMatrix g m x ≈ schutteMatrix g' m x :=
  equiv_intro (schutte_matrix_monotone_func m g g' x hg hg' (fun z => (h z).le))
    (schutte_matrix_monotone_func m g' g x hg' hg (fun z => (h z).ge))

/-- The statement of `schutte_column_matrix_interpolants` for one column
index `b`. -/
private def ColumnInterp (b : VForm) : Prop :=
  ∀ (xs : List (VForm × VForm)) (p : Ordinal.{0}),
    p ≤ LargeVeblenOrdinal → IsProper b → HI (denote b) → denote b < finalIndex p (matrixDenote xs) →
    SchutteMatrixProper (matrixDenote xs) p LargeVeblenOrdinal →
    Each (fun x => IsProper x.1 ∧ IsProper x.2) xs →
    NormalFunction (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) →
    (∀ x, Complete x → HI x → HI (schutteMatrix (fun y => 1 + y) (matrixDenote xs) x)) →
    (∀ a : VForm, IsProper a → HI (denote a) → ∀ x, Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) x)) ∧
    (∀ a, Complete a → HI a →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) a 0))

/-- Rocq: `Notation.SchutteMatrix.schutte_column_matrix_interpolants`. -/
theorem schutte_column_matrix_interpolants : ∀ (b : VForm) (xs : List (VForm × VForm)) (p : Ordinal.{0}),
    p ≤ LargeVeblenOrdinal → IsProper b → HasInterpolants denote IsNormal (denote b) →
    denote b < finalIndex p (matrixDenote xs) →
    SchutteMatrixProper (matrixDenote xs) p LargeVeblenOrdinal →
    Each (fun x => IsProper x.1 ∧ IsProper x.2) xs →
    NormalFunction (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) →
    (∀ x, Complete x → HasInterpolants denote IsNormal x →
      HasInterpolants denote IsNormal (schutteMatrix (fun y => 1 + y) (matrixDenote xs) x)) →
    (∀ a : VForm, IsProper a → HasInterpolants denote IsNormal (denote a) → ∀ x, Complete x →
      HasInterpolants denote IsNormal x →
      HasInterpolants denote IsNormal
        (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) x)) ∧
    (∀ a, Complete a → HasInterpolants denote IsNormal a →
      HasInterpolants denote IsNormal
        (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) a 0)) := by
  intro b
  refine measure_ind (motive := ColumnInterp) (fun b ihb => ?_) b
  intro xs p hp hb₁ hb₂ hb₃ hxs₂ hxs hf hxs₄
  have hmono := hf.monotone
  -- Extending the matrix by one more column `(b, c)`.
  have hext : ∀ c : VForm,
      SchutteMatrixProper (matrixDenote (xs ++ [(b, c)])) p LargeVeblenOrdinal ∧
      finalIndex p (matrixDenote (xs ++ [(b, c)])) = denote b ∧
      ∀ z, schutteMatrix (fun y => 1 + y) (matrixDenote (xs ++ [(b, c)])) z ≈
        schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote c) z := by
    intro c
    rw [matrix_denote_app]
    refine ⟨(schutte_matrix_proper_app _ _ _ _).2 ⟨hxs₂, hb₃, bounded c, trivial⟩,
      final_index_last _ _ _ _, fun z => ?_⟩
    rw [schutte_matrix_app]; exact equiv_refl _
  have heach : ∀ c : VForm, IsProper c → Each (fun x => IsProper x.1 ∧ IsProper x.2) (xs ++ [(b, c)]) :=
    fun _ hc => (CantorDecomposition.each_app _ _ _).2 ⟨hxs, ⟨hb₁, hc⟩, trivial⟩
  have colN : ∀ c : VForm, NormalFunction
      (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote c)) :=
    fun c => schutte_column_normal _ _ _ (complete b) (complete c) hf
  -- The first conjunct.
  have main : ∀ a : VForm, IsProper a → HI (denote a) → ∀ x, Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) x) := by
    intro a
    refine measure_ind (motive := fun a => IsProper a → HI (denote a) → ∀ x, Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) x))
      (fun a iha ha₀ ha₁ => ?_) a
    intro x
    refine ltRec (motive := fun x => Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) x))
      (fun x ihx hx₁ hx₂ => ?_) x
    rw [schutte_column_unroll]
    refine has_interpolants_lub _ _ ?_ ((has_interpolants_unfold _).2 fun i hi => ?_)
    · have hna := normalize_correct a ha₀
      refine hxs₄ _ (add_complete (complete a) hx₁)
        ((has_interpolants_eq_mor (add_congr hna.1 (equiv_refl x))).1 ?_)
      exact has_interpolants_add add add_reflects (normalize a) x hna.2
        ((has_interpolants_eq_mor hna.1).2 ha₁) hx₂
    obtain ⟨b', hi⟩ := sup_lt hi
    obtain ⟨a', hi⟩ := sup_lt hi
    obtain ⟨bq, hbq₁, hbq₂, hbq₃, hbq₄⟩ :=
      (has_interpolants_unfold _).1 hb₂ ((denote b) b') (index_lt _ b')
    obtain ⟨aq, haq₁, haq₂, haq₃, haq₄⟩ :=
      (has_interpolants_unfold _).1 ha₁ ((denote a) a') (index_lt _ a')
    have hcN := colN a
    -- the limit below `x`
    have hlimc : Complete (lim fun i : x.Carrier =>
        schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) (x i)) :=
      lim_complete (fun i => hcN.complete _ (complete_subord hx₁ i))
        (directed_monotone x _ (fun _ _ h => hcN.monotone _ _ h) hx₁) (cast (complete_unfold x) hx₁).2.1
    have hlim : HI (lim fun i : x.Carrier =>
        schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) (x i)) := by
      refine (has_interpolants_unfold _).2 fun j hj => ?_
      obtain ⟨x', hj⟩ := lt_elim hj
      obtain ⟨xq, hxq₁, hxq₂, hxq₃, hxq₄⟩ := (has_interpolants_unfold _).1 hx₂ (x x') (index_lt x x')
      have hb0 : 0 < denote b := lt_of_le_of_lt (zero_least _) (index_lt _ b')
      have hyp : IsProper (N (xs ++ [(b, a), (Z, xq)])) := by
        refine (matrix_proper_correct _).2 ⟨(CantorDecomposition.each_app _ _ _).2
          ⟨hxs, ⟨hb₁, ha₀⟩, ⟨trivial, normal_proper _ hxq₁⟩, trivial⟩, ?_⟩
        rw [matrix_denote_app]
        exact (schutte_matrix_proper_app _ _ _ _).2
          ⟨schutte_matrix_proper_monotone _ _ _ _ _ hp (le_refl _) hxs₂,
            lt_of_lt_of_le hb₃ (final_index_monotone _ _ _ hp), bounded a, hb0, bounded xq, trivial⟩
      have hny := normalize_correct _ hyp
      have hy' : denote (normalize (N (xs ++ [(b, a), (Z, xq)]))) ≈
          schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) (denote xq) := by
        refine equiv_trans hny.1 ?_
        show schutteMatrix _ (matrixDenote (xs ++ [(b, a), (Z, xq)])) 0 ≈ _
        rw [matrix_denote_app, schutte_matrix_app]
        exact equiv_trans (schutte_column0 _ _ 0) (equiv_intro (hcN.monotone _ _ (add_zero _).le)
          (hcN.monotone _ _ (add_zero _).ge))
      obtain ⟨x'', hx''⟩ := lt_elim hxq₃
      exact ⟨normalize _, hny.2, le_trans hj (le_trans (hcN.monotone _ _ hxq₂) hy'.ge),
        lt_intro (show (lim fun i : x.Carrier => schutteColumn (schutteMatrix (fun y => 1 + y)
          (matrixDenote xs)) (denote b) (denote a) (x i)).Carrier from x'')
          (le_trans hy'.le (hcN.monotone _ _ hx'')),
        (has_interpolants_eq_mor hy').2 (ihx _ hxq₃ (complete xq) hxq₄)⟩
    -- the fixpoint above the limit, for the column at `aq`
    obtain ⟨he₁, he₂, he₄⟩ := hext aq
    have hN' := matrix_normal (xs ++ [(b, aq)]) onePlus_normal
    have hIH := (ihb bq hbq₃ (xs ++ [(b, aq)]) p hp (normal_proper _ hbq₁) hbq₄ (by rw [he₂]; exact hbq₃)
      he₁ (heach aq (normal_proper _ haq₁)) hN'
      (fun x hx hxI => (has_interpolants_eq_mor (he₄ x)).2
        (iha aq haq₃ (normal_proper _ haq₁) haq₄ x hx hxI))).2
    have hIH : ∀ c, Complete c → HI c → HI (schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
        (matrixDenote xs)) (denote b) (denote aq)) (denote bq) c 0) := fun c hc hcI =>
      (has_interpolants_eq_mor (col_congr hN'.monotone (colN aq).monotone he₄ _ _ _)).1 (hIH c hc hcI)
    have hgN := schutte_column_normal_arg (denote bq) _ (complete bq) (colN aq)
    have hfix : HI (fixOrd (fun δ => schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
        (matrixDenote xs)) (denote b) (denote aq)) (denote bq) δ 0) (lim fun i : x.Carrier =>
          schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) (x i))) := by
      refine has_interpolants_sup _ _ fun m => ?_
      induction m.down with
      | zero => exact hlim
      | succ m ihm => exact hIH _ (iterF_complete m _ hlimc hgN.complete) ihm
    have hi' := lt_of_lt_of_le hi (fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono haq₂ (le_refl z))
        hbq₂ (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN.monotone _ _ h) _)
    obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
    obtain ⟨aq', haq'⟩ := lt_elim haq₃
    obtain ⟨bq', hbq'⟩ := lt_elim hbq₃
    refine ⟨z, hz₁, hz₂, lt_of_lt_of_le hz₃ ?_, hz₄⟩
    refine le_trans ?_ (sup_le _ bq')
    refine le_trans ?_ (sup_le (fun a' => fixOrd (fun δ => schutteColumn (schutteColumn
      (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) ((denote a) a')) ((denote b) bq') δ 0)
      (lim fun i : x.Carrier => schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs))
        (denote b) (denote a) (x i))) aq')
    have hgN' := schutte_column_normal_arg ((denote b) bq') _ (complete_subord (complete b) bq')
      (schutte_column_normal _ _ _ (complete b) (complete_subord (complete a) aq') hf)
    exact fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono haq' (le_refl z))
        hbq' (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN'.monotone _ _ h) _
  -- The second conjunct.
  refine ⟨main, fun a => ?_⟩
  refine ltRec (motive := fun a => Complete a → HI a →
    HI (schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) a 0))
    (fun a _ ha₁ ha₂ => ?_) a
  rw [schutte_column_unroll]
  refine has_interpolants_lub _ _ (hxs₄ _ (add_complete ha₁ zero_complete)
    ((has_interpolants_eq_mor (add_zero a)).2 ha₂)) ((has_interpolants_unfold _).2 fun i hi => ?_)
  obtain ⟨b', hi⟩ := sup_lt hi
  obtain ⟨a', hi⟩ := sup_lt hi
  obtain ⟨bq, hbq₁, hbq₂, hbq₃, hbq₄⟩ := (has_interpolants_unfold _).1 hb₂ ((denote b) b') (index_lt _ b')
  obtain ⟨aq, haq₁, haq₂, haq₃, haq₄⟩ := (has_interpolants_unfold _).1 ha₂ (a a') (index_lt a a')
  obtain ⟨he₁, he₂, he₄⟩ := hext aq
  have hN' := matrix_normal (xs ++ [(b, aq)]) onePlus_normal
  have hIH := (ihb bq hbq₃ (xs ++ [(b, aq)]) p hp (normal_proper _ hbq₁) hbq₄ (by rw [he₂]; exact hbq₃)
    he₁ (heach aq (normal_proper _ haq₁)) hN'
    (fun x hx hxI => (has_interpolants_eq_mor (he₄ x)).2 (main aq (normal_proper _ haq₁) haq₄ x hx hxI))).2
  have hIH : ∀ c, Complete c → HI c → HI (schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
      (matrixDenote xs)) (denote b) (denote aq)) (denote bq) c 0) := fun c hc hcI =>
    (has_interpolants_eq_mor (col_congr hN'.monotone (colN aq).monotone he₄ _ _ _)).1 (hIH c hc hcI)
  have hgN := schutte_column_normal_arg (denote bq) _ (complete bq) (colN aq)
  have hfix : HI (fixOrd (fun δ => schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
      (matrixDenote xs)) (denote b) (denote aq)) (denote bq) δ 0) 0) := by
    refine has_interpolants_sup _ _ fun m => ?_
    induction m.down with
    | zero => exact has_interpolants_zero
    | succ m ihm => exact hIH _ (iterF_complete m _ zero_complete hgN.complete) ihm
  have ha'N := schutte_column_normal_arg ((denote b) b') _ (complete_subord (complete b) b')
    (schutte_column_normal _ _ _ (complete b) (complete_subord ha₁ a') hf)
  have hL : (lim fun i : (0 : Ordinal.{0}).Carrier => schutteColumn (schutteMatrix (fun y => 1 + y)
      (matrixDenote xs)) (denote b) a ((0 : Ordinal.{0}) i)) ≤ 0 := limit_least fun i => nomatch i
  have hi' := lt_of_lt_of_le hi (le_trans (fixOrd_monotone (fun _ _ h => ha'N.monotone _ _ h) hL)
    (fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono haq₂ (le_refl z))
        hbq₂ (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN.monotone _ _ h) 0))
  obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
  obtain ⟨aq', haq'⟩ := lt_elim haq₃
  obtain ⟨bq', hbq'⟩ := lt_elim hbq₃
  refine ⟨z, hz₁, hz₂, lt_of_lt_of_le hz₃ ?_, hz₄⟩
  refine le_trans ?_ (sup_le _ bq')
  refine le_trans ?_ (sup_le (fun a' => fixOrd (fun δ => schutteColumn (schutteColumn
    (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (a a')) ((denote b) bq') δ 0)
    (lim fun i : (0 : Ordinal.{0}).Carrier => schutteColumn (schutteMatrix (fun y => 1 + y)
      (matrixDenote xs)) (denote b) a ((0 : Ordinal.{0}) i))) aq')
  have hgN' := schutte_column_normal_arg ((denote b) bq') _ (complete_subord (complete b) bq')
    (schutte_column_normal _ _ _ (complete b) (complete_subord ha₁ aq') hf)
  exact le_trans (fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono haq' (le_refl z))
        hbq' (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN'.monotone _ _ h) 0)
    (fixOrd_monotone (fun _ _ h => hgN'.monotone _ _ h) (zero_least _))

/-- Rocq: `Notation.SchutteMatrix.schutte_matrix_interpolants_aux`. -/
theorem schutte_matrix_interpolants_aux : ∀ (ys xs : List (VForm × VForm)) (p : Ordinal.{0}),
    p ≤ LargeVeblenOrdinal → SchutteMatrixProper (matrixDenote xs) p LargeVeblenOrdinal →
    Each (fun x => IsProper x.1 ∧ IsProper x.2) xs →
    (∀ x, Complete x → HasInterpolants denote IsNormal x →
      HasInterpolants denote IsNormal (schutteMatrix (fun y => 1 + y) (matrixDenote xs) x)) →
    SchutteMatrixProper (matrixDenote ys) (finalIndex p (matrixDenote xs)) LargeVeblenOrdinal →
    Each (fun x => IsNormal x.1 ∧ IsNormal x.2) ys →
    Each (fun x => HasInterpolants denote IsNormal (denote x.1) ∧
      HasInterpolants denote IsNormal (denote x.2)) ys →
    HasInterpolants denote IsNormal
      (schutteMatrix (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (matrixDenote ys) 0)
  | [], _, _, _, _, _, hf, _, _, _ => hf 0 zero_complete has_interpolants_zero
  | (b, a) :: ys, xs, p, hp, hxs₂, hxs, hf, hys₁, hys₂, hys₃ => by
    have hF := matrix_normal xs onePlus_normal
    have hcolN := schutte_column_normal (denote b) (denote a) _ (complete b) (complete a) hF
    have hext : ∀ z, schutteMatrix (fun y => 1 + y) (matrixDenote (xs ++ [(b, a)])) z ≈
        schutteColumn (schutteMatrix (fun y => 1 + y) (matrixDenote xs)) (denote b) (denote a) z := by
      intro z
      rw [matrix_denote_app, schutte_matrix_app]
      exact equiv_refl _
    have hN' := matrix_normal (xs ++ [(b, a)]) onePlus_normal
    have hih := schutte_matrix_interpolants_aux ys (xs ++ [(b, a)]) p hp
      (by
        rw [matrix_denote_app]
        exact (schutte_matrix_proper_app _ _ _ _).2 ⟨hxs₂, hys₁.1, hys₁.2.1, trivial⟩)
      ((CantorDecomposition.each_app _ _ _).2
        ⟨hxs, ⟨normal_proper _ hys₂.1.1, normal_proper _ hys₂.1.2⟩, trivial⟩)
      (fun x hx hxI => (has_interpolants_eq_mor (hext x)).2
        ((schutte_column_matrix_interpolants b xs p hp (normal_proper _ hys₂.1.1) hys₃.1.1 hys₁.1 hxs₂ hxs
          hF hf).1 a (normal_proper _ hys₂.1.2) hys₃.1.2 x hx hxI))
      (by
        rw [matrix_denote_app]
        show SchutteMatrixProper _ (finalIndex p (matrixDenote xs ++ [(denote b, denote a)])) _
        rw [final_index_last]
        exact hys₁.2.2)
      hys₂.2 hys₃.2
    exact (has_interpolants_eq_mor (matrix_func_congr hN'.monotone hcolN.monotone hext _ 0)).1 hih

/-- Rocq: `Notation.SchutteMatrix.schutte_matrix_interpolants`. -/
theorem schutte_matrix_interpolants (ys : List (VForm × VForm)) (hp : MatrixProper ys)
    (hn : Each (fun x => IsNormal x.1 ∧ IsNormal x.2) ys)
    (hi : Each (fun x => HasInterpolants denote IsNormal (denote x.1) ∧
      HasInterpolants denote IsNormal (denote x.2)) ys) :
    HasInterpolants denote IsNormal (schutteMatrix (fun y => 1 + y) (matrixDenote ys) 0) :=
  schutte_matrix_interpolants_aux ys [] LargeVeblenOrdinal (le_refl _) trivial trivial
    (fun x _ hx => onePlus_interpolants Z ⟨equiv_refl 0, trivial⟩ (add one)
      (fun x a h => add_reflects 1 one ⟨equiv_symm (add_zero 1), one_normal⟩ x a h) x hx)
    ((matrix_proper_correct ys).1 hp).2 hn hi

private theorem each_of_mem {α : Type} {P : α → Prop} : ∀ l : List α, (∀ x, x ∈ l → P x) → Each P l
  | [], _ => trivial
  | x :: l, h => ⟨h x (.head _), each_of_mem l fun y hy => h y (.tail _ hy)⟩

private theorem sparse_mem : ∀ {l : List (VForm × VForm)} {b a : VForm}, IsSparse l → (b, a) ∈ l → a ≠ Z
  | (_, _) :: _, _, _, h, .head _ => h.1
  | (_, _) :: _, _, _, h, .tail _ hm => sparse_mem h.2 hm

/-- Rocq: `Notation.SchutteMatrix.schutte_matrix_has_all_interpolants`. -/
theorem schutte_matrix_has_all_interpolants : HasAllInterpolants denote IsNormal := by
  intro a
  refine measure_ind (motive := fun a => IsNormal a → HasInterpolants denote IsNormal (denote a))
    (fun a ih ha => ?_) a
  cases a with
  | Z => exact has_interpolants_zero
  | N l =>
    have h := (isNormal_N l).1 ha
    refine schutte_matrix_interpolants l h.2.1 h.2.2.1 (each_of_mem l fun p hp => ?_)
    match p, hp with
    | (b, a'), hp =>
      have hn := each_mem (P := fun x => IsNormal x.1 ∧ IsNormal x.2) h.2.2.1 hp
      exact ⟨ih b (matrix_index_lt l b a' h.2.1 hp ((VF_nonzero a').2 (sparse_mem h.1 hp))) hn.1,
        ih a' (each_mem (P := fun x => denote x.2 < denote (N l)) h.2.2.2 hp) hn.2⟩

/-- Rocq: `Notation.SchutteMatrix.VF_nadd`. -/
def nadd : VForm → VForm → VForm := cantorNadd hasCantorDecomposition

/-- Rocq: `Notation.SchutteMatrix.VF_reflects_nadd`. -/
theorem reflects_nadd : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ♯ ·) nadd :=
  cantor_nadd_reflects hasCantorDecomposition schutte_matrix_has_all_interpolants

/-- With the excluded middle, every ordinal below the large Veblen ordinal has
a unique normal form. Rocq's `exists!` is spelled out.
Rocq: `Notation.SchutteMatrix.VF_has_enough_notations`. -/
theorem has_enough_notations (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < LargeVeblenOrdinal →
      ∃ a : VForm, (IsNormal a ∧ denote a ≈ x) ∧ ∀ a', IsNormal a' ∧ denote a' ≈ x → a' = a := by
  intro x hx
  obtain ⟨b, hb₁, hb₂⟩ := LVO_proper_VForm x hx
  have hn := normalize_correct b hb₁
  obtain ⟨c, hc₁, hc₂⟩ := has_interpolants_has_enough_notations em schutte_matrix_has_all_interpolants
    (normalize b) x hn.2 (le_trans hb₂ hn.1.ge)
  exact ⟨c, ⟨hc₁, hc₂⟩, fun a' ⟨ha₁, ha₂⟩ =>
    normal_form_unique a' c ha₁ hc₁ (equiv_trans ha₂ (equiv_symm hc₂))⟩

/-! ## Sample computations -/

/-- `3 < ω < SVO`, and dropping zero arguments and normalizing the entries of
`N [(1, N [(Z, Z)]), (Z, Z)]` yields `ω` (checked by kernel reduction). -/
theorem sample_compare : compare (nat 3) omega = .lt ∧ compare omega SVO = .lt ∧
    normalize (N [(one, N [(Z, Z)]), (Z, Z)]) = omega := ⟨rfl, rfl, rfl⟩

end VForm

end ConstructiveOrdinals.SchutteMatrixNotation
