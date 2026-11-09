import ConstructiveOrdinals.Notation.CantorDecomposition
import ConstructiveOrdinals.Notation.CantorProduct
import ConstructiveOrdinals.Schutte.ColumnFacts
import ConstructiveOrdinals.Prelude.Relations

/-!
# Schütte stacks: a notation system for the small Veblen ordinal

Port of `Ordinal/Notation/SchutteStack.v`.

A form `N [x₁, …, xₙ]` denotes the Schütte stack
`schutteStack (1 + ·) [x₁, …, xₙ] 0`: the column with index `n - i` has
argument `xᵢ`. The normal forms denote exactly the ordinals below the small
Veblen ordinal. Comparison converts stacks to sparse matrices (dropping zero
arguments) and runs the matrix comparison of `Schutte/ColumnFacts`.
Normalization is a confluent, strongly normalizing rewriting system, and the
system has a Cantor decomposition, all interpolants, and (with the excluded
middle) a unique notation for every ordinal below the small Veblen ordinal.

Lean notes:

- Rocq defines the comparison `VF_compare_loop` by well-founded recursion on
  the combined term size, through the dependently typed `check_lt` and
  `sparse_compare`, which carry their correctness proofs. Here `checkLt`,
  `sparseCompare` and `compareFuel` are plain functions, recursing on explicit
  fuel in the last case, so that `compare` computes in the kernel. Their
  correctness lemmas are stated separately. The fuel is the term size, and
  the correctness proof only needs each entry of a stack to be smaller than the
  stack itself; Rocq instead threads explicit size budgets.
- `VF_denote` maps over the list of subterms. Here that map is the mutually
  recursive `denoteList`, equal to `List.map denote`; likewise for normality
  (`IsNormalList`) and normalization (`normalizeList`).
- `∃!` (not in Lean core) is spelled out as existence plus uniqueness.
-/

namespace ConstructiveOrdinals.SchutteStackNotation

open Ordinal

universe u

/-- Forms. Rocq: `Notation.SchutteStack.VForm`. -/
inductive VForm : Type where
  | Z : VForm
  | N : List VForm → VForm

namespace VForm

mutual
/-- Rocq: `Notation.SchutteStack.VF_termSize`. -/
def termSize : VForm → Nat
  | Z => 0
  | N l => listSize l + 1

/-- Rocq: `Notation.SchutteStack.VF_listSize`. -/
def listSize : List VForm → Nat
  | [] => 0
  | x :: xs => termSize x + listSize xs + 1
end

mutual
/-- Rocq: `Notation.SchutteStack.VF_denote`. -/
def denote : VForm → Ordinal.{0}
  | Z => 0
  | N l => schutteStack (fun y => 1 + y) (denoteList l) 0

/-- `List.map denote`. -/
def denoteList : List VForm → List Ordinal.{0}
  | [] => []
  | x :: xs => denote x :: denoteList xs
end

instance : Sized VForm := ⟨denote⟩

theorem denoteList_eq_map : ∀ l : List VForm, denoteList l = l.map denote
  | [] => rfl
  | x :: xs => congrArg (denote x :: ·) (denoteList_eq_map xs)

theorem denoteList_length : ∀ l : List VForm, (denoteList l).length = l.length
  | [] => rfl
  | _ :: xs => congrArg (· + 1) (denoteList_length xs)

theorem denoteList_append : ∀ l₁ l₂ : List VForm,
    denoteList (l₁ ++ l₂) = denoteList l₁ ++ denoteList l₂
  | [], _ => rfl
  | x :: l₁, l₂ => congrArg (denote x :: ·) (denoteList_append l₁ l₂)

mutual
private theorem induction_aux (P : VForm → Prop) (hZ : P Z)
    (hN : ∀ xs, Each P xs → P (N xs)) : ∀ x, P x
  | Z => hZ
  | N xs => hN xs (induction_list P hZ hN xs)

private theorem induction_list (P : VForm → Prop) (hZ : P Z)
    (hN : ∀ xs, Each P xs → P (N xs)) : ∀ xs : List VForm, Each P xs
  | [] => trivial
  | x :: xs => ⟨induction_aux P hZ hN x, induction_list P hZ hN xs⟩
end

/-- Induction with a hypothesis for every element of the list.
Rocq: `Notation.SchutteStack.VForm_induction`. -/
theorem induction' (P : VForm → Prop) (hZ : P Z) (hN : ∀ xs, Each P xs → P (N xs)) :
    ∀ x, P x :=
  induction_aux P hZ hN

mutual
/-- Rocq: `Notation.SchutteStack.VForm_complete`. -/
theorem complete : ∀ x : VForm, Complete (denote x)
  | Z => zero_complete
  | N l => (schutte_stack_normal _ _ (each_complete l) onePlus_normal).complete 0 zero_complete

/-- Rocq: `Notation.SchutteStack.VForm_each_complete`. -/
theorem each_complete : ∀ xs : List VForm, Each Complete (denoteList xs)
  | [] => trivial
  | x :: xs => ⟨complete x, each_complete xs⟩
end

/-- Rocq: `Notation.SchutteStack.VForm_list_complete`. -/
theorem list_complete (xs : List VForm) : ListComplete (denoteList xs) := each_complete xs

/-- The stack function of a form's list is normal. -/
theorem stack_normal (l : List VForm) {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f) :
    NormalFunction (schutteStack f (denoteList l)) :=
  schutte_stack_normal _ _ (list_complete l) hf

/-- Rocq: `Notation.SchutteStack.VF_listSize_app`. -/
theorem listSize_app : ∀ xs ys : List VForm, listSize (xs ++ ys) = listSize xs + listSize ys
  | [], ys => (Nat.zero_add _).symm
  | x :: xs, ys => by
    show termSize x + listSize (xs ++ ys) + 1 = termSize x + listSize xs + 1 + listSize ys
    rw [listSize_app xs ys, Nat.add_right_comm (termSize x + listSize xs) 1, ← Nat.add_assoc (termSize x)]

/-- Every element of a list is smaller than the form built from it. -/
theorem each_lt_termSize : ∀ l : List VForm, Each (fun a => termSize a < termSize (N l)) l
  | [] => trivial
  | _ :: xs => ⟨Nat.lt_succ_of_le (Nat.le_succ_of_le (Nat.le_add_right _ _)),
      (each_lt_termSize xs).imp fun _ h => Nat.lt_of_lt_of_le h
        (Nat.succ_le_succ (Nat.le_succ_of_le (Nat.le_add_left _ _)))⟩

theorem each_denoteList (P : Ordinal.{0} → Prop) :
    ∀ xs : List VForm, Each P (denoteList xs) ↔ Each (fun x => P (denote x)) xs
  | [] => Iff.rfl
  | _ :: xs => ⟨fun h => ⟨h.1, (each_denoteList P xs).1 h.2⟩,
      fun h => ⟨h.1, (each_denoteList P xs).2 h.2⟩⟩

/-- Rocq: `Notation.SchutteStack.VForm_bounded`. -/
theorem bounded : ∀ x : VForm, denote x < SmallVeblenOrdinal :=
  induction' _ SVO_nonzero fun xs ih =>
    SVO_stack_unreachable' _ 0 (list_complete xs) zero_complete SVO_nonzero
      ((each_denoteList _ xs).2 ih)

end VForm

/-- The ordinal of all forms. Rocq: `Notation.SchutteStack.VF`. -/
def VF : Ordinal.{0} := mk VForm VForm.denote

namespace VForm

private theorem length_replicate {α : Type u} (a : α) : ∀ i : Nat, (List.replicate i a).length = i
  | 0 => rfl
  | i + 1 => congrArg (· + 1) (length_replicate a i)

private theorem denoteList_replicate_Z : ∀ i : Nat, denoteList (List.replicate i Z) = List.replicate i 0
  | 0 => rfl
  | i + 1 => congrArg (0 :: ·) (denoteList_replicate_Z i)

private theorem stack_one_zeros (i : Nat) :
    schutteColumn (fun y => 1 + y) (ofNat i) (1 + 0) 0 ≤ denote (N (N [] :: List.replicate i Z)) := by
  show _ ≤ schutteStack (schutteColumn (fun y => 1 + y)
      (ofNat (denoteList (List.replicate i Z)).length) (1 + 0)) (denoteList (List.replicate i Z)) 0
  rw [denoteList_replicate_Z, length_replicate]
  exact (schutte_stack_zeros i _ 0 (fun _ _ h =>
    schutte_column_monotone _ _ _ _ _ _ onePlus_normal.monotone (le_refl _) h)).ge

/-- Rocq: `Notation.SchutteStack.VForm_le_SVO`. -/
theorem le_SVO : SmallVeblenOrdinal ≤ VF :=
  le_trans SVO_alt.le (le_trans (schutte_column_omega_sup _ onePlus_normal).le
    (sup_least fun i => le_trans (le_trans
      (schutte_column_monotone _ _ 1 0 (1 + 0) 0 onePlus_normal.monotone (add_zero 1).ge (le_refl 0))
      (stack_one_zeros i.down)) (index_le VF (N (N [] :: List.replicate i.down Z)))))

end VForm

/-- The forms have order type the small Veblen ordinal.
Rocq: `Notation.SchutteStack.VF_SVO`. -/
theorem VF_SVO : VF ≈ SmallVeblenOrdinal :=
  equiv_intro (limit_least fun x => VForm.bounded x) VForm.le_SVO

namespace VForm

/-! ## Active subterms and sparse stacks -/

/-- `x` is the last nonzero entry of the list.
Rocq: `Notation.SchutteStack.active_subterm`. -/
inductive ActiveSubterm : List VForm → VForm → Prop
  | last {x : VForm} {xs : List VForm} : x ≠ Z → Each (fun x => x = Z) xs → ActiveSubterm (x :: xs) x
  | later {z x : VForm} {xs : List VForm} : ActiveSubterm xs z → ActiveSubterm (x :: xs) z

/-- Rocq: `Notation.SchutteStack.active_subterm_nonzero`. -/
theorem active_subterm_nonzero {xs : List VForm} {b : VForm} : ActiveSubterm xs b → b ≠ Z
  | .last h _ => h
  | .later h => active_subterm_nonzero h

/-- Rocq: `Notation.SchutteStack.active_subterm_all_zeros`. -/
theorem active_subterm_all_zeros : ∀ {xs : List VForm} {b : VForm},
    Each (fun x => x = Z) xs → ActiveSubterm xs b → False
  | _ :: _, _, h, .last hb _ => hb h.1
  | _ :: _, _, h, .later ha => active_subterm_all_zeros h.2 ha

/-- Rocq: `Notation.SchutteStack.active_subterm_unique`. -/
theorem active_subterm_unique : ∀ {xs : List VForm} {a b : VForm},
    ActiveSubterm xs a → ActiveSubterm xs b → a = b
  | _ :: _, _, _, .last _ _, .last _ _ => rfl
  | _ :: _, _, _, .last _ h, .later hb => (active_subterm_all_zeros h hb).elim
  | _ :: _, _, _, .later ha, .last _ h => (active_subterm_all_zeros h ha).elim
  | _ :: _, _, _, .later ha, .later hb => active_subterm_unique ha hb

/-- The nonzero entries of a stack, with their column indices.
Rocq: `Notation.SchutteStack.sparse_stack`. -/
def sparseStack : List VForm → List (Nat × VForm)
  | [] => []
  | Z :: xs => sparseStack xs
  | N l :: xs => (xs.length, N l) :: sparseStack xs

/-- Rocq: `Notation.SchutteStack.sparse_matrix`. -/
def sparseMatrix : List (Nat × VForm) → List (Ordinal.{0} × Ordinal.{0})
  | [] => []
  | (b, a) :: xs => (ofNat b, denote a) :: sparseMatrix xs

/-- Rocq: `Notation.SchutteStack.sparse_term_size`. -/
def sparseTermSize : List (Nat × VForm) → Nat
  | [] => 0
  | (_, a) :: xs => termSize a + sparseTermSize xs + 1

/-- Rocq: `Notation.SchutteStack.sparse_matrix_eq`. -/
theorem sparse_matrix_eq : ∀ (xs : List VForm) (f : Ordinal.{0} → Ordinal.{0}) (x₀ : Ordinal.{0}),
    NormalFunction f → Complete x₀ →
    schutteStack f (denoteList xs) x₀ ≈ schutteMatrix f (sparseMatrix (sparseStack xs)) x₀
  | [], _, _, _, _ => equiv_refl _
  | Z :: xs, f, x₀, hf, hx₀ =>
    equiv_trans (schutte_stack_leading_zero f (denoteList xs) x₀ hf)
      (sparse_matrix_eq xs f x₀ hf hx₀)
  | N l :: xs, f, x₀, hf, hx₀ => by
    show schutteStack (schutteColumn f (ofNat (denoteList xs).length) (denote (N l))) (denoteList xs) x₀ ≈
      schutteMatrix (schutteColumn f (ofNat xs.length) (denote (N l))) (sparseMatrix (sparseStack xs)) x₀
    rw [denoteList_length]
    exact sparse_matrix_eq xs _ x₀ (schutte_column_normal _ _ f (ofNat_complete _) (complete _) hf) hx₀

/-- Rocq: `Notation.SchutteStack.sparse_matrix_size`. -/
theorem sparse_matrix_size : ∀ xs : List VForm, sparseTermSize (sparseStack xs) ≤ listSize xs
  | [] => Nat.le_refl 0
  | Z :: xs => Nat.le_succ_of_le (Nat.le_trans (sparse_matrix_size xs) (Nat.le_add_left _ _))
  | N _ :: xs => Nat.succ_le_succ (Nat.add_le_add_left (sparse_matrix_size xs) _)

/-- Every entry is nonzero. Rocq: `Notation.SchutteStack.is_sparse`. -/
def IsSparse : List (Nat × VForm) → Prop
  | [] => True
  | (_, a) :: xs => a ≠ Z ∧ IsSparse xs

/-- Rocq: `Notation.SchutteStack.sparse_stack_is_sparse`. -/
theorem sparse_stack_is_sparse : ∀ xs : List VForm, IsSparse (sparseStack xs)
  | [] => trivial
  | Z :: xs => sparse_stack_is_sparse xs
  | N _ :: xs => ⟨fun h => VForm.noConfusion h, sparse_stack_is_sparse xs⟩

/-- Rocq: `Notation.SchutteStack.all_zero_sparse_stack`. -/
theorem all_zero_sparse_stack : ∀ xs : List VForm, Each (fun x => x = Z) xs ↔ sparseStack xs = []
  | [] => ⟨fun _ => rfl, fun _ => trivial⟩
  | Z :: xs => ⟨fun h => (all_zero_sparse_stack xs).1 h.2, fun h => ⟨rfl, (all_zero_sparse_stack xs).2 h⟩⟩
  | N _ :: _ => ⟨fun h => VForm.noConfusion h.1, fun h => (nomatch h)⟩

/-- Rocq: `Notation.SchutteStack.active_subterm_sparse`. -/
theorem active_subterm_sparse : ∀ (xs : List VForm) (x : VForm),
    ActiveSubterm xs x ↔ ∃ l n, sparseStack xs = l ++ [(n, x)]
  | [], _ => ⟨fun h => (nomatch h), fun ⟨l, _, h⟩ => by
    cases l <;> exact (nomatch (show ([] : List (Nat × VForm)) = _ from h))⟩
  | a :: xs, x => by
    constructor
    · intro h
      cases h with
      | last hx hz =>
        cases a with
        | Z => exact absurd rfl hx
        | N l' => exact ⟨[], xs.length, by
            show (xs.length, N l') :: sparseStack xs = _
            rw [(all_zero_sparse_stack xs).1 hz]; rfl⟩
      | later h =>
        obtain ⟨l, n, e⟩ := (active_subterm_sparse xs x).1 h
        cases a with
        | Z => exact ⟨l, n, e⟩
        | N l' => exact ⟨(xs.length, N l') :: l, n, by
            show (xs.length, N l') :: sparseStack xs = _
            rw [e]; rfl⟩
    · rintro ⟨l, n, e⟩
      cases a with
      | Z => exact .later ((active_subterm_sparse xs x).2 ⟨l, n, e⟩)
      | N l' =>
        cases l with
        | nil =>
          injection e with e₁ e₂
          injection e₁ with _ e₃
          subst e₃
          exact .last (fun h => VForm.noConfusion h) ((all_zero_sparse_stack xs).2 e₂)
        | cons p l =>
          injection e with _ e₂
          exact .later ((active_subterm_sparse xs x).2 ⟨l, n, e₂⟩)

/-- Rocq: `Notation.SchutteStack.ordering_swap_inv`. -/
theorem ordering_swap_inv (o : Ordering) : o.swap.swap = o := by cases o <;> rfl

theorem N_pos (l : List VForm) : 0 < denote (N l) :=
  lt_of_lt_of_le (lt_of_lt_of_le (succ_lt 0) (le_add_right 1 0))
    (schutte_stack_base _ _ 0 onePlus_normal (list_complete l))

/-- Rocq: `Notation.SchutteStack.VF_nonzero`. -/
theorem VF_nonzero : ∀ x : VForm, 0 < denote x ↔ x ≠ Z
  | Z => ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h⟩
  | N l => ⟨fun _ h => VForm.noConfusion h, fun _ => N_pos l⟩

/-- Decide whether a sparse matrix is trivial.
Rocq: `Notation.SchutteStack.sparse_trivial`. -/
def sparseTrivial : (xs : List (Nat × VForm)) →
    PSum (TrivialMatrix (sparseMatrix xs)) (NontrivialMatrix (sparseMatrix xs))
  | [] => .inl trivial
  | (_, Z) :: xs =>
    match sparseTrivial xs with
    | .inl h => .inl ⟨equiv_refl 0, h⟩
    | .inr h => .inr (.inr h)
  | (_, N l) :: _ => .inr (.inl (N_pos l))

/-- Rocq: `Notation.SchutteStack.all_complete_sparse_matrix`. -/
theorem all_complete_sparse_matrix : ∀ xs : List (Nat × VForm), AllComplete (sparseMatrix xs)
  | [] => trivial
  | (_, a) :: xs => ⟨ofNat_complete _, complete a, all_complete_sparse_matrix xs⟩

/-- Rocq: `Notation.SchutteStack.sparse_stack_proper`. -/
theorem sparse_stack_proper : ∀ xs : List VForm,
    SchutteMatrixProper (sparseMatrix (sparseStack xs)) (ofNat xs.length) SmallVeblenOrdinal
  | [] => trivial
  | Z :: xs => schutte_matrix_proper_monotone _ _ _ _ _ (le_of_lt (succ_lt _)) (le_refl _)
      (sparse_stack_proper xs)
  | N l :: xs => ⟨succ_lt _, bounded (N l), sparse_stack_proper xs⟩

/-- Rocq: `Notation.SchutteStack.nontrivial_matrix_app`. -/
theorem nontrivial_matrix_app : ∀ m n : List (Ordinal.{0} × Ordinal.{0}),
    NontrivialMatrix (m ++ n) ↔ NontrivialMatrix m ∨ NontrivialMatrix n
  | [], _ => ⟨.inr, fun h => h.elim (fun h => h.elim) id⟩
  | _ :: m, n => by
    show (_ ∨ NontrivialMatrix (m ++ n)) ↔ (_ ∨ NontrivialMatrix m) ∨ _
    have ih := nontrivial_matrix_app m n
    exact ⟨fun h => h.elim (fun h => .inl (.inl h))
        (fun h => (ih.1 h).elim (fun h => .inl (.inr h)) .inr),
      fun h => h.elim (fun h => h.elim .inl (fun h => .inr (ih.2 (.inl h))))
        (fun h => .inr (ih.2 (.inr h)))⟩

/-- Rocq: `Notation.SchutteStack.sparse_matrix_app`. -/
theorem sparse_matrix_app : ∀ m n : List (Nat × VForm),
    sparseMatrix (m ++ n) = sparseMatrix m ++ sparseMatrix n
  | [], _ => rfl
  | (b, a) :: m, n => congrArg ((ofNat b, denote a) :: ·) (sparse_matrix_app m n)

/-- Rocq: `Notation.SchutteStack.is_sparse_app`. -/
theorem is_sparse_app : ∀ m n : List (Nat × VForm), IsSparse (m ++ n) ↔ IsSparse m ∧ IsSparse n
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: m, n =>
    ⟨fun h => ⟨⟨h.1, ((is_sparse_app m n).1 h.2).1⟩, ((is_sparse_app m n).1 h.2).2⟩,
      fun h => ⟨h.1.1, (is_sparse_app m n).2 ⟨h.1.2, h.2⟩⟩⟩

/-! ## Comparison -/

/-- Compare a sparse matrix with the term `ytop` it is checked against.
Rocq: `Notation.SchutteStack.check_lt`. -/
def checkLt (cmp : VForm → VForm → Ordering) : List (Nat × VForm) → VForm → Ordering
  | [], _ => .lt
  | (_, a) :: xs, ytop =>
    match cmp a ytop with
    | .lt => checkLt cmp xs ytop
    | .eq =>
      match sparseTrivial xs with
      | .inl _ => .eq
      | .inr _ => .gt
    | .gt => .gt

/-- Compare two sparse matrices, denoting `xtop` and `ytop`.
Rocq: `Notation.SchutteStack.sparse_compare`. -/
def sparseCompare (cmp : VForm → VForm → Ordering) (xtop : VForm) :
    List (Nat × VForm) → List (Nat × VForm) → VForm → Ordering
  | [], [], _ => .eq
  | [], _ :: _, _ => .lt
  | _ :: _, [], _ => .gt
  | (xb, xa) :: xs, (yb, ya) :: ys, ytop =>
    match natCompare xb yb with
    | .lt => checkLt cmp ((xb, xa) :: xs) ytop
    | .eq =>
      match cmp xa ya with
      | .lt => checkLt cmp xs ytop
      | .eq => sparseCompare cmp xtop xs ys ytop
      | .gt => (checkLt cmp ys xtop).swap
    | .gt => (checkLt cmp ((yb, ya) :: ys) xtop).swap

/-- Comparison with explicit fuel. Rocq: `Notation.SchutteStack.VF_compare_loop`. -/
def compareFuel : Nat → VForm → VForm → Ordering
  | 0, _, _ => .eq
  | _ + 1, Z, Z => .eq
  | _ + 1, Z, N _ => .lt
  | _ + 1, N _, Z => .gt
  | k + 1, N xs, N ys =>
    sparseCompare (compareFuel k) (N xs) (sparseStack xs) (sparseStack ys) (N ys)

/-- Rocq: `Notation.SchutteStack.VF_compare`. -/
def compare (x y : VForm) : Ordering := compareFuel (termSize x + termSize y + 1) x y

theorem checkLt_correct (cmp : VForm → VForm → Ordering) (ytop : VForm) :
    ∀ xs : List (Nat × VForm),
      Each (fun p => OrderingCorrect (cmp p.2 ytop) (denote p.2) (denote ytop)) xs →
      ConfirmLt (checkLt cmp xs ytop) (sparseMatrix xs) (denote ytop)
  | [], _ => .nil _
  | (b, a) :: xs, h => by
    show ConfirmLt (match cmp a ytop with
      | .lt => checkLt cmp xs ytop
      | .eq =>
        match sparseTrivial xs with
        | .inl _ => .eq
        | .inr _ => .gt
      | .gt => .gt) ((ofNat b, denote a) :: sparseMatrix xs) (denote ytop)
    have hc : OrderingCorrect (cmp a ytop) (denote a) (denote ytop) := h.1
    revert hc
    cases cmp a ytop with
    | lt => exact fun hc => .lt _ _ _ _ _ hc (checkLt_correct cmp ytop xs h.2)
    | eq =>
      intro hc
      cases sparseTrivial xs with
      | inl ht => exact .eq1 _ _ _ _ hc ht
      | inr ht => exact .eq2 _ _ _ _ hc ht
    | gt => exact fun hc => .gt _ _ _ _ hc

/-- Two matrices with the same columns and equivalent arguments at the head
give the same values. -/
private theorem matrix_head_congr {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f)
    (m : List (Ordinal.{0} × Ordinal.{0})) (β : Ordinal.{0}) {α α' : Ordinal.{0}} (h : α ≈ α')
    (x : Ordinal.{0}) : schutteMatrix (schutteColumn f β α) m x ≈ schutteMatrix (schutteColumn f β α') m x :=
  have mono : ∀ γ : Ordinal.{0}, ∀ a b, a ≤ b → schutteColumn f β γ a ≤ schutteColumn f β γ b :=
    fun _ _ _ hab => schutte_column_monotone f β _ _ _ _ hf.monotone (le_refl _) hab
  equiv_intro
    (schutte_matrix_monotone_func m _ _ x (mono α) (mono α')
      (fun z => schutte_column_monotone f β _ z _ z hf.monotone h.le (le_refl z)))
    (schutte_matrix_monotone_func m _ _ x (mono α') (mono α)
      (fun z => schutte_column_monotone f β _ z _ z hf.monotone h.ge (le_refl z)))

theorem sparseCompare_correct (cmp : VForm → VForm → Ordering) (xtop ytop : VForm) :
    ∀ (xs ys : List (Nat × VForm)) (f : Ordinal.{0} → Ordinal.{0}), NormalFunction f →
      Each (fun p => OrderingCorrect (cmp p.2 ytop) (denote p.2) (denote ytop)) xs →
      Each (fun q => OrderingCorrect (cmp q.2 xtop) (denote q.2) (denote xtop)) ys →
      Each (fun p => Each (fun q => OrderingCorrect (cmp p.2 q.2) (denote p.2) (denote q.2)) ys) xs →
      IsSparse xs → IsSparse ys →
      denote xtop ≈ schutteMatrix f (sparseMatrix xs) 0 →
      denote ytop ≈ schutteMatrix f (sparseMatrix ys) 0 →
      SchutteMatrixCompare (sparseCompare cmp xtop xs ys ytop) f (sparseMatrix xs) (sparseMatrix ys)
  | [], [], f, _, _, _, _, _, _, _, _ => .nil_nil f
  | [], (_, ya) :: _, f, _, _, _, _, _, hspy, _, _ => .nil_left f _ _ _ ((VF_nonzero ya).2 hspy.1)
  | (_, xa) :: _, [], f, _, _, _, _, hspx, _, _, _ => .nil_right f _ _ _ ((VF_nonzero xa).2 hspx.1)
  | (xb, xa) :: xs, (yb, ya) :: ys, f, hf, hx, hy, hxy, hspx, hspy, hxeq, hyeq => by
    show SchutteMatrixCompare (match natCompare xb yb with
      | .lt => checkLt cmp ((xb, xa) :: xs) ytop
      | .eq =>
        match cmp xa ya with
        | .lt => checkLt cmp xs ytop
        | .eq => sparseCompare cmp xtop xs ys ytop
        | .gt => (checkLt cmp ys xtop).swap
      | .gt => (checkLt cmp ((yb, ya) :: ys) xtop).swap) f
      ((ofNat xb, denote xa) :: sparseMatrix xs) ((ofNat yb, denote ya) :: sparseMatrix ys)
    have hn := natCompare_correct xb yb
    revert hn
    cases natCompare xb yb with
    | lt =>
      exact fun hn => .index_lt _ f _ _ _ _ _ _ (ofNat_increasing hn) ((VF_nonzero ya).2 hspy.1)
        (ConfirmLt.congr hyeq (checkLt_correct cmp ytop ((xb, xa) :: xs) hx))
    | eq =>
      intro hn
      subst hn
      have hc : OrderingCorrect (cmp xa ya) (denote xa) (denote ya) := hxy.1.1
      revert hc
      cases cmp xa ya with
      | lt =>
        exact fun hc => .arg_lt _ f _ _ _ _ _ _ (equiv_refl _) hc
          (ConfirmLt.congr hyeq (checkLt_correct cmp ytop xs hx.2))
      | eq =>
        intro hc
        have hf' := schutte_column_normal _ _ f (ofNat_complete xb) (complete xa) hf
        exact .eq _ f _ _ _ _ _ _ (equiv_refl _) hc
          (sparseCompare_correct cmp xtop ytop xs ys _ hf' hx.2 hy.2 (hxy.2.imp fun _ h => h.2)
            hspx.2 hspy.2 hxeq
            (equiv_trans hyeq (matrix_head_congr hf _ _ (equiv_symm hc) 0)))
      | gt =>
        intro hc
        refine .arg_gt _ f _ _ _ _ _ _ (equiv_refl _) hc ?_
        rw [ordering_swap_inv]
        exact ConfirmLt.congr hxeq (checkLt_correct cmp xtop ys hy.2)
    | gt =>
      intro hn
      refine .index_gt _ f _ _ _ _ _ _ (ofNat_increasing hn) ((VF_nonzero xa).2 hspx.1) ?_
      rw [ordering_swap_inv]
      exact ConfirmLt.congr hxeq (checkLt_correct cmp xtop ((yb, ya) :: ys) hy)

private theorem sparseStack_each {Q : VForm → Prop} :
    ∀ xs : List VForm, Each Q xs → Each (fun p => Q p.2) (sparseStack xs)
  | [], _ => trivial
  | Z :: xs, h => sparseStack_each xs h.2
  | N _ :: xs, h => ⟨h.1, sparseStack_each xs h.2⟩

theorem compareFuel_correct : ∀ (fuel : Nat) (x y : VForm), termSize x + termSize y < fuel →
    OrderingCorrect (compareFuel fuel x y) (denote x) (denote y)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, Z, Z, _ => equiv_refl _
  | _ + 1, Z, N l, _ => N_pos l
  | _ + 1, N l, Z, _ => N_pos l
  | k + 1, N xs, N ys, h => by
    have hk : termSize (N xs) + termSize (N ys) ≤ k := Nat.le_of_lt_succ h
    have hk' : termSize (N ys) + termSize (N xs) ≤ k := Nat.add_comm _ _ ▸ hk
    have hxs := sparseStack_each xs (each_lt_termSize xs)
    have hys := sparseStack_each ys (each_lt_termSize ys)
    have sc := sparseCompare_correct (compareFuel k) (N xs) (N ys) (sparseStack xs) (sparseStack ys)
      (fun y => 1 + y) onePlus_normal
      (hxs.imp fun p hp => compareFuel_correct k _ _
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hp _) hk))
      (hys.imp fun q hq => compareFuel_correct k _ _
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hq _) hk'))
      (hxs.imp fun p hp => hys.imp fun q hq => compareFuel_correct k p.2 q.2
        (Nat.lt_of_lt_of_le (Nat.add_lt_add hp hq) hk))
      (sparse_stack_is_sparse xs) (sparse_stack_is_sparse ys)
      (sparse_matrix_eq xs _ 0 onePlus_normal zero_complete)
      (sparse_matrix_eq ys _ 0 onePlus_normal zero_complete)
    exact OrderingCorrect.congr (equiv_symm (sparse_matrix_eq xs _ 0 onePlus_normal zero_complete))
      (equiv_symm (sparse_matrix_eq ys _ 0 onePlus_normal zero_complete))
      (schutte_matrix_compare_correct sc _ _ _ _ onePlus_normal (all_complete_sparse_matrix _)
        (all_complete_sparse_matrix _) (sparse_stack_proper xs) (sparse_stack_proper ys))

/-- Rocq: `Notation.SchutteStack.VF_compare_correct`. -/
theorem compare_correct (x y : VForm) : OrderingCorrect (compare x y) (denote x) (denote y) :=
  compareFuel_correct _ x y (Nat.lt_succ_self _)

/-- Rocq: `Notation.SchutteStack.VF_dec_order`. -/
def decOrder (x y : VForm) :
    PSum (PSum (denote x < denote y) (denote x ≈ denote y)) (denote y < denote x) :=
  match compare x y, compare_correct x y with
  | .lt, h => .inl (.inl h)
  | .eq, h => .inl (.inr h)
  | .gt, h => .inr h

/-! ## Normal forms -/

/-- Rocq: `Notation.SchutteStack.each_lt_mono`. -/
theorem each_lt_mono (xs : List (Nat × VForm)) {p q : Ordinal.{0}} (h : p ≤ q)
    (hx : Each (fun x => denote x.2 < p) xs) : Each (fun x => denote x.2 < q) xs :=
  hx.imp fun _ hx => lt_of_lt_of_le hx h

/-- `f 0` is below any matrix with a nonzero leading argument. -/
private theorem base_lt_matrix {f : Ordinal.{0} → Ordinal.{0}} (hf : NormalFunction f) (b : Nat) (a : VForm)
    (m : List (Nat × VForm)) (ha : a ≠ Z) : f 0 < schutteMatrix f (sparseMatrix ((b, a) :: m)) 0 :=
  lt_of_lt_of_le (hf.increasing _ _ (add_complete (complete a) zero_complete)
      (lt_of_lt_of_le ((VF_nonzero a).2 ha) (add_zero _).ge))
    (le_trans (schutte_column_le_f _ _ 0 f hf.monotone)
      (schutte_matrix_base _ _ 0 (schutte_column_normal _ _ f (ofNat_complete b) (complete a) hf)
        (all_complete_sparse_matrix m)))

/-- Rocq: `Notation.SchutteStack.sparse_stack_eq_unique`. -/
theorem sparse_stack_eq_unique : ∀ (xs ys : List (Nat × VForm)) (f : Ordinal.{0} → Ordinal.{0})
    (p q : Ordinal.{0}), NormalFunction f →
    schutteMatrix f (sparseMatrix xs) 0 ≈ schutteMatrix f (sparseMatrix ys) 0 →
    IsSparse xs → IsSparse ys →
    SchutteMatrixProper (sparseMatrix xs) p (schutteMatrix f (sparseMatrix xs) 0) →
    SchutteMatrixProper (sparseMatrix ys) q (schutteMatrix f (sparseMatrix ys) 0) →
    Forall₂ (fun x y => x.1 = y.1 ∧ denote x.2 ≈ denote y.2) xs ys
  | [], [], _, _, _, _, _, _, _, _, _ => .nil
  | [], (yb, ya) :: ys, _, _, _, hf, heq, _, hys, _, _ =>
    absurd (lt_of_lt_of_le (base_lt_matrix hf yb ya ys hys.1) heq.ge) (lt_irrefl _)
  | (xb, xa) :: xs, [], _, _, _, hf, heq, hxs, _, _, _ =>
    absurd (lt_of_lt_of_le (base_lt_matrix hf xb xa xs hxs.1) heq.le) (lt_irrefl _)
  | (xb, xa) :: xs, (yb, ya) :: ys, f, p, q, hf, heq, hxs₁, hys₁, hxs₂, hys₂ => by
    have hxa := complete xa
    have hya := complete ya
    -- the column indices agree
    have hb : xb = yb := by
      have hc := natCompare_correct xb yb
      revert hc
      cases natCompare xb yb with
      | lt =>
        intro hc
        refine absurd (lt_of_lt_of_le (schutte_matrix_lt1 _ f _ _ _ _ _ 0 hf
          (all_complete_sparse_matrix xs) (ofNat_complete _) hxa (all_complete_sparse_matrix ys)
          (ofNat_complete _) hya zero_complete
          (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq.le hxs₂.2.2)
          ((VF_nonzero ya).2 hys₁.1) (ofNat_increasing hc)
          (lt_of_lt_of_le hxs₂.2.1 heq.le)) heq.ge) (lt_irrefl _)
      | eq => exact id
      | gt =>
        intro hc
        refine absurd (lt_of_lt_of_le (schutte_matrix_lt1 _ f _ _ _ _ _ 0 hf
          (all_complete_sparse_matrix ys) (ofNat_complete _) hya (all_complete_sparse_matrix xs)
          (ofNat_complete _) hxa zero_complete
          (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq.ge hys₂.2.2)
          ((VF_nonzero xa).2 hxs₁.1) (ofNat_increasing hc)
          (lt_of_lt_of_le hys₂.2.1 heq.ge)) heq.le) (lt_irrefl _)
    subst hb
    -- the arguments agree
    have ha : denote xa ≈ denote ya := by
      match decOrder xa ya with
      | .inl (.inr h) => exact h
      | .inl (.inl h) =>
        exact absurd (lt_of_lt_of_le (schutte_matrix_lt2 _ f _ _ _ _ 0 hf
          (all_complete_sparse_matrix xs) (ofNat_complete _) hxa (all_complete_sparse_matrix ys)
          hya zero_complete ⟨_, hys₂.2.2⟩
          (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq.le hxs₂.2.2) h) heq.ge)
          (lt_irrefl _)
      | .inr h =>
        exact absurd (lt_of_lt_of_le (schutte_matrix_lt2 _ f _ _ _ _ 0 hf
          (all_complete_sparse_matrix ys) (ofNat_complete _) hya (all_complete_sparse_matrix xs)
          hxa zero_complete ⟨_, hxs₂.2.2⟩
          (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq.ge hys₂.2.2) h) heq.le)
          (lt_irrefl _)
    have hcong := matrix_head_congr hf (sparseMatrix ys) (ofNat xb) (equiv_symm ha) 0
    refine .cons ⟨rfl, ha⟩ (sparse_stack_eq_unique xs ys _ (ofNat xb) (ofNat xb)
      (schutte_column_normal _ _ f (ofNat_complete _) hxa hf) (equiv_trans heq hcong)
      hxs₁.2 hys₁.2 hxs₂.2.2
      (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) hcong.le hys₂.2.2))

/-- Rocq: `Notation.SchutteStack.sparse_stack_length_lt`. -/
theorem sparse_stack_length_lt (x : Nat × VForm) (l : List (Nat × VForm)) :
    ∀ xs : List VForm, x :: l = sparseStack xs → x.1 < xs.length
  | [], h => nomatch h
  | Z :: xs, h => Nat.lt_succ_of_lt (sparse_stack_length_lt x l xs h)
  | N _ :: xs, h => by
    injection h with h₁ _
    subst h₁
    exact Nat.lt_succ_self _

/-- Rocq: `Notation.SchutteStack.no_leading_zeros`. -/
def NoLeadingZeros : List VForm → Prop
  | [] => True
  | x :: _ => x ≠ Z

mutual
/-- No leading zeros, normal entries, and every entry below the whole stack.
Rocq: `Notation.SchutteStack.VF_normal`. -/
def IsNormal : VForm → Prop
  | Z => True
  | N l => NoLeadingZeros l ∧ IsNormalList l ∧ Each (fun x => denote x < denote (N l)) l

/-- `Each IsNormal`. -/
def IsNormalList : List VForm → Prop
  | [] => True
  | x :: xs => IsNormal x ∧ IsNormalList xs
end

theorem isNormalList_iff : ∀ l : List VForm, IsNormalList l ↔ Each IsNormal l
  | [] => Iff.rfl
  | _ :: xs => ⟨fun h => ⟨h.1, (isNormalList_iff xs).1 h.2⟩, fun h => ⟨h.1, (isNormalList_iff xs).2 h.2⟩⟩

theorem isNormal_N (l : List VForm) :
    IsNormal (N l) ↔ NoLeadingZeros l ∧ Each IsNormal l ∧ Each (fun x => denote x < denote (N l)) l :=
  ⟨fun h => ⟨h.1, (isNormalList_iff l).1 h.2.1, h.2.2⟩,
    fun h => ⟨h.1, (isNormalList_iff l).2 h.2.1, h.2.2⟩⟩

/-- Rocq: `Notation.SchutteStack.sparse_subterm_lt`. -/
theorem sparse_subterm_lt : ∀ (xs : List VForm) (l : List (Nat × VForm)) (n : Nat) (x : VForm)
    (f : Ordinal.{0} → Ordinal.{0}), NormalFunction f → sparseStack xs = l ++ [(n, x)] →
    Each (fun z => denote z.2 < schutteMatrix f (sparseMatrix (l ++ [(n, x)])) 0) l
  | [], l, _, _, _, _, h => by cases l <;> exact (nomatch (show ([] : List (Nat × VForm)) = _ from h))
  | Z :: xs, l, n, x, f, hf, h => sparse_subterm_lt xs l n x f hf h
  | N l' :: xs, l, n, x, f, hf, h => by
    cases l with
    | nil => exact trivial
    | cons p l =>
      have h' : (xs.length, N l') :: sparseStack xs = p :: (l ++ [(n, x)]) := h
      obtain ⟨h₁, h₂⟩ := List.cons.inj h'
      subst h₁
      have hsp := sparse_stack_is_sparse xs
      rw [h₂] at hsp
      have hx : x ≠ Z := ((is_sparse_app _ _).1 hsp).2.1
      have hnt : NontrivialMatrix (sparseMatrix (l ++ [(n, x)])) := by
        rw [sparse_matrix_app]
        exact (nontrivial_matrix_app _ _).2 (.inr (.inl ((VF_nonzero x).2 hx)))
      exact ⟨nontrivial_matrix_member_lt [] _ f _ _ hf trivial (ofNat_complete _) (complete _)
          (all_complete_sparse_matrix _) hnt,
        sparse_subterm_lt xs l n x _
          (schutte_column_normal _ _ f (ofNat_complete _) (complete _) hf) h₂⟩

/-- Rocq: `Notation.SchutteStack.each_lt_sparse_stack`. -/
theorem each_lt_sparse_stack : ∀ (xs : List VForm) (p q : Ordinal.{0}), 0 < q → p ≤ q →
    Each (fun z => denote z.2 < p) (sparseStack xs) → Each (fun z => denote z < q) xs
  | [], _, _, _, _, _ => trivial
  | Z :: xs, p, q, hq, hpq, h => ⟨hq, each_lt_sparse_stack xs p q hq hpq h⟩
  | N _ :: xs, p, q, hq, hpq, h =>
    ⟨lt_of_lt_of_le h.1 hpq, each_lt_sparse_stack xs p q hq hpq h.2⟩

/-- A nonempty list ends in some element. -/
private theorem exists_last {α : Type} : ∀ l : List α, l ≠ [] → ∃ l' a, l = l' ++ [a]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: l, _ =>
    let ⟨l', c, e⟩ := exists_last (b :: l) (fun h => nomatch h)
    ⟨a :: l', c, congrArg (a :: ·) e⟩

/-- Rocq: `Notation.SchutteStack.active_subterm_lt`. -/
theorem active_subterm_lt (xs : List VForm)
    (hact : ∀ x, ActiveSubterm xs x → denote x < denote (N xs)) :
    Each (fun x => denote x < denote (N xs)) xs := by
  have heqv := sparse_matrix_eq xs _ 0 onePlus_normal zero_complete
  match hs : sparseStack xs with
  | [] =>
    exact ((all_zero_sparse_stack xs).2 hs).imp fun x hx => by
      subst hx; exact N_pos xs
  | p :: ps =>
    obtain ⟨l', ⟨n, x⟩, e⟩ := exists_last (p :: ps) (fun h => nomatch h)
    rw [← hs] at e
    have hx : ActiveSubterm xs x := (active_subterm_sparse xs x).2 ⟨l', n, e⟩
    have hM : denote (N xs) ≈ schutteMatrix (fun y => 1 + y) (sparseMatrix (l' ++ [(n, x)])) 0 := by
      rw [← e]; exact heqv
    refine each_lt_sparse_stack xs _ _ (N_pos xs) hM.ge ?_
    rw [e]
    exact (CantorDecomposition.each_app _ _ _).2 ⟨sparse_subterm_lt xs l' n x _ onePlus_normal e,
      lt_of_lt_of_le (hact x hx) hM.le, trivial⟩

/-- Rocq: `Notation.SchutteStack.active_subterm_lt'`. -/
theorem active_subterm_lt' {xs : List VForm} {q : Ordinal.{0}} (h : Each (fun x => denote x < q) xs) :
    ∀ x, ActiveSubterm xs x → denote x < q := by
  intro x hx
  induction hx with
  | last _ _ => exact h.1
  | later _ ih => exact ih h.2

/-- Rocq: `Notation.SchutteStack.VF_normal_alt`. -/
theorem normal_alt (l : List VForm) :
    IsNormal (N l) ↔ NoLeadingZeros l ∧ Each IsNormal l ∧
      ∀ x, ActiveSubterm l x → denote x < denote (N l) :=
  ⟨fun h => let h := (isNormal_N l).1 h; ⟨h.1, h.2.1, active_subterm_lt' h.2.2⟩,
    fun h => (isNormal_N l).2 ⟨h.1, h.2.1, active_subterm_lt l h.2.2⟩⟩

/-! ## Normalization by rewriting -/

/-- Rocq: `Notation.SchutteStack.redex`. -/
inductive Redex : VForm → VForm → Prop
  | leading_zero (l : List VForm) : Redex (N (Z :: l)) (N l)
  | fixpoint {l : List VForm} {x : VForm} : ActiveSubterm l x → compare (N l) x = .eq → Redex (N l) x

/-- Rocq: `Notation.SchutteStack.redex_sound`. -/
theorem redex_sound {x y : VForm} : Redex x y → denote x ≈ denote y
  | .leading_zero l => schutte_stack_leading_zero _ (denoteList l) 0 onePlus_normal
  | .fixpoint (l := l) (x := x) _ h => by
    have hc := compare_correct (N l) x
    rw [h] at hc
    exact hc

private theorem active_lt_size {l : List VForm} {x : VForm} (h : ActiveSubterm l x) :
    termSize x < termSize (N l) := by
  induction h with
  | last _ _ => exact (each_lt_termSize (_ :: _)).1
  | later _ ih =>
    exact Nat.lt_of_lt_of_le ih (Nat.succ_le_succ (Nat.le_succ_of_le (Nat.le_add_left _ _)))

/-- Rocq: `Notation.SchutteStack.redex_size`. -/
theorem redex_size {x y : VForm} : Redex x y → termSize y < termSize x
  | .leading_zero l => Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.le_add_left (listSize l) 0))
  | .fixpoint h _ => active_lt_size h

/-- Rocq: `Notation.SchutteStack.one_step_reduce`. -/
inductive OneStepReduce : VForm → VForm → Prop
  | redex {x y : VForm} : Redex x y → OneStepReduce x y
  | cong {x x' : VForm} (l₁ l₂ : List VForm) : OneStepReduce x x' →
      OneStepReduce (N (l₁ ++ x :: l₂)) (N (l₁ ++ x' :: l₂))

private theorem length_cong {α : Type u} (x x' : α) (l₂ : List α) :
    ∀ l₁ : List α, (l₁ ++ x :: l₂).length = (l₁ ++ x' :: l₂).length
  | [] => rfl
  | _ :: l₁ => congrArg (· + 1) (length_cong x x' l₂ l₁)

/-- Rocq: `Notation.SchutteStack.schutte_stack_le_cong`. -/
theorem schutte_stack_le_cong : ∀ (l₁ l₂ : List Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (x x' : Ordinal.{0}), Each Complete l₁ → NormalFunction f → x ≤ x' →
    schutteStack f (l₁ ++ x :: l₂) 0 ≤ schutteStack f (l₁ ++ x' :: l₂) 0
  | [], l₂, f, x, x', _, hf, h =>
    schutte_stack_monotone_func l₂ _ _ 0
      (fun _ _ hab => schutte_column_monotone f _ x _ x _ hf.monotone (le_refl _) hab)
      (fun _ _ hab => schutte_column_monotone f _ x' _ x' _ hf.monotone (le_refl _) hab)
      (fun z => schutte_column_monotone f _ x z x' z hf.monotone h (le_refl z))
  | a :: l₁, l₂, f, x, x', hl, hf, h => by
    show schutteStack (schutteColumn f (ofNat (l₁ ++ x :: l₂).length) a) (l₁ ++ x :: l₂) 0 ≤
      schutteStack (schutteColumn f (ofNat (l₁ ++ x' :: l₂).length) a) (l₁ ++ x' :: l₂) 0
    rw [length_cong x x' l₂ l₁]
    exact schutte_stack_le_cong l₁ l₂ _ x x' hl.2
      (schutte_column_normal _ a f (ofNat_complete _) hl.1 hf) h

/-- Rocq: `Notation.SchutteStack.one_step_reduce_sound`. -/
theorem one_step_reduce_sound {x y : VForm} : OneStepReduce x y → denote x ≈ denote y
  | .redex h => redex_sound h
  | .cong (x := x) (x' := x') l₁ l₂ h => by
    have ih := one_step_reduce_sound h
    show schutteStack _ (denoteList (l₁ ++ x :: l₂)) 0 ≈ schutteStack _ (denoteList (l₁ ++ x' :: l₂)) 0
    rw [denoteList_append, denoteList_append]
    exact equiv_intro
      (schutte_stack_le_cong _ _ _ _ _ (each_complete l₁) onePlus_normal ih.le)
      (schutte_stack_le_cong _ _ _ _ _ (each_complete l₁) onePlus_normal ih.ge)

/-- Rocq: `Notation.SchutteStack.step_reduce_sound`. -/
theorem step_reduce_sound {x y : VForm} :
    ClosReflTrans OneStepReduce x y → denote x ≈ denote y
  | .step h => one_step_reduce_sound h
  | .refl _ => equiv_refl _
  | .trans h₁ h₂ => equiv_trans (step_reduce_sound h₁) (step_reduce_sound h₂)

/-- Rocq: `Notation.SchutteStack.VF_normal_matrix_proper_aux`. -/
theorem normal_matrix_proper_aux : ∀ (l : List VForm) (p q : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}),
    NormalFunction f → p ≤ q → Each (fun x => denote x < p) l →
    SchutteMatrixProper (stackToMatrix (denoteList l)) (ofNat l.length) q
  | [], _, _, _, _, _, _ => trivial
  | _ :: l, p, q, f, hf, hpq, h => by
    show _ < _ ∧ _ < q ∧ _
    rw [denoteList_length]
    exact ⟨succ_lt _, lt_of_lt_of_le h.1 hpq,
      denoteList_length l ▸ normal_matrix_proper_aux l p q f hf hpq h.2⟩

/-- Rocq: `Notation.SchutteStack.VF_normal_matrix_proper`. -/
theorem normal_matrix_proper (l : List VForm) (h : IsNormal (N l)) :
    SchutteMatrixProper (stackToMatrix (denoteList l)) (ofNat l.length)
      (schutteMatrix (fun y => 1 + y) (stackToMatrix (denoteList l)) 0) :=
  normal_matrix_proper_aux l _ _ _ onePlus_normal
    (stack_to_matrix_eq (denoteList l) (fun y => 1 + y) 0 ▸ le_refl _) ((isNormal_N l).1 h).2.2

/-- Rocq: `Notation.SchutteStack.VF_normal_sparse_matrix_proper_aux`. -/
theorem normal_sparse_matrix_proper_aux : ∀ (l : List VForm) (p q : Ordinal.{0})
    (f : Ordinal.{0} → Ordinal.{0}), NormalFunction f → p ≤ q → Each (fun x => denote x < p) l →
    SchutteMatrixProper (sparseMatrix (sparseStack l)) (ofNat l.length) q
  | [], _, _, _, _, _, _ => trivial
  | Z :: l, p, q, f, hf, hpq, h =>
    schutte_matrix_proper_monotone _ _ _ _ _ (le_of_lt (succ_lt _)) (le_refl _)
      (normal_sparse_matrix_proper_aux l p q f hf hpq h.2)
  | N _ :: l, p, q, f, hf, hpq, h =>
    ⟨succ_lt _, lt_of_lt_of_le h.1 hpq, normal_sparse_matrix_proper_aux l p q f hf hpq h.2⟩

/-- Rocq: `Notation.SchutteStack.VF_normal_sparse_matrix_proper`. -/
theorem normal_sparse_matrix_proper (l : List VForm) (h : IsNormal (N l)) :
    SchutteMatrixProper (sparseMatrix (sparseStack l)) (ofNat l.length)
      (schutteMatrix (fun y => 1 + y) (sparseMatrix (sparseStack l)) 0) :=
  normal_sparse_matrix_proper_aux l (denote (N l)) _ _ onePlus_normal
    (sparse_matrix_eq l _ 0 onePlus_normal zero_complete).le ((isNormal_N l).1 h).2.2

/-- Rocq: `Notation.SchutteStack.sparse_stack_pairwise_eq`. -/
theorem sparse_stack_pairwise_eq : ∀ xs ys : List VForm, xs.length = ys.length →
    Forall₂ (fun x y => x.1 = y.1 ∧ denote x.2 ≈ denote y.2) (sparseStack xs) (sparseStack ys) →
    Forall₂ (fun x y => denote x ≈ denote y) xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | x :: xs, y :: ys, hl, h => by
    have hl' : xs.length = ys.length := Nat.succ.inj hl
    cases x with
    | Z =>
      cases y with
      | Z => exact .cons (equiv_refl _) (sparse_stack_pairwise_eq xs ys hl' h)
      | N yl =>
        change Forall₂ _ (sparseStack xs) ((ys.length, N yl) :: sparseStack ys) at h
        generalize hs : sparseStack xs = s at h
        revert hs
        cases h with
        | cons hr _ =>
          intro hs
          exact absurd (hr.1 ▸ hl' ▸ sparse_stack_length_lt _ _ xs hs.symm) (Nat.lt_irrefl _)
    | N xl =>
      cases y with
      | Z =>
        change Forall₂ _ ((xs.length, N xl) :: sparseStack xs) (sparseStack ys) at h
        generalize hs : sparseStack ys = s at h
        revert hs
        cases h with
        | cons hr _ =>
          intro hs
          exact absurd (hr.1.symm ▸ hl'.symm ▸ sparse_stack_length_lt _ _ ys hs.symm)
            (Nat.lt_irrefl _)
      | N yl =>
        change Forall₂ _ ((xs.length, N xl) :: sparseStack xs) ((ys.length, N yl) :: sparseStack ys) at h
        cases h with
        | cons hr h' => exact .cons hr.2 (sparse_stack_pairwise_eq xs ys hl' h')

/-- `1 + 0` is below any stack with a nonzero head. -/
private theorem stack_head_gt (y : VForm) (yl : List VForm) (hy : y ≠ Z) :
    1 + 0 < denote (N (y :: yl)) :=
  lt_of_lt_of_le (add_lt_add_left 1 (lt_of_lt_of_le ((VF_nonzero y).2 hy) (add_zero _).ge))
    (le_trans (schutte_column_le_f _ _ 0 _ onePlus_normal.monotone)
      (schutte_stack_base _ _ 0 (schutte_column_normal _ _ _ (ofNat_complete _) (complete y)
        onePlus_normal) (list_complete yl)))

/-- Rocq: `Notation.SchutteStack.VF_normal_form_unique`. -/
theorem normal_form_unique : ∀ x y : VForm, IsNormal x → IsNormal y → denote x ≈ denote y → x = y := by
  intro x
  refine induction' (fun x => ∀ y : VForm, IsNormal x → IsNormal y → denote x ≈ denote y → x = y)
    ?_ ?_ x
  · intro y _ _ h
    cases y with
    | Z => rfl
    | N yl => exact absurd (lt_of_lt_of_le (N_pos yl) h.ge) (lt_irrefl 0)
  · intro xl ih y hx hy heq
    cases y with
    | Z => exact absurd (lt_of_lt_of_le (N_pos xl) heq.le) (lt_irrefl 0)
    | N yl =>
      have hx' := (isNormal_N xl).1 hx
      have hy' := (isNormal_N yl).1 hy
      -- the stacks have the same height
      have hlen : xl.length = yl.length := by
        cases xl with
        | nil =>
          cases yl with
          | nil => rfl
          | cons y yl => exact absurd (lt_of_lt_of_le (stack_head_gt y yl hy'.1) heq.ge) (lt_irrefl _)
        | cons x xl =>
          cases yl with
          | nil => exact absurd (lt_of_lt_of_le (stack_head_gt x xl hx'.1) heq.le) (lt_irrefl _)
          | cons y yl =>
            have hX := normal_matrix_proper (x :: xl) hx
            have hY := normal_matrix_proper (y :: yl) hy
            have heq' : schutteMatrix (fun y => 1 + y) (stackToMatrix (denoteList (x :: xl))) 0 ≈
                schutteMatrix (fun y => 1 + y) (stackToMatrix (denoteList (y :: yl))) 0 := by
              rw [← stack_to_matrix_eq, ← stack_to_matrix_eq]; exact heq
            have hxc := (stack_to_matrix_complete (denoteList xl)).2 (list_complete xl)
            have hyc := (stack_to_matrix_complete (denoteList yl)).2 (list_complete yl)
            have hc := natCompare_correct xl.length yl.length
            revert hc
            cases natCompare xl.length yl.length with
            | lt =>
              intro hc
              rw [← denoteList_length xl, ← denoteList_length yl] at hc
              exact absurd (lt_of_lt_of_le (schutte_matrix_lt1 _ _ _ _ _ _ _ 0 onePlus_normal
                hxc (ofNat_complete _) (complete x) hyc (ofNat_complete _) (complete y) zero_complete
                (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq'.le hX.2.2)
                ((VF_nonzero y).2 hy'.1) (ofNat_increasing hc) (lt_of_lt_of_le hX.2.1 heq'.le))
                heq'.ge) (lt_irrefl _)
            | eq => exact fun hc => congrArg (· + 1) hc
            | gt =>
              intro hc
              rw [← denoteList_length xl, ← denoteList_length yl] at hc
              exact absurd (lt_of_lt_of_le (schutte_matrix_lt1 _ _ _ _ _ _ _ 0 onePlus_normal
                hyc (ofNat_complete _) (complete y) hxc (ofNat_complete _) (complete x) zero_complete
                (schutte_matrix_proper_monotone _ _ _ _ _ (le_refl _) heq'.ge hY.2.2)
                ((VF_nonzero x).2 hx'.1) (ofNat_increasing hc) (lt_of_lt_of_le hY.2.1 heq'.ge))
                heq'.le) (lt_irrefl _)
      have hpw := sparse_stack_pairwise_eq xl yl hlen
        (sparse_stack_eq_unique _ _ _ (ofNat xl.length) (ofNat yl.length) onePlus_normal
          (equiv_trans (equiv_symm (sparse_matrix_eq xl _ 0 onePlus_normal zero_complete))
            (equiv_trans heq (sparse_matrix_eq yl _ 0 onePlus_normal zero_complete)))
          (sparse_stack_is_sparse xl) (sparse_stack_is_sparse yl)
          (normal_sparse_matrix_proper xl hx) (normal_sparse_matrix_proper yl hy))
      suffices h : ∀ xl yl : List VForm, Each (fun x => ∀ y, IsNormal x → IsNormal y →
          denote x ≈ denote y → x = y) xl → Each IsNormal xl → Each IsNormal yl →
          Forall₂ (fun x y => denote x ≈ denote y) xl yl → xl = yl from
        congrArg N (h xl yl ih hx'.2.1 hy'.2.1 hpw)
      intro xl yl ih hxl hyl hpw
      induction hpw with
      | nil => rfl
      | cons hr _ ihr => rw [ih.1 _ hxl.1 hyl.1 hr, ihr ih.2 hxl.2 hyl.2]

/-- Rocq: `Notation.SchutteStack.no_leading_zeros_dec`. -/
def noLeadingZerosDec : (xs : List VForm) → PSum (∃ l, xs = Z :: l) (NoLeadingZeros xs)
  | [] => .inr trivial
  | Z :: l => .inl ⟨l, rfl⟩
  | N _ :: _ => .inr fun h => VForm.noConfusion h

/-- Rocq: `Notation.SchutteStack.active_subterm_dec`. -/
def activeSubtermDec : (xs : List VForm) → PSum { x // ActiveSubterm xs x } (Each (fun x => x = Z) xs)
  | [] => .inr trivial
  | a :: xs =>
    match activeSubtermDec xs with
    | .inl ⟨x, h⟩ => .inl ⟨x, .later h⟩
    | .inr h =>
      match a with
      | Z => .inr ⟨rfl, h⟩
      | N l => .inl ⟨N l, .last (fun h => VForm.noConfusion h) h⟩

/-- Rocq: `Notation.SchutteStack.active_subterm_le`. -/
theorem active_subterm_le {xs : List VForm} {x : VForm} (h : ActiveSubterm xs x) :
    ∀ f : Ordinal.{0} → Ordinal.{0}, NormalFunction f → denote x ≤ schutteStack f (denoteList xs) 0 := by
  induction h with
  | last _ _ =>
    intro f hf
    exact le_trans (schutte_column_inflationary1 _ _ 0 f (normal_inflationary hf) (complete _)
      zero_complete) (schutte_stack_base _ _ 0 (schutte_column_normal _ _ f (ofNat_complete _)
        (complete _) hf) (list_complete _))
  | later _ ih =>
    intro f hf
    exact ih _ (schutte_column_normal _ _ f (ofNat_complete _) (complete _) hf)

/-- Comparison returns `eq` exactly on equivalent forms. Stated for the port. -/
theorem eq_correct (x y : VForm) : compare x y = .eq ↔ denote x ≈ denote y := by
  have h := compare_correct x y
  revert h
  cases compare x y with
  | lt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h h'.ge)).elim⟩
  | eq => exact fun h => ⟨fun _ => h, fun _ => rfl⟩
  | gt => exact fun h => ⟨fun h' => (nomatch h'), fun h' => (lt_irrefl _ (lt_of_lt_of_le h h'.le)).elim⟩

mutual
/-- Normality is decidable. Rocq: `Notation.SchutteStack.VF_normal_dec`. -/
def isNormalDec : (x : VForm) → Decidable (IsNormal x)
  | Z => isTrue trivial
  | N l =>
    match noLeadingZerosDec l with
    | .inl he => isFalse fun h => he.elim fun _ e => by subst e; exact h.1 rfl
    | .inr hnz =>
      match activeSubtermDec l with
      | .inl ⟨x, hx⟩ =>
        match decOrder (N l) x with
        | .inl (.inl hlt) => isFalse fun h =>
            lt_irrefl _ (lt_trans hlt (((normal_alt l).1 h).2.2 x hx))
        | .inl (.inr heq) => isFalse fun h =>
            lt_irrefl _ (lt_of_lt_of_le (((normal_alt l).1 h).2.2 x hx) heq.le)
        | .inr hgt =>
          match isNormalListDec l with
          | isTrue hl => isTrue ((normal_alt l).2 ⟨hnz, (isNormalList_iff l).1 hl,
              fun y hy => active_subterm_unique hx hy ▸ hgt⟩)
          | isFalse hl => isFalse fun h => hl ((isNormalList_iff l).2 ((normal_alt l).1 h).2.1)
      | .inr hz =>
        match l, hnz, hz with
        | [], _, _ => isTrue ⟨trivial, trivial, trivial⟩
        | _ :: _, hnz, hz => absurd hz.1 hnz

/-- `Each IsNormal` is decidable. -/
def isNormalListDec : (l : List VForm) → Decidable (IsNormalList l)
  | [] => isTrue trivial
  | x :: xs =>
    match isNormalDec x with
    | isFalse h => isFalse fun h' => h h'.1
    | isTrue h =>
      match isNormalListDec xs with
      | isFalse h' => isFalse fun h'' => h' h''.2
      | isTrue h' => isTrue ⟨h, h'⟩
end

instance : DecidablePred IsNormal := isNormalDec

private theorem find_reducible : ∀ l : List VForm, Each (fun a => ¬ IsNormal a ↔ ∃ y, OneStepReduce a y) l →
    ¬ Each IsNormal l → ∃ l₁ l₂ x x', l = l₁ ++ x :: l₂ ∧ OneStepReduce x x'
  | [], _, h => absurd trivial h
  | a :: l, ih, h =>
    match isNormalDec a with
    | isTrue ha =>
      let ⟨l₁, l₂, x, x', e, hr⟩ := find_reducible l ih.2 fun h' => h ⟨ha, h'⟩
      ⟨a :: l₁, l₂, x, x', congrArg (a :: ·) e, hr⟩
    | isFalse ha =>
      let ⟨x', hr⟩ := ih.1.1 ha
      ⟨[], l, a, x', rfl, hr⟩

/-- Rocq: `Notation.SchutteStack.VF_notIsNormal_redex`. -/
theorem notIsNormal_redex : ∀ x : VForm, ¬ IsNormal x ↔ ∃ y, OneStepReduce x y := by
  intro x
  refine induction' (fun x => ¬ IsNormal x ↔ ∃ y, OneStepReduce x y) ?_ ?_ x
  · exact ⟨fun h => absurd trivial h, fun ⟨_, h⟩ => by cases h with | redex h => cases h⟩
  · intro xs ih
    constructor
    · intro hn
      match noLeadingZerosDec xs with
      | .inl ⟨l, e⟩ => subst e; exact ⟨N l, .redex (.leading_zero l)⟩
      | .inr hnz =>
        have hfinish : ¬ Each IsNormal xs → ∃ y, OneStepReduce (N xs) y := fun h => by
          obtain ⟨l₁, l₂, x, x', e, hr⟩ := find_reducible xs ih h
          subst e
          exact ⟨_, .cong l₁ l₂ hr⟩
        match activeSubtermDec xs with
        | .inl ⟨x, hx⟩ =>
          match decOrder (N xs) x with
          | .inl (.inr heq) => exact ⟨x, .redex (.fixpoint hx ((eq_correct _ _).2 heq))⟩
          | .inl (.inl hlt) =>
            exact absurd (lt_of_lt_of_le hlt (active_subterm_le hx _ onePlus_normal)) (lt_irrefl _)
          | .inr hgt =>
            exact hfinish fun heach => hn ((normal_alt xs).2 ⟨hnz, heach,
              fun y hy => active_subterm_unique hx hy ▸ hgt⟩)
        | .inr hz =>
          exact hfinish fun heach => hn ((normal_alt xs).2 ⟨hnz, heach,
            fun y hy => (active_subterm_all_zeros hz hy).elim⟩)
    · rintro ⟨y, hy⟩ hn
      cases hy with
      | redex r =>
        cases r with
        | leading_zero l => exact hn.1 rfl
        | fixpoint hx hc =>
          exact lt_irrefl _ (lt_of_lt_of_le (((normal_alt _).1 hn).2.2 _ hx)
            ((eq_correct _ _).1 hc).le)
      | cong l₁ l₂ h =>
        have hx := ((CantorDecomposition.each_app _ _ _).1 ((isNormal_N _).1 hn).2.1).2.1
        exact ((CantorDecomposition.each_app _ _ _).1 ih).2.1.2 ⟨_, h⟩ hx

/-- Rocq: `Notation.SchutteStack.VF_normal_no_redex`. -/
theorem normal_no_redex (x : VForm) : IsNormal x ↔ ¬ ∃ y, OneStepReduce x y :=
  match isNormalDec x with
  | isTrue h => ⟨fun _ hr => (notIsNormal_redex x).2 hr h, fun _ => h⟩
  | isFalse h => ⟨fun h' => absurd h' h, fun hr => absurd ((notIsNormal_redex x).1 h) hr⟩

/-- `x` reduces to the normal form `y`. Rocq: `Notation.SchutteStack.normalizes`. -/
inductive Normalizes : VForm → VForm → Prop
  | normal {x : VForm} : (¬ ∃ y, OneStepReduce x y) → Normalizes x x
  | step {x y z : VForm} : OneStepReduce x y → Normalizes y z → Normalizes x z

/-- Rocq: `Notation.SchutteStack.one_step_reduce_size`. -/
theorem one_step_reduce_size {x y : VForm} : OneStepReduce x y → termSize y < termSize x
  | .redex h => redex_size h
  | .cong (x := x) (x' := x') l₁ l₂ h => by
    show listSize (l₁ ++ x' :: l₂) + 1 < listSize (l₁ ++ x :: l₂) + 1
    rw [listSize_app, listSize_app]
    exact Nat.succ_lt_succ (Nat.add_lt_add_left
      (Nat.succ_lt_succ (Nat.add_lt_add_right (one_step_reduce_size h) _)) _)

/-- Rocq: `Notation.SchutteStack.normalizes_eq`. -/
theorem normalizes_eq {x y : VForm} : Normalizes x y → denote x ≈ denote y
  | .normal _ => equiv_refl _
  | .step h₁ h₂ => equiv_trans (one_step_reduce_sound h₁) (normalizes_eq h₂)

/-- Rocq: `Notation.SchutteStack.normalizes_normal`. -/
theorem normalizes_normal {x y : VForm} : Normalizes x y → IsNormal y
  | .normal h => (normal_no_redex _).2 h
  | .step _ h₂ => normalizes_normal h₂

/-- Every form has a unique normal form, reached by reduction.
Rocq: `Notation.SchutteStack.strongly_normalizing`. -/
theorem strongly_normalizing (x : VForm) :
    ∃ y, Normalizes x y ∧ ∀ y', Normalizes x y' → y' = y := by
  suffices h : ∀ n x, termSize x < n → ∃ y, Normalizes x y ∧ ∀ y', Normalizes x y' → y' = y from
    h _ x (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun x h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx
    match isNormalDec x with
    | isTrue h =>
      refine ⟨x, .normal ((normal_no_redex x).1 h), fun y' hy' => ?_⟩
      cases hy' with
      | normal _ => rfl
      | step h₁ _ => exact absurd ⟨_, h₁⟩ ((normal_no_redex x).1 h)
    | isFalse h =>
      obtain ⟨y, hy⟩ := (notIsNormal_redex x).1 h
      obtain ⟨z, hz, _⟩ :=
        ih y (Nat.lt_of_lt_of_le (one_step_reduce_size hy) (Nat.le_of_lt_succ hx))
      refine ⟨z, .step hy hz, fun q hq => normal_form_unique _ _ (normalizes_normal hq)
        (normalizes_normal hz) ?_⟩
      exact equiv_trans (equiv_symm (normalizes_eq hq))
        (equiv_trans (one_step_reduce_sound hy) (normalizes_eq hz))

/-- Rocq: `Notation.SchutteStack.delete_leading_zeros`. -/
def deleteLeadingZeros : List VForm → List VForm
  | [] => []
  | Z :: xs => deleteLeadingZeros xs
  | N l :: xs => N l :: xs

/-- Rocq: `Notation.SchutteStack.delete_leading_zeros_correct`. -/
theorem delete_leading_zeros_correct : ∀ xs : List VForm,
    denote (N (deleteLeadingZeros xs)) ≈ denote (N xs) ∧ NoLeadingZeros (deleteLeadingZeros xs)
  | [] => ⟨equiv_refl _, trivial⟩
  | Z :: xs =>
    let ih := delete_leading_zeros_correct xs
    ⟨equiv_trans ih.1 (equiv_symm (schutte_stack_leading_zero _ (denoteList xs) 0 onePlus_normal)),
      ih.2⟩
  | N _ :: _ => ⟨equiv_refl _, fun h => VForm.noConfusion h⟩

private theorem each_deleteLeadingZeros {P : VForm → Prop} :
    ∀ xs : List VForm, Each P xs → Each P (deleteLeadingZeros xs)
  | [], h => h
  | Z :: xs, h => each_deleteLeadingZeros xs h.2
  | N _ :: _, h => h

/-- Rocq: `Notation.SchutteStack.find_active_subterm`. -/
def findActiveSubterm (r : Option VForm) : List VForm → Option VForm
  | [] => r
  | Z :: xs => findActiveSubterm r xs
  | N l :: xs => findActiveSubterm (some (N l)) xs

/-- Rocq: `Notation.SchutteStack.is_active_subterm`. -/
def IsActiveSubterm : Option VForm → List VForm → Prop
  | none, xs => Each (fun x => x = Z) xs
  | some x, xs => ActiveSubterm xs x

/-- Rocq: `Notation.SchutteStack.active_subterm_app`. -/
theorem active_subterm_app : ∀ (xs : List VForm) {ys : List VForm} {x : VForm},
    ActiveSubterm ys x → ActiveSubterm (xs ++ ys) x
  | [], _, _, h => h
  | _ :: xs, _, _, h => .later (active_subterm_app xs h)

/-- Rocq: `Notation.SchutteStack.active_subterm_last_Z`. -/
theorem active_subterm_last_Z {xs : List VForm} {x : VForm} (h : ActiveSubterm xs x) :
    ActiveSubterm (xs ++ [Z]) x := by
  induction h with
  | last hx hz => exact .last hx ((CantorDecomposition.each_app _ _ _).2 ⟨hz, rfl, trivial⟩)
  | later _ ih => exact .later ih

/-- Rocq: `Notation.SchutteStack.active_subterm_last_N`. -/
theorem active_subterm_last_N : ∀ (xs l : List VForm), ActiveSubterm (xs ++ [N l]) (N l)
  | [], _ => .last (fun h => VForm.noConfusion h) trivial
  | _ :: xs, l => .later (active_subterm_last_N xs l)

/-- Rocq: `Notation.SchutteStack.find_active_subterm_correct_aux`. -/
theorem find_active_subterm_correct_aux : ∀ (ys xs : List VForm) (r : Option VForm),
    IsActiveSubterm r xs → IsActiveSubterm (findActiveSubterm r ys) (xs ++ ys)
  | [], xs, r, h => by rw [ConstructiveOrdinals.List.append_nil]; exact h
  | Z :: ys, xs, r, h => by
    have e : xs ++ Z :: ys = (xs ++ [Z]) ++ ys := (ConstructiveOrdinals.List.append_assoc xs [Z] ys).symm
    rw [e]
    refine find_active_subterm_correct_aux ys _ r ?_
    cases r with
    | none => exact (CantorDecomposition.each_app _ _ _).2 ⟨h, rfl, trivial⟩
    | some x => exact active_subterm_last_Z h
  | N l :: ys, xs, _, _ => by
    have e : xs ++ N l :: ys = (xs ++ [N l]) ++ ys := (ConstructiveOrdinals.List.append_assoc xs [N l] ys).symm
    rw [e]
    exact find_active_subterm_correct_aux ys _ (some (N l)) (active_subterm_last_N xs l)

/-- Rocq: `Notation.SchutteStack.find_active_subterm_correct`. -/
theorem find_active_subterm_correct (xs : List VForm) :
    IsActiveSubterm (findActiveSubterm none xs) xs :=
  find_active_subterm_correct_aux xs [] none trivial

/-- Normalize the top level of `N l`: drop leading zeros, and collapse to the
active subterm when it is a fixpoint. Rocq: `Notation.SchutteStack.Nnorm`. -/
def nnorm (l : List VForm) : VForm :=
  match findActiveSubterm none (deleteLeadingZeros l) with
  | none => N (deleteLeadingZeros l)
  | some x =>
    match compare x (N (deleteLeadingZeros l)) with
    | .lt => N (deleteLeadingZeros l)
    | .eq => x
    | .gt => x

/-- Rocq: `Notation.SchutteStack.Nnorm_eq`. -/
theorem nnorm_eq (l : List VForm) : denote (nnorm l) ≈ denote (N l) := by
  have hd := delete_leading_zeros_correct l
  have hf := find_active_subterm_correct (deleteLeadingZeros l)
  show denote (match findActiveSubterm none (deleteLeadingZeros l) with
    | none => N (deleteLeadingZeros l)
    | some x =>
      match compare x (N (deleteLeadingZeros l)) with
      | .lt => N (deleteLeadingZeros l)
      | .eq => x
      | .gt => x) ≈ _
  revert hf
  cases findActiveSubterm none (deleteLeadingZeros l) with
  | none => exact fun _ => hd.1
  | some v =>
    intro hv
    show denote (match compare v (N (deleteLeadingZeros l)) with
      | .lt => N (deleteLeadingZeros l)
      | .eq => v
      | .gt => v) ≈ _
    have hc := compare_correct v (N (deleteLeadingZeros l))
    revert hc
    cases compare v (N (deleteLeadingZeros l)) with
    | lt => exact fun _ => hd.1
    | eq => exact fun hc => equiv_trans hc hd.1
    | gt =>
      exact fun hc => (lt_irrefl _ (lt_of_lt_of_le hc (active_subterm_le hv _ onePlus_normal))).elim

private theorem active_subterm_mem {P : VForm → Prop} {l : List VForm} {x : VForm}
    (h : ActiveSubterm l x) (hl : Each P l) : P x := by
  induction h with
  | last _ _ => exact hl.1
  | later _ ih => exact ih hl.2

/-- Rocq: `Notation.SchutteStack.Nnorm_normal`. -/
theorem nnorm_normal (l : List VForm) (hl : Each IsNormal l) : IsNormal (nnorm l) := by
  have hd := delete_leading_zeros_correct l
  have he := each_deleteLeadingZeros l hl
  have hf := find_active_subterm_correct (deleteLeadingZeros l)
  show IsNormal (match findActiveSubterm none (deleteLeadingZeros l) with
    | none => N (deleteLeadingZeros l)
    | some x =>
      match compare x (N (deleteLeadingZeros l)) with
      | .lt => N (deleteLeadingZeros l)
      | .eq => x
      | .gt => x)
  revert hf
  cases findActiveSubterm none (deleteLeadingZeros l) with
  | none =>
    exact fun hz => (normal_alt _).2 ⟨hd.2, he, fun x hx => (active_subterm_all_zeros hz hx).elim⟩
  | some v =>
    intro hv
    have hvn : IsNormal v := active_subterm_mem hv he
    show IsNormal (match compare v (N (deleteLeadingZeros l)) with
      | .lt => N (deleteLeadingZeros l)
      | .eq => v
      | .gt => v)
    have hc := compare_correct v (N (deleteLeadingZeros l))
    revert hc
    cases compare v (N (deleteLeadingZeros l)) with
    | lt =>
      exact fun hc => (normal_alt _).2 ⟨hd.2, he, fun y hy => active_subterm_unique hv hy ▸ hc⟩
    | eq => exact fun _ => hvn
    | gt => exact fun _ => hvn

mutual
/-- Rocq: `Notation.SchutteStack.VF_normalize`. -/
def normalize : VForm → VForm
  | Z => Z
  | N l => nnorm (normalizeList l)

/-- `List.map normalize`. -/
def normalizeList : List VForm → List VForm
  | [] => []
  | x :: xs => normalize x :: normalizeList xs
end

private theorem each_normalizeList {P : VForm → Prop} :
    ∀ xs : List VForm, Each (fun x => P (normalize x)) xs → Each P (normalizeList xs)
  | [], _ => trivial
  | _ :: xs, h => ⟨h.1, each_normalizeList xs h.2⟩

/-- Rocq: `Notation.SchutteStack.VF_normalize_normal`. -/
theorem normalize_normal : ∀ x : VForm, IsNormal (normalize x) :=
  induction' _ trivial fun xs ih => nnorm_normal _ (each_normalizeList xs ih)

/-- Stacks with pointwise equivalent entries over pointwise equivalent
functions are equivalent. -/
theorem stack_congr {xs ys : List Ordinal.{0}} (h : Forall₂ (· ≈ ·) xs ys) :
    ∀ (f g : Ordinal.{0} → Ordinal.{0}) (x : Ordinal.{0}), (∀ a b, a ≤ b → f a ≤ f b) →
      (∀ a b, a ≤ b → g a ≤ g b) → (∀ z, f z ≈ g z) → schutteStack f xs x ≈ schutteStack g ys x := by
  induction h with
  | nil => exact fun f g x _ _ hfg => hfg x
  | cons hab hr ih =>
    intro f g x hf hg hfg
    show schutteStack (schutteColumn f _ _) _ x ≈ schutteStack (schutteColumn g _ _) _ x
    rw [hr.length_eq]
    exact ih _ _ x (fun _ _ h => schutte_column_monotone f _ _ _ _ _ hf (le_refl _) h)
      (fun _ _ h => schutte_column_monotone g _ _ _ _ _ hg (le_refl _) h)
      (fun z => equiv_intro
        (schutte_column_monotone_func f g _ _ z _ z hf hg (fun w => (hfg w).le) hab.le (le_refl z))
        (schutte_column_monotone_func g f _ _ z _ z hg hf (fun w => (hfg w).ge) hab.ge (le_refl z)))

/-- Rocq: `Notation.SchutteStack.VF_normalize_eq`. -/
theorem normalize_eq : ∀ x : VForm, denote (normalize x) ≈ denote x := by
  refine induction' _ (equiv_refl _) fun xs ih => equiv_trans (nnorm_eq _) ?_
  have hpw : Forall₂ (· ≈ ·) (denoteList (normalizeList xs)) (denoteList xs) := by
    induction xs with
    | nil => exact .nil
    | cons _ xs ihx => exact .cons ih.1 (ihx ih.2)
  exact stack_congr hpw _ _ 0 onePlus_normal.monotone onePlus_normal.monotone (fun z => equiv_refl _)

/-! ## Cantor decomposition -/

/-- `N [x]` denotes `1 + x`. -/
theorem denote_one (x : VForm) : denote (N [x]) ≈ 1 + denote x :=
  equiv_trans (schutte_stack_zero_column _ _ 0) (add_congr (equiv_refl 1) (add_zero _))

/-- `N [x, y]` denotes `ω ^ x + y`. -/
theorem denote_two (x y : VForm) : denote (N [x, y]) ≈ ω ^ denote x + denote y :=
  equiv_trans (schutte_stack_veblen _ _ _ 0 onePlus_normal (complete x) (complete y) zero_complete)
    (equiv_trans (veblen_congr onePlus_normal.monotone (equiv_refl _) (add_zero _))
      (veblen_onePlus _ (complete x) _ (complete y)))

/-- `N [a, Z, c]` denotes the second Schütte column at `a` and `c`. -/
theorem denote_aZc (a c : VForm) :
    denote (N [a, Z, c]) ≈ schutteColumn (fun y => 1 + y) 2 (denote a) (denote c) := by
  have hmono := fun γ : Ordinal.{0} => fun x y (h : x ≤ y) =>
    schutte_column_monotone (fun y => 1 + y) 2 γ x γ y onePlus_normal.monotone (le_refl _) h
  refine equiv_trans (schutte_column0 _ _ 0) (equiv_trans
    (schutte_column_arg0 1 _ _ (hmono _)) ?_)
  exact equiv_intro (hmono _ _ _ (add_zero _).le) (hmono _ _ _ (add_zero _).ge)

/-- Rocq: `Notation.SchutteStack.schutte_stack_epsilon`. -/
theorem schutte_stack_epsilon (l : List VForm) (hl : NoLeadingZeros l) (hlen : 2 < l.length) :
    ω ^ denote (N l) ≤ denote (N l) := by
  have heq := sparse_matrix_eq l _ 0 onePlus_normal zero_complete
  refine le_trans (pow_le_pow_right ω heq.le) (le_trans ?_ heq.ge)
  match l, hl, hlen with
  | v :: l₀, hv, hlen =>
    cases v with
    | Z => exact absurd rfl hv
    | N lv =>
      have hβ : (1 : Ordinal.{0}) < ofNat l₀.length := ofNat_increasing (Nat.lt_of_succ_lt_succ hlen)
      have hα : (0 : Ordinal.{0}) < denote (N lv) := N_pos lv
      have hf' := schutte_column_normal (ofNat l₀.length) (denote (N lv)) _ (ofNat_complete _)
        (complete _) onePlus_normal
      refine schutte_matrix_fixpoint1 (sparseMatrix (sparseStack l₀)) 0 _ powOmega
        (all_complete_sparse_matrix _) zero_complete hf' powOmega_normal fun z hz => ?_
      have hg := schutte_column_normal (ofNat l₀.length) 0 _ (ofNat_complete _) zero_complete
        onePlus_normal
      have ht := hf'.complete z hz
      calc ω ^ schutteColumn _ (ofNat l₀.length) (denote (N lv)) z
          ≤ ω ^ schutteColumn _ (ofNat l₀.length) (denote (N lv)) z + 0 := (add_zero _).ge
        _ ≈ veblen (fun y => 1 + y) (schutteColumn _ (ofNat l₀.length) (denote (N lv)) z) 0 :=
            equiv_symm (veblen_onePlus _ ht _ zero_complete)
        _ ≤ veblen (schutteColumn (fun y => 1 + y) (ofNat l₀.length) 0)
              (schutteColumn _ (ofNat l₀.length) (denote (N lv)) z) 0 :=
            veblen_monotone_func onePlus_normal hg
              (fun i _ => (schutte_column_arg0 _ i _ onePlus_normal.monotone).ge) _ _ ht zero_complete
        _ ≈ schutteColumn (schutteColumn (fun y => 1 + y) (ofNat l₀.length) 0) 1
              (schutteColumn _ (ofNat l₀.length) (denote (N lv)) z) 0 :=
            equiv_symm (schutte_column_veblen _ 0 _ hg ht zero_complete)
        _ ≤ schutteColumn _ (ofNat l₀.length) (denote (N lv)) z :=
            schutte_column_fixpoint _ _ z _ 1 0 (ofNat_complete _) (complete _) onePlus_normal hβ hα
              (ofNat_complete 1) zero_complete hz

/-- Rocq: `Notation.SchutteStack.VF_decompose`. -/
def decompose : VForm → List VForm
  | Z => []
  | N [] => [Z]
  | N [x] => Z :: decompose x
  | N [x, y] => x :: decompose y
  | N (x :: y :: z :: l) => [N (x :: y :: z :: l)]

/-- Rocq: `Notation.SchutteStack.VF_recompose`. -/
def recompose : List VForm → VForm
  | [] => Z
  | [x] =>
    match x with
    | Z => N []
    | N [] => N [N [], Z]
    | N [a] => N [N [a], Z]
    | N [a, b] => N [N [a, b], Z]
    | N (a :: b :: c :: l) => N (a :: b :: c :: l)
  | Z :: x' :: xs' => N [recompose (x' :: xs')]
  | N l :: x' :: xs' => N [N l, recompose (x' :: xs')]

open CantorDecomposition Interpolants in
/-- Rocq: `Notation.SchutteStack.VF_decompose_correct`. -/
theorem decompose_correct : ∀ x : VForm, IsNormal x →
    Each IsNormal (decompose x) ∧ CantorOrdered denote (decompose x) ∧
      denote x ≈ cantorDenote denote (decompose x)
  | Z, _ => ⟨trivial, trivial, equiv_refl _⟩
  | N [], _ => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
      add_congr (equiv_symm (pow_zero ω)) (equiv_refl _)⟩
  | N [x], h => by
    have h' := (isNormal_N _).1 h
    have ih := decompose_correct x h'.2.1.1
    have hx1 := denote_one x
    refine ⟨⟨trivial, ih.1⟩, ⟨?_, ih.2.1⟩,
      equiv_trans hx1 (add_congr (equiv_symm (pow_zero ω)) ih.2.2)⟩
    -- the leading exponent of `x` is zero, or else `1 + x ≈ x`
    have hlt : denote x < denote (N [x]) := h'.2.2.1
    revert ih
    cases decompose x with
    | nil => exact fun _ => trivial
    | cons d ds =>
      intro ih
      cases d with
      | Z => exact le_refl _
      | N ld =>
        refine (lt_irrefl _ (lt_of_lt_of_le hlt (le_trans hx1.le ?_))).elim
        calc 1 + denote x
            ≈ 1 + (ω ^ denote (N ld) + cantorDenote denote ds) := add_congr (equiv_refl 1) ih.2.2
          _ ≈ (1 + ω ^ denote (N ld)) + cantorDenote denote ds := add_assoc _ _ _
          _ ≤ ω ^ denote (N ld) + cantorDenote denote ds :=
              add_le_add (additively_closed_collapse (powOmega_additively_closed (complete _))
                (lt_of_le_of_lt (pow_zero ω).ge (pow_lt_pow_right omega_gt1 (N_pos ld)))) (le_refl _)
          _ ≈ denote x := equiv_symm ih.2.2
  | N [x, y], h => by
    have h' := (isNormal_N _).1 h
    have ih := decompose_correct y h'.2.1.2.1
    have hxy := denote_two x y
    refine ⟨⟨h'.2.1.1, ih.1⟩, ⟨?_, ih.2.1⟩, equiv_trans hxy (add_congr (equiv_refl _) ih.2.2)⟩
    have hlt : denote y < denote (N [x, y]) := h'.2.2.2.1
    revert ih
    cases decompose y with
    | nil => exact fun _ => trivial
    | cons d ds =>
      intro ih
      match decOrder d x with
      | .inl (.inl h) => exact le_of_lt h
      | .inl (.inr h) => exact h.le
      | .inr hgt =>
        refine (lt_irrefl _ (lt_of_lt_of_le hlt (le_trans hxy.le ?_))).elim
        calc ω ^ denote x + denote y
            ≈ ω ^ denote x + (ω ^ denote d + cantorDenote denote ds) := add_congr (equiv_refl _) ih.2.2
          _ ≈ (ω ^ denote x + ω ^ denote d) + cantorDenote denote ds := add_assoc _ _ _
          _ ≤ ω ^ denote d + cantorDenote denote ds :=
              add_le_add (pow_add_collapse (complete d) hgt) (le_refl _)
          _ ≈ denote y := equiv_symm ih.2.2
  | N (x :: y :: z :: l), h =>
    ⟨⟨h, trivial⟩, ⟨trivial, trivial⟩,
      equiv_intro (le_trans (normal_inflationary powOmega_normal _ (complete _)) (add_zero _).ge)
        (le_trans (add_zero _).le (schutte_stack_epsilon _ ((isNormal_N _).1 h).1
          (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))))⟩

/-- Rocq: `Notation.SchutteStack.expOmega_denote`. -/
theorem expOmega_denote (x : VForm) : ω ^ denote x ≈ denote (N [x, Z]) :=
  equiv_symm (equiv_trans (denote_two x Z) (add_zero _))

theorem recompose_ne_Z : ∀ (x : VForm) (xs : List VForm), recompose (x :: xs) ≠ Z
  | Z, [] => fun h => VForm.noConfusion h
  | N [], [] => fun h => VForm.noConfusion h
  | N [_], [] => fun h => VForm.noConfusion h
  | N [_, _], [] => fun h => VForm.noConfusion h
  | N (_ :: _ :: _ :: _), [] => fun h => VForm.noConfusion h
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

/-- The forms that `recompose` wraps as `N [x, Z]`: those with at most two
entries. -/
private def Small : VForm → Prop
  | Z => True
  | N [] => True
  | N [_] => True
  | N [_, _] => True
  | N (_ :: _ :: _ :: _) => False

/-- `x < ω ^ x` for the normal forms that `recompose` wraps. -/
private theorem lt_powOmega_small : ∀ x : VForm, IsNormal x → Small x → denote x < ω ^ denote x
  | Z, _, _ => pow_pos ω 0
  | N [], _, _ =>
    lt_of_le_of_lt (add_zero 1).le (lt_of_lt_of_le omega_gt1 (le_trans (pow_one' omega_gt0).ge
      (pow_le_pow_right ω (add_zero 1).ge)))
  | N [y], h, _ => by
    have h' := (isNormal_N _).1 h
    have hy₀ : 0 < denote y := (VF_nonzero y).2 h'.1
    have h1 := denote_one y
    refine lt_of_le_of_lt h1.le (lt_of_lt_of_le ?_ (pow_le_pow_right ω h1.ge))
    calc 1 + denote y
        ≤ 1 + ω ^ denote y := add_le_add (le_refl 1) (normal_inflationary powOmega_normal _ (complete y))
      _ ≤ ω ^ denote y := additively_closed_collapse (powOmega_additively_closed (complete y))
          (lt_of_le_of_lt (pow_zero ω).ge (pow_lt_pow_right omega_gt1 hy₀))
      _ < ω ^ (1 + denote y) := pow_lt_pow_right omega_gt1 (lt_of_lt_of_le h'.2.2.1 h1.le)
  | N [y, z], h, _ => by
    have h' := (isNormal_N _).1 h
    exact lt_of_le_of_lt (denote_two y z).le (powOmega_additively_closed (complete _) _ _
      (pow_lt_pow_right omega_gt1 h'.2.2.1)
      (lt_of_lt_of_le h'.2.2.2.1 (normal_inflationary powOmega_normal _ (complete _))))
  | N (_ :: _ :: _ :: _), _, h => h.elim

open CantorDecomposition Interpolants in
/-- Rocq: `Notation.SchutteStack.VF_recompose_correct`. -/
theorem recompose_correct : ∀ xs : List VForm, Each IsNormal xs → CantorOrdered denote xs →
    IsNormal (recompose xs) ∧ cantorDenote denote xs ≈ denote (recompose xs)
  | [], _, _ => ⟨trivial, equiv_refl _⟩
  | [x], hP, _ => by
    have hwrap : ∀ x : VForm, IsNormal x → x ≠ Z → Small x →
        IsNormal (N [x, Z]) ∧ ω ^ denote x + 0 ≈ denote (N [x, Z]) := fun x hx hx0 hs =>
      ⟨(isNormal_N _).2 ⟨hx0, ⟨hx, trivial, trivial⟩,
          lt_of_lt_of_le (lt_powOmega_small x hx hs) (expOmega_denote x).le,
          lt_of_lt_of_le (pow_pos ω _) (expOmega_denote x).le, trivial⟩,
        equiv_trans (add_zero _) (expOmega_denote x)⟩
    match x, hP with
    | Z, _ => exact ⟨⟨trivial, trivial, trivial⟩, add_congr (pow_zero ω) (equiv_refl _)⟩
    | N [], hP => exact hwrap _ hP.1 (fun h => VForm.noConfusion h) trivial
    | N [_], hP => exact hwrap _ hP.1 (fun h => VForm.noConfusion h) trivial
    | N [_, _], hP => exact hwrap _ hP.1 (fun h => VForm.noConfusion h) trivial
    | N (a :: b :: c :: l), hP =>
      exact ⟨hP.1, equiv_intro
        (le_trans (add_zero _).le (schutte_stack_epsilon _ ((isNormal_N _).1 hP.1).1
          (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))))
        (le_trans (normal_inflationary powOmega_normal _ (complete _)) (add_zero _).ge)⟩
  | x :: x' :: xs', hP, hord => by
    have ih := recompose_correct (x' :: xs') hP.2 hord.2
    have hr := recompose_ne_Z x' xs'
    cases x with
    | Z =>
      -- all the terms are zero, so the sum is finite
      have hx' : denote x' ≈ 0 := equiv_intro hord.1 (zero_least _)
      have hfin := leading_zero_finite (f := denote) xs' x' hord.2 hx'
      have h1 := denote_one (recompose (x' :: xs'))
      refine ⟨(isNormal_N _).2 ⟨hr, ⟨ih.1, trivial⟩, ?_, trivial⟩, ?_⟩
      · refine lt_of_lt_of_le ?_ h1.ge
        refine lt_of_le_of_lt (equiv_trans (equiv_symm ih.2) hfin).le
          (lt_of_lt_of_le ?_ (add_le_add (le_refl 1) (equiv_trans (equiv_symm ih.2) hfin).ge))
        exact lt_of_lt_of_le (succ_lt _) (onePlus_finite_succ _).ge
      · exact equiv_trans (add_congr (pow_zero ω) ih.2) (equiv_symm h1)
    | N l =>
      have h2 := denote_two (N l) (recompose (x' :: xs'))
      have hr₀ := (VF_nonzero _).2 hr
      refine ⟨(isNormal_N _).2 ⟨fun h => VForm.noConfusion h, ⟨hP.1, ih.1, trivial⟩, ?_, ?_, trivial⟩,
        equiv_trans (add_congr (equiv_refl _) ih.2) (equiv_symm h2)⟩
      · exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans
          (normal_inflationary powOmega_normal _ (complete _)) (add_zero _).ge) (add_lt_add_left _ hr₀))
          h2.ge
      · exact lt_of_lt_of_le (lt_of_le_of_lt ih.2.ge (lt_of_lt_of_le
          (cantor_tail_lt (N l) (x' :: xs') hord) (add_le_add (le_refl _) ih.2.le))) h2.ge

open CantorDecomposition Interpolants

/-- Rocq: `Notation.SchutteStack.VF_has_cantor_decomposition`. -/
def hasCantorDecomposition : HasCantorDecomposition denote IsNormal where
  compare := compare
  decompose := decompose
  recompose := recompose
  complete := complete
  compare_correct x y _ _ := compare_correct x y
  decompose_correct := decompose_correct
  recompose_correct := recompose_correct

/-- Rocq: `Notation.SchutteStack.VF_succ`. -/
def succ : VForm → VForm := cantorSucc hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_add`. -/
def add : VForm → VForm → VForm := cantorAdd hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_mul`. -/
def mul : VForm → VForm → VForm := cantorMul hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_exp`. -/
def exp : VForm → VForm → VForm := cantorExp hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_succ_reflects`. -/
theorem succ_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Ordinal.succ succ :=
  cantor_succ_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_add_reflects`. -/
theorem add_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· + ·) add :=
  cantor_add_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_mul_reflects`. -/
theorem mul_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· * ·) mul :=
  cantor_mul_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_exp_reflects`. -/
theorem exp_reflects : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ^ ·) exp :=
  cantor_exp_reflects hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_one`. -/
def one : VForm := N []

/-- Rocq: `Notation.SchutteStack.VF_two`. -/
def two : VForm := N [N []]

/-- Rocq: `Notation.SchutteStack.VF_powOmega`. -/
def powOmega (x : VForm) : VForm := nnorm [x, Z]

/-- Rocq: `Notation.SchutteStack.VF_omega`. -/
def omega : VForm := powOmega one

/-- Rocq: `Notation.SchutteStack.VF_epsilon`. -/
def epsilon (x : VForm) : VForm := nnorm [one, Z, x]

/-- Rocq: `Notation.SchutteStack.VF_gamma`. -/
def gamma (x : VForm) : VForm := nnorm [two, Z, x]

/-- Rocq: `Notation.SchutteStack.VF_ackermann`. -/
def ackermann (a x : VForm) : VForm := nnorm [a, Z, x]

/-- Rocq: `Notation.SchutteStack.VF_FAO`. -/
def FAO : VForm := N [omega, Z, Z]

/-- Rocq: `Notation.SchutteStack.VF_AO`. -/
def AO : VForm := N [one, Z, Z, Z]

/-- Rocq: `Notation.SchutteStack.VF_nat`. -/
def nat : Nat → VForm
  | 0 => Z
  | 1 => N []
  | n + 2 => N [nat (n + 1)]

/-- Rocq: `Notation.SchutteStack.VF_nat_eq`. -/
theorem nat_eq : ∀ n : Nat, denote (nat n) ≈ ofNat n
  | 0 => equiv_refl _
  | 1 => add_zero 1
  | n + 2 => equiv_trans (denote_one _) (equiv_trans (add_congr (equiv_refl 1) (nat_eq (n + 1)))
      (onePlus_finite_succ (n + 1)))

/-- Rocq: `Notation.SchutteStack.VF_nat_normal`. -/
theorem nat_normal : ∀ n : Nat, IsNormal (nat n)
  | 0 => trivial
  | 1 => ⟨trivial, trivial, trivial⟩
  | n + 2 => (isNormal_N _).2 ⟨by cases n <;> exact fun h => VForm.noConfusion h,
      ⟨nat_normal (n + 1), trivial⟩,
      lt_of_le_of_lt (nat_eq (n + 1)).le (lt_of_lt_of_le (succ_lt _) (nat_eq (n + 2)).ge), trivial⟩

/-- Rocq: `Notation.SchutteStack.VF_natOrdSize_reflects`. -/
theorem natOrdSize_reflects (n : Nat) : Reflects VForm denote IsNormal .ord (ofNat n) (nat n) :=
  ⟨equiv_symm (nat_eq n), nat_normal n⟩

/-- Rocq: `Notation.SchutteStack.VF_powOmega_reflects`. -/
theorem powOmega_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Ordinal.powOmega powOmega :=
  fun _ a ⟨hxa, ha⟩ =>
    ⟨equiv_trans (pow_congr (equiv_refl ω) hxa) (equiv_trans (expOmega_denote a)
        (equiv_symm (nnorm_eq _))),
      nnorm_normal _ ⟨ha, trivial, trivial⟩⟩

theorem one_normal : IsNormal one := ⟨trivial, trivial, trivial⟩

/-- Rocq: `Notation.SchutteStack.VF_omega_reflects`. -/
theorem omega_reflects : Reflects VForm denote IsNormal .ord ω omega :=
  let h := powOmega_reflects 1 one ⟨equiv_symm (add_zero 1), one_normal⟩
  ⟨equiv_trans (equiv_symm (pow_one' omega_gt0)) h.1, h.2⟩

private theorem col2_congr {a a' x x' : Ordinal.{0}} (ha : a ≈ a') (hx : x ≈ x') :
    schutteColumn (fun y => 1 + y) 2 a x ≈ schutteColumn (fun y => 1 + y) 2 a' x' :=
  equiv_intro (schutte_column_monotone _ 2 _ _ _ _ onePlus_normal.monotone ha.le hx.le)
    (schutte_column_monotone _ 2 _ _ _ _ onePlus_normal.monotone ha.ge hx.ge)

/-- Rocq: `Notation.SchutteStack.VF_epsilon_reflects`. -/
theorem epsilon_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) ε epsilon :=
  fun _ a ⟨hxa, ha⟩ =>
    ⟨equiv_trans (equiv_intro (ε_monotone hxa.le) (ε_monotone hxa.ge)) (equiv_trans
        (equiv_symm (schutte_column_2_1 _ (complete a))) (equiv_trans
          (col2_congr (equiv_symm (add_zero 1)) (equiv_refl _))
          (equiv_symm (equiv_trans (nnorm_eq _) (denote_aZc one a))))),
      nnorm_normal _ ⟨one_normal, trivial, ha, trivial⟩⟩

/-- Rocq: `Notation.SchutteStack.VF_gamma_reflects`. -/
theorem gamma_reflects : Reflects VForm denote IsNormal (.ord ==> .ord) Γ gamma :=
  fun _ a ⟨hxa, ha⟩ =>
    ⟨equiv_trans (equiv_intro (Γ_monotone hxa.le) (Γ_monotone hxa.ge)) (equiv_trans
        (equiv_symm (schutte_column_2_2 _ (complete a))) (equiv_trans
          (col2_congr (equiv_symm (nat_eq 2)) (equiv_refl _))
          (equiv_symm (equiv_trans (nnorm_eq _) (denote_aZc two a))))),
      nnorm_normal _ ⟨nat_normal 2, trivial, ha, trivial⟩⟩

/-- Rocq: `Notation.SchutteStack.VF_ackermann_tower_reflects`. -/
theorem ackermann_tower_reflects :
    Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (ackermannTower fun y => 1 + y) ackermann :=
  fun _ a ⟨hxa, ha⟩ _ b ⟨hyb, hb⟩ =>
    ⟨equiv_trans (equiv_intro
        (ackermann_tower_monotone _ onePlus_normal.monotone _ _ _ _ hxa.le hyb.le)
        (ackermann_tower_monotone _ onePlus_normal.monotone _ _ _ _ hxa.ge hyb.ge))
      (equiv_trans (equiv_symm (schutte_column_2_ackermann_tower _ _ _ onePlus_normal (complete a)
        (complete b))) (equiv_symm (equiv_trans (nnorm_eq _) (denote_aZc a b)))),
      nnorm_normal _ ⟨ha, trivial, hb, trivial⟩⟩

/-- Rocq: `Notation.SchutteStack.VF_FinAckermannOrdinal`. -/
theorem FinAckermannOrdinal_reflects :
    Reflects VForm denote IsNormal .ord FinAckermannOrdinal FAO :=
  ⟨equiv_trans FinAckermannOrdinal_alt (equiv_trans (equiv_intro
      (ackermann_tower_monotone _ onePlus_normal.monotone _ _ _ _ omega_reflects.1.le (le_refl 0))
      (ackermann_tower_monotone _ onePlus_normal.monotone _ _ _ _ omega_reflects.1.ge (le_refl 0)))
    (equiv_trans (equiv_symm (schutte_column_2_ackermann_tower _ _ _ onePlus_normal (complete omega)
      zero_complete)) (equiv_symm (denote_aZc omega Z)))),
    by decide⟩

/-- Rocq: `Notation.SchutteStack.VF_AO_eq`. -/
theorem AO_eq : denote AO ≈ schutteColumn (fun y => 1 + y) 3 1 0 := by
  have mono : ∀ (f : Ordinal.{0} → Ordinal.{0}) (β α : Ordinal.{0}), (∀ a b, a ≤ b → f a ≤ f b) →
      ∀ a b, a ≤ b → schutteColumn f β α a ≤ schutteColumn f β α b := fun f β α hf _ _ h =>
    schutte_column_monotone f β α _ α _ hf (le_refl _) h
  have m3 := mono _ 3 (1 + 0) onePlus_normal.monotone
  have m2 := mono _ 2 0 m3
  refine equiv_trans (schutte_column0 _ _ 0) (equiv_trans (schutte_column_arg0 1 _ _ m2)
    (equiv_trans (schutte_column_arg0 2 _ _ m3) ?_))
  exact equiv_intro
    (schutte_column_monotone _ 3 _ _ _ _ onePlus_normal.monotone (add_zero 1).le (add_zero 0).le)
    (schutte_column_monotone _ 3 _ _ _ _ onePlus_normal.monotone (add_zero 1).ge (add_zero 0).ge)

/-- Rocq: `Notation.SchutteStack.VF_AckermannOrdinal`. -/
theorem AckermannOrdinal_reflects :
    Reflects VForm denote IsNormal .ord AckermannOrdinal AO := by
  refine ⟨equiv_trans ?_ (equiv_symm AO_eq), by decide⟩
  have hf := onePlus_normal
  have h3 : Complete (3 : Ordinal.{0}) := ofNat_complete 3
  have h1 : Complete (1 : Ordinal.{0}) := ofNat_complete 1
  have hfirst := ackermann_tower_normal_first _ hf
  have hL : Complete (AckermannOrdinal.{0}) :=
    normal_fix_complete 0 zero_complete (normal_inflationary hfirst) hfirst.monotone hfirst.complete
  have hC := (schutte_column_normal 3 1 _ h3 h1 hf).complete 0 zero_complete
  have hg := schutte_column_normal 3 0 _ h3 zero_complete hf
  -- `schutteColumn f 3 0` is `f` up to equivalence
  have hgf : ∀ z, schutteColumn (fun y => 1 + y) 3 0 z ≈ 1 + z := fun z =>
    schutte_column_arg0 3 z _ hf.monotone
  refine equiv_intro ?_ ?_
  · refine normal_fix_least hfirst 0 _ hC (zero_least _) ?_
    calc ackermannTower (fun y => 1 + y) (schutteColumn (fun y => 1 + y) 3 1 0) 0
        ≤ ackermannTower (schutteColumn (fun y => 1 + y) 3 0) (schutteColumn (fun y => 1 + y) 3 1 0) 0 :=
          ackermann_tower_monotone_func _ _ _ _ hf hg hC zero_complete fun z _ => (hgf z).ge
      _ ≈ schutteColumn (schutteColumn (fun y => 1 + y) 3 0) 2 (schutteColumn (fun y => 1 + y) 3 1 0) 0 :=
          equiv_symm (schutte_column_2_ackermann_tower _ _ _ hg hC zero_complete)
      _ ≤ schutteColumn (fun y => 1 + y) 3 1 0 :=
          schutte_column_fixpoint 3 1 0 _ 2 0 h3 h1 hf (ofNat_increasing (Nat.lt_succ_self 2))
            (succ_lt 0) (ofNat_complete 2) zero_complete zero_complete
  · refine le_trans (schutte_column_gt0 3 1 _ 0 h3 h1 zero_complete hf (ofNat_increasing
      (Nat.zero_lt_succ 2)) (succ_lt 0)).le (sup_least fun _ => sup_least fun _ => ?_)
    have hn := schutte_column_normal_arg 2 _ (ofNat_complete 2) hg
    refine normal_fix_least hn _ _ hL (limit_least fun i => nomatch i) ?_
    calc schutteColumn (schutteColumn (fun y => 1 + y) 3 0) 2 AckermannOrdinal 0
        ≈ ackermannTower (schutteColumn (fun y => 1 + y) 3 0) AckermannOrdinal 0 :=
          schutte_column_2_ackermann_tower _ _ _ hg hL zero_complete
      _ ≤ ackermannTower (fun y => 1 + y) AckermannOrdinal 0 :=
          ackermann_tower_monotone_func _ _ _ _ hg hf hL zero_complete fun z _ => (hgf z).le
      _ ≈ AckermannOrdinal := equiv_symm (normal_fixpoint hfirst 0 zero_complete)

/-! ## Interpolants -/

theorem has_interpolants_zero : HasInterpolants denote IsNormal 0 :=
  (has_interpolants_unfold _).2 fun i hi => (lt_irrefl i (lt_of_lt_of_le hi (zero_least i))).elim

/-- Rocq: `Notation.SchutteStack.VF_has_interpolants_nat`. -/
theorem has_interpolants_nat : ∀ n : Nat, HasInterpolants denote IsNormal (ofNat n)
  | 0 => has_interpolants_zero
  | n + 1 => (has_interpolants_unfold _).2 fun _ hi =>
    let ⟨_, hi⟩ := lt_elim hi
    ⟨nat n, nat_normal n, le_trans hi (nat_eq n).ge,
      lt_of_le_of_lt (nat_eq n).le (succ_lt _),
      (has_interpolants_eq_mor (nat_eq n)).2 (has_interpolants_nat n)⟩

/-- Drop the zero entries of a list of indexed arguments.
Rocq: `Notation.SchutteStack.make_sparse`. -/
def makeSparse : List (Nat × VForm) → List (Nat × VForm)
  | [] => []
  | (_, Z) :: xs => makeSparse xs
  | (n, N l) :: xs => (n, N l) :: makeSparse xs

/-- Rocq: `Notation.SchutteStack.make_sparse_correct`. -/
theorem make_sparse_correct : ∀ xs : List (Nat × VForm),
    IsSparse (makeSparse xs) ∧
    (∀ f : Ordinal.{0} → Ordinal.{0}, NormalFunction f →
      schutteMatrix f (sparseMatrix (makeSparse xs)) 0 ≈ schutteMatrix f (sparseMatrix xs) 0) ∧
    (∀ p q, SchutteMatrixProper (sparseMatrix xs) p q → SchutteMatrixProper (sparseMatrix (makeSparse xs)) p q)
  | [] => ⟨trivial, fun _ _ => equiv_refl _, fun _ _ h => h⟩
  | (n, Z) :: xs =>
    let ih := make_sparse_correct xs
    ⟨ih.1, fun f hf => equiv_trans (ih.2.1 f hf)
        (equiv_symm (schutte_matrix_zero_arg [] (sparseMatrix xs) (ofNat n) f 0 hf.monotone
          (ofNat_complete n))),
      fun p q h => ih.2.2 p q (schutte_matrix_proper_monotone _ _ _ _ _ (le_of_lt h.1) (le_refl _) h.2.2)⟩
  | (n, N _) :: xs =>
    let ih := make_sparse_correct xs
    ⟨⟨fun h => VForm.noConfusion h, ih.1⟩,
      fun f hf => ih.2.1 _ (schutte_column_normal _ _ f (ofNat_complete n) (complete _) hf),
      fun _ q h => ⟨h.1, h.2.1, ih.2.2 _ q h.2.2⟩⟩

private theorem length_append' {α : Type u} (ys : List α) : ∀ xs : List α, (xs ++ ys).length = xs.length + ys.length
  | [] => (Nat.zero_add _).symm
  | _ :: xs => by
    show (xs ++ ys).length + 1 = xs.length + 1 + ys.length
    rw [length_append' ys xs, Nat.add_right_comm]

private theorem sparseStack_replicate_Z (ys : List VForm) :
    ∀ k : Nat, sparseStack (List.replicate k Z ++ ys) = sparseStack ys
  | 0 => rfl
  | k + 1 => sparseStack_replicate_Z ys k

private theorem le_of_ofNat_le {m n : Nat} (h : ofNat.{0} m ≤ ofNat n) : m ≤ n :=
  match Nat.lt_or_ge n m with
  | .inl hlt => absurd (lt_of_lt_of_le (ofNat_increasing hlt) h) (lt_irrefl _)
  | .inr hge => hge

/-- Rocq: `Notation.SchutteStack.exhibit_matrix_form_sparse`. -/
theorem exhibit_matrix_form_sparse (xs : List (Nat × VForm)) (p : Ordinal.{0})
    (h₁ : SchutteMatrixProper (sparseMatrix xs) p SmallVeblenOrdinal) (h₂ : IsSparse xs) :
    ∃ y : VForm, denote y ≈ schutteMatrix (fun y => 1 + y) (sparseMatrix xs) 0 := by
  have hys : ∀ (xs : List (Nat × VForm)) (p : Ordinal.{0}),
      SchutteMatrixProper (sparseMatrix xs) p SmallVeblenOrdinal → IsSparse xs →
      ∃ ys : List VForm, sparseStack ys = xs ∧ ofNat ys.length ≤ p := by
    intro xs
    induction xs with
    | nil => exact fun p _ _ => ⟨[], rfl, zero_least p⟩
    | cons q xs ih =>
      intro p h₁ h₂
      obtain ⟨n, a⟩ := q
      obtain ⟨ys, hys₁, hys₂⟩ := ih (ofNat n) h₁.2.2 h₂.2
      cases a with
      | Z => exact absurd rfl h₂.1
      | N l =>
        have hle := le_of_ofNat_le hys₂
        refine ⟨N l :: (List.replicate (n - ys.length) Z ++ ys), ?_, ?_⟩
        · show ((List.replicate (n - ys.length) Z ++ ys).length, N l) ::
            sparseStack (List.replicate (n - ys.length) Z ++ ys) = (n, N l) :: xs
          rw [length_append', length_replicate, ConstructiveOrdinals.Nat.sub_add_cancel hle,
            sparseStack_replicate_Z, hys₁]
        · show Ordinal.succ (ofNat (List.replicate (n - ys.length) Z ++ ys).length) ≤ p
          rw [length_append', length_replicate, ConstructiveOrdinals.Nat.sub_add_cancel hle]
          exact succ_least h₁.1
  obtain ⟨ys, hys₁, _⟩ := hys xs p h₁ h₂
  exact ⟨N ys, hys₁ ▸ sparse_matrix_eq ys _ 0 onePlus_normal zero_complete⟩

/-- Rocq: `Notation.SchutteStack.exhibit_matrix_form`. -/
theorem exhibit_matrix_form (xs : List (Nat × VForm)) (p : Ordinal.{0})
    (h : SchutteMatrixProper (sparseMatrix xs) p SmallVeblenOrdinal) :
    ∃ y : VForm, denote y ≈ schutteMatrix (fun y => 1 + y) (sparseMatrix xs) 0 :=
  let ⟨h₁, h₂, h₃⟩ := make_sparse_correct xs
  let ⟨y, hy⟩ := exhibit_matrix_form_sparse _ p (h₃ p _ h) h₁
  ⟨y, equiv_trans hy (h₂ _ onePlus_normal)⟩

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

/-- The statement of `schutte_column_sparse_matrix_interpolants` for one
column index `n`. -/
private def ColumnInterp (n : Nat) : Prop :=
  ∀ (xs : List (Nat × VForm)) (p : Ordinal.{0}),
    AllComplete (sparseMatrix xs) →
    SchutteMatrixProper (sparseMatrix xs) p SmallVeblenOrdinal →
    Ordinal.succ (ofNat n) ≤ finalIndex p (sparseMatrix xs) →
    NormalFunction (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) →
    (∀ x, Complete x → HI x → HI (schutteMatrix (fun y => 1 + y) (sparseMatrix xs) x)) →
    (∀ a : VForm, HI (denote a) → ∀ x, Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) (denote a) x)) ∧
    (∀ b, Complete b → HI b →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) b 0))

/-- Rocq: `Notation.SchutteStack.schutte_column_sparse_matrix_interpolants`. -/
theorem schutte_column_sparse_matrix_interpolants : ∀ (n : Nat) (xs : List (Nat × VForm)) (p : Ordinal.{0}),
    AllComplete (sparseMatrix xs) →
    SchutteMatrixProper (sparseMatrix xs) p SmallVeblenOrdinal →
    Ordinal.succ (ofNat n) ≤ finalIndex p (sparseMatrix xs) →
    NormalFunction (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) →
    (∀ x, Complete x → HasInterpolants denote IsNormal x →
      HasInterpolants denote IsNormal (schutteMatrix (fun y => 1 + y) (sparseMatrix xs) x)) →
    (∀ a : VForm, HasInterpolants denote IsNormal (denote a) → ∀ x, Complete x →
      HasInterpolants denote IsNormal x →
      HasInterpolants denote IsNormal
        (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) (denote a) x)) ∧
    (∀ b, Complete b → HasInterpolants denote IsNormal b →
      HasInterpolants denote IsNormal
        (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) b 0)) := by
  suffices H : ∀ N n, n < N → ColumnInterp n from fun n => H (n + 1) n (Nat.lt_succ_self n)
  intro N
  induction N with
  | zero => exact fun n h => absurd h (Nat.not_lt_zero _)
  | succ N ihN =>
  intro n hn xs p hxs₁ hxs₂ hxs₃ hf hxs₄
  have hmono := hf.monotone
  have hβ : ofNat n < finalIndex p (sparseMatrix xs) := lt_of_lt_of_le (succ_lt _) hxs₃
  -- Extending the matrix by one more column `(n, c)`.
  have hext : ∀ c : VForm, ∀ k : Nat, n = k + 1 →
      AllComplete (sparseMatrix (xs ++ [(n, c)])) ∧
      SchutteMatrixProper (sparseMatrix (xs ++ [(n, c)])) p SmallVeblenOrdinal ∧
      Ordinal.succ (ofNat k) ≤ finalIndex p (sparseMatrix (xs ++ [(n, c)])) ∧
      ∀ z, schutteMatrix (fun y => 1 + y) (sparseMatrix (xs ++ [(n, c)])) z ≈
        schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) (denote c) z := by
    intro c k hk
    rw [sparse_matrix_app]
    refine ⟨(all_complete_app _ _).2 ⟨hxs₁, ofNat_complete _, complete c, trivial⟩,
      (schutte_matrix_proper_app _ _ _ _).2 ⟨hxs₂, hβ, bounded c, trivial⟩, ?_, ?_⟩
    · show _ ≤ finalIndex p (sparseMatrix xs ++ [(ofNat n, denote c)])
      rw [final_index_last, hk]; exact le_refl _
    · intro z
      show schutteMatrix _ (sparseMatrix xs ++ [(ofNat n, denote c)]) z ≈ _
      rw [schutte_matrix_app]; exact equiv_refl _
  have colN : ∀ c : VForm, NormalFunction
      (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) (denote c)) :=
    fun c => schutte_column_normal _ _ _ (ofNat_complete n) (complete c) hf
  -- The first conjunct.
  have main : ∀ a : VForm, HI (denote a) → ∀ x, Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) (denote a) x) := by
    intro a
    refine measure_ind (motive := fun a => HI (denote a) → ∀ x, Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) (denote a) x))
      (fun a iha ha₁ => ?_) a
    intro x
    refine ltRec (motive := fun x => Complete x → HI x →
      HI (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) (denote a) x))
      (fun x ihx hx₁ hx₂ => ?_) x
    rw [schutte_column_unroll]
    refine has_interpolants_lub _ _ ?_ ((has_interpolants_unfold _).2 fun i hi => ?_)
    · refine hxs₄ _ (add_complete (complete a) hx₁)
        ((has_interpolants_eq_mor (add_congr (normalize_eq a) (equiv_refl x))).1 ?_)
      exact has_interpolants_add add add_reflects (normalize a) x (normalize_normal a)
        ((has_interpolants_eq_mor (normalize_eq a)).2 ha₁) hx₂
    obtain ⟨l, hi⟩ := sup_lt hi
    obtain ⟨a', hi⟩ := sup_lt hi
    cases n with
    | zero => exact nomatch l
    | succ k =>
    obtain ⟨aq, haq₁, haq₂, haq₃, haq₄⟩ :=
      (has_interpolants_unfold _).1 ha₁ ((denote a) a') (index_lt _ a')
    have hcN := colN a
    -- the limit below `x`
    have hlimc : Complete (lim fun i : x.Carrier =>
        schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat (k + 1)) (denote a) (x i)) :=
      lim_complete (fun i => hcN.complete _ (complete_subord hx₁ i))
        (directed_monotone x _ (fun _ _ h => hcN.monotone _ _ h) hx₁) (cast (complete_unfold x) hx₁).2.1
    have hlim : HI (lim fun i : x.Carrier =>
        schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat (k + 1)) (denote a) (x i)) := by
      refine (has_interpolants_unfold _).2 fun j hj => ?_
      obtain ⟨x', hj⟩ := lt_elim hj
      obtain ⟨xq, hxq₁, hxq₂, hxq₃, hxq₄⟩ := (has_interpolants_unfold _).1 hx₂ (x x') (index_lt x x')
      have hproper : SchutteMatrixProper (sparseMatrix (xs ++ [(k + 1, a), (0, xq)])) p SmallVeblenOrdinal := by
        rw [sparse_matrix_app]
        exact (schutte_matrix_proper_app _ _ _ _).2 ⟨hxs₂, hβ, bounded a, ofNat_increasing (Nat.zero_lt_succ k),
          bounded xq, trivial⟩
      obtain ⟨y, hy⟩ := exhibit_matrix_form _ p hproper
      have hy' : denote (normalize y) ≈ schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs))
          (ofNat (k + 1)) (denote a) (denote xq) := by
        refine equiv_trans (normalize_eq y) (equiv_trans hy ?_)
        rw [sparse_matrix_app, schutte_matrix_app]
        exact equiv_trans (schutte_column0 _ _ 0) (equiv_intro (hcN.monotone _ _ (add_zero _).le)
          (hcN.monotone _ _ (add_zero _).ge))
      obtain ⟨x'', hx''⟩ := lt_elim hxq₃
      exact ⟨normalize y, normalize_normal y, le_trans hj (le_trans (hcN.monotone _ _ hxq₂) hy'.ge),
        lt_intro (show (lim fun i : x.Carrier => schutteColumn (schutteMatrix (fun y => 1 + y)
          (sparseMatrix xs)) (ofNat (k + 1)) (denote a) (x i)).Carrier from x'')
          (le_trans hy'.le (hcN.monotone _ _ hx'')),
        (has_interpolants_eq_mor hy').2 (ihx _ hxq₃ (complete xq) hxq₄)⟩
    -- the fixpoint above the limit, for the column at `aq`
    obtain ⟨he₁, he₂, he₃, he₄⟩ := hext aq k rfl
    have hN' := schutte_matrix_normal _ _ he₁ onePlus_normal
    have hIH := (ihN k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt_succ hn))
      (xs ++ [(k + 1, aq)]) p he₁ he₂ he₃ hN'
      (fun x hx hxI => (has_interpolants_eq_mor (he₄ x)).2 (iha aq haq₃ haq₄ x hx hxI))).2
    have hIH : ∀ b, Complete b → HI b → HI (schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
        (sparseMatrix xs)) (ofNat (k + 1)) (denote aq)) (ofNat k) b 0) := fun b hb hbI =>
      (has_interpolants_eq_mor (col_congr hN'.monotone (colN aq).monotone he₄ _ _ _)).1 (hIH b hb hbI)
    have hgN := schutte_column_normal_arg (ofNat k) _ (ofNat_complete k) (colN aq)
    have hfix : HI (fixOrd (fun δ => schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
        (sparseMatrix xs)) (ofNat (k + 1)) (denote aq)) (ofNat k) δ 0) (lim fun i : x.Carrier =>
          schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat (k + 1)) (denote a) (x i))) := by
      refine has_interpolants_sup _ _ fun m => ?_
      induction m.down with
      | zero => exact hlim
      | succ m ihm =>
        exact hIH _ (iterF_complete m _ hlimc hgN.complete) ihm
    have hi' := lt_of_lt_of_le hi (fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono haq₂ (le_refl z))
        (le_refl _) (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN.monotone _ _ h) _)
    obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
    obtain ⟨aq', haq'⟩ := lt_elim haq₃
    refine ⟨z, hz₁, hz₂, lt_of_lt_of_le hz₃ ?_, hz₄⟩
    refine le_trans ?_ (sup_le _ l)
    refine le_trans ?_ (sup_le (fun a' => fixOrd (fun δ => schutteColumn (schutteColumn
      (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat (k + 1)) ((denote a) a')) (ofNat k) δ 0)
      (lim fun i : x.Carrier => schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs))
        (ofNat (k + 1)) (denote a) (x i))) aq')
    have hgN' := schutte_column_normal_arg (ofNat k) _ (ofNat_complete k)
      (schutte_column_normal _ _ _ (ofNat_complete (k + 1)) (complete_subord (complete a) aq') hf)
    exact fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono haq' (le_refl z))
        (le_refl _) (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN'.monotone _ _ h) _
  -- The second conjunct.
  refine ⟨main, fun b => ?_⟩
  refine ltRec (motive := fun b => Complete b → HI b →
    HI (schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat n) b 0))
    (fun b ihb hb₁ hb₂ => ?_) b
  rw [schutte_column_unroll]
  refine has_interpolants_lub _ _ (hxs₄ _ (add_complete hb₁ zero_complete)
    ((has_interpolants_eq_mor (add_zero b)).2 hb₂)) ((has_interpolants_unfold _).2 fun i hi => ?_)
  obtain ⟨l, hi⟩ := sup_lt hi
  obtain ⟨b', hi⟩ := sup_lt hi
  cases n with
  | zero => exact nomatch l
  | succ k =>
  obtain ⟨bq, hbq₁, hbq₂, hbq₃, hbq₄⟩ := (has_interpolants_unfold _).1 hb₂ (b b') (index_lt b b')
  obtain ⟨he₁, he₂, he₃, he₄⟩ := hext bq k rfl
  have hN' := schutte_matrix_normal _ _ he₁ onePlus_normal
  have hIH := (ihN k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt_succ hn))
    (xs ++ [(k + 1, bq)]) p he₁ he₂ he₃ hN'
    (fun x hx hxI => (has_interpolants_eq_mor (he₄ x)).2 (main bq hbq₄ x hx hxI))).2
  have hIH : ∀ b, Complete b → HI b → HI (schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
      (sparseMatrix xs)) (ofNat (k + 1)) (denote bq)) (ofNat k) b 0) := fun b hb hbI =>
    (has_interpolants_eq_mor (col_congr hN'.monotone (colN bq).monotone he₄ _ _ _)).1 (hIH b hb hbI)
  have hgN := schutte_column_normal_arg (ofNat k) _ (ofNat_complete k) (colN bq)
  have hfix : HI (fixOrd (fun δ => schutteColumn (schutteColumn (schutteMatrix (fun y => 1 + y)
      (sparseMatrix xs)) (ofNat (k + 1)) (denote bq)) (ofNat k) δ 0) 0) := by
    refine has_interpolants_sup _ _ fun m => ?_
    induction m.down with
    | zero => exact has_interpolants_zero
    | succ m ihm => exact hIH _ (iterF_complete m _ zero_complete hgN.complete) ihm
  have hb'N := schutte_column_normal_arg (ofNat k) _ (ofNat_complete k)
    (schutte_column_normal _ _ _ (ofNat_complete (k + 1)) (complete_subord hb₁ b') hf)
  have hL : (lim fun i : (0 : Ordinal.{0}).Carrier => schutteColumn (schutteMatrix (fun y => 1 + y)
      (sparseMatrix xs)) (ofNat (k + 1)) b ((0 : Ordinal.{0}) i)) ≤ 0 := limit_least fun i => nomatch i
  have hi' := lt_of_lt_of_le hi (le_trans (fixOrd_monotone (fun _ _ h => hb'N.monotone _ _ h) hL)
    (fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono hbq₂ (le_refl z))
        (le_refl _) (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN.monotone _ _ h) 0))
  obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
  obtain ⟨bq', hbq'⟩ := lt_elim hbq₃
  refine ⟨z, hz₁, hz₂, lt_of_lt_of_le hz₃ ?_, hz₄⟩
  refine le_trans ?_ (sup_le _ l)
  refine le_trans ?_ (sup_le (fun b' => fixOrd (fun δ => schutteColumn (schutteColumn
    (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat (k + 1)) (b b')) (ofNat k) δ 0)
    (lim fun i : (0 : Ordinal.{0}).Carrier => schutteColumn (schutteMatrix (fun y => 1 + y)
      (sparseMatrix xs)) (ofNat (k + 1)) b ((0 : Ordinal.{0}) i))) bq')
  have hgN' := schutte_column_normal_arg (ofNat k) _ (ofNat_complete k)
    (schutte_column_normal _ _ _ (ofNat_complete (k + 1)) (complete_subord hb₁ bq') hf)
  exact le_trans (fixOrd_monotone_func
      (fun δ => schutte_column_monotone_full _ _ _ _ _ _ _ _
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun _ _ h => schutte_column_monotone _ _ _ _ _ _ hmono (le_refl _) h)
        (fun z => schutte_column_monotone _ _ _ z _ z hmono hbq' (le_refl z))
        (le_refl _) (le_refl δ) (le_refl 0))
      (fun _ _ h => hgN'.monotone _ _ h) 0)
    (fixOrd_monotone (fun _ _ h => hgN'.monotone _ _ h) (zero_least _))

/-- Rocq: `Notation.SchutteStack.sparse_stack_interpolants`. -/
theorem sparse_stack_interpolants : ∀ (ys : List VForm) (xs : List (Nat × VForm)) (p : Ordinal.{0}),
    AllComplete (sparseMatrix xs) →
    SchutteMatrixProper (sparseMatrix xs) p SmallVeblenOrdinal →
    ofNat ys.length ≤ finalIndex p (sparseMatrix xs) →
    (∀ x, Complete x → HasInterpolants denote IsNormal x →
      HasInterpolants denote IsNormal (schutteMatrix (fun y => 1 + y) (sparseMatrix xs) x)) →
    Each IsNormal ys → Each (HasInterpolants denote IsNormal) (denoteList ys) →
    HasInterpolants denote IsNormal (schutteStack (schutteMatrix (fun y => 1 + y) (sparseMatrix xs))
      (denoteList ys) 0)
  | [], _, _, _, _, _, hxs₃, _, _ => hxs₃ 0 zero_complete has_interpolants_zero
  | a :: ys, xs, p, hxs₁, hxs₂, hle, hxs₃, hn, hi => by
    have hf := schutte_matrix_normal _ _ hxs₁ onePlus_normal
    have hcolN := schutte_column_normal (ofNat ys.length) (denote a) _ (ofNat_complete _) (complete a) hf
    have hext : ∀ z, schutteMatrix (fun y => 1 + y) (sparseMatrix (xs ++ [(ys.length, a)])) z ≈
        schutteColumn (schutteMatrix (fun y => 1 + y) (sparseMatrix xs)) (ofNat ys.length) (denote a) z := by
      intro z
      rw [sparse_matrix_app]
      show schutteMatrix _ (sparseMatrix xs ++ [(ofNat ys.length, denote a)]) z ≈ _
      rw [schutte_matrix_app]; exact equiv_refl _
    have hxs'₁ : AllComplete (sparseMatrix (xs ++ [(ys.length, a)])) := by
      rw [sparse_matrix_app]
      exact (all_complete_app _ _).2 ⟨hxs₁, ofNat_complete _, complete a, trivial⟩
    have hN' := schutte_matrix_normal _ _ hxs'₁ onePlus_normal
    have hih := sparse_stack_interpolants ys (xs ++ [(ys.length, a)]) p hxs'₁
      (by
        rw [sparse_matrix_app]
        exact (schutte_matrix_proper_app _ _ _ _).2 ⟨hxs₂, lt_of_lt_of_le (succ_lt _) hle, bounded a,
          trivial⟩)
      (by
        rw [sparse_matrix_app]
        show _ ≤ finalIndex p (sparseMatrix xs ++ [(ofNat ys.length, denote a)])
        rw [final_index_last])
      (fun x hx hxI => (has_interpolants_eq_mor (hext x)).2
        ((schutte_column_sparse_matrix_interpolants ys.length xs p hxs₁ hxs₂ hle hf hxs₃).1 a hi.1 x hx hxI))
      hn.2 hi.2
    show HasInterpolants denote IsNormal (schutteStack (schutteColumn _ (ofNat (denoteList ys).length)
      (denote a)) (denoteList ys) 0)
    rw [denoteList_length]
    exact (has_interpolants_eq_mor (stack_congr (Forall₂.equiv_refl _) _ _ 0 hN'.monotone hcolN.monotone
      hext)).1 hih

/-- Rocq: `Notation.SchutteStack.schutte_stack_interpolants`. -/
theorem schutte_stack_interpolants (ys : List VForm) (hn : Each IsNormal ys)
    (hi : Each (HasInterpolants denote IsNormal) (denoteList ys)) :
    HasInterpolants denote IsNormal (schutteStack (fun y => 1 + y) (denoteList ys) 0) :=
  sparse_stack_interpolants ys [] (ofNat ys.length) trivial trivial (le_refl _)
    (fun x _ hx => onePlus_interpolants Z ⟨equiv_refl 0, trivial⟩ (add one)
      (fun x a h => add_reflects 1 one ⟨equiv_symm (add_zero 1), one_normal⟩ x a h) x hx) hn hi

private theorem each_and {P Q R : VForm → Prop} (h : ∀ x, P x → Q x → R x) :
    ∀ l : List VForm, Each P l → Each Q l → Each R l
  | [], _, _ => trivial
  | x :: l, hp, hq => ⟨h x hp.1 hq.1, each_and h l hp.2 hq.2⟩

/-- Rocq: `Notation.SchutteStack.schutte_stack_has_all_interpolants`. -/
theorem schutte_stack_has_all_interpolants : HasAllInterpolants denote IsNormal := by
  intro a
  refine measure_ind (motive := fun a => IsNormal a → HasInterpolants denote IsNormal (denote a))
    (fun a ih ha => ?_) a
  cases a with
  | Z => exact has_interpolants_zero
  | N l =>
    have h := (isNormal_N l).1 ha
    exact schutte_stack_interpolants l h.2.1 ((each_denoteList _ l).2
      (each_and (fun x hx hlt => ih x hlt hx) l h.2.1 h.2.2))

/-- Rocq: `Notation.SchutteStack.VF_nadd`. -/
def nadd : VForm → VForm → VForm := cantorNadd hasCantorDecomposition

/-- Rocq: `Notation.SchutteStack.VF_reflects_nadd`. -/
theorem reflects_nadd : Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) (· ♯ ·) nadd :=
  cantor_nadd_reflects hasCantorDecomposition

/-- The natural product, computed on Cantor normal forms.
Rocq: `Notation.SchutteStack.VF_nmul`. -/
def nmul : VForm → VForm → VForm := CantorProduct.cantorNmul hasCantorDecomposition

/-- Constructively, using interpolants. Rocq: `Notation.SchutteStack.VF_reflects_nmul`. -/
theorem reflects_nmul :
    Reflects VForm denote IsNormal (.ord ==> .ord ==> .ord) NaturalProduct.nmul nmul :=
  CantorProduct.cantor_nmul_reflects hasCantorDecomposition schutte_stack_has_all_interpolants

/-- With the excluded middle, every ordinal below the small Veblen ordinal has
a unique normal form. Rocq's `exists!` is spelled out.
Rocq: `Notation.SchutteStack.VF_has_enough_notations`. -/
theorem has_enough_notations (em : ExcludedMiddle) :
    ∀ x : Ordinal.{0}, x < SmallVeblenOrdinal →
      ∃ a : VForm, (IsNormal a ∧ denote a ≈ x) ∧ ∀ a', IsNormal a' ∧ denote a' ≈ x → a' = a := by
  intro x hx
  obtain ⟨b, hb⟩ := lt_elim (lt_of_lt_of_le hx VF_SVO.ge)
  obtain ⟨c, hc₁, hc₂⟩ := has_interpolants_has_enough_notations em schutte_stack_has_all_interpolants
    (normalize b) x (normalize_normal b) (le_trans hb (normalize_eq b).ge)
  exact ⟨c, ⟨hc₁, hc₂⟩, fun a' ⟨ha₁, ha₂⟩ =>
    normal_form_unique a' c ha₁ hc₁ (equiv_trans ha₂ (equiv_symm hc₂))⟩

/-! ## Sample computations -/

/-- `ω < ω ^ 2 < ε 0` (checked by kernel reduction). -/
theorem sample_compare : compare omega (N [two, Z]) = .lt ∧
    compare (N [two, Z]) (epsilon Z) = .lt := ⟨rfl, rfl⟩

end VForm

end ConstructiveOrdinals.SchutteStackNotation
