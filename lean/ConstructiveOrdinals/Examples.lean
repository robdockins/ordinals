import ConstructiveOrdinals.WellFounded

/-!
# Examples: ordinal measures on data types

Ordinal measures (`Sized` instances) for functions, lists, streams and
countably-branching trees. They are used to define the Ackermann function by
well-founded recursion on a lexicographic measure, and to prove disequalities
such as `x ≠ a :: b :: c :: x` by comparing sizes.

Rocq attaches measures to types with canonical structures, so a lemma such as
`head_lt` takes an `(A : Ord)` and values in its carrier. Here the canonical
structures are `Sized` instances, and these lemmas take a type `α` with a
`[Sized α]` instance. For `α := A.Carrier` this is the Rocq statement. The
named ordinals (`FunOrd`, `ListOrd`, …) are kept as definitions.

Ported from the Rocq file `Examples.v`.
-/

namespace ConstructiveOrdinals

universe u

open Ordinal

namespace Examples

/-! ## Functions -/

/-- Functions into a measured type are measured by the limit of their values.
Rocq: `Examples.funOrd`. -/
def funOrd {A B : Type u} (s : B → Ordinal.{u}) (f : A → B) : Ordinal.{u} :=
  lim fun x => s (f x)

/-- Rocq: `Examples.FunOrd` (a canonical structure). -/
def FunOrd (A : Type u) (B : Ordinal.{u}) : Ordinal.{u} := mk (A → B) (funOrd B.size)

/-- Rocq: `Examples.FunOrd` (as a canonical structure). -/
instance instSizedFun {A B : Type u} [Sized B] : Sized (A → B) := ⟨funOrd sz⟩

/-- Rocq: `Examples.depOrd`. -/
def depOrd {A : Type u} {B : A → Type u} (s : ∀ a, B a → Ordinal.{u}) (f : ∀ a, B a) : Ordinal.{u} :=
  lim fun x => s x (f x)

/-- Rocq: `Examples.DepOrd`. -/
def DepOrd (A : Type u) (B : A → Ordinal.{u}) : Ordinal.{u} :=
  mk (∀ a, B a) (depOrd fun x => (B x).size)

/-- A function is larger than each of its values. Rocq: `Examples.fun_lt`. -/
@[ord_hint]
theorem fun_lt (A : Type u) (B : Ordinal.{u}) (f : A → B) (i : A) : f i ◃ f :=
  limit_lt (fun x => B (f x)) i

/-- Rocq: `Examples.dep_lt`. -/
@[ord_hint]
theorem dep_lt (A : Type u) (B : A → Ordinal.{u}) (f : (DepOrd A B).Carrier) (i : A) :
    sz (f i) < sz f :=
  limit_lt (fun x => (B x).size (f x)) i

/-! ## Lexicographic orders, encoded as ordinals -/

/-- Rocq: `Examples.lex`. -/
def lex (α β : Ordinal.{u}) (x : α) (y : β) : Ordinal.{u} := β * α x + β y

/-- Rocq: `Examples.lex1`. -/
theorem lex1 (α β : Ordinal.{u}) (x x' : α) (y y' : β) (h : x ◃ x') :
    lex α β x y < lex α β x' y' :=
  calc β * α x + β y
      < β * α x + β := add_lt_add_left _ (index_lt β y)
    _ ≈ β * succ (α x) := equiv_symm (mul_succ β (α x))
    _ ≤ β * α x' := mul_le_mul_left β (succ_least h)
    _ ≤ β * α x' + β y' := le_add_right _ _

/-- Rocq: `Examples.lex2`. -/
theorem lex2 (α β : Ordinal.{u}) (x : α) (y y' : β) (h : y ◃ y') :
    lex α β x y < lex α β x y' :=
  add_lt_add_left _ h

/-- The two-argument Ackermann–Péter function, by well-founded recursion on
the lexicographic measure `lex ω ω`. Rocq: `Examples.Ack` (over binary `N`). -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => lex Ordinal.omega.{0} Ordinal.omega.{0} (ULift.up m) (ULift.up n)
decreasing_by
  all_goals first
    | exact lex1 _ _ _ _ _ _ (ofNat_increasing (Nat.le_refl _))
    | exact lex2 _ _ _ _ _ (ofNat_increasing (Nat.le_refl _))

-- The simplified Ackermann function, OEIS A046859.
#guard ack 0 0 = 1
#guard ack 1 1 = 3
#guard ack 2 2 = 7
#guard ack 3 3 = 61

/-- The measures used to define `ack` are bounded by `ω ^ 2`.
Rocq: `Examples.ackermann_bound`. -/
theorem ackermann_bound :
    (sup fun m : (ω : Ordinal.{u}).Carrier => sup fun n : (ω : Ordinal.{u}).Carrier => lex ω ω m n) ≈
      (ω : Ordinal.{u}) ^ (2 : Ordinal.{u}) := by
  refine equiv_trans (y := ω * ω) ?_ (equiv_symm ?_)
  · refine equiv_intro (sup_least fun m => sup_least fun n => ?_) ?_
    · rw [mul_unfold ω ω]
      exact le_trans (add_le_add (le_refl _) (le_of_lt (index_lt ω n)))
        (sup_le (fun i : (ω : Ordinal.{u}).Carrier => ω * ω i + ω) m)
    · rw [mul_unfold ω ω]
      refine sup_least fun m => ?_
      have hm : ∀ n, lex ω ω m n ≤ sup fun m : (ω : Ordinal.{u}).Carrier =>
          sup fun n : (ω : Ordinal.{u}).Carrier => lex ω ω m n := fun n =>
        le_trans (sup_le (fun n : (ω : Ordinal.{u}).Carrier => lex ω ω m n) n)
          (sup_le (fun m : (ω : Ordinal.{u}).Carrier => sup fun n => lex ω ω m n) m)
      rw [add_unfold]
      refine lub_least (le_trans (add_zero _).ge (hm ⟨0⟩)) (sup_least fun n => succ_least ?_)
      exact lt_of_lt_of_le (add_lt_add_left _ (ofNat_increasing (Nat.le_refl _))) (hm ⟨n.down + 1⟩)
  · exact equiv_trans (pow_succ (1 : Ordinal.{u}) omega_gt0)
      (mul_congr (pow_one' omega_gt0) (equiv_refl ω))

/-! ## Helper lemmas for proof search -/

/-- Rocq: `Examples.subterm_trans`. -/
theorem subterm_trans {α β γ : Type u} [Sized α] [Sized β] [Sized γ] (x : α) (y : β) (z : γ) :
    x ◃ y → y ◃ z → x ◃ z :=
  lt_trans

/-- Values of smaller measure are different. Rocq: `Examples.size_discriminate`. -/
theorem size_discriminate {α : Type u} [Sized α] (x y : α) (h : x ◃ y) : x ≠ y := by
  intro e
  subst e
  exact lt_irrefl _ h

/-- Rocq: `Examples.lub_trans1`. -/
@[ord_hint]
theorem lub_trans1 {x y z : Ordinal.{u}} (h : x ≤ y) : x ≤ y ⊔ z := le_trans h (lub_le1 _ _)

/-- Rocq: `Examples.lub_trans2`. -/
@[ord_hint]
theorem lub_trans2 {x y z : Ordinal.{u}} (h : x ≤ z) : x ≤ y ⊔ z := le_trans h (lub_le2 _ _)

/-- Rocq: `Examples.add_trans1`. -/
@[ord_hint]
theorem add_trans1 {x y z : Ordinal.{u}} (h : x ≤ y) : x ≤ y ♯ z := le_trans h (nadd_le1 _ _)

/-- Rocq: `Examples.add_trans1'`. -/
@[ord_hint]
theorem add_trans1' {x y z : Ordinal.{u}} (h : x < y) : x < y ♯ z := lt_of_lt_of_le h (nadd_le1 _ _)

/-- Rocq: `Examples.add_trans2`. -/
@[ord_hint]
theorem add_trans2 {x y z : Ordinal.{u}} (h : x ≤ z) : x ≤ y ♯ z := le_trans h (nadd_le2 _ _)

/-- Rocq: `Examples.add_trans2'`. -/
@[ord_hint]
theorem add_trans2' {x y z : Ordinal.{u}} (h : x < z) : x < y ♯ z := lt_of_lt_of_le h (nadd_le2 _ _)

/-! ## Lists -/

/-- Lists of measured values are measured by the successor-padded natural
sum of their elements. Rocq: `Examples.listOrd`. -/
def listOrd {A : Type u} (f : A → Ordinal.{u}) : List A → Ordinal.{u}
  | [] => 0
  | x :: xs => succ (f x ♯ listOrd f xs)

/-- Rocq: `Examples.ListOrd` (a canonical structure). -/
def ListOrd (A : Ordinal.{u}) : Ordinal.{u} := mk (List A) (listOrd A.size)

/-- Rocq: `Examples.ListOrd` (as a canonical structure). -/
instance instSizedList {α : Type u} [Sized α] : Sized (List α) := ⟨listOrd sz⟩

/-- Rocq: `Examples.listAdd`. -/
theorem size_append {α : Type u} [Sized α] : ∀ xs ys : List α, sz (xs ++ ys) ≈ sz xs ♯ sz ys
  | [], _ => equiv_symm (nadd_zero_l _)
  | _ :: xs, ys =>
    equiv_trans (succ_congruence (equiv_trans (nadd_congr (equiv_refl _) (size_append xs ys))
      (nadd_assoc _ _ _))) (equiv_symm (nadd_succ _ _))

/-- Rocq: `Examples.S_lt`. -/
theorem nat_succ_lt (x : Nat) : x ◃ x.succ := succ_lt _

/-- Rocq: `Examples.head_lt`. -/
@[ord_hint]
theorem head_lt {α : Type u} [Sized α] (h : α) (t : List α) : h ◃ (h :: t) :=
  succ_trans (nadd_le1 _ _)

/-- Rocq: `Examples.tail_lt`. -/
@[ord_hint]
theorem tail_lt {α : Type u} [Sized α] (h : α) (t : List α) : t ◃ (h :: t) :=
  succ_trans (nadd_le2 _ _)

/-- Rocq: `Examples.app_lt1`. -/
theorem app_lt1 {α : Type u} [Sized α] (xs ys : List α) (h : ys ≠ []) : xs ◃ xs ++ ys :=
  match ys, h with
  | [], h => absurd rfl h
  | _ :: _, _ =>
    calc sz xs ≈ sz xs ♯ 0 := equiv_symm (nadd_zero_r _)
      _ < sz xs ♯ sz (_ :: _) := nadd_increasing2 _ (succ_trans (zero_least _))
      _ ≈ sz (xs ++ _ :: _) := equiv_symm (size_append _ _)

/-- Rocq: `Examples.app_lt2`. -/
theorem app_lt2 {α : Type u} [Sized α] (xs ys : List α) (h : xs ≠ []) : ys ◃ xs ++ ys :=
  match xs, h with
  | [], h => absurd rfl h
  | _ :: _, _ =>
    calc sz ys ≈ 0 ♯ sz ys := equiv_symm (nadd_zero_l _)
      _ < sz (_ :: _) ♯ sz ys := nadd_increasing1 _ (succ_trans (zero_least _))
      _ ≈ sz (_ :: _ ++ ys) := equiv_symm (size_append _ _)

private theorem nadd_succ_assoc (a b c : Ordinal.{u}) : a ♯ succ (b ♯ c) ≈ succ ((a ♯ b) ♯ c) :=
  equiv_trans (nadd_succ2 a _) (succ_congruence (nadd_assoc a b c))

/-- Permuting a list does not change its measure.
Rocq: `Examples.Permutation_size`. -/
theorem permutation_size {α : Type u} [Sized α] {r s : List α} (h : Permutation r s) : sz r ≈ sz s := by
  induction h with
  | nil => exact equiv_refl _
  | skip _ _ ih => exact succ_congruence (nadd_congr (equiv_refl _) ih)
  | swap x y l =>
    exact equiv_trans (succ_congruence (nadd_succ_assoc (sz y) (sz x) (sz l)))
      (equiv_trans (succ_congruence (succ_congruence (nadd_congr (nadd_comm _ _) (equiv_refl _))))
        (equiv_symm (succ_congruence (nadd_succ_assoc (sz x) (sz y) (sz l)))))
  | trans _ _ ih₁ ih₂ => exact equiv_trans ih₁ ih₂

/-- Rocq: `Examples.In_lt`. -/
@[ord_hint]
theorem mem_lt {α : Type u} [Sized α] {x : α} {l : List α} (h : x ∈ l) : x ◃ l := by
  induction h with
  | head t => exact head_lt _ t
  | tail b _ ih => exact lt_trans ih (tail_lt b _)

/-- Rocq: `Examples.listOrd_bounded_aux`. -/
theorem listOrd_bounded_aux (A : Type u) (f : A → Ordinal.{u}) :
    ∀ l : List A, listOrd f l ≤ jmul (mk A f) (ofNat l.length)
  | [] => zero_least _
  | a :: l => by
    rw [jmul_unfold]
    refine succ_least ?_
    calc f a ♯ listOrd f l
        ≈ listOrd f l ♯ f a := nadd_comm _ _
      _ < listOrd f l ♯ mk A f := nadd_increasing2 _ (index_lt (mk A f) a)
      _ ≤ jmul (mk A f) (ofNat l.length) ♯ mk A f :=
          nadd_le_nadd (listOrd_bounded_aux A f l) (le_refl _)
      _ ≤ _ := sup_le (fun i : (ofNat.{u} (l.length + 1)).Carrier =>
          jmul (mk A f) (ofNat (l.length + 1) i) ♯ mk A f) PUnit.unit

/-- Rocq: `Examples.listOrd_bounded`. -/
theorem listOrd_bounded (A : Ordinal.{u}) (l : List A) : sz l ≤ jmul A ω := by
  obtain ⟨A, f⟩ := A
  rw [jmul_unfold]
  exact le_trans (listOrd_bounded_aux A f l) (le_trans (nadd_le1 _ _)
    (sup_le (fun i : (ω : Ordinal.{u}).Carrier => jmul (mk A f) (ω i) ♯ mk A f) ⟨l.length⟩))

/-- Rocq: `Examples.listOrd_bounded'`. -/
theorem listOrd_bounded' (A : Ordinal.{u}) (l : List A) : sz l < jmul (succ A) ω := by
  obtain ⟨A, f⟩ := A
  calc listOrd f l
      ≤ jmul (mk A f) (ofNat l.length) := listOrd_bounded_aux A f l
    _ ≤ jmul (succ (mk A f)) (ofNat l.length) := jmul_monotone1 _ (le_of_lt (succ_lt _))
    _ ≤ jmul (succ (mk A f)) (ofNat l.length) ♯ mk A f := nadd_le1 _ _
    _ < succ (jmul (succ (mk A f)) (ofNat l.length) ♯ mk A f) := succ_lt _
    _ ≈ jmul (succ (mk A f)) (ofNat l.length) ♯ succ (mk A f) := equiv_symm (nadd_succ2 _ _)
    _ ≤ jmul (succ (mk A f)) ω := by
        rw [jmul_unfold (succ (mk A f)) ω]
        exact sup_le (fun i : (ω : Ordinal.{u}).Carrier =>
          jmul (succ (mk A f)) (ω i) ♯ succ (mk A f)) ⟨l.length⟩

/-! ## Streams -/

/-- Streams, as functions from the natural numbers. Rocq: `Examples.stream`. -/
def Stream' (A : Type u) : Type u := Nat → A

/-- Rocq: `Examples.streamIdx`. -/
def streamIdx {A : Type u} (n : Nat) (s : Stream' A) : A := s n

/-- Rocq: `Examples.streamCons`. -/
def streamCons {A : Type u} (a : A) (s : Stream' A) : Stream' A := fun n =>
  match n with
  | 0 => a
  | n + 1 => streamIdx n s

/-- Rocq: `Examples.streamAppend`. -/
def streamAppend {A : Type u} : List A → Stream' A → Stream' A
  | [], s => s
  | h :: tl, s => streamCons h (streamAppend tl s)

/-- The measure of a stream. It is arranged so that list prefixes of a stream
are smaller than it (hence the `succ A ×ⱼ ω` term), and the leading `succ`
makes every element smaller than the stream. Rocq: `Examples.streamOrd`. -/
def streamOrd {A : Type u} (f : A → Ordinal.{u}) (s : Stream' A) : Ordinal.{u} :=
  succ (sup fun n : ULift Nat => f (streamIdx n.down s) ♯ jmul (succ (mk A f)) ω)

/-- Rocq: `Examples.StreamOrd` (a canonical structure). -/
def StreamOrd (A : Ordinal.{u}) : Ordinal.{u} := mk (Stream' A) (streamOrd A.size)

/-- Rocq: `Examples.StreamOrd` (as a canonical structure). -/
instance instSizedStream {α : Type u} [Sized α] : Sized (Stream' α) := ⟨streamOrd sz⟩

section streams

variable {α : Type u} [Sized α]

private theorem stream_term_le (s : Stream' α) (n : Nat) :
    sz (streamIdx n s) ♯ jmul (succ (mk α sz)) ω ≤
      sup fun n : ULift Nat => sz (streamIdx n.down s) ♯ jmul (succ (mk α sz)) ω :=
  sup_le (fun n : ULift Nat => sz (streamIdx n.down s) ♯ jmul (succ (mk α sz)) ω) ⟨n⟩

/-- Rocq: `Examples.streamIdx_lt`. -/
theorem streamIdx_lt (s : Stream' α) (n : Nat) : streamIdx n s ◃ s :=
  succ_trans (le_trans (nadd_le1 _ _) (stream_term_le s n))

/-- Rocq: `Examples.streamHead_lt`. -/
theorem streamHead_lt (h : α) (tl : Stream' α) : h ◃ streamCons h tl :=
  succ_trans (le_trans (nadd_le1 _ _) (stream_term_le (streamCons h tl) 0))

/-- Rocq: `Examples.streamTail_le`. -/
theorem streamTail_le (h : α) (tl : Stream' α) : tl ⊴ streamCons h tl :=
  succ_monotone (sup_least fun i => stream_term_le (streamCons h tl) (i.down + 1))

/-- Rocq: `Examples.streamAppend_lt1`. -/
theorem streamAppend_lt1 (xs : List α) (ys : Stream' α) : xs ◃ streamAppend xs ys :=
  match xs with
  | [] => succ_trans (zero_least _)
  | x :: xs =>
    succ_increasing (lt_of_lt_of_le (nadd_increasing2 _ (listOrd_bounded' (mk α sz) xs))
      (stream_term_le (streamCons x (streamAppend xs ys)) 0))

/-- Rocq: `Examples.streamAppend_le2`. -/
theorem streamAppend_le2 : ∀ (xs : List α) (ys : Stream' α), ys ⊴ streamAppend xs ys
  | [], _ => le_refl _
  | x :: xs, ys => le_trans (streamAppend_le2 xs ys) (streamTail_le x _)

end streams

/-! ## Countably-branching rose trees -/

/-- Rocq: `Examples.CountableRoseTree`. -/
inductive CountableRoseTree (A : Type u) : Type u
  /-- Rocq: `RoseNode`. -/
  | node : A → (Nat → CountableRoseTree A) → CountableRoseTree A

/-- Rocq: `Examples.countableRoseOrd`. -/
def countableRoseOrd (A : Type u) (f : A → Ordinal.{u}) : CountableRoseTree A → Ordinal.{u}
  | .node a s => succ (f a ♯ succ (sup fun n : ULift Nat => countableRoseOrd A f (s n.down)))

/-- Rocq: `Examples.CountableRoseOrd` (a canonical structure). -/
def CountableRoseOrd (A : Ordinal.{u}) : Ordinal.{u} :=
  mk (CountableRoseTree A) (countableRoseOrd _ A.size)

/-- Rocq: `Examples.CountableRoseOrd` (as a canonical structure). -/
instance instSizedCountableRoseTree {α : Type u} [Sized α] : Sized (CountableRoseTree α) :=
  ⟨countableRoseOrd α sz⟩

/-- Rocq: `Examples.is_subtree`. -/
inductive IsSubtree {A : Type u} (sub : CountableRoseTree A) : CountableRoseTree A → Prop
  /-- Rocq: `immediate_subtree`. -/
  | immediate (a : A) (s : Nat → CountableRoseTree A) (n : Nat) :
      streamIdx n s = sub → IsSubtree sub (.node a s)
  /-- Rocq: `distant_subtree`. -/
  | distant (a : A) (s : Nat → CountableRoseTree A) (n : Nat) :
      IsSubtree sub (s n) → IsSubtree sub (.node a s)

section rose

variable {α : Type u} [Sized α]

/-- Rocq: `Examples.rose_elem_lt`. -/
theorem rose_elem_lt (a : α) (s : Nat → CountableRoseTree α) : a ◃ CountableRoseTree.node a s :=
  succ_trans (nadd_le1 _ _)

/-- Rocq: `Examples.rose_immediate_subtree_lt`. -/
theorem rose_immediate_subtree_lt (a : α) (s : Nat → CountableRoseTree α) (n : Nat) :
    s n ◃ CountableRoseTree.node a s :=
  succ_trans (le_trans (le_of_lt (succ_trans
    (sup_le (fun n : ULift Nat => countableRoseOrd α sz (s n.down)) ⟨n⟩))) (nadd_le2 _ _))

/-- Rocq: `Examples.rose_subtree_lt`. -/
theorem rose_subtree_lt (sub t : CountableRoseTree α) (h : IsSubtree sub t) : sub ◃ t := by
  induction h with
  | immediate a s n e => subst e; exact rose_immediate_subtree_lt a s n
  | distant a s n _ ih => exact lt_trans ih (rose_immediate_subtree_lt a s n)

/-- Rocq: `Examples.rose_acyclic`. -/
theorem rose_acyclic (sub t : CountableRoseTree α) (h : IsSubtree sub t) : sub ≠ t :=
  size_discriminate _ _ (rose_subtree_lt sub t h)

end rose

/-! ## Proof automation

`ord_crush` proves a disequality `x ≠ y` by showing `x ◃ y`: it searches with
the `ord_hint` lemmas, including the transitivity hints `succ_trans`,
`add_trans1`, `head_lt`, …. Rocq: the Ltac `try_ord`, `subterm_trans`,
`esubterm_trans` and `ord_crush`. -/

set_option hygiene false in
/-- Rocq: Ltac `try_ord`. -/
macro "try_ord" : tactic => `(tactic| try (solve | solve_by_elim (maxDepth := 40) using ord_hint))

/-- Rocq: Ltac `ord_crush`. -/
macro "ord_crush" : tactic => `(tactic| (intros; apply size_discriminate; try_ord))

/-! ### Natural numbers and lists -/

example : ∀ x : Nat, x ≠ Nat.succ (Nat.succ (Nat.succ (Nat.succ x))) := by
  ord_crush

example : ∀ (a b c : Nat) (x : List Nat), x ≠ a :: b :: c :: x := by
  ord_crush

/-! ### Mutually inductive even and odd numbers -/

mutual
/-- Rocq: `Examples.even`. -/
inductive Even : Type
  /-- Rocq: `even0`. -/
  | zero : Even
  /-- Rocq: `evenS`. -/
  | succ : Odd → Even
/-- Rocq: `Examples.odd`. -/
inductive Odd : Type
  /-- Rocq: `oddS`. -/
  | succ : Even → Odd
end

mutual
/-- Rocq: `Examples.even_size`. -/
def evenSize : Even → Ordinal.{0}
  | .zero => 0
  | .succ y => succ (oddSize y)
/-- Rocq: `Examples.odd_size`. -/
def oddSize : Odd → Ordinal.{0}
  | .succ y => succ (evenSize y)
end

/-- Rocq: `Examples.evenOrdSize` (a canonical structure). -/
instance evenOrdSize : Sized Even := ⟨evenSize⟩

/-- Rocq: `Examples.oddOrdSize` (a canonical structure). -/
instance oddOrdSize : Sized Odd := ⟨oddSize⟩

/-- Rocq: `Examples.even_odd_neq`. -/
theorem even_odd_neq : ∀ x : Odd, x ≠ .succ (.succ (.succ (.succ x))) := by
  ord_crush

/-! ### Mutual recursion, nested lists and dependent types

Rocq nests `list (qwerty n)` inside `asdf`. Lean's kernel does not allow a
nested occurrence whose parameter mentions a constructor argument (here `n`),
so the list type is a third member of the mutual block, `QwertyList`. -/

mutual
/-- Rocq: `Examples.asdf`. -/
inductive Asdf : Nat → Type
  /-- Rocq: `mkAsdf`. -/
  | mk (n : Nat) : QwertyList n → Asdf n
/-- Lists of `Qwerty n`; Rocq uses `list (qwerty n)`. -/
inductive QwertyList : Nat → Type
  | nil (n : Nat) : QwertyList n
  | cons (n : Nat) : Qwerty n → QwertyList n → QwertyList n
/-- Rocq: `Examples.qwerty`. -/
inductive Qwerty : Nat → Type
  /-- Rocq: `emptyQwerty`. -/
  | empty : Qwerty 0
  /-- Rocq: `someQwerty`. -/
  | some (n : Nat) : Qwerty n → (∀ m, Asdf m) → Qwerty (n + 1)
end

mutual
/-- Rocq: `Examples.asdf_size`. -/
def asdfSize : (n : Nat) → Asdf n → Ordinal.{0}
  | _, .mk n xs => succ (qwertyListSize n xs)
/-- The measure of a list of `Qwerty n`, as `listOrd (qwertySize n)` in Rocq. -/
def qwertyListSize : (n : Nat) → QwertyList n → Ordinal.{0}
  | _, .nil _ => 0
  | _, .cons n x xs => succ (qwertySize n x ♯ qwertyListSize n xs)
/-- Rocq: `Examples.qwerty_size`. -/
def qwertySize : (n : Nat) → Qwerty n → Ordinal.{0}
  | _, .empty => 0
  | _, .some n x y => succ (qwertySize n x ♯ lim fun m => asdfSize m (y m))
end

/-- The `someQwerty` case of `qwerty_size` as written in Rocq. -/
theorem qwertySize_some (n : Nat) (x : Qwerty n) (y : ∀ m, Asdf m) :
    qwertySize (n + 1) (.some n x y) = succ (qwertySize n x ♯ depOrd asdfSize y) :=
  rfl

/-- Rocq: `Examples.AsdfOrdSize` (a canonical structure). -/
instance AsdfOrdSize (n : Nat) : Sized (Asdf n) := ⟨asdfSize n⟩

/-- Rocq: `Examples.QwertyOrdSize` (a canonical structure). -/
instance QwertyOrdSize (n : Nat) : Sized (Qwerty n) := ⟨qwertySize n⟩

example (n : Nat) (a b : Qwerty (n + 1)) (c : Qwerty n) (f : ∀ m, Asdf m) :
    f (n + 1) ≠ .mk _ (.cons _ a (.cons _ b (.cons _ (.some _ c f) (.nil _)))) := by
  apply size_discriminate
  exact succ_trans (succ_trans' (add_trans2 (succ_trans' (add_trans2 (succ_trans'
    (add_trans1 (succ_trans' (add_trans2 (le_of_lt (dep_lt Nat (fun m => mk (Asdf m) (asdfSize m))
      f (n + 1)))))))))))

end Examples

end ConstructiveOrdinals
