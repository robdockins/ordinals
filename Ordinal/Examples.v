From Stdlib Require Import Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import Permutation.
From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Relations.
From Stdlib Require Import Program.Wf.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Wellfounded.Transitive_Closure.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import NaturalArith.
From Ordinal Require Import WellFounded.

(** Functions into sized types have sizes defined by nontrivial
    limit ordinals.
*)
Definition funOrd {A B:Type} (sz:B -> Ord) (f:A -> B) : Ord :=
  limOrd (fun x => sz (f x)).
Canonical Structure FunOrd (A:Type) (B:Ord) :=
  ord (A -> B) (@funOrd A B (ordSize B)).

Definition depOrd {A:Type} {B:A -> Type} (sz : forall a:A, B a -> Ord) (f:forall a:A, B a) : Ord :=
  limOrd (fun x => sz x (f x)).
Definition DepOrd (A:Type) (B:A -> Ord) :=
  ord (forall a:A, B a) (@depOrd A B (fun x => ordSize (B x))).

(** Functions have larger ordinal size than each of their points. *)
Lemma fun_lt : forall A (B:Ord) (f:A -> B) i, f i ◃ f.
Proof.
  simpl; intros.
  unfold funOrd.
  apply (limit_lt _ (fun x => ordSize B (f x))).
Qed.

Lemma dep_lt : forall (A:Type) (B:A->Ord) (f:DepOrd A B) i, f i ◃ f.
Proof.
  simpl; intros.
  unfold depOrd.
  apply (limit_lt _ (fun x => ordSize (B x) (f x))).
Qed.

Global Hint Resolve fun_lt dep_lt : ord.

(** * Lexicographic orders, encoded as ordinals *)

Definition lex (α β:Ord) (x:α) (y:β) := (β * x + y)%ord.

Lemma lex1 (α β:Ord) (x x':α) (y y':β) :
  x ◃ x' ->
  lex _ _ x y < lex _ _ x' y'.
Proof.
  unfold lex; intros.
  apply ord_lt_le_trans with (β * succOrd x + y').
  - rewrite <- (addOrd_le1 _ (sz y')).
    rewrite mulOrd_succ.
    apply addOrd_increasing; auto with ord.
  - apply addOrd_monotone; auto with ord.
    apply mulOrd_monotone2; auto with ord.
Qed.

Lemma lex2 (α β:Ord) (x:α) (y y':β) :
  y ◃ y' ->
  lex _ _ x y < lex _ _ x y'.
Proof.
  unfold lex; intros.
  apply addOrd_increasing; auto.
Qed.

(* The well-known 2-argument Ackermann-Peter function, defined over the
   binary natural number representation N. *)
Program Fixpoint Ack (m:N) (n:N) {measure (lex ωN ωN m n) ord_lt} : N :=
  match m, n with
  | N0     , _       => N.succ n
  | Npos pm, N0      => Ack (Pos.pred_N pm) 1%N
  | Npos pm, Npos pn => Ack (Pos.pred_N pm) (Ack m (Pos.pred_N pn))
  end.
Next Obligation.
  apply lex1. apply nOrd_increasing. lia.
Qed.
Next Obligation.
  apply lex2. apply nOrd_increasing. lia.
Qed.
Next Obligation.
  apply lex1. apply nOrd_increasing. lia.
Qed.
Next Obligation.
  apply (Acc_intro_generator 250).
  apply measure_wf.
  apply ord_lt_wf.
Defined.

(* CF: The OEIS sequence for the Simplified Ackermann function:
     https://oeis.org/A046859 *)
Eval vm_compute in (Ack 0 0).
Eval vm_compute in (Ack 1 1).
Eval vm_compute in (Ack 2 2).
Eval vm_compute in (Ack 3 3).
(* Ack 4 4 is much to large to attempt to compute inside the Coq kernel *)

(* Defining the Ackermann function requires recursion up to ω*ω ≈ ω², which is the
   supremum of all the ordinal measures that may appear in its definition. *)
Theorem ackermann_bound:
  supOrd (fun m => (supOrd (fun n => lex ωN ωN m n))) ≈ expOrd ω 2.
Proof.
  transitivity (ωN * ωN).
  2:{ rewrite expOrd_succ; auto with ord.
      rewrite expOrd_one'; auto with ord.
      repeat rewrite omegaN_eq.
      reflexivity. }
  split.
  - apply sup_least; intro m.
    apply sup_least; intro n.
    unfold lex.
    rewrite (mulOrd_unfold ωN ωN).
    rewrite <- (sup_le _ _ m).
    apply addOrd_monotone; auto with ord.
  - rewrite (mulOrd_unfold ωN ωN).
    apply sup_least; intro m.
    rewrite addOrd_unfold. apply lub_least.
    + rewrite <- (sup_le _ _ m).
      rewrite <- (sup_le _ _ 0%N).
      unfold lex. simpl.
      rewrite addOrd_zero_r.
      reflexivity.
    + apply sup_least; intro n.
      rewrite <- (sup_le _ _ m).
      rewrite <- (sup_le _ _ (N.succ n)).
      unfold lex. simpl.
      apply succ_least.
      apply addOrd_increasing.
      apply nOrd_increasing.
      lia.
Qed.


Lemma subterm_trans : forall {A B C:Ord} (x:A) (y:B) (z:C),
  x ◃ y -> y ◃ z -> x ◃ z.
Proof.
  simpl; intros. eapply ord_lt_trans; eauto.
Qed.

Lemma size_discriminate : forall (A:Ord) (x y:A), x ◃ y -> x <> y.
Proof.
  repeat intro; subst y.
  apply (ord_lt_irreflexive _ H).
Qed.

Lemma lub_trans1 x y z : x ≤ y -> x ≤ y ⊔ z.
Proof.
  intros.
  apply ord_le_trans with y; auto.
  apply lub_le1.
Qed.

Lemma lub_trans2 x y z : x ≤ z -> x ≤ y ⊔ z.
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply lub_le2.
Qed.

Lemma add_trans1 x y z : x ≤ y -> x ≤ y ⊕ z.
Proof.
  intros.
  apply ord_le_trans with y; auto.
  apply naddOrd_le1.
Qed.

Lemma add_trans1' x y z : x < y -> x < y ⊕ z.
Proof.
  intros.
  apply ord_lt_le_trans with y; auto.
  apply naddOrd_le1.
Qed.

Lemma add_trans2 x y z : x ≤ z -> x ≤ y ⊕ z.
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply naddOrd_le2.
Qed.

Lemma add_trans2' x y z : x < z -> x < y ⊕ z.
Proof.
  intros.
  apply ord_lt_le_trans with z; auto.
  apply naddOrd_le2.
Qed.

Global Hint Resolve
     succ_trans
     succ_trans'
     lub_trans1 lub_trans2
     add_trans1 add_trans2
     add_trans1' add_trans2' : ord.

(* Lists of ordinal-sized types have an ordinal size.
 *)
Definition listOrd {A} (f:A -> Ord) : list A -> Ord :=
  fix listOrd (l:list A) : Ord :=
    match l with
    | [] => 0
    | x::xs => succOrd (f x ⊕ listOrd xs)
    end.

Canonical Structure ListOrd (A:Ord) : Ord :=
  ord (list A) (listOrd (ordSize A)).

Lemma listAdd (A:Ord) (xs ys:list A) :
  sz (xs ++ ys) ≈ sz xs ⊕ sz ys.
Proof.
  induction xs; simpl.
  - rewrite naddOrd_comm.
    apply naddOrd_zero.
  - rewrite naddOrd_succ.
    rewrite IHxs.
    rewrite naddOrd_assoc.
    reflexivity.
Qed.


(** Basic lemmas about constructors for nat and list *)
Lemma S_lt : forall x:ω, x ◃ S x.
Proof.
  simpl; auto with ord.
Qed.

Lemma head_lt : forall (A:Ord) (h:A) (t:list A), h ◃ (h::t).
Proof.
  simpl; eauto with ord.
Qed.

Lemma tail_lt : forall (A:Ord) (h:A) (t:list A), t ◃ (h::t).
Proof.
  simpl; eauto with ord.
Qed.

Global Hint Resolve head_lt tail_lt : ord.

Lemma app_lt1 : forall (A:Ord) (xs ys:list A), ys <> [] ->  xs ◃ xs ++ ys.
Proof.
  intros. rewrite listAdd. simpl.
  rewrite naddOrd_zero at 1.
  apply naddOrd_increasing2.
  destruct ys.
  + elim H; auto.
  + simpl.
    apply succ_trans.
    apply zero_least.
Qed.

Lemma app_lt2 : forall (A:Ord) (xs ys:list A), xs <> [] -> ys ◃ xs ++ ys.
Proof.
  intros. rewrite listAdd. simpl.
  rewrite naddOrd_zero at 1.
  rewrite naddOrd_comm.
  apply naddOrd_increasing1.
  destruct xs.
  + elim H; auto.
  + simpl.
    apply succ_trans.
    apply zero_least.
Qed.

Lemma Permutation_size (A:Ord) (r s:list A) : Permutation r s -> sz r ≈ sz s.
Proof.
  intro H; induction H; simpl; eauto with ord.
  - rewrite IHPermutation; auto with ord.
  - repeat rewrite naddOrd_succ2.
    do 2 rewrite naddOrd_assoc.
    rewrite (naddOrd_comm (A y)).
    auto with ord.
Qed.

Lemma In_lt : forall (A:Ord) (x:A) l, In x l -> x ◃ l.
Proof.
  induction l; simpl; intuition; subst; eauto with ord.
Qed.
Global Hint Resolve In_lt : ord.

Lemma listOrd_bounded_aux A (f:A -> Ord) l :
  listOrd f l ≤ (ord A f) × (length l : ω).
Proof.
  induction l; simpl.
  apply zero_least.
  apply succ_least.
  rewrite (naddOrd_comm (f a)).
  apply ord_lt_le_trans with (listOrd f l ⊕ (ord A f)).
  apply naddOrd_increasing2. apply (index_lt (ord A f)).
  rewrite <- (sup_le _ _ tt).
  apply naddOrd_monotone; auto with ord.
Qed.

Lemma listOrd_bounded (A:Ord) (l:list A) :
  sz l ≤ A × ω.
Proof.
  destruct A as [A f].
  simpl. rewrite <- (sup_le _ _ (length l)).
  rewrite listOrd_bounded_aux; auto with ord.
Qed.

Lemma listOrd_bounded' (A:Ord) (l:list A) :
  sz l < (succOrd A) × ω.
Proof.
  destruct A as [A f].
  simpl. rewrite <- (sup_le _ _ (length l)).
  rewrite naddOrd_succ2.
  apply succ_trans.
  rewrite <- naddOrd_le1.
  rewrite listOrd_bounded_aux; auto with ord.
  simpl.
  apply jmulOrd_monotone1.
  auto with ord.
Qed.

(* Streams, represented as functions from natural numbers to values *)
Definition stream (A:Type) := nat -> A.

Definition streamIdx {A:Type} (n:nat) (s:stream A) : A := s n.

Definition streamCons {A:Type} (a:A) (s:stream A) : stream A :=
  fun n => match n with
           | O => a
           | S n' => streamIdx n' s
           end.

Fixpoint streamAppend {A:Type} (l:list A) (s:stream A) : stream A :=
  match l with
  | [] => s
  | (h::tl) => streamCons h (streamAppend tl s)
  end.

(* The ordinal size of a stream.  We carefully arrange it so that
   list prefixes of streams are subterms; this is the reason for
   the (succ A ⊗ ω) term.  Moreover, the leading succ ensures that
   the elements of streams are always subterms of the stream.
 *)
Definition streamOrd {A} (f:A -> Ord) (s:stream A) : Ord :=
  succOrd (supOrd (fun n => f (streamIdx n s) ⊕ (succOrd (ord A f) × ω))).
Canonical Structure StreamOrd (A:Ord) : Ord :=
  ord (stream A) (streamOrd (ordSize A)).

Lemma streamIdx_lt (A:Ord) (s:stream A) n :
  streamIdx n s ◃ s.
Proof.
  simpl. unfold streamOrd.
  eapply ord_le_lt_trans; [ | apply succ_lt ].
  rewrite <- (sup_le _ _ n). simpl.
  auto with ord.
Qed.

Lemma streamHead_lt (A:Ord) (h:A) (tl:stream A) :
  h ◃ streamCons h tl.
Proof.
  simpl. unfold streamOrd.
  eapply ord_le_lt_trans; [ | apply succ_lt ].
  rewrite <- (sup_le _ _ 0%nat). simpl.
  auto with ord.
Qed.

Lemma streamTail_le (A:Ord) (h:A) (tl:stream A) :
  tl ⊴ streamCons h tl.
Proof.
  simpl. unfold streamOrd.
  apply succ_monotone.
  apply sup_least. intro i.
  rewrite <- (sup_le _ _ (S i)).
  simpl.
  auto with ord.
Qed.

Lemma streamAppend_lt1 (A:Ord) (xs:list A) (ys:stream A) :
  xs ◃ streamAppend xs ys.
Proof.
  induction xs; intros; simpl; auto with ord.
  - unfold streamOrd.
    apply succ_trans; apply zero_least.
  - unfold streamOrd.
    apply succ_increasing.
    rewrite <- (sup_le _ _ 0%nat).
    unfold streamIdx; unfold streamCons.
    apply naddOrd_increasing2; auto with ord.
    destruct A; apply listOrd_bounded'.
Qed.

Lemma streamAppend_le2 (A:Ord) (xs:list A) (ys:stream A) :
  ys ⊴ streamAppend xs ys.
Proof.
  revert ys; induction xs; intros; simpl; auto with ord.
  etransitivity. apply IHxs.
  apply streamTail_le.
Qed.

(* Countably-wide rose trees. *)
Inductive CountableRoseTree (A:Type) :=
  | RoseNode : A -> (nat -> CountableRoseTree A) -> CountableRoseTree A.

Fixpoint countableRoseOrd (A:Type) (f:A -> Ord) (t:CountableRoseTree A) : Ord :=
  match t with
  | RoseNode _ a s => succOrd (f a ⊕ succOrd (supOrd (fun n => countableRoseOrd A f (s n))))
  end.
Canonical Structure CountableRoseOrd (A:Ord) : Ord :=
  ord (CountableRoseTree A) (countableRoseOrd _ A).

Lemma rose_elem_lt (A:Ord) (a:A) (s:nat -> CountableRoseTree A) :
  a ◃ RoseNode _ a s.
Proof.
  simpl; auto with ord.
Qed.

Lemma rose_immediate_subtree_lt (A:Ord) (a:A) (s:nat -> CountableRoseTree A) n :
  s n ◃ RoseNode _ a s.
Proof.
  simpl.
  apply succ_trans.
  rewrite <- naddOrd_le2.
  apply ord_lt_le; apply succ_trans.
  rewrite <- (sup_le _ _ n).
  auto with ord.
Qed.

Inductive is_subtree {A} (sub:CountableRoseTree A) : CountableRoseTree A  -> Prop :=
| immediate_subtree : forall a s n, streamIdx n s = sub -> is_subtree sub (RoseNode _ a s)
| distant_subtree : forall a s n, is_subtree sub (s n) -> is_subtree sub (RoseNode _ a s).

Lemma rose_subtree_lt (A:Ord) (sub t:CountableRoseTree A) : is_subtree sub t -> sub ◃ t.
Proof.
  intro H; induction H.
  - rewrite <- H. apply rose_immediate_subtree_lt.
  - rewrite IHis_subtree. apply rose_immediate_subtree_lt.
Qed.

Lemma rose_acyclic (A:Ord) (sub t:CountableRoseTree A) (H:is_subtree sub t) : sub <> t.
Proof.
  apply size_discriminate.
  apply rose_subtree_lt; auto.
Qed.


(** Let's play around with some Ltac support.

    This Ltac code is currently super first-pass, and could probably
    be improved a lot.
  *)
Ltac try_ord := try (solve [ simpl; auto 40 with ord | simpl; eauto with ord ]).

Ltac subterm_trans x :=
  apply subterm_trans with x; try_ord.

Ltac esubterm_trans :=
  eapply subterm_trans; try_ord.

Ltac ord_crush :=
  intros; apply size_discriminate;
  try_ord;
  repeat (progress esubterm_trans).

(** Some simple examples based on nats and lists *)

Goal forall x:nat, x <> S (S (S (S x))).
Proof.
  ord_crush.
Qed.

Goal forall (a b c:nat) x, x <> a::b::c::x.
Proof.
  ord_crush.
Qed.


(** An example based on even/odd numbers *)

Inductive even :=
| even0 : even
| evenS : odd -> even
with odd :=
| oddS : even -> odd.

(* Some fairly boilerplate code defining the ordinal size function,
   and registering associated canconical structures.
 *)
Fixpoint even_size (x:even) : Ord :=
  match x with
  | even0 => zeroOrd
  | evenS y => succOrd (odd_size y)
  end
with
odd_size (x:odd) : Ord :=
  match x with
  | oddS y => succOrd (even_size y)
  end.

Canonical Structure evenOrdSize :=
  ord even even_size.
Canonical Structure oddOrdSize :=
  ord odd odd_size.

(* Now we can crush that proof *)
Lemma even_odd_neq : forall x, x <> oddS (evenS (oddS (evenS x))).
Proof.
  ord_crush.
Qed.

(** A more complicated example using mutual recursion,
    nested lists and dependent types.
 *)
Inductive asdf : nat -> Set :=
| mkAsdf : forall n, list (qwerty n) -> asdf n
with
qwerty : nat -> Set :=
| emptyQwerty : qwerty 0
| someQwerty  : forall n, qwerty n -> (forall m, asdf m) -> qwerty (S n).

Fixpoint asdf_size n (x:asdf n) : Ord :=
  match x with
  | mkAsdf n xs => succOrd (listOrd (qwerty_size n) xs)
  end
with qwerty_size n (x:qwerty n) : Ord :=
  match x with
  | emptyQwerty => zeroOrd
  | someQwerty n x y => succOrd (qwerty_size n x ⊕ depOrd asdf_size y)
  end.

Canonical Structure AsdfOrdSize n :=
  ord (asdf n) (asdf_size n).
Canonical Structure QwertyOrdSize n :=
  ord (qwerty n) (qwerty_size n).

Goal forall n a b c f,
  f (S n) <> mkAsdf _ [a; b; someQwerty _ c f].
Proof.
  intros; apply size_discriminate.
  eapply subterm_trans. auto with ord.
  simpl.
  unfold depOrd.
  apply succ_trans.
  apply succ_trans'.
  apply add_trans2.
  apply succ_trans'.
  apply add_trans2.
  apply succ_trans'.
  apply add_trans1.
  apply succ_trans'.
  apply add_trans2.
  auto with ord.
Qed.
