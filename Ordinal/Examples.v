Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Require Import List.
Require Import Relations.
Require Import Wf.
Require Import Wellfounded.Transitive_Closure.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.

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

Definition lex {α β:Ord} (x:α) (y:β) :=
  β ⊗ sz x ⊕ sz y.

Lemma lex1 (α β:Ord) (x x':α) (y y':β) :
  x ◃ x' ->
  lex x y < lex x' y'.
Proof.
  unfold lex; intros.
  apply ord_lt_le_trans with (β ⊗ succOrd x ⊕ y').
  - rewrite <- (addOrd_le1 _ (sz y')).
    rewrite mulOrd_succ.
    apply addOrd_monotone_lt2; auto with ord.
  - apply addOrd_monotone_le; auto with ord.
    apply mulOrd_monotone_le2.
    apply succ_least. auto.
Qed.

Lemma lex2 (α β:Ord) (x x':α) (y y':β) :
  x ⊴ x' ->
  y ◃ y' ->
  lex x y < lex x' y'.
Proof.
  unfold lex; intros.
  rewrite H.
  apply addOrd_monotone_lt2; auto.
Qed.

(** * Well-founded relations generate ordinals *)

Section wf_ord.
  Variable A:Type.
  Variable R:A -> A -> Prop.
  Hypothesis Hwf : well_founded R.

  Fixpoint mk_wf_ord (a:A) (X:Acc R a) : Ord :=
    match X with
    | Acc_intro _ H => ord { a':A | R a' a } (fun x => mk_wf_ord (proj1_sig x) (H _ (proj2_sig x)))
    end.
  Definition wf_ord (a:A) : Ord := mk_wf_ord a (Hwf a).

  Lemma wf_ord_lt : forall a a', R a' a -> wf_ord a' < wf_ord a.
  Proof.
    unfold wf_ord. intros a a'.
    generalize (Hwf a'). revert a'.
    generalize (Hwf a).
    induction a using (well_founded_induction Hwf); intros.
    destruct a0; simpl.
    rewrite ord_lt_unfold.
    exists (exist _ a' H0); simpl.
    rewrite ord_le_unfold.
    destruct a1. simpl; intros.
    destruct a2. simpl.
    apply H; auto.
  Qed.

  Lemma wf_ord_lt_trans : forall a a', clos_trans _ R a' a -> wf_ord a' < wf_ord a.
  Proof.
    intros; induction H.
    - apply wf_ord_lt; auto.
    - eapply ord_lt_trans; eauto.
  Qed.

  Lemma wf_ord_le_trans : forall a a', clos_refl_trans _ R a' a -> wf_ord a' ≤ wf_ord a.
  Proof.
    intros; induction H.
    - apply ord_lt_le; apply wf_ord_lt; auto.
    - apply ord_le_refl.
    - eapply ord_le_trans; eauto.
  Qed.

End wf_ord.


Definition ord_measure (o:Ord) := Acc ord_lt o.

Definition Ack_measure (m:nat) (n:nat) := ord_measure (@lex ω ω m n).

Program Fixpoint Ackdef (m:nat) (n:nat) {HM : Ack_measure m n} {struct HM}: nat :=
  match m, n with
  | O   , _    => n+1
  | S m', O    => Ackdef m' 1%nat
  | S m', S n' => Ackdef m' (Ackdef m n')
  end.
Next Obligation.
  destruct HM as [HM]; apply HM; simpl.
  apply lex1.
  apply succ_lt.
Defined.
Next Obligation.
  destruct HM as [HM]; apply HM; simpl.
  apply lex2.
  apply ord_le_refl.
  apply succ_lt.
Defined.
Next Obligation.
  - destruct HM as [HM]; apply HM; simpl.
    apply lex1. apply succ_lt.
  - destruct HM as [HM]; apply HM; simpl.
    apply lex1. apply succ_lt.
Defined.

Definition Ack m n := @Ackdef m n (ord_lt_wf _).

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

Lemma succ_trans x y : x ≤ y -> x < succOrd y.
Proof.
  intros.
  rewrite ord_lt_unfold.
  simpl. exists tt. auto.
Qed.

Lemma succ_trans' x y : x ≤ y -> x ≤ succOrd y.
Proof.
  intros.
  apply ord_lt_le.
  apply succ_trans; auto.
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
  apply addOrd_le1.
Qed.

Lemma add_trans1' x y z : x < y -> x < y ⊕ z.
Proof.
  intros.
  apply ord_lt_le_trans with y; auto.
  apply addOrd_le1.
Qed.

Lemma add_trans2 x y z : x ≤ z -> x ≤ y ⊕ z.
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply addOrd_le2.
Qed.

Lemma add_trans2' x y z : x < z -> x < y ⊕ z.
Proof.
  intros.
  apply ord_lt_le_trans with z; auto.
  apply addOrd_le2.
Qed.

Global Hint Unfold ordSize : ord.
Global Hint Resolve
     limit_lt lub_le1 lub_le2
     ord_lt_trans ord_le_trans ord_eq_trans
     succ_trans
     succ_trans'
     lub_trans1 lub_trans2
     add_trans1 add_trans2
     add_trans1' add_trans2'
     ord_lt_le ord_le_refl ord_eq_refl : ord.


(* Lists of ordinal-sized types have an ordinal size.
 *)
Definition listOrd {A} (f:A -> Ord) : list A -> Ord :=
  fix listOrd (l:list A) : Ord :=
    match l with
    | [] => zeroOrd
    | x::xs => succOrd (addOrd (f x) (listOrd xs))
    end.

Canonical Structure ListOrd (A:Ord) : Ord :=
  ord (list A) (listOrd (ordSize A)).

Lemma listAdd (A:Ord) (xs ys:list A) :
  sz (xs ++ ys) ≈ sz xs ⊕ sz ys.
Proof.
  induction xs; simpl.
  - rewrite addOrd_comm.
    apply addOrd_zero.
  - rewrite addOrd_succ.
    rewrite IHxs.
    rewrite addOrd_assoc.
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
  rewrite addOrd_zero at 1.
  apply addOrd_monotone_lt2.
  destruct ys.
  + elim H; auto.
  + simpl.
    apply succ_trans.
    apply zero_least.
Qed.

Lemma app_lt2 : forall (A:Ord) (xs ys:list A), xs <> [] -> ys ◃ xs ++ ys.
Proof.
  intros. rewrite listAdd. simpl.
  rewrite addOrd_zero at 1.
  rewrite addOrd_comm.
  apply addOrd_monotone_lt1.
  destruct xs.
  + elim H; auto.
  + simpl.
    apply succ_trans.
    apply zero_least.
Qed.

Require Import Permutation.

Lemma Permutation_size (A:Ord) (r s:list A) : Permutation r s -> sz r ≈ sz s.
Proof.
  intro H; induction H; simpl; eauto with ord.
  - rewrite IHPermutation; auto with ord.
  - repeat rewrite addOrd_succ2.
    do 2 rewrite addOrd_assoc.
    rewrite (addOrd_comm (A y)).
    auto with ord.
Qed.

Lemma In_lt : forall (A:Ord) (x:A) l, In x l -> x ◃ l.
Proof.
  induction l; simpl; intuition; subst; eauto with ord.
Qed.
Global Hint Resolve In_lt : ord.

Lemma listOrd_bounded_aux A (f:A -> Ord) l :
  listOrd f l ≤ (ord A f) ⊗ (length l : ω).
Proof.
  induction l; simpl.
  apply zero_least.
  apply succ_least.
  rewrite (addOrd_comm (f a)).
  apply ord_lt_le_trans with (listOrd f l ⊕ (ord A f)).
  apply addOrd_monotone_lt2. apply (index_lt (ord A f)).
  rewrite <- (sup_le _ _ tt).
  apply addOrd_monotone_le; auto with ord.
Qed.

Lemma listOrd_bounded (A:Ord) (l:list A) :
  sz l ≤ A ⊗ ω.
Proof.
  destruct A as [A f].
  simpl. rewrite <- (sup_le _ _ (length l)).
  rewrite listOrd_bounded_aux; auto with ord.
Qed.

Lemma listOrd_bounded' (A:Ord) (l:list A) :
  sz l < (succOrd A) ⊗ ω.
Proof.
  destruct A as [A f].
  simpl. rewrite <- (sup_le _ _ (length l)).
  rewrite addOrd_succ2.
  apply succ_trans.
  rewrite <- addOrd_le1.
  rewrite listOrd_bounded_aux; auto with ord.
  simpl.
  apply mulOrd_monotone_le1.
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
  succOrd (supOrd (fun n => f (streamIdx n s) ⊕ (succOrd (ord A f) ⊗ ω))).
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
  apply succ_monotone_le.
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
    apply succ_monotone_lt.
    rewrite <- (sup_le _ _ 0%nat).
    unfold streamIdx; unfold streamCons.
    apply addOrd_monotone_lt2; auto with ord.
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
  rewrite <- addOrd_le2.
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
Ltac try_ord := try solve [ auto with ord | simpl; auto 100 with ord | simpl; eauto with ord ].

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
  | someQwerty n x y => succOrd (addOrd (qwerty_size n x) (depOrd asdf_size y))
  end.

Canonical Structure AsdfOrdSize n :=
  ord (asdf n) (asdf_size n).
Canonical Structure QwertyOrdSize n :=
  ord (qwerty n) (qwerty_size n).

Goal forall n a b c f,
  f (S n) <> mkAsdf _ [a; b; someQwerty _ c f].
Proof.
  ord_crush.
Qed.
