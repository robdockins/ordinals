Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Unset Printing Records.

(** Constructive type-theoretic ordinals.

In this development, I attempt to reconstruct enough of classical
ordinal theory to both be useful.

My first (and primary) goal was for these ordinals to represent a
practical proof techinque for, e.g., constructing termination measures
of recursive programs and building acyclicity proofs invovling
complicated data structures.

My secondary goal was to climb the first part of the way into
"Cantor's attic" by constructing the Veblen hierarchy, the
Feferman-Shütte ordinal Γ₀, and perhaps up to the small Veblen ordinal
(SVO), which is formed as the limit of the extended Veblen functions
on finitely-many variables.

Regarding the first goal, I believe this effort has been quite
successful. Some examples of using ordinals for these purposes
is given a the end of this file.

On the second goal, the result is a bit more mixed.  Development
proceeds smoothly up through computing the ε numbers with no problems.
The definition of the Vebeln functions and many of their properties
likewise goes through without much trouble.  However, it has remained
stubbornly difficult to find a proof that the Veblen functions are
inflationary in their first argument, a property necessary to
show that they have fixpoints.  More details follow.
*)


Declare Scope ord_scope.
Delimit Scope ord_scope with ord.
Open Scope ord_scope.

(** * Ordinals, represented as Type-indexed trees of potentially
      infinite width, but finite depth.

   Note we do not restrict ourselves here to countably-wide trees,
   which (I believe) would give us the countable ordinals instead.
   This might make some of the development more managable, but make
   them less convenient.

   The current definition allows us to view ordinals both as objects
   of their own interest, but also as a collection of canonical
   structures that assign a distingushed way to measure the size of
   values.  *)
Inductive Ord : Type :=
  ord { ordCarrier :> Type
      ; ordSize :> ordCarrier -> Ord
      }.

Definition sz {A:Ord} (x:A) : Ord := ordSize A x.
Coercion sz : ordCarrier >-> Ord.
Add Printing Coercion sz.


(** We define < and ≤ essentially by mutual
    recursion on the structure of ordinals. The ordering
    relation has an elegant game semantics flavor, defined
    by the quantifier nesting structure.
  *)
Fixpoint ord_lt (x y:Ord) {struct x}: Prop :=
  match x, y with
  | ord A f, ord B g =>
    exists b:B, forall a:A, ord_lt (f a) (g b)
  end.

Definition ord_le (x y:Ord) : Prop :=
  match x with
  | ord A f => forall a:A, ord_lt (f a) y
  end.

Definition ord_eq (x y:Ord) : Prop :=
  ord_le x y /\ ord_le y x.

Notation "x > y" := (ord_lt y x) : ord_scope.
Notation "x < y" := (ord_lt x y) : ord_scope.
Notation "x >= y" := (ord_le y x) : ord_scope.
Notation "x <= y" := (ord_le x y) : ord_scope.
Notation "x ≥ y" := (ord_le y x) (at level 70, no associativity) : ord_scope.
Notation "x ≤ y" := (ord_le x y) (at level 70, no associativity) : ord_scope.
Notation "x ≈ y" := (ord_eq x y) (at level 70, no associativity) : ord_scope.

(*  The notation "x ◃ y" indicates that "x" has a strictly smaller ordinal measure
    than "y".  Note that "x" and "y" do not need to have the same type.

    Likewise "x ⊴ y" indicates that "x" has an ordinal measure no larger than "y".
 *)
Notation "x ◃ y" := (sz x < sz y)%ord (at level 80, no associativity).
Notation "x ⊴ y" := (sz x ≤ sz y)%ord (at level 80, no associativity).

(** Characteristic equation for less-than *)
Lemma ord_lt_unfold x y :
  x < y = exists b:y, x ≤ y b.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

(** Characteristic equation for less-equal *)
Lemma ord_le_unfold x y :
  x ≤ y = forall a:x, x a < y.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

Global Opaque ord_le ord_lt.

(** Another way to unfold the definition of <= *)
Lemma ord_le_subord x y :
  x <= y ->
  forall i, exists j, x i <= y j.
Proof.
  intros.
  rewrite ord_le_unfold in H.
  specialize (H i).
  rewrite ord_lt_unfold in H.
  auto.
Qed.

(** Less-than implies less-equal
  *)
Lemma ord_lt_le : forall b a,
  a < b -> a ≤ b.
Proof.
  induction b as [B g]. intros.
  rewrite ord_lt_unfold in H0. simpl in *.
  destruct H0 as [b ?].
  destruct a as [A f].
  rewrite ord_le_unfold in *.
  intros.
  specialize (H0 a).
  rewrite ord_lt_unfold.
  exists b. apply H. auto.
Qed.

(** Less-equal is a reflexive relation
  *)
Lemma ord_le_refl x : x ≤ x.
Proof.
  induction x as [A f].
  rewrite ord_le_unfold.
  intros.
  rewrite ord_lt_unfold.
  exists a. apply H.
Qed.


Lemma index_lt : forall (a:Ord) (i:a), a i < a.
Proof.
  intros.
  rewrite ord_lt_unfold.
  exists i. apply ord_le_refl.
Qed.

Lemma index_le : forall (a:Ord) (i:a), a i ≤ a.
Proof.
  intros.
  apply ord_lt_le.
  apply index_lt.
Qed.

Global Hint Resolve ord_lt_le ord_le_refl index_lt index_le : ord.

(** These various transitivity-releated facts need to
    be proved simultaneuously.
  *)
Lemma ord_trans :
  forall b a c,
    (a ≤ b -> b ≤ c -> a ≤ c) /\
    (a ≤ b -> b < c -> a < c) /\
    (a < b -> b ≤ c -> a < c).
Proof.
  induction b as [B g].
  intros.
  repeat split; intros.
  - rewrite ord_le_unfold.
    rewrite ord_le_unfold in H0.
    intro ai.
    specialize (H0 ai).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [bi ?].
    rewrite ord_le_unfold in H1.
    specialize (H1 bi).
    specialize (H bi (a ai) c); intuition.
  - rewrite ord_lt_unfold.
    rewrite ord_lt_unfold in H1.
    destruct H1 as [ci ?].
    exists ci.
    rewrite ord_le_unfold in H1.
    rewrite ord_le_unfold.
    rewrite ord_le_unfold in H0.
    intros ai.
    specialize (H0 ai).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [bi ?].
    specialize (H1 bi).
    specialize (H bi (a ai) (c ci)); intuition.
  - rewrite ord_lt_unfold in H0.
    destruct H0 as [bi ?].
    rewrite ord_le_unfold in H1.
    specialize (H1 bi).
    destruct (H bi a c); intuition.
Qed.

(** Less-equal is transitive.
  *)
Lemma ord_le_trans a b c :
    a ≤ b -> b ≤ c -> a ≤ c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** Less-than is transitive *)
Lemma ord_lt_trans a b c :
    a < b -> b < c -> a < c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** Less-equal preserves less-than *)
Lemma ord_lt_le_trans a b c :
  a < b -> b ≤ c -> a < c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

Lemma ord_le_lt_trans a b c :
  a ≤ b -> b < c -> a < c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

Lemma ord_le_intro x y :
  (forall a, a < x -> a < y) -> x <= y.
Proof.
  intros.
  rewrite ord_le_unfold; intro a.
  apply H; auto with ord.
Qed.

Lemma ord_le_elim x y :
  x <= y ->
  (forall a, a < x -> a < y).
Proof.
  intros.
  apply ord_lt_le_trans with x; auto.
Qed.

(** The less-than ordering on ordinals is well-founded.
  *)
Lemma ord_lt_acc : forall x y,  y ≤ x -> Acc ord_lt y.
Proof.
  induction x as [A f]; intros z Hz.
  constructor. intros y Hy.
  assert (Hyx : (ord_lt y (ord A f))).
  { apply ord_lt_le_trans with z; auto. }

  rewrite ord_lt_unfold in Hyx.
  destruct Hyx as [b ?].
  apply (H b).
  auto.
Defined.

Theorem ord_lt_wf : well_founded ord_lt.
Proof.
  red; intros.
  apply ord_lt_acc with a.
  apply ord_le_refl.
Defined.

(* The workhorse for proving properties about ordinals. *)
Definition ordinal_induction
  : forall P : Ord -> Set,
     (forall x : Ord, (forall y : Ord, y < x -> P y) -> P x) ->
     (forall a : Ord, P a)
  := well_founded_induction ord_lt_wf.

(** The less-than order is irreflexive, a simple corollary of well-foundedness. *)
Corollary ord_lt_irreflexive : forall x, x < x -> False.
Proof.
  induction x using ordinal_induction.
  firstorder.
Qed.

(** * Ordinal equality is an equality relation *)

Lemma ord_eq_refl : forall x, x ≈ x.
Proof.
  intros; split; apply ord_le_refl.
Qed.

Lemma ord_eq_trans : forall x y z, x ≈ y -> y ≈ z -> x ≈ z.
Proof.
  unfold ord_eq; intuition; eapply ord_le_trans; eauto.
Qed.

Lemma ord_eq_sym : forall x y, x ≈ y -> y ≈ x.
Proof.
  unfold ord_eq; intuition.
Qed.


Add Parametric Relation : Ord ord_le
    reflexivity proved by ord_le_refl
    transitivity proved by ord_le_trans
    as ord_le_rel.

Add Parametric Relation : Ord ord_lt
    transitivity proved by ord_lt_trans
    as ord_lt_rel.

Add Parametric Relation : Ord ord_eq
    reflexivity proved by ord_eq_refl
    symmetry proved by ord_eq_sym
    transitivity proved by ord_eq_trans
    as ord_eq_rel.

Instance ord_lt_le_subreleation : subrelation ord_lt ord_le.
Proof.
  red. intros; apply ord_lt_le; auto.
Qed.

Instance ord_eq_le_subrelation : subrelation ord_eq ord_le.
Proof.
  red. unfold ord_eq. intuition.
Qed.

Instance ord_eq_flip_le_subrelation : subrelation ord_eq (flip ord_le).
Proof.
  red. unfold ord_eq. intuition.
Qed.

Add Parametric Morphism : ord_lt with signature
    ord_le --> ord_le ++> impl as ord_lt_mor.
Proof.
  repeat intro.
  apply ord_le_lt_trans with x; auto.
  apply ord_lt_le_trans with x0; auto.
Qed.

Add Parametric Morphism : ord_lt with signature
    ord_le ++> ord_le --> flip impl as ord_lt_mor'.
Proof.
  repeat intro.
  apply ord_le_lt_trans with y; auto.
  apply ord_lt_le_trans with y0; auto.
Qed.

Lemma increasing_inflationary f :
  (forall x y, x < y -> f x < f y) ->
  forall a, a ≤ f a.
Proof.
  intro Hinc.
  induction a using ordinal_induction.
  apply ord_le_intro.
  intros z Hz.
  rewrite (H z); auto.
Qed.

(** * Definitions of zero, limit, and successor ordinals.

    In a classical setting, we would show that all ordinals
    fall into one of these three classes. Without the excluded
    middle, we cannot prove this.  However, we can show that these
    classes are mutually exclusive and demonstrate some properties
    that they have.
 *)

Definition hasMaxElement A (f:A -> Ord) :=
  exists a, forall a', f a ≥ f a'.

Definition ascendingSet A (f:A -> Ord) :=
  forall a, exists a', f a < f a'.

Definition zeroOrdinal (x:Ord) : Prop :=
  match x with
  | ord A f => A -> False
  end.

Definition successorOrdinal (x:Ord) : Prop :=
  match x with
  | ord A f => hasMaxElement A f
  end.

Definition limitOrdinal (x:Ord) : Prop :=
  match x with
  | ord A f => inhabited A /\ ascendingSet A f
  end.

Lemma hasMax_ascending_contradiction A f : hasMaxElement A f -> ascendingSet A f -> False.
Proof.
  intros.
  destruct H as [a Ha].
  destruct (H0 a) as [a' Ha'].
  apply ord_lt_irreflexive with (f a').
  apply ord_le_lt_trans with (f a); auto.
Qed.

(** An ordinal cannot be both zero and a successor *)
Lemma zero_not_successor : forall x, zeroOrdinal x -> successorOrdinal x -> False.
Proof.
  intros [A f]; simpl; intros Hz Hsucc.
  destruct Hsucc as [a Ha]; auto.
Qed.

(** An ordinal cannot be both zero and a limit *)
Lemma zero_not_limit : forall x, zeroOrdinal x -> limitOrdinal x -> False.
Proof.
  intros [A f]; simpl; intros Hz [Hnz _].
  destruct Hnz as [a]; auto.
Qed.

(** An ordinal cannot be both a successor and a limit *)
Lemma successor_not_limit : forall x, successorOrdinal x -> limitOrdinal x -> False.
Proof.
  intros [A f]; simpl; intros Hsucc [_ Hlim].
  apply (hasMax_ascending_contradiction A f); auto.
Qed.

