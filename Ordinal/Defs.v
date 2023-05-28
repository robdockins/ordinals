Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Wf.

Unset Printing Records.

(** Constructive type-theoretic ordinals.

In this development, I attempt to reconstruct enough of classical
ordinal theory to both be useful.

When I first set out to build this formalization of ordinals, my first
(and primary) goal was for these ordinals to represent a practical
proof techinque for, e.g., constructing termination measures of
recursive programs and building acyclicity proofs invovling
complicated data structures. I belive this goal is well met (although
it could certainly benefit from additional proof automation).

My secondary goal (which expanded to consume most of the effort, in
the end) was to climb the first part of the way into "Cantor's attic"
by constructing the Veblen hierarchy, the Feferman-Schütte ordinal Γ₀,
and perhaps up to the small Veblen ordinal (SVO), which is formed as
the limit of the extended Veblen functions on finitely-many
variables. This goal has been met, and exceeded. In this development
we have surpassed the SVO, continuing on to the to the Large Veblen
Ordinal (LVO) and beyond to the Bachmann-Howard ordinal (BH).

Moreover, we have constructed a series of ordinal notation systems,
each of increasing power, up to: ε₀, Γ₀, SVO, LVO and BH. These
notation systems, unlike their semantic counterparts, enjoy decidable
ordering and constructive decomposition into Cantor normal forms.

In contrast to the usual methods of the Schütte school, we do not need
to give a separate, syntactic well-foundedness proof for our notation
systems to put them on constructive footings. Instead, the semantic
ordinal foundations given here are already constructive, so we can
instead rely directly on the dentation of the notation systems for
this proof.

Throughout this development, I have insisted on the principle that all
definitions must be constructive. Definitions are always directly
given, usually as recursive functions; no non-constructive proof
principles are used to exhibit any mathematical object.

I have also attempted to keep proofs as constructive as possible,
using the excluded middle only where it is actually necessary (in a
sense we can make formal); or, in a few additional cases where I have
not (yet?) found a constructive proof. In all cases, uses of the
excluded middle appear a an explicit hypothesis to theorems instead of
being asserted as an unconditional axiom. In once instance, (proofs
regarding the ordinal infimum operator) a choice axiom seems to be
required; it is likewise added as an explicit hypothesis.

As a result, every lemma and theorem in this developement should report
"Closed Under the Global Context" when queried via the "Print
Assumptions" command at top-level (i.e., not inside a section).

*)

Declare Scope ord_scope.
Delimit Scope ord_scope with ord.
Open Scope ord_scope.

(** * Ordinals, represented as Type-indexed trees of potentially
infinite width, but finite depth.

This definition allows us to view ordinals both as objects of their
own interest, but also as a collection of canonical structures that
assign a distingushed way to measure the size of values.

Note carefully that this inductive definition abstracts over
@Type@. According to the rules of CiC, this means the inductive
definition of @Ord@ must live in a strictly larger universe than any
of the types it abstracts over. This basically corresponds to the
usual idea in set-theoretic foundations that the proper class of
ordinals is "too large" to be a set. In particular, the type @Ord@
itself can never appear as the carrier set of an ordinal definition,
or Coq will complain of a universe inconsistency.

The @:>@ annotations in this definition set up @ordCarrier@ and
@ordSize@ as implicit coercions. When @x@ is an ordinal, this
gives us the ability to write @i:x@ to indicate that @i@ is
of type @ordCarrier x@, and also to write @x i@ to
mean @ordSize x i@.
*)

Inductive Ord : Type :=
  ord { ordCarrier :> Type
      ; ordSize :> ordCarrier -> Ord
      }.

Definition sz {A:Ord} (x:A) : Ord := ordSize A x.
Coercion sz : ordCarrier >-> Ord.
Add Printing Coercion sz.


(** We define < and ≤ essentially by mutual recursion on the structure
of ordinals.

The recursive quantifier nesting strucutre of this definition can be
thought of as defining a game for two players. Each ordinal represents
a set of choices avaliable to a player.

Think of the proposition @x < y@ as a game state where it is our turn
and we must make a choice in the ordinal @y@. Suppose @j:y@ represents
the choice we make on our turn; then the game transisitions to @x ≤ y
j@. In this state, it is our opponent's turn and they must make a
choice in @x@. After our opponent chooses some @i:x@, play transitions
to @x i < y j@, where we must again make a choice. The game ends when
one player has no choices remaining; the inductiveness of ordinals
ensures this will happen after a finite number of moves. Finally, the
propsitions @x < y@ or @x ≤ y@ are true just when the games so
described have a winning strategy, and a (constructive) proof of these
propositions exhibits such a strategy.

We consider two ordinals to be equal, written @x ≈ y@, just when
@x ≤ y@ and @y ≤ x@. As we shall see later, this corresponds to the
idea that @x@ and @y@ have winning strategies in exactly the same
situations. Formally @x ≈ y@ just when @forall a, a < x <-> a < y@.
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
  intros H i.
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
  induction b as [B g Hind]. intros a Ha.
  rewrite ord_lt_unfold in Ha.
  destruct Ha as [b Hb].
  destruct a as [A f].
  rewrite ord_le_unfold in *.
  intro a.
  specialize (Hb a).
  rewrite ord_lt_unfold.
  exists b. apply Hind. auto.
Qed.

(** Less-equal is a reflexive relation
  *)
Lemma ord_le_refl x : x ≤ x.
Proof.
  induction x as [A f Hind].
  rewrite ord_le_unfold.
  intros a.
  rewrite ord_lt_unfold.
  exists a.
  apply Hind.
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


(** @≤@ is transitive. *)
Lemma ord_le_trans a b c :
  a ≤ b -> b ≤ c -> a ≤ c.
Proof.
  revert b c.
  induction a as [A f Hind].
  intros b c Hab Hbc.
  rewrite ord_le_unfold; intro ai.
  rewrite ord_le_unfold in Hab. specialize (Hab ai).
  rewrite ord_lt_unfold in Hab. destruct Hab as [bi Hab].
  rewrite ord_le_unfold in Hbc. specialize (Hbc bi).
  rewrite ord_lt_unfold in Hbc. destruct Hbc as [ci Hbc].
  rewrite ord_lt_unfold. exists ci.
  apply (Hind ai (b bi) (c ci)); auto.
Qed.

(** @≤@ preserves @<@ on the left *)
Lemma ord_le_lt_trans a b c :
  a ≤ b -> b < c -> a < c.
Proof.
  intros Hab Hbc.
  rewrite ord_lt_unfold in Hbc.
  destruct Hbc as [ci Hbc].
  rewrite ord_lt_unfold. exists ci.
  apply (ord_le_trans a b (c ci)); auto.
Qed.  

(** @≤@ preserves @<@ on the right *)
Lemma ord_lt_le_trans a b c :
  a < b -> b ≤ c -> a < c.
Proof.
  intros Hab Hbc.
  rewrite ord_lt_unfold in Hab.
  destruct Hab as [bi ab].
  rewrite ord_le_unfold in Hbc.
  specialize (Hbc bi).
  apply (ord_le_lt_trans a bi c); auto.
Qed.

(** @<@ is transitive *)
Lemma ord_lt_trans a b c :
    a < b -> b < c -> a < c.
Proof.
  intros. eapply ord_lt_le_trans; eauto with ord.
Qed.

(** Some alternate characterizations of order and equality based only
    on @<@. These forms make the connection to the von Neumann ordinals
    more clear. Here, if we read @<@ as the set membership operator @∈@,
    then @≤@ is corresponds to the usual definition of subset, and @≈@
    corresponds to the usual definition of set equality.
*)
Lemma ord_le_intro x y :
  (forall a, a < x -> a < y) -> x ≤ y.
Proof.
  intros.
  rewrite ord_le_unfold; intro a.
  apply H; auto with ord.
Qed.

Lemma ord_le_elim x y :
  x ≤ y -> (forall a, a < x -> a < y).
Proof.
  intros.
  apply ord_lt_le_trans with x; auto.
Qed.

Lemma ord_le_equiv x y:
  x ≤ y <-> (forall a, a < x -> a < y).
Proof.
  split.
  apply ord_le_elim.
  apply ord_le_intro.
Qed.

Lemma ord_eq_intro x y :
  (forall a, a < x <-> a < y) -> x ≈ y.
Proof.
  intros.
  split; apply ord_le_intro; intuition.
  apply H; auto.
  apply H; auto.
Qed.

Lemma ord_eq_elim x y:
  x ≈ y -> (forall a, a < x <-> a < y).
Proof.
  intros [??] a; split; apply ord_le_elim; auto.
Qed.

Lemma ord_eq_equiv x y:
  x ≈ y <-> (forall a, a < x <-> a < y).  
Proof.
  split.
  apply ord_eq_elim.
  apply ord_eq_intro.
Qed.

(** The less-than ordering on ordinals is well-founded.
  *)
Lemma ord_lt_acc : forall x y, y ≤ x -> Acc ord_lt y.
Proof.
  induction x as [A f Hind]; intros z Hz.
  constructor. intros y Hy.
  assert (Hyx : y < ord A f).
  { apply ord_lt_le_trans with z; auto. }

  rewrite ord_lt_unfold in Hyx.
  destruct Hyx as [b ?].
  apply (Hind b).
  auto.
Defined.

Theorem ord_lt_wf : well_founded ord_lt.
Proof.
  intro a.
  apply ord_lt_acc with a.
  apply ord_le_refl.
Defined.

(* The workhorse for proving properties about ordinals. *)
Definition ordinal_induction
  : forall P : Ord -> Set,
     (forall x : Ord, (forall y : Ord, y < x -> P y) -> P x) ->
     (forall a : Ord, P a)
  := well_founded_induction ord_lt_wf.

(* An induction principle for the elements of an ordinal. *)
Definition size_induction (A:Ord) :
  forall P:A -> Set,
    (forall x:A, (forall y, y ◃ x -> P y) -> P x) ->
    (forall x:A, P x)
 := well_founded_induction (measure_wf ord_lt_wf sz).

(** The less-than order is irreflexive, a simple corollary of well-foundedness. *)
Corollary ord_lt_irreflexive : forall x, x < x -> False.
Proof.
  induction x as [x Hind] using ordinal_induction.
  intro H.
  exact (Hind x H H).
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

(** Every increasing function is inflationary. *)
Lemma increasing_inflationary f :
  (forall x y, x < y -> f x < f y) ->
  forall a, a ≤ f a.
Proof.
  intro Hinc.
  induction a as [a Hind] using ordinal_induction.
  apply ord_le_intro; intros z Hz.
  apply ord_le_lt_trans with (f z); auto.
Qed.

(** * Set up @<@, @≤@ and @≈@ as relations for rewriting. *)

Global Add Parametric Relation : Ord ord_le
    reflexivity proved by ord_le_refl
    transitivity proved by ord_le_trans
    as ord_le_rel.

Global Add Parametric Relation : Ord ord_lt
    transitivity proved by ord_lt_trans
    as ord_lt_rel.

Global Add Parametric Relation : Ord ord_eq
    reflexivity proved by ord_eq_refl
    symmetry proved by ord_eq_sym
    transitivity proved by ord_eq_trans
    as ord_eq_rel.

Global Instance ord_lt_le_subreleation : subrelation ord_lt ord_le.
Proof.
  red. intros; apply ord_lt_le; auto.
Qed.

Global Instance ord_eq_le_subrelation : subrelation ord_eq ord_le.
Proof.
  red. unfold ord_eq. intuition.
Qed.

Global Instance ord_eq_flip_le_subrelation : subrelation ord_eq (flip ord_le).
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

(** * Definitions of zero, limit, and successor ordinals.

    In a classical setting, we would show that all ordinals
    fall into one of these three classes. Without the excluded
    middle, we cannot prove this. However, we can show that these
    classes are mutually exclusive and demonstrate some properties
    that they have.
 *)

Definition hasMaxElement A (f:A -> Ord) :=
  exists a, forall a', f a ≥ f a'.

Definition ascendingSet A (f:A -> Ord) :=
  forall a, exists a', f a < f a'.

Definition zeroOrdinal (x:Ord) : Prop :=
  match x with
  | ord A f => ~inhabited A
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
  intros Hmax Hasc.
  destruct Hmax as [a Ha].
  destruct (Hasc a) as [a' Ha'].
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
  intros [A f]; simpl; intros Hz [Hnz _]; auto.
Qed.

(** An ordinal cannot be both a successor and a limit *)
Lemma successor_not_limit : forall x, successorOrdinal x -> limitOrdinal x -> False.
Proof.
  intros [A f]; simpl; intros Hsucc [_ Hlim].
  apply (hasMax_ascending_contradiction A f); auto.
Qed.


(** * Some auxiliary definitions that will be useful later. *)
Require Import List.
Import ListNotations.

Fixpoint each {A:Type} (P:A -> Prop) (xs:list A) : Prop :=
  match xs with
  | [] => True
  | (x::xs) => P x /\ each P xs
  end.

Lemma each_implies A (P Q:A -> Prop) (xs: list A) :
  (forall x, P x -> Q x) ->
  each P xs -> each Q xs.
Proof.
  induction xs; simpl; intuition.
Qed.
                 
Lemma each_map A B : forall (P:B -> Prop) (f:A->B) (xs:list A),
    each P (map f xs) <-> each (fun x => P (f x)) xs.
Proof.
  induction xs; simpl; intuition.
Qed.

Inductive pairwise {A B} (R:A -> B -> Prop) : list A -> list B -> Prop :=
  | pairwise_nil : pairwise R nil nil
  | pairwise_cons : forall x xs y ys,
      R x y -> pairwise R xs ys -> pairwise R (x::xs) (y::ys).

Lemma pairwise_length A B (R:A -> B -> Prop) xs ys :
  pairwise R xs ys -> length xs = length ys.
Proof.
  intro H; induction H; simpl; auto.
Qed.

Lemma pairwise_le_refl xs : pairwise ord_le xs xs.
Proof.
  induction xs; constructor; auto with ord.
Qed.

Lemma pairwise_eq_refl xs : pairwise ord_eq xs xs.
Proof.
  induction xs; constructor; auto with ord.
  reflexivity.
Qed.
