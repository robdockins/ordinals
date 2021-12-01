Require Import ClassicalFacts.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.

Module classical.
Section classic.
  Hypothesis EM : excluded_middle.

  Lemma ord_swizzle (x y:Ord) :
    (~(x ≤ y) -> y < x) /\
    (~(x < y) -> y <= x).
  Proof.
    revert y.
    induction x using ordinal_induction. rename H into Hindx.
    induction y using ordinal_induction. rename H into Hindy.
    split.
    * rewrite ord_le_unfold.
      intros.
      destruct (EM (exists a, ~x a < y)).
      2: { elim H; intros.
           destruct (EM (x a < y)); auto.
           elim H0; eauto. }
      clear H.
      destruct H0 as [a Ha].
      destruct (EM (y <= x a)); auto.
      rewrite ord_lt_unfold. exists a. auto.
      destruct (Hindx (x a) (index_lt x a) y).
      rewrite ord_lt_unfold. exists a. intuition.

    * intros.
      rewrite ord_le_unfold. intro a.
      destruct (Hindy (y a) (index_lt y a)).
      apply H0.
      intro.
      apply H.
      rewrite ord_lt_unfold. exists a. auto.
  Qed.

  (** Classicaly, ordinals form a total order. *)
  Theorem order_total (x y:Ord) : x ≤ y \/ y < x.
  Proof.
    destruct (EM (x ≤ y)); auto.
    right.
    destruct (ord_swizzle x y); intuition.
  Qed.

  Theorem order_trichotomy (x y:Ord) : x < y \/ x ≈ y \/ x > y.
  Proof.
    unfold ord_eq.
    destruct (order_total x y); auto.
    destruct (order_total y x); auto.
  Qed.

  Lemma max_or_ascending A (f:A -> Ord) :
    hasMaxElement A f \/ ascendingSet A f.
  Proof.
    destruct (EM (hasMaxElement A f)); auto.
    right; hnf; intros.
    destruct (EM (exists a', f a < f a')); auto.
    elim H. exists a. intros a'.
    destruct (order_total (f a') (f a)); firstorder.
  Qed.

  (** Classicaly, ordinals must either be a zero, successor or limit ordinal. *)
  Theorem ordinal_discriminate (x:Ord) :
    zeroOrdinal x \/ successorOrdinal x \/ limitOrdinal x.
  Proof.
    destruct x as [A f]; simpl.
    destruct (max_or_ascending A f); auto.
    destruct (EM (inhabited A)); intuition.
  Qed.

  (** Classical ordinals form a total order, so every ordinal is complete. *)
  Theorem ord_complete (x:Ord) : complete x.
  Proof.
    induction x as [A f]; simpl; intuition.
    + intros a1 a2; destruct (order_total (f a1) (f a2)).
      * exists a2. split; auto with ord.
      * exists a1. split; auto with ord.
    + apply EM.
  Qed.

  (** Classicaly, we can provide a more traditional induction principle for ordinals
      that has cases for the three classes of ordinal.
    *)
  Lemma classical_ordinal_induction (P:Ord -> Prop) :
    (forall x y, x ≈ y -> P x -> P y) ->
    P zeroOrd ->
    (forall o, P o -> P (succOrd o)) ->
    (forall x, (forall a, a < x -> P a) -> limitOrdinal x -> P x) ->
    forall x, P x.
  Proof.
    intros Heq Hzero Hsucc Hlimit.
    induction x using ordinal_induction. rename H into Hind.
    destruct (ordinal_discriminate x) as [H|[H|H]].
    - apply Heq with zeroOrd.
      symmetry. apply ord_isZero; auto.
      apply Hzero.
    - rewrite ord_isSucc in H.
      destruct H as [o Ho].
      apply Heq with (succOrd o).
      symmetry; auto.
      apply Hsucc.
      apply Hind.
      apply ord_lt_le_trans with (succOrd o).
      apply succ_lt.
      destruct Ho; auto.
    - apply Hlimit; auto.
  Qed.

End classic.
End classical.
