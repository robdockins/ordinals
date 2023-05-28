Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import ClassicalFacts.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Classical.
From Ordinal Require Import Arith.

(* We say a function f enumerates a class of ordinals P if
   f x is the least element of P that is strictly above
   all f y for y < x. *)
Record enumerates (f:Ord -> Ord) (P:Ord -> Prop) : Prop :=
  Enumerates
    { enumerates_included   : forall x, P (f x);
      enumerates_monotone   : forall x y, x ≤ y -> f x ≤ f y;
      enumerates_increasing : forall x y, x < y -> f x < f y;
      enumerates_least      : forall x z, P z -> (forall y, y < x -> f y < z) -> f x ≤ z
    }.

Lemma enumerates_range (EM:excluded_middle) f :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall x y, x < y -> f x < f y) ->
  enumerates f (fun x => exists y, x ≈ f y).
Proof.
  intros Hmono Hinc.
  constructor; auto.
  - intro x; exists x; reflexivity.
  - intros x z [y Hy] H.
    rewrite Hy.
    destruct (classical.order_total EM x y).
    + apply Hmono; auto.
    + apply H in H0.
      rewrite <- Hy in H0.
      elim (ord_lt_irreflexive z); auto.
Qed.

Lemma enumerates_equiv_pred f P P' :
  (forall x, P x <-> P' x) ->
  enumerates f P ->
  enumerates f P'.
Proof.
  intros Hp Hf.
  constructor.
  - intro x. apply Hp. apply enumerates_included; auto.
  - eapply enumerates_monotone; eauto.
  - eapply enumerates_increasing; eauto.
  - intros x z Hz1 Hz2.
    apply (enumerates_least f P Hf); auto.
    apply Hp; auto.
Qed.


Lemma enumerates_unique_aux f g P :
  enumerates f P ->
  enumerates g P ->
  (forall x, f x ≤ g x).
Proof.
  intros Hf Hg.
  induction x using ordinal_induction.
  apply (enumerates_least f P Hf x); auto.
  apply (enumerates_included g P Hg x).
  intros y Hy.
  apply ord_le_lt_trans with (g y).
  apply H; auto.
  apply (enumerates_increasing g P Hg y x); auto.
Qed.

Theorem enumerates_unique f g P :
  enumerates f P ->
  enumerates g P ->
  (forall x, f x ≈ g x).
Proof.
  intros; split; apply enumerates_unique_aux with P; auto.
Qed.

(* If f enumeates P then f 0 is the least element of P *)
Theorem enumerates_zero f P :
  enumerates f P ->
  (forall z, P z -> f 0 ≤ z).
Proof.
  intros Henum z Hz.
  apply (enumerates_least f P Henum 0); auto.
  intros.
  rewrite ord_lt_unfold in H.
  destruct H as [[] _].
Qed.

(* If f enumeates P then f (S x) is the least element of P strictly above (f x) *)
Theorem enumerates_succ f P :
  enumerates f P ->
  (forall x z, P z -> f x < z -> f (succOrd x) <= z).
Proof.
  intros Henum x z Hz Hx.
  apply (enumerates_least f P Henum (succOrd x)); auto.
  intros y Hy.
  apply ord_le_lt_trans with (f x); auto.
  apply (enumerates_monotone f P Henum y x); auto.
  rewrite ord_lt_unfold in Hy.
  destruct Hy as [[] Hy].
  auto.
Qed.

(* Classically, we can show that if f enumerates P then
   f is surjective on P.
 *)
Theorem enumerates_surjective (EM:excluded_middle) f P:
  enumerates f P -> forall x, P x -> exists a, f a ≈ x.
Proof.
  intros Henum x Hx.
  set (Q z := f z >= x).
  destruct (classical.ord_well_ordered EM Q x) as [a [??]]; auto.
  - hnf. apply increasing_inflationary.
    apply (enumerates_increasing f P Henum).
  - exists a. unfold Q in *.
    split; auto.
    apply (enumerates_least f P Henum a); auto.
    intros y Hy.
    destruct (classical.order_total EM x (f y)); auto.
    apply H0 in H1.
    elim (ord_lt_irreflexive y).
    apply ord_lt_le_trans with a; auto.
Qed.

(* Morover, classically a monotone, increasing, surjective function onto P enumerates P.
 *)
Theorem increasing_surjective_enumerates (EM:excluded_middle) f (P:Ord -> Prop) :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall x y, x < y -> f x < f y) ->
  (forall x, P x -> exists a, f a ≈ x) ->
  (forall x, P (f x)) ->
  enumerates f P.
Proof.
  intros Hmono Hinc Hsurj HP.
  constructor; auto.

  intros x z Hz1 Hz2.
  destruct (Hsurj z) as [a Ha]; auto.
  rewrite <- Ha.
  destruct (classical.order_total EM x a); auto.
  apply Hz2 in H.
  elim (ord_lt_irreflexive z).
  apply ord_le_lt_trans with (f a); auto.
  apply Ha.
Qed.


Definition unbounded (P:Ord -> Prop) :=
  forall x, P x -> exists y, x < y /\ P y.

Corollary enumerates_unbounded (EM:excluded_middle) f P :
  enumerates f P -> unbounded P.
Proof.
  intros Henum x Hx.
  destruct (enumerates_surjective EM f P Henum x Hx) as [a Ha].
  exists (f (succOrd a)).
  split.
  rewrite <- Ha.
  apply enumerates_increasing with P; auto.
  apply succ_lt.
  apply enumerates_included. auto.
Qed.

