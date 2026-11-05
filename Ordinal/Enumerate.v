From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import NArith.
From Stdlib Require Import ClassicalFacts.

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

(* Conversely, [enumerates_surjective] implies excluded middle.  The
   function z ↦ c + z enumerates the ordinals above c, constructively, and
   surjectivity is then left subtraction: c ≤ z gives a with c + a ≈ z.
   For c = truth_ord R and z = 1, such an a decides R.
 *)
Lemma addOrd_enumerates c : enumerates (addOrd c) (fun z => c ≤ z).
Proof.
  constructor.
  - intro x. apply addOrd_le1.
  - intros. apply addOrd_monotone; auto with ord.
  - intros. apply addOrd_increasing; auto.
  - intros x z Hz H.
    rewrite addOrd_unfold.
    apply lub_least; auto.
    apply sup_least; intro i.
    apply succ_least.
    apply H. apply index_lt.
Qed.

(* Left subtraction: classically, c ≤ z gives a unique a with c + a ≈ z.
   Its existence alone implies excluded middle, already for z = 1. *)
Lemma addOrd_left_subtraction_EM :
  (forall c z, c ≤ z -> exists a, c + a ≈ z) ->
  excluded_middle.
Proof.
  intros H R.
  set (c := classical.truth_ord R).
  assert (Hc : c ≤ 1).
  { unfold c, classical.truth_ord.
    rewrite ord_le_unfold; simpl; intros. apply succ_lt. }
  destruct (H c 1 Hc) as [a [Ha1 Ha2]].
  assert (H0 : 0 < c + a).
  { apply ord_lt_le_trans with 1; auto. apply succ_lt. }
  rewrite addOrd_unfold in H0.
  apply lub_lt in H0. destruct H0 as [H0|H0].
  - left. unfold c, classical.truth_ord in H0.
    rewrite ord_lt_unfold in H0. destruct H0 as [HR _]. exact HR.
  - right. intro HR.
    apply sup_lt in H0. destruct H0 as [i _].
    apply (ord_lt_irreflexive 1).
    apply ord_lt_le_trans with (c + a); auto.
    rewrite addOrd_unfold. rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    apply ord_lt_le_trans with (succOrd c); [| apply succ_monotone, addOrd_le1 ].
    apply ord_le_lt_trans with c; [| apply succ_lt ].
    unfold c, classical.truth_ord.
    rewrite ord_le_unfold; simpl; intros.
    rewrite ord_lt_unfold. exists HR. simpl. reflexivity.
Qed.

Lemma enumerates_surjective_EM :
  (forall f P, enumerates f P -> forall x, P x -> exists a, f a ≈ x) ->
  excluded_middle.
Proof.
  intro H. apply addOrd_left_subtraction_EM.
  intros c z Hcz. exact (H _ _ (addOrd_enumerates c) z Hcz).
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


(* Conversely, [enumerates_range] (and so [increasing_surjective_enumerates])
   implies excluded middle.  The function f z = z + [¬¬(0 < z)] is monotone
   and increasing, but it does not reflect the order: f 0 < f (truth_ord R)
   holds as soon as ¬¬R, while f 1 ≤ f (truth_ord R) gives R.
 *)
Section enumerates_range_EM.
  Let g (z:Ord) := classical.truth_ord (~~(0 < z)).
  Let f (z:Ord) := z + g z.

  Let g_monotone x y : x ≤ y -> g x ≤ g y.
  Proof.
    intro H. unfold g, classical.truth_ord.
    rewrite ord_le_unfold; simpl; intro Hx.
    rewrite ord_lt_unfold; simpl.
    exists (fun Hy => Hx (fun H0 => Hy (ord_lt_le_trans _ _ _ H0 H))).
    reflexivity.
  Qed.

  Let g_le_one x : g x ≤ 1.
  Proof.
    unfold g, classical.truth_ord.
    rewrite ord_le_unfold; simpl; intros. apply succ_lt.
  Qed.

  Let g_pos x : ~~(0 < x) -> 0 < g x.
  Proof.
    intro H. unfold g, classical.truth_ord.
    rewrite ord_lt_unfold. exists H. simpl. reflexivity.
  Qed.

  Let f_monotone x y : x ≤ y -> f x ≤ f y.
  Proof.
    intro H. unfold f. apply addOrd_monotone; auto.
  Qed.

  Let f_le_succ x : f x ≤ succOrd x.
  Proof.
    unfold f.
    transitivity (x + 1).
    - apply addOrd_monotone; auto with ord.
    - rewrite addOrd_succ, addOrd_zero_r. reflexivity.
  Qed.

  Let f_increasing x y : x < y -> f x < f y.
  Proof.
    intro H.
    apply ord_le_lt_trans with (succOrd x); auto.
    apply ord_le_lt_trans with y; [ apply succ_least; auto |].
    unfold f.
    apply ord_le_lt_trans with (y + 0); [ apply addOrd_zero_r |].
    apply addOrd_increasing.
    apply g_pos. intro Hn. apply Hn.
    apply ord_le_lt_trans with x; auto. apply zero_least.
  Qed.

  Lemma enumerates_range_EM :
    (forall f, (forall x y, x ≤ y -> f x ≤ f y) ->
               (forall x y, x < y -> f x < f y) ->
               enumerates f (fun x => exists y, x ≈ f y)) ->
    excluded_middle.
  Proof.
    intro H.
    (* it suffices to show double-negation elimination *)
    cut (forall R:Prop, ~~R -> R).
    { intros DNE P. apply DNE. intro HN. apply HN. right. intro HP. apply HN. left. exact HP. }
    intros R HR.
    set (w := classical.truth_ord R).
    assert (Hlt : f 0 < f w).
    { apply ord_le_lt_trans with 0.
      - unfold f.
        rewrite addOrd_zero_l.
        unfold g, classical.truth_ord.
        rewrite ord_le_unfold; simpl; intro Hn.
        elim Hn. intro H0. apply (ord_lt_irreflexive 0); auto.
      - apply ord_lt_le_trans with (g w).
        + apply g_pos. intro Hn. apply HR. intro HR'. apply Hn.
          unfold w, classical.truth_ord.
          rewrite ord_lt_unfold. exists HR'. reflexivity.
        + unfold f. apply addOrd_le2. }
    assert (Hle : f 1 ≤ f w).
    { apply (enumerates_least f _ (H f f_monotone f_increasing) 1 (f w)).
      - exists w. reflexivity.
      - intros y Hy.
        apply ord_le_lt_trans with (f 0); auto.
        apply f_monotone.
        rewrite ord_lt_unfold in Hy. destruct Hy as [[] Hy]. auto. }
    assert (H1 : succOrd 1 ≤ succOrd w).
    { transitivity (f 1).
      { unfold f. transitivity (1 + 1).
        - rewrite addOrd_succ, addOrd_zero_r. reflexivity.
        - apply addOrd_monotone; [ reflexivity |].
          apply succ_least. apply g_pos.
          intro Hn. apply Hn. apply succ_lt. }
      transitivity (f w); auto. }
    apply succ_cancel_le in H1.
    assert (H0 : 0 < w).
    { apply ord_lt_le_trans with 1; auto. apply succ_lt. }
    unfold w, classical.truth_ord in H0.
    rewrite ord_lt_unfold in H0. destruct H0 as [HR' _]. exact HR'.
  Qed.
End enumerates_range_EM.

Corollary increasing_surjective_enumerates_EM :
  (forall f (P:Ord -> Prop),
      (forall x y, x ≤ y -> f x ≤ f y) ->
      (forall x y, x < y -> f x < f y) ->
      (forall x, P x -> exists a, f a ≈ x) ->
      (forall x, P (f x)) ->
      enumerates f P) ->
  excluded_middle.
Proof.
  intro H. apply enumerates_range_EM.
  intros f Hmono Hinc. apply H; auto.
  - intros x [y Hy]. exists y. symmetry. exact Hy.
  - intro x. exists x. reflexivity.
Qed.


Definition unbounded (P:Ord -> Prop) :=
  forall x, P x -> exists y, x < y /\ P y.

(* Unboundedness needs no classical reasoning: f (S x) is above x. *)
Corollary enumerates_unbounded f P :
  enumerates f P -> unbounded P.
Proof.
  intros Henum x Hx.
  exists (f (succOrd x)).
  split.
  - apply ord_le_lt_trans with (f x).
    + apply increasing_inflationary.
      apply (enumerates_increasing f P Henum).
    + apply enumerates_increasing with P; auto.
      apply succ_lt.
  - apply enumerates_included. auto.
Qed.

