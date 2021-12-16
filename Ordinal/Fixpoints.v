Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import ClassicalFacts.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Classical.

Section fixpoints.
  Variable f : Ord -> Ord.

  Definition iter_f (base:Ord) : nat -> Ord :=
    fix iter_f (n:nat) : Ord :=
      match n with
      | 0 => base
      | S n' => f (iter_f n')
      end.

  Lemma iter_f_monotone :
     (forall x y, x <= y -> f x <= f y) ->
     forall i x y, x <= y -> iter_f x i <= iter_f y i.
  Proof.
    intro H. induction i; simpl; auto.
  Qed.

  Definition fixOrd (base:Ord) : Ord := supOrd (iter_f base).

  Lemma fixOrd_above : forall base, base ≤ fixOrd base.
  Proof.
    intros.
    unfold fixOrd.
    apply (sup_le _ (iter_f base) 0%nat).
  Qed.

  Hypothesis Hmonotone : forall x y, x <= y -> f x <= f y.

  Lemma fixOrd_monotone :
     forall x y, x <= y -> fixOrd x <= fixOrd y.
  Proof.
    unfold fixOrd; intros.
    apply sup_least. intro n.
    eapply ord_le_trans with (iter_f y n); [ | apply sup_le ].
    apply iter_f_monotone; auto.
  Qed.

  Hypothesis Hcont : strongly_continuous f.

  Lemma fixOrd_prefixpoint : forall base, f (fixOrd base) ≤ fixOrd base.
  Proof.
    intros.
    apply ord_le_trans with (supOrd (fun i => f (iter_f base i))).
    - apply (Hcont nat (iter_f base) 0%nat).
    - apply sup_least. intro i.
      unfold fixOrd.
      apply (sup_le _ (iter_f base) (S i)).
  Qed.

  Hypothesis Hinflationary : forall x, x ≤ f x.

  Lemma fixOrd_fixpoint : forall base, fixOrd base ≈ f (fixOrd base).
  Proof.
    intros; split.
    - apply Hinflationary.
    - apply fixOrd_prefixpoint; auto.
  Qed.

  Lemma fixOrd_least : forall base z, base ≤ z -> f z ≤ z -> fixOrd base ≤ z.
  Proof.
    intros.
    unfold fixOrd.
    apply sup_least.
    intro i; induction i; simpl; auto.
    apply ord_le_trans with (f z); auto.
  Qed.

  Lemma normal_fix_continuous : strongly_continuous fixOrd.
  Proof.
    intros A g a0. unfold fixOrd.
    apply sup_least; intro i.
    induction i; simpl.
    - apply sup_ord_le_morphism. intro a.
      rewrite <- (sup_le _ _ 0%nat).
      simpl. auto with ord.
    - etransitivity; [ apply Hmonotone; apply IHi |].
      rewrite (Hcont A (fun i => supOrd (iter_f (g i))) a0).
      apply sup_ord_le_morphism. intro a.
      apply fixOrd_prefixpoint.
  Qed.

End fixpoints.


Lemma iter_f_monotone_func f g n :
  (forall x, f x ≤ g x) ->
  (forall x y, x ≤ y -> g x ≤ g y) ->
  forall x, iter_f f x n ≤ iter_f g x n.
Proof.
  intros Hf Hg.
  induction n; intros; simpl.
  - reflexivity.
  - etransitivity; [ apply Hf | apply Hg; auto ].
Qed.


Definition powOmega (x:Ord) : Ord := expOrd ω x.

Lemma omega_gt1 : 1 < ω.
Proof.
  apply (index_lt ω 1%nat).
Qed.

Lemma powOmega_monotone : forall x y, x ≤ y -> powOmega x ≤ powOmega y.
Proof.
  unfold powOmega. apply expOrd_monotone.
Qed.

Lemma powOmega_increasing : forall x y, x < y -> powOmega x < powOmega y.
Proof.
  intros.
  apply expOrd_increasing; auto.
  apply omega_gt1.
Qed.

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


Definition enum_fixpoints (f:Ord -> Ord) : Ord -> Ord :=
  fix rec (x:Ord) : Ord :=
  match x with
  | ord B g => fixOrd f (ord B (fun b => rec (g b)))
  end.

Lemma enum_fixpoints_monotone f :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall x y, x ≤ y -> enum_fixpoints f x ≤ enum_fixpoints f y).
Proof.
  intros Hf x y; revert x.
  induction y as [C h Hy].
  destruct x as [B g].
  simpl; intros.
  unfold fixOrd.
  apply sup_ord_le_morphism; intro i; simpl.
  apply iter_f_monotone; auto.
  rewrite ord_le_unfold; simpl; intro b.
  rewrite ord_lt_unfold; simpl.
  destruct (ord_le_subord _ _ H b) as [c Hb].
  exists c.
  apply Hy; auto.
Qed.

Lemma enum_fixpoints_increasing f :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall x y, x < y -> enum_fixpoints f x < enum_fixpoints f y).
Proof.
  intros Hf x y H.
  rewrite ord_lt_unfold in H.
  destruct x as [B g].
  destruct y as [C h].
  simpl in *.
  destruct H as [i ?].
  eapply ord_lt_le_trans; [| apply fixOrd_above ].
  rewrite ord_lt_unfold. exists i. simpl.
  apply (enum_fixpoints_monotone f Hf (ord B g) (h i)); auto.
Qed.

Lemma enum_fixpoints_func_mono f g :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall x y, x ≤ y -> g x ≤ g y) ->
  (forall x, f x ≤ g x) ->
  (forall x, enum_fixpoints f x ≤ enum_fixpoints g x).
Proof.
  intros Hf Hg Hfg.
  induction x as [A q Hx]; simpl.
  unfold fixOrd.
  apply sup_ord_le_morphism. intro i.
  transitivity (iter_f f (ord A (fun b : A => enum_fixpoints g (q b))) i).
  - apply iter_f_monotone; auto.
    rewrite ord_le_unfold; simpl; intro a.
    rewrite ord_lt_unfold; simpl; exists a.
    auto.
  - apply iter_f_monotone_func; auto.
Qed.

Lemma enum_are_fixpoints f :
  strongly_continuous f ->
  (forall x, x ≤ f x) ->
  forall x, enum_fixpoints f x ≈ f (enum_fixpoints f x).
Proof.
  intros Hcont Hinflationary.
  destruct x as [X g]; simpl.
  apply fixOrd_fixpoint; auto.
Qed.

Lemma enum_fixpoints_zero f :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  enum_fixpoints f zeroOrd ≈ fixOrd f zeroOrd.
Proof.
  simpl.
  split; apply fixOrd_monotone; auto.
  - rewrite ord_le_unfold; simpl; intuition.
  - rewrite ord_le_unfold; simpl; intuition.
Qed.

Lemma enum_fixpoints_succ f x :
  enum_fixpoints f (succOrd x) ≈ fixOrd f (succOrd (enum_fixpoints f x)).
Proof.
  simpl; intros. reflexivity.
Qed.

Lemma enum_fixpoints_cont f :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall x, x ≤ f x) ->
  strongly_continuous f ->
  strongly_continuous (enum_fixpoints f).
Proof.
  intros Hmono Hinf Hcont A g a0.
  apply fixOrd_least; auto.
  - rewrite ord_le_unfold.
    simpl.
    intros [a i]. simpl.
    rewrite <- (sup_le _ _ a).
    apply enum_fixpoints_increasing; auto with ord.
  - rewrite (Hcont A (fun i => enum_fixpoints f (g i)) a0).
    apply sup_least; intro a.
    rewrite <- enum_are_fixpoints; auto.
    rewrite <- (sup_le _ _ a); auto with ord.
Qed.    

Theorem enum_fixpoints_enumerates f:
  (forall x, x ≤ f x) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  strongly_continuous f ->
  enumerates (enum_fixpoints f) (fun x => x ≈ f x).
Proof.
  intros Hinf Hmono Hcont.
  hnf; intros.
  constructor; auto.
  - apply enum_are_fixpoints; auto.
  - intros; apply enum_fixpoints_monotone; auto.
  - intros; apply enum_fixpoints_increasing; auto.
  - intros x z Hz1 Hz2.
    destruct x as [A g]. simpl.
    apply fixOrd_least; auto.
    + rewrite ord_le_unfold. simpl; intros.
      apply Hz2. apply (index_lt (ord A g) a).
    + apply Hz1.
Qed.


Lemma enum_fixpoints_enumerates_range f : 
  (forall x, x ≤ f x) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  strongly_continuous f ->
  enumerates (enum_fixpoints f) (fun x => exists y, x ≈ enum_fixpoints f y).
Proof.
  intros Hinf Hmono Hcont.
  hnf; intros.
  constructor; auto.
  - intro x. exists x. reflexivity.
  - intros; apply enum_fixpoints_monotone; auto.
  - intros; apply enum_fixpoints_increasing; auto.
  - intros x z [y Hy] H.
    destruct x as [A g]; simpl; intros.
    apply fixOrd_least; auto.
    + rewrite ord_le_unfold; simpl; intros.
      apply H. apply (index_lt (ord A g)).
    + transitivity (f (enum_fixpoints f y)).
      apply Hmono. apply Hy.
      rewrite Hy.
      apply enum_are_fixpoints; auto.
Qed.



Definition ε (x:Ord) := enum_fixpoints powOmega x.

Lemma ε_monotone : forall x y, x ≤ y -> ε x ≤ ε y.
Proof.
  unfold ε.
  apply enum_fixpoints_monotone.
  apply powOmega_monotone.
Qed.

Lemma ε_increasing : forall x y, x < y -> ε x < ε y.
Proof.
  unfold ε.
  apply enum_fixpoints_increasing.
  apply powOmega_monotone.
Qed.

Lemma ε_continuous : strongly_continuous ε.
Proof.
  unfold ε.
  apply enum_fixpoints_cont; auto.
  apply powOmega_monotone.
  apply increasing_inflationary.
  apply powOmega_increasing.
  unfold powOmega.
  apply expOrd_continuous.
  apply omega_gt1.
Qed.

Lemma ε_fixpoint : forall x, ε x ≈ expOrd ω (ε x).
Proof.
  intro x.
  apply enum_are_fixpoints.
  apply expOrd_continuous.
  apply omega_gt1.
  apply increasing_inflationary.
  apply powOmega_increasing.
Qed.

Theorem ε_enumerates : enumerates ε (fun x => x ≈ expOrd ω x).
Proof.
  unfold ε.
  apply enum_fixpoints_enumerates.
  apply increasing_inflationary.
  apply powOmega_increasing.
  apply powOmega_monotone.
  apply expOrd_continuous.
  apply omega_gt1.
Qed.
