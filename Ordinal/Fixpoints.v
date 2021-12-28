Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import ClassicalFacts.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Enumerate.

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
