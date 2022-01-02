Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.

(** * Definitions by transfinite primitive recursion.
  *)
Definition foldOrd (z:Ord) (s:Ord -> Ord) : Ord -> Ord :=
  fix foldOrd (x:Ord) : Ord :=
    match x with
    | ord A f => z ⊔ supOrd (fun i => s (foldOrd (f i)))
    end.

Lemma foldOrd_unfold z s x :
  foldOrd z s x = z ⊔ supOrd (fun i => s (foldOrd z s (x i))).
Proof.
  destruct x; reflexivity.
Qed.

Lemma foldOrd_least z s (q:Ord -> Ord)
      (Hz : forall x, z ≤ q x)
      (Hmono : forall x y, x ≤ y -> s x ≤ s y)
      (Hsq : forall (x:Ord) (i:x), s (q (x i)) ≤ (q x)) :
      (forall x, foldOrd z s x ≤ q x).
Proof.
  induction x as [A f Hx].
  simpl.
  apply lub_least.
  - apply Hz.
  - apply sup_least. intros a.
    transitivity (s (q (f a))); auto.
    apply (Hsq (ord A f)).
Qed.

Lemma foldOrd_unfold_le z s (x:Ord) i :
  s (foldOrd z s (x i)) ≤ foldOrd z s x.
Proof.
  destruct x as [A f]. simpl.
  etransitivity; [ | apply lub_le2 ].
  etransitivity; [ | apply (sup_le _ _ i)]. simpl.
  reflexivity.
Qed.

Lemma foldOrd_above_z z s x : z ≤ foldOrd z s x.
Proof.
  destruct x as [A f]; simpl.
  apply lub_le1.
Qed.

Lemma foldOrd_monotone z s : forall x y,
    (forall a b, a ≤ b -> s a ≤ s b) ->
    x ≤ y -> foldOrd z s x ≤ foldOrd z s y.
Proof.
  induction x as [A f Hx]. simpl; intros.
  apply lub_least.
  - apply foldOrd_above_z.
  - apply sup_least. intros a; simpl.
    rewrite ord_le_unfold in H0.
    specialize (H0 a). simpl in H0.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [b ?].
    rewrite <- (foldOrd_unfold_le z s y b).
    apply H.
    apply Hx; auto.
Qed.

Lemma foldOrd_zero z s : foldOrd z s 0 ≈ z.
Proof.
  split.
  - simpl.
    apply lub_least.
    + apply ord_le_refl.
    + apply sup_least. intros. elim a.
  - apply foldOrd_above_z.
Qed.

Lemma foldOrd_increasing z s : forall x y,
    (forall a, z ≤ a -> a < s a) ->
    (forall a b, a ≤ b -> s a ≤ s b) ->
    x < y -> foldOrd z s x < foldOrd z s y.
Proof.
  intros x y. revert x.
  destruct y as [B g]; simpl; intros.
  rewrite ord_lt_unfold in H1.
  destruct H1 as [b ?].
  simpl in *.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ b).
  eapply ord_le_lt_trans; [ | apply H; apply foldOrd_above_z ].
  apply foldOrd_monotone; auto.
Qed.

Lemma foldOrd_succ z s x :
  (forall q, z ≤ q -> z ≤ s q) ->
  foldOrd z s (succOrd x) ≈ s (foldOrd z s x).
Proof.
  split.
  - simpl.
    apply lub_least.
    + apply H.
      destruct x; simpl.
      apply lub_le1.
    + apply sup_least. intro.
      apply ord_le_refl.
  - simpl.
    + rewrite <- lub_le2.
      rewrite <- (sup_le _ _ tt).
      reflexivity.
Qed.

Lemma foldOrd_limit z s x :
  limitOrdinal x ->
  (forall a b, a ≤ b -> s a ≤ s b) ->
  foldOrd z s x ≈ boundedSup x (foldOrd z s).
Proof.
  intros.
  split.
  - destruct x as [A f]. destruct H. simpl.
    apply lub_least.
    + destruct H as [a0].
      eapply ord_le_trans; [ | apply (sup_le _ _ a0) ]. simpl.
      destruct (f a0); simpl.
      apply lub_le1.
    + apply sup_least. intro a.
      destruct (H1 a) as [a' ?].
      eapply ord_le_trans; [ | apply (sup_le _ _ a') ]. simpl.
      apply ord_le_trans with (foldOrd z s (succOrd (f a))).
      simpl.
      eapply ord_le_trans; [ | apply lub_le2 ].
      eapply ord_le_trans; [ | apply (sup_le _ _ tt) ]. simpl.
      apply ord_le_refl.
      apply foldOrd_monotone; auto.
      apply succ_least. auto.
  - apply boundedSup_least. intros a Ha.
    apply foldOrd_monotone; auto with ord.
Qed.

Lemma foldOrd_strongly_continuous z s :
  strongly_continuous (foldOrd z s).
Proof.
  red; simpl; intros.
  apply lub_least.
  - rewrite <- (sup_le _ _ a0).
    apply foldOrd_above_z.
  - apply sup_least.
    intros [a q]; simpl.
    rewrite <- (sup_le _ _ a).
    apply foldOrd_unfold_le.
Qed.

Lemma foldOrd_complete z s :
  complete z ->
  (forall x, z <= x -> 0 < s x) ->
  z <= s z ->
  (forall x y, x <= y -> s x <= s y) ->
  (forall o, complete o -> complete (s o)) ->
  forall x, complete x -> complete (foldOrd z s x).
Proof.
  intros Hz Hs0 Hs1 Hs2 Hs3.
  induction x as [X f Hx].
  simpl; intros [Hx1 [Hx2 Hx3]].
  assert (Hsup : complete (supOrd (fun i : X => s (foldOrd z s (f i))))).
  { apply sup_complete; auto.
    - intros x1 x2.
      destruct (Hx1 x1 x2) as [x' [Hx'1 Hx'2]].
      exists x'.
      split; apply Hs2; apply foldOrd_monotone; auto.
    - destruct Hx2 as [[x]|Hx2].
      + left. exists x.
        apply Hs0.
        apply foldOrd_above_z.
      + right. intro x; elim Hx2. exact (inhabits x).
  }
  destruct Hx2 as [[x]|Hx2].
  + apply lub_complete2; auto.
    rewrite <- (sup_le _ _ x).
    transitivity (s z); auto.
    apply Hs2. apply foldOrd_above_z.
  + apply lub_complete1; auto.
    apply sup_least. intro x.
    elim Hx2. exact (inhabits x).
Qed.


(** * Ordinal addition *)

Definition addOrd (x y:Ord) := foldOrd x succOrd y.

Notation "x + y" := (addOrd x y) : ord_scope.

Lemma addOrd_le1 x y : x ≤ x + y.
Proof.
  destruct y as [B g].
  simpl.
  apply lub_le1.
Qed.

Lemma addOrd_le2 x y : y ≤ x + y.
Proof.
  induction y as [B g Hy].
  destruct x as [A f].
  simpl.
  rewrite ord_le_unfold; intro b. simpl.
  rewrite ord_lt_unfold. simpl.
  exists (inr (existT _ b tt)).
  simpl.
  auto.
Qed.

Lemma addOrd_zero_r x : x ≈ x + 0.
Proof.
  split.
  - simpl.
    apply lub_le1.
  - simpl.
    apply lub_least.
    reflexivity.
    apply sup_least. intros [].
Qed.

Lemma addOrd_zero_l x : x ≈ 0 + x.
Proof.
  induction x as  [X f Hx].
  split; simpl.
  - rewrite ord_le_unfold.
    simpl; intro x.
    rewrite ord_lt_unfold; simpl.
    exists (inr (existT _ x tt)).
    simpl. apply Hx.
  - rewrite ord_le_unfold.
    simpl; intros [[]|[x []]]. simpl.
    rewrite ord_lt_unfold; simpl.
    exists x.
    apply Hx.
Qed.

Lemma addOrd_monotone :
  forall x y z1 z2, x ≤ y -> z1 ≤ z2 -> x + z1 ≤ y + z2.
Proof.
  induction z1 as [C h]. destruct z2 as [D i].
  simpl; intros.
  apply lub_least.
  + rewrite <- lub_le1. auto.
  + rewrite <- lub_le2.
    apply sup_least; intro c.
    destruct (ord_le_subord _ _ H1 c) as [d Hd]. simpl in *.
    rewrite <- (sup_le _ _ d).
    apply succ_monotone.
    apply H; auto.
Qed.

Lemma addOrd_increasing :
  forall x y z, x < y -> z + x < z + y.
Proof.
  intros.
  unfold addOrd.
  apply foldOrd_increasing; auto with ord.
  apply succ_monotone.
Qed.

Lemma addOrd_continuous x :
  strongly_continuous (addOrd x).
Proof.
  unfold addOrd.
  apply foldOrd_strongly_continuous.
Qed.

Lemma addOrd_complete x y :
  complete x -> complete y -> complete (x + y).
Proof.
  intros. unfold addOrd.
  apply foldOrd_complete; auto with ord.
  - intros. eapply ord_le_lt_trans; auto with ord.
  - intros; apply succ_monotone; auto.
  - apply succ_complete.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_le ++> ord_le ++> ord_le as addOrd_le_mor.
Proof.
  intros. apply addOrd_monotone; auto.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_le ++> ord_lt ++> ord_lt as addOrd_lt_mor2.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply addOrd_increasing; eauto.
  apply addOrd_monotone; auto.
  reflexivity.
Qed.

Add Parametric Morphism : addOrd with signature
   ord_eq ==> ord_eq ==> ord_eq as addOrd_eq_mor.
Proof.
  intros; split; apply addOrd_le_mor; solve [apply H|apply H0].
Qed.

Lemma addOrd_lub a b c :
  a + (b ⊔ c) ≈ (a + b) ⊔ (a + c).
Proof.
  apply (lub_continuous (addOrd a)).
  - intros. apply addOrd_monotone; auto with ord.
  - apply foldOrd_strongly_continuous.
Qed.

Lemma addOrd_assoc a b c :
  a + (b + c) ≈ a + b + c.
Proof.
  induction c as [C g]; simpl.
  rewrite addOrd_lub.
  split.
  - apply lub_least.
    + apply lub_le1.
    + unfold addOrd.
      rewrite foldOrd_unfold at 1.
      apply lub_least.
      rewrite <- lub_le1.
      apply foldOrd_above_z.
      apply sup_least. simpl.
      intros [??]. simpl.
      apply succ_least.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ x).
      rewrite ord_lt_unfold.
      simpl. exists tt; simpl.
      apply H.
  - apply lub_least.
    + apply lub_le1.
    + apply sup_least; intro c.
      apply succ_least.
      rewrite <- H.
      rewrite <- addOrd_lub.
      apply addOrd_increasing.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ c).
      rewrite ord_lt_unfold. exists tt; simpl.
      reflexivity.
Qed.

Lemma addOrd_cancel_le a b x y :
  a + x ≤ b + y -> a ≥ b -> x ≤ y.
Proof.
  revert y.
  induction x as [X f].
  intro y.
  unfold addOrd. rewrite foldOrd_unfold.
  intros H1 H2.
  rewrite ord_le_unfold. simpl; intro x.
  assert (H3 : a + f x < b + y).
  { eapply ord_lt_le_trans; [ | apply H1 ].
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ x).
    rewrite ord_lt_unfold. exists tt. simpl.
    reflexivity. }
  unfold addOrd at 2 in H3.
  rewrite foldOrd_unfold in H3.
  apply lub_lt in H3.
  destruct H3.
  - elim (ord_lt_irreflexive b).
    apply ord_le_lt_trans with (a + f x); auto.
    rewrite <- H2. apply addOrd_le1.
  - apply sup_lt in H0.
    destruct H0 as [i ?].
    rewrite ord_lt_unfold.
    exists i.
    apply H; auto.
    rewrite ord_lt_unfold in H0.
    destruct H0; simpl in *.
    auto.
Qed.


Lemma addOrd_cancel a b x y :
  a + x ≈ b + y -> a ≈ b -> x ≈ y.
Proof.
  unfold ord_eq; intuition; eapply addOrd_cancel_le; eauto.
Qed.


(** * Ordinal multiplication *)

Fixpoint mulOrd (x:Ord) (y:Ord) : Ord :=
    match y with
    | ord B g => supOrd (fun b:B => mulOrd x (g b) + x)
    end.

Notation "x * y" := (mulOrd x y) : ord_scope.

Lemma mulOrd_unfold (x:Ord) (y:Ord) :
  x * y =
  supOrd (fun i:y => x * (y i) + x).
Proof.
  destruct y; auto.
Qed.

Lemma mulOrd_monotone1 : forall z x y, x ≤ y -> x * z ≤ y * z.
Proof.
  induction z as [C h Hz].
  simpl; intros.
  apply sup_least. intro c. simpl.
  rewrite <- (sup_le _ _ c).
  apply addOrd_monotone; auto.
Qed.

Lemma mulOrd_monotone2 : forall y x z, y ≤ z -> x * y ≤ x * z.
Proof.
  induction y as [B g Hy].
  intros.
  destruct x as [A f]; simpl in *.
  apply sup_least. intro b.
  rewrite ord_le_unfold in H.
  specialize (H b).
  simpl in H.
  rewrite ord_lt_unfold in H.
  destruct H as [q ?].
  specialize (Hy b).
  generalize (Hy (ord A f) (z q) H).
  intros.
  rewrite (mulOrd_unfold (ord A f) z).
  rewrite <- (sup_le _ _ q).
  simpl.
  apply lub_least.
  - rewrite <- lub_le1.
    apply Hy. auto.
  - rewrite <- lub_le2.
    apply sup_least; intro i.
    rewrite <- (sup_le _ _ i).
    apply succ_monotone.
    apply addOrd_monotone; auto.
    reflexivity.
Qed.

Lemma mulOrd_increasing2 : forall x y z,
    0 < x ->
    y < z ->
    x * y < x * z.
Proof.
  intros x y [C h] Hx H.
  rewrite (mulOrd_unfold x (ord C h)).
  simpl.
  rewrite ord_lt_unfold in H.
  destruct H as [c Hc]. simpl in Hc.
  rewrite <- (sup_le _ _ c).
  apply ord_le_lt_trans with (mulOrd x (h c)); [ apply mulOrd_monotone2 ; assumption | ].
  apply ord_le_lt_trans with (addOrd (mulOrd x (h c)) zeroOrd).
  - apply addOrd_zero_r.
  - apply addOrd_increasing. auto.
Qed.

Add Parametric Morphism : mulOrd with signature
    ord_le ++> ord_le ++> ord_le as mulOrd_le_mor.
Proof.
  intros.
  apply ord_le_trans with (x * y0).
  apply mulOrd_monotone2; auto.
  apply mulOrd_monotone1; auto.
Qed.

Add Parametric Morphism : mulOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as mulOrd_eq_mor.
Proof.
  unfold ord_eq; intuition; apply mulOrd_le_mor; auto.
Qed.


Lemma mulOrd_zero_r : forall x, x * 0 ≈ 0.
Proof.
  intros; split.
  - destruct x as [A f]. simpl.
    apply sup_least. intuition.
  - apply zero_least.
Qed.

Lemma mulOrd_zero_l : forall x, 0 * x ≈ 0.
Proof.
  induction x as [X f Hx].
  split; simpl.
  - apply sup_least; intro x.
    apply lub_least.
    apply Hx.
    apply sup_least; intros [].
  - apply zero_least.
Qed.

Lemma mulOrd_succ : forall x y, x * (succOrd y) ≈ (x * y) + x.
Proof.
  intros; split; simpl.
  - apply sup_least; auto with ord.
  - rewrite <- (sup_le _ _ tt); auto with ord.
Qed.

Lemma mulOrd_one_r : forall x, mulOrd x 1 ≈ x.
Proof.
  intro.
  rewrite mulOrd_succ.
  rewrite mulOrd_zero_r.
  symmetry.
  apply addOrd_zero_l.
Qed.

Lemma mulOrd_continuous x : strongly_continuous (mulOrd x).
Proof.
  red; simpl; intros.
  apply sup_least.
  intros [a q]. simpl.
  rewrite <- (sup_le _ _ a).
  rewrite (mulOrd_unfold x (f a)).
  rewrite <- (sup_le _ _ q).
  apply ord_le_refl.
Qed.

Lemma mulOrd_lub a b c :
  a * (b ⊔ c) ≈ (a * b) ⊔ (a * c).
Proof.
  apply (lub_continuous (mulOrd a)).
  - intros. apply mulOrd_monotone2; auto with ord.
  - apply mulOrd_continuous.
Qed.

Lemma mulOrd_one_l : forall x, mulOrd 1 x ≈ x.
Proof.
  intro.
  induction x as [X f].
  rewrite mulOrd_unfold.
  split.
  - apply sup_least. intro i.
    simpl.
    apply lub_least.
    + rewrite H. apply (index_le (ord X f)).
    + apply sup_least; intro.
      apply succ_least.
      rewrite ord_lt_unfold. exists i. simpl.
      apply lub_least.
      apply H.
      apply sup_least; intros [].
  - rewrite ord_le_unfold; intro i.
    rewrite <- (sup_le _ _ i).
    simpl.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ tt).
    rewrite ord_lt_unfold. exists tt. simpl.
    rewrite <- lub_le1.
    apply H.
Qed.

Lemma mulOrd_positive : forall x y,
    0 < x ->
    0 < y ->
    0 < x * y.
Proof.
  intros x y Hx Hy.
  destruct x as [A f].
  destruct y as [B g].
  simpl.
  rewrite ord_lt_unfold in Hx.
  rewrite ord_lt_unfold in Hy.
  destruct Hx as [a _].
  destruct Hy as [b _].
  simpl in *.
  rewrite <- (sup_le _ _ b).
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ a).
  rewrite ord_lt_unfold. simpl.
  exists tt.
  auto with ord.
Qed.

Lemma mulOrd_limit : forall x y,
    limitOrdinal y ->
    x * y ≈ supOrd (fun b:y => x * (y b)).
Proof.
  destruct y as [B g]; simpl; intros.
  split.
  - apply sup_least. intro b.
    destruct H as [_ H].
    destruct (H b) as [b' Hb'].
    rewrite <- (sup_le _ _ b').
    apply ord_le_trans with (mulOrd x (succOrd (g b))).
    apply (mulOrd_succ x (g b)).
    apply mulOrd_monotone2.
    apply succ_least; auto.
  - apply sup_least. intro b.
    rewrite <- (sup_le _ _ b).
    apply addOrd_le1.
Qed.

Lemma mulOrd_complete x y : complete x -> complete y -> complete (x * y).
Proof.
  induction y as [Y g Hy]; simpl mulOrd; intros Hx [Hy1 [Hy2 Hy3]].
  apply sup_complete.
  - intros. apply addOrd_complete; auto.
  - intros y1 y2.
    destruct (Hy1 y1 y2) as [y' [Hy'1 Hy'2]].
    exists y'. split.
    + apply addOrd_monotone; auto.
      apply mulOrd_monotone2; auto.
      reflexivity.
    + apply addOrd_monotone; auto.
      apply mulOrd_monotone2; auto.
      reflexivity.
  - destruct (complete_zeroDec x Hx).
    + right; intro y.
      rewrite (addOrd_zero_l 0).
      apply addOrd_monotone; auto.
      rewrite H.
      rewrite mulOrd_zero_l.
      reflexivity.
    + destruct Hy2 as [[y]|Hy2].
      * left. exists y.
        apply ord_lt_le_trans with x; auto.
        rewrite (addOrd_zero_l x) at 1.
        apply addOrd_monotone; auto with ord.
      * right.
        intro y. elim Hy2. exact (inhabits y).
Qed.


Lemma ordDistrib_left a b c :
  a * (b + c) ≈ (a * b) + (a * c).
Proof.
  induction c as [C h]; simpl.
  rewrite (mulOrd_lub a).
  split.
  - apply lub_least.
    + apply lub_le1.
    + unfold mulOrd at 1.
      simpl. fold mulOrd.
      apply sup_least. intros [??]. simpl.
      rewrite (H x).
      rewrite <- addOrd_assoc.
      unfold addOrd at 1.
      rewrite foldOrd_unfold.
      apply ord_lub_le_mor.
      { reflexivity. }
      apply sup_least. intro i.
      rewrite <- (sup_le _ _ (existT _ x i)). simpl.
      reflexivity.
  - apply lub_least.
    + apply lub_le1.
    + apply sup_least; intros [??]. simpl.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ (existT _ x tt)). simpl.
      apply succ_least.
      rewrite (H x).
      rewrite <- addOrd_assoc.
      apply addOrd_increasing.
      apply index_lt.
Qed.


Lemma mulOrd_assoc a b c :
  a * (b * c) ≈ a * b * c.
Proof.
  induction c as [C h]; simpl.
  split.
  - apply sup_least. intros [??]. simpl.
    rewrite <- (sup_le _ _ x).
    rewrite <- (H x).
    rewrite <- ordDistrib_left.
    destruct (b * h x + b) as [Q q]; simpl.
    rewrite <- (sup_le _ _ o).
    reflexivity.
  - apply sup_least. simpl; intro x.
    rewrite <- (H x).
    rewrite <- ordDistrib_left.
    rewrite mulOrd_unfold.
    apply sup_least; intro i.
    rewrite <- (sup_le _ _ (existT _ x i)). simpl.
    reflexivity.
Qed.

(** * Ordinal exponentiation *)

Definition expOrd (x y:Ord) : Ord :=
  foldOrd 1 (fun a => a * x) y.

Lemma expOrd_unfold (x:Ord) (y:Ord) :
  expOrd x y =
  1 ⊔ supOrd (fun i:y => expOrd x (y i) * x).
Proof.
  destruct y; auto.
Qed.

Lemma expOrd_nonzero x y : 0 < expOrd x y.
Proof.
  apply ord_lt_le_trans with 1.
  apply succ_lt.
  apply foldOrd_above_z.
Qed.

Lemma expOrd_zero x : expOrd x 0 ≈ 1.
Proof.
  apply foldOrd_zero.
Qed.

Lemma expOrd_succ x y :
  0 < x ->
  expOrd x (succOrd y) ≈ (expOrd x y) * x.
Proof.
  intros.
  apply foldOrd_succ.
  intros.
  apply succ_least.
  apply mulOrd_positive.
  rewrite ord_le_unfold in H0. apply (H0 tt). auto.
Qed.

Lemma expOrd_monotone a : forall x y,
    x ≤ y ->
    expOrd a x ≤ expOrd a y.
Proof.
  intros. apply foldOrd_monotone; auto.
  intros; apply mulOrd_monotone1; auto.
Qed.

Lemma expOrd_monotone_base : forall x y a,
  x ≤ y ->
  expOrd x a ≤ expOrd y a.
Proof.
  intros.
  induction a as [A f].
  do 2 rewrite expOrd_unfold.
  apply lub_least. { apply lub_le1. }
  rewrite <- lub_le2.
  apply sup_least; intro i.
  rewrite <- (sup_le _ _ i).
  etransitivity.
  { apply mulOrd_monotone2. apply H. }
  apply mulOrd_monotone1.
  apply H0.
Qed.

Add Parametric Morphism : expOrd with signature
    ord_le ++> ord_le ++> ord_le as expOrd_le_mor.
Proof.
  intros.
  transitivity (expOrd x y0).
  apply expOrd_monotone; auto.
  apply expOrd_monotone_base; auto.
Qed.

Add Parametric Morphism : expOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as expOrd_eq_mor.
Proof.
  unfold ord_eq; intuition; apply expOrd_le_mor; auto.
Qed.

Lemma expOrd_increasing a (Ha : 1 < a) :
  forall x y,
    x < y ->
    expOrd a x < expOrd a y.
Proof.
  intros.
  apply foldOrd_increasing; auto.
  - intros.
    rewrite <- (mulOrd_one_r a0) at 1.
    apply mulOrd_increasing2; auto.
    apply ord_lt_le_trans with 1; auto.
    apply succ_lt.
  - apply mulOrd_monotone1.
Qed.

Lemma expOrd_limit x y (Hx: 1 < x) :
  limitOrdinal y ->
  expOrd x y ≈ boundedSup y (expOrd x).
Proof.
  intros.
  apply foldOrd_limit; auto.
  apply mulOrd_monotone1.
Qed.

Lemma expOrd_continuous x :
  strongly_continuous (expOrd x).
Proof.
  apply foldOrd_strongly_continuous; auto.
Qed.

Lemma expOrd_complete x y :
  0 < x -> complete x -> complete y -> complete (expOrd x y).
Proof.
  intros Hx0 Hx Hy. unfold expOrd.
  apply foldOrd_complete; auto.
  - apply succ_complete. apply zero_complete.
  - intros. apply mulOrd_positive; auto.
    apply ord_lt_le_trans with 1; auto.
    apply succ_lt.
  - apply succ_least.
    apply mulOrd_positive; auto.
    apply succ_lt.
  - intros. apply mulOrd_monotone1; auto.
  - intros; apply mulOrd_complete; auto.
Qed.


Lemma expOrd_one_base x : expOrd 1 x ≈ 1.
Proof.
  induction x as [A f].
  rewrite expOrd_unfold.
  split.
  - apply lub_least; auto with ord.
    apply sup_least; intro i.
    rewrite mulOrd_one_r.
    apply (H i).
  - apply lub_le1.
Qed.

Lemma expOrd_one x : expOrd x 1 ≈ 1 ⊔ x.
Proof.
  rewrite expOrd_unfold.
  split; apply lub_least.
  apply lub_le1.
  apply sup_least; intro i.
  rewrite expOrd_zero.
  rewrite mulOrd_one_l.
  apply lub_le2.
  apply lub_le1.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ tt).
  rewrite expOrd_zero.
  rewrite mulOrd_one_l.
  reflexivity.
Qed.

Lemma expOrd_one' x : x > 0 -> expOrd x 1 ≈ x.
Proof.
  intros.
  rewrite expOrd_one.
  split.
  apply lub_least; auto with ord.
  apply succ_least; auto.
  apply lub_le2.
Qed.  

Lemma expOrd_lub a b c :
  expOrd a (b ⊔ c) ≈ expOrd a b ⊔ expOrd a c.
Proof.
  unfold expOrd.
  apply lub_continuous.
  intros; apply foldOrd_monotone; auto.
  intros; apply mulOrd_monotone1; auto.
  apply foldOrd_strongly_continuous.
Qed.

Lemma expOrd_add a b c :
  expOrd a (b + c) ≈ expOrd a b * expOrd a c.
Proof.
  induction c as [C h]; simpl.
  rewrite expOrd_lub.
  split.
  - apply lub_least.
    + rewrite <- (sup_le _ _ (inl _ tt)).
      transitivity (0 + expOrd a b).
      { apply addOrd_zero_l. }
      apply addOrd_monotone; auto with ord.
    + rewrite expOrd_unfold at 1.
      apply lub_least.
      * rewrite <- (sup_le _ _ (inl _ tt)).
        transitivity (0 + 1).
        { apply addOrd_zero_l. }
        apply addOrd_monotone; auto with ord.
        rewrite ord_le_unfold. simpl; intro.
        apply expOrd_nonzero.
      * apply sup_least; simpl.
        intros [??]. simpl.
        rewrite (H x).
        rewrite <- mulOrd_assoc.
        rewrite mulOrd_unfold.
        apply sup_least. simpl; intro i.
        rewrite <- (sup_le _ _ (inr _ (existT _ x i))). simpl.
        reflexivity.
  - apply sup_least. intros [|[x i]]; simpl.
    + rewrite <- lub_le1.
      transitivity (0 + expOrd a b).
      apply addOrd_monotone; auto with ord.
      apply sup_least; intros [].
      apply addOrd_zero_l.
    + rewrite <- lub_le2.
      transitivity (expOrd a (b + h x) * a).
      rewrite (H x).
      rewrite <- mulOrd_assoc.
      rewrite (mulOrd_unfold (expOrd a b) (expOrd a (h x) * a)).
      rewrite <- (sup_le _ _ i).
      reflexivity.
      rewrite ord_le_unfold. intro j.
      rewrite ord_lt_unfold. simpl.
      exists (inr _ (existT _ (existT _ x tt) j)). simpl.
      reflexivity.
Qed.


Lemma expOrd_mul a b c :
  expOrd a (b * c) ≈ expOrd (expOrd a b) c.
Proof.
  revert a b; induction c as [C h]; intros.
  rewrite mulOrd_unfold.
  rewrite (expOrd_unfold (expOrd a b)).
  split.
  - rewrite expOrd_unfold.
    apply lub_least; auto with ord.
    { apply lub_le1. }
    apply sup_least; intros [i q].
    rewrite <- lub_le2.
    simpl.
    rewrite <- (sup_le _ _ i).
    rewrite <- (H i).
    rewrite <- expOrd_add.
    unfold expOrd at 2.
    rewrite foldOrd_unfold.
    rewrite <- lub_le2.
    rewrite <- (sup_le  _ _ q).
    reflexivity.
  - apply lub_least. { apply succ_least; apply expOrd_nonzero. }
    apply sup_least. intro i. 
    rewrite <- (H i).
    transitivity (expOrd a (b * h i + b)).
    rewrite expOrd_add. reflexivity.
    apply expOrd_monotone.
    rewrite <- (sup_le _ _ i).
    reflexivity.
Qed.

Definition powOmega (x:Ord) : Ord := expOrd ω x.

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


Fixpoint KnuthUp (n:nat) (a:Ord) : Ord -> Ord :=
  match n with
  | O    => fun b => b * a
  | S n' => foldOrd 1 (KnuthUp n' a)
  end.

Lemma KnuthUp_zero a b : KnuthUp 0%nat a b ≈ b * a.
Proof. reflexivity. Qed.

Lemma KnuthUp_succ n a b : KnuthUp (S n) a b ≈ foldOrd 1 (KnuthUp n a) b.
Proof. reflexivity. Qed.

Lemma KnuthUp_one a b : KnuthUp 1%nat a b ≈ expOrd a b.
Proof. reflexivity. Qed.
