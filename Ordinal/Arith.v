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
  destruct x as [A f]; simpl; auto with ord.
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
      destruct x; simpl; auto with ord.
    + apply sup_least. intro.
      apply ord_le_refl.
  - rewrite succ_unfold. simpl foldOrd.
    rewrite <- lub_le2.
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
      destruct (f a0); simpl; auto with ord.
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

Lemma addOrd_unfold (x y:Ord) : x + y = x ⊔ supOrd (fun i => succOrd (x + y i)).
Proof.
  destruct y; reflexivity.
Qed.

Lemma addOrd_succ (x y:Ord) : x + succOrd y ≈ succOrd (x + y).
Proof.
  unfold addOrd. apply foldOrd_succ.
  intros; auto with ord.
Qed.

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
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ b).
  apply succ_trans.
  apply Hy.
Qed.

Lemma addOrd_zero_r x : x + 0 ≈ x.
Proof.
  split; simpl; auto with ord.
  apply lub_least; auto with ord.
  apply sup_least. intros [].
Qed.

Lemma addOrd_zero_l x : 0 + x ≈ x.
Proof.
  induction x as  [X f Hx].
  split; simpl.
  - apply lub_least; auto with ord.
    apply sup_least; intro i.
    apply succ_least.
    rewrite Hx.
    apply (index_lt (ord X f)).
  - rewrite ord_le_unfold.
    simpl; intro x.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ x).
    apply succ_trans.
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
    + unfold addOrd at 1.
      rewrite foldOrd_unfold at 1.
      apply lub_least.
      rewrite <- lub_le1.
      apply addOrd_le1.
      apply sup_least.
      rewrite sup_unfold. simpl.
      intros [??]. simpl.
      apply succ_least.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ x).
      apply succ_trans.
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
      apply succ_trans.
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

Lemma onePlus_succ x : 1 + x ≤ succOrd x.
Proof.
  induction x as [X f Hx].
  rewrite addOrd_unfold. simpl.
  apply lub_least. apply succOrd_le_mor. auto with ord.
  apply sup_least; intro i.
  apply succOrd_le_mor.
  rewrite Hx.
  apply succ_least. apply (index_lt (ord X f) i).
Qed.

Lemma limit_onePlus x : limitOrdinal x -> 1 + x ≤ x.
Proof.
  destruct x as [X f]; simpl; intros [??].
  apply lub_least.
  apply succ_least.
  destruct H as [x]. rewrite ord_lt_unfold. exists x. auto with ord.
  apply sup_least; intro x.
  apply succ_least. simpl.
  hnf in H0.
  destruct (H0 x) as [y Hy].
  apply ord_le_lt_trans with (f y).
  transitivity (succOrd (f x)).
  apply onePlus_succ.
  apply succ_least. auto.
  apply (index_lt (ord X f) y).
Qed.

Lemma natOrdSize_add n m :
  natOrdSize (n+m)%nat ≈ natOrdSize m + natOrdSize n.
Proof.
  induction n; simpl natOrdSize.
  - symmetry. apply addOrd_zero_r.
  - rewrite addOrd_succ.
    rewrite IHn. reflexivity.
Qed.

Lemma limitOrdinal_intro : forall x,
    x > 0 ->
    (forall i, i < x -> exists j, i < j /\ j < x) ->
    limitOrdinal x.
Proof.
  destruct x as [X f]; intros.
  simpl; split.
  - rewrite ord_lt_unfold in H. destruct H as [i _].
    exact (inhabits i).
  - hnf. intros.
    destruct (H0 (f a)) as [b [??]].
    apply (index_lt (ord X f) a).
    rewrite ord_lt_unfold in H2.
    destruct H2 as [k ?].
    exists k.
    apply ord_lt_le_trans with b; auto.
Qed.

Lemma successor_add x y :
  successorOrdinal y -> successorOrdinal (x + y).
Proof.
  rewrite ord_isSucc.
  intros [o Ho].
  rewrite ord_isSucc.
  exists (x + o).
  rewrite Ho.
  apply addOrd_succ.
Qed.

Lemma limit_add x y :
  limitOrdinal y -> limitOrdinal (x + y).
Proof.
  intros.
  destruct y as [Y f]; simpl in *; intuition.
  apply limitOrdinal_intro.
  destruct H0 as [y].
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ y).
  apply succ_trans. auto with ord.
  intros.
  apply lub_lt in H.
  destruct H.
  exists x.
  split; auto.
  destruct H0 as [y].
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ y).
  apply succ_trans. apply addOrd_le1.
  apply sup_lt in H.
  destruct H as [y H].
  destruct (H1 y) as [y' H2].
  exists (x + f y').
  split.
  eapply ord_lt_le_trans; [ apply H |].
  apply succ_least.
  apply addOrd_increasing.
  auto.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ y').
  apply succ_trans.
  reflexivity.
Qed.


Lemma foldOrd_add z s a b :
  (forall x y, x ≤ y -> s x ≤ s y) ->
  foldOrd z s (a + b) ≈ foldOrd (foldOrd z s a) s b.
Proof.
  intros.
  induction b as [B g]. simpl.
  rewrite lub_continuous.
  split.
  apply lub_least.
  apply lub_le1.
  transitivity (foldOrd z s (limOrd (fun i => a + g i))).
  apply foldOrd_monotone; auto; apply sup_succ_lim.
  simpl.
  apply lub_least.
  rewrite <- lub_le1.
  apply foldOrd_above_z.
  apply sup_least; intro i.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ i).
  apply H.
  apply H0.
  apply lub_least; auto with ord.
  apply sup_least; intro i.
  rewrite <- lub_le2.
  transitivity (foldOrd z s (succOrd (a + g i))).
  simpl.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ tt).
  apply H.
  apply H0.
  apply foldOrd_monotone; auto.
  rewrite <- (sup_le _ _ i); auto with ord.
  intros; apply foldOrd_monotone; auto.
  apply foldOrd_strongly_continuous.
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
  apply lub_least.
  - simpl.
    rewrite <- lub_le1.
    apply Hy. auto.
  - simpl.
    rewrite <- lub_le2.
    apply sup_ord_le_morphism. intro i.
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
  split; simpl mulOrd.
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
  - simpl.
    rewrite <- (sup_le _ _ tt); auto with ord.
Qed.

Lemma mulOrd_one_r : forall x, mulOrd x 1 ≈ x.
Proof.
  intro.
  rewrite mulOrd_succ.
  rewrite mulOrd_zero_r.
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
    rewrite addOrd_unfold; simpl.
    apply lub_least.
    + rewrite H. apply (index_le (ord X f)).
    + apply sup_least; intro.
      apply succ_least.
      rewrite ord_lt_unfold. exists i.
      apply lub_least.
      apply H.
      apply sup_least; intros [].
  - rewrite ord_le_unfold; intro i.
    rewrite <- (sup_le _ _ i); simpl.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ tt).
    apply succ_trans.
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
  rewrite <- lub_le2. simpl.
  rewrite <- (sup_le _ _ a).
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
      rewrite <- (addOrd_zero_l 0).
      apply addOrd_monotone; auto.
      rewrite H.
      rewrite mulOrd_zero_l.
      reflexivity.
    + destruct Hy2 as [[y]|Hy2].
      * left. exists y.
        apply ord_lt_le_trans with x; auto.
        rewrite <- (addOrd_zero_l x) at 1.
        apply addOrd_monotone; auto with ord.
      * right. intro y. elim Hy2. exact (inhabits y).
Qed.


Lemma ordDistrib_left a b c :
  a * (b + c) ≈ (a * b) + (a * c).
Proof.
  induction c as [C h].
  split.
  - rewrite addOrd_unfold.
    rewrite mulOrd_lub.
    apply lub_least.
    + apply addOrd_le1.
    + rewrite mulOrd_unfold.
      apply sup_least.
      intros [??]. unfold boundedSup.
      rewrite (H x).
      rewrite <- addOrd_assoc.
      apply addOrd_monotone; auto with ord.
      rewrite (mulOrd_unfold a (ord C h)).
      rewrite <- (sup_le _ _ x).
      apply addOrd_monotone; auto with ord.
  - rewrite addOrd_unfold.
    apply lub_least.
    + rewrite addOrd_unfold.
      rewrite mulOrd_lub.
      apply lub_le1.
    + rewrite mulOrd_unfold.
      simpl.
      rewrite (sup_unfold C (fun i => a * h i + a)). simpl.
      apply sup_least; intros [??]. simpl.
      apply succ_least.
      apply ord_lt_le_trans with (a * b + (a * h x + a)).
      apply addOrd_increasing.
      apply index_lt.
      rewrite addOrd_assoc.
      rewrite mulOrd_lub.
      rewrite <- lub_le2.
      rewrite (mulOrd_unfold a (supOrd _ )).
      rewrite (sup_unfold C (fun i => succOrd (b + h i))). simpl.
      rewrite <- (sup_le _ _ (existT _ x tt)). simpl.
      rewrite (H x).
      reflexivity.
Qed.

Lemma mulOrd_assoc a b c :
  a * (b * c) ≈ a * b * c.
Proof.
  induction c as [C h]; simpl.
  split.
  - apply sup_least. intros [??]. simpl.
    fold mulOrd.
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
    rewrite (mulOrd_unfold a (supOrd _)). simpl.
    rewrite (sup_unfold C (fun i => b * h i + b)). simpl.
    rewrite <- (sup_le _ _ (existT _ x i)). simpl.
    reflexivity.
Qed.

Lemma natOrdSize_mul n m :
  natOrdSize (n*m)%nat ≈ natOrdSize m * natOrdSize n.
Proof.
  induction n; simpl natOrdSize.
  - rewrite mulOrd_zero_r; reflexivity.
  - rewrite mulOrd_succ.
    rewrite natOrdSize_add.
    rewrite IHn.
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
    + rewrite mulOrd_lub.
      rewrite <- lub_le1.
      rewrite mulOrd_one_r.
      reflexivity.
    + rewrite expOrd_unfold at 1.
      apply lub_least.
      * rewrite mulOrd_lub.
        rewrite <- lub_le1.
        rewrite mulOrd_one_r.
        apply succ_least.
        apply expOrd_nonzero.
      * apply sup_least; simpl.
        intros [??]. simpl.
        rewrite (H x).
        rewrite <- mulOrd_assoc.
        rewrite mulOrd_unfold.
        apply sup_least. simpl; intro i.
        rewrite mulOrd_lub.
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ x).
        rewrite (mulOrd_unfold _ (expOrd a (h x) * a)).
        rewrite <- (sup_le _ _ i).
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
    apply sup_least; intros [i q].
    rewrite <- lub_le2.
    etransitivity; [ | apply (sup_le _ _ i) ]. simpl.
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

(** * The Knuth up-arrow functions, adapted to ordinals.

    The up-arrow functions continue the pattern established above:
    multiplication is defined via transfinite iteration of addition,
    exponentation is defined via transfinite iteration of multiplication, etc.
    
    However, the later functions in the the sequence (@KnuthUp 2@ and above)
    are rather less interesting. They saturate at @ω@ and fail to be increasing.
    This limits their applicability for constructing larger ordinals, even though
    they are a rapidly increasing sequence of functions on finite ordinals AKA
    the natural numbers.
*)

Fixpoint KnuthUp (n:nat) (a:Ord) : Ord -> Ord :=
  match n with
  | O    => fun b => b * a
  | S n' => foldOrd 1 (KnuthUp n' a)
  end.

Lemma KnuthUp_zero : KnuthUp 0%nat = fun a b => b * a.
Proof. reflexivity. Qed.

Lemma KnuthUp_succ n : KnuthUp (S n) = fun a => foldOrd 1 (KnuthUp n a).
Proof. reflexivity. Qed.

Lemma KnuthUp_one : KnuthUp 1%nat = expOrd.
Proof. reflexivity. Qed.

Lemma KnuthUp_two : KnuthUp 2%nat = fun a => foldOrd 1 (expOrd a).
Proof. reflexivity. Qed.

Lemma KnuthUp_monotone n : forall a b c d,
  a ≤ b ->
  c ≤ d ->
  KnuthUp n a c ≤ KnuthUp n b d.
Proof.
  induction n; simpl; intros.
  transitivity (c*b).
  apply mulOrd_monotone2; auto.
  apply mulOrd_monotone1; auto.
  transitivity (foldOrd 1 (KnuthUp n b) c).
  apply foldOrd_least.
  apply foldOrd_above_z.
  intros; apply IHn; auto with ord.
  intros.
  destruct x as [X f].
  simpl.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ i).
  apply IHn; auto with ord.
  apply foldOrd_monotone; auto.
  intros; apply IHn; auto with ord.
Qed.

Lemma KnuthUp_continuous n : forall a,
  (n > 0)%nat ->
  strongly_continuous (KnuthUp n a).
Proof.
  intros. inversion H; subst; apply foldOrd_strongly_continuous.
Qed.

Lemma KnuthUp_one_eq n : forall a,
  0 < a ->
  KnuthUp n a 1 ≈ a.
Proof.
  induction n; simpl KnuthUp.
  - intros. rewrite mulOrd_one_l. reflexivity.
  - intros. split.
    apply lub_least.
    apply succ_least; auto.
    apply sup_least; intros.
    destruct n; simpl KnuthUp.
    transitivity (1 * a).
    apply mulOrd_monotone1.
    apply lub_least; auto with ord.
    apply sup_least. intros [].
    rewrite mulOrd_one_l. auto with ord.
    rewrite lub_continuous.
    apply lub_least.
    apply IHn. auto.
    rewrite sup_unfold.
    simpl.
    apply lub_least.
    apply succ_least; auto.
    apply sup_least; intros [[] _].
    intros.
    apply foldOrd_monotone; auto.
    intros; apply KnuthUp_monotone; auto with ord.
    apply foldOrd_strongly_continuous.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ tt).
    rewrite <- IHn at 1; auto.
    apply KnuthUp_monotone; auto with ord.
Qed.


Lemma KnuthUp_omega_fix : forall n a,
    (n > 0)%nat ->
    0 < a ->
    KnuthUp n a (KnuthUp (S n) a ω) ≈ KnuthUp (S n) a ω.
Proof.
  split.
  - intros.
    rewrite KnuthUp_succ.
    intros.
    transitivity (KnuthUp n a (supOrd (fun (i:ω) => foldOrd 1 (KnuthUp n a) i))).
    apply KnuthUp_monotone; auto with ord.
    simpl.
    apply lub_least.
    rewrite <- (sup_le _ _ 0%nat).
    apply foldOrd_above_z.
    apply sup_least; intro i.
    rewrite <- (sup_le _ _ (S i)).
    simpl.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ tt).
    reflexivity.
    transitivity (supOrd (fun (i:ω) => KnuthUp n a (foldOrd 1 (KnuthUp n a) (sz i)))).
    apply KnuthUp_continuous; auto.
    apply sup_least; intro i.
    simpl.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    reflexivity.
  - simpl.
    apply lub_least.
    inversion H; simpl; apply foldOrd_above_z.
    apply sup_least; intro i.
    apply KnuthUp_monotone; auto with ord.
    induction i; simpl.
    apply lub_least; auto with ord.
    apply sup_least; intros [].
    apply lub_least; auto with ord.
    apply sup_least; intros [].
    rewrite <- lub_le2.
    rewrite <- (sup_le  _ _ i).
    apply KnuthUp_monotone; auto with ord.
Qed.

Theorem KnuthUp_saturates : forall n a b,
    (n > 0)%nat ->
    0 < a ->
    KnuthUp (S n) a b ≤ KnuthUp (S n) a ω.
Proof.
  intros.
  induction b as [B g]; intros.
  rewrite <- KnuthUp_omega_fix; auto.
  rewrite KnuthUp_succ.
  simpl foldOrd at 1.
  apply lub_least.
  inversion H; simpl; apply foldOrd_above_z.
  apply sup_least; intro i.
  apply KnuthUp_monotone; auto with ord.
  apply H1; auto.
Qed.

Theorem KnuthUp_not_increasing : forall n,
    (n > 1)%nat ->
    (forall a b c, b < c -> KnuthUp n a b < KnuthUp n a c) -> False.
Proof.
  intros.
  apply (ord_lt_irreflexive (KnuthUp n ω (succOrd ω))).
  apply ord_le_lt_trans with (KnuthUp n ω ω).
  destruct n. inversion H.
  apply KnuthUp_saturates; auto.
  inversion H; auto with arith.
  apply (index_lt _ 0%nat).
  apply H0.
  apply succ_lt.
Qed.

Theorem KnuthUp2_epsilon_number : forall a,
    a ≥ ω ->
    KnuthUp 2%nat a ω ≈ expOrd ω (KnuthUp 2%nat a ω).
Proof.
  intros. split.
  - apply increasing_inflationary; auto.
    intros; apply expOrd_increasing; auto.
    apply omega_gt1.
  - rewrite <- KnuthUp_omega_fix at 2; auto.
    rewrite KnuthUp_one.
    apply expOrd_monotone_base; auto.
    rewrite <- H. apply (index_lt _ 0%nat).
Qed.


Global Opaque addOrd mulOrd expOrd.


(** Misc. facts about the addition of finite ordinals *)

Lemma add_cancel_finite (n:ω) x y :
  x + sz n ≈ y + sz n -> x ≈ y.
Proof.
  induction n; simpl; intro H.
  do 2 rewrite addOrd_zero_r in H; auto.
  do 2 rewrite addOrd_succ in H.
  apply succ_cancel_eq in H.
  auto.
Qed.

Lemma onePlus_finite_succ m :
  1 + natOrdSize m ≈ succOrd (natOrdSize m).
Proof.
  induction m; simpl.
  rewrite addOrd_zero_r. auto with ord.
  rewrite addOrd_succ.
  rewrite IHm.
  reflexivity.
Qed.
