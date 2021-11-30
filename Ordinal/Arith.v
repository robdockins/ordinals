Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.

(** * Definitions by transfinite recursion.
  *)
Definition foldOrd (z:Ord) (s:Ord -> Ord) : Ord -> Ord :=
  fix foldOrd (x:Ord) : Ord :=
    match x with
    | ord A f => z ⊔ supOrd (fun i => s (foldOrd (f i)))
    end.

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
    apply ord_le_trans with (s (q (f a))).
    apply Hmono. auto.
    apply (Hsq (ord A f)).
Qed.

Lemma foldOrd_unfold z s (x:Ord) i :
  s (foldOrd z s (x i)) ≤ foldOrd z s x.
Proof.
  destruct x as [A f]. simpl.
  eapply ord_le_trans; [ | apply lub_le2 ].
  eapply ord_le_trans; [ | apply (sup_le _ _ i)]. simpl.
  apply ord_le_refl.
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
    rewrite <- (foldOrd_unfold z s y b).
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
    apply foldOrd_unfold.
Qed.

Lemma foldOrd_complete z s :
  complete z ->
  (forall x, 0 < s x) ->
  z <= s z ->
  (forall x y, x <= y -> s x <= s y) ->
  (forall o, complete o -> complete (s o)) ->
  forall x, complete x -> complete (foldOrd z s x).
Proof.
  intros Hz Hs0 Hs1 Hs2 Hs3.
  induction x as [X f Hx].
  simpl; intros [Hx1 [Hx2 Hx3]].
  destruct z as [Z h]; simpl in *.
  destruct  Hz as [Hz1 [Hz2 Hz3]].
  repeat split.
  - intros [z1|x1] [z2|x2].
    + destruct (Hz1 z1 z2) as [z' [??]].
      exists (inl z'). split; auto.
    + destruct x2 as [x2 q1]. simpl.
      assert (ord Z h <= s (foldOrd (ord Z h) s (f x2))).
      { etransitivity. apply Hs1.
        apply Hs2. apply foldOrd_above_z.
      }
      destruct (ord_le_subord (ord Z h) (s (foldOrd (ord Z h) s (f x2))) H z1) as [q2 Hq2].
      destruct (complete_directed _ (Hs3 _ (Hx _ (Hx3 _))) q1 q2) as [q' [Hq'1 Hq'2]].
      exists (inr (existT _ x2 q')); simpl.
      split.
      * etransitivity; [ apply Hq2 | apply Hq'2 ].
      * apply Hq'1.
    + destruct x1 as [x1 q1]. simpl.
      assert (ord Z h <= s (foldOrd (ord Z h) s (f x1))).
      { etransitivity. apply Hs1.
        apply Hs2. apply foldOrd_above_z.
      }
      destruct (ord_le_subord (ord Z h) (s (foldOrd (ord Z h) s (f x1))) H z2) as [q2 Hq2].
      destruct (complete_directed _ (Hs3 _ (Hx _ (Hx3 _))) q1 q2) as [q' [Hq'1 Hq'2]].
      exists (inr (existT _ x1 q')); simpl.
      split.
      * apply Hq'1.
      * etransitivity; [ apply Hq2 | apply Hq'2 ].
    + destruct x1 as [x1 q1].
      destruct x2 as [x2 q2].
      simpl.
      destruct (Hx1 x1 x2) as [x' [Hx'1 Hx'2]].
      assert (Hsx1 : s (foldOrd (ord Z h) s (f x1)) <= s (foldOrd (ord Z h) s (f x'))).
      { apply Hs2. apply foldOrd_monotone; auto. }
      assert (Hsx2 : s (foldOrd (ord Z h) s (f x2)) <= s (foldOrd (ord Z h) s (f x'))).
      { apply Hs2. apply foldOrd_monotone; auto. }
      generalize Hsx1 Hsx2.
      do 2 rewrite ord_le_unfold.
      intros Hq1. specialize (Hq1 q1). rewrite ord_lt_unfold in Hq1.
      destruct Hq1 as [q1' Hq1].
      intros Hq2. specialize (Hq2 q2). rewrite ord_lt_unfold in Hq2.
      destruct Hq2 as [q2' Hq2].
      destruct (complete_directed _ (Hs3 _ (Hx _ (Hx3 _))) q1' q2') as [q' [Hq'1 Hq'2]].
      exists (inr (existT _ x' q')); simpl.
      split.
      * etransitivity; [ apply Hq1 | apply Hq'1 ].
      * etransitivity; [ apply Hq2 | apply Hq'2 ].

  - destruct Hz2 as [[z]|Hz2].
    + left. exact (inhabits (inl z)).
    + destruct Hx2 as [[x]|Hx2].
      * assert (zeroOrd < s (foldOrd (ord Z h) s (f x))).
        apply Hs0.
        rewrite ord_lt_unfold in H.
        destruct H as [q Hq].
        left.
        exact (inhabits (inr (existT _ x q))).
      * right. intros [[z|[x ?]]].
        ** apply Hz2. exact (inhabits z).
        ** apply Hx2. exact (inhabits x).
  - intros [z | [x q]]; simpl; auto.
    assert (Hc : complete (s (foldOrd (ord Z h) s (f x)))).
    { apply Hs3. apply Hx. apply Hx3. }
    destruct (s (foldOrd (ord Z h) s (f x))); destruct Hc as [Hc1 [Hc2 Hc3]].
    apply Hc3.
Qed.

(** The "natural" ordinal addition function as defined by Hessenberg.
  * This ordinal operation is commutative, associative and absorbs zero.
  * It is also strictly monotone in both of its arguments.
  *
  * Morover, it is the smallest binary operation on ordinals which is strictly monotone
  * in both of its arguments.
  *)
Fixpoint addOrd (x:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match x, y with
    | ord A f, ord B g =>
      ord (A+B) (fun ab =>
                 match ab with
                 | inl a => addOrd (f a) y
                 | inr b => inner (g b)
                 end
                )
    end.

Notation "a ⊕ b" := (addOrd a b) (at level 45, right associativity) : ord_scope.

Lemma addOrd_unfold (x y:Ord) :
  x ⊕ y =
    (limOrd (fun a:x => x a ⊕ y))
    ⊔
    (limOrd (fun b:y => x ⊕ y b)).
Proof.
  destruct x; destruct y; auto.
Qed.

Global Opaque addOrd.

Lemma addOrd_le1 x y : x ≤ x ⊕ y.
Proof.
  induction x as [A f Hx].
  destruct y as [B g].
  rewrite addOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite ord_lt_unfold.
  simpl.
  exists (inl a).
  auto.
Qed.

Lemma addOrd_le2 x y : y ≤ x ⊕ y.
Proof.
  induction y as [A f Hx].
  destruct x as [B g].
  rewrite addOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite ord_lt_unfold.
  exists (inr a).
  apply Hx.
Qed.

Lemma addOrd_zero x : x ≈ x ⊕ 0.
Proof.
  split.
  - induction x as [A f].
    rewrite addOrd_unfold.
    simpl.
    rewrite ord_le_unfold; simpl; intros.
    rewrite ord_lt_unfold.
    exists (inl a).
    apply H.
  - induction x as [A f].
    rewrite addOrd_unfold.
    rewrite ord_le_unfold; simpl; intros.
    destruct a; intuition.
    rewrite ord_lt_unfold.
    exists a.
    auto.
Qed.

Lemma addOrd_comm_le x y : x ⊕ y ≤ y ⊕ x.
Proof.
  revert y.
  induction x as [A f Hx].
  intro y. revert A f Hx.
  induction y as [B g Hy]; intros.
  rewrite ord_le_unfold. rewrite addOrd_unfold.
  simpl; intros.
  destruct a.
  - rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    simpl.
    exists (inr a); auto.
  - rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    exists (inl b).
    apply Hy. auto.
Qed.

Lemma addOrd_comm x y : x ⊕ y ≈ y ⊕ x.
Proof.
  split; apply addOrd_comm_le; auto.
Qed.

Lemma addOrd_assoc1 : forall x y z,  x ⊕ (y ⊕ z) ≤ (x ⊕ y) ⊕ z.
Proof.
  induction x as [A f]. induction y as [B g]. induction z as [C h].
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl.
  intros.
  rewrite ord_lt_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl in *.
  destruct a as [a|[b|c]].
  - exists (inl (inl a)).
    generalize (H a (ord B g) (ord C h)).
    rewrite (addOrd_unfold (ord B g) (ord C h)); simpl; auto.
  - exists (inl (inr b)).
    apply H0.
  - exists (inr c).
    apply H1.
Qed.

Lemma addOrd_assoc2 : forall x y z, (x ⊕ y) ⊕ z ≤ x ⊕ (y ⊕ z).
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl; intros.
  rewrite ord_lt_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl.
  destruct a as [[a|b]|c].
  - exists (inl a).
    apply H.
  - exists (inr (inl b)).
    apply H0.
  - exists (inr (inr c)).
    apply H1.
Qed.

Lemma addOrd_assoc : forall x y z,  x ⊕ (y ⊕ z) ≈ (x ⊕ y) ⊕ z.
Proof.
  intros; split.
  apply addOrd_assoc1.
  apply addOrd_assoc2.
Qed.

Lemma addOrd_cancel :
  forall x y z, addOrd x z < addOrd y z -> x < y.
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  rewrite ord_lt_unfold.
  rewrite addOrd_unfold.
  rewrite ord_lt_unfold.
  simpl.
  intros [[b|c] ?].
  - exists b.
    rewrite ord_le_unfold. intros.
    rewrite ord_le_unfold in H2.
    rewrite addOrd_unfold in H2.
    specialize (H2 (inl a)).
    simpl in H2.
    eapply H. apply H2.
  - rewrite ord_le_unfold in H2.
    rewrite addOrd_unfold in H2.
    specialize (H2 (inr c)).
    simpl in H2.
    apply H1 in H2.
    rewrite ord_lt_unfold in H2.
    auto.
Qed.

Lemma addOrd_monotone :
  forall x y z1 z2, x ≤ y -> z1 ≤ z2 -> x ⊕ z1 ≤ y ⊕ z2.
Proof.
  induction x as [A f]. destruct y as [B g]. induction z1 as [C h]. destruct z2.
  intros.
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  simpl.
  intros [a|c].
  - rewrite ord_le_unfold in H1.
    specialize (H1 a).
    rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    simpl.
    rewrite ord_lt_unfold in H1.
    destruct H1 as [b Hb].
    exists (inl b).
    apply H; auto.
  - rewrite ord_le_unfold in H2.
    specialize (H2 c).
    rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    rewrite ord_lt_unfold in H2.
    simpl.
    destruct H2 as [a Ha].
    exists (inr a).
    apply H0; auto.
Qed.

Lemma addOrd_increasing_both :
  forall x y z1 z2, (x < y -> z1 ≤ z2 -> x ⊕ z1 < y ⊕ z2) /\
                    (x ≤ y -> z1 < z2 -> x ⊕ z1 < y ⊕ z2).
Proof.
  induction x as [A f Hx].
  induction y as [B g Hy].
  induction z1 as [C h Hz1].
  destruct z2 as [D i].
  split; intros.
  - rewrite ord_lt_unfold in H.
    destruct H as [a Ha].
    rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    simpl.
    exists (inl a).
    rewrite ord_le_unfold.
    rewrite addOrd_unfold.
    simpl.
    intros.
    destruct a0.
    + rewrite ord_le_unfold in Ha; auto.
      destruct (Hx a0 (g a) (ord C h) (ord D i)); auto.
    + rewrite ord_le_unfold in H0.
      specialize (H0 c).
      apply Hy; auto.
  - rewrite ord_lt_unfold in H0.
    destruct H0 as [q Hq].
    rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    simpl.
    exists (inr q).
    rewrite ord_le_unfold.
    rewrite addOrd_unfold.
    simpl.
    intros.
    destruct a as [a|c].
    + rewrite ord_le_unfold in H.
      specialize (H a).
      destruct (Hx a (ord B g) (ord C h) (i q)).
      auto.
    + rewrite ord_le_unfold in Hq.
      specialize (Hq c).
      destruct (Hz1 c (i q)).
      auto.
Qed.

Lemma addOrd_increasing1 :
  forall x y z, x < y -> x ⊕ z < y ⊕ z.
Proof.
  intros.
  destruct (addOrd_increasing_both x y z z).
  apply H0; auto.
  apply ord_le_refl.
Qed.

Lemma addOrd_increasing2 :
  forall x y z, x < y -> z ⊕ x < z ⊕ y.
Proof.
  intros.
  destruct (addOrd_increasing_both z z x y).
  apply H1; auto.
  apply ord_le_refl.
Qed.

Lemma addOrd_least (f:Ord -> Ord -> Ord)
  (Hmono1 : forall a b c, a < b -> f a c < f b c)
  (Hmono2 : forall a b c, a < b -> f c a < f c b)
  :
  (forall x y, x ⊕ y ≤ f x y).
Proof.
  induction x as [A fa].
  induction y as [B g].
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  simpl.
  intros [a|b].
  - eapply ord_le_lt_trans; [ apply H | auto with ord ].
  - eapply ord_le_lt_trans; [ apply H0 | auto with ord ].
Qed.

Lemma addOrd_succ x y : succOrd x ⊕ y ≈ succOrd (x ⊕ y).
Proof.
  split.
  - induction y as [B g Hy].
    rewrite ord_le_unfold.
    rewrite addOrd_unfold.
    simpl.
    intro ua.
    rewrite ord_lt_unfold. simpl.
    exists tt.
    destruct ua as [u|a].
    + apply ord_le_refl.
    + rewrite Hy.
      apply succ_least.
      apply addOrd_increasing2; auto with ord.
  - apply succ_least.
    apply addOrd_increasing1.
    apply succ_lt.
Qed.

Lemma addOrd_succ2 x y : x ⊕ succOrd y ≈ succOrd (x ⊕ y).
Proof.
  rewrite addOrd_comm.
  rewrite addOrd_succ.
  rewrite addOrd_comm.
  reflexivity.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_le ++> ord_le ++> ord_le as addOrd_le_mor.
Proof.
  intros. apply addOrd_monotone; auto.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_lt ++> ord_le ++> ord_lt as addOrd_lt_mor1.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply addOrd_increasing1; eauto.
  apply addOrd_monotone; auto.
  reflexivity.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_le ++> ord_lt ++> ord_lt as addOrd_lt_mor2.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply addOrd_increasing2; eauto.
  apply addOrd_monotone; auto.
  reflexivity.
Qed.

Add Parametric Morphism : addOrd with signature
   ord_eq ==> ord_eq ==> ord_eq as addOrd_eq_mor.
Proof.
  intros; split; apply addOrd_le_mor; solve [apply H|apply H0].
Qed.


(** * An ordinal multiplication *)

Fixpoint mulOrd (x:Ord) (y:Ord) : Ord :=
    match y with
    | ord B g => supOrd (fun b:B => mulOrd x (g b) ⊕ x)
    end.

Notation "x ⊗ y" := (mulOrd x y) (at level 43, right associativity) : ord_scope.

Lemma mulOrd_unfold (x:Ord) (y:Ord) :
  x ⊗ y =
  supOrd (fun i:y => x ⊗ (y i) ⊕ x).
Proof.
  destruct y; auto.
Qed.

Lemma mulOrd_monotone1 : forall z x y, x ≤ y -> x ⊗ z ≤ y ⊗ z.
Proof.
  induction z as [C h Hz].
  simpl; intros.
  apply sup_least. intro c. simpl.
  rewrite <- (sup_le _ _ c).
  apply addOrd_monotone; auto.
Qed.

Lemma mulOrd_monotone2 : forall y x z, y ≤ z -> x ⊗ y ≤ x ⊗ z.
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
  apply addOrd_monotone; auto.
  apply ord_le_refl.
Qed.

Lemma mulOrd_increasing2 : forall x y z,
    zeroOrd < x ->
    y < z ->
    x ⊗ y < x ⊗ z.
Proof.
  intros x y [C h] Hx H.
  rewrite (mulOrd_unfold x (ord C h)).
  simpl.
  rewrite ord_lt_unfold in H.
  destruct H as [c Hc]. simpl in Hc.
  rewrite <- (sup_le _ _ c).
  apply ord_le_lt_trans with (mulOrd x (h c)); [ apply mulOrd_monotone2 ; assumption | ].
  apply ord_le_lt_trans with (addOrd (mulOrd x (h c)) zeroOrd).
  - apply addOrd_zero.
  - apply addOrd_increasing2. auto.
Qed.

Lemma mulOrd_zero : forall x, x ⊗ zeroOrd ≈ zeroOrd.
Proof.
  intros; split.
  - destruct x as [A f]. simpl.
    apply sup_least. intuition.
  - apply zero_least.
Qed.

Lemma mulOrd_succ : forall x y, x ⊗ (succOrd y) ≈ (x ⊗ y) ⊕ x.
Proof.
  intros; split; simpl.
  - apply sup_least; auto with ord.
  - rewrite <- (sup_le _ _ tt); auto with ord.
Qed.

Lemma mulOrd_one : forall x, mulOrd x oneOrd ≈ x.
Proof.
  intro.
  unfold oneOrd.
  rewrite mulOrd_succ.
  rewrite mulOrd_zero.
  rewrite addOrd_comm.
  rewrite <- addOrd_zero.
  reflexivity.
Qed.

Lemma mulOrd_positive : forall x y,
    zeroOrd < x ->
    zeroOrd < y ->
    zeroOrd < x ⊗ y.
Proof.
  intros.
  destruct x as [A f].
  destruct y as [B g].
  simpl.
  rewrite ord_lt_unfold in H.
  rewrite ord_lt_unfold in H0.
  destruct H as [a _].
  destruct H0 as [b _].
  simpl in *.
  rewrite <- (sup_le _ _ b).
  rewrite addOrd_unfold.
  rewrite <- lub_le2.
  rewrite ord_lt_unfold. exists a.
  apply zero_least.
Qed.

Lemma mulOrd_limit : forall x y,
    limitOrdinal y ->
    x ⊗ y ≈ supOrd (fun b:y => x ⊗ (y b)).
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

Add Parametric Morphism : mulOrd with signature
    ord_le ++> ord_le ++> ord_le as mulOrd_le_mor.
Proof.
  intros.
  apply ord_le_trans with (x ⊗ y0).
  apply mulOrd_monotone2; auto.
  apply mulOrd_monotone1; auto.
Qed.

Add Parametric Morphism : mulOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as mulOrd_eq_mor.
Proof.
  unfold ord_eq; intuition; apply mulOrd_le_mor; auto.
Qed.


(** * An ordinal exponentiation *)

Definition expOrd (x y:Ord) : Ord :=
  foldOrd oneOrd (fun a => a ⊗ x) y.

Lemma expOrd_nonzero x y : 0 < expOrd x y.
Proof.
  apply ord_lt_le_trans with oneOrd.
  apply succ_lt.
  apply foldOrd_above_z.
Qed.

Lemma expOrd_zero x : expOrd x 0 ≈ 1.
Proof.
  apply foldOrd_zero.
Qed.

Lemma expOrd_succ x y :
  zeroOrd < x ->
  expOrd x (succOrd y) ≈ (expOrd x y) ⊗ x.
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

Lemma expOrd_increasing a (Ha : oneOrd < a) :
  forall y x,
    x < y ->
    expOrd a x < expOrd a y.
Proof.
  intros.
  apply foldOrd_increasing; auto.
  - intros.
    rewrite mulOrd_unfold.
    rewrite ord_lt_unfold in Ha.
    destruct Ha as [q ?].
    rewrite ord_le_unfold in H1. specialize (H1 tt).
    rewrite ord_le_unfold in H0. specialize (H0 tt).
    simpl in *.
    eapply ord_lt_le_trans; [ | apply (sup_le _ _ q)]. simpl.
    apply ord_le_lt_trans with (addOrd zeroOrd a0).
    + eapply ord_le_trans; [ | apply addOrd_comm ].
      apply addOrd_zero.
    + apply addOrd_increasing1.
      apply mulOrd_positive; auto.
  - apply mulOrd_monotone1.
Qed.

Lemma expOrd_limit x y (Hx:oneOrd < x) :
  limitOrdinal y ->
  expOrd x y ≈ boundedSup y (expOrd x).
Proof.
  intros.
  apply foldOrd_limit; auto.
  apply mulOrd_monotone1.
Qed.

Lemma expOrd_continuous x (Hx:ord_lt oneOrd x) :
  strongly_continuous (expOrd x).
Proof.
  apply foldOrd_strongly_continuous; auto.
Qed.
