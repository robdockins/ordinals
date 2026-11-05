From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenCon.

From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import Classical.


Open Scope ord_scope.

(** The "natural" ordinal addition function as defined by Hessenberg.
  * This ordinal operation is commutative, associative and absorbs zero.
  * It is also strictly monotone in both of its arguments.
  *
  * Morover, it is the smallest binary operation on ordinals which is strictly monotone
  * in both of its arguments.
  *)
Fixpoint naddOrd (x:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match x, y with
    | ord A f, ord B g =>
      ord (A+B) (fun ab =>
                 match ab with
                 | inl a => naddOrd (f a) y
                 | inr b => inner (g b)
                 end
                )
    end.

Notation "a ⊕ b" := (naddOrd a b) (at level 45, right associativity) : ord_scope.

Lemma naddOrd_unfold (x y:Ord) :
  x ⊕ y =
    (limOrd (fun a:x => x a ⊕ y))
    ⊔
    (limOrd (fun b:y => x ⊕ y b)).
Proof.
  destruct x; destruct y; auto.
Qed.

Global Opaque naddOrd.

Lemma naddOrd_le1 x y : x ≤ x ⊕ y.
Proof.
  induction x as [A f Hx].
  destruct y as [B g].
  rewrite naddOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite <- lub_le1.
  eapply ord_le_lt_trans; [ | apply (limit_lt _ _ a) ].
  simpl; auto.
Qed.

Lemma naddOrd_le2 x y : y ≤ x ⊕ y.
Proof.
  induction y as [A f Hx].
  destruct x as [B g].
  rewrite naddOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite <- lub_le2.
  eapply ord_le_lt_trans; [ | apply (limit_lt _ _ a) ].
  simpl; auto.
Qed.

Lemma naddOrd_zero_r x : x ⊕ 0 ≈ x.
Proof.
  split.
  - induction x as [A f].
    rewrite naddOrd_unfold.
    apply lub_least.
    apply limit_least; intros.
    rewrite H. apply limit_lt.
    apply limit_least; intros [].
  - induction x as [A f].
    rewrite naddOrd_unfold.
    simpl.
    rewrite ord_le_unfold; simpl; intros.
    rewrite <- lub_le1.
    eapply ord_le_lt_trans; [ | apply (limit_lt _ _ a) ].
    simpl; apply H.
Qed.

Lemma naddOrd_comm_le x y : x ⊕ y ≤ y ⊕ x.
Proof.
  revert y.
  induction x as [A f Hx].
  intro y. revert A f Hx.
  induction y as [B g Hy]; intros.
  repeat rewrite naddOrd_unfold.
  apply lub_least; apply limit_least; intro; simpl.
  - rewrite (Hx i).
    rewrite <- lub_le2.
    eapply ord_le_lt_trans; [ | apply (limit_lt _ _ i)]. simpl.
    reflexivity.
  - rewrite Hy; auto.
    rewrite <- lub_le1.
    eapply ord_le_lt_trans; [ | apply (limit_lt _ _ i)]. simpl.
    reflexivity.
Qed.

Lemma naddOrd_comm x y : x ⊕ y ≈ y ⊕ x.
Proof.
  split; apply naddOrd_comm_le; auto.
Qed.

Lemma naddOrd_zero_l x: 0 ⊕ x ≈ x.
Proof.
  rewrite naddOrd_comm. apply naddOrd_zero_r.
Qed.

Lemma naddOrd_assoc1 : forall x y z,  x ⊕ (y ⊕ z) ≤ (x ⊕ y) ⊕ z.
Proof.
  induction x as [A f]. induction y as [B g]. induction z as [C h].
  repeat rewrite naddOrd_unfold.
  repeat rewrite lub_unfold. simpl.
  rewrite ord_le_unfold. simpl.
  intros.
  rewrite ord_lt_unfold.
  simpl in *.
  destruct a as [a|[b|c]].
  - exists (inl (inl a)).
    generalize (H a (ord B g) (ord C h)).
    rewrite (naddOrd_unfold (ord B g) (ord C h)); simpl; auto.
  - exists (inl (inr b)).
    apply H0.
  - exists (inr c).
    apply H1.
Qed.

Lemma naddOrd_assoc2 : forall x y z, (x ⊕ y) ⊕ z ≤ x ⊕ (y ⊕ z).
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  repeat rewrite naddOrd_unfold.
  repeat rewrite lub_unfold.
  rewrite ord_le_unfold.
  simpl; intros.
  rewrite ord_lt_unfold.
  simpl.
  destruct a as [[a|b]|c].
  - exists (inl a).
    apply H.
  - exists (inr (inl b)).
    apply H0.
  - exists (inr (inr c)).
    apply H1.
Qed.

Lemma naddOrd_assoc : forall x y z,  x ⊕ (y ⊕ z) ≈ (x ⊕ y) ⊕ z.
Proof.
  intros; split.
  apply naddOrd_assoc1.
  apply naddOrd_assoc2.
Qed.

Lemma naddOrd_cancel :
  forall x y z, naddOrd x z < naddOrd y z -> x < y.
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  rewrite ord_lt_unfold.
  rewrite naddOrd_unfold.
  rewrite ord_lt_unfold.
  simpl.
  intros [[b|c] ?].
  - exists b.
    rewrite ord_le_unfold. intros.
    rewrite ord_le_unfold in H2.
    rewrite naddOrd_unfold in H2.
    specialize (H2 (inl a)).
    simpl in H2.
    eapply H. apply H2.
  - rewrite ord_le_unfold in H2.
    rewrite naddOrd_unfold in H2.
    specialize (H2 (inr c)).
    simpl in H2.
    apply H1 in H2.
    rewrite ord_lt_unfold in H2.
    auto.
Qed.

Lemma naddOrd_monotone :
  forall x y z1 z2, x ≤ y -> z1 ≤ z2 -> x ⊕ z1 ≤ y ⊕ z2.
Proof.
  induction x as [A f]. destruct y as [B g]. induction z1 as [C h]. destruct z2.
  intros.
  rewrite ord_le_unfold.
  rewrite naddOrd_unfold.
  simpl.
  intros [a|c].
  - rewrite ord_le_unfold in H1.
    specialize (H1 a).
    rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    simpl.
    rewrite ord_lt_unfold in H1.
    destruct H1 as [b Hb].
    exists (inl b).
    apply H; auto.
  - rewrite ord_le_unfold in H2.
    specialize (H2 c).
    rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    rewrite ord_lt_unfold in H2.
    simpl.
    destruct H2 as [a Ha].
    exists (inr a).
    apply H0; auto.
Qed.

Lemma naddOrd_cancel_le :
  forall x y z, naddOrd x z <= naddOrd y z -> x <= y.
Proof.
  intros x y z.
  rewrite naddOrd_unfold.
  intro H.
  rewrite ord_le_unfold; intro i.
  apply naddOrd_cancel with z.
  rewrite <- H.
  rewrite <- lub_le1.
  rewrite ord_lt_unfold.
  exists i.
  simpl.
  auto with ord.
Qed.


Lemma naddOrd_increasing_both :
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
    rewrite naddOrd_unfold.
    simpl.
    exists (inl a).
    rewrite ord_le_unfold.
    rewrite naddOrd_unfold.
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
    rewrite naddOrd_unfold.
    simpl.
    exists (inr q).
    rewrite ord_le_unfold.
    rewrite naddOrd_unfold.
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

Lemma naddOrd_increasing1 :
  forall x y z, x < y -> x ⊕ z < y ⊕ z.
Proof.
  intros.
  destruct (naddOrd_increasing_both x y z z).
  apply H0; auto.
  apply ord_le_refl.
Qed.

Lemma naddOrd_increasing2 :
  forall x y z, x < y -> z ⊕ x < z ⊕ y.
Proof.
  intros.
  destruct (naddOrd_increasing_both z z x y).
  apply H1; auto.
  apply ord_le_refl.
Qed.

Lemma naddOrd_least (f:Ord -> Ord -> Ord)
  (Hmono1 : forall a b c, a < b -> f a c < f b c)
  (Hmono2 : forall a b c, a < b -> f c a < f c b)
  :
  (forall x y, x ⊕ y ≤ f x y).
Proof.
  induction x as [A fa].
  induction y as [B g].
  rewrite ord_le_unfold.
  rewrite naddOrd_unfold.
  simpl.
  intros [a|b].
  - eapply ord_le_lt_trans; [ apply H | auto with ord ].
  - eapply ord_le_lt_trans; [ apply H0 | auto with ord ].
Qed.

Lemma naddOrd_succ x y : succOrd x ⊕ y ≈ succOrd (x ⊕ y).
Proof.
  split.
  - induction y as [B g Hy].
    rewrite naddOrd_unfold.
    rewrite lub_unfold.
    simpl.
    rewrite ord_le_unfold.
    intro ua.
    rewrite ord_lt_unfold. simpl.
    exists tt.
    destruct ua as [u|a].
    + apply ord_le_refl.
    + rewrite Hy.
      apply succ_least.
      apply naddOrd_increasing2; auto with ord.
  - apply succ_least.
    apply naddOrd_increasing1.
    apply succ_lt.
Qed.

Lemma naddOrd_succ2 x y : x ⊕ succOrd y ≈ succOrd (x ⊕ y).
Proof.
  rewrite naddOrd_comm.
  rewrite naddOrd_succ.
  rewrite naddOrd_comm.
  reflexivity.
Qed.

Add Parametric Morphism : naddOrd with signature
    ord_le ++> ord_le ++> ord_le as naddOrd_le_mor.
Proof.
  intros. apply naddOrd_monotone; auto.
Qed.

Add Parametric Morphism : naddOrd with signature
    ord_lt ++> ord_le ++> ord_lt as naddOrd_lt_mor1.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply naddOrd_increasing1; eauto.
  apply naddOrd_monotone; auto.
  reflexivity.
Qed.

Add Parametric Morphism : naddOrd with signature
    ord_le ++> ord_lt ++> ord_lt as naddOrd_lt_mor2.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply naddOrd_increasing2; eauto.
  apply naddOrd_monotone; auto.
  reflexivity.
Qed.

Add Parametric Morphism : naddOrd with signature
   ord_eq ==> ord_eq ==> ord_eq as naddOrd_eq_mor.
Proof.
  intros; split; apply naddOrd_le_mor; solve [apply H|apply H0].
Qed.


Lemma add_nadd_le : forall x y,
  x + y ≤ x ⊕ y.
Proof.
  induction y as [Y g Hy].
  rewrite addOrd_unfold.
  rewrite naddOrd_unfold.
  apply lub_least.
  - rewrite <- lub_le1.
    rewrite ord_le_unfold; intro a.
    rewrite ord_lt_unfold; exists a.
    simpl.
    apply naddOrd_le1.
  - apply sup_least; intro.
    simpl.
    rewrite <- lub_le2.
    apply succ_least.
    rewrite ord_lt_unfold.
    exists a.
    simpl.
    auto with ord.
Qed.

Lemma naddOrd_least2: forall (x y z:Ord),
    (forall i, x i ⊕ y < z) ->
    (forall j, x ⊕ y j < z) ->
    x ⊕ y <= z.
Proof.
  induction x as [x Hx] using ordinal_induction.
  induction y as [y Hy] using ordinal_induction.
  intros z H1 H2.
  rewrite naddOrd_unfold.
  rewrite ord_le_unfold.
  rewrite lub_unfold. simpl.
  intros [i|j]; auto.
Qed.

Lemma naddOrd_least3: forall (x y z:Ord),
    (forall i, i < x -> i ⊕ y < z) ->
    (forall j, j < y -> x ⊕ j < z) ->
    x ⊕ y <= z.
Proof.
  intros.
  apply naddOrd_least2.
  intros. apply H; auto with ord.
  intros. apply H0; auto with ord.
Qed.

Lemma add_nadd_assoc1 : forall x y z,
    x+(y⊕z) <= (x+y)⊕z.
Proof.
  intro x.
  induction y as [y Hy] using ordinal_induction.
  induction z as [z Hz] using ordinal_induction.
  rewrite addOrd_unfold.
  apply lub_least.
  { rewrite <- naddOrd_le1.
    apply addOrd_le1. }
  apply sup_least.
  rewrite naddOrd_unfold.
  rewrite lub_unfold. simpl.
  intros [i|j]; apply succ_least.
  - rewrite (Hy); auto with ord.
    apply naddOrd_increasing1.
    apply addOrd_increasing; auto with ord.
  - rewrite Hz; auto with ord.
    apply naddOrd_increasing2.
    auto with ord.
Qed.


Lemma nadd_1_omega : 1⊕ω ≈ ω+1.
Proof.
  rewrite naddOrd_comm.
  rewrite naddOrd_succ2.
  rewrite naddOrd_zero_r.
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Lemma add_nadd_assoc_impossible :
  ~(forall x y z, (x+y)⊕z <= x+(y⊕z)).
Proof.
  intro H. specialize (H 1 1 ω).
  assert (H1: 1 + (1 ⊕ ω) <= 1 ⊕ ω).
  { rewrite nadd_1_omega at 1.
    rewrite nadd_1_omega.
    rewrite addOrd_assoc.
    apply addOrd_monotone; auto with ord.
    apply additively_closed_collapse.
    apply additively_closed_omega.
    apply omega_gt1. }
  rewrite H1 in H.
  apply naddOrd_cancel_le in H.
  apply (ord_lt_irreflexive 1).
  rewrite <- H at 2.
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  auto with ord.
Qed.

Lemma add_nadd_assoc2 :
  forall x y z,
    (forall q, q <= z -> x⊕q <= x+q) ->
    (x+y)⊕z <= x+(y⊕z).
Proof.
  intro x.
  induction y as [y Hy] using ordinal_induction.
  induction z as [z Hz] using ordinal_induction.
  intro H.
  apply naddOrd_least2.
  - rewrite addOrd_unfold. rewrite lub_unfold. rewrite sup_unfold. simpl.
    intros [i|[j []]]; simpl.
    + apply ord_lt_le_trans with (x⊕z).
      apply naddOrd_increasing1. auto with ord.
      rewrite H; auto with ord.
      apply addOrd_monotone; auto with ord.
      apply naddOrd_le2.
    + rewrite Hy; auto with ord.
      apply addOrd_increasing.
      apply naddOrd_increasing1.
      auto with ord.
  - intros. rewrite Hz; auto with ord.
    apply addOrd_increasing.
    apply naddOrd_increasing2.
    auto with ord.
    intros.
    apply H.
    rewrite H0; auto with ord.
Qed.

Section nadd_closed.
  Variable EM:excluded_middle.

  Lemma leading_cantor_term:
    forall n a q,
      expOrd ω a ≤ q ->
      q ≤ expOrd ω a * sz (S n) ->
      exists q' : Ord, q' < q /\ q ≈ expOrd ω a + q'.
  Proof.
    intros n a q Hq1 Hq2.
    destruct (cantor_decomposition EM q) as [ls [Hls1 Hls2]].
    destruct ls.
    { simpl in *.
      rewrite <- Hls2 in Hq1.
      elim (ord_lt_irreflexive 0).
      rewrite <- Hq1 at 2.
      apply expOrd_nonzero. }
    simpl in *.
    destruct Hls1 as [H1 H2].
    exists (cantor_denote ls).
    assert (Ho : o ≈ a).
    { destruct (classical.order_trichotomy EM o a) as [H|[H|H]]; auto.
      - elim (ord_lt_irreflexive q).
        rewrite <- Hls2 at 1.
        rewrite <- Hq1.
        rewrite (expOrd_unfold _ a).
        rewrite <- lub_le2.
        rewrite ord_lt_unfold in H.
        destruct H as [j Hj].
        rewrite <- (sup_le _ _ j).
        rewrite mulOrd_unfold.
        rewrite <- (sup_le _ _ (S (length ls))).
        simpl.
        apply ord_le_lt_trans with (expOrd ω o + cantor_denote ls + 0).
        { rewrite addOrd_zero_r. reflexivity. }
        apply ord_lt_le_trans with (expOrd ω o + cantor_denote ls + expOrd ω (a j)).
        { apply addOrd_increasing; auto. apply expOrd_nonzero. }
        apply addOrd_monotone; auto with ord.
        transitivity (expOrd ω (a j) * (sz (length ls + 1)%nat)).
        rewrite natOrdSize_add.
        rewrite ordDistrib_left.
        apply addOrd_monotone; simpl.
        rewrite mulOrd_one_r.
        apply expOrd_monotone; auto with ord.
        { clear - H2 Hj.
          revert o H2 Hj.
          induction ls; simpl; intros.
          rewrite mulOrd_zero_r. reflexivity.
          transitivity (expOrd ω (a j) * (sz (length ls + 1)%nat)).
          rewrite natOrdSize_add.
          rewrite ordDistrib_left.
          apply addOrd_monotone; simpl.
          rewrite mulOrd_one_r.
          apply expOrd_monotone; auto.
          destruct H2.
          rewrite H. auto.
          destruct H2.
          eapply IHls; eauto.
          rewrite H. auto.
          apply mulOrd_monotone2.
          replace (length ls + 1)%nat with (1 + length ls)%nat by lia.
          simpl. reflexivity. }
        replace (length ls + 1)%nat with (1 + length ls)%nat by lia.
        simpl. reflexivity.
      - elim (ord_lt_irreflexive q).
        rewrite Hq2 at 1.
        rewrite <- Hls2.
        rewrite <- addOrd_le1.
        rewrite ord_lt_unfold in H.
        destruct H as [j H].
        rewrite (expOrd_unfold _ o).
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ j).
        rewrite H.
        apply mulOrd_increasing2.
        apply expOrd_nonzero.
        rewrite ord_lt_unfold.
        exists (S n). simpl.
        reflexivity. }
    split.
    - rewrite <- Hls2.
      clear - H2.
      revert o H2.
      induction ls; simpl; intros.
      rewrite addOrd_zero_r.
      apply expOrd_nonzero.
      simpl in *.
      destruct H2.
      rewrite H at 1.
      apply addOrd_increasing.
      apply IHls; auto.
    - rewrite <- Ho.
      symmetry; auto.
  Qed.

  Variable a:Ord.
  Hypothesis Ha : complete a.
  Hypothesis Hnadd_closed_ind:
    forall a' : Ord,
      a' ≤ a ->
      forall x y : Ord, complete a' -> x < expOrd ω a' -> y < expOrd ω a' -> x ⊕ y < expOrd ω a'.

  Lemma nadd_closed_technical1:
    forall
      n q r,
      r < expOrd ω a ->
      q ≤ expOrd ω a * succOrd (natOrdSize n) ->
      r ⊕ q < expOrd ω a + q.
  Proof.
    induction q as [q Hindq] using ordinal_induction; intros.

    destruct (classical.order_total EM (expOrd ω a) q).
    + assert (exists q', q' < q /\ q ≈ expOrd ω a + q').
      { apply leading_cantor_term with n; auto. }

      destruct H2 as [q' [Hq1 Hq2]].
      rewrite Hq2.
      rewrite naddOrd_comm.
      rewrite add_nadd_assoc2.
      rewrite naddOrd_comm.
      apply addOrd_increasing.
      apply Hindq; auto.
      rewrite Hq1. auto.

      intros. induction q0 as [q0 Hindq0] using ordinal_induction.
      apply naddOrd_least3.
      * intros.
        rewrite <- addOrd_le1.
        apply Hnadd_closed_ind; auto with ord.
        rewrite H2. auto with ord.
      * intros. rewrite Hindq0; auto with ord.
        apply addOrd_increasing; auto.
        rewrite H3; auto.

    + rewrite <- addOrd_le1.
      apply Hnadd_closed_ind; auto with ord.
  Qed.

  Lemma nadd_closed_technical2:
    forall m n q,
      q ≤ expOrd ω a * succOrd (natOrdSize n) ->
      expOrd ω a * natOrdSize m ⊕ q ≤ expOrd ω a * natOrdSize m + q.
  Proof.
    induction m as [m Hindm] using (size_induction ω).
    induction n as [n Hindn] using (size_induction ω).
    induction q as [q Hindq] using ordinal_induction.
    intro Hq.
    apply naddOrd_least3.
    - intros i Hi.
      destruct m.
      { simpl in Hi. rewrite mulOrd_zero_r in Hi.
        rewrite ord_lt_unfold in Hi.
        destruct Hi as [[] _]. }
      simpl in Hi.
      rewrite mulOrd_succ in Hi.
      rewrite addOrd_unfold in Hi.
      apply lub_lt in Hi.
      destruct Hi as [Hi|Hi].
      { apply ord_lt_le_trans with ((expOrd ω a * sz m) ⊕ q).
        apply naddOrd_increasing1; auto.
        rewrite (Hindm m) with (n:=n) (q:=q); simpl; auto with ord.
        apply addOrd_monotone; auto with ord.
        apply mulOrd_monotone2; auto with ord. }
      apply sup_lt in Hi.
      destruct Hi as [r Hi].
      rewrite ord_lt_unfold in Hi. simpl in Hi.
      destruct Hi as [[] Hi].
      rewrite Hi. clear i Hi.

      rewrite add_nadd_assoc2.
      2:{ intros. apply Hindm with n; simpl; auto with ord.
          rewrite H. auto. }
      simpl.
      rewrite mulOrd_succ.
      rewrite <- addOrd_assoc.
      apply addOrd_increasing.

      eapply nadd_closed_technical1; eauto with ord.

    - intros.
      rewrite Hindq; auto with ord.
      apply addOrd_increasing; auto with ord.
      rewrite H; auto.
  Qed.

  Lemma nadd_add_same_powers_step:
    forall m n,
      expOrd ω a * sz (S m) ⊕ expOrd ω a * sz (S n) ≤ expOrd ω a * ω (m + n + 2)%nat.
  Proof.
    induction m as [m Hindm] using (size_induction ω).
    induction n as [n Hindn] using (size_induction ω).
    apply naddOrd_least3.
    - simpl; intros q Hq.
      rewrite mulOrd_succ in Hq.
      rewrite addOrd_unfold in Hq.
      apply lub_lt in Hq.
      destruct Hq as [Hq|Hq].
      { destruct m.
        - simpl in Hq. rewrite mulOrd_zero_r in Hq.
          rewrite ord_lt_unfold in Hq. destruct Hq as [[] _].
        - apply ord_lt_le_trans with ((expOrd ω a * natOrdSize (S m)) ⊕ expOrd ω a * succOrd (sz n)).
          apply naddOrd_increasing1. auto.
          rewrite (Hindm m) with (n:=n); simpl; auto with ord.
          apply mulOrd_monotone2; auto with ord. }
      apply sup_lt in Hq.
      destruct Hq as [r Hq].
      rewrite ord_lt_unfold in Hq. simpl in Hq.
      destruct Hq as [[] Hq].
      rewrite Hq.

      rewrite add_nadd_assoc2.
      + replace (m+n+2)%nat with (2+n+m)%nat by lia.
        rewrite natOrdSize_add.
        rewrite ordDistrib_left.
        apply addOrd_increasing.
        rewrite naddOrd_comm.
        simpl.
        rewrite (mulOrd_succ _ (succOrd (sz n))).
        simpl.
        change (expOrd ω a * sz (S n) ⊕ expOrd ω a r <
                expOrd ω a * sz (S n) + expOrd ω a).
        rewrite (nadd_closed_technical2) with (n:=S n); auto.
        apply addOrd_increasing; auto with ord.
        rewrite mulOrd_succ.
        rewrite <- addOrd_le2.
        auto with ord.
      + apply nadd_closed_technical2; auto.
    - simpl; intros q Hq.
      rewrite mulOrd_succ in Hq.
      rewrite addOrd_unfold in Hq.
      apply lub_lt in Hq.
      destruct Hq as [Hq|Hq].
      { destruct n.
        - simpl in Hq. rewrite mulOrd_zero_r in Hq.
          rewrite ord_lt_unfold in Hq. destruct Hq as [[] _].
        - apply ord_lt_le_trans with
            ((expOrd ω a * succOrd (sz m)) ⊕ (expOrd ω a * sz (S n))).
          apply naddOrd_increasing2. auto.
          rewrite (Hindn n).
          apply mulOrd_monotone2; auto with ord.
          apply natOrdSize_monotone. lia.
          simpl; auto with ord. }
      apply sup_lt in Hq.
      destruct Hq as [r Hq].
      rewrite ord_lt_unfold in Hq. simpl in Hq.
      destruct Hq as [[] Hq].
      rewrite Hq.

      rewrite naddOrd_comm.
      rewrite add_nadd_assoc2.
      + replace (m+n+2)%nat with (2+m+n)%nat by lia.
        rewrite natOrdSize_add.
        rewrite ordDistrib_left.
        apply addOrd_increasing.
        rewrite naddOrd_comm.
        simpl.
        rewrite (mulOrd_succ _ (succOrd (sz m))).
        simpl.
        change (expOrd ω a * sz (S m) ⊕ expOrd ω a r <
                expOrd ω a * sz (S m) + expOrd ω a).
        rewrite (nadd_closed_technical2) with (n:=S m); auto.
        apply addOrd_increasing; auto with ord.
        rewrite mulOrd_succ.
        rewrite <- addOrd_le2.
        auto with ord.
      + apply nadd_closed_technical2; auto.
  Qed.
End nadd_closed.

Lemma nadd_closed (EM:excluded_middle):
  forall a x y,
    complete a ->
    x < expOrd ω a ->
    y < expOrd ω a ->
    x ⊕ y < expOrd ω a.
Proof.
  induction a as [a Hinda] using ordinal_induction.
  intros x y Ha Hx Hy.
  rewrite expOrd_unfold in Hx.
  apply lub_lt in Hx.
  destruct Hx as [Hx|Hx].
  { rewrite ord_lt_unfold in Hx.
    destruct Hx as [[] Hx].
    simpl in Hx.
    rewrite Hx.
    rewrite naddOrd_comm.
    rewrite naddOrd_zero_r.
    auto. }
  rewrite expOrd_unfold in Hy.
    apply lub_lt in Hy.
    destruct Hy as [Hy|Hy].
    { rewrite ord_lt_unfold in Hy.
      destruct Hy as [[] Hy].
      simpl in Hy.
      rewrite Hy.
      rewrite naddOrd_zero_r.
      rewrite expOrd_unfold.
      rewrite <- lub_le2.
      auto. }
    apply sup_lt in Hx.
    apply sup_lt in Hy.
    destruct Hx as [i Hx].
    destruct Hy as [j Hy].
    destruct (complete_directed a Ha i j) as [k [Hk1 Hk2]].
    rewrite mulOrd_unfold in Hx.
    apply sup_lt in Hx.
    destruct Hx as [m Hx].
    rewrite mulOrd_unfold in Hy.
    apply sup_lt in Hy.
    destruct Hy as [n Hy].
    rewrite expOrd_unfold.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ k).
    rewrite mulOrd_unfold.
    rewrite <- (sup_le _ _ (m+n+2)%nat).
    apply ord_le_lt_trans with (expOrd ω (a k) * ω (m + n + 2)%nat + 0).
    2: { apply addOrd_increasing. apply expOrd_nonzero. }
    rewrite addOrd_zero_r.
    transitivity ((expOrd ω (a k) * sz (S m)) ⊕ (expOrd ω (a k) * sz (S n))).
    apply naddOrd_monotone.
    { rewrite Hx. simpl. rewrite <- mulOrd_succ.
      apply mulOrd_monotone1.
      apply expOrd_monotone; auto. }
    { rewrite Hy. simpl. rewrite <- mulOrd_succ.
      apply mulOrd_monotone1.
      apply expOrd_monotone; auto. }

    apply nadd_add_same_powers_step; auto with ord.
    intros; apply Hinda; auto with ord.
    rewrite H. auto with ord.
Qed.

Lemma nadd_add_same_powers (EM:excluded_middle):
  forall a m n,
    complete a ->
    expOrd ω a * sz m ⊕ expOrd ω a * sz n ≤ expOrd ω a * sz (m + n)%nat.
Proof.
  intros.
  destruct m. rewrite mulOrd_zero_r.
  rewrite naddOrd_zero_l.
  simpl. reflexivity.
  destruct n. rewrite mulOrd_zero_r.
  rewrite naddOrd_zero_r.
  simpl.
  replace (m+0)%nat with m by lia.
  reflexivity.
  replace (S m + S n)%nat with (m+n+2)%nat by lia.
  apply nadd_add_same_powers_step; auto.
  intros. apply nadd_closed; auto.
Qed.

(** ** Constructive closure of ω-powers under natural sum

  [nadd_closed] and [nadd_add_same_powers] above assume excluded middle,
  which enters only through [nadd_closed_technical1]: it compares [ω^a]
  with an arbitrary [q] and splits off a leading Cantor term.  Keeping
  every quantity in the explicit form [ω^c·m + u] with [u < ω^c] avoids
  the comparison: a child of [ω^c·m + u] is either [ω^c·m + u'] for a
  child [u'] of [u], or lies below [ω^c·(m-1) + w] for some [w < ω^c].
  The completeness hypothesis on the exponent is still needed (it is
  what makes the children of [ω^a] directed); without it, closure fails
  constructively. *)

Section same_powers.
  Variable c : Ord.
  Let E := expOrd ω c.
  Hypothesis Hc : forall x y, x < E -> y < E -> x ⊕ y < E.

  (* E * (k+1) as E * k + E, with the successor on the right *)
  Lemma mul_succ_strict k w : w < E -> E * natOrdSize k + w < E * natOrdSize (S k).
  Proof.
    intro Hw. simpl. rewrite mulOrd_succ. apply addOrd_increasing; auto.
  Qed.

  Lemma same_powers_le : forall o m u n v,
    (E * natOrdSize m + u) ⊕ (E * natOrdSize n + v) ≤ o ->
    u < E -> v < E ->
    (E * natOrdSize m + u) ⊕ (E * natOrdSize n + v) ≤ E * natOrdSize (m + n) + (u ⊕ v).
  Proof.
    induction o as [o IH] using (well_founded_ind ord_lt_wf).
    intros m u n v Ho Hu Hv.
    apply naddOrd_least3.
    - intros i Hi.
      destruct (add_lt _ _ _ Hi) as [Hi'|[k Hk]].
      + (* i below E * m *)
        destruct m as [|m'].
        { simpl in Hi'. rewrite mulOrd_zero_r in Hi'. elim (zero_lt i Hi'). }
        simpl in Hi'. rewrite mulOrd_succ in Hi'.
        assert (Hw : exists w, w < E /\ i ≤ E * natOrdSize m' + w).
        { destruct (add_lt _ _ _ Hi') as [H1|[w Hw]].
          - exists 0. split; [apply expOrd_nonzero|]. rewrite addOrd_zero_r. auto with ord.
          - exists (ordSize E w). split; auto with ord. }
        destruct Hw as [w [Hw Hiw]].
        apply ord_le_lt_trans with ((E * natOrdSize m' + w) ⊕ (E * natOrdSize n + v)).
        { apply naddOrd_monotone; auto. reflexivity. }
        assert (Hlt : (E * natOrdSize m' + w) ⊕ (E * natOrdSize n + v) <
                      (E * natOrdSize (S m') + u) ⊕ (E * natOrdSize n + v)).
        { apply naddOrd_increasing1.
          apply ord_lt_le_trans with (E * natOrdSize (S m')).
          - apply mul_succ_strict; auto.
          - apply addOrd_le1. }
        rewrite (IH _ (ord_lt_le_trans _ _ _ Hlt Ho) m' w n v); auto with ord.
        apply ord_lt_le_trans with (E * natOrdSize (S (m' + n))).
        * apply mul_succ_strict; auto.
        * apply addOrd_le1.
      + (* i below E * m + u_k *)
        rewrite Hk.
        assert (Hlt : (E * natOrdSize m + ordSize u k) ⊕ (E * natOrdSize n + v) <
                      (E * natOrdSize m + u) ⊕ (E * natOrdSize n + v)).
        { apply naddOrd_increasing1. apply addOrd_increasing. auto with ord. }
        rewrite (IH _ (ord_lt_le_trans _ _ _ Hlt Ho) m (ordSize u k) n v); auto with ord.
        * apply addOrd_increasing. apply naddOrd_increasing1. auto with ord.
        * apply ord_lt_trans with u; auto with ord.
    - intros j Hj.
      destruct (add_lt _ _ _ Hj) as [Hj'|[k Hk]].
      + destruct n as [|n'].
        { simpl in Hj'. rewrite mulOrd_zero_r in Hj'. elim (zero_lt j Hj'). }
        simpl in Hj'. rewrite mulOrd_succ in Hj'.
        assert (Hw : exists w, w < E /\ j ≤ E * natOrdSize n' + w).
        { destruct (add_lt _ _ _ Hj') as [H1|[w Hw]].
          - exists 0. split; [apply expOrd_nonzero|]. rewrite addOrd_zero_r. auto with ord.
          - exists (ordSize E w). split; auto with ord. }
        destruct Hw as [w [Hw Hjw]].
        apply ord_le_lt_trans with ((E * natOrdSize m + u) ⊕ (E * natOrdSize n' + w)).
        { apply naddOrd_monotone; auto. reflexivity. }
        assert (Hlt : (E * natOrdSize m + u) ⊕ (E * natOrdSize n' + w) <
                      (E * natOrdSize m + u) ⊕ (E * natOrdSize (S n') + v)).
        { apply naddOrd_increasing2.
          apply ord_lt_le_trans with (E * natOrdSize (S n')).
          - apply mul_succ_strict; auto.
          - apply addOrd_le1. }
        rewrite (IH _ (ord_lt_le_trans _ _ _ Hlt Ho) m u n' w); auto with ord.
        replace (m + S n')%nat with (S (m + n'))%nat by lia.
        apply ord_lt_le_trans with (E * natOrdSize (S (m + n'))).
        * apply mul_succ_strict; auto.
        * apply addOrd_le1.
      + rewrite Hk.
        assert (Hlt : (E * natOrdSize m + u) ⊕ (E * natOrdSize n + ordSize v k) <
                      (E * natOrdSize m + u) ⊕ (E * natOrdSize n + v)).
        { apply naddOrd_increasing2. apply addOrd_increasing. auto with ord. }
        rewrite (IH _ (ord_lt_le_trans _ _ _ Hlt Ho) m u n (ordSize v k)); auto with ord.
        * apply addOrd_increasing. apply naddOrd_increasing2. auto with ord.
        * apply ord_lt_trans with v; auto with ord.
  Qed.

  Lemma same_powers_lt m n :
    E * natOrdSize m ⊕ E * natOrdSize n < E * natOrdSize (S (m + n)).
  Proof.
    apply ord_le_lt_trans with ((E * natOrdSize m + 0) ⊕ (E * natOrdSize n + 0)).
    { apply naddOrd_monotone; rewrite addOrd_zero_r; reflexivity. }
    rewrite (same_powers_le _ m 0 n 0 (ord_le_refl _)); try apply expOrd_nonzero.
    apply mul_succ_strict. apply Hc; apply expOrd_nonzero.
  Qed.
End same_powers.

Theorem nadd_closed_con : forall a x y,
  complete a ->
  x < expOrd ω a ->
  y < expOrd ω a ->
  x ⊕ y < expOrd ω a.
Proof.
  induction a as [a IHa] using ordinal_induction.
  intros x y Ha Hx Hy.
  rewrite expOrd_unfold in Hx. apply lub_lt in Hx.
  destruct Hx as [Hx|Hx].
  { rewrite ord_lt_unfold in Hx. destruct Hx as [[] Hx]. simpl in Hx.
    rewrite Hx. rewrite naddOrd_comm, naddOrd_zero_r. auto. }
  rewrite expOrd_unfold in Hy. apply lub_lt in Hy.
  destruct Hy as [Hy|Hy].
  { rewrite ord_lt_unfold in Hy. destruct Hy as [[] Hy]. simpl in Hy.
    rewrite Hy. rewrite naddOrd_zero_r. rewrite expOrd_unfold.
    eapply ord_lt_le_trans; [exact Hx | apply lub_le2]. }
  apply sup_lt in Hx. destruct Hx as [i Hx].
  apply sup_lt in Hy. destruct Hy as [j Hy].
  destruct (complete_directed a Ha i j) as [k [Hk1 Hk2]].
  rewrite mulOrd_unfold in Hx. apply sup_lt in Hx. destruct Hx as [m Hx].
  rewrite mulOrd_unfold in Hy. apply sup_lt in Hy. destruct Hy as [n Hy].
  set (E := expOrd ω (a k)).
  assert (HE : forall x y, x < E -> y < E -> x ⊕ y < E).
  { intros. apply IHa; auto with ord; apply complete_subord; auto. }
  rewrite expOrd_unfold. rewrite <- lub_le2.
  rewrite <- (sup_le _ _ k).
  rewrite mulOrd_unfold.
  rewrite <- (sup_le _ _ (S (S m + S n))).
  apply ord_le_lt_trans with (E * natOrdSize (S (S m + S n))).
  2: { apply ord_le_lt_trans with (E * natOrdSize (S (S m + S n)) + 0);
       [ rewrite addOrd_zero_r; reflexivity | apply addOrd_increasing; apply expOrd_nonzero ]. }
  apply ord_lt_le.
  apply ord_le_lt_trans with (E * natOrdSize (S m) ⊕ E * natOrdSize (S n)).
  - apply naddOrd_monotone.
    + apply ord_lt_le in Hx. rewrite Hx. simpl.
      rewrite <- mulOrd_succ. apply mulOrd_monotone1. apply expOrd_monotone; auto.
    + apply ord_lt_le in Hy. rewrite Hy. simpl.
      rewrite <- mulOrd_succ. apply mulOrd_monotone1. apply expOrd_monotone; auto.
  - apply same_powers_lt. auto.
Qed.

Lemma nadd_add_same_powers_con a m n :
  complete a ->
  expOrd ω a * natOrdSize m ⊕ expOrd ω a * natOrdSize n ≤ expOrd ω a * natOrdSize (m + n).
Proof.
  intro Ha.
  apply ord_le_trans with
      ((expOrd ω a * natOrdSize m + 0) ⊕ (expOrd ω a * natOrdSize n + 0)).
  { apply naddOrd_monotone; rewrite addOrd_zero_r; reflexivity. }
  rewrite (same_powers_le a (fun x y => nadd_closed_con a x y Ha) _ m 0 n 0 (ord_le_refl _));
    try apply expOrd_nonzero.
  rewrite naddOrd_zero_r, addOrd_zero_r. reflexivity.
Qed.

(** The completeness hypothesis cannot be dropped: closure of every
    [ω^a] under natural sum implies weak excluded middle.  Take [a] with
    exactly two children [c1 = ord P (fun _ => ω)] (0, or ω+1 if [P]) and
    [c2 = succ (ord P (fun _ => 0))] (1, or 2 if [P]).  Then
    [ω^c1 ⊕ ω^c2 < ω^a] must name a child of [ω^a]: below [ω^c1 · (n+1)],
    refuted by [~P] (it is then finite, while [ω^c2 ≥ ω]), or below
    [ω^c2 · (n+1)], refuted by [P] (it is then below [ω^3 ≤ ω^c1]). *)
Theorem nadd_closed_needs_complete :
  (forall a x y, x < expOrd ω a -> y < expOrd ω a -> x ⊕ y < expOrd ω a) ->
  weak_excluded_middle.
Proof.
  intros H P.
  pose (c1 := ord P (fun _ => ω)).
  pose (e := ord P (fun _ => zeroOrd)).
  pose (c2 := succOrd e).
  pose (a := ord bool (fun b:bool => if b then c1 else c2)).
  assert (Hc1a : c1 < a) by apply (index_lt a true).
  assert (Hc2a : c2 < a) by apply (index_lt a false).
  assert (Hx : expOrd ω c1 < expOrd ω a) by (apply expOrd_increasing; auto; apply omega_gt1).
  assert (Hy : expOrd ω c2 < expOrd ω a) by (apply expOrd_increasing; auto; apply omega_gt1).
  assert (He1 : e ≤ 1).
  { unfold e. rewrite ord_le_unfold. intro q. simpl. apply succ_lt. }
  assert (Hyω : ω ≤ expOrd ω c2).
  { destruct (expOrd_one' ω omega_gt0) as [_ H2].
    apply ord_le_trans with (expOrd ω 1); auto. apply expOrd_monotone.
    unfold c2. apply succ_monotone. apply zero_least. }
  generalize (H a _ _ Hx Hy). intro Hxy.
  rewrite (expOrd_unfold ω a) in Hxy. apply lub_lt in Hxy.
  destruct Hxy as [H1|H1].
  { exfalso. rewrite ord_lt_unfold in H1. destruct H1 as [t H1].
    apply (ord_lt_irreflexive 0).
    apply ord_lt_le_trans with (expOrd ω c2); [apply expOrd_nonzero|].
    apply ord_le_trans with (expOrd ω c1 ⊕ expOrd ω c2); [apply naddOrd_le2|].
    exact H1. }
  apply sup_lt in H1. destruct H1 as [i H1].
  rewrite mulOrd_unfold in H1. apply sup_lt in H1. destruct H1 as [n H1].
  simpl in H1.
  destruct i; simpl in H1.
  - (* the child c1: refuted by ~P *)
    left. intro np.
    assert (Hc1z : c1 ≤ 0).
    { unfold c1. rewrite ord_le_unfold. intro p. elim (np p). }
    assert (HE : expOrd ω c1 ≤ 1).
    { rewrite (expOrd_monotone ω c1 0 Hc1z). apply expOrd_zero. }
    assert (Hfin : expOrd ω c1 * natOrdSize n + expOrd ω c1 < ω).
    { apply ord_le_lt_trans with (1 * natOrdSize n + 1).
      - apply addOrd_monotone; auto. apply mulOrd_monotone1; auto.
      - rewrite mulOrd_one_l.
        change (natOrdSize n + succOrd 0 < ω).
        rewrite addOrd_succ, addOrd_zero_r.
        apply (index_lt ω (S n)). }
    apply (ord_lt_irreflexive ω).
    apply ord_le_lt_trans with (expOrd ω c1 ⊕ expOrd ω c2).
    + apply ord_le_trans with (expOrd ω c2); auto. apply naddOrd_le2.
    + apply ord_lt_trans with (expOrd ω c1 * natOrdSize n + expOrd ω c1); auto.
  - (* the child c2: refuted by P *)
    right. intro p.
    assert (Hc1ω : ω ≤ c1).
    { apply ord_lt_le. unfold c1. rewrite ord_lt_unfold. exists p. reflexivity. }
    assert (Hc2 : c2 ≤ 2) by (unfold c2; apply succ_monotone; auto).
    assert (HE : expOrd ω c2 ≤ expOrd ω 2) by (apply expOrd_monotone; auto).
    apply (ord_lt_irreflexive (expOrd ω c1)).
    apply ord_le_lt_trans with (expOrd ω c1 ⊕ expOrd ω c2); [apply naddOrd_le1|].
    apply ord_lt_le_trans with (expOrd ω c2 * natOrdSize n + expOrd ω c2); auto.
    apply ord_le_trans with (expOrd ω 2 * natOrdSize (S n)).
    { simpl. rewrite mulOrd_succ.
      apply addOrd_monotone; auto. apply mulOrd_monotone1; auto. }
    apply ord_le_trans with (expOrd ω 2 * ω).
    { apply ord_lt_le. apply mulOrd_increasing2; [apply expOrd_nonzero | apply (index_lt ω (S n))]. }
    apply ord_le_trans with (expOrd ω (succOrd 2)).
    { apply expOrd_succ. apply omega_gt0. }
    apply expOrd_monotone. rewrite <- Hc1ω.
    apply ord_lt_le. apply (index_lt ω 3%nat).
Qed.

Lemma cantor_denote_app: forall xs ys,
  cantor_denote (xs ++ ys) ≈ cantor_denote xs + cantor_denote ys.
Proof.
  induction xs; simpl; intros.
  { rewrite addOrd_zero_l. reflexivity. }
  rewrite IHxs.
  rewrite addOrd_assoc.
  reflexivity.
Qed.

Lemma each_app: forall A (P:A -> Prop) xs ys,
    each P (xs ++ ys) -> each P xs /\ each P ys.
Proof.
  intros A P xs ys.
  induction xs; simpl; intuition.
Qed.

Lemma cantor_sequence_le1:
  forall xs x,
    cantor_sequence x xs ->
    forall x', List.In x' xs -> x' <= x.
Proof.
  induction xs; simpl; intuition subst; auto.
  rewrite <- H0.
  apply IHxs; auto.
Qed.

Lemma cantor_sequence_le:
  forall xs x ys,
    cantor_sequence x (xs++ys) ->
    forall x' y,
      List.In x' xs ->
      List.In y ys ->
      y <= x'.
Proof.
  induction xs; simpl; intuition subst.
  apply cantor_sequence_le1 with (xs++ys); auto.
  apply List.in_or_app; auto.
  eapply IHxs; eauto.
Qed.

Lemma cantor_denote_nadd_add (EM:excluded_middle):
  forall xs b,
    each complete xs ->
    (forall a, List.In a xs -> a >= b) ->
    forall q, q <= expOrd ω b ->
      cantor_denote xs ⊕ q <= cantor_denote xs + q.
Proof.
  induction xs as [|x xs] using List.rev_ind; simpl; auto with ord.
  { intros.
    rewrite naddOrd_zero_l.
    rewrite addOrd_zero_l. reflexivity. }
  intros b Hxs1 Hxs2.
  intros q Hq.
  apply each_app in Hxs1.
  rewrite cantor_denote_app. simpl.
  rewrite addOrd_zero_r.
  rewrite add_nadd_assoc2.
  - rewrite <- addOrd_assoc.
    apply addOrd_monotone; auto with ord.
    revert Hq.
    induction q as [q Hindq] using ordinal_induction.
    intro Hq.
    apply naddOrd_least3.
    + intros i Hi.
      eapply nadd_closed_technical1 with (n:=O); simpl; auto.
      simpl in *; intuition.
      intros; apply nadd_closed; auto.
      rewrite mulOrd_one_r.
      rewrite Hq.
      apply expOrd_monotone.
      apply Hxs2.
      apply List.in_or_app.
      simpl; auto.
    + intros j Hj.
      rewrite Hindq; auto with ord.
      apply addOrd_increasing; auto.
      rewrite Hj; auto.
  - intros. apply IHxs with b; simpl in *; intuition.
    + apply Hxs2; simpl.
      apply List.in_or_app; auto.
    + rewrite H. auto.
Qed.

Fixpoint cantor_denote_nadd (xs:list Ord) : Ord :=
  match xs with
  | nil => 0
  | x::xs' => expOrd ω x ⊕ cantor_denote_nadd xs'
  end.


Lemma cantor_denote_nadd_app: forall xs ys,
  cantor_denote_nadd (xs ++ ys) ≈ cantor_denote_nadd xs ⊕ cantor_denote_nadd ys.
Proof.
  induction xs; simpl; intros.
  { rewrite naddOrd_zero_l. auto with ord. }
  rewrite IHxs.
  rewrite naddOrd_assoc.
  reflexivity.
Qed.

Lemma cantor_sequence_app1:
  forall xs x ys,
    cantor_sequence x (xs ++ ys) -> cantor_sequence x xs.
Proof.
  induction xs; simpl; intuition eauto.
Qed.

(** ** Natural sums of Cantor sequences, constructively

  [cantor_denote_nadd_eq] above needs excluded middle only to compare
  adjacent exponents.  When each exponent is known to be either below or
  equal to its predecessor, closure under natural sum ([nadd_closed_con])
  suffices: group the leading run of equal exponents as [ω^y · k], bound
  the rest below [ω^y], and apply [same_powers_le].  Without such
  decisions the identity is not constructive, even for complete
  exponents ([cantor_denote_nadd_eq_WEM] below). *)

Fixpoint cantor_sequence_dec (x:Ord) (ls:list Ord) : Prop :=
  match ls with
  | nil => True
  | y::ys => (y < x \/ y ≈ x) /\ cantor_sequence_dec y ys
  end.

Lemma cantor_sequence_dec_weaken : forall ls x,
  cantor_sequence_dec x ls -> cantor_sequence x ls.
Proof.
  induction ls as [|y ys IH]; simpl; intuition auto with ord.
  apply H.
Qed.

Lemma cantor_sequence_dec_EM (EM:excluded_middle) : forall ls x,
  cantor_sequence x ls -> cantor_sequence_dec x ls.
Proof.
  induction ls as [|y ys IH]; simpl; intuition.
  destruct (classical.order_trichotomy EM y x) as [H|[H|H]]; auto.
  elim (ord_lt_irreflexive x). apply ord_lt_le_trans with y; auto.
Qed.

Lemma mul_nat_below_power c z k :
  complete c -> z < c -> expOrd ω z * natOrdSize k < expOrd ω c.
Proof.
  intros Hc Hz. induction k; simpl.
  - rewrite mulOrd_zero_r. apply expOrd_nonzero.
  - rewrite mulOrd_succ. rewrite add_nadd_le.
    apply nadd_closed_con; auto.
    apply expOrd_increasing; auto with ord.
Qed.

(** A Cantor sequence below [y] splits as [ω^y · k + r] with [r < ω^y]. *)
Lemma cantor_dec_split : forall xs y,
  complete y -> each complete xs -> cantor_sequence_dec y xs ->
  exists k r, r < expOrd ω y /\ cantor_denote xs ≈ expOrd ω y * natOrdSize k + r.
Proof.
  induction xs as [|z zs IH]; intros y Hy Hxs Hd.
  - exists 0%nat, 0. split; [apply expOrd_nonzero|].
    simpl. rewrite mulOrd_zero_r, addOrd_zero_r. reflexivity.
  - simpl in Hxs, Hd. destruct Hxs as [Hz Hzs]. destruct Hd as [Hzy Hd].
    destruct (IH z Hz Hzs Hd) as [k [r [Hr Heq]]].
    destruct Hzy as [Hlt|Heqz].
    + exists 0%nat, (cantor_denote (z::zs)). split.
      * assert (Hzy : expOrd ω z < expOrd ω y) by (apply expOrd_increasing; auto with ord).
        simpl. rewrite Heq.
        rewrite add_nadd_le, add_nadd_le.
        apply nadd_closed_con; auto.
        apply nadd_closed_con; auto.
        -- apply mul_nat_below_power; auto.
        -- apply ord_lt_trans with (expOrd ω z); auto.
      * rewrite mulOrd_zero_r, addOrd_zero_l. reflexivity.
    + exists (S k), r. split.
      * rewrite <- Heqz. auto.
      * simpl cantor_denote. rewrite Heq. rewrite Heqz.
        replace (S k) with (k+1)%nat by lia.
        rewrite natOrdSize_add, ordDistrib_left, mulOrd_one_r.
        apply addOrd_assoc.
Qed.

Lemma nadd_power_cantor y xs :
  complete y -> each complete xs -> cantor_sequence_dec y xs ->
  expOrd ω y ⊕ cantor_denote xs ≤ expOrd ω y + cantor_denote xs.
Proof.
  intros Hy Hxs Hd.
  destruct (cantor_dec_split xs y Hy Hxs Hd) as [k [r [Hr Heq]]].
  rewrite Heq.
  apply ord_le_trans with
      ((expOrd ω y * natOrdSize 1 + 0) ⊕ (expOrd ω y * natOrdSize k + r)).
  { apply naddOrd_monotone; [|reflexivity].
    rewrite addOrd_zero_r, mulOrd_one_r. reflexivity. }
  rewrite (same_powers_le y (fun a b => nadd_closed_con y a b Hy) _ 1 0 k r (ord_le_refl _));
    auto; [|apply expOrd_nonzero].
  rewrite naddOrd_zero_l.
  replace (1+k)%nat with (k+1)%nat by lia.
  rewrite natOrdSize_add, ordDistrib_left, mulOrd_one_r.
  rewrite addOrd_assoc. reflexivity.
Qed.

Theorem cantor_denote_nadd_eq_dec : forall xs x,
  each complete xs ->
  cantor_sequence_dec x xs ->
  cantor_denote xs ≈ cantor_denote_nadd xs.
Proof.
  induction xs as [|y ys IH]; intros x Hxs Hd; simpl; [reflexivity|].
  simpl in Hxs, Hd. destruct Hxs as [Hy Hys]. destruct Hd as [_ Hd].
  rewrite <- (IH y); auto.
  split; [apply add_nadd_le | apply nadd_power_cantor; auto].
Qed.

Theorem cantor_denote_nadd_eq (EM:excluded_middle) :
  forall xs x,
    each complete xs ->
    cantor_sequence x xs ->
    cantor_denote xs ≈ cantor_denote_nadd xs.
Proof.
  intros xs x Hxs Hx.
  apply cantor_denote_nadd_eq_dec with x; auto.
  apply cantor_sequence_dec_EM; auto.
Qed.

(** The decisions cannot be dropped.  Let [x] have the children [0] and,
    if [P], [1]; it is complete, and [x] is [1], or [2] if [P].  In
    [ω^2 ⊕ ω^x ≤ ω^2 + ω^x], the child [ω ⊕ ω^x] of the left side must lie
    below [ω^2], which refutes [P], or below [ω^2 + j] for some [j < ω^x].
    Such a [j] lies below [ω^(x i) · ω] for a child [i] of [x]: the child
    [1] proves [P]; the child [0] makes [j] finite, which refutes [P]. *)
Theorem cantor_denote_nadd_eq_WEM :
  (forall xs x, each complete xs -> cantor_sequence x xs ->
     cantor_denote xs ≈ cantor_denote_nadd xs) ->
  weak_excluded_middle.
Proof.
  intros H P.
  pose (x := ord (option P) (fun o => match o with None => 0 | Some _ => 1 end)).
  set (two := succOrd 1).
  assert (Hx2 : x ≤ two).
  { unfold x, two. rewrite ord_le_unfold. intros [p|]; simpl.
    - apply succ_lt.
    - apply succ_trans. apply zero_least. }
  assert (Hxc : complete x).
  { unfold x. simpl. split; [|split].
    - intros [p|] [q|].
      + exists (Some p). split; reflexivity.
      + exists (Some p). simpl. split; [reflexivity | apply zero_least].
      + exists (Some q). simpl. split; [apply zero_least | reflexivity].
      + exists None. split; reflexivity.
    - left. exact (inhabits None).
    - intros [p|]; auto with ord. }
  assert (HA : expOrd ω two ⊕ expOrd ω x ≤ expOrd ω two + expOrd ω x).
  { destruct (H (two :: x :: nil) two) as [_ H2].
    - cbn [each]. split; [unfold two; auto with ord | split; [exact Hxc | exact I]].
    - cbn [cantor_sequence]. split; [reflexivity | split; [exact Hx2 | exact I]].
    - simpl in H2. rewrite naddOrd_zero_r, addOrd_zero_r in H2. exact H2. }
  assert (HP2 : P -> expOrd ω two ≤ expOrd ω x).
  { intro p. apply expOrd_monotone. unfold two. apply succ_least.
    apply (index_lt x (Some p)). }
  assert (Hw2 : ω < expOrd ω two).
  { apply ord_le_lt_trans with (expOrd ω 1).
    - rewrite expOrd_one'; auto with ord.
    - apply expOrd_increasing; auto with ord. }
  (* under P, a finite j cannot pad ω^2 up to ω ⊕ ω^x *)
  assert (Hfin : forall j, j < ω -> ω ⊕ expOrd ω x ≤ expOrd ω two + j -> ~P).
  { intros j Hj Hle p. apply (ord_lt_irreflexive ω).
    apply ord_le_lt_trans with j; auto.
    apply addOrd_cancel_le with (expOrd ω two) (expOrd ω two); [|reflexivity].
    rewrite <- Hle. rewrite add_nadd_le. rewrite naddOrd_comm.
    apply naddOrd_monotone; auto with ord. }
  assert (Hlt : ω ⊕ expOrd ω x < expOrd ω two + expOrd ω x).
  { eapply ord_lt_le_trans; [|exact HA]. apply naddOrd_increasing1; auto. }
  destruct (add_lt _ _ _ Hlt) as [H1|[r Hr]].
  - right. intro p. apply (ord_lt_irreflexive (expOrd ω two)).
    eapply ord_le_lt_trans; [|exact H1].
    rewrite (HP2 p). apply naddOrd_le2.
  - set (j := ordSize (expOrd ω x) r) in Hr.
    assert (Hj : j < expOrd ω x) by apply index_lt.
    rewrite (expOrd_unfold ω x) in Hj. apply lub_lt in Hj.
    destruct Hj as [Hj|Hj].
    + right. apply (Hfin j); auto.
      apply ord_lt_trans with 1; auto with ord.
    + apply sup_lt in Hj. destruct Hj as [[p|] Hj].
      * left. intro np. exact (np p).
      * right. apply (Hfin j); auto.
        eapply ord_lt_le_trans; [exact Hj|]. simpl.
        rewrite expOrd_zero, mulOrd_one_l. reflexivity.
Qed.

Inductive merge_lists {A:Type} : list A -> list A -> list A -> Prop :=
| merge_lists_nil : merge_lists nil nil nil
| merge_lists_left:
    forall x xs ys zs,
           merge_lists xs ys zs ->
           merge_lists (x::xs) ys (x::zs)
| merge_lists_right:
    forall xs y ys zs,
           merge_lists xs ys zs ->
           merge_lists xs (y::ys) (y::zs).

Lemma cantor_denote_nadd_merge:
  forall xs ys zs,
    merge_lists xs ys zs ->
    cantor_denote_nadd xs ⊕ cantor_denote_nadd ys ≈ cantor_denote_nadd zs.
Proof.
  intros xs ys zs H.
  induction H; simpl.
  - rewrite naddOrd_zero_r. reflexivity.
  - rewrite <- naddOrd_assoc.
    rewrite IHmerge_lists.
    reflexivity.
  - rewrite naddOrd_comm.
    rewrite <- naddOrd_assoc.
    rewrite (naddOrd_comm (cantor_denote_nadd ys)).
    rewrite IHmerge_lists.
    reflexivity.
Qed.

Theorem nadd_cantor_sequences (EM:excluded_middle):
  forall xs ys zs,
    merge_lists xs ys zs ->
    forall a b c,
    cantor_sequence a xs ->
    cantor_sequence b ys ->
    cantor_sequence c zs ->
    cantor_denote xs ⊕ cantor_denote ys ≈ cantor_denote zs.
Proof.
  intros xs ys zs Hmerge a b c Hxs Hys Hzs.
  rewrite (cantor_denote_nadd_eq EM xs a); auto.
  rewrite (cantor_denote_nadd_eq EM ys b); auto.
  rewrite (cantor_denote_nadd_eq EM zs c); auto.
  apply cantor_denote_nadd_merge; auto.
  clear -EM. induction zs; simpl; intuition. apply classical.ord_complete; auto.
  clear -EM. induction ys; simpl; intuition. apply classical.ord_complete; auto.
  clear -EM. induction xs; simpl; intuition. apply classical.ord_complete; auto.
Qed.

(** ** The natural sum does not preserve completeness

  The children of [u ⊕ v] are [u i ⊕ v] and [u ⊕ v j].  A directed upper
  bound for one of each kind must be of one of these two kinds, which
  compares the gap below [u] with the gap below [v].  Let [u] have the
  children [0] and, if [P], [1] (so [u] is [1], or [2] if [P]), and let [v]
  have the children [1] and, if [P], [ω] (so [v] is [2], or [ω+1] if [P]).
  Both are complete.  An upper bound for [0 ⊕ v] and [u ⊕ 1] is a child
  indexed by a proof of [P], or [0 ⊕ v] (which needs a child of [v] above
  [u]: [1] refutes [P], [ω] needs [P]), or [u ⊕ 1] (which refutes [P]). *)

Lemma nadd_complete_directed u v :
  complete (u ⊕ v) ->
  forall i j,
    (exists i', u i ⊕ v ≤ u i' ⊕ v /\ u ⊕ v j ≤ u i' ⊕ v) \/
    (exists j', u i ⊕ v ≤ u ⊕ v j' /\ u ⊕ v j ≤ u ⊕ v j').
Proof.
  destruct u as [A f], v as [B g]. intros H i j.
  destruct (complete_directed _ H (inl i) (inr j)) as [[i'|j'] [H1 H2]].
  - left. exists i'. split; auto.
  - right. exists j'. split; auto.
Qed.

Theorem nadd_complete_WEM :
  (forall u v, complete u -> complete v -> complete (u ⊕ v)) ->
  weak_excluded_middle.
Proof.
  intros H P.
  pose (u := ord (option P) (fun o => match o with None => 0 | Some _ => 1 end)).
  pose (v := ord (option P) (fun o => match o with None => 1 | Some _ => ω end)).
  assert (Hu : complete u).
  { unfold u. simpl. split; [|split].
    - intros [p|] [q|].
      + exists (Some p). split; reflexivity.
      + exists (Some p). simpl. split; [reflexivity | apply zero_least].
      + exists (Some q). simpl. split; [apply zero_least | reflexivity].
      + exists None. split; reflexivity.
    - left. exact (inhabits None).
    - intros [p|]; auto with ord. }
  assert (Hv : complete v).
  { unfold v. simpl. split; [|split].
    - intros [p|] [q|].
      + exists (Some p). split; reflexivity.
      + exists (Some p). simpl. split; [reflexivity | apply ord_lt_le, omega_gt1].
      + exists (Some q). simpl. split; [apply ord_lt_le, omega_gt1 | reflexivity].
      + exists None. split; reflexivity.
    - left. exact (inhabits None).
    - intros [p|]; auto with ord. }
  assert (Hu3 : u < ω).
  { apply ord_le_lt_trans with (natOrdSize 2); [|apply (index_lt ω 2%nat)].
    unfold u. rewrite ord_le_unfold. intros [p|]; simpl.
    - apply succ_lt.
    - apply succ_trans. apply zero_least. }
  destruct (nadd_complete_directed u v (H u v Hu Hv) None None)
    as [[[p|] [_ H2]]|[[p|] [H1 _]]].
  - left. intro np. exact (np p).
  - (* u ⊕ 1 ≤ 0 ⊕ v, so u < v *)
    change (u ⊕ 1 ≤ 0 ⊕ v) in H2.
    rewrite naddOrd_zero_l in H2.
    assert (Huv : u < v).
    { eapply ord_lt_le_trans; [|exact H2].
      apply ord_le_lt_trans with (u ⊕ 0); [rewrite naddOrd_zero_r; reflexivity|].
      apply naddOrd_increasing2. apply succ_lt. }
    rewrite ord_lt_unfold in Huv. destruct Huv as [[p|] Hp].
    + left. intro np. exact (np p).
    + right. intro p. apply (ord_lt_irreflexive 1).
      apply ord_lt_le_trans with u; [apply (index_lt u (Some p)) | exact Hp].
  - left. intro np. exact (np p).
  - (* 0 ⊕ v ≤ u ⊕ 1, finite: refutes P *)
    change (0 ⊕ v ≤ u ⊕ 1) in H1.
    right. intro p. apply (ord_lt_irreflexive ω).
    apply ord_lt_le_trans with v; [apply (index_lt v (Some p))|].
    rewrite <- naddOrd_zero_l. rewrite H1.
    apply ord_lt_le.
    apply ord_lt_le_trans with (expOrd ω 1); [|rewrite expOrd_one'; auto with ord].
    apply nadd_closed_con; auto with ord; rewrite expOrd_one'; auto with ord.
Qed.

Theorem nadd_cantor_sequences_dec:
  forall xs ys zs,
    merge_lists xs ys zs ->
    forall a b c,
      each complete xs -> each complete ys -> each complete zs ->
      cantor_sequence_dec a xs ->
      cantor_sequence_dec b ys ->
      cantor_sequence_dec c zs ->
      cantor_denote xs ⊕ cantor_denote ys ≈ cantor_denote zs.
Proof.
  intros xs ys zs Hmerge a b c Hxs Hys Hzs Ha Hb Hc.
  rewrite (cantor_denote_nadd_eq_dec xs a), (cantor_denote_nadd_eq_dec ys b),
    (cantor_denote_nadd_eq_dec zs c); auto.
  apply cantor_denote_nadd_merge; auto.
Qed.


Module incorrect_nmul.

(** * Natural multiplication, a failed attempt.

Actually, it turns out this is not the correct definition. It fails to
distribute over addition, as proved below.
*)

Fixpoint nmulOrd (x:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match x, y with
    | ord A f, ord B g =>
      (supOrd (fun a:A => nmulOrd (f a) y ⊕ y))
      ⊔
      (supOrd (fun b:B => inner (g b) ⊕ x))
    end.

Notation "a ⊗ b" := (nmulOrd a b) (at level 35, right associativity) : ord_scope.

Lemma nmulOrd_unfold (x y:Ord) :
  x ⊗ y =
    (supOrd (fun a:x => x a ⊗ y ⊕ y))
    ⊔
    (supOrd (fun b:y => x ⊗ y b ⊕ x)).
Proof.
  destruct x; destruct y; auto.
Qed.

Global Opaque nmulOrd.

Lemma nmulOrd_comm_le : forall x y,
  x ⊗ y ≤ y ⊗ x.
Proof.
  induction x as [A f]. induction y as [B g].
  rewrite nmulOrd_unfold.
  apply lub_least.
  - apply sup_least; intro a. simpl.
    rewrite H.
    rewrite (nmulOrd_unfold (ord B g) (ord A f)).
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ a).
    auto with ord.
  - apply sup_least; intro b. simpl.
    rewrite H0.
    rewrite (nmulOrd_unfold (ord B g) (ord A f)).
    rewrite <- lub_le1.
    rewrite <- (sup_le _ _ b).
    auto with ord.
Qed.

Lemma nmulOrd_comm x y :
  x ⊗ y ≈ y ⊗ x.
Proof.
  split; apply nmulOrd_comm_le; auto.
Qed.

Lemma nmulOrd_monotone : forall x y a b,
    a ≤ x -> b ≤ y -> a ⊗ b ≤ x ⊗ y.
Proof.
  induction x as [X f].
  induction y as [Y g].
  intros.
  rewrite (nmulOrd_unfold a b).
  apply lub_least.
  - apply sup_least; intro ai.
    rewrite (nmulOrd_unfold (ord X f) (ord Y g)).
    rewrite <- lub_le1.
    generalize (ord_le_subord _ _ H1 ai); intros [x Hx].
    rewrite <- (sup_le _ _ x).
    simpl.
    apply naddOrd_monotone; auto with ord.
  - apply sup_least; intro bi.
    rewrite (nmulOrd_unfold (ord X f) (ord Y g)).
    rewrite <- lub_le2.
    generalize (ord_le_subord _ _ H2 bi); intros [y Hy].
    rewrite <- (sup_le _ _ y).
    simpl.
    apply naddOrd_monotone; auto with ord.
Qed.

Lemma nmulOrd_increasing2 :
  forall x y z1 z2, x < y -> 0 < z1 -> z1 ≤ z2 -> x ⊗ z1 < y ⊗ z2.
Proof.
  intros x y z1 z2 Hxy Hz1 Hzs.
  rewrite ord_lt_unfold in Hxy.
  destruct Hxy as [b Hb].
  rewrite (nmulOrd_unfold y z2).
  rewrite <- lub_le1.
  rewrite <- (sup_le _ _ b).
  apply ord_lt_le_trans with (y b ⊗ z2 ⊕ 1).
  rewrite naddOrd_comm.
  rewrite naddOrd_succ.
  rewrite naddOrd_comm.
  rewrite naddOrd_zero_r.
  rewrite ord_lt_unfold; exists tt. simpl.
  apply nmulOrd_monotone; auto.
  apply naddOrd_monotone; auto with ord.
  rewrite <- Hzs.
  apply succ_least; auto.
Qed.

Lemma nmulOrd_increasing1 :
  forall x y z1 z2, x < y -> 0 < z1 -> z1 ≤ z2 -> z1 ⊗ x < z2 ⊗ y.
Proof.
  intros.
  rewrite (nmulOrd_comm z1 x).
  rewrite (nmulOrd_comm z2 y).
  apply nmulOrd_increasing2; auto.
Qed.

Add Parametric Morphism : nmulOrd with signature
    ord_le ++> ord_le ++> ord_le as nmulOrd_le_mor.
Proof.
  intros. apply nmulOrd_monotone; auto.
Qed.

Add Parametric Morphism : naddOrd with signature
   ord_eq ==> ord_eq ==> ord_eq as nmulOrd_eq_mor.
Proof.
  intros; split; apply naddOrd_le_mor; solve [apply H|apply H0].
Qed.

Lemma nmulOrd_stepl (x y:Ord) (i:x) :
  x i ⊗ y ⊕ y ≤ x ⊗ y.
Proof.
  rewrite (nmulOrd_unfold x y).
  rewrite <- lub_le1.
  rewrite <- (sup_le _ _ i).
  reflexivity.
Qed.

Lemma nmulOrd_stepr (x y:Ord) (i:y) :
  x ⊗ y i ⊕ x ≤ x ⊗ y.
Proof.
  rewrite (nmulOrd_unfold x y).
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ i).
  reflexivity.
Qed.

Lemma nmulOrd_zero x : x ⊗ 0 ≈ 0.
Proof.
  split; auto with ord.
  induction x as [X f].
  rewrite nmulOrd_unfold.
  apply lub_least.
  - apply sup_least; intro a.
    rewrite naddOrd_zero_r.
    apply H.
  - apply sup_least. intros [].
Qed.

Lemma nmulOrd_one x : x ⊗ 1 ≈ x.
Proof.
  induction x as [A f].
  rewrite nmulOrd_unfold.
  split.
  apply lub_least.
  apply sup_least. intro a.
  simpl.
  rewrite (H a).
  rewrite naddOrd_comm.
  rewrite naddOrd_succ.
  rewrite naddOrd_comm.
  rewrite naddOrd_zero_r.
  apply succ_least.
  apply (index_lt _ a).
  apply sup_least. simpl; intro.
  rewrite nmulOrd_zero.
  rewrite naddOrd_comm.
  rewrite naddOrd_zero_r.
  auto with ord.

  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ tt).
  simpl.
  rewrite nmulOrd_zero.
  rewrite naddOrd_comm.
  rewrite naddOrd_zero_r.
  auto with ord.
Qed.

Lemma nmulOrd_succ: forall x y,
  succOrd x ⊗ y ≈ x ⊗ y ⊕ y.
Proof.
  intro x. induction y using ordinal_induction.
  split.
  - rewrite (nmulOrd_unfold (succOrd x) y).
    apply lub_least.
    + apply sup_least. simpl. intro; auto with ord.
    + apply sup_least. simpl; intros.
      rewrite H; auto with ord.
      rewrite naddOrd_succ2.
      apply succ_least.
      rewrite naddOrd_comm.
      rewrite naddOrd_assoc.
      apply ord_lt_le_trans with ((x ⊕ x ⊗ y a) ⊕ y).
      { apply naddOrd_increasing2; auto with ord. }
      apply naddOrd_monotone; auto with ord.
      rewrite (nmulOrd_unfold x y).
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ a).
      rewrite naddOrd_comm.
      reflexivity.
  - rewrite (nmulOrd_unfold (succOrd x) y).
    rewrite <- lub_le1. simpl.
    rewrite <- (sup_le _ _ tt). reflexivity.
Qed.

Lemma nmulDistrib1 : forall x y z,
  x ⊗ (y ⊕ z) ≤ (x ⊗ y) ⊕ (x ⊗ z).
Proof.
  induction x as [x Hindx] using ordinal_induction.
  induction y as [y Hindy] using ordinal_induction.
  induction z as [z Hindz] using ordinal_induction.
  rewrite (nmulOrd_unfold x (y⊕z)).
  apply lub_least.
  + apply sup_least; intro i.
    rewrite (Hindx (x i)); auto with ord.
    transitivity ((x i ⊗ y ⊕ y) ⊕ (x i ⊗ z ⊕ z)).
    rewrite naddOrd_assoc.
    rewrite (naddOrd_comm _ y).
    rewrite naddOrd_assoc.
    rewrite (naddOrd_comm y _).
    repeat rewrite naddOrd_assoc.
    reflexivity.
    apply naddOrd_monotone; apply nmulOrd_stepl.
  + apply sup_least.
    rewrite (naddOrd_unfold y z).
    rewrite lub_unfold. simpl.
    intros [i|i].
    * rewrite (Hindy (y i)); auto with ord.
      rewrite (naddOrd_comm _ x).
      rewrite naddOrd_assoc.
      apply naddOrd_monotone; auto with ord.
      rewrite naddOrd_comm.
      apply nmulOrd_stepr.
    * rewrite (Hindz (z i)); auto with ord.
      rewrite <- naddOrd_assoc.
      apply naddOrd_monotone; auto with ord.
      apply nmulOrd_stepr.
Qed.

Definition Q : Ord :=
      supOrd (fun (n:ω) => iter_f (nmulOrd ω) 1 n).

Lemma nmul_distrib_counterexample:
  ω ⊗ (Q ⊕ Q) < ω ⊗ Q ⊕ ω ⊗ Q.
Proof.
  apply ord_le_lt_trans with (Q ⊕ ω ⊗ Q).
  2: { apply naddOrd_increasing1.
       rewrite nmulOrd_unfold.
       rewrite <- lub_le1.
       rewrite <- (sup_le _ _ 1%nat). simpl.
       rewrite nmulOrd_comm.
       rewrite nmulOrd_one.
       apply ord_le_lt_trans with (Q ⊕ 0).
       apply naddOrd_zero_r.
       apply naddOrd_increasing2.
       unfold Q.
       rewrite <- (sup_le _ _ 0%nat); simpl; auto with ord. }

  rewrite nmulOrd_unfold.
  apply lub_least.
  - apply sup_least; simpl; intro.
    rewrite naddOrd_comm.
    repeat rewrite <- naddOrd_assoc.
    apply naddOrd_monotone; auto with ord.
    rewrite (nmulOrd_unfold ω).
    rewrite <- lub_le1.
    rewrite <- (sup_le _ _ (a*2)%nat).
    simpl.
    rewrite naddOrd_comm.
    repeat rewrite <- naddOrd_assoc.
    apply naddOrd_monotone; auto with ord.
    induction a; simpl.
    + rewrite nmulOrd_comm. rewrite nmulOrd_zero.
      rewrite nmulOrd_comm. rewrite nmulOrd_zero.
      reflexivity.
    + repeat rewrite nmulOrd_succ.
      repeat rewrite <- naddOrd_assoc.
      apply naddOrd_monotone; auto with ord.
  - apply sup_least. simpl; intros.
    assert (Ha : a < Q ⊕ Q).
    { auto with ord. }
    rewrite naddOrd_unfold in Ha.
    apply lub_lt in Ha.
    destruct Ha.
    + rewrite ord_lt_unfold in H. simpl in H.
      destruct H as [b Ha].
      assert (Hb : b < Q).
      { auto with ord. }
      unfold Q in Hb.
      apply sup_lt in Hb.
      destruct Hb as [n Hb].
      rewrite Ha.
      rewrite nmulDistrib1.
      rewrite naddOrd_comm.
      rewrite naddOrd_assoc.
      apply naddOrd_monotone; auto with ord.
      transitivity (ω ⊗ iter_f (nmulOrd ω) 1 n).
      rewrite naddOrd_comm.
      rewrite (nmulOrd_unfold _ (iter_f _ _ _)).
      rewrite <- lub_le2.
      rewrite ord_lt_unfold in Hb.
      destruct Hb as [q Hb].
      rewrite <- (sup_le _ _ q).
      unfold Q in *. rewrite Hb.
      reflexivity.
      unfold Q.
      rewrite <- (sup_le _ _ (S n)).
      simpl.
      reflexivity.
    + rewrite ord_lt_unfold in H. simpl in H.
      destruct H as [b Ha].
      assert (Hb : b < Q).
      { auto with ord. }
      unfold Q in Hb.
      apply sup_lt in Hb.
      destruct Hb as [n Hb].
      rewrite Ha.
      rewrite nmulDistrib1.
      rewrite naddOrd_comm.
      rewrite (naddOrd_comm _ (ω ⊗ sz b)).
      rewrite naddOrd_assoc.
      apply naddOrd_monotone; auto with ord.
      transitivity (ω ⊗ iter_f (nmulOrd ω) 1 n).
      rewrite naddOrd_comm.
      rewrite (nmulOrd_unfold _ (iter_f _ _ _)).
      rewrite <- lub_le2.
      rewrite ord_lt_unfold in Hb.
      destruct Hb as [q Hb].
      rewrite <- (sup_le _ _ q).
      unfold Q in *. rewrite Hb.
      reflexivity.
      unfold Q.
      rewrite <- (sup_le _ _ (S n)).
      simpl.
      reflexivity.
Qed.

Theorem nmul_not_distributive:
  ~(forall x y z, x ⊗ (y ⊕ z) ≈ (x ⊗ y) ⊕ (x ⊗ z)).
Proof.
  intro H.
  generalize nmul_distrib_counterexample.
  rewrite H. apply ord_lt_irreflexive.
Qed.

End incorrect_nmul.



(** * Jacobsthal multiplication.
      This is the transfinite iteration of natural addition.
  *)

Fixpoint jmulOrd (a:Ord) (b:Ord) : Ord :=
    match b with
    | ord B g => supOrd (fun i:B => (jmulOrd a (g i)) ⊕ a)
    end.

Notation "a × b" := (jmulOrd a b) (at level 35, right associativity) : ord_scope.

Lemma jmulOrd_unfold (a:Ord) (b:Ord) :
  a × b =
  supOrd (fun i:b => a × (b i) ⊕ a).
Proof.
  destruct b as [B g]; simpl; auto.
Qed.

Lemma jmulOrd_monotone1 : forall z a b , a ≤ b -> a × z ≤ b × z.
Proof.
  induction z as [C h Hz].
  simpl; intros.
  apply sup_least. intro c. simpl.
  rewrite <- (sup_le _ _ c).
  apply naddOrd_monotone; auto.
Qed.

Lemma jmulOrd_monotone2 : forall b a z, b ≤ z -> a × b ≤ a × z.
Proof.
  induction b as [B g Hb].
  intros.
  destruct a as [A f]; simpl in *.
  apply sup_least. intro i.
  rewrite ord_le_unfold in H.
  specialize (H i).
  simpl in H.
  rewrite ord_lt_unfold in H.
  destruct H as [q ?].
  specialize (Hb i).
  generalize (Hb (ord A f) (z q) H).
  intros.
  rewrite (jmulOrd_unfold (ord A f) z).
  rewrite <- (sup_le _ _ q).
  rewrite H0. reflexivity.
Qed.

Lemma jmulOrd_increasing2 : forall a b c,
    0 < a ->
    b < c ->
    a × b < a × c.
Proof.
  intros a b [C h] Ha H.
  rewrite (jmulOrd_unfold a (ord C h)).
  simpl.
  rewrite ord_lt_unfold in H.
  destruct H as [c Hc]. simpl in Hc.
  rewrite <- (sup_le _ _ c).
  apply ord_le_lt_trans with (jmulOrd a (h c)); [ apply jmulOrd_monotone2 ; assumption | ].
  apply ord_le_lt_trans with (naddOrd (jmulOrd a (h c)) zeroOrd).
  - rewrite naddOrd_zero_r. reflexivity.
  - apply naddOrd_increasing2. auto.
Qed.

Add Parametric Morphism : jmulOrd with signature
    ord_le ++> ord_le ++> ord_le as jmulOrd_le_mor.
Proof.
  intros.
  apply ord_le_trans with (x × y0).
  apply jmulOrd_monotone2; auto.
  apply jmulOrd_monotone1; auto.
Qed.

Add Parametric Morphism : jmulOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as jmulOrd_eq_mor.
Proof.
  unfold ord_eq; intuition; apply jmulOrd_le_mor; auto.
Qed.


Lemma jmulOrd_zero_r : forall a, a × 0 ≈ 0.
Proof.
  intros; split.
  - destruct a as [A f]. simpl.
    apply sup_least. intuition.
  - apply zero_least.
Qed.

Lemma jmulOrd_zero_l : forall a, 0 × a ≈ 0.
Proof.
  induction a as [A f Ha].
  split; simpl.
  - apply sup_least; intro x.
    rewrite naddOrd_zero_r.
    apply Ha.
  - apply zero_least.
Qed.

Lemma jmulOrd_succ : forall a b, a × (succOrd b) ≈ (a × b) ⊕ a.
Proof.
  intros; split; simpl.
  - apply sup_least; auto with ord.
  - rewrite <- (sup_le _ _ tt); auto with ord.
Qed.

Lemma jmulOrd_one : forall a, a × 1 ≈ a.
Proof.
  intro.
  rewrite jmulOrd_succ.
  rewrite jmulOrd_zero_r.
  rewrite naddOrd_comm.
  rewrite naddOrd_zero_r.
  reflexivity.
Qed.

Lemma jmulOrd_positive : forall a b,
    zeroOrd < a ->
    zeroOrd < b ->
    zeroOrd < a × b.
Proof.
  intros.
  destruct a as [A f].
  destruct b as [B g].
  simpl.
  rewrite ord_lt_unfold in H.
  rewrite ord_lt_unfold in H0.
  destruct H as [a _].
  destruct H0 as [b _].
  simpl in *.
  rewrite <- (sup_le _ _ b).
  rewrite <- naddOrd_le2.
  rewrite ord_lt_unfold. exists a.
  auto with ord.
Qed.

Lemma jmulOrd_limit : forall a b,
    limitOrdinal b ->
    a × b ≈ supOrd (fun i:b => a × (b i)).
Proof.
  destruct b as [B g]; simpl; intros.
  split.
  - apply sup_least. intro b.
    destruct H as [_ H].
    destruct (H b) as [b' Hb'].
    rewrite <- (sup_le _ _ b').
    apply ord_le_trans with (jmulOrd a (succOrd (g b))).
    apply (jmulOrd_succ a (g b)).
    apply jmulOrd_monotone2.
    apply succ_least; auto.
  - apply sup_least. intro b.
    rewrite <- (sup_le _ _ b).
    apply naddOrd_le1.
Qed.

Lemma jmulOrd_continuous a : strongly_continuous (jmulOrd a).
Proof.
  red; simpl; intros.
  apply sup_least.
  intros [i q]. simpl.
  rewrite <- (sup_le _ _ i).
  rewrite (jmulOrd_unfold a (f i)).
  rewrite <- (sup_le _ _ q).
  reflexivity.
Qed.

Definition smash_sum (x y:Ord) :=
  limOrd (fun i => x (fst i) ⊕ y (snd i)).

Lemma smash_sum_zero_l : forall x, smash_sum 0 x ≈ 0.
Proof.
  intro x. split; auto with ord.
  unfold smash_sum.
  rewrite ord_le_unfold. simpl.
  intros [[] _].
Qed.

Lemma smash_sum_zero_r : forall x, smash_sum x 0 ≈ 0.
Proof.
  intro x. split; auto with ord.
  unfold smash_sum.
  rewrite ord_le_unfold.
  intros [_ []].
Qed.

Lemma smash_sum_one_l: forall x, smash_sum 1 x ≈ x.
Proof.
  intro x. split.
  - apply limit_least. intros [[] i]; simpl.
    rewrite naddOrd_zero_l. auto with ord.
  - rewrite ord_le_unfold. intro i.
    rewrite ord_lt_unfold. simpl.
    exists (tt, i). simpl.
    rewrite naddOrd_zero_l. auto with ord.
Qed.

Lemma smash_sum_one_r: forall x, smash_sum x 1 ≈ x.
Proof.
  intro x. split.
  - apply limit_least. intros [i []]; simpl.
    rewrite naddOrd_zero_r. auto with ord.
  - rewrite ord_le_unfold. intro i.
    rewrite ord_lt_unfold. simpl.
    exists (i, tt). simpl.
    rewrite naddOrd_zero_r. auto with ord.
Qed.

Lemma smash_sum_sym_le: forall x y, smash_sum x y <= smash_sum y x.
Proof.
  unfold smash_sum. intros.
  rewrite ord_le_unfold. intros [a b].
  rewrite ord_lt_unfold. exists (b,a).
  simpl.
  apply naddOrd_comm.
Qed.

Lemma smash_sum_sym: forall x y, smash_sum x y ≈ smash_sum y x.
Proof.
  intros; split; apply smash_sum_sym_le.
Qed.

Lemma smash_sum_assoc1: forall x y z, smash_sum x (smash_sum y z) <= smash_sum (smash_sum x y) z.
Proof.
  unfold smash_sum; simpl. intros x y z.
  apply limit_least; intros [a [b c]]. simpl.
  rewrite ord_lt_unfold. simpl.
  exists (a,b,c). simpl.
  apply naddOrd_assoc.
Qed.

Lemma smash_sum_assoc2: forall x y z, smash_sum (smash_sum x y) z <= smash_sum x (smash_sum y z).
Proof.
  unfold smash_sum; simpl. intros x y z.
  apply limit_least; intros [[a b] c]. simpl.
  rewrite ord_lt_unfold. simpl.
  exists (a,(b,c)). simpl.
  apply naddOrd_assoc.
Qed.

Lemma smash_sum_assoc: forall x y z, smash_sum (smash_sum x y) z ≈ smash_sum x (smash_sum y z).
Proof.
  intros; split.
  apply smash_sum_assoc2.
  apply smash_sum_assoc1.
Qed.

Definition iterated_smash_sum (x:Ord) :=
  limOrd (fun xs:list x => List.fold_right (fun x y => sz x ⊕ y) 0 xs).

Lemma iterated_smash_sum_nonzero: forall x, 0 < iterated_smash_sum x.
Proof.
  intros. rewrite ord_lt_unfold. exists nil.
  auto with ord.
Qed.

Lemma iterated_smash_sum_monotone: forall x y,
    x <= y -> iterated_smash_sum x <= iterated_smash_sum y.
Proof.
  intros x y H.
  unfold iterated_smash_sum.
  apply limit_least. intro xs.
  assert (Hys: exists ys: list y, pairwise (fun x y => sz x <= sz y) xs ys).
  { induction xs; simpl.
    - exists nil. apply pairwise_nil.
    - rewrite ord_le_unfold in H.
      specialize (H a). rewrite ord_lt_unfold in H.
      destruct H as [b H].
      destruct IHxs as [ys Hys].
      exists (b::ys).
      constructor; auto.
  }
  destruct Hys as [ys Hys].
  rewrite ord_lt_unfold. simpl.
  exists ys.
  induction Hys; simpl; auto with ord.
  apply naddOrd_monotone; auto with ord.
Qed.

Theorem iterated_smash_sum_eq (x:Ord) :
  iterated_smash_sum x ≈ supOrd (fun i:nat => Nat.iter i (smash_sum x) 1).
Proof.
  split.
  - unfold iterated_smash_sum.
    apply limit_least; intro xs.
    rewrite <- (sup_le _ _ (length xs)).
    induction xs; simpl; auto with ord.
    rewrite ord_lt_unfold in IHxs.
    destruct IHxs as [b Hb]. simpl in *.
    rewrite Hb.
    unfold smash_sum. rewrite ord_lt_unfold; simpl.
    exists (a, b). simpl.
    apply naddOrd_monotone; auto with ord.
  - apply sup_least. intro i.
    induction i; simpl.
    + apply succ_least. unfold iterated_smash_sum.
      rewrite ord_lt_unfold; simpl.
      exists nil. auto with ord.
    + unfold smash_sum. apply limit_least. simpl.
      intros [a q]. simpl.
      rewrite ord_le_unfold in IHi.
      specialize (IHi q).
      rewrite ord_lt_unfold in IHi. unfold iterated_smash_sum in IHi.
      simpl in IHi.
      destruct IHi as [xs Hxs].
      rewrite Hxs.
      unfold iterated_smash_sum.
      rewrite ord_lt_unfold; simpl.
      exists (a::xs). simpl.
      auto with ord.
Qed.

Fixpoint tree_selection (x:Ord) :=
  match x with
  | ord A f => iterated_smash_sum (ord A (fun a => tree_selection (f a)))
  end.

Lemma tree_selection_unfold: forall x,
    tree_selection x = iterated_smash_sum (limOrd (fun a:x => tree_selection a)).
Proof.
  intros [A f]. simpl. reflexivity.
Qed.

Lemma tree_selection_nonzero: forall x, 0 < tree_selection x.
Proof.
  intros [A f]; simpl. apply iterated_smash_sum_nonzero.
Qed.

Lemma tree_selection_monotone: forall x y,
    x <= y -> tree_selection x <= tree_selection y.
Proof.
  induction x as [A f Hx]; intros [B g]; simpl; intro H.
  apply iterated_smash_sum_monotone.
  apply limit_least; intro a.
  rewrite ord_le_unfold in H.
  specialize (H a).
  rewrite ord_lt_unfold in H.
  destruct H as [b H].
  rewrite ord_lt_unfold. simpl.
  exists b.
  auto.
Qed.

Lemma tree_selection_increasing: forall x y,
    x < y -> tree_selection x < tree_selection y.
Proof.
  intros x [Y g] H.
  rewrite ord_lt_unfold in H.
  destruct H as [b Hb].
  simpl. unfold iterated_smash_sum. simpl.
  rewrite ord_lt_unfold. simpl.
  exists [b]. simpl.
  rewrite naddOrd_zero_r.
  apply tree_selection_monotone; auto.
Qed.

Lemma tree_selection_scott_continuous:
  scott_continuous tree_selection.
Proof.
  hnf; simpl; intros.
  rewrite sup_unfold. simpl.
  unfold iterated_smash_sum. simpl.
  apply limit_least. simpl.
  intros xs. destruct xs as [|x xs].
  { simpl. rewrite <- (sup_le _ _ a0).
    apply tree_selection_nonzero. }
  assert (exists i:A, Forall (fun x => f (projT1 x) <= f i) (x::xs)).
  { induction xs; simpl.
    - exists (projT1 x). constructor; auto with ord.
    - destruct IHxs as [i Hi].
      destruct (H i (projT1 a)) as [j [Hj1 Hj2]].
      exists j.
      constructor; auto. inversion Hi; subst.
      rewrite H3. auto.
      constructor; auto with ord.
      inversion Hi; subst.
      clear -H4 Hj1.
      induction xs; simpl; auto with ord.
      inversion H4; subst.
      constructor; auto.
      rewrite H1; auto. }
  destruct H1 as [i Hi].
  rewrite <- (sup_le _ _ i).
  case_eq (f i). intros Q g HQ.
  simpl tree_selection.
  rewrite HQ in Hi.
  unfold iterated_smash_sum.
  rewrite ord_lt_unfold. simpl.

  assert (Hqs: exists qs: list Q, pairwise (fun x q => ordSize (f (projT1 x)) (projT2 x) <= g q) (x::xs) qs).
  { revert Hi; clear.
    generalize (x::xs). intros l H.
    induction H.
    { exists []. constructor. }
    destruct IHForall as [qs Hqs].
    destruct x0 as [a z]. simpl in *.
    rewrite ord_le_unfold in H.
    specialize (H z). rewrite ord_lt_unfold in H.
    destruct H as [q Hq].
    exists (q::qs). constructor; simpl; auto. }
  destruct Hqs as [qs Hqs].
  exists qs. simpl.
  inversion Hqs; subst.
  simpl. apply naddOrd_monotone.
  apply tree_selection_monotone; auto.
  clear -H5.
  induction H5; simpl; auto with ord.
  apply naddOrd_monotone; auto.
  apply tree_selection_monotone; auto.
Qed.

Lemma tree_selection_complete: forall x,
    complete x ->
    complete (tree_selection x).
Proof.
  induction x as [A f Hind]; simpl.
  repeat split.
  - hnf; simpl; intros.
    exists (a1 ++ a2). split.
    + induction a1; simpl; auto with ord.
      apply naddOrd_monotone; auto with ord.
    + induction a1; simpl; auto with ord.
      rewrite <- naddOrd_le2. auto with ord.
  - left. apply (inhabits nil).
  - (* This cannot be completed constructively: see
       [tree_selection_complete_WEM] below. *)
Abort.

(** Classicaly, at least, the `tree_selection` function is normal. This means
    it has has fixpoints, as all normal functions do. I suspect it behaves
    in a similar way to the standard `expOrd ω x` function. In particular,
    I suspect that the least fixpoint of both functions coincide, as ε(0).
    (Indeed, on complete ordinals the two functions agree, constructively:
    see [tree_selection_eq_powOmega_complete] below.)

    I find this result quite surprising, as the natural addition operation
    is not continuous in either of it's arguments.

    However, this proof requires the excluded middle: preserving
    completeness is not constructive ([tree_selection_complete_WEM]
    below), because natural sums of complete ordinals need not be complete
    ([nadd_complete_WEM]).
*)
Lemma normal_tree_selection (EM:excluded_middle): normal_function tree_selection.
Proof.
  constructor.
  - intros; apply tree_selection_monotone; auto.
  - intros; apply tree_selection_increasing; auto.
  - apply tree_selection_scott_continuous.
  - intros. apply (classical.ord_complete EM).
  - intros. apply tree_selection_nonzero.
Qed.

Lemma powOmega_le_tree_selection: forall x,
    expOrd ω x ≤ tree_selection x.
Proof.
  induction x as [x Hindx] using ordinal_induction.
  rewrite expOrd_unfold. apply lub_least.
  { apply succ_least. apply tree_selection_nonzero. }
  apply sup_least; intro q.
  rewrite mulOrd_unfold.
  apply sup_least; intro i. simpl.
  rewrite tree_selection_unfold.
  unfold iterated_smash_sum. simpl.
  apply ord_lt_le.
  rewrite ord_lt_unfold.
  exists (List.repeat q (S i)). simpl.
  rewrite naddOrd_comm.
  rewrite add_nadd_le.
  apply naddOrd_monotone; auto with ord.
  induction i; simpl; auto with ord.
  - rewrite mulOrd_zero_r. auto with ord.
  - rewrite mulOrd_succ.
    rewrite naddOrd_comm.
    rewrite add_nadd_le.
    apply naddOrd_monotone; auto with ord.
Qed.

(** For complete [x], the bound holds constructively: the only uses of
    classical logic were to make the children of [x] directed and to add
    equal powers, and completeness provides both ([nadd_add_same_powers_con]). *)
Lemma tree_selection_le_powOmega_complete : forall x,
    complete x -> tree_selection x ≤ expOrd ω x.
Proof.
  induction x as [x Hindx] using ordinal_induction.
  intro Hx.
  rewrite tree_selection_unfold. unfold iterated_smash_sum.
  apply limit_least; simpl; intros xs.
  case_eq xs.
  { intros. subst. simpl. auto with ord. }
  intros o l Hxs.
  rewrite <- Hxs.
  rewrite expOrd_unfold.
  rewrite <- lub_le2.
  assert (exists i:x, Forall (fun x => sz x <= sz i) xs).
  { subst xs.
    induction l; simpl.
    { exists o. constructor; auto with ord. }
    destruct IHl as [i Hi].
    inversion Hi; subst.
    destruct (complete_directed x Hx i a) as [k [??]].
    exists k.
    constructor. rewrite H1; auto.
    constructor; auto.
    clear Hi.
    induction H2; simpl; intuition.
    constructor; auto with ord.
    rewrite H2; auto. }
  clear o l Hxs.
  destruct H as [i Hi].
  rewrite <- (sup_le _ _ i).
  rewrite mulOrd_unfold.
  rewrite <- (sup_le _ _ (length xs)).
  apply ord_le_lt_trans with
    (expOrd ω (x i) * (natOrdSize (length xs)) + 0).
  2:{ apply addOrd_increasing; auto with ord. }
  rewrite addOrd_zero_r.
  induction Hi.
  { simpl. auto with ord. }
  replace (length (x0::l)) with (1+length l)%nat by (simpl; auto with ord).
  rewrite <- nadd_add_same_powers_con; auto with ord.
  simpl.
  rewrite IHHi.
  rewrite Hindx; auto with ord.
  rewrite mulOrd_one_r.
  apply naddOrd_monotone; auto with ord.
Qed.

Lemma tree_selection_le_powOmega (EM:excluded_middle) : forall x,
    tree_selection x ≤ expOrd ω x.
Proof.
  intro x. apply tree_selection_le_powOmega_complete.
  apply classical.ord_complete; auto.
Qed.

Theorem tree_selection_eq_powOmega_complete :
  forall x, complete x -> tree_selection x ≈ expOrd ω x.
Proof.
  intros; split.
  apply tree_selection_le_powOmega_complete; auto.
  apply powOmega_le_tree_selection.
Qed.

Theorem tree_selection_eq_powOmega (EM:excluded_middle) :
  forall x, tree_selection x ≈ expOrd ω x.
Proof.
  intros; apply tree_selection_eq_powOmega_complete.
  apply classical.ord_complete; auto.
Qed.

(** [tree_selection] does not preserve completeness either.  Let [a] be
    the ordinal [u] above ([1], or [2] if [P]), and let [x] have the
    children [a] and [2]; [x] is complete.  The child [ts a ⊕ (ts 2 ⊕ 0)]
    of [ts x] is a natural sum of [ω^a] and [ω^2], and an upper bound for
    its children [0 ⊕ ω^2] and [ts a ⊕ ω] is either [n ⊕ ω^2] for a child
    [n] of [ts a] (one that is finite refutes [P]; the others need [P]),
    or [ts a ⊕ y] for some [y < ω^2], which refutes [~P]. *)

Lemma tree_selection_finite_or (P:Prop) (f:option P -> Ord) :
  f None ≈ 0 ->
  forall l : list (option P),
    P \/ List.fold_right (fun o y => tree_selection (f o) ⊕ y) 0 l < ω.
Proof.
  intros Hf. induction l as [|[p|] l IH]; simpl.
  - right. auto with ord.
  - left. exact p.
  - destruct IH as [p|IH]; [left; exact p|right].
    assert (H0 : tree_selection (f None) < ω).
    { rewrite (tree_selection_monotone _ _ (proj1 Hf)).
      rewrite tree_selection_eq_powOmega_complete; auto with ord.
      rewrite expOrd_zero. auto with ord. }
    apply ord_lt_le_trans with (expOrd ω 1); [|rewrite expOrd_one'; auto with ord].
    apply nadd_closed_con; auto with ord;
      rewrite expOrd_one'; auto with ord.
Qed.

Theorem tree_selection_complete_WEM :
  (forall x, complete x -> complete (tree_selection x)) ->
  weak_excluded_middle.
Proof.
  intros H P.
  pose (a := ord (option P) (fun o => match o with None => 0 | Some _ => 1 end)).
  pose (two := succOrd 1).
  pose (x := ord bool (fun b => if b then a else two)).
  assert (Ha : complete a).
  { unfold a. simpl. split; [|split].
    - intros [p|] [q|].
      + exists (Some p). split; reflexivity.
      + exists (Some p). simpl. split; [reflexivity | apply zero_least].
      + exists (Some q). simpl. split; [apply zero_least | reflexivity].
      + exists None. split; reflexivity.
    - left. exact (inhabits None).
    - intros [p|]; auto with ord. }
  assert (Ha2 : a ≤ two).
  { unfold a, two. rewrite ord_le_unfold. intros [p|]; simpl.
    - apply succ_lt.
    - apply succ_trans. apply zero_least. }
  assert (Hx : complete x).
  { unfold x. simpl. split; [|split].
    - intros b1 b2. exists false.
      destruct b1, b2; simpl; split; auto with ord.
    - left. exact (inhabits true).
    - intros []; unfold two; auto with ord. }
  set (A := tree_selection a). set (B := tree_selection two).
  assert (HA : A ≈ expOrd ω a) by (apply tree_selection_eq_powOmega_complete; auto).
  assert (HB : B ≈ expOrd ω two) by (apply tree_selection_eq_powOmega_complete; unfold two; auto with ord).
  assert (Hw2 : ω < expOrd ω two).
  { apply ord_le_lt_trans with (expOrd ω 1).
    - rewrite expOrd_one'; auto with ord.
    - apply expOrd_increasing; auto with ord. }
  assert (HcB : forall y, y < B -> ω ⊕ y < B).
  { intros y Hy. rewrite HB in *. apply nadd_closed_con; unfold two; auto with ord. }
  (* the child of ts x for the list [a; 2] *)
  assert (Hc : complete (A ⊕ (B ⊕ 0))).
  { generalize (complete_subord _ (H x Hx) (true :: false :: nil)). simpl. auto. }
  (* a child of B ⊕ 0 equivalent to ω *)
  set (j := (inl (tt :: nil) : ordCarrier (B ⊕ 0))).
  assert (Hj : ω ≤ ordSize (B ⊕ 0) j).
  { change (ω ≤ (tree_selection 1 ⊕ 0) ⊕ 0).
    rewrite naddOrd_zero_r, naddOrd_zero_r.
    rewrite tree_selection_eq_powOmega_complete; auto with ord.
    rewrite expOrd_one'; auto with ord. }
  destruct (nadd_complete_directed A (B ⊕ 0) Hc nil j) as [[l [_ H2]]|[m [H1 _]]].
  - (* an upper bound n ⊕ ω^2 with n a child of ts a *)
    change (A ⊕ ordSize (B ⊕ 0) j ≤
            List.fold_right (fun o y => tree_selection (match o with None => 0 | Some _ => 1 end) ⊕ y) 0 l
              ⊕ (B ⊕ 0)) in H2.
    destruct (tree_selection_finite_or P (fun o => match o with None => 0 | Some _ => 1 end)
                (ord_eq_refl _) l) as [p|Hl].
    + left. intro np. exact (np p).
    + right. intro p.
      (* under P: ω^2 ⊕ ω ≤ A ⊕ ω ≤ n ⊕ ω^2 < ω ⊕ ω^2 *)
      apply (ord_lt_irreflexive (ω ⊕ B)).
      apply ord_le_lt_trans with (B ⊕ ω).
      { rewrite naddOrd_comm. reflexivity. }
      apply ord_le_lt_trans with (A ⊕ ordSize (B ⊕ 0) j).
      { apply naddOrd_monotone; auto.
        rewrite HA, HB. apply expOrd_monotone. unfold two. apply succ_least.
        apply (index_lt a (Some p)). }
      rewrite H2. rewrite naddOrd_zero_r.
      apply naddOrd_increasing1; auto.
  - (* an upper bound ts a ⊕ y with y < ω^2 *)
    change (0 ⊕ (B ⊕ 0) ≤ A ⊕ ordSize (B ⊕ 0) m) in H1.
    left. intro np.
    assert (Hy : ordSize (B ⊕ 0) m < B).
    { rewrite <- (naddOrd_zero_r B) at 2. apply index_lt. }
    set (y := ordSize (B ⊕ 0) m) in *. clearbody y.
    apply (ord_lt_irreflexive B).
    apply ord_le_lt_trans with (ω ⊕ y); [|apply HcB; auto].
    rewrite <- (naddOrd_zero_r B) at 1. rewrite <- naddOrd_zero_l.
    rewrite H1. apply naddOrd_monotone; [|reflexivity].
    rewrite HA. rewrite <- (expOrd_one' ω) at 2; auto with ord.
    apply expOrd_monotone.
    unfold a. rewrite ord_le_unfold. intros [p|]; simpl.
    + elim (np p).
    + apply succ_lt.
Qed.

(** Consequently completeness is not invariant under ≈: for complete [x],
    [tree_selection x] and [ω^x] are equivalent, and the second is
    complete.  ([classical.complete_intensional_EM] gives the stronger
    conclusion EM from a simpler witness.) *)
Corollary complete_intensional_WEM :
  (forall x y, x ≈ y -> complete x -> complete y) ->
  weak_excluded_middle.
Proof.
  intro H. apply tree_selection_complete_WEM.
  intros x Hx. apply H with (expOrd ω x).
  - symmetry. apply tree_selection_eq_powOmega_complete; auto.
  - apply expOrd_complete; auto with ord.
Qed.
