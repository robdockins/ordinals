Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.

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

Lemma naddOrd_zero x : x ≈ x ⊕ 0.
Proof.
  split.
  - induction x as [A f].
    rewrite naddOrd_unfold.
    simpl.
    rewrite ord_le_unfold; simpl; intros.
    rewrite <- lub_le1.
    eapply ord_le_lt_trans; [ | apply (limit_lt _ _ a) ].
    simpl; apply H.
  - induction x as [A f].
    rewrite naddOrd_unfold.
    apply lub_least.
    apply limit_least; intros.
    rewrite H. apply limit_lt.
    apply limit_least; intros [].
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
  rewrite <- naddOrd_zero.
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

Require Import Lia.

Lemma mulOmega_fix: forall a,
  a * ω ≈ a + a * ω.
Proof.
  split.
  apply addOrd_le2.
  transitivity (a + a * (supOrd (fun i:ω => i))).
  { apply addOrd_monotone; auto with ord.
    apply mulOrd_monotone2.
    rewrite ord_le_unfold; intro i.
    rewrite <- (sup_le _ _ (S i)).
    simpl. apply succ_lt. }
  transitivity (a + supOrd (fun i:ω => a * i)).
  { apply addOrd_monotone; auto with ord.
    apply mulOrd_continuous.
    exact O. }
  transitivity (supOrd (fun i:ω => a + a * i)).
  { apply addOrd_continuous. exact O. }
  apply sup_least; intro i.
  rewrite (mulOrd_unfold a ω).
  rewrite <- (sup_le _ _ i).
  simpl.
  induction i; simpl.
  - rewrite mulOrd_zero_r.
    rewrite addOrd_zero_l.
    rewrite addOrd_zero_r.
    reflexivity.
  - repeat rewrite mulOrd_succ.
    rewrite addOrd_assoc.
    rewrite IHi.
    reflexivity.
Qed.

Lemma mulOmega_eat_fin: forall a (n:ω) c,
  c ≤ a * ω ->
  a * n + c ≤ a * ω.
Proof.
  induction n; simpl; intros.
  - rewrite mulOrd_zero_r.
    rewrite addOrd_zero_l.
    auto.
  - rewrite mulOrd_succ.
    rewrite <- addOrd_assoc.
    apply IHn.
    rewrite mulOmega_fix.
    apply addOrd_monotone; auto with ord.
Qed.


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

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
    rewrite <- naddOrd_zero.
    auto. }
  rewrite expOrd_unfold in Hy.
    apply lub_lt in Hy.
    destruct Hy as [Hy|Hy].
    { rewrite ord_lt_unfold in Hy.
      destruct Hy as [[] Hy].
      simpl in Hy.
      rewrite Hy.
      rewrite <- naddOrd_zero.
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
    apply complete_subord; auto.
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
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
  simpl. reflexivity.
  destruct n. rewrite mulOrd_zero_r.
  rewrite <- naddOrd_zero.
  simpl.
  replace (m+0)%nat with m by lia.
  reflexivity.
  replace (S m + S n)%nat with (m+n+2)%nat by lia.
  apply nadd_add_same_powers_step; auto.
  intros. apply nadd_closed; auto.
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
    rewrite naddOrd_comm. rewrite <- naddOrd_zero.
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
    rewrite H. auto.
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
  { rewrite naddOrd_comm. rewrite <- naddOrd_zero. reflexivity. }
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

Theorem cantor_denote_nadd_eq (EM:excluded_middle) :
  forall xs x,
    each complete xs ->
    cantor_sequence x xs ->
    cantor_denote xs ≈ cantor_denote_nadd xs.
Proof.
  induction xs as [|x xs IHxs] using List.rev_ind; simpl; auto with ord.
  intros b Hxs Hb.
  apply each_app in Hxs.
  rewrite cantor_denote_app.
  rewrite cantor_denote_nadd_app.
  simpl.
  rewrite addOrd_zero_r.
  rewrite <- naddOrd_zero.
  rewrite <- IHxs with b.
  split.
  apply add_nadd_le.
  apply cantor_denote_nadd_add with x; intuition auto with ord.
  eapply cantor_sequence_le; eauto.
  simpl; auto.
  intuition.
  apply cantor_sequence_app1 in Hb. auto.
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
  - rewrite <- naddOrd_zero. reflexivity.
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


(** * Natural multiplication

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
  rewrite <- naddOrd_zero.
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
    rewrite <- naddOrd_zero.
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
  rewrite <- naddOrd_zero.
  apply succ_least.
  apply (index_lt _ a).
  apply sup_least. simpl; intro.
  rewrite nmulOrd_zero.
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
  auto with ord.

  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ tt).
  simpl.
  rewrite nmulOrd_zero.
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
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

From Ordinal Require Import Fixpoints.

Section distrib_counterexample.

  Let Q : Ord :=
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
         apply naddOrd_zero.
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
        subst Q. rewrite Hb.
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
        subst Q. rewrite Hb.
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

End distrib_counterexample.


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
  - rewrite <- naddOrd_zero. reflexivity.
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
    rewrite <- naddOrd_zero.
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
  rewrite <- naddOrd_zero.
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
  rewrite (naddOrd_zero 0).
  apply ord_le_lt_trans with (ord A f × g b ⊕ 0).
  apply naddOrd_le_mor; apply zero_least.
  apply naddOrd_increasing2.
  rewrite ord_lt_unfold. simpl.
  exists a.
  apply zero_least.
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
