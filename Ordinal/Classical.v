From Coq Require Import ClassicalFacts.
From Coq Require Import Arith.
From Coq Require Import Lia.

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
    induction x as [x Hindx] using ordinal_induction.
    induction y as [y Hindy] using ordinal_induction.

    split.
    * rewrite ord_le_unfold.
      intros.
      destruct (EM (exists a, ~x a < y)).
      + clear H.
        destruct H0 as [a Ha].
        destruct (Hindx (x a) (index_lt x a) y).
        rewrite ord_lt_unfold. exists a. intuition.
      + elim H; intros.
        destruct (EM (x a < y)); auto.
        elim H0; eauto.
    * intros. rewrite ord_le_unfold. intro a.
      destruct (Hindy (y a) (index_lt y a)).
      apply H0.
      intro. apply H.
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

  (** Every indexed collection of classical ordinals is directed, which
      follows easily from the totality of order. *)
  Theorem ord_directed A (f:A -> Ord) : directed A f.
  Proof.
    hnf. intros a1 a2.
    destruct (order_total (f a1) (f a2)).
    - exists a2. split; auto with ord.
    - exists a1. split; auto with ord.
  Qed.

  (** Classical ordinals form a total order, so every ordinal is complete. *)
  Theorem ord_complete (x:Ord) : complete x.
  Proof.
    induction x as [A f]; simpl; intuition.
    + apply ord_directed.
    + apply EM.
  Qed.

  (** Classical ordinals are well-ordered by <=. More precisely,
      every nonempty collection of ordinals (as defined by a predicate)
      has a least element.
   *)
  Lemma ord_well_ordered (P:Ord -> Prop) :
    forall o, P o -> exists o0, P o0 /\ forall o', P o' -> o0 <= o'.
  Proof.
    induction o as [o Hind] using ordinal_induction. intros HP.
    destruct (EM (exists o1, P o1 /\ (o1 < o))).
    - destruct H as [o1 [H H1]].
      apply (Hind o1); auto.
    - exists o. split; auto.
      intros o' Ho'.
      apply ord_swizzle. intro.
      elim H. exists o'. split; auto.
  Qed.

  (** As a consequence, every nonempty indexed collection of ordinals has a least element. *)
  Corollary ord_well_ordered_indexed A (f:A -> Ord) (Hinh:inhabited A) :
    exists a, forall a', f a <= f a'.
  Proof.
    set (P o := exists a, f a = o).
    destruct Hinh as [a].
    assert (Ha : P (f a)).
    { hnf. exists a; auto. }
    destruct (ord_well_ordered P (f a) Ha) as [o0 [Ho0 Hleast]].
    destruct Ho0 as [a0 Ha0]. subst o0.
    exists a0. intros; apply Hleast.
    red. eauto.
  Qed.

  (** Classicaly, we can provide a more traditional induction principle for ordinals
      that has cases for the three classes of ordinal.
    *)
  Lemma classical_ordinal_induction (P:Ord -> Prop) :
    (forall x y, x ≈ y -> P x -> P y) ->
    P 0 ->
    (forall o, P o -> P (succOrd o)) ->
    (forall x, (forall a, a < x -> P a) -> limitOrdinal x -> P x) ->
    forall x, P x.
  Proof.
    intros Heq Hzero Hsucc Hlimit.
    induction x as [x Hind] using ordinal_induction.
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

(** Now, we show some reverse results. In particular, we will show how certain
    reasoning principles about our presentation of ordinals imply non-constructive
    principles. The workhorse of these results will be the truth ordinal,
    which is 0 for a false proposition and 1 for a true proposition. The main
    results follow from the fact that being able to distinguish which of these cases
    holds is equivalant to the excluded middle.
*)

Definition truth_ord (P:Prop) := ord P (fun H => 0).

Lemma truth_ord_false : forall (P:Prop), ~P -> truth_ord P ≈ 0.
Proof.
  intros P H.
  split.
  - rewrite ord_le_unfold. intro H1. simpl in *. contradiction.
  - apply zero_least.
Qed.

Lemma truth_ord_true : forall (P:Prop), P -> truth_ord P ≈ 1.
Proof.
  intros P H.
  split.
  - rewrite ord_le_unfold; simpl; intros.
    apply succ_lt.
  - rewrite ord_le_unfold; simpl; intros.
    unfold truth_ord.
    rewrite ord_lt_unfold. exists H. simpl.
    reflexivity.
Qed.

Lemma zero_dec_EM :
  (forall x, x <= 1 -> x <= 0 \/ 0 < x) ->
  excluded_middle.
Proof.
  intros Hzdec P.
  destruct (Hzdec (truth_ord P)).
  - rewrite ord_le_unfold.
    simpl; intros.
    apply succ_lt.
  - right.
    intro H1.
    destruct (ord_le_subord _ _ H H1) as [[] _].
  - left.
    rewrite ord_lt_unfold in H.
    destruct H; auto.
Qed.

Lemma order_total_EM :
  (forall x y, x <= y \/ y < x) ->
  excluded_middle.
Proof.
  intro; apply zero_dec_EM.
  intros; auto.
Qed.

Lemma complete_EM :
  (forall x, complete x) ->
  excluded_middle.
Proof.
  intro. apply zero_dec_EM.
  intros; apply complete_zeroDec; auto.
Qed.

Lemma ord_well_ordered_WEM :
  (forall (P:Ord -> Prop),
     forall o, P o -> exists o0, P o0 /\ forall o', P o' -> o0 <= o') ->
  weak_excluded_middle.
Proof.
  intros Hwo P.
  set (X o := o = truth_ord P \/ o = truth_ord (~P)).
  assert (X (truth_ord P)) by (hnf; auto).
  destruct (Hwo X _ H) as [x0 [Hx0 Hleast]].
  hnf in Hx0. destruct Hx0; subst x0.
  - right. intro HP.
    assert (truth_ord P <= truth_ord (~P)).
    apply Hleast.
    hnf. auto.
    rewrite ord_le_unfold in H0.
    specialize (H0 HP).
    rewrite ord_lt_unfold in H0.
    destruct H0.
    hnf in x. auto.
  - left; intro HNP.
    assert (truth_ord (~P) <= truth_ord P).
    apply Hleast.
    hnf. auto.
    rewrite ord_le_unfold in H0.
    specialize (H0 HNP).
    rewrite ord_lt_unfold in H0.
    destruct H0.
    hnf in x. auto.
Qed.

Lemma directed_WEM :
  (forall x, directed (ordCarrier x) (ordSize x)) ->
  weak_excluded_middle.
Proof.
  intros H P.
  set (x := ord bool (fun b => if b then truth_ord P else truth_ord (~P))).
  destruct (H x true false) as [b [Hb1 Hb2]]. simpl in *.
  destruct b.
  - left. intro HNP.
    rewrite ord_le_unfold in Hb2.
    generalize (Hb2 HNP).
    rewrite ord_lt_unfold. intros [HP _].
    apply HNP; auto.
  - right. intro HP.
    rewrite ord_le_unfold in Hb1.
    generalize (Hb1 HP).
    rewrite ord_lt_unfold. intros [HNP _].
    apply HNP; auto.
Qed.

Definition truth_ord' (P:Prop) := supOrd (fun n => 1 ⊔ (ord P (fun H => natOrdSize n))).

Lemma truth_ord'_false (P:Prop) : ~P -> truth_ord' P ≈ 1.
Proof.
  intro H. unfold truth_ord'; split.
  - apply sup_least; intro n.
    apply lub_least; auto with ord.
    rewrite ord_le_unfold. simpl; intros.
    elim H; auto.
  - rewrite <- (sup_le _ _ 0%nat).
    apply lub_le1.
Qed.

Lemma truth_ord'_true (P:Prop) : P -> truth_ord' P ≈ ω.
Proof.
  intro H. unfold truth_ord'; split.
  - apply sup_least; intro n.
    apply lub_least; auto with ord.
    rewrite ord_le_unfold. simpl; intros.
    rewrite ord_lt_unfold. exists 0%nat. auto with ord.
    rewrite ord_le_unfold; simpl; intro.
    rewrite ord_lt_unfold. simpl. exists n. auto with ord.
  - rewrite ord_le_unfold; intro n.
    rewrite <- (sup_le _ _ n).
    rewrite <- lub_le2.
    rewrite ord_lt_unfold. exists H. simpl.
    auto with ord.
Qed.

Lemma truth_ord'_complete P : complete (truth_ord' P).
Proof.
  unfold truth_ord'. rewrite sup_unfold. simpl. intuition.
  - unfold directed.
    intros [n1 q1] [n2 q2]. simpl.
    destruct q1; destruct q2; simpl.
    + exists (existT _ 0%nat (inl tt)). simpl; split; auto with ord.
    + exists (existT _ n2 (inr p)); simpl; split; auto with ord.
    + exists (existT _ n1 (inr p)); simpl; split; auto with ord.
    + exists (existT _ (Nat.max n1 n2) (inr p)); simpl; split.
      apply natOrdSize_monotone; apply PeanoNat.Nat.le_max_l.
      apply natOrdSize_monotone; apply PeanoNat.Nat.le_max_r.
  - left. exact (inhabits (existT _ 0%nat (inl tt))).
  - destruct a; simpl.
    revert o.
    rewrite lub_unfold.
    simpl. intros [| _].
    apply zero_complete.
    apply natOrdSize_complete.
Qed.

Lemma succ_limit_dec_EM :
  (forall x, 0 < x -> x <= ω -> complete x -> successorOrdinal x \/ limitOrdinal x) ->
  excluded_middle.
Proof.
  intros Hdec P.
  destruct (Hdec (truth_ord' P)).
  - unfold truth_ord'.
    rewrite <- (sup_le _ _ 0%nat).
    rewrite <- lub_le1.
    apply succ_lt.
  - unfold truth_ord'.
    apply sup_least. intro i.
    apply lub_least.
    apply succ_least.
    apply (index_lt _ 0%nat).
    rewrite ord_le_unfold; simpl; intros.
    apply index_lt.
  - apply truth_ord'_complete.
  - hnf in H; simpl in H.
    destruct H as [[i s]H].
    destruct s; simpl in *.
    + right; intro HP.
      generalize (H (existT _ 1%nat (inr HP))).
      simpl.
      intro.
      destruct (ord_le_subord _ _ H0 tt) as [[] _].
    + right; intro HP.
      generalize (H (existT _ (S i) (inr HP))).
      simpl.
      intro.
      rewrite ord_le_unfold in H0. simpl in *.
      generalize (H0 tt).
      apply ord_lt_irreflexive.
  - left.
    destruct H.
    simpl in H0.
    hnf in H0.
    destruct (H0 (existT _ O (inl tt))) as [[i q] H1].
    destruct q; auto. simpl in *.
    apply ord_lt_irreflexive in H1. elim H1.
Qed.

Definition Brouwer_continuity_for_numbers :=
  forall (R : (nat -> nat) -> nat -> Prop),
    (forall f, exists m, R f m) ->
    forall (a : nat -> nat),
    exists (n : nat) (m : nat),
    forall (b: nat -> nat),
      (forall i, (i < n)%nat -> a i = b i) ->
      R b m.

Definition limited_principle_of_omniscience :=
  forall (f:nat -> nat), (forall i, f i = 0%nat) \/ (exists i, f i <> 0%nat).

Theorem EM_LPO : excluded_middle -> limited_principle_of_omniscience.
Proof.
  intros EM f.
  destruct (EM (exists i, f i <> 0%nat)); auto.
  left. intro i.
  case_eq (f i); auto.
  intros. elim H.
  exists i.
  rewrite H0.
  discriminate.
Qed.

Theorem Brouwer_continuity_LPO :
  Brouwer_continuity_for_numbers -> limited_principle_of_omniscience -> False.
Proof.
  intros Hcont HLPO.
  set (R (f:nat->nat) (n:nat) :=
         f n <> 0%nat \/ (forall i, f i = 0%nat)).
  assert (Hn : forall f, exists n, R f n).
  { intro f. destruct (HLPO f); auto.
    - exists 0%nat. hnf. right. auto.
    - destruct H as [i Hi]. exists i. hnf. left. auto. }
  apply Hcont in Hn.
  destruct (Hn (fun _ => 0%nat)) as [n [m Hm]].
  unfold R in Hm.
  set (g i := (if le_lt_dec i (Nat.max n m) then 0 else 1)%nat).
  destruct (Hm g).
  - unfold g; simpl; intros.
    destruct (le_lt_dec i (Nat.max n m)); lia.
  - unfold g in H.
    destruct (le_lt_dec m (Nat.max n m)); lia.
  - unfold g in H.
    specialize (H (S (Nat.max n m))).
    destruct (le_lt_dec (S (Nat.max n m)) (Nat.max n m)); lia.
Qed.

Corollary Brouwer_continuity_anticlassical :
  Brouwer_continuity_for_numbers -> excluded_middle -> False.
Proof.
  intros.
  apply Brouwer_continuity_LPO; auto.
  apply EM_LPO.
  assumption.
Qed.

End classical.
