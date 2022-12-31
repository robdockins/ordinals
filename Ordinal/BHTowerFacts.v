Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import List.
Import ListNotations.
Open Scope list.
Require Import Lia.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import VTowerFin.
From Ordinal Require Import VTower.
From Ordinal Require Import BHTower.

Open Scope ord_scope.

Definition succ_unreachable (x:Ord) :=
  forall a, a < x -> succOrd a < x.

Add Parametric Morphism : succ_unreachable with signature
    ord_eq ==> impl as succ_unreachable_eq_mor.
Proof.
  intros. hnf; intros.
  unfold succ_unreachable.
  intro i.
  rewrite <- H.
  apply H0.
Qed.


Lemma limit_unreachable y :
    limitOrdinal y ->
    succ_unreachable y.
Proof.
  intros Hlim x Hxy.
  rewrite ord_isLimit in Hlim.
  destruct Hlim as [Hz Hlim].
  destruct (Hlim x) as [q [??]]; auto.
  apply ord_le_lt_trans with q; auto.
  apply succ_least; auto.
Qed.

Lemma unreachable_limit y :
  y > 0 -> succ_unreachable y -> limitOrdinal y.
Proof.
  intros. rewrite ord_isLimit; split; auto.
  intros.
  exists (succOrd i). split; auto with ord.
Qed.


Local Hint Resolve
  bhtower_monotone nextCritical_monotone
  zero_complete succ_complete addOrd_complete
  complete_subord normal_monotone normal_complete
  onePlus_normal veblen_normal veblen_first_normal
  bhtower_normal bhtower_first_normal bhtower_monotone
  powOmega_normal normal_monotone normal_complete normal_inflationary
  vtower_monotone vtower_normal vtower_first_normal
  : core.

Goal (bhtower 0 (addOrd 1) 0 0 ≈ 1).
Proof.
  rewrite bhtower_index_zero.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Goal (bhtower 1 (addOrd 1) 1 0 ≈ ω).
Proof.
  rewrite bhtower_index_one; auto with ord.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite expOrd_one'; auto with ord.
  apply omega_gt0.
Qed.

Lemma succ_reachable : forall n f i,
    normal_function f ->
    complete i ->
    succOrd i <= bhtower (S n) f i i.
Proof.
  intros.
  rewrite bhtower_unroll.
  destruct (complete_zeroDec i); auto.
  - rewrite H1 at 1.
    rewrite <- lub_le1.
    rewrite ord_le_unfold. simpl; intro.
    apply normal_nonzero; auto.
  - rewrite <- lub_le2.
    rewrite ord_lt_unfold in H1. destruct H1 as [z _].
    rewrite <- (sup_le _ _ z).
    rewrite <- nextCritical_above.
    apply succ_least.
    rewrite ord_lt_unfold. simpl. exists z.
    transitivity (bhtower (S n) f i 0).
    apply (normal_inflationary (fun x => bhtower (S n) f x 0)); auto.
    apply bhtower_monotone; auto with ord.
    rewrite <- addOrd_le1.
    auto with ord.
Qed.


Lemma bhtower_collapse n :
  forall f (Hf:normal_function f),
  forall a b c,
    complete a ->
    complete b ->
    complete c ->
    a < c ->
    b <= c ->
    bhtower (S n) f c 0 <= c ->
    bhtower (S n) f a b <= c.
Proof.
  intros.
  transitivity (bhtower (S n) f c 0); auto.
  rewrite <- (bhtower_fixpoint (S n) f a c 0); auto with arith ord.
  apply normal_monotone; auto with ord.
  transitivity c; auto.
  apply (normal_inflationary (fun x => bhtower (S n) f x 0)); auto.
Qed.

Lemma bhtower_collapse' n :
  forall f (Hf:normal_function f),
  forall a b c,
    complete a ->
    complete b ->
    complete c ->
    a < c ->
    b < c ->
    bhtower (S n) f c 0 <= c ->
    bhtower (S n) f a b < c.
Proof.
  intros.
  apply ord_lt_le_trans with (bhtower (S n) f c 0); auto.
  rewrite <- (bhtower_fixpoint (S n) f a c 0); auto with arith ord.
  apply normal_increasing; auto with ord.
  apply ord_lt_le_trans with c; auto.
  apply (normal_inflationary (fun x => bhtower (S n) f x 0)); auto.
Qed.


Definition apex n f := fixOrd (fun x => bhtower (S n) f x 0) 0.

Lemma apex_complete : forall n f,
    normal_function f ->
    complete (apex n f).
Proof.
  intros.
  apply normal_fix_complete; auto with ord.
  intros. apply (normal_inflationary (fun x => bhtower (S n) f x 0)); auto with ord.
Qed.

Local Hint Resolve apex_complete: core.

Lemma apex_fixpoint : forall n f,
    normal_function f ->
    apex n f ≈ bhtower (S n) f (apex n f) 0.
Proof.
  intros. unfold apex at 1.
  rewrite normal_fixpoint; auto with ord.
Qed.

Lemma apex_monotone : forall n m f g,
    (m <= n)%nat ->
    normal_function f ->
    normal_function g ->
    (forall x, f x <= g x) ->
    apex m f <= apex n g.
Proof.
  intros.
  unfold apex at 1.
  apply fixOrd_least; auto with ord.
  rewrite apex_fixpoint at 2; auto.
  apply bhtower_monotone_strong; auto with ord arith.
Qed.

Theorem apex_unreachable : forall n f a x,
    normal_function f ->
    complete a ->
    complete x ->
    a < apex n f ->
    x < apex n f ->
    bhtower (S n) f a x < apex n f.
Proof.
  intros.
  apply bhtower_collapse'; auto.
  apply apex_fixpoint; auto.
Qed.

Lemma limitOrdinal_intro' : forall x,
    x > 0 ->
    (forall i:x, exists j:x, i < j) ->
    limitOrdinal x.
Proof.
  destruct x as [X f]; intros.
  simpl; split.
  - rewrite ord_lt_unfold in H. destruct H as [i _].
    exact (inhabits i).
  - hnf. intros. apply H0.
Qed.

Theorem apex_nonzero : forall n f,
    normal_function f ->
    0 < apex n f.
Proof.
  intros.
  rewrite apex_fixpoint; auto with ord.
  apply normal_nonzero; auto with ord.
Qed.

Theorem apex_limit : forall n f,
    normal_function f ->
    limitOrdinal (apex n f).
Proof.
  intros.
  apply limitOrdinal_intro'.
  - apply apex_nonzero; auto.
  - intro i.
    assert (succOrd i < apex n f).
    { apply ord_le_lt_trans with (bhtower (S n) f i i); auto.
      apply succ_reachable; auto.
      apply apex_unreachable; auto with ord. }

    rewrite ord_lt_unfold in H0.
    destruct H0 as [j Hj].
    exists j.
    rewrite <- Hj.
    auto with ord.
Qed.

Theorem apex_least_unreachable : forall n f q,
    normal_function f ->
    complete q ->
    limitOrdinal q ->
    (forall a x,
        complete a ->
        complete x ->
        a < q ->
        x < q ->
        bhtower (S n) f a x < q) ->
    apex n f <= q.
Proof.
  intros.
  unfold apex.
  apply normal_fix_least; auto with ord.
  rewrite bhtower_unroll.
  apply lub_least.
  - transitivity (bhtower (S n) f 0 0).
    rewrite bhtower_unroll; auto with ord.
    rewrite ord_isLimit in H1.
    apply ord_lt_le. apply H2; intuition auto with ord.

  - apply sup_least. simpl.
    intro a.
    transitivity (nextCritical n (bhtower (S n) f a) 1 0).
    { apply nextCritical_monotone; auto with ord.
      rewrite addOrd_zero_r. auto with ord.
      rewrite ord_le_unfold; intros []. }
    apply nextCritical_least; auto with ord.
    intros.
    rewrite ord_lt_unfold in H4.
    destruct H4 as [[] ?]. simpl in H4.
    transitivity (bhtower n (bhtower (S n) f a) 0 q).
    apply bhtower_monotone; auto with ord.
    rewrite bhtower_zero.

    transitivity (bhtower (S n) f a (boundedSup q (fun i => i))).
    { apply bhtower_monotone; auto with ord.
      apply limit_boundedSup; auto. }
    transitivity (supOrd (fun i:q => bhtower (S n) f a i)).
    { destruct q as [Q q]. simpl.
      destruct H1 as [Hz Hlim].
      destruct Hz.
      apply normal_continuous; intuition.
      hnf in H0; intuition.
      hnf in H0; intuition.
      hnf in H0; intuition.
    }
    apply sup_least; intro i.
    apply ord_lt_le. apply H2; auto with ord.
Qed.


Lemma succ_not_unreachable : forall n f i,
    normal_function f ->
    complete i ->
    (forall a x,
        complete a ->
        complete x ->
        a < succOrd i ->
        x < succOrd i ->
        bhtower (S n) f a x < succOrd i) ->
    False.
Proof.
  intros.
  elim (ord_lt_irreflexive (succOrd i)).
  apply ord_le_lt_trans with (bhtower (S n) f i i).
  apply succ_reachable; auto.
  apply (H1 i i); auto with ord.
Qed.

Lemma apex_alternate n f :
  normal_function f ->
  apex n f ≈ bhtower (S (S n)) f 2 0.
Proof.
  intros.
  rewrite bhtower_succ; auto with ord arith.
  transitivity (bhtower (S n) (bhtower (S (S n)) f 1) 1 0).
  { rewrite bhtower_one_zero; auto with ord.
    split.
    - unfold apex.
      apply fixOrd_least; auto with ord.
      rewrite normal_fixpoint at 2; auto with ord.
      rewrite bhtower_one; auto with ord arith.
      apply bhtower_monotone; auto with ord.
      apply addOrd_le2.
      apply normal_fix_complete; auto with ord.
    - apply fixOrd_least; auto with ord.
      rewrite apex_fixpoint at 2; auto.
      rewrite bhtower_one; auto with ord arith.
      apply bhtower_monotone; auto with ord.
      apply limit_onePlus. apply apex_limit; auto. }
  - split; apply bhtower_monotone; auto with ord.
    rewrite addOrd_zero_r; auto with ord.
    rewrite addOrd_zero_r; auto with ord.
Qed.

Lemma apex0 : apex 0 (addOrd 1) ≈ ε 0.
Proof.
  unfold apex.
  assert (forall x, complete x -> bhtower 1 (addOrd 1) x 0 ≈ powOmega x).
  { intros.
    rewrite bhtower_index_one; auto.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r; auto with ord. }

  unfold ε.
  rewrite enum_fixpoints_zero; auto.
  split.
  - apply normal_fix_least; auto with ord.
    apply normal_fix_complete; auto with ord.
    rewrite H; auto.
    rewrite normal_fixpoint at 2; auto with ord.
    apply normal_fix_complete; auto with ord.
  - apply normal_fix_least; auto with ord.
    apply normal_fix_complete; auto with ord.
    intros. apply (normal_inflationary (fun x => bhtower 1 (addOrd 1) x 0)); auto with ord.
    rewrite normal_fixpoint at 2; auto with ord.
    rewrite H; auto with ord.
    apply normal_fix_complete; auto with ord.
    intros. apply (normal_inflationary (fun x => bhtower 1 (addOrd 1) x 0)); auto with ord.
Qed.

Lemma apex1 : apex 1 (addOrd 1) ≈ LargeVeblenOrdinal.
Proof.
  unfold apex.
  unfold LargeVeblenOrdinal.
  split.
  - apply normal_fix_least; auto with ord.
    apply normal_fix_complete; auto with ord.
    intros. apply (normal_inflationary (fun x => vtower (addOrd 1) x 0)); auto with ord.
    rewrite bhtower_index_two; auto with ord.
    rewrite normal_fixpoint at 2; auto.
    intros; apply vtower_monotone; auto with ord.
    apply normal_fix_complete; auto with ord.
    intros. apply (normal_inflationary (fun x => vtower (addOrd 1) x 0)); auto with ord.
  - apply normal_fix_least; auto with ord.
    apply normal_fix_complete; auto.
    intros. apply (normal_inflationary (fun x => bhtower 2 (addOrd 1) x 0)); auto with ord.
    intros; apply bhtower_monotone; auto with ord.
    rewrite normal_fixpoint at 2; auto with ord.
    rewrite bhtower_index_two; auto with ord.
    apply normal_fix_complete; auto with ord.
    intros. apply (normal_inflationary (fun x => bhtower 2 (addOrd 1) x 0)); auto with ord.
Qed.


Definition BachmanHoward := supOrd (fun n:nat => apex n (addOrd 1)).


Fixpoint each {A:Type} (P:A -> Prop) (xs:list A) : Prop :=
  match xs with
  | [] => True
  | (x::xs) => P x /\ each P xs
  end.

Definition each_lt (x:Ord) (vs:list Ord) := each (fun v => v < x) vs.

Fixpoint BH_stack (f:Ord -> Ord) (x:Ord) (xs:list Ord) : Ord :=
  match xs with
  | [] => f x
  | (y::ys) => BH_stack (bhtower (S (length ys)) f x) y ys
  end.

Definition BH_full_stack (xs:list Ord) : Ord :=
  match xs with
  | [] => 0
  | (x::xs) => BH_stack (addOrd 1) x xs
  end.

Inductive pairwise {A B} (R:A -> B -> Prop) : list A -> list B -> Prop :=
  | pairwise_nil : pairwise R nil nil
  | pairwise_cons : forall x xs y ys,
      R x y -> pairwise R xs ys -> pairwise R (x::xs) (y::ys).

Lemma pairwise_length A B (R:A -> B -> Prop) xs ys :
  pairwise R xs ys -> length xs = length ys.
Proof.
  intro H; induction H; simpl; auto.
Qed.

Lemma BH_stack_monotone f g x y xs ys :
  (forall a b, a <= b -> f a <= g b) ->
  (forall a b, a <= b -> g a <= g b) ->
  x <= y ->
  pairwise ord_le xs ys ->
  BH_stack f x xs <= BH_stack g y ys.
Proof.
  intros Hfg Hg Hxy H.
  revert f g x y Hfg Hg Hxy.
  induction H; intros f g x' y' Hfg Hg Hxy; simpl; auto with ord.
  apply IHpairwise; auto.
  replace (length ys) with (length xs).
  - intros; apply bhtower_monotone; auto with ord.
  - eapply pairwise_length; eauto.
  - intros; apply bhtower_monotone; auto with ord.
Qed.

Lemma BH_stack_leading_zero :
  forall f x xs,
    normal_function f ->
    BH_stack f 0 (x::xs) ≈ BH_stack f x xs.
Proof.
  intros; split; simpl.
  - simpl.
    apply BH_stack_monotone; auto with ord.
    intros. rewrite bhtower_zero; auto with ord.
    { clear. induction xs; simpl; auto with ord.
      - constructor.
      - constructor; auto with ord. }
  - apply BH_stack_monotone; auto with ord.
    intros. rewrite bhtower_zero; auto with ord.
    { clear. induction xs; simpl; auto with ord.
      - constructor.
      - constructor; auto with ord. }
Qed.

Lemma BH_full_stack_leading_zero :
  forall xs, (length xs > 0)%nat ->
    BH_full_stack (0::xs) ≈ BH_full_stack xs.
Proof.
  simpl; intros.
  destruct xs; simpl in *. lia.
  apply BH_stack_leading_zero; auto with ord.
Qed.

Fixpoint stackZeros (n:nat) (xs:list Ord) : list Ord :=
  match n with
  | O => xs
  | S n' => 0 :: stackZeros n' xs
  end.

Lemma stackZeros_length n xs : length (stackZeros n xs) = (n + length xs)%nat.
Proof.
  induction n; simpl; auto.
Qed.

Lemma BH_stack_zeros' n :
  forall f a x xs,
    (forall a b, a <= b -> f a <= f b) ->
    BH_stack f a (stackZeros n (x::xs)) ≈ BH_stack (bhtower (n + length (x::xs)) f a) x xs.
Proof.
  induction n; simpl; auto with ord.

  intros.
  rewrite IHn; auto with ord.

  split; apply BH_stack_monotone; auto with ord.
  intros. rewrite bhtower_zero; auto with ord.
  simpl. rewrite stackZeros_length; simpl; auto with ord.
  { clear. induction xs; constructor; auto with ord. }
  intros. rewrite bhtower_zero; auto with ord.
  simpl. rewrite stackZeros_length; simpl; auto with ord.
  { clear. induction xs; constructor; auto with ord. }
Qed.

Lemma BH_stack_zeros n f a b :
  BH_stack f a (stackZeros n [b]) ≈ bhtower (S n) f a b.
Proof.
  destruct n; simpl; auto with ord.
  rewrite stackZeros_length.
  simpl.
  replace (S (n+1)) with (S (S n)) by lia.
  generalize (bhtower (S (S n)) f a).
  induction n; simpl; intros.
  rewrite bhtower_zero; auto with ord.
  rewrite IHn.
  rewrite bhtower_zero. auto with ord.
Qed.

Lemma BH_stack_leading_succ_zero :
  forall f x n,
    (n > 0)%nat ->
    normal_function f ->
    complete x ->
    BH_stack f (succOrd x) (stackZeros (S n) [0]) ≈ BH_stack f x (stackZeros n [1;0]).
Proof.
  intros.
  rewrite BH_stack_zeros'; auto with ord.
  simpl.
  destruct n. lia.
  simpl.
  rewrite BH_stack_zeros'; auto with ord.
  simpl.
  rewrite bhtower_succ; auto with ord arith.
  rewrite bhtower_index_one; auto with ord.
  rewrite veblen_succ; auto with ord.
  rewrite enum_fixpoints_zero; auto with ord.
  transitivity (bhtower (S (n + 1)) (bhtower (S (S (n + 1))) f x) 1 0).
  { split; apply bhtower_monotone; auto with ord;
      rewrite addOrd_zero_r; auto with ord. }
  rewrite bhtower_one_zero; auto with ord.
  rewrite stackZeros_length. simpl.
  replace (S (S (n+1))) with (S (n+2)) by lia.
  split; apply fixOrd_least; auto with ord.
  - rewrite normal_fixpoint at 2; auto with ord.
    rewrite veblen_zero.
    rewrite bhtower_zero.
    auto with ord.
  - rewrite veblen_zero.
    rewrite bhtower_zero.
    rewrite normal_fixpoint at 2; auto with ord.
Qed.


Lemma critical_shrink_step : forall
  m f x v
  (Hf : normal_function f)
  (Hx : complete x)
  (Hv : complete v)
  (Hlim : limitOrdinal x)
  (Hfix : bhtower (S (S m)) f x 0 ≤ x)
  (Hvx : v < x),
  bhtower (S m) (bhtower (S (S m)) f v) x 0 ≤ x.
Proof.
  intros.
  transitivity (supOrd (fun i:x =>
                          bhtower (S m) (bhtower (S (S m)) f v) i 0)).
  { transitivity (bhtower (S m) (bhtower (S (S m)) f v) (boundedSup x (fun i => i)) 0).
    apply bhtower_monotone; auto with ord.
    apply limit_boundedSup; auto.
    destruct x as [X g]. simpl in *.
    destruct Hlim. destruct H as [x0].
    apply (normal_continuous (fun x => bhtower (S m) (bhtower (S (S m)) f v) x 0)); intuition.
  }
  apply sup_least; intro i.
  rewrite (bhtower_unroll m).
  apply lub_least.
  + rewrite <- Hfix.
    apply bhtower_monotone; auto with ord.
  + apply sup_least; intro j.
    apply nextCritical_least; auto with ord.
    rewrite ord_le_unfold; intros [].
    intros y' Hy'c Hy'.
    transitivity (bhtower m (bhtower (S m) (bhtower (S (S m)) f v) (sz j)) 0 x).
    { apply bhtower_monotone; auto with ord.
      rewrite addOrd_zero_r in Hy'.
      rewrite ord_lt_unfold in Hy'.
      destruct Hy' as [[] Hy']. simpl in Hy'.
      auto with ord.
    }
    rewrite bhtower_zero.
    transitivity (supOrd (fun k:x =>
                            bhtower (S m) (bhtower (S (S m)) f v) (sz j) k)).
    { transitivity (bhtower (S m) (bhtower (S (S m)) f v) j (boundedSup x (fun i => i))).
      apply bhtower_monotone; auto with ord.
      apply limit_boundedSup; auto.
      destruct x as [X g]. simpl in *.
      destruct Hlim. destruct H as [x0].
      apply (normal_continuous (bhtower (S m) (bhtower (S (S m)) f v) j)); intuition.
    }

    apply sup_least; intro k.

    transitivity (bhtower (S (S m)) f x 0); auto.
    destruct (complete_directed x Hx i k) as [l [Hl1 Hl2]].
    rewrite ord_lt_unfold in Hvx.
    destruct Hvx as [q ?].
    destruct (complete_directed x Hx l q) as [r [Hr1 Hr2]].
    assert (Hr': exists r':x, r < r').
    { destruct x as [X g]; simpl in *; intuition. }
    destruct Hr' as [r' Hr'].
    rewrite ord_lt_unfold in Hr'.
    destruct Hr' as [q' Hr'].
    rewrite (bhtower_unroll (S m)).
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ r').
    rewrite <- nextCritical_fix; auto with ord.
    rewrite (bhtower_unroll (S m)).
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ q').
    rewrite <- nextCritical_critical.
    * apply bhtower_monotone; auto with ord.
      intros. apply bhtower_monotone; auto with ord.
      rewrite H. rewrite Hr2. auto.
      rewrite <- nextCritical_fix; auto with ord.
      ** transitivity (bhtower (S (S m)) f q' 0).
         transitivity q'.
         rewrite Hl2. rewrite Hr1. auto.
         apply (normal_inflationary (fun x => bhtower (S (S m)) f x 0)); auto with ord.
         apply bhtower_monotone; auto with ord.
      ** apply lim_normal_complete; auto with ord.
         apply nextCritical_complete; auto with ord.
         apply lim_normal_complete; auto with ord.
      ** apply addOrd_complete; auto with ord.
         apply nextCritical_complete; auto with ord.
         apply lim_normal_complete; auto with ord.
      ** rewrite <- addOrd_le1. auto with ord.
    * auto with ord.
    * auto with ord.
    * auto with ord.
    * apply addOrd_complete; auto with ord.
      apply nextCritical_complete; auto with ord.
      apply lim_normal_complete; auto with ord.
    * apply lim_normal_complete; auto with ord.
      apply nextCritical_complete; auto with ord.
      apply lim_normal_complete; auto with ord.
    * apply ord_lt_le_trans with i; auto with ord.
      rewrite <- addOrd_le2.
      rewrite <- nextCritical_fix; auto with ord.
      transitivity r'.
      { rewrite Hl1. rewrite Hr1. rewrite Hr'. auto with ord. }
      transitivity (bhtower (S (S m)) f r' 0).
      { apply (normal_inflationary (fun x => bhtower (S (S m)) f x 0)); auto with ord. }
      apply bhtower_monotone; auto with ord.
      apply lim_normal_complete; auto with ord.
      rewrite <- addOrd_le1; auto with ord.
    * apply lim_normal_complete; auto with ord.
    * rewrite <- addOrd_le1; auto with ord.
Qed.

Lemma BH_stack_unreachable :
  forall (m:ω) x f v vs,
    (length vs <= S m)%nat ->
    normal_function f ->
    each_lt x (v::vs) ->
    complete x ->
    limitOrdinal x ->
    each complete (v::vs) ->
    bhtower (S m) f x 0 <= x ->
    BH_stack f v vs < x.
Proof.
  unfold each_lt.
  induction m using size_induction.
  intros x f v vs Hlen Hf Hlt Hx Hlim Hcs Hfix.
  simpl in *.
  destruct vs.
  - simpl.
    apply ord_lt_le_trans with (f x); auto with ord.
    apply normal_increasing; intuition.
    rewrite <- Hfix at 2.
    rewrite <- bhtower_fixpoint with (a:=0); auto with ord.
    rewrite bhtower_zero.
    apply normal_monotone; auto with ord.
    apply (normal_inflationary (fun x => bhtower (S m) f x 0)); auto with ord.
    auto with arith.
    rewrite <- Hfix.
    apply normal_nonzero; auto with ord.
  - simpl in *.
    assert (length vs <= m)%nat by lia.
    destruct m.
    + destruct vs; simpl in *.
      apply bhtower_collapse'; intuition.
      lia.
    + apply (H m); intuition.
      apply natOrdSize_increasing. lia.
      transitivity (bhtower (S m) (bhtower (S (S m)) f v) x 0).
      apply bhtower_monotone; auto with ord.
      intros.
      apply bhtower_monotone_strong; auto with ord.
      apply critical_shrink_step; auto.
Qed.

Lemma BH_stack_unreachable_apex :
  forall f n v vs,
    normal_function f ->
    each_lt (apex n f) (v::vs) ->
    each complete (v::vs) ->
    (length vs <= S n)%nat ->
    BH_stack f v vs < apex n f.
Proof.
  intros. unfold each_lt in *.
  apply BH_stack_unreachable with n; auto with ord.
  apply apex_limit; auto.
  apply apex_fixpoint; auto.
Qed.

Lemma BH_full_stack_unreachable_apex :
  forall n vs,
    (length vs <= 2 + n)%nat ->
    each complete vs ->
    each_lt (apex n (addOrd 1)) vs ->
    BH_full_stack vs < apex n (addOrd 1).
Proof.
  intros.
  destruct vs; simpl.
  apply apex_nonzero; auto.
  apply BH_stack_unreachable_apex; auto with ord.
  simpl in *. lia.
Qed.

Theorem BH_full_stack_uneachable :
  forall vs,
    each complete vs ->
    each_lt BachmanHoward vs ->
    BH_full_stack vs < BachmanHoward.
Proof.
  unfold each_lt in *; intros.
  assert (Hk: exists k, (length vs <= k)%nat /\ each (fun x => x < apex k (addOrd 1)) vs).
  { induction vs; simpl in *.
    { exists 0%nat. auto. }
    destruct IHvs as [k_tail Htail]; intuition.
    unfold BachmanHoward in H.
    apply sup_lt in H.
    destruct H as [k_head Hhead].
    exists (max k_head (S k_tail)).
    split; [ lia | split ].
    * apply ord_lt_le_trans with (apex k_head (addOrd 1)); auto.
      apply apex_monotone; auto with ord arith.
    * clear -H4.
      induction vs; simpl in *; intuition.
      apply ord_lt_le_trans with (apex k_tail (addOrd 1)); auto.
      apply apex_monotone; auto with ord arith.
      lia.
  }
  destruct Hk as [k [Hk1 Hk2]].
  unfold BachmanHoward.
  rewrite <- (sup_le _ _ k).
  destruct vs. simpl.
  apply apex_nonzero; auto with ord.
  simpl.
  apply BH_stack_unreachable_apex; simpl; auto with ord.
  simpl in *.
  lia.
Qed.


Lemma BH_stack_nonzero :
  forall xs f x,
    normal_function f ->
    each complete (x::xs) ->
    0 < BH_stack f x xs.
Proof.
  induction xs; simpl; intros.
  - apply normal_nonzero; auto.
  - apply IHxs; simpl; intuition.
Qed.

Theorem BachmanHoward_nonzero :
  0 < BachmanHoward.
Proof.
  unfold BachmanHoward.
  rewrite <- (sup_le _ _ 0%nat).
  unfold apex.
  rewrite normal_fixpoint; auto with ord.
  apply bhtower_normal; auto with ord.
  apply normal_fix_complete; auto with ord.
  intros. apply (normal_inflationary (fun x => bhtower 1 (addOrd 1) x 0)); auto with ord.
Qed.

Theorem BachmanHoward_complete :
  complete BachmanHoward.
Proof.
  unfold BachmanHoward.
  apply sup_complete; auto with ord.
  hnf; intros.
  exists (max a1 a2); split; apply apex_monotone; auto with ord arith.
  left.
  exists 0%nat.
  unfold apex.
  rewrite normal_fixpoint; auto with ord.
  apply bhtower_normal; auto with ord.
  apply normal_fix_complete; auto with ord.
  intros. apply (normal_inflationary (fun x => bhtower 1 (addOrd 1) x 0)); auto with ord.
Qed.

Theorem BachmanHoward_limit :
  limitOrdinal BachmanHoward.
Proof.
  apply limitOrdinal_intro.
  - apply BachmanHoward_nonzero.
  - unfold BachmanHoward.
    intros.
    apply sup_lt in H.
    destruct H as [k Hk].
    assert (limitOrdinal (apex k (addOrd 1))).
    { apply apex_limit; auto with ord. }
    rewrite ord_isLimit in H. destruct H.
    destruct (H0 i) as [j [Hj1 Hj2]]; auto.
    exists j. split; auto.
    rewrite <- (sup_le _ _ k). auto.
Qed.

Lemma BH_stack_complete : forall xs f x,
  normal_function f ->
  each complete (x::xs) ->
  complete (BH_stack f x xs).
Proof.
  induction xs; simpl; intros.
  - apply normal_complete; intuition.
  - apply IHxs; simpl; intuition.
Qed.


Lemma BH_stack_fixpoint1 : forall xs x f g,
    each complete (x::xs) ->
    normal_function f ->
    normal_function g ->
    (forall z, complete z -> g (f z) <= f z) ->
    g (BH_stack f x xs) <= BH_stack f x xs.
Proof.
  induction xs; simpl; intros; simpl in *; intuition.
  apply IHxs; intuition.
  destruct (complete_zeroDec x); auto with ord.
  - transitivity (g (bhtower (S (length xs)) f 0 z)); auto with ord.
    transitivity (g (f z)).
    { apply normal_monotone; auto with ord.
      rewrite bhtower_zero; auto with ord. }
    rewrite H2; auto.
    rewrite bhtower_unroll; auto with ord.
  - assert (f (bhtower (S (length xs)) f x z) <= bhtower (S (length xs)) f x z).
    { rewrite <- (bhtower_fixpoint (S (length xs)) f) with (a:=0) at 2; auto with ord arith.
      rewrite bhtower_zero. auto with ord.
    }
    transitivity (g (f (bhtower (S (length xs)) f x z))); auto with ord.
    rewrite H2; auto with ord.
Qed.

Fixpoint hasNonzeroIndexLoop (x:Ord) (xs:list Ord) :=
  match xs with
  | [] => False
  | (x'::xs') => x > 0 \/ hasNonzeroIndexLoop x' xs'
  end.

Definition hasNonzeroIndex (xs : list Ord) :=
  match xs with
  | [] => False
  | x::xs => hasNonzeroIndexLoop x xs
  end.

Lemma BH_stack_fixpoint2 : forall xs x f,
    each complete (x::xs) ->
    normal_function f ->
    hasNonzeroIndexLoop x xs ->
    f (BH_stack f x xs) <= BH_stack f x xs.
Proof.
  induction xs; simpl; intros; simpl in *; intuition.
  - apply BH_stack_fixpoint1; auto.
    simpl; intuition.
    intros.
    rewrite <- (bhtower_fixpoint (S (length xs)) f 0 x z) at 2; auto with ord arith.
    rewrite bhtower_zero. auto with ord.
  - rewrite <- IHxs at 2; intuition.
    rewrite bhtower_unroll.
    auto with ord.
Qed.


Lemma BH_stack_succ_redex :
  forall f n x y,
    normal_function f ->
    complete x ->
    complete y ->
    BH_stack f (succOrd x) (stackZeros (S n) [y]) ≈
      BH_stack f x ( (1+y) :: stackZeros n [0]).
Proof.
  intros; simpl.
  rewrite BH_stack_zeros.
  rewrite BH_stack_zeros.
  rewrite bhtower_zero.
  rewrite bhtower_succ; auto with ord.
  rewrite stackZeros_length. simpl.
  rewrite stackZeros_length. simpl.
  replace (S n) with (n+1)%nat by lia.
  auto with ord.
  rewrite stackZeros_length. simpl. auto with arith.
Qed.


Lemma BH_stack_apex_redex :
  forall f n x,
    normal_function f ->
    complete x ->
    bhtower (S n) f x 0 <= x ->
    BH_stack f x (stackZeros n [0]) ≈ x.
Proof.
  intros.
  rewrite BH_stack_zeros.
  split; auto.
  apply (normal_inflationary (fun x => bhtower (S n) f x 0)); auto.
Qed.



Lemma BH_stack_lt_fixpoint_limit :
  forall xs f x z,
    normal_function f ->
    each complete (x::xs) ->
    each_lt z (x::xs) ->
    complete z ->
    limitOrdinal z ->
    (forall q, complete q -> q < z -> bhtower (length xs) f q z <= z) ->
    BH_stack f x xs < z.
Proof.
  unfold each_lt.
  induction xs; simpl; intros f x z Hf Hc Hltz Hz Hlim Hfix; intuition.
  - rewrite <- (Hfix x); auto.
    rewrite bhtower_index_zero.
    apply normal_increasing; auto with ord.

  - apply IHxs; simpl; auto with ord.
    intros.
    destruct xs; simpl.
    { rewrite bhtower_index_zero. simpl in *. apply Hfix; auto. }
    rewrite <- (Hfix (succOrd x)) at 2; auto with ord.
    rewrite bhtower_succ; simpl; auto with ord arith.
    rewrite <- (bhtower_fixpoint (S (length xs)) _ q (1+z) 0); auto with ord arith.
    apply bhtower_monotone; auto with ord.
    transitivity (1+z); auto with ord.
    apply (normal_inflationary (fun q => bhtower (S (length xs)) (bhtower (S (S (length xs))) f x) q 0)); auto with ord.
    apply ord_lt_le_trans with z; auto with ord.
    apply limit_unreachable; auto.
Qed.


Lemma bhtower_preserves_unreachable:
  forall n f,
    normal_function f ->
    (forall x, complete x -> succ_unreachable (f x)) ->
    (forall x y, complete x -> complete y -> succ_unreachable (bhtower (S n) f x y)).
Proof.
  intros n f Hf Hlim.
  intros x y Hx Hy.
  destruct (complete_zeroDec x Hx).
  - assert (bhtower (S n) f x y ≈ bhtower (S n) f 0 y).
    { split; apply bhtower_monotone; auto with ord. }
    rewrite H0.
    rewrite bhtower_zero.
    apply Hlim; auto.
  - assert (bhtower (S n) f x y ≈ f (bhtower (S n) f x y)).
    { rewrite <- (bhtower_fixpoint (S n) f 0 x y) at 1; auto with ord arith.
      rewrite bhtower_zero. auto with ord. }
    rewrite H0.
    apply Hlim; auto with ord.
Qed.

Lemma normal_fixOrd_succ_unreachable:
  forall f x,
    normal_function f ->
    complete x ->
    (forall a, complete a -> succ_unreachable a -> succ_unreachable (f a)) ->
    succ_unreachable x ->
    succ_unreachable (fixOrd f x).
Proof.
  intros f x Hf Hx Hf2 Hsucc i Hi.
  unfold fixOrd in *.
  apply sup_lt in Hi.
  destruct Hi as [n Hi].
  rewrite <- (sup_le _ _ n).
  revert i Hi.
  induction n.
  - simpl; intros; auto.
  - simpl; intros.
    apply Hf2 in Hi; auto.
    apply iter_f_complete; auto.
Qed.

Lemma addOrd_lt :
  forall i x y,
    i < x+y ->
    i < x \/ exists j:y, i <= x+j.
Proof.
  intros i x y.
  rewrite addOrd_unfold.
  intros.
  apply lub_lt in H; intuition.
  apply sup_lt in H0.
  destruct H0 as [j ?].
  rewrite ord_lt_unfold in H.
  destruct H as [[] ?].
  simpl in H.
  right. exists j. auto.
Qed.

Lemma normal_limitOrdinal :
  forall f x,
    complete x ->
    normal_function f ->
    limitOrdinal x ->
    limitOrdinal (f x).
Proof.
  intros.
  assert (f x ≈ f (boundedSup x (fun i => i))).
  { split; apply normal_monotone; auto; apply limit_boundedSup; auto. }
  assert (f x ≈ supOrd (fun i:x => f i)).
  { rewrite H2. split.
    destruct x as [X g]. simpl in *.
    destruct H1. destruct H1.
    apply normal_continuous; auto with ord.
    intuition.
    intuition.
    apply sup_least; intro i.
    apply normal_monotone; auto.
    destruct x as [X g]; simpl.
    rewrite <- (sup_le _ _ i). auto with ord.
  }
  rewrite H3.
  rewrite ord_isLimit.
  split; intros.
  - destruct x as [X g]; simpl in *.
    destruct H1. destruct H1.
    rewrite <- (sup_le _ _ X0).
    apply normal_nonzero. auto.
  - apply sup_lt in H4. destruct H4 as [a ?].
    destruct x as [X g]; simpl in *; intuition.
    destruct (H7 a) as [a' ?].
    exists (f (g a)).
    split; auto.
    rewrite <- (sup_le _ _ a').
    apply normal_increasing; auto with ord.
Qed.


Lemma bhtower_onePlus_unreachable:
  forall n x y,
    complete x ->
    complete y ->
    succ_unreachable y ->
    succ_unreachable (bhtower (S n) (addOrd 1) (1+x) y).
Proof.
  induction x as [x Hind] using ordinal_induction.
  intros y Hx Hy Hsucc.

  destruct (complete_zeroDec y Hy).
  - intros i Hi0.
    assert (Hi: i < bhtower (S n) (addOrd 1) (1+x) 0).
    { eapply ord_lt_le_trans; [ apply Hi0 | ].
      apply bhtower_monotone; auto with ord. }
    clear Hi0.
    rewrite bhtower_unroll in Hi.
    apply lub_lt in Hi.
    destruct Hi as [Hi|Hi].
    + rewrite addOrd_zero_r in Hi.
      apply ord_lt_le_trans with 2.
      { apply succ_increasing; auto. }
      transitivity (1+1).
      { rewrite addOrd_succ. rewrite addOrd_zero_r. auto with ord. }
      rewrite <- (bhtower_fixpoint (S n) (addOrd 1) 0 (1+x) y); auto with ord arith.
      rewrite bhtower_zero.
      apply addOrd_monotone; auto with ord.
      apply succ_least.
      apply normal_nonzero; auto with ord.
      rewrite <- addOrd_le1.
      auto with ord.
    + apply sup_lt in Hi.
      destruct Hi as [a Hi].
      unfold nextCritical in Hi.
      apply sup_lt in Hi.
      destruct Hi as [b Hi].
      assert (Hi' : i < fixOrd (bhtower (S n) (addOrd 1) a) 0).
      { eapply ord_lt_le_trans; [ apply Hi | ].
        transitivity (fixOrd (bhtower n (bhtower (S n) (addOrd 1) a) b) 0).
        { apply fixOrd_monotone; auto with ord.
          rewrite ord_le_unfold; intros []. }
        apply fixOrd_monotone_func; auto with ord.
        intros.
        transitivity (bhtower n (bhtower (S n) (addOrd 1) a) 0 x0).
        { apply bhtower_monotone; auto with ord.
          clear Hi.
          assert (b < 1+0).
          auto with ord.
          rewrite addOrd_zero_r in H0 at 2.
          rewrite ord_lt_unfold in H0. destruct H0; auto. }
        rewrite bhtower_zero. auto with ord.
      }
      clear Hi.
      destruct (complete_zeroDec a); auto with ord.
      * apply ord_lt_le_trans with ω.
        apply limit_unreachable; auto with ord.
        apply omega_limit.
        eapply ord_lt_le_trans; [ apply Hi' | ].
        apply normal_fix_least; auto with ord.
        apply omega_complete.
        transitivity (bhtower (S n) (addOrd 1) 0 ω).
        apply bhtower_monotone; auto with ord.
        rewrite bhtower_zero.
        apply additively_closed_collapse; auto with ord.
        apply additively_closed_omega.
        rewrite ord_lt_unfold. exists 1%nat.
        simpl. auto with ord.
        rewrite ord_le_unfold. simpl; intro q.
        induction q; simpl.
        ** apply normal_nonzero; auto.
        ** simpl.
           rewrite <- onePlus_finite_succ.
           rewrite <- (bhtower_fixpoint (S n) (addOrd 1) 0 (1+x) y); auto with ord arith.
           rewrite bhtower_zero.
           apply addOrd_increasing; auto.
           rewrite <- addOrd_le1.
           auto with ord.
      * assert (Ha : a < 1+x) by auto with ord.
        apply addOrd_lt in Ha.
        destruct Ha.
        { rewrite ord_lt_unfold in H1.
          destruct H1. simpl in *.
          elim ord_lt_irreflexive with 0.
          apply ord_lt_le_trans with a; auto with ord. }
        destruct H1 as [j Ha].
        assert (Hi'' : i < fixOrd (bhtower (S n) (addOrd 1) (1+j)) 0).
        { eapply ord_lt_le_trans; [ apply Hi' | ].
          apply fixOrd_monotone_func; auto with ord. }
        apply normal_fixOrd_succ_unreachable in Hi''; auto with ord.
        2: { hnf; simpl; intros. rewrite ord_lt_unfold in H1. destruct H1 as [[] _]. }
        eapply ord_lt_le_trans; [ apply Hi'' | ].
        rewrite bhtower_unroll.
        rewrite <- lub_le2.
        assert (1 + j < 1+x).
        { apply addOrd_increasing; auto with ord. }
        rewrite ord_lt_unfold in H1.
        destruct H1 as [q Hq].
        rewrite <- (sup_le _ _ q).
        unfold nextCritical.
        assert (0 < 1+y).
        { rewrite <- addOrd_le1. auto with ord. }
        rewrite ord_lt_unfold in H1.
        destruct H1 as [b' ?].
        rewrite <- (sup_le _ _ b').
        simpl in *.
        transitivity (fixOrd (bhtower n (bhtower (S n) (addOrd 1) q) b') 0).
        ** apply fixOrd_monotone_func; auto with ord.
           intros.
           transitivity (bhtower n (bhtower (S n) (addOrd 1) q) 0 x0).
           rewrite bhtower_zero. auto with ord.
           apply bhtower_monotone; auto with ord.
        ** apply fixOrd_monotone; auto with ord.

  - apply limit_unreachable.
    apply normal_limitOrdinal; auto with ord.
    apply unreachable_limit; auto.
Qed.

Lemma bhtower_onePlus_limit:
  forall n x,
    complete x ->
    limitOrdinal (bhtower (S n) (addOrd 1) (1+x) 0).
Proof.
  intros.
  apply unreachable_limit.
  apply normal_nonzero; auto with ord.
  apply bhtower_onePlus_unreachable; auto with ord.
  hnf; simpl; intros.
  rewrite ord_lt_unfold in  H0.
  destruct H0 as [[] _].
Qed.

Lemma BH_stack_preserves_limit:
  forall ys f y,
    normal_function f ->
    (forall x, complete x -> limitOrdinal (f x)) ->
    each complete (y::ys) ->
    limitOrdinal (BH_stack f y ys).
Proof.
  induction ys; simpl; intuition.
  apply IHys; simpl; intuition.
  apply unreachable_limit.
  apply normal_nonzero; auto with ord.
  apply bhtower_preserves_unreachable; auto with ord.
  intros. apply limit_unreachable; auto.
Qed.

Lemma BH_full_stack_epsilon1:
  forall ys,
    each complete ys ->
    hasNonzeroIndex ys ->
    expOrd ω (BH_full_stack (1::ys)) <= BH_full_stack (1::ys).
Proof.
  intros. simpl.
  destruct ys; simpl in *; [ lia | ].
  rewrite <- BH_stack_fixpoint2 at 2; auto with ord.
  rewrite bhtower_one; auto with ord arith.
  transitivity (bhtower 1 (addOrd 1) (1+BH_stack (bhtower (S (length ys)) (addOrd 1) 1) o ys) 0).
  { rewrite bhtower_index_one; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r.
    apply expOrd_monotone; auto with ord.
    apply addOrd_le2.
    apply addOrd_complete; auto with ord.
    apply BH_stack_complete; auto with ord. }
  apply bhtower_monotone_strong; auto with ord.
  destruct ys; simpl in *; intuition.
  destruct ys; simpl in *; intuition.
  apply BH_stack_complete; auto with ord.
Qed.

Lemma BH_full_stack_epsilon2:
  forall y ys,
    each complete (y::ys) ->
    y > 1 ->
    (length ys > 1)%nat ->
    expOrd ω (BH_full_stack (y::ys)) <= BH_full_stack (y::ys).
Proof.
  intros. simpl.
  destruct ys; simpl in *; [ lia | ].
  apply BH_stack_fixpoint1; simpl; intuition auto with ord.
  rewrite <- bhtower_fixpoint with (a:=1) at 2; auto with ord arith.
  rewrite bhtower_one; auto with ord arith.
  transitivity (bhtower 1 (addOrd 1) (1+bhtower (S (length ys)) (addOrd 1) y z) 0).
  { rewrite bhtower_index_one; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r.
    auto with ord. }
  apply bhtower_monotone_strong; auto with ord.
  lia.
Qed.


Lemma BH_full_stack_limit1:
  forall ys,
    each complete ys ->
    (length ys > 1)%nat ->
    limitOrdinal (BH_full_stack (1::ys)).
Proof.
  intros.
  simpl.
  destruct ys; simpl in *; [ lia | ].
  apply BH_stack_preserves_limit; simpl; intuition auto with ord.
  rewrite bhtower_one; auto with ord.
  2: lia.
  destruct (length ys); [ lia | ].
  apply bhtower_onePlus_limit; auto with ord.
Qed.

Lemma BH_full_stack_limit2:
  forall y ys,
    each complete (y::ys) ->
    y > 1 ->
    (length ys > 1)%nat ->
    limitOrdinal (BH_full_stack (y::ys)).
Proof.
  intros.
  simpl.
  destruct ys; simpl in *; [ lia | ].
  apply BH_stack_preserves_limit; simpl; intuition auto with ord.
  rewrite <- (bhtower_fixpoint (S (length ys)) (addOrd 1) 1 y x); auto with ord arith; try lia.
  rewrite bhtower_one; auto with ord; try lia.
  destruct (length ys); [ lia | ].
  apply bhtower_onePlus_limit; auto with ord.
Qed.

Lemma BH_full_stack_limit : 
  forall x xs,
    each complete (x::xs) ->
    (x ≈ 1 \/ x > 1) ->
    (length xs > 1)%nat ->
    limitOrdinal (BH_full_stack (x::xs)).
Proof.
  intuition.
  - assert (BH_full_stack (x::xs) ≈ BH_full_stack (1::xs)).
    { simpl.
      destruct H2; split; apply BH_stack_monotone; auto with ord.
      clear. induction xs; constructor; auto with ord.
      clear. induction xs; constructor; auto with ord. }
    rewrite H0.
    apply BH_full_stack_limit1; simpl in *; intuition.
  - apply BH_full_stack_limit2; auto with ord.
Qed.


Lemma compare_stack_lt_short :
  forall x y xs ys f,
    each complete (x::xs) ->
    each complete (y::ys) ->
    normal_function f ->
    length xs = length ys ->
    (length ys <= 1)%nat ->
    x < y ->
    each_lt (BH_stack f y ys) xs ->
    BH_stack f x xs < BH_stack f y ys.
Proof.
  unfold each_lt. intros.
  destruct xs.
  { destruct ys; simpl in *; try discriminate.
    apply normal_increasing; intuition. }
  destruct ys; simpl in *; try discriminate.
  destruct xs.
  { destruct ys; simpl in *; try discriminate.
    rewrite <- (bhtower_fixpoint 1 f x y o0); intuition auto with ord.
    apply normal_increasing; auto with ord. }
  simpl in *. lia.
Qed.

Lemma compare_stack_lt_long :
  forall x y xs ys f,
    each complete (x::xs) ->
    each complete (y::ys) ->
    normal_function f ->
    length xs = length ys ->
    (limitOrdinal y \/ hasNonzeroIndex ys) ->
    limitOrdinal (BH_stack f y ys) ->
    x < y ->
    each_lt (BH_stack f y ys) xs ->
    BH_stack f x xs < BH_stack f y ys.
Proof.
  unfold each_lt.
  intros x y xs ys f Hcxs Hcys Hf Hlen Hstable Hlim2 Hxy Hxs.
  destruct xs as [ | x1 xs ].
  { destruct ys; simpl in *; try discriminate.
    apply normal_increasing; intuition. }
  destruct xs as [ | x2 xs ].
  { destruct ys. simpl in *. discriminate.
    destruct ys; simpl in *; try discriminate.
    rewrite <- (bhtower_fixpoint 1 f x y o); intuition auto with ord.
    apply normal_increasing; auto with ord.
  }

  change (BH_stack (bhtower (S (S (length xs))) f x) x1 (x2::xs) < BH_stack f y ys).

  apply BH_stack_lt_fixpoint_limit; auto with ord.
  - apply bhtower_normal; auto with ord. simpl in *; intuition.
  - simpl in *; intuition.
  - apply BH_stack_complete; simpl in *; intuition.
  - intros.
    simpl.
    apply bhtower_collapse; auto with ord.
    * apply bhtower_normal; simpl in *; intuition.
    * apply BH_stack_complete; simpl in * ; intuition.
    * apply BH_stack_complete; simpl in *; intuition.
    * assert (bhtower (S (S (length xs))) f (succOrd x) (BH_stack f y ys) <= BH_stack f y ys).
      { destruct ys. simpl in *. discriminate.
        simpl in *.
        destruct Hstable.
        - apply BH_stack_fixpoint1; auto.
          + simpl in *; intuition.
          + simpl in *; intuition auto with ord.
          + apply bhtower_normal; auto with ord.
            apply succ_complete. simpl in *; intuition.
          + intros. simpl in *.
            rewrite <- Hlen.
            apply bhtower_fixpoint; auto with ord arith.
            * apply succ_complete. simpl in *; intuition.
            * simpl in *; intuition.
            * apply limit_unreachable; auto with ord.
        - simpl in *.
          rewrite <- BH_stack_fixpoint2 at 2; simpl; intuition; auto with ord.
          rewrite Hlen.
          apply bhtower_monotone; auto with ord.
          apply succ_least; auto. }
      rewrite <- H1 at 2.
      rewrite bhtower_succ; auto with ord arith.
      apply bhtower_monotone; auto with ord.
      apply addOrd_le2.
      simpl in *; intuition.
      apply BH_stack_complete; auto.
Qed.


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Require VeblenFacts.

Lemma BH_stack_decompose (EM:excluded_middle) :
  forall n f (Hf:normal_function f) x (Hlim:limitOrdinal x),
    forall i,
      f x <= x ->
      i < x ->
      x < bhtower (S n) f i x ->

      exists v, exists vs, x ≈ BH_stack f v vs /\ length vs = S n /\ each_lt x (v::vs).
Proof.
  induction n; intros f Hf x Hlim i Hfx Hi Hix.

  - rewrite bhtower_index_one in Hix; auto.
    destruct (veblen_decompose EM f Hf x Hlim) as [a [b [?[?[??]]]]]; auto.
    + eapply ord_lt_le_trans; [ exact Hix | ].
      rewrite <- (veblen_fixpoints f Hf i x); auto.
      apply veblen_monotone; auto with ord.
      apply (normal_inflationary (fun x => veblen f x 0)).
      apply veblen_first_normal; auto.
      apply classical.ord_complete; auto.
      apply classical.ord_complete; auto.
      apply classical.ord_complete; auto.
    + exists a, (b::nil); unfold each_lt; simpl; intuition.
      rewrite bhtower_index_one; auto.

  - induction i as [i Hind] using ordinal_induction.

    (* Classify i as zero, successor or limit *)
    destruct (classical.ordinal_discriminate EM i) as [Hz|[Hs|Hl]].

    + (* zero case *)
      apply ord_isZero in Hz.
      elim (ord_lt_irreflexive x).
      apply ord_lt_le_trans with (f x); auto.
      apply ord_lt_le_trans with (bhtower (S (S n)) f i x); auto.
      transitivity (bhtower (S (S n)) f 0 x).
      apply bhtower_monotone; auto with ord.
      apply Hz.
      rewrite bhtower_zero; auto with ord.

    + (* successor case *)
      rewrite ord_isSucc in Hs.
      destruct Hs as [i' Hi'].
      assert (x < bhtower (S (S n)) f (succOrd i') x).
      { apply ord_lt_le_trans with (bhtower (S (S n)) f i x); auto.
        apply bhtower_monotone; auto with ord.
        apply Hi'. }
      rewrite bhtower_succ in H; auto with arith; (try apply classical.ord_complete; auto).

      set (f' := bhtower (S (S n)) f i').
      destruct (classical.order_total EM (f' x) x).
      * destruct (EM (exists j, j < x /\ x < bhtower (S n) f' j x)) as [Hj|Hj].
        ** destruct Hj as [j [Hh1 Hj2]].
           destruct IHn with f' x j as [v [vs [?[?[??]]]]]; auto.
           *** unfold f'. apply bhtower_normal; auto.
               apply classical.ord_complete; auto.
           *** exists i', (v::vs).
               unfold each_lt; simpl. rewrite H2; intuition.
               transitivity i; auto with ord.
               rewrite Hi'; auto with ord.
        ** assert (forall j, j < x -> bhtower (S n) f' j x <= x).
           { intros.
             destruct (classical.order_total EM (bhtower (S n) f' j x) x); auto.
             elim Hj; eauto. }

           (* this is a contradiction now... maybe could prove it directly instead
              of invoking EM above on (exists j, j < x ...) etc above
            *)
           rewrite bhtower_unroll in H.
           apply lub_lt in H. destruct H.
           { elim (ord_lt_irreflexive x).
             eapply ord_lt_le_trans; [ exact H | ].
             rewrite <- H0.
             apply bhtower_monotone; auto with ord. }
           apply sup_lt in H. destruct H as [a H].
           assert (H' : x < nextCritical n (bhtower (S n) (bhtower (S (S n)) f i') a) 1 0).
           { eapply ord_lt_le_trans; [ exact H | ].
             apply nextCritical_monotone; auto with ord.
             rewrite addOrd_zero_r. auto with ord.
             rewrite ord_le_unfold; intros []. }
           unfold nextCritical in H'.
           apply sup_lt in H'. destruct H' as [[] H']. simpl in H'.
           clear H.
           elim (ord_lt_irreflexive x).
           eapply ord_lt_le_trans; [ exact H' |].
           apply fixOrd_least; auto with ord.
           rewrite bhtower_zero.
           apply H1.
           apply ord_lt_le_trans with (1+x); auto with ord.
           apply limit_onePlus; auto.

       * apply (Hind i'); auto with ord.
         rewrite Hi'. auto with ord.
         transitivity i; auto with ord.
         rewrite Hi'; auto with ord.

    + (* limit case *)
      assert (exists q:x, x < bhtower (S (S n)) f i q).
      { assert (bhtower (S (S n)) f i x <= supOrd (fun q:x => bhtower (S (S n)) f i q)).
        transitivity (bhtower (S (S n)) f i (boundedSup x (fun q => q))).
        destruct x as [X g]. simpl.
        apply bhtower_monotone; auto with ord. simpl.
        apply limit_boundedSup; auto.
        rewrite ord_lt_unfold in Hi.
        destruct Hi.
        destruct x; apply normal_continuous; auto with ord.
        apply bhtower_normal; auto.
        apply classical.ord_complete; auto.
        apply classical.ord_directed; auto.
        intros; apply classical.ord_complete; auto.
        rewrite H in Hix.
        apply sup_lt in Hix. auto. }

      destruct H as [q Hq].
      set (Q a := a < x /\ x <= bhtower (S (S n)) f i a).
      destruct (classical.ord_well_ordered EM Q q).
      { hnf. auto with ord. }
      subst Q; simpl in *.
      destruct H as [[H0 H1] H2].

      destruct (classical.order_total EM (bhtower (S (S n)) f i x0) x).
      * exists i. exists (stackZeros (S n) [x0]).
        unfold each_lt. rewrite stackZeros_length.
        split.
        rewrite BH_stack_zeros.
        split; auto.
        simpl; intuition.
        lia.
        apply ord_le_lt_trans with x0; auto with ord.
        clear - H0.
        induction n; simpl; intuition.
        apply ord_le_lt_trans with x0; auto with ord.

      * rewrite bhtower_unroll in H.
        apply lub_lt in H.
        destruct H.
        { elim (ord_lt_irreflexive x).
          apply ord_lt_le_trans with (f x0); auto.
          transitivity (f x); auto with ord. }
        apply sup_lt in H. destruct H as [i' Hi'].

        rewrite ord_isLimit in Hl.
        destruct Hl as [Hl1 Hl2].
        destruct (Hl2 i') as [i'' [??]]; auto with ord.

        apply (Hind i''); auto with ord.
        transitivity i; auto with ord.
        assert (limOrd (fun x : x0 => bhtower (S (S n)) f i (sz x)) <= x).
        { rewrite ord_le_unfold. simpl; intros.
          destruct (classical.order_total EM x (bhtower (S (S n)) f i a)); auto.
          elim (ord_lt_irreflexive x0).
          apply ord_le_lt_trans with a; auto with ord.
          apply H2; split; auto.
          transitivity x0; auto with ord. }

        rewrite bhtower_unroll.
        rewrite <- lub_le2.
        rewrite ord_lt_unfold in H.
        destruct H as [i3 ?].
        rewrite <- (sup_le _ _ i3).
        eapply ord_lt_le_trans; [ exact Hi' |].
        apply nextCritical_monotone; auto with ord.
        rewrite H4.
        rewrite ord_le_unfold. simpl; intros.
        rewrite ord_lt_unfold. simpl. exists a.
        apply normal_inflationary; auto.
        apply bhtower_normal; auto.
        apply classical.ord_complete; auto.
        apply classical.ord_complete; auto.
Qed.


Lemma BH_stack_decompose_apex (EM:excluded_middle) :
  forall n f (Hf:normal_function f) x (Hlim:limitOrdinal x),
      f x <= x ->
      x < apex n f ->
      exists v, exists vs, x ≈ BH_stack f v vs /\ length vs = S n /\ each_lt x (v::vs).
Proof.
  intros.

  assert (Hbnd : exists i, i < x /\ x < bhtower (S n) f i x).
  { set (P a := x < bhtower (S n) f a x).
    destruct (classical.ord_well_ordered EM P (apex n f)) as [i Hi].
    + hnf.
      eapply ord_lt_le_trans; [ apply H0 |].
      transitivity (bhtower (S n) f (apex n f) 0).
      apply (normal_inflationary (fun q => bhtower (S n) f q 0)).
      apply bhtower_first_normal; auto.
      apply classical.ord_complete; auto.
      apply bhtower_monotone; auto with ord.

    + subst P. destruct Hi as [Hi1 Hi2].
      exists i; split; auto.

      destruct (classical.order_total EM x i); auto.
      elim (ord_lt_irreflexive x).
      eapply ord_lt_le_trans; [ apply H0 | ].
      apply normal_fix_least; auto with ord.
      apply classical.ord_complete; auto.
      destruct (classical.order_total EM (bhtower (S n) f x 0) x); auto.
      elim (ord_lt_irreflexive x).
      apply ord_le_lt_trans with i; auto.
      assert (bhtower (S n) f x 0 <= supOrd (fun i:x => bhtower (S n) f i 0)).
      { transitivity (bhtower (S n) f (boundedSup x (fun i => i)) 0).
        apply bhtower_monotone; auto with ord.
        apply limit_boundedSup; auto.
        destruct x as [X g]; simpl in *; intuition.
        destruct H3.
        apply (normal_continuous (fun x => bhtower (S n) f x 0)); intuition.
        apply classical.ord_directed; auto.
        apply classical.ord_complete; auto.
      }
      rewrite H3 in H2.
      apply sup_lt in H2.
      destruct H2.
      apply ord_le_lt_trans with x0; auto with ord.
      apply Hi2. auto.
      apply ord_lt_le_trans with (bhtower (S n) f x0 0); auto with ord.
  }

  destruct Hbnd as [i [??]].
  apply BH_stack_decompose with i; auto.
Qed.

Theorem BachmanHoward_limit_decompose (EM:excluded_middle) :
  forall x (Hlim:limitOrdinal x),
    x < BachmanHoward ->
    exists vs, x ≈ BH_full_stack vs /\ each_lt x vs.
Proof.
  unfold BachmanHoward.
  intros x Hlim H.
  apply sup_lt in H.
  destruct H as [n H].
  destruct (BH_stack_decompose_apex EM n (addOrd 1) (onePlus_normal) x Hlim) as [v [vs [?[??]]]]; auto.
  apply limit_onePlus; auto.
  exists (v::vs).
  unfold BH_full_stack; split; auto.
Qed.
