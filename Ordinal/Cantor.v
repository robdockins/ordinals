Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import ClassicalFacts.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Classical.
From Ordinal Require Import Enumerate.

Definition additively_closed (x:Ord) :=
  forall a b, a < x -> b < x -> a + b < x .

Lemma additively_closed_collapse a b :
  additively_closed b ->
  a < b -> a + b ≤ b.
Proof.
  intros.
  unfold addOrd.
  rewrite foldOrd_unfold.
  apply lub_least; auto with ord.
  apply sup_least; intro i.
  apply succ_least.
  apply (H a (b i)); auto with ord.
Qed.

Lemma additively_closed_limit x :
  1 < x ->
  additively_closed x ->
  limitOrdinal x.
Proof.
  intros H0 Hx.
  destruct x as [X f]. simpl; intros.
  split.
  - rewrite ord_lt_unfold in H0. destruct H0 as [x _]. constructor. exact x.
  - hnf. intros.
    hnf in Hx.
    generalize (Hx (f a) 1 (index_lt (ord X f) a) H0).
    unfold addOrd.
    rewrite foldOrd_succ.
    rewrite foldOrd_zero.
    rewrite ord_lt_unfold.
    intros [a' ?].
    rewrite ord_le_unfold in H.
    specialize (H tt). simpl in H.
    exists a'. auto.
    intros.
    rewrite H. apply ord_lt_le. apply succ_lt.
Qed.

Lemma additively_closed_mul_omega x :
  additively_closed x ->
  additively_closed (x * ω).
Proof.
  intros H a b Ha Hb.
  rewrite mulOrd_unfold in Ha.
  rewrite mulOrd_unfold in Hb.
  apply sup_lt in Ha.
  apply sup_lt in Hb.
  destruct Ha as [i Ha].
  destruct Hb as [j Hb].
  simpl in *.
  rewrite <- (sup_le _ _ (j + 1 + i)%nat).
  eapply ord_lt_le_trans.
  { apply addOrd_increasing. apply Hb. }
  clear b Hb.
  induction j.
  - simpl.
    rewrite addOrd_assoc.
    apply addOrd_monotone; auto with ord.
    transitivity (a + 0).
    { apply addOrd_monotone; auto with ord.
      apply sup_least; intros []. }
    rewrite <- addOrd_zero_r.
    rewrite <- (sup_le _ _ tt).
    auto with ord.
  - simpl.
    rewrite addOrd_assoc.
    apply addOrd_monotone; auto with ord.
    transitivity (a + (x * natOrdSize j + x)).
    { apply addOrd_monotone; auto with ord.
      apply sup_least. intro; auto with ord. }
    rewrite IHj.
    rewrite <- (sup_le _ _ tt).
    reflexivity.
Qed.

Lemma additively_closed_one : additively_closed 1.
Proof.
  hnf; simpl; intros.
  rewrite ord_lt_unfold in H.
  destruct H as [? ?]. simpl in H.
  rewrite H.
  rewrite <- addOrd_zero_l.
  auto.
Qed.

Lemma additively_closed_omega : additively_closed ω.
Proof.
  hnf; simpl; intros.
  rewrite <- (mulOrd_one_l ω).
  apply additively_closed_mul_omega.
  + apply additively_closed_one.
  + rewrite (mulOrd_one_l ω); auto.
  + rewrite (mulOrd_one_l ω); auto.
Qed.

Lemma expOmega_additively_closed c :
  complete c ->
  additively_closed (expOrd ω c).
Proof.
  induction c as [C h].
  intros Hc a b Ha Hb.
  generalize Ha; intro Ha'.
  unfold expOrd in Ha.
  rewrite foldOrd_unfold in Ha.
  apply lub_lt in  Ha.
  destruct Ha.
  { rewrite ord_lt_unfold in H0.
    destruct H0 as [[] ?].
    rewrite H0.
    rewrite <- addOrd_zero_l. auto. }
  unfold expOrd in Hb.
  rewrite foldOrd_unfold in Hb.
  apply lub_lt in Hb.
  destruct Hb.
  { rewrite ord_lt_unfold in H1.
    destruct H1 as [[] ?]. simpl in *.
    rewrite H1.
    rewrite <- addOrd_zero_r. auto. }
  apply sup_lt in H0.
  destruct H0 as [ca ?].
  apply sup_lt in H1.
  destruct H1 as [cb ?].
  destruct (complete_directed _ Hc ca cb) as [c' [??]].
  unfold expOrd.
  rewrite foldOrd_unfold.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ c').
  apply additively_closed_mul_omega; auto.
  - red; intros. apply H; auto.
    apply Hc.
  - eapply ord_lt_le_trans; [ apply H0 | ].
    apply mulOrd_monotone1.
    apply foldOrd_monotone.
    apply mulOrd_monotone1.
    auto.
  - eapply ord_lt_le_trans; [ apply H1 | ].
    apply mulOrd_monotone1.
    apply foldOrd_monotone.
    apply mulOrd_monotone1.
    auto.
Qed.

Lemma expOrd_add_collapse b c :
  complete c ->
  b < c ->
  expOrd ω b + expOrd ω c ≤ expOrd ω c.
Proof.
  intros; apply additively_closed_collapse.
  - apply expOmega_additively_closed; auto.
  - apply expOrd_increasing; auto.
    rewrite ord_lt_unfold.
    exists 1%nat. simpl.
    reflexivity.
Qed.

Lemma natOrdSize_add n m :
  natOrdSize (n+m)%nat ≈ natOrdSize m + natOrdSize n.
Proof.
  induction n.
  - simpl.
    split; auto with ord.
    apply lub_le1.
    apply lub_least; auto with ord.
    apply sup_least; intros [].
  - simpl natOrdSize.
    unfold addOrd.
    rewrite foldOrd_succ.
    rewrite IHn. reflexivity.
    intros. rewrite H. apply ord_lt_le; apply succ_lt.
Qed.

Lemma natOrdSize_mul n m :
  natOrdSize (n*m)%nat ≈ natOrdSize m * natOrdSize n.
Proof.
  induction n.
  - simpl.
    split; auto with ord.
    apply sup_least; intros [].
  - simpl natOrdSize.
    rewrite mulOrd_succ.
    rewrite natOrdSize_add.
    rewrite IHn.
    reflexivity.
Qed.

Lemma mul_omega_collapse a b (n:ω) :
  a*n ≥ b -> (a + b) * ω ≤ a * ω.
Proof.
  intros.
  simpl mulOrd at 1.
  apply sup_least; intro m.
  assert (Hn : a + b ≤ a * natOrdSize n + a).
  { unfold sz in H; simpl in H.
    rewrite H. clear H.
    induction n; simpl natOrdSize.
    - rewrite mulOrd_zero_r.
      rewrite <- addOrd_zero_l.
      rewrite <- addOrd_zero_r.
      reflexivity.
    - rewrite mulOrd_succ.
      rewrite addOrd_assoc.
      rewrite IHn.
      reflexivity. }

  simpl. rewrite <- (sup_le _ _ (n + m*(1+n))%nat).
  simpl natOrdSize.
  rewrite natOrdSize_add.
  rewrite ordDistrib_left.
  rewrite <- addOrd_assoc.
  apply addOrd_monotone; auto.
  induction m.
  + simpl. apply sup_least; intros [].
  + simpl natOrdSize.
    rewrite mulOrd_succ.
    rewrite mulOrd_succ.
    rewrite natOrdSize_add.
    rewrite ordDistrib_left.
    rewrite <- addOrd_assoc.
    apply addOrd_monotone; auto.
Qed.


Lemma expOrd_omega_collapse a b c (n:ω) :
  complete c ->
  c > 0 ->
  a*n ≥ b ->
  (a + b) * expOrd ω c ≤ a * expOrd ω c.
Proof.
  intros. induction c as [C h].
  unfold expOrd. rewrite foldOrd_unfold.
  rewrite mulOrd_lub.
  rewrite mulOrd_one_r.
  rewrite ord_lt_unfold in H0.
  destruct H0 as [c _].
  apply lub_least.
  - rewrite <- lub_le2.
    rewrite <- (sup_le _ _ c).
    transitivity (a * ω).
    { transitivity ((a+b) * ω).
      transitivity ((a+b) * 1).
      apply mulOrd_one_r.
      apply mulOrd_monotone2.
      apply (index_le ω 1%nat).
      apply mul_omega_collapse with n. auto. }
    apply mulOrd_monotone2.
    transitivity (1 * ω).
    apply mulOrd_one_l.
    apply mulOrd_monotone1.
    apply foldOrd_above_z.
  - rewrite (mulOrd_continuous _ _ (fun i => foldOrd 1 (fun x => x * ω) (h i) * ω) c).
    apply sup_least; intro i.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    destruct (complete_zeroDec (h i)). apply H.
    + transitivity ((a+b) * ω).
      apply mulOrd_monotone2.
      transitivity (1 * ω).
      apply mulOrd_monotone1.
      rewrite foldOrd_unfold.
      apply lub_least; auto with ord.
      apply sup_least; intros.
      rewrite ord_le_unfold in H0.
      specialize (H0 a0). rewrite ord_lt_unfold in H0.
      destruct H0 as [[] _].
      apply mulOrd_one_l.
      transitivity (a * ω).
      apply mul_omega_collapse with n; auto.
      apply mulOrd_monotone2.
      transitivity (1 * ω).
      apply mulOrd_one_l.
      apply mulOrd_monotone1.
      rewrite foldOrd_unfold.
      apply lub_le1.
    + rewrite mulOrd_assoc.
      rewrite mulOrd_assoc.
      apply mulOrd_monotone1.
      apply H2; auto.
      apply H.
Qed.

Lemma omegaMul_closed : forall x y,
  x < ω -> y < ω -> x*y < ω.
Proof.
  intros.
  rewrite ord_lt_unfold in H.
  destruct H as [i Hi].
  rewrite ord_lt_unfold in H0.
  destruct H0 as [j Hj].
  rewrite Hi.
  rewrite Hj.
  simpl.
  rewrite <- natOrdSize_mul.
  apply index_lt.
Qed.

Opaque mulOrd.
Opaque expOrd.

Lemma expNatToOmega (n:ω) :
  n > 1 ->
  expOrd n ω ≈ ω.
Proof.
  intros.
  split.
  - rewrite expOrd_unfold.
    apply lub_least. { apply (index_le ω 1%nat). }
    apply sup_least; intro i.
    apply ord_lt_le.
    apply omegaMul_closed.
    simpl.
    induction i.
    + simpl natOrdSize. rewrite expOrd_zero.
      apply (index_lt ω 1%nat).
    + simpl natOrdSize. rewrite expOrd_succ.
      apply omegaMul_closed; auto.
      apply index_lt.
      apply ord_le_lt_trans with 1; auto with ord.
    + apply index_lt.
  - rewrite ord_le_unfold. intro i.
    rewrite expOrd_unfold.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    unfold sz. simpl ordSize.
    induction i.
    + apply mulOrd_positive.
      apply expOrd_nonzero.
      apply ord_le_lt_trans with 1; auto with ord.
    + simpl natOrdSize.
      rewrite expOrd_succ.
      apply ord_lt_le_trans with
        (expOrd (natOrdSize n) (natOrdSize i) * natOrdSize n * 2).
      rewrite mulOrd_succ.
      rewrite mulOrd_one_r.
      apply ord_le_lt_trans with (natOrdSize i + 1).
      { transitivity (natOrdSize (1+i)).
        reflexivity.
        rewrite natOrdSize_add.
        reflexivity. }
      apply ord_le_lt_trans with
          (expOrd (natOrdSize n) (natOrdSize i) * natOrdSize n + 1).
      apply addOrd_monotone; auto with ord.
      apply addOrd_increasing.
      apply ord_lt_le_trans with (1 * natOrdSize n).
      rewrite mulOrd_one_l. auto.
      apply mulOrd_monotone1.
      apply succ_least. apply expOrd_nonzero.
      apply mulOrd_monotone2.
      apply succ_least. auto.
      apply ord_le_lt_trans with 1; auto with ord.
Qed.

Lemma expNatToOmegaPow (n:ω) e :
  n > 1 ->
  expOrd n (expOrd ω (1+e)) ≈ expOrd ω (expOrd ω e).
Proof.
  intros.
  rewrite expOrd_add.
  rewrite expOrd_one'; [ | apply (index_lt _ 0%nat) ].
  rewrite expOrd_mul.
  rewrite expNatToOmega; auto.
  reflexivity.
Qed.

Lemma expNatToOmegaInf (n:ω) e :
  n > 1 ->
  e ≈ 1 + e ->
  expOrd n (expOrd ω e) ≈ expOrd ω (expOrd ω e).
Proof.
  intros Hn He.
  rewrite He at 1.
  apply expNatToOmegaPow; auto.
Qed.

(* TODO, I think we can simplify these two theorems by
   proving expOrd (a + b) e <= expOrd a e assuming
   that e is a limit *)
Lemma expToOmega_collapse a b (n:ω) :
  a ≥ n+1 ->
  a*n ≥ b ->
  expOrd (a + b) ω ≤ expOrd a ω.
Proof.
  intros.
  rewrite expOrd_unfold.
  apply lub_least. apply succ_least; apply expOrd_nonzero.
  apply sup_least; intro i.
  rewrite (expOrd_unfold a ω).
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ (1 + i*2)%nat).
  change (expOrd (a+b) (natOrdSize i) * (a+b) ≤ expOrd a (natOrdSize (S (i*2)%nat)) * a).
  assert (Ha0 : 0 < a).
  { rewrite <- H.
    unfold addOrd.
    rewrite foldOrd_succ.
    eapply ord_le_lt_trans; [ | apply succ_lt ].
    auto with ord.
    intros. rewrite H1. apply ord_lt_le; apply succ_lt. }
  assert (Hab0 : 0 < a + b).
  { apply ord_lt_le_trans with a; auto. apply addOrd_le1. }
  assert (Hab_aa : a+b <= a*a).
  { transitivity (a * natOrdSize (1+n)%nat).
    - rewrite H0; clear.
      unfold sz; simpl ordSize.
      induction n.
      + simpl natOrdSize; intros.
        rewrite mulOrd_one_r.
        rewrite mulOrd_zero_r.
        rewrite <- addOrd_zero_r. reflexivity.
      + simpl natOrdSize in *.
        do 3 rewrite mulOrd_succ.
        rewrite addOrd_assoc.
        rewrite IHn.
        rewrite mulOrd_succ.
        reflexivity.
    - apply mulOrd_monotone2.
      simpl.
      rewrite <- H.
      unfold addOrd.
      rewrite foldOrd_succ.
      rewrite foldOrd_zero.
      reflexivity.
      intros.
      rewrite H1. apply ord_lt_le. apply succ_lt. }

  simpl natOrdSize.
  rewrite expOrd_succ; auto.
  rewrite <- mulOrd_assoc.
  apply mulOrd_le_mor; auto.
  induction i; simpl natOrdSize.
  + do 2 rewrite expOrd_zero. reflexivity.
  + rewrite expOrd_succ; auto.
    rewrite expOrd_succ; auto.
    rewrite expOrd_succ; auto.
    rewrite <- mulOrd_assoc.
    apply mulOrd_le_mor; auto.
Qed.

Lemma expToOmega_collapse_tower a b (n:ω) c :
  a ≥ n+1 ->
  a*n ≥ b ->
  complete c ->
  c > 0 ->
  expOrd (a + b) (expOrd ω c) ≤ expOrd a (expOrd ω c).
Proof.
  intros Ha Hb.
  induction c as [C h]; intros.
  rewrite (expOrd_unfold ω).
  do 2 rewrite expOrd_lub.
  rewrite ord_lt_unfold in H1. destruct H1 as [c _].
  apply lub_least.
  - rewrite <- lub_le2.
    rewrite expOrd_unfold.
    apply lub_least.
    + apply succ_least. apply expOrd_nonzero.
    + apply sup_least; intros [].
      rewrite expOrd_zero.
      rewrite mulOrd_one_l.
      transitivity (expOrd (a+b) ω).
      { transitivity (expOrd (a+b) 1).
        rewrite expOrd_unfold.
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ tt).
        rewrite expOrd_zero.
        rewrite mulOrd_one_l. reflexivity.
        apply expOrd_monotone.
        apply (index_le ω 1%nat). }
      transitivity (expOrd a ω).
      { apply expToOmega_collapse with n; auto. }
      apply expOrd_monotone.
      rewrite <- (sup_le _ _ c).
      transitivity (1 * ω).
      { rewrite mulOrd_one_l. reflexivity. }
      apply mulOrd_monotone1.
      apply succ_least. apply expOrd_nonzero.
  - etransitivity; [ apply expOrd_continuous; auto |].
    apply sup_least; intro ci.
    rewrite <- lub_le2.
    simpl ordSize.
    destruct (complete_zeroDec (h ci)); [ apply H0 | |].
    + rewrite H1.
      rewrite expOrd_zero.
      rewrite mulOrd_one_l.
      transitivity (expOrd a ω).
      { apply expToOmega_collapse with n; auto. }
      apply expOrd_monotone.
      rewrite <- (sup_le _ _ ci).
      transitivity (1 * ω).
      { rewrite mulOrd_one_l. reflexivity. }
      apply mulOrd_monotone1.
      apply succ_least. apply expOrd_nonzero.
    + rewrite expOrd_mul.
      rewrite H; [ | apply H0 | assumption ].
      rewrite <- expOrd_mul.
      apply expOrd_monotone.
      rewrite <- (sup_le _ _ ci).
      reflexivity.
Qed.

Lemma truth_ord'_expOmega (P:Prop) : classical.truth_ord' P ≈ expOrd ω (classical.truth_ord P).
Proof.
  unfold classical.truth_ord, classical.truth_ord'.
  split.
  - apply sup_least. intro n.
    apply lub_least.
    + apply succ_least. apply expOrd_nonzero.
    + rewrite ord_le_unfold. intro H.
      simpl in H.
      rewrite expOrd_unfold.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ H).
      apply ord_lt_le_trans with ω.
      rewrite ord_lt_unfold. exists n.
      simpl. auto with ord.
      transitivity (1 * ω).
      rewrite mulOrd_one_l. reflexivity.
      apply mulOrd_monotone1.
      apply succ_least. apply expOrd_nonzero.
  - rewrite expOrd_unfold.
    apply lub_least.
    + rewrite <- (sup_le _ _ 0%nat).
      apply lub_le1.
    + apply sup_least. intro H.
      transitivity (1 * ω).
      { apply mulOrd_monotone1.
        rewrite expOrd_unfold.
        apply lub_least; auto with ord.
        apply sup_least. intros []. }
      rewrite mulOrd_one_l.
      rewrite ord_le_unfold; intro n.
      rewrite <- (sup_le _ _ n).
      rewrite <- lub_le2.
      rewrite ord_lt_unfold. simpl. exists H.
      auto with ord.
Qed.

Theorem additively_closed_enumerate (EM:excluded_middle) :
  enumerates (expOrd ω) (fun x => x > 0 /\ additively_closed x).
Proof.
  constructor.
  - intros. split.
    apply expOrd_nonzero.
    apply expOmega_additively_closed.
    apply (classical.ord_complete EM).
  - apply expOrd_monotone.
  - apply expOrd_increasing.
    rewrite ord_lt_unfold. exists 1%nat. simpl. reflexivity.
  - simpl; intros x z [Hz1 Hz2] H.
    destruct x as [X f].
    rewrite expOrd_unfold.
    apply lub_least.
    + rewrite ord_le_unfold; simpl; intro. auto.
    + apply sup_least; intro i.
      rewrite mulOrd_unfold.
      apply sup_least; intro j.
      apply ord_lt_le.
      apply Hz2.
      induction j.
      * simpl.
        apply ord_le_lt_trans with 0; auto.
        rewrite mulOrd_zero_r. auto with ord.
      * unfold ordSize. unfold ω.
        simpl natOrdSize.
        rewrite mulOrd_succ.
        apply Hz2; auto.
        apply H. apply (index_lt (ord X f)).
      * apply H. apply (index_lt (ord X f)).
Qed.


Theorem additively_closed_expOrd (EM:excluded_middle) x :
  0 < x -> additively_closed x -> exists c, expOrd ω c ≈ x.
Proof.
  intros.
  eapply (enumerates_surjective EM).
  apply (additively_closed_enumerate EM).
  simpl; split; auto.
Qed.

Require Import List.
Import ListNotations.
Open Scope list.

Fixpoint cantor_sequence x (ls : list Ord) :=
  match ls with
  | [] => True
  | (y::ys) => x >= y /\ cantor_sequence y ys
  end.

Fixpoint cantor_denote (ls:list Ord) : Ord :=
  match ls with
  | [] => 0
  | (y::ys) => expOrd ω y + cantor_denote ys
  end.

Lemma cantor_normal_add (EM:excluded_middle) : forall x xs y ys,
    cantor_sequence x xs ->
    cantor_sequence y ys ->
    exists zs, cantor_sequence (x ⊔ y) zs /\ cantor_denote zs ≈ cantor_denote xs + cantor_denote ys.
Proof.
  intros x xs; revert x.
  induction xs.
  - simpl; intros.
    exists ys. split.
    + destruct ys; simpl in *; intuition.
      rewrite <- lub_le2. auto.
    + rewrite <- addOrd_zero_l. reflexivity.
  - simpl. intros x y ys [Ha Hxs] Hys.
    destruct (IHxs a y ys) as [zs [Hzs1 Hzs2]]; auto.
    destruct zs.
    + simpl in *.
      exists [a].
      simpl; intuition.
      rewrite Ha. apply lub_le1.
      rewrite <- addOrd_assoc.
      rewrite <- Hzs2.
      rewrite <- addOrd_zero_r.
      split.
      * apply lub_least; auto with ord.
        apply sup_least; intros [].
      * apply lub_le1.
    + simpl in Hzs1.
      destruct (classical.order_total EM o a).
      * exists (a::o::zs).
        simpl; intuition.
        rewrite Ha. apply lub_le1.
        rewrite <- addOrd_assoc.
        apply addOrd_eq_mor; auto with ord.
        reflexivity.
      * exists (o::zs).
        simpl; intuition.
        rewrite H0.
        apply ord_lub_le_mor; auto with ord.
        rewrite <- addOrd_assoc.
        rewrite <- Hzs2.
        simpl.
        rewrite addOrd_assoc.
        apply addOrd_eq_mor; [ | reflexivity ].
        split.
        rewrite (addOrd_zero_l (expOrd ω o)) at 1.
        apply addOrd_monotone; auto with ord.
        apply expOrd_add_collapse; auto.
        apply (classical.ord_complete EM).
Qed.

Fixpoint cantor_eq xs ys :=
  match xs, ys with
  | [], [] => True
  | _ , [] => False
  | [],  _ => False
  | (x::xs), (y::ys) => x ≈ y /\ cantor_eq xs ys
  end.

Theorem cantor_decomposition_unique (EM:excluded_middle) x y xs ys :
  cantor_sequence x xs ->
  cantor_sequence y ys ->
  cantor_denote xs ≈ cantor_denote ys ->
  cantor_eq xs ys.
Proof.
  revert x y ys.
  induction xs; simpl; intros.
  - destruct ys; auto.
    simpl in H1.
    cut (1 <= 0).
    { intros. rewrite ord_le_unfold in H2. specialize (H2 tt).
      simpl in H2. rewrite ord_lt_unfold in H2. destruct H2 as [[] _]. }
    transitivity (expOrd ω o).
    { apply succ_least. apply expOrd_nonzero. }
    rewrite H1. apply addOrd_le1.
  - destruct ys.
    { simpl in H1.
      cut (1 <= 0).
      { intros. rewrite ord_le_unfold in H2. specialize (H2 tt).
        simpl in H2. rewrite ord_lt_unfold in H2. destruct H2 as [[] _]. }
      transitivity (expOrd ω a).
      { apply succ_least. apply expOrd_nonzero. }
      rewrite <- H1. apply addOrd_le1. }
    simpl in *.
    destruct (classical.order_total EM o a).
    + destruct (classical.order_total EM a o).
      * split. split; auto.
        apply (IHxs a o); intuition.
        eapply addOrd_cancel. apply H1.
        split; apply expOrd_monotone; auto.
      * elimtype False.
        assert (expOrd ω o + cantor_denote ys < expOrd ω a).
        { apply expOmega_additively_closed.
          apply classical.ord_complete; auto.
          apply expOrd_increasing; auto.
          rewrite ord_lt_unfold. exists 1%nat; simpl. reflexivity.
          destruct H0.
          clear -EM H4 H3.
          revert o H3 H4.
          induction ys.
          - simpl; intros.
            apply expOrd_nonzero.
          - simpl; intros.
            destruct H4.
            apply expOmega_additively_closed.
            apply classical.ord_complete; auto.
            apply expOrd_increasing; auto.
            rewrite ord_lt_unfold. exists 1%nat; simpl. reflexivity.
            apply ord_le_lt_trans with o; auto.
            apply IHys with a0; auto.
            apply ord_le_lt_trans with o; auto. }
        rewrite <- H1 in H4.
        elim (ord_lt_irreflexive (expOrd ω a)).
        eapply ord_le_lt_trans; [ | apply H4 ].
        unfold addOrd.
        apply foldOrd_above_z.
    + elimtype False.
      assert (expOrd ω a + cantor_denote xs < expOrd ω o).
      { apply expOmega_additively_closed.
        apply classical.ord_complete; auto.
        apply expOrd_increasing; auto.
        rewrite ord_lt_unfold. exists 1%nat; simpl. reflexivity.
        destruct H.
        clear -EM H2 H3.
          revert a H2 H3.
          induction xs.
          - simpl; intros.
            apply expOrd_nonzero.
          - simpl; intros.
            destruct H3.
            apply expOmega_additively_closed.
            apply classical.ord_complete; auto.
            apply expOrd_increasing; auto.
            rewrite ord_lt_unfold. exists 1%nat; simpl. reflexivity.
            apply ord_le_lt_trans with a0; auto.
            apply IHxs with a; auto.
            apply ord_le_lt_trans with a0; auto. }
        rewrite H1 in H3.
        elim (ord_lt_irreflexive (expOrd ω o)).
        eapply ord_le_lt_trans; [ | apply H3 ].
        unfold addOrd.
        apply foldOrd_above_z.
Qed.


Theorem cantor_decomposition (EM:excluded_middle) :
  forall x:Ord, exists ls,
    cantor_sequence x ls /\ cantor_denote ls ≈ x.
Proof.
  induction x using ordinal_induction.
  destruct (EM (exists a, exists b, a < x /\ b < x /\ a + b ≈ x)).
  - destruct H0 as [a [b [?[??]]]].
    destruct (H a H0) as [ls1 [??]].
    destruct (H b H1) as [ls2 [??]].

    destruct (cantor_normal_add EM a ls1 b ls2 H3 H5) as [ls [??]].
    exists ls; split; auto.
    + destruct ls; simpl in *; intuition.
      rewrite H9.
      apply lub_least; auto with ord.
    + rewrite <- H2.
      rewrite H8.
      rewrite H4. rewrite H6.
      reflexivity.
  - destruct (classical.order_total EM x 0).
    { exists []. simpl; intuition. split; auto with ord. }
    destruct (additively_closed_expOrd EM x) as [c Hc]; auto.
    + hnf; intros.
      destruct (classical.order_total EM x (a+b)); auto.
      elim H0.

      set (P b' := b' < x /\ x <= a + b').
      destruct (classical.ord_well_ordered EM P) with b as [b' ?].
      hnf. split; auto.
      destruct H5 as [[??]?].
      exists a. exists b'. unfold ord_eq. intuition.
      destruct (classical.order_total EM (a+b') x); auto.
      elimtype False.
      unfold addOrd in H8.
      rewrite foldOrd_unfold in H8.
      apply lub_lt in H8.
      destruct H8.
      * elim (ord_lt_irreflexive a); transitivity x; auto.
      * apply sup_lt in H8.
        destruct H8 as [q Hq].
        rewrite ord_lt_unfold in Hq.
        destruct Hq as [??]. simpl in H8.
        assert (b' <= b' q).
        apply H7.
        split; auto.
        transitivity b'; auto.
        apply index_lt.
        elim (ord_lt_irreflexive b').
        apply ord_le_lt_trans with (b' q); auto.
        apply index_lt.
    + exists [c]. simpl; intuition.
      rewrite <- Hc.
      apply increasing_inflationary.
      apply expOrd_increasing; auto.
      rewrite ord_lt_unfold.
      exists 1%nat. simpl. reflexivity.
      rewrite Hc.
      split.
      * apply lub_least; auto with ord.
        apply sup_least; intros [].
      * apply lub_le1.
Qed.


Theorem cantor_decomposition_is_classical :
  (forall x:Ord, exists ls,
        cantor_sequence x ls /\ cantor_denote ls ≈ x) ->
  excluded_middle.
Proof.
  intros H P.
  destruct (H (classical.truth_ord P)) as [ls [??]].
  destruct ls; simpl in *.
  - right; intro HN.
    destruct H1.
    rewrite ord_le_unfold in H2.
    specialize (H2 HN). simpl in H2.
    apply (ord_lt_irreflexive 0); auto.
  - assert (1 <= classical.truth_ord P).
    rewrite <- H1.
    transitivity (expOrd ω o).
    rewrite ord_le_unfold. simpl; intros.
    apply expOrd_nonzero.
    apply addOrd_le1.
    rewrite ord_le_unfold in H2.
    specialize (H2 tt).
    rewrite ord_lt_unfold in H2.
    destruct H2 as [HP _].
    left; auto.
Qed.

Theorem cantor_decomposition_is_classical_for_complete_ordinals :
  (forall x:Ord, complete x -> exists ls,
     (forall y, In y ls -> complete y) /\ cantor_sequence x ls /\ cantor_denote ls ≈ x) ->
  excluded_middle.
Proof.
  intros H P.
  destruct (H (classical.truth_ord' P)) as [ls [?[??]]].
  apply classical.truth_ord'_complete.
  destruct ls; simpl in *.
  - elimtype False.
    destruct H2.
    unfold classical.truth_ord' in H3.
    rewrite ord_le_unfold in H3.
    simpl in H3.
    specialize (H3 (existT _ 0%nat (inl tt))). simpl in H3.
    apply (ord_lt_irreflexive 0); auto.
  - destruct (complete_zeroDec o). { apply H0; simpl; auto. }
    + clear H0.
      destruct H1.
      right; intro HN.
      rewrite (classical.truth_ord'_true _ HN) in H2.
      apply (ord_lt_irreflexive ω).
      rewrite <- H2 at 1.
      apply additively_closed_omega.
      apply ord_le_lt_trans with 1.
      transitivity (expOrd ω 0).
      apply expOrd_monotone; auto.
      rewrite expOrd_zero. auto with ord.
      rewrite ord_lt_unfold. exists 1%nat. simpl. auto with ord.
      clear -H1 H3.
      induction ls; simpl.
      * rewrite ord_lt_unfold; exists 0%nat. simpl. auto with ord.
      * apply additively_closed_omega.
        apply ord_le_lt_trans with 1.
        transitivity (expOrd ω 0).
        apply expOrd_monotone; auto.
        simpl in H1; intuition.
        transitivity o; auto.
        rewrite expOrd_zero. auto with ord.
        rewrite ord_lt_unfold. exists 1%nat. simpl. auto with ord.
        apply IHls. destruct H1.
        destruct ls; simpl in * ; intuition.
        transitivity a; auto.

    + left.
      rewrite ord_lt_unfold in H3. destruct H3 as [i _].
      destruct H2.
      rewrite <- addOrd_le1 in H2.
      rewrite expOrd_unfold in H2.
      rewrite <- lub_le2 in H2.
      rewrite <- (sup_le _ _ i) in H2.
      rewrite <- (zero_least (o i)) in H2.
      rewrite expOrd_zero in H2.
      rewrite mulOrd_one_l in H2.
      rewrite ord_le_unfold in H2.
      specialize (H2 1%nat). simpl in H2.
      unfold classical.truth_ord' in H2.
      apply sup_lt in H2.
      destruct H2 as [n H2].
      apply lub_lt in H2.
      destruct H2; [ elim (ord_lt_irreflexive 1); auto | ].
      rewrite ord_lt_unfold in H2.
      destruct H2; auto.
Qed.
