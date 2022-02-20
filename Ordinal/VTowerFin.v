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

Open Scope ord_scope.

Fixpoint vtower_fin (n:nat) : Ord -> Ord :=
  match n with
  | O    => addOrd 1
  | S n' => fun x => veblen (vtower_fin n') (1+x) 0
  end.

Definition SmallVeblenOrdinal := supOrd (fun i => vtower_fin i 0).

Lemma vtower_fin_succ n x : vtower_fin (S n) x = veblen (vtower_fin n) (1+x) 0.
Proof.
  reflexivity.
Qed.

Lemma vtower_fin_normal n :
  normal_function (vtower_fin n).
Proof.
  induction n; simpl.
  - apply onePlus_normal.
  - apply veblen_first_onePlus_normal; auto.
Qed.

Lemma vtower_fin_eq_mor n x y :
  x ≈ y -> vtower_fin n x ≈ vtower_fin n y.
Proof.
  intros; split; apply normal_monotone; auto.
  apply vtower_fin_normal.
  apply H.
  apply vtower_fin_normal.
  apply H.
Qed.

Lemma vtower_fin_complete n :
  forall x, complete x -> complete (vtower_fin n x).
Proof.
  apply normal_complete. apply vtower_fin_normal; auto.
Qed.

Add Parametric Morphism n : (veblen (vtower_fin n))
    with signature ord_le ==> ord_le ==> ord_le
      as veblen_vtower_fin_le_mor.
Proof.
  intros.
  apply veblen_le_mor; auto.
  intros; apply normal_monotone; auto.
  apply vtower_fin_normal; auto.
Qed.

Add Parametric Morphism n : (veblen (vtower_fin n))
    with signature ord_eq ==> ord_eq ==> ord_eq
      as veblen_vtower_fin_eq_mor.
Proof.
  intros.
  apply veblen_eq_mor; auto.
  intros; apply normal_monotone; auto.
  apply vtower_fin_normal; auto.
Qed.

Lemma zero_lt_onePlus x : 0 < 1 + x.
Proof.
  apply ord_lt_le_trans with 1; [ apply succ_lt | apply addOrd_le1 ].
Qed.

Local Hint Resolve
      vtower_fin_complete
      vtower_fin_normal
      veblen_complete
      veblen_normal
      veblen_first_normal
      veblen_first_onePlus_normal
      normal_monotone
      onePlus_normal
      powOmega_normal
      addOrd_complete
      addOrd_increasing
      succ_complete
      zero_complete
      natOrdSize_complete
      zero_lt_onePlus
  : core.

Lemma vtower_fin_succ_monotone :
  forall n i, complete i -> vtower_fin n i ≤ vtower_fin (S n) i.
Proof.
  induction n; simpl; intros.
  - apply (onePlus_least_normal (fun i => veblen (addOrd 1) (1+i) 0)); auto.
  - apply veblen_monotone_func; auto.
Qed.

Lemma vtower_fin_index_monotone :
  forall m n, (m <= n)%nat ->
    forall i, complete i -> vtower_fin m i ≤ vtower_fin n i.
Proof.
  intros. induction H; auto with ord.
  rewrite IHle.
  apply vtower_fin_succ_monotone; auto.
Qed.

Lemma vtower_fin_fixpoints_succ n : forall a x,
  0 < a ->
  complete a ->
  complete x ->
  veblen (vtower_fin (S n)) a x ≈ veblen (vtower_fin n) (veblen (vtower_fin (S n)) a x) 0.
Proof.
  intros.
  simpl.
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal (S n)) 0 a x) at 1; auto.
  rewrite veblen_zero.
  simpl.
  rewrite onePlus_veblen; auto.
  reflexivity.
Qed.

Theorem vtower_fin_fixpoints n : forall m a x,
  (m < n)%nat ->
  0 < a ->
  complete a ->
  complete x ->
  veblen (vtower_fin n) a x ≈ veblen (vtower_fin m) (veblen (vtower_fin n) a x) 0.
Proof.
  destruct n.
  - intros. inversion H.
  - intros. inversion H.
    + subst m. apply vtower_fin_fixpoints_succ; auto.
    + split; simpl.
      * apply (normal_inflationary (fun i => veblen (vtower_fin m) i 0)); auto.
      * rewrite <- (veblen_fixpoints _ (vtower_fin_normal (S n)) 0 a x) at 2; auto.
        rewrite veblen_zero.
        simpl.
        rewrite onePlus_veblen; auto.
        apply veblen_monotone_func; auto.
        apply vtower_fin_index_monotone; auto.
        lia.
Qed.

Lemma vtower_fin_0_0 : vtower_fin 0 0 ≈ 1.
Proof.
  simpl.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Lemma vtower_fin_1_func : forall x, complete x -> vtower_fin 1 x ≈ expOrd ω (1+x).
Proof.
  simpl; intros.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Lemma vtower_fin_1_0 : vtower_fin 1 0 ≈ ω.
Proof.
  rewrite vtower_fin_1_func; auto.
  rewrite addOrd_zero_r.
  rewrite expOrd_one'; auto with ord.
  apply (index_lt _ 0%nat).
Qed.

Lemma vtower_fin_2_func : forall x, complete x -> vtower_fin 2 x ≈ veblen powOmega (1+x) 0.
Proof.
  intros.
  rewrite vtower_fin_succ.
  simpl.
  rewrite (veblen_func_onePlus (fun i => veblen (addOrd 1) i 0)); auto.
  split; apply veblen_monotone_func; auto.
  intros; rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r. reflexivity.
  intros; rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r. reflexivity.
Qed.

Lemma vtower_fin_2_0 : vtower_fin 2 0 ≈ ε 0.
Proof.
  rewrite vtower_fin_2_func; auto.
  rewrite addOrd_zero_r.
  rewrite veblen_succ; auto.
  unfold ε.
  split; apply enum_fixpoints_func_mono; auto;
    intros; rewrite veblen_zero; auto with ord.
Qed.

Lemma vtower_fin_3_func :
  forall x, complete x -> vtower_fin 3 x ≈ veblen (fun i => veblen powOmega i 0) (1+x) 0.
Proof.
  intros.
  rewrite vtower_fin_succ.
  symmetry.
  rewrite <- veblen_func_onePlus; auto.
  split; apply veblen_monotone_func; auto;
    intros; rewrite vtower_fin_2_func; auto with ord.
Qed.

Lemma vtower_fin_3_0 : vtower_fin 3 0 ≈ Γ 0.
Proof.
  rewrite vtower_fin_3_func; auto.
  transitivity (veblen (fun i : Ord => veblen powOmega i 0) 1 0).
  apply veblen_eq_mor; auto with ord.
  intros; apply veblen_monotone_first; auto.
  rewrite addOrd_zero_r; auto with ord.
  rewrite veblen_succ; auto.
  unfold Γ.
  split; apply enum_fixpoints_func_mono; auto;
    intros; rewrite veblen_zero; auto with ord.
Qed.
