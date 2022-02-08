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

Inductive VForm : Set :=
| F : nat -> VForm
| V : VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | F n   => natOrdSize n
  | V a x => veblen (addOrd 1) (1 + VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Fixpoint VF_normal (x:VForm) : Prop :=
  match x with
  | F _ => True
  | V a x => VF_normal a /\
             VF_normal x /\
             match x with
             | F _ => True
             | V b y => VF_denote a >= VF_denote b
             end
  end.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x; simpl.
  - apply natOrdSize_complete.
  - apply veblen_complete; auto.
    apply onePlus_normal.
    apply onePlus_complete; auto.
    apply onePlus_complete; auto.
Qed.

Local Hint Resolve
      VF_complete onePlus_normal
      natOrdSize_complete
      onePlus_complete
      onePlus_nonzero
      addOrd_increasing
      veblen_onePlus_complete
      succ_complete zero_complete : core.

Lemma VF_denote_shrink1 : forall a x,
  VF_denote a < VF_denote (V a x).
Proof.
  simpl; intros.
  apply ord_lt_le_trans with (veblen (addOrd 1) (1 + VF_denote a) 0).
  - clear x.
    induction a; simpl; intuition.
    + apply ord_lt_le_trans with (1 + natOrdSize n).
      apply onePlus_finite.
      apply (normal_inflationary (fun i => veblen (addOrd 1) i 0)); auto.
      apply veblen_first_normal; auto.
    + rewrite onePlus_veblen; auto.
      apply veblen_shrink_lemma; auto.
      rewrite <- onePlus_veblen; auto.
      destruct a2; simpl.
      destruct n. simpl. apply veblen_nonzero; auto.
      apply finite_veblen_lt; auto.
      simpl. apply succ_trans; auto with ord.
      simpl in IHa2.
      rewrite onePlus_veblen in IHa2; auto.

  - apply veblen_monotone; auto with ord.
    intros; apply addOrd_monotone; auto with ord.
Qed.

Lemma VF_denote_shrink2 : forall x a,
  VF_normal (V a x) ->
  VF_denote x < VF_denote (V a x).
Proof.
  induction x; simpl; intuition.
  { apply finite_veblen_lt; auto. }
  apply veblen_increasing'; auto.
  apply addOrd_monotone; auto with ord.
  apply IHx2. simpl; intuition.
Qed.

Theorem VNotation_below_ε₀ x :
  VF_denote x < ε 0.
Proof.
  induction x; simpl VF_denote.
  - rewrite ε_fixpoint.
    apply ord_lt_le_trans with (expOrd ω 1).
    rewrite expOrd_one'; auto.
    apply index_lt.
    apply omega_gt0.
    apply expOrd_monotone.
    rewrite ε_fixpoint.
    apply succ_least. apply expOrd_nonzero.
  - rewrite veblen_onePlus; auto.
    apply epslion_additively_closed; auto.
    rewrite ε_fixpoint.
    apply expOrd_increasing; auto.
    apply (index_lt _ 1%nat).
    apply epslion_additively_closed; auto.
    apply ord_le_lt_trans with (expOrd ω 0).
    rewrite expOrd_zero; auto with ord.
    rewrite ε_fixpoint.
    apply expOrd_increasing; auto.
    apply omega_gt1.
    rewrite ε_fixpoint.
    apply expOrd_nonzero.
Qed.

Fixpoint VF_compare (x:VForm) : VForm -> ordering :=
  fix inner (y:VForm) : ordering :=
    match x, y with
    | F m, F n   => nat_compare m n
    | F _, V _ _ => LT
    | V _ _, F _ => GT
    | V a x' , V b y' =>
      match VF_compare a b with
      | LT => VF_compare x' y
      | EQ => VF_compare x' y'
      | GT => inner y'
      end
    end.

Lemma VF_compare_correct : forall x y,
    match VF_compare x y with
    | LT => VF_denote x < VF_denote y
    | EQ => VF_denote x ≈ VF_denote y
    | GT => VF_denote x > VF_denote y
    end.
Proof.
  induction x as [m|a IHa x IHx].
  { destruct y as [n|b y]; simpl; auto with ord.
    + generalize (nat_compare_correct m n).
      destruct (nat_compare m n); intros; subst; auto with ord.
      apply natOrdSize_increasing; auto.
      apply natOrdSize_increasing; auto.
    + apply finite_veblen_lt; auto. }

  induction y as [n|b IHb y IHy]; simpl.
  { apply finite_veblen_lt; auto. }

  apply veblen_compare_correct; auto.
  - generalize (IHa b).
    destruct (VF_compare a b); simpl; auto.
    intros; apply addOrd_eq_mor; auto with ord.
  - apply IHx.
  - apply IHx.
Qed.

Theorem V_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y); intros.
  - left; assumption.
  - right; apply H.
  - right; auto with ord.
Qed.

Theorem V_normal_forms_unique : forall x y,
  VF_normal x ->
  VF_normal y ->
  VF_denote x ≈ VF_denote y ->
  x = y.
Proof.
  induction x as [m|a Ha x Hx].
  - simpl. intro y; destruct y; simpl; intros; auto.
    + clear - H1.
      f_equal.
      revert n H1. induction m; intros.
      * destruct n; simpl in *; auto.
        elim (ord_lt_irreflexive 0).
        rewrite H1 at 2.
        apply succ_trans; auto with ord.
      * destruct n; simpl in *; auto.
        elim (ord_lt_irreflexive 0).
        rewrite <- H1 at 2.
        apply succ_trans; auto with ord.
        f_equal. apply IHm.
        destruct H1 as [H1 H2].
        destruct (ord_le_subord _ _ H1 tt).
        destruct (ord_le_subord _ _ H2 tt).
        simpl in *. split; auto.

    + elim (ord_lt_irreflexive (natOrdSize m)).
      rewrite H1 at 2.
      apply finite_veblen_lt; auto.

  - destruct y as [n|b y].
    + simpl; intros.
      elim (ord_lt_irreflexive (natOrdSize n)).
      rewrite <- H1 at 2.
      apply finite_veblen_lt; auto.
    + simpl; intuition.

      assert (a = b).
      { apply Ha; auto.
        generalize (VF_compare_correct a b).
        destruct (VF_compare a b); intros; auto.
        * elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ onePlus_normal (1+VF_denote a) (1+VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply VF_denote_shrink2. simpl; intuition.
        * elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote b) (VF_denote y))).
          rewrite <- H1 at 2.
          rewrite <- (veblen_fixpoints _ onePlus_normal (1+VF_denote b) (1+VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply VF_denote_shrink2. simpl; intuition. }
      subst b.
      f_equal.
      apply Hx; auto.
      generalize (VF_compare_correct x y).
      destruct (VF_compare x y); intros; auto.
      * elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote x))).
        rewrite H1 at 2.
        apply veblen_increasing; auto.
      * elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote y))).
        rewrite <- H1 at 2.
        apply veblen_increasing; auto.
Qed.

Definition Vnorm (a x:VForm) :=
  match x with
  | F _ => V a x
  | V b y =>
    match VF_compare a b with
    | GT => V a (V b y)
    | EQ => V a (V b y)
    | LT => V b y
    end
  end.

Lemma Vnorm_normal a x :
  VF_normal a -> VF_normal x -> VF_normal (Vnorm a x).
Proof.
  unfold Vnorm; simpl; intros.
  destruct x; simpl in *; intuition.
  generalize (VF_compare_correct a x1).
  destruct (VF_compare a x1); simpl; intuition.
  rewrite H2. reflexivity.
Qed.

Lemma Vnorm_V a x : VF_denote (V a x) ≈ VF_denote (Vnorm a x).
Proof.
  simpl. unfold Vnorm.
  destruct x; simpl; try reflexivity.
  generalize (VF_compare_correct a x1).
  destruct (VF_compare a x1); simpl; intuition.
  apply veblen_fixpoints; auto.
Qed.

Fixpoint Vnormalize (x:VForm) : VForm :=
  match x with
  | F n => F n
  | V a y => Vnorm (Vnormalize a) (Vnormalize y)
  end.

Lemma Vnormalize_normal : forall x, VF_normal (Vnormalize x).
Proof.
  induction x; simpl; intuition.
  apply Vnorm_normal; auto.
Qed.

Lemma Vnormalize_equal : forall x, VF_denote (Vnormalize x) ≈ VF_denote x.
Proof.
  induction x; simpl; intuition.
  rewrite <- Vnorm_V. simpl.
  rewrite IHx1.
  rewrite IHx2.
  reflexivity.
Qed.

Fixpoint VF_add (x y:VForm) : VForm :=
  match x with
  | F m  => match y with
            | F n   => F (n+m)
            | V _ _ => y
            end
  | V a x' => V a (VF_add x' y)
  end.

Theorem VF_add_correct x y : VF_denote (VF_add x y) ≈ VF_denote x + VF_denote y.
Proof.
  induction x; simpl.
  - destruct y; simpl.
    apply natOrdSize_add.
    symmetry. apply finite_veblen; auto.
  - repeat rewrite veblen_onePlus; auto.
    rewrite IHx2.
    apply addOrd_assoc.
Qed.

Definition VF_one := F 1.
Definition VF_succ x := VF_add x VF_one.
Definition VF_omega := V (F 0) (F 0).
Definition VF_expOmega x :=
  match x with
  | F 0 => F 1
  | F (S n) => V (F n) (F 0)
  | _ => V x (F 0)
  end.

Definition VF_isZero x : { x = F 0 } + { VF_denote x > 0 }.
Proof.
  destruct x.
  - destruct n; auto.
    right; simpl.
    apply succ_trans. auto with ord.
  - right. simpl. apply veblen_nonzero; auto.
Qed.

Definition VF_onePlus (x:VForm) : VForm :=
  match x with
  | F n => F (S n)
  | V _ _ => x
  end.

Lemma VF_onePlus_correct : forall x, VF_denote (VF_onePlus x) ≈ 1 + VF_denote x.
Proof.
  intro x. symmetry.
  destruct x; simpl; auto.
  apply onePlus_finite_succ.
  apply onePlus_veblen; auto.
Qed.

(* VF_mul_single x e = x * ω^(1+e) *)
Definition VF_mul_single (x:VForm) (e:VForm) : VForm :=
  match x with
  (* 0 * ωᵉ = 0 *)
  | F O => F O
  | F (S m) => V e (F 0)
  (* (ωᵃ + q) * ωᵉ = ω^(a + e) otherwise *)
  | V a _ => V (VF_add a (VF_onePlus e)) (F 0)
  end.

Definition VF_mul x : VForm -> VForm :=
  let x' := Vnormalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | F n    => Nat.iter n (fun a => VF_add a x') (F 0)
  | V b y' => VF_add (VF_mul_single x' b) (loop y')
  end.

(** Compute the value x^(ω¹⁺ᵉ). This algorithm has quite a few special cases,
    which are commented inline.
 *)
Definition VF_exp_single (x:VForm) (e:VForm) : VForm :=
  match x with
  | F 0     => VF_one (* 0 ^ (ω¹⁺ᵉ) = 1 *)
  | F 1     => VF_one (* 1 ^ (ω¹⁺ᵉ) = 1 *)
  | F _     => match e with
               | F 0     => V (F 0) (F 0)
               | F (S m) => V (V (F m) (F 0)) (F 0)
               | _       => V (V e (F 0)) (F 0)
               end
  | V a _ => V (VF_mul_single (VF_onePlus a) e) (F 0)
  end.

(** Compute xʸ. The terms on the right are used to exponentate the entire
    term on the left via VF_exp_single and all the results are multiplied together.
  *)
Definition VF_exp (x:VForm) : VForm -> VForm :=
  let x' := Vnormalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | F 0    => VF_one
  | F n    => if VF_isZero x then F 1 else Nat.iter n (fun a => VF_mul a x') (F 1)
  | V b y' => VF_mul (VF_exp_single x' b) (loop y')
  end.

Lemma VF_normal_dominates : forall x a,
    VF_normal (V a x) ->
    exists n:ω, expOrd ω (1+VF_denote a) * n ≥ VF_denote x.
Proof.
  induction x; simpl; intuition.
  - exists 1%nat. simpl.
    rewrite mulOrd_one_r.
    transitivity (expOrd ω 1).
    rewrite expOrd_one'; auto.
    apply index_le. apply omega_gt0.
    apply expOrd_monotone.
    apply succ_least. rewrite <- addOrd_le1. apply succ_lt.
  - destruct x2; simpl.
    + exists 2%nat. simpl.
      rewrite veblen_onePlus; auto.
      rewrite mulOrd_succ.
      apply addOrd_monotone.
      rewrite mulOrd_one_r.
      apply expOrd_monotone; auto.
      apply addOrd_monotone; auto with ord.
      transitivity (expOrd ω 1).
      rewrite expOrd_one'; auto.
      apply index_le. apply omega_gt0.
      apply expOrd_monotone.
      apply addOrd_le1.

    + destruct (IHx2 a) as [n Hn].
      simpl in *; intuition.
      rewrite H4. auto.
      exists (S n).
      simpl.
      rewrite mulOrd_succ.
      rewrite veblen_onePlus; auto.
      simpl in Hn. rewrite Hn.
      rewrite H2.
      clear.
      induction n; simpl.
      * rewrite mulOrd_zero_r.
        rewrite addOrd_zero_l.
        rewrite addOrd_zero_r.
        reflexivity.
      * rewrite mulOrd_succ.
        rewrite addOrd_assoc.
        apply addOrd_monotone; auto with ord.
Qed.

Lemma VF_mul_single_correct : forall x e,
    VF_normal x ->
    VF_denote (VF_mul_single x e) ≈ VF_denote x * expOrd ω (1+VF_denote e).
Proof.
  destruct x as [m|a x]; intros; simpl.
  - destruct m; simpl.
    + rewrite mulOrd_zero_l. reflexivity.
    + rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      transitivity (1 * expOrd ω (1 + VF_denote e)).
      rewrite mulOrd_one_l; reflexivity.
      transitivity ((1 + natOrdSize m) * expOrd ω (1 + VF_denote e)).
      split.
      apply mulOrd_monotone1.
      apply addOrd_le1.
      apply expOrd_omega_collapse with m; auto.
      rewrite mulOrd_one_l; auto with ord.
      rewrite onePlus_finite_succ. reflexivity.

  - repeat rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    rewrite VF_add_correct.
    rewrite addOrd_assoc.
    rewrite (VF_onePlus_correct e).
    rewrite expOrd_add.
    destruct (VF_normal_dominates x a) as [n Hn]; auto.
    split.
    apply mulOrd_monotone1.
    apply addOrd_le1.
    apply expOrd_omega_collapse with n; auto.
Qed.

Theorem VF_mul_correct : forall y x,
  VF_denote (VF_mul x y) ≈ VF_denote x * VF_denote y.
Proof.
  induction y; simpl; intros.
  - induction n; simpl.
    symmetry. apply mulOrd_zero_r.
    rewrite mulOrd_succ.
    rewrite VF_add_correct.
    apply addOrd_eq_mor; auto.
    apply Vnormalize_equal.
  - rewrite VF_add_correct.
    rewrite VF_mul_single_correct; auto.
    rewrite veblen_onePlus; auto.
    rewrite ordDistrib_left.
    rewrite IHy2.
    apply addOrd_eq_mor; auto with ord.
    apply mulOrd_eq_mor; auto with ord.
    apply Vnormalize_equal.
    apply Vnormalize_normal.
Qed.


Lemma VF_exp_single_correct x e :
  VF_normal x ->
  VF_denote (VF_exp_single x e) ≈ expOrd (VF_denote x) (expOrd ω (1+(VF_denote e))).
Proof.
  unfold VF_exp_single.
  destruct x. simpl; intros.
  - destruct n. simpl.
    + split.
      apply succ_least. apply expOrd_nonzero.
      rewrite expOrd_unfold.
      apply lub_least; intros; auto with ord.
      apply sup_least. intros. rewrite mulOrd_zero_r.
      auto with ord.
    + destruct n; simpl.
      { split. apply succ_least. apply expOrd_nonzero.
        apply expOrd_one_base. }
      destruct e.
      * destruct n0.
        ** simpl.
           rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           rewrite (expNatToOmegaPow (S (S n)) 0).
           rewrite expOrd_zero.
           rewrite addOrd_zero_r; auto with ord.
           simpl.
           apply succ_trans. apply succ_least; auto with ord.
        ** simpl.
           rewrite onePlus_veblen; auto.
           rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           rewrite <- (onePlus_finite_succ n0).
           rewrite (expNatToOmegaPow (S (S n)) (1+natOrdSize n0)).
           reflexivity.
           apply succ_trans. apply succ_least; auto with ord.
      * simpl.
        rewrite onePlus_veblen; auto.
        do 2 (rewrite veblen_onePlus; auto).
        repeat rewrite addOrd_zero_r.
        rewrite (expNatToOmegaPow (S (S n)) (veblen (addOrd 1) (1 + VF_denote e1) (VF_denote e2))).
        rewrite onePlus_veblen; auto.
        reflexivity.
        simpl; apply succ_trans. apply succ_least; auto with ord.
  - intro Hnorm.
    unfold VF_denote at 1; fold VF_denote.
    simpl.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    transitivity (expOrd ω (VF_denote (VF_mul_single (VF_onePlus x1) e))).
    apply expOrd_eq_mor; auto with ord.
    { destruct x1; simpl.
      apply onePlus_veblen; auto.
      apply onePlus_veblen; auto. }
    rewrite VF_mul_single_correct; auto.
    rewrite veblen_onePlus; auto.
    transitivity (expOrd ω (VF_denote (VF_onePlus x1) * expOrd ω (1 + VF_denote e))).
    apply expOrd_eq_mor; auto with ord.

    rewrite expOrd_mul.
    rewrite VF_onePlus_correct.
    split.
    apply expOrd_monotone_base.
    apply addOrd_le1.
    destruct (VF_normal_dominates x2 x1) as [m Hm]; auto.
    apply expToOmega_collapse_tower with m; auto.
    transitivity (expOrd ω 1).
    { rewrite expOrd_one'; auto.
      transitivity (natOrdSize (1+m)).
      rewrite natOrdSize_add. reflexivity.
      apply index_le. apply omega_gt0. }
    apply expOrd_monotone.
    apply succ_least. rewrite <- addOrd_le1. apply succ_lt.
    simpl in Hnorm. unfold VF_onePlus. destruct x1; intuition.
Qed.


Theorem VF_exp_correct : forall y x,
  VF_denote (VF_exp x y) ≈ expOrd (VF_denote x) (VF_denote y).
Proof.
  induction y; simpl; intros.
  - destruct n; simpl.
    + rewrite expOrd_zero.
      reflexivity.
    + destruct (VF_isZero x).
      * subst x. simpl.
        split.
        apply succ_least. apply expOrd_nonzero.
        rewrite expOrd_unfold; simpl.
        apply lub_least; auto with ord.
        apply sup_least; intro.
        rewrite mulOrd_zero_r. auto with ord.
      * rewrite VF_mul_correct.
        rewrite expOrd_succ; auto.
        apply mulOrd_eq_mor; auto with ord.
        2: { apply Vnormalize_equal. }
        induction n.
        ** simpl Nat.iter.
           simpl.
           rewrite expOrd_zero.
           reflexivity.
        ** simpl natOrdSize.
           unfold Nat.iter. unfold nat_rect.
           rewrite VF_mul_correct.
           rewrite expOrd_succ; auto.
           apply mulOrd_eq_mor; auto.
           apply Vnormalize_equal.
  - rewrite veblen_onePlus; auto.
    rewrite VF_mul_correct.
    rewrite VF_exp_single_correct.
    rewrite Vnormalize_equal.
    rewrite IHy2.
    rewrite (expOrd_add (VF_denote x)).
    reflexivity.
    apply Vnormalize_normal.
Qed.

Theorem VF_reflects_nat n : reflects VForm VF_denote ORD (sz n) (F n).
Proof.
  simpl. reflexivity.
Qed.

Theorem VF_reflects_zero : reflects VForm VF_denote ORD 0 (F 0).
Proof.
  apply (VF_reflects_nat 0%nat).
Qed.

Theorem VF_reflects_one : reflects VForm VF_denote ORD 1 (F 1).
Proof.
  apply (VF_reflects_nat 1%nat).
Qed.

Theorem VF_reflects_omega : reflects VForm VF_denote ORD ω VF_omega.
Proof.
  simpl; intros.
  rewrite veblen_onePlus; auto.
  do 2 rewrite addOrd_zero_r.
  rewrite expOrd_one'; auto with ord.
  apply omega_gt0.
Qed.

Theorem VF_reflects_add : reflects VForm VF_denote (ORD ==> ORD ==> ORD) addOrd VF_add.
Proof.
  simpl; intros.
  rewrite VF_add_correct.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

Theorem VF_reflects_succ : reflects VForm VF_denote (ORD ==> ORD) succOrd VF_succ.
Proof.
  simpl; intros.
  unfold VF_succ.
  transitivity (x + 1).
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  reflexivity.
  apply VF_reflects_add; auto.
  apply VF_reflects_one.
Qed.

Theorem VF_reflects_mul : reflects VForm VF_denote (ORD ==> ORD ==> ORD) mulOrd VF_mul.
Proof.
  simpl; intros.
  rewrite VF_mul_correct.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

Theorem VF_reflects_expOmega : reflects VForm VF_denote (ORD ==> ORD) (expOrd ω) VF_expOmega.
Proof.
  simpl; intros.
  rewrite H.
  unfold VF_expOmega.
  destruct a; simpl.
  destruct n; simpl.
  * rewrite expOrd_zero; reflexivity.
  * rewrite onePlus_finite_succ.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    reflexivity.
  * rewrite onePlus_veblen; auto.
    do 2 (rewrite veblen_onePlus; auto).
    rewrite addOrd_zero_r.
    reflexivity.
    apply addOrd_complete; auto.
    apply expOrd_complete; auto.
    apply omega_gt0.
    apply omega_complete.
Qed.

Theorem VF_reflects_expOrd : reflects VForm VF_denote (ORD ==> ORD ==> ORD) expOrd VF_exp.
  simpl; intros.
  rewrite H.
  rewrite H0.
  symmetry.
  apply VF_exp_correct.
Qed.

Theorem VF_ε₀ : VF ≈ ε 0.
Proof.
  split.
  - rewrite ord_le_unfold; intro x.
    apply VNotation_below_ε₀.
  - apply ε0_least_exp_closed with (F 0) VF_succ VF_expOmega.
    apply VF_reflects_zero.
    apply VF_reflects_succ.
    apply VF_reflects_expOmega.
Qed.

(** Note, we cannot go any higher in Knuth's "up arrow" hierarchy. If we could compute x↑↑y,
    for VForm values x and y, then we could compute ω↑↑ω = ε₀, which is too large.
  *)
Theorem VF_reflects_KnuthUp2_impossible :
  ~exists f, reflects VForm VF_denote (ORD ==> ORD ==> ORD) (KnuthUp 2) f.
Proof.
  intros [f Hf].
  hnf in Hf.
  specialize (Hf ω VF_omega VF_reflects_omega).
  hnf in Hf.
  specialize (Hf ω VF_omega VF_reflects_omega).
  red in Hf.
  rewrite KnuthUp_epsilon in Hf.
  apply (ord_lt_irreflexive (ε 0)).
  rewrite Hf at 1.
  apply VNotation_below_ε₀.
Qed.


Require ClassicalFacts.
From Ordinal Require Import Classical.


Theorem VF_has_enough_notations (EM:ClassicalFacts.excluded_middle) :
  forall x:Ord, x < ε 0 -> exists c:VF, x ≈ c.
Proof.
  induction x as [x Hx] using ordinal_induction. intro H.
  destruct (classical.ordinal_discriminate EM x) as [Hzero|[Hsucc|Hlimit]].
  - (* Zero ordinal, exhibit Z *)
    exists (F 0%nat). simpl.
    apply ord_isZero in Hzero. auto.

  - (* Successor ordinal *)
    apply ord_isSucc in Hsucc.
    destruct Hsucc as [o Ho].

    (* invoke the induction hypothesis *)
    destruct (Hx o) as [vo Hvo].
    rewrite Ho. apply succ_lt.
    transitivity x; auto.
    rewrite Ho. apply succ_lt.

    (* exhibit the successor V form and wrap up *)
    exists (VF_succ vo).
    rewrite Ho.
    apply VF_reflects_succ; auto.

  - (* x is a limit, it must be a fixpoint of (addOrd 1) *)
    assert (Hlimit' : 1 + x <= x).
    { apply limit_onePlus; auto. }

    (* x cannot be an ε number, as it would be too large *)
    assert (Hepsilon: x < veblen (addOrd 1) x 0).
    { destruct (classical.order_total EM (veblen (addOrd 1) x 0) x); auto.
      elim (ord_lt_irreflexive (ε 0)).
      apply ord_le_lt_trans with x; auto.
      unfold ε. simpl.
      apply fixOrd_least; auto.
      apply normal_monotone. apply powOmega_normal.
      rewrite ord_le_unfold; intros [].
      rewrite veblen_onePlus in H0; auto.
      rewrite addOrd_zero_r in H0. auto.
      apply classical.ord_complete; auto.
    }

    (* decompose the ordinal *)
    destruct (veblen_decompose EM (addOrd 1) (onePlus_normal) x) as [a [b [Hab[Ha0[Ha Hb]]]]]; auto.

    (* invoke the induction hypotheses *)
    destruct (Hx a) as [va Hva]; auto.
    transitivity x; auto.
    destruct (Hx b) as [vb Hvb]; auto.
    transitivity x; auto.

    (* adjust va *)
    assert (Hva' :  exists va', 1 + VF_denote va' ≈ VF_denote va).
    { destruct va.
      destruct n.
      - elim (ord_lt_irreflexive a).
        rewrite Hva at 1. simpl. auto.
      - exists (F n). simpl.
        apply onePlus_finite_succ.
      - exists (V va1 va2).
        simpl.
        apply onePlus_veblen; auto. }
    destruct Hva' as [va' Hva'].

    (* exhibit the V form and wrap up *)
    exists (V va' vb).
    rewrite Hab. simpl.
    apply veblen_eq_mor; auto with ord.
    apply normal_monotone; auto.
    rewrite Hva'.
    auto.
Qed.

Corollary VF_has_enough_normal_forms (EM:ClassicalFacts.excluded_middle) :
  forall x:Ord, x < ε 0 -> exists c:VF, x ≈ c /\ VF_normal c.
Proof.
  (* We could likely do this in one step, proving the normal form property
     as we go, but invoking the normalization procedure is simpler. *)
  intros. destruct (VF_has_enough_notations EM x) as [c Hc]; auto.
  exists (Vnormalize c). split.
  rewrite Hc.
  symmetry. apply Vnormalize_equal.
  apply Vnormalize_normal.
Qed.
