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
| V : VForm -> VForm -> VForm
| W : VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | F n   => natOrdSize n
  | V a x => veblen (addOrd 1) (1 + VF_denote a) (VF_denote x)
  | W a x => veblen (expOrd ω) (1 + VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x; simpl.
  - apply natOrdSize_complete.
  - apply veblen_complete; auto.
    apply onePlus_normal; auto.
    intros; apply addOrd_complete; auto.
    apply succ_complete; apply zero_complete.
    apply addOrd_complete; auto.
    apply succ_complete; apply zero_complete.
  - apply veblen_complete; auto.
    apply powOmega_normal.
    intros; apply expOrd_complete; auto.
    apply (index_lt _ 0%nat).
    apply omega_complete.
    apply addOrd_complete; auto.
    apply succ_complete; apply zero_complete.
Qed.

Lemma onePlus_nonzero : forall x, 0 < 1 + x.
Proof.
  intros. rewrite <- addOrd_le1. apply succ_lt.
Qed.


Local Hint Unfold powOmega : core.
Local Hint Resolve
      VF_complete veblen_complete addOrd_complete natOrdSize_complete
      onePlus_normal powOmega_normal expOrd_complete
      omega_complete succ_complete zero_complete
      normal_monotone normal_complete
      addOrd_increasing onePlus_nonzero
      omega_gt0 omega_gt1 : core.

Lemma V_collapse :
  forall a b x,
    VF_denote a < VF_denote b ->
    VF_denote (V a (V b x)) ≈ VF_denote (V b x).
Proof.
  intros. simpl.
  apply veblen_fixpoints; auto.
Qed.

Lemma W_collapse :
  forall a b x,
    VF_denote a < VF_denote b ->
    VF_denote (W a (W b x)) ≈ VF_denote (W b x).
Proof.
  intros. simpl.
  apply veblen_fixpoints; auto.
Qed.

Lemma VW_collapse : forall a b c,
  VF_denote a < VF_denote (W b c) ->
  VF_denote (V a (W b c)) ≈ VF_denote (W b c).
Proof.
  simpl VF_denote.
  intros.
  split.
  2: { apply veblen_inflationary; auto. }
  apply veblen_collapse; auto with ord.
  rewrite <- onePlus_veblen; auto.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite <- (veblen_fixpoints _ powOmega_normal 0 (1+VF_denote b) (VF_denote c)) at 2; auto.
  rewrite veblen_zero.
  reflexivity.
Qed.

Lemma VW_collapse2 : forall b c,
  VF_denote (V (W b c) (F 0)) ≈ VF_denote (W b c).
Proof.
  intros. simpl.
  rewrite <- (veblen_fixpoints _ (powOmega_normal) 0) at 2; auto.
  rewrite veblen_zero.
  rewrite veblen_onePlus; auto.
  rewrite onePlus_veblen; auto.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Definition VF_isZero x : { x = F 0 } + { 0 < VF_denote x }.
Proof.
  destruct x. destruct n.
  - left. reflexivity.
  - right. simpl; auto with ord.
  - right. simpl. apply veblen_nonzero; auto.
  - right. simpl. apply veblen_nonzero; auto.
Qed.

Fixpoint VF_compare (x:VForm) : VForm -> ordering :=
  fix inner (y:VForm) : ordering :=
    match x, y with
    | F m, F n => nat_compare m n
    | F _, V _ _ => LT
    | F _, W _ _ => LT
    | V _ _, F _ => GT
    | W _ _, F _ => GT

    | V a x', V b y' =>
      match VF_compare a b with
      | LT => VF_compare x' y
      | EQ => VF_compare x' y'
      | GT => inner y'
      end

    | W a x', W b y' =>
      match VF_compare a b with
      | LT => VF_compare x' y
      | EQ => VF_compare x' y'
      | GT => inner y'
      end

    | V a x', W b y' =>
      match VF_compare a (W b y') with
      | LT => VF_compare x' (W b y')
      | EQ => if VF_isZero x' then EQ else GT
      | GT => GT
      end

    | W a x', V b y' =>
      match inner b with
      | LT => LT
      | EQ => if VF_isZero y' then EQ else LT
      | GT => inner y'
      end
    end.

Lemma VW_compare_eq a x b y :
  VF_compare (V a x) (W b y) =
  match VF_compare a (W b y) with
  | LT => VF_compare x (W b y)
  | EQ => if VF_isZero x then EQ else GT
  | GT => GT
  end.
Proof. reflexivity. Qed.

Lemma WV_compare_eq a x b y :
  VF_compare (W a x) (V b y) =
  match VF_compare (W a x) b with
  | LT => LT
  | EQ => if VF_isZero y then EQ else LT
  | GT => VF_compare (W a x) y
  end.
Proof. reflexivity. Qed.

Lemma VF_compare_correct : forall x y,
    ordering_correct (VF_compare x y) (VF_denote x) (VF_denote y).
Proof.
  unfold ordering_correct.
  induction x as [m|a IHa x IHx|a IHa x IHx].
  (* x => F n case *)
  - destruct y as [n|b y|b y]; simpl; auto with ord.
    + generalize (nat_compare_correct m n).
      destruct (nat_compare m n); intros; subst; auto with ord.
      apply natOrdSize_increasing; auto.
      apply natOrdSize_increasing; auto.
    + apply finite_veblen_lt; auto.
    + apply finite_veblen_lt; auto.

  (* x => V a x case *)
  - induction y as [n|b IHb y IHy|b IHb y IHy].
    (* y => F n case *)
    + simpl. apply finite_veblen_lt; auto.
    (* y => V b y case *)
    + simpl. apply (veblen_compare_correct); auto.
      * generalize (IHa b).
        destruct (VF_compare a b); simpl; auto with ord.
        intros; rewrite H. auto with ord.
      * apply IHx.
      * apply IHx.

    (* y => W b y case *)
    + rewrite VW_compare_eq.
      generalize (IHa (W b y)); simpl.
      destruct (VF_compare a (W b y)); intros Hasub.
      * generalize (IHx (W b y)).
        destruct (VF_compare x (W b y)); intros Hxsub.
        ** apply veblen_collapse'; auto.
           rewrite <- onePlus_veblen; auto.
           rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
           rewrite veblen_zero.
           reflexivity.
        ** split.
           apply veblen_collapse; auto.
           rewrite <- onePlus_veblen; auto.
           apply Hxsub.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
           rewrite veblen_zero.
           rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           reflexivity.
           rewrite <- Hxsub.
           apply veblen_inflationary; auto.
        ** simpl in Hxsub.
           rewrite veblen_onePlus; auto.
           rewrite <- (addOrd_le2 _ (VF_denote x)). apply Hxsub.
      * destruct (VF_isZero x); subst; simpl; auto with ord.
        ** rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           rewrite Hasub.
           rewrite onePlus_veblen; auto.
           symmetry.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
           rewrite veblen_zero.
           reflexivity.
        ** rewrite veblen_onePlus; auto.
           rewrite Hasub.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
           rewrite veblen_zero.
           rewrite <- addOrd_zero_r.
           rewrite onePlus_veblen; auto.
      * rewrite veblen_onePlus; auto.
        rewrite <- (addOrd_le1 (expOrd ω (1 + VF_denote a))).
        rewrite <- (veblen_fixpoints _ powOmega_normal 0); auto.
        rewrite veblen_zero.
        apply expOrd_increasing; auto.
        rewrite <- onePlus_veblen; auto.

  (* x => W a x case *)
  - induction y as [n|b IHb y IHy|b IHb y IHy].
    (* y => F n case *)
    + simpl; apply finite_veblen_lt; auto.
    (* y => V b y case *)
    + rewrite WV_compare_eq.
      destruct (VF_compare (W a x) b).
      * simpl.
        rewrite veblen_onePlus; auto.
        rewrite <- (addOrd_le1 (expOrd ω (1+VF_denote b))).
        simpl in IHb.
        rewrite <- (veblen_fixpoints _ powOmega_normal 0); auto.
        rewrite veblen_zero.
        apply expOrd_increasing; auto.
        rewrite <- onePlus_veblen; auto.
        
      * destruct (VF_isZero y); subst; simpl.
        ** rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           rewrite <- IHb.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
           rewrite veblen_zero.
           simpl.           
           rewrite onePlus_veblen; auto with ord.
        ** rewrite veblen_onePlus; auto.
           rewrite <- IHb.
           simpl.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
           rewrite veblen_zero.
           rewrite <- addOrd_zero_r.
           rewrite onePlus_veblen; auto.
      * destruct (VF_compare (W a x) y).
        ** simpl.
           rewrite veblen_onePlus; auto.
           rewrite <- (addOrd_le2 _ (VF_denote y)).
           apply IHy.
           
        ** simpl; split.
           rewrite IHy.
           apply veblen_inflationary; auto.
           apply veblen_collapse; auto.
           rewrite <- onePlus_veblen; auto.
           apply IHy.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
           rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           rewrite veblen_zero.
           reflexivity.
        ** simpl.
           apply veblen_collapse'; auto.
           rewrite <- onePlus_veblen; auto.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
           rewrite veblen_zero.
           rewrite veblen_onePlus; auto.
           rewrite addOrd_zero_r.
           reflexivity.

    (* y => W b y case *)
    + simpl; apply (veblen_compare_correct); auto.
      * generalize (IHa b).
        destruct (VF_compare a b); simpl; auto.
        intro H; rewrite H; auto with ord.
      * apply (IHx y).
      * apply IHx.
Qed.

Global Opaque VF_compare.

Theorem VF_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y); intros.
  - left; assumption.
  - right; apply H.
  - right; auto with ord.
Qed.

Fixpoint VF_isNormal (x:VForm) : Prop :=
  match x with
  | F _ => True
  | V a b => VF_isNormal a /\
             VF_isNormal b /\
             match b with
             | F 0 => match a with | W _ _ => False | _ => True end
             | F _ => True
             | V x _ => VF_denote a >= VF_denote x
             | W _ _ => VF_denote a >= VF_denote b
             end
  | W a b => VF_isNormal a /\
             VF_isNormal b /\
             match b with
             | W x _ => VF_denote a >= VF_denote x
             | _ => True
             end
  end.

Definition VF_subterm_shrink x :=
  match x with
  | F _ => True
  | V a b => VF_denote a < VF_denote x /\
             VF_denote b < VF_denote x
  | W a b => VF_denote a < VF_denote x /\
             VF_denote b < VF_denote x
  end.

Lemma VF_normal_subterm_shrink :
  forall x,
    VF_isNormal x ->
    VF_subterm_shrink x.
Proof.
  induction x; simpl; intuition.
  - destruct x2; simpl; intuition.
    destruct n; simpl; intuition.
    destruct x1; simpl; intuition.
    + apply finite_veblen_lt; auto. 
    + apply veblen_subterm1_zero_nest; simpl in *; intuition.
      rewrite onePlus_veblen; auto.
    + apply veblen_subterm1; auto.
      apply succ_trans; auto with ord.
      apply addOrd_le2.
    + apply veblen_subterm1; auto.
      apply veblen_nonzero; auto.
      apply addOrd_le2.
    + apply veblen_subterm1; auto.
      apply veblen_nonzero; auto.
      apply addOrd_le2.
  - destruct x2; simpl; intuition.
    + apply finite_veblen_lt; auto.
    + apply veblen_increasing'; auto.
      apply H3.
    + eapply ord_le_lt_trans; [ apply H2 |].
      apply veblen_subterm1; auto.
      apply veblen_nonzero; auto.
      apply addOrd_le2.
  - destruct (VF_isZero x2).
    + subst x2. simpl.
      destruct x1; simpl; intuition.
      * apply finite_veblen_lt; auto.
      * apply ord_le_lt_trans with (veblen (expOrd ω) (1+VF_denote x1_1) (VF_denote x1_2)).
        apply veblen_monotone_func; auto.
        intros; apply onePlus_least_normal; auto.
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
        rewrite onePlus_veblen; auto.
      * apply veblen_subterm1_zero_nest; simpl in *; intuition.
        rewrite onePlus_veblen; auto.
    + apply veblen_subterm1; auto.
      apply addOrd_le2.
  - destruct x2; simpl; intuition.
    + apply finite_veblen_lt; auto.
    + simpl in H3. intuition.
      apply veblen_collapse'; auto.
      rewrite <- onePlus_veblen; auto.
      apply addOrd_increasing.
      eapply ord_lt_le_trans; [ apply H4 |].
      apply veblen_inflationary; auto.
      eapply ord_lt_le_trans; [ apply H5 |].
      apply veblen_inflationary; auto.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
      rewrite veblen_zero.
      reflexivity.
    + apply veblen_increasing'; simpl in *; intuition.
Qed.

Theorem VF_normal_forms_unique :
  forall x y,
    VF_isNormal x ->
    VF_isNormal y ->
    VF_denote x ≈ VF_denote y ->
    x = y.
Proof.
  induction x as [m|a Ha x Hx|a Ha x Hx].
  - destruct y as [n|b y|b y]; simpl; intuition.
    + f_equal.
      apply natOrdSize_unique; auto.
    + elim (ord_lt_irreflexive (natOrdSize m)).
      rewrite H1 at 2.
      apply finite_veblen_lt; auto.
    + elim (ord_lt_irreflexive (natOrdSize m)).
      rewrite H1 at 2.
      apply finite_veblen_lt; auto.
  - destruct y as [n|b y|b y]; simpl; intuition.
    + elim (ord_lt_irreflexive (natOrdSize n)).
      rewrite <- H1 at 2.
      apply finite_veblen_lt; auto.
    + assert (a = b).
      { apply Ha; auto.
        generalize (VF_compare_correct a b).
        destruct (VF_compare a b); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ onePlus_normal (1+VF_denote a) (1+VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (VF_normal_subterm_shrink (V a x)); simpl; intuition.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (veblen_fixpoints _ onePlus_normal (1+VF_denote b) (1+VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply (VF_normal_subterm_shrink (V b y)); simpl; intuition. }
      subst b.
      f_equal.
      apply Hx; auto.
      { generalize (VF_compare_correct x y).
        destruct (VF_compare x y); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          apply veblen_increasing'; auto with ord.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          apply veblen_increasing'; auto with ord. }
    + elim (ord_lt_irreflexive (veblen (addOrd 1) (1+VF_denote a) (VF_denote x))).
      apply ord_lt_le_trans with (VF_denote (V (V a x) (F 0))).
      apply (VF_normal_subterm_shrink (V (V a x) (F 0))).
      simpl; intuition.
      rewrite H1.
      transitivity (veblen (expOrd ω) 0 (veblen (expOrd ω) (1+VF_denote b) (VF_denote y))).
      rewrite veblen_zero.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite onePlus_veblen; auto.
      apply expOrd_monotone; apply H1.
      apply (veblen_fixpoints _ powOmega_normal 0 (1+VF_denote b)); auto.

  - destruct y as [n|b y|b y]; simpl; intuition.
    + elim (ord_lt_irreflexive (natOrdSize n)).
      rewrite <- H1 at 2.
      apply finite_veblen_lt; auto.
    + elim (ord_lt_irreflexive (veblen (expOrd ω) (1+VF_denote a) (VF_denote x))).
      rewrite H1 at 1.
      apply ord_lt_le_trans with (VF_denote (V (V b y) (F 0))).
      apply (VF_normal_subterm_shrink (V (V b y) (F 0))).
      simpl; intuition.
      transitivity (veblen (expOrd ω) 0 (veblen (expOrd ω) (1+VF_denote a) (VF_denote x))).
      simpl.
      rewrite veblen_zero.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite onePlus_veblen; auto.
      apply expOrd_monotone; apply H1.
      apply (veblen_fixpoints _ powOmega_normal 0 (1+VF_denote a)); auto.

    + assert (a = b).
      { apply Ha; auto.
        generalize (VF_compare_correct a b).
        destruct (VF_compare a b); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ powOmega_normal (1+VF_denote a) (1+VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (VF_normal_subterm_shrink (W a x)); simpl; intuition.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (veblen_fixpoints _ powOmega_normal (1+VF_denote b) (1+VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply (VF_normal_subterm_shrink (W b y)); simpl; intuition. }
      subst b.
      f_equal.
      apply Hx; auto.
      { generalize (VF_compare_correct x y).
        destruct (VF_compare x y); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          apply veblen_increasing'; auto with ord.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          apply veblen_increasing'; auto with ord. }
Qed.

Definition Vnorm (a:VForm) (b:VForm) : VForm :=
  match b with
  | F 0   => match a with
             | W _ _ => a
             | _ => V a b
             end
  | F n   => V a b
  | V x y => match VF_compare a x with
             | LT => b
             | _  => V a b
             end
  | W _ _ => match VF_compare a b with
             | LT => b
             | _  => V a b
             end
  end.

Definition Wnorm (a:VForm) (b:VForm) : VForm :=
  match b with
  | F _   => W a b
  | V _ _ => W a b
  | W x y => match VF_compare a x with
             | LT => b
             | _  => W a b
             end

  end.

Fixpoint VF_normalize (x:VForm) : VForm :=
  match x with
  | F n => F n
  | V a b => Vnorm (VF_normalize a) (VF_normalize b)
  | W a b => Wnorm (VF_normalize a) (VF_normalize b)
  end.

Lemma Vnorm_isNormal : forall a b, VF_isNormal a -> VF_isNormal b -> VF_isNormal (Vnorm a b).
Proof.
  unfold Vnorm; simpl; intros.
  destruct b; simpl in *.
  destruct n; simpl; intuition.
  - destruct a; simpl in *; intuition.
  - generalize (VF_compare_correct a b1).
    destruct (VF_compare a b1); simpl; intuition.
    apply H1.
  - generalize (VF_compare_correct a (W b1 b2)).
    destruct (VF_compare a (W b1 b2)); simpl; intuition.
    apply H1.
Qed.

Lemma Wnorm_isNormal : forall a b, VF_isNormal a -> VF_isNormal b -> VF_isNormal (Wnorm a b).
Proof.
  unfold Wnorm; simpl; intros.
  destruct b; simpl in *; intuition.
  generalize (VF_compare_correct a b1).
  destruct (VF_compare a b1); simpl; intuition.
  apply H2.
Qed.

Theorem VF_normalize_isNormal : forall x, VF_isNormal (VF_normalize x).
Proof.
  induction x; simpl; intuition.
  apply Vnorm_isNormal; auto.
  apply Wnorm_isNormal; auto.
Qed.

Lemma Vnorm_equal : forall a b ,
  VF_isNormal a -> VF_isNormal b ->
  VF_denote (Vnorm a b) ≈ (VF_denote (V a b)).
Proof.
  intros; unfold Vnorm; simpl.
  destruct b; simpl; auto with ord.
  destruct n; simpl; auto with ord.
  - destruct a; simpl; auto with ord.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    rewrite onePlus_veblen; auto.
    reflexivity.
  - generalize (VF_compare_correct a b1).
    destruct (VF_compare a b1); simpl; intuition.
    symmetry. apply V_collapse; auto.
  - generalize (VF_compare_correct a (W b1 b2)).
    destruct (VF_compare a (W b1 b2)); simpl; intuition.
    symmetry. apply VW_collapse; auto.
Qed.

Lemma Wnorm_equal : forall a b,
    VF_isNormal a -> VF_isNormal b ->
    VF_denote (Wnorm a b) ≈ (VF_denote (W a b)).
Proof.
  intros; unfold Wnorm; simpl.
  destruct b; simpl in *; intuition.
  generalize (VF_compare_correct a b1).
  destruct (VF_compare a b1); simpl; auto with ord.
  intros; symmetry; apply W_collapse; auto.
Qed.

Theorem VF_normalize_equal : forall x, VF_denote (VF_normalize x) ≈ VF_denote x.
Proof.
  induction x; simpl; auto with ord.
  - rewrite Vnorm_equal; auto.
    simpl. rewrite IHx1. rewrite IHx2. reflexivity.
    apply VF_normalize_isNormal.
    apply VF_normalize_isNormal.
  - rewrite Wnorm_equal; auto.
    simpl. rewrite IHx1. rewrite IHx2. reflexivity.
    apply VF_normalize_isNormal.
    apply VF_normalize_isNormal.
Qed.

Lemma VF_isNormal_dominates : forall (b a:VF),
    match b with
    | V b1 _ => VF_denote a >= VF_denote b1
    | W _ _  => VF_denote a >= VF_denote b
    | F _ => True
    end ->
    VF_isNormal b ->
    exists n:ω, expOrd ω (1+a) * n ≥ b.
Proof.
  induction b; simpl; intuition.
  - exists 1%nat. simpl.
    rewrite mulOrd_one_r.
    transitivity (expOrd ω 1).
    rewrite expOrd_one'; auto.
    apply index_le.
    apply expOrd_monotone.
    apply addOrd_le1.
  - destruct (IHb2 a) as [n Hn]; intuition.
    destruct b2; simpl in *; intuition.
    rewrite H3; auto.
    rewrite H3; auto.

    exists (n+1)%nat.
    rewrite natOrdSize_add.
    rewrite ordDistrib_left.
    simpl.
    rewrite mulOrd_one_r.
    rewrite veblen_onePlus; auto.
    apply addOrd_monotone; auto.
  - exists 1%nat. simpl.
    rewrite mulOrd_one_r.
    rewrite <- H.
    rewrite onePlus_veblen; auto.
    apply normal_inflationary; auto.
Qed.

Fixpoint VF_add (x y:VForm) : VForm :=
  match x with
  | F m  => match y with
            | F n => F (n+m)
            | _   => y
            end
  | V a x' => V a (VF_add x' y)
  | W _ _  => V x y
  end.

Lemma VF_add_correct x y : VF_denote (VF_add x y) ≈ VF_denote x + VF_denote y.
Proof.
  induction x; simpl.
  - destruct y; simpl.
    rewrite natOrdSize_add. reflexivity.
    symmetry. apply finite_veblen; auto.
    symmetry. apply finite_veblen; auto.
  - rewrite IHx2.
    rewrite veblen_onePlus; auto.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_assoc. reflexivity.
  - rewrite veblen_onePlus; auto.
    rewrite onePlus_veblen; auto.
    symmetry.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    reflexivity.
Qed.    


Definition VF_one := F 1.
Definition VF_succ x := VF_add x VF_one.
Definition VF_expOmega x :=
  match x with
  | F 0 => F 1
  | F (S n) => V (F n) (F 0)
  | _ => V x (F 0)
  end.
Definition VF_epsilon x  := W (F 0) x.

Definition VF_veblen x y :=
  match x with
  | F 0 => VF_expOmega y
  | F (S n) => W (F n) y
  | _ => W x y
  end.

Lemma VF_succ_correct x : VF_denote (VF_succ x) ≈ succOrd (VF_denote x).
Proof.
  unfold VF_succ.
  rewrite VF_add_correct.
  simpl.
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Definition VF_onePlus (x:VForm) : VForm :=
  match x with
  | F n => F (S n)
  | _ => x
  end.

Lemma VF_onePlus_correct : forall x, VF_denote (VF_onePlus x) ≈ 1 + VF_denote x.
Proof.
  intro x. symmetry.
  destruct x; simpl; auto.
  apply onePlus_finite_succ.
  apply onePlus_veblen; auto.
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
  | _     => V (VF_add x (VF_onePlus e)) (F 0)
  end.

Lemma VF_mul_single_correct : forall x e,
    VF_isNormal x ->
    VF_denote (VF_mul_single x e) ≈ VF_denote x * expOrd ω (1+VF_denote e).
Proof.
  unfold VF_mul_single. intros.
  destruct x; simpl.
  + destruct n; simpl.
    * rewrite mulOrd_zero_l.
      reflexivity.
    * rewrite veblen_onePlus at 1; auto.
      rewrite addOrd_zero_r.
      transitivity (1 * expOrd ω (1+VF_denote e)).
      rewrite mulOrd_one_l. reflexivity.
      transitivity ((1+natOrdSize n) * expOrd ω (1+VF_denote e)).
      split.
      apply mulOrd_monotone1. apply addOrd_le1.
      apply expOrd_omega_collapse with n; auto.
      rewrite mulOrd_one_l. reflexivity.
      apply mulOrd_eq_mor; auto with ord.
      apply onePlus_finite_succ.
  + rewrite VF_add_correct.
    rewrite addOrd_assoc.
    rewrite veblen_onePlus at 1; auto.
    rewrite expOrd_add.
    rewrite veblen_onePlus at 1; auto.
    rewrite addOrd_zero_r.
    rewrite VF_onePlus_correct.
    split.
    { apply mulOrd_monotone1. apply addOrd_le1. }
    destruct (VF_isNormal_dominates x2 x1) as [n Hn]; auto.
    simpl in H; intuition.
    destruct x2; intuition.
    simpl in H; intuition.
    apply expOrd_omega_collapse with n; auto.
  + rewrite onePlus_veblen; auto.
    rewrite onePlus_veblen; auto.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    rewrite veblen_onePlus; auto.
    rewrite expOrd_add.
    apply mulOrd_eq_mor; auto with ord.
    symmetry.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    apply expOrd_eq_mor; auto with ord.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    reflexivity.
    rewrite VF_onePlus_correct.
    reflexivity.
Qed.

Definition VF_mul x : VForm -> VForm :=
  let x' := VF_normalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | F n    => Nat.iter n (fun a => VF_add a x') (F 0)
  | V b y' => VF_add (VF_mul_single x' b) (loop y')
  | _      => VF_mul_single x' y
  end.

Lemma VF_mul_correct x y : VF_denote (VF_mul x y) ≈ VF_denote x * VF_denote y.
Proof.
  induction y; simpl.
  - induction n; simpl.
    rewrite mulOrd_zero_r. reflexivity.
    rewrite mulOrd_succ.
    rewrite VF_add_correct.
    apply addOrd_eq_mor; auto.
    apply VF_normalize_equal.
  - rewrite VF_add_correct.
    rewrite VF_mul_single_correct.
    rewrite IHy2.
    rewrite veblen_onePlus; auto.
    rewrite ordDistrib_left.
    apply addOrd_eq_mor; auto with ord.
    apply mulOrd_eq_mor; auto with ord.
    apply VF_normalize_equal.
    apply VF_normalize_isNormal.
  - rewrite VF_mul_single_correct.
    simpl.
    rewrite onePlus_veblen; auto.
    apply mulOrd_eq_mor.
    apply VF_normalize_equal.
    symmetry.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    reflexivity.
    apply VF_normalize_isNormal.
Qed.

Lemma VF_expOmega_correct x : VF_denote (VF_expOmega x) ≈ expOrd ω (VF_denote x).
Proof.
  simpl.
  destruct x; simpl.
  destruct n; simpl.
  - rewrite expOrd_zero; reflexivity.
  - rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    apply expOrd_eq_mor; auto with ord.
    apply onePlus_finite_succ.
  - rewrite onePlus_veblen; auto.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    reflexivity.
  - rewrite onePlus_veblen; auto.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    reflexivity.
Qed.


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
  | _     => V (VF_mul_single x e) (F 0)
  end.

Local Opaque VF_mul.

Lemma VF_exp_single_correct x e :
  VF_isNormal x ->
  VF_denote (VF_exp_single x e) ≈ expOrd (VF_denote x) (expOrd ω (1+VF_denote e)).
Proof.
  unfold VF_exp_single. intros.
  destruct x; simpl.
  destruct n; simpl.
  - split.
    apply succ_least. apply expOrd_nonzero.
    rewrite expOrd_unfold.
    apply lub_least. reflexivity.
    apply sup_least; intros.
    rewrite mulOrd_zero_r. auto with ord.
  - destruct n; simpl.
    symmetry. apply expOrd_one_base.
    destruct e; simpl.
    destruct n0; simpl.
    + rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite (expNatToOmegaPow (S (S n)) 0).
      rewrite expOrd_zero.
      rewrite addOrd_zero_r; auto with ord.
      simpl. apply succ_trans. apply succ_least. apply succ_trans; auto with ord.
    + rewrite onePlus_veblen; auto.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite <- (onePlus_finite_succ n0).
      rewrite (expNatToOmegaPow (S (S n)) (1+natOrdSize n0)).
      reflexivity.
      apply succ_trans. apply succ_least; auto with ord.
    + rewrite onePlus_veblen; auto.
      do 2 (rewrite veblen_onePlus; auto).
      repeat rewrite addOrd_zero_r.
      rewrite (expNatToOmegaPow (S (S n)) (veblen (addOrd 1) (1 + VF_denote e1) (VF_denote e2))).
      rewrite onePlus_veblen; auto.
      reflexivity.
      simpl; apply succ_trans. apply succ_least; auto with ord.
    + rewrite onePlus_veblen; auto.
      do 2 (rewrite veblen_onePlus; auto).
      repeat rewrite addOrd_zero_r.
      rewrite (expNatToOmegaPow (S (S n)) (veblen (expOrd ω) (1 + VF_denote e1) (VF_denote e2))).
      rewrite onePlus_veblen; auto.
      reflexivity.
      simpl; apply succ_trans. apply succ_least; auto with ord.
  - rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    transitivity (expOrd ω (VF_denote (VF_mul_single (VF_onePlus x1) e))).
    apply expOrd_eq_mor; auto with ord.
    { destruct x1; simpl.
      apply onePlus_veblen; auto.
      apply onePlus_veblen; auto.
      apply onePlus_veblen; auto.
      apply addOrd_complete; auto. }
    rewrite VF_mul_single_correct; auto.
    rewrite veblen_onePlus; auto.
    transitivity (expOrd ω (VF_denote (VF_onePlus x1) * expOrd ω (1 + VF_denote e))).
    apply expOrd_eq_mor; auto with ord.
    rewrite expOrd_mul.
    rewrite VF_onePlus_correct.
    split.
    apply expOrd_monotone_base.
    apply addOrd_le1.
    destruct (VF_isNormal_dominates x2 x1) as [m Hm]; auto.
    simpl in *; intuition.
    destruct x2; auto.
    simpl in H; intuition.
    apply expToOmega_collapse_tower with m; auto.
    transitivity (expOrd ω 1).
    { rewrite expOrd_one'; auto.
      transitivity (natOrdSize (1+m)).
      rewrite natOrdSize_add. reflexivity.
      apply index_le. }
    apply expOrd_monotone.
    apply addOrd_le1.
    simpl in H; destruct x1; simpl in *; intuition.
  - repeat( rewrite onePlus_veblen; auto).
    repeat (rewrite veblen_onePlus; auto).
    repeat rewrite addOrd_zero_r.
    rewrite expOrd_add.
    rewrite expOrd_mul.
    rewrite VF_onePlus_correct.
    apply expOrd_eq_mor; auto with ord.
    symmetry.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    apply expOrd_eq_mor; auto with ord.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    apply expOrd_eq_mor; auto with ord.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    reflexivity.
    apply addOrd_complete; auto.
Qed.


(** Compute xʸ. The terms on the right are used to exponentate the entire
    term on the left via VF_exp_single and all the results are multiplied together.
  *)
Definition VF_exp (x:VForm) : VForm -> VForm :=
  let x' := VF_normalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | F 0    => VF_one
  | F n    => if VF_isZero x then F 1 else Nat.iter n (fun a => VF_mul a x') (F 1)
  | V b y' => VF_mul (VF_exp_single x' b) (loop y')
  | W _ _  => VF_exp_single x' y
  end.

Lemma VF_exp_correct : forall x y,
  VF_denote (VF_exp x y) ≈ expOrd (VF_denote x) (VF_denote y).
Proof.
  intro x. induction y; simpl.
  - destruct n; simpl.
    rewrite expOrd_zero.
    reflexivity.
    destruct (VF_isZero x). subst x.
    simpl.
    { split.
      apply succ_least. apply expOrd_nonzero.
      rewrite expOrd_unfold.
      apply lub_least; auto with ord.
      apply sup_least; intros.
      rewrite mulOrd_zero_r. auto with ord. }
    rewrite VF_mul_correct.
    rewrite expOrd_succ; auto.
    apply mulOrd_eq_mor; auto.
    induction n; simpl.
    rewrite expOrd_zero; reflexivity.
    rewrite VF_mul_correct.
    rewrite expOrd_succ; auto.
    apply mulOrd_eq_mor; auto.
    apply VF_normalize_equal.
    apply VF_normalize_equal.
  - rewrite VF_mul_correct.
    rewrite VF_exp_single_correct.
    rewrite IHy2.
    rewrite veblen_onePlus; auto.
    rewrite (expOrd_add _ _ (VF_denote y2)).
    apply mulOrd_eq_mor; auto with ord.
    apply expOrd_eq_mor; auto with ord.
    apply VF_normalize_equal.
    apply VF_normalize_isNormal.
  - rewrite VF_exp_single_correct.
    apply expOrd_eq_mor.
    apply VF_normalize_equal.
    simpl.
    rewrite onePlus_veblen; auto.
    symmetry.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    reflexivity.
    apply VF_normalize_isNormal.
Qed.

Lemma VF_epsilon_correct : forall x,
    VF_denote (VF_epsilon x) ≈ ε (VF_denote x).
Proof.
  simpl; intros.
  rewrite addOrd_zero_r.
  rewrite veblen_succ; auto.
  unfold ε.
  split; apply enum_fixpoints_func_mono; auto.
  apply veblen_normal; auto.
  intros. rewrite veblen_zero. reflexivity.
  apply veblen_normal; auto.
  intros. rewrite veblen_zero. reflexivity.
Qed.

Theorem VF_reflects_zero : reflects VForm VF_denote ORD 0 (F 0).
Proof.
  simpl; auto with ord.
Qed.

Theorem VF_reflects_one : reflects VForm VF_denote ORD 1 (F 1).
Proof.
  simpl; auto with ord.
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
  symmetry.
  apply VF_expOmega_correct.
Qed.

Theorem VF_reflects_expOrd : reflects VForm VF_denote (ORD ==> ORD ==> ORD) expOrd VF_exp.
Proof.
  simpl; intros.
  rewrite H.
  rewrite H0.
  symmetry.
  apply VF_exp_correct.
Qed.

Theorem VF_reflects_epsilon : reflects VForm VF_denote (ORD ==> ORD) ε VF_epsilon.
Proof.
  red; intros.
  rewrite VF_epsilon_correct.
  unfold ε.
  split; apply enum_fixpoints_monotone; auto; apply H.
Qed.

Theorem VF_reflects_veblen : reflects VForm VF_denote (ORD ==> ORD ==> ORD) (veblen (expOrd ω)) VF_veblen.
Proof.
  red; intros.
  destruct a; simpl.
  destruct n.
  rewrite VF_expOmega_correct.
  rewrite H. simpl.
  rewrite veblen_zero.
  rewrite H0. reflexivity.
  rewrite H. rewrite H0.
  simpl.
  rewrite onePlus_finite_succ.
  reflexivity.
  rewrite onePlus_veblen; auto.
  rewrite H. rewrite H0.
  simpl.
  reflexivity.
  rewrite onePlus_veblen; auto.
  rewrite H. rewrite H0.
  simpl.
  reflexivity.
Qed.

Theorem VF_below_Γ₀ : forall x, VF_denote x < Γ 0.
Proof.
  induction x; simpl VF_denote.
  - rewrite Γ_fixpoints; auto.
    apply finite_veblen_lt; auto.
    apply normal_nonzero. apply Γ_normal.
    apply normal_complete; auto. apply Γ_normal.
  - rewrite Γ_fixpoints; auto.
    rewrite <- (veblen_fixpoints _ powOmega_normal (1+VF_denote x1) (Γ 0) 0); auto.
    apply ord_le_lt_trans with
        (veblen powOmega (1+VF_denote x1) (VF_denote x2)).
    apply veblen_monotone_func; auto.
    intros. apply onePlus_least_normal; auto.
    apply veblen_increasing; auto.
    apply veblen_complete; auto.
    apply normal_complete; auto.
    apply Γ_normal.
    apply ord_lt_le_trans with (Γ 0); auto.
    apply (normal_inflationary (fun x => veblen powOmega x 0)).
    apply veblen_first_normal; auto.
    apply normal_complete; auto.
    apply Γ_normal.
    apply normal_complete; auto.
    apply Γ_normal.
    apply ord_lt_le_trans with (1+Γ 0); auto.
    rewrite Γ_fixpoints at 1; auto.
    rewrite onePlus_veblen; auto.
    rewrite <- Γ_fixpoints at 1; auto with ord.
    apply normal_nonzero.
    apply Γ_normal.
    apply normal_complete; auto.
    apply Γ_normal.

  - rewrite Γ_fixpoints; auto.
    rewrite <- (veblen_fixpoints _ powOmega_normal (1+VF_denote x1) (Γ 0) 0); auto.
    apply veblen_increasing; auto.
    apply veblen_complete; auto.
    apply normal_complete; auto.
    apply Γ_normal.
    apply ord_lt_le_trans with (Γ 0); auto.
    apply (normal_inflationary (fun x => veblen powOmega x 0)).
    apply veblen_first_normal; auto.
    apply normal_complete; auto.
    apply Γ_normal.
    apply normal_complete; auto.
    apply Γ_normal.
    apply ord_lt_le_trans with (1+Γ 0); auto.
    rewrite Γ_fixpoints at 1; auto.
    rewrite onePlus_veblen; auto.
    rewrite <- Γ_fixpoints at 1; auto with ord.
    apply normal_nonzero.
    apply Γ_normal.
    apply normal_complete; auto.
    apply Γ_normal.
Qed.

Lemma VF_limit : limitOrdinal VF.
Proof.
  hnf. split.
  exact (inhabits (F 0)).
  red; simpl; intros.
  exists (VF_succ a).
  simpl.
  rewrite VF_succ_correct.
  apply succ_lt.
Qed.

Lemma VF_veblen_closed : veblen powOmega VF 0 ≤ VF.
Proof.
  transitivity (veblen powOmega (boundedSup VF (fun x => x)) 0).
  { apply veblen_monotone_first.
    intros; apply expOrd_monotone; auto.
    apply (limit_boundedSup VF). apply VF_limit. }
  unfold boundedSup. unfold VF at 1.
  transitivity (supOrd (fun x => veblen powOmega (VF_denote x) 0)).
  { apply veblen_continuous_first; auto. exact (F 0). }
  apply sup_least. intro x.
  transitivity (VF_denote (VF_veblen x (F 0))).
  apply VF_reflects_veblen; simpl; auto with ord.
  apply index_le.
Qed.

Theorem VF_Γ₀ : VF ≈ Γ 0.
Proof.
  split.
  - rewrite ord_le_unfold. intro x.
    apply VF_below_Γ₀.
  - unfold Γ.
    rewrite enum_fixpoints_zero; auto.
    unfold fixOrd. apply sup_least.
    intro i; induction i.
    + simpl; auto with ord.
    + simpl.
      transitivity (veblen powOmega VF 0).
      apply veblen_monotone_first; auto.
      apply VF_veblen_closed.
    + apply veblen_first_normal; auto.
Qed.


Require ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VW_has_enough_notations (EM:ClassicalFacts.excluded_middle) :
  forall x, x < Γ 0 -> exists v:VF, v ≈ x.
Proof.
  induction x as [x Hx] using ordinal_induction. intro H.
  destruct (classical.ordinal_discriminate EM x) as [Hzero|[Hsucc|Hlimit]].
  - (* Zero ordinal, exhibit Z *)
    exists (F 0). simpl.
    apply ord_isZero in Hzero. symmetry; auto.

  - (* Successor ordninal *)
    apply ord_isSucc in Hsucc.
    destruct Hsucc as [o Ho].

    (* invoke the induction hypothesis *)
    destruct (Hx o) as [vo Hvo].
    rewrite Ho. apply succ_lt.
    transitivity x; auto.
    rewrite Ho. apply succ_lt.

    (* exhibit the successor V form and wrap up *)
    exists (VF_succ vo).
    rewrite Ho. rewrite <- Hvo.
    apply VF_succ_correct.

  - (* x is a limit, it must be a fixpoint of (addOrd 1) *)
    assert (Hlimit' : 1 + x <= x). { apply limit_onePlus; auto. }

    destruct (classical.order_total EM (veblen (addOrd 1) x 0) x) as [Hepsilon|Hepsilon].

    (* x is an epsilon number, find its W form *)
    * rewrite veblen_onePlus in Hepsilon; auto.
      2:{ apply classical.ord_complete; auto. }
      rewrite addOrd_zero_r in Hepsilon.

      (* x cannot be a Γ number, as it would be too large *)
      assert (Hgamma : x < veblen powOmega x 0).
      { destruct (classical.order_total EM (veblen powOmega x 0) x); auto.
        elim (ord_lt_irreflexive (Γ 0)).
        apply ord_le_lt_trans with x; auto.
        unfold Γ. simpl.
        apply fixOrd_least; auto.
        intros; apply veblen_monotone_first; auto.
        rewrite ord_le_unfold; intros []. }

      (* decompose the ordinal *)
      destruct (veblen_decompose EM powOmega powOmega_normal x) as [a [b [Hab [Ha0[Ha Hb]]]]]; auto.

      (* invoke the induction hypotheses *)
      destruct (Hx a) as [va Hva]; auto.
      transitivity x; auto.
      destruct (Hx b) as [vb Hvb]; auto.
      transitivity x; auto.

      (* Adjust va' *)
      assert (Hva' :  exists va', 1 + VF_denote va' ≈ VF_denote va).
      { destruct va.
        destruct n.
        - elim (ord_lt_irreflexive a).
          rewrite <- Hva at 1. simpl. auto.
        - exists (F n). simpl.
          apply onePlus_finite_succ.
        - exists (V va1 va2).
          simpl.
          apply onePlus_veblen; auto.
        - exists (W va1 va2).
          simpl.
          apply onePlus_veblen; auto. }
      destruct Hva' as [va' Hva'].

      (* exhibit the W form and wrap up *)
      exists (W va' vb).
      simpl. rewrite Hab.
      rewrite  Hva'.
      rewrite Hva. rewrite Hvb. reflexivity.

    (* x is not a epsilon number, find its V form *)
    * (* decompose the ordinal *)
      destruct (veblen_decompose EM (addOrd 1) (onePlus_normal) x) as [a [b [Hab[Ha0[Ha Hb]]]]]; auto.

      (* invoke the induction hypotheses *)
      destruct (Hx a) as [va Hva]; auto.
      transitivity x; auto.
      destruct (Hx b) as [vb Hvb]; auto.
      transitivity x; auto.

      (* Adjust va' *)
      assert (Hva' :  exists va', 1 + VF_denote va' ≈ VF_denote va).
      { destruct va.
        destruct n.
        - elim (ord_lt_irreflexive a).
          rewrite <- Hva at 1. simpl. auto.
        - exists (F n). simpl.
          apply onePlus_finite_succ.
        - exists (V va1 va2).
          simpl.
          apply onePlus_veblen; auto.
        - exists (W va1 va2).
          simpl.
          apply onePlus_veblen; auto. }
      destruct Hva' as [va' Hva'].

      (* exhibit the V form and wrap up *)
      exists (V va' vb).
      rewrite Hab. simpl.
      rewrite  Hva'.
      rewrite Hva. rewrite Hvb. reflexivity.
Qed.
