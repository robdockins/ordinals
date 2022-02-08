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
| Z : VForm
| V : VForm -> VForm -> VForm
| W : VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | V a x => veblen (addOrd 1) (VF_denote a) (VF_denote x)
  | W a x => veblen (expOrd ω) (VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x.
  - apply zero_complete.
  - simpl.
    apply veblen_complete; auto.
    apply onePlus_normal; auto.
    intros; apply addOrd_complete; auto.
    apply succ_complete; apply zero_complete.
  - simpl.
    apply veblen_complete; auto.
    apply powOmega_normal.
    intros; apply expOrd_complete; auto.
    apply (index_lt _ 0%nat).
    apply omega_complete.
Qed.

Local Hint Unfold powOmega : core.
Local Hint Resolve VF_complete veblen_complete
        onePlus_normal powOmega_normal expOrd_complete addOrd_complete
        omega_complete succ_complete zero_complete
        normal_monotone normal_complete omega_gt0 omega_gt1 : core.

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

Lemma WZ_collapse :
  forall a, VF_denote (W Z a) ≈ VF_denote (V a Z).
Proof.
  simpl; intros.
  rewrite veblen_zero.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.


Lemma VW_collapse : forall a b c,
  0 < VF_denote b ->
  VF_denote a < VF_denote (W b c) ->
  VF_denote (V a (W b c)) ≈ VF_denote (W b c).
Proof.
  simpl VF_denote.
  intros.
  split.
  2: { apply veblen_inflationary; auto. }

  apply veblen_collapse; auto with ord.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite <- (veblen_fixpoints _ powOmega_normal 0 (VF_denote b) (VF_denote c)) at 2; auto.
  rewrite veblen_zero in *.
  reflexivity.
Qed.

Lemma VW_collapse2 : forall b c,
  0 < VF_denote b ->
  VF_denote (V (W b c) Z) ≈ VF_denote (W b c).
Proof.
  intros. simpl.
  rewrite <- (veblen_fixpoints _ (powOmega_normal) 0) at 2; auto.
  rewrite veblen_zero.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Definition VF_isZero x : { x = Z } + { 0 < VF_denote x }.
Proof.
  destruct x.
  - left. apply eq_refl.
  - right. simpl. apply veblen_nonzero; auto.
  - right. simpl. apply veblen_nonzero; auto.
Qed.

Fixpoint VF_compare (x:VForm) : VForm -> ordering :=
  fix inner (y:VForm) : ordering :=
    match x, y with
    | Z, Z     => EQ
    | Z, V _ _ => LT
    | Z, W _ _ => LT
    | V _ _, Z => GT
    | W _ _, Z => GT

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
      if VF_isZero b then
        match VF_compare a y' with
        | LT => VF_compare x' (V y' Z)
        | EQ => if VF_isZero x' then EQ else GT
        | GT => GT
        end
      else
        match VF_compare a (W b y') with
        | LT => VF_compare x' (W b y')
        | EQ => if VF_isZero x' then EQ else GT
        | GT => GT
        end

    | W a x', V b y' =>
      if VF_isZero a then
        match VF_compare x' b with
        | LT => LT
        | EQ => if VF_isZero y' then EQ else LT
        | GT => inner y'
        end
      else
        match inner b with
        | LT => LT
        | EQ => if VF_isZero y' then EQ else LT
        | GT => inner y'
        end
    end.

Lemma VW_compare_eq a x b y :
  VF_compare (V a x) (W b y) =
  if VF_isZero b then
    match VF_compare a y with
    | LT => VF_compare x (V y Z)
    | EQ => if VF_isZero x then EQ else GT
    | GT => GT
    end
  else
    match VF_compare a (W b y) with
    | LT => VF_compare x (W b y)
    | EQ => if VF_isZero x then EQ else GT
    | GT => GT
    end.
Proof. reflexivity. Qed.

Lemma WV_compare_eq a x b y :
  VF_compare (W a x) (V b y) =
  if VF_isZero a then
    match VF_compare x b with
    | LT => LT
    | EQ => if VF_isZero y then EQ else LT
    | GT => VF_compare (W a x) y
    end
  else
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
  induction x as [|a IHa x IHx|a IHa x IHx].
  (* x => Z case *)
  - destruct y as [|b y|b y]; simpl; auto with ord.
    apply veblen_nonzero; auto.
    apply veblen_nonzero; auto.
  (* x => V a x case *)
  - induction y as [|b IHb y IHy|b IHb y IHy].
    (* y => Z case *)
    + simpl. apply veblen_nonzero; auto.
    (* y => V b y case *)
    + simpl. apply (veblen_compare_correct); auto.
      apply (IHa b). apply (IHx y). apply IHx.

    (* y => W b y case *)
    + rewrite VW_compare_eq.
      destruct (VF_isZero b).
      * subst b.
        change (ordering_correct 
                  (match VF_compare a y with
                   | LT => VF_compare x (V y Z)
                   | EQ => if VF_isZero x then EQ else GT
                   | GT => GT
                   end)
                  (VF_denote (V a x)) (VF_denote (W Z y))).
        rewrite WZ_collapse.
        simpl.
        apply veblen_compare_correct; auto.
        ** apply IHa.
        ** destruct (VF_isZero x); subst; simpl; auto with ord.
        ** apply IHx.

      * generalize (IHa (W b y)); simpl.
        destruct (VF_compare a (W b y)); intros Hasub.
        ** generalize (IHx (W b y)).
           destruct (VF_compare x (W b y)); intros Hxsub.
           *** apply veblen_collapse'; auto.
               rewrite veblen_onePlus; auto.
               rewrite addOrd_zero_r.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
               rewrite veblen_zero.
               reflexivity.
           *** split.
               apply veblen_collapse; auto.
               apply Hxsub.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
               rewrite veblen_zero.
               rewrite veblen_onePlus; auto.
               rewrite addOrd_zero_r.
               reflexivity.
               rewrite <- Hxsub.
               apply veblen_inflationary; auto.
           *** rewrite veblen_onePlus; auto.
               rewrite <- addOrd_le2. apply Hxsub.
        ** destruct (VF_isZero x); subst; simpl; auto with ord.
           *** rewrite veblen_onePlus; auto.
               rewrite addOrd_zero_r.
               rewrite Hasub.
               symmetry.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
               rewrite veblen_zero.
               reflexivity.
           *** rewrite veblen_onePlus; auto.
               rewrite Hasub.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
               rewrite veblen_zero.
               rewrite <- addOrd_zero_r.
               apply addOrd_increasing; auto.
        ** rewrite veblen_onePlus; auto.
           rewrite <- addOrd_le1.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0); auto.
           rewrite veblen_zero.
           apply expOrd_increasing; auto.

  (* x => W a x case *)
  - induction y as [|b IHb y IHy|b IHb y IHy].
    (* y => Z case *)
    + simpl; apply veblen_nonzero; auto.
    (* y => V b y case *)
    + rewrite WV_compare_eq.
      destruct (VF_isZero a).
      * subst a.
        change (ordering_correct 
                  match VF_compare x b with
                  | LT => LT
                  | EQ => if VF_isZero y then EQ else LT
                  | GT => VF_compare (W Z x) y
                  end
                  (VF_denote (W Z x)) (VF_denote (V b y))).
        rewrite WZ_collapse.
        assert (H : ordering_correct (VF_compare (W Z x) y) (VF_denote (W Z x)) (VF_denote y)); auto.
        rewrite WZ_collapse in H.

        apply veblen_compare_correct; auto.
        ** apply IHx.
        ** destruct (VF_isZero y); subst; simpl; auto with ord.
        ** simpl. apply veblen_nonzero; auto.

      * destruct (VF_compare (W a x) b).
        ** simpl.
           rewrite veblen_onePlus; auto.
           rewrite <- addOrd_le1.
           simpl in IHb.
           rewrite <- (veblen_fixpoints _ powOmega_normal 0); auto.
           rewrite veblen_zero.
           apply expOrd_increasing; auto.

        ** destruct (VF_isZero y); subst; simpl.
           *** rewrite veblen_onePlus; auto.
               rewrite addOrd_zero_r.
               rewrite <- IHb.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
               rewrite veblen_zero.
               reflexivity.
           *** rewrite veblen_onePlus; auto.
               rewrite <- IHb.
               simpl.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
               rewrite veblen_zero.
               rewrite <- addOrd_zero_r.
               apply addOrd_increasing; auto.
        ** destruct (VF_compare (W a x) y).
           *** simpl.
               rewrite veblen_onePlus; auto.
               rewrite <- addOrd_le2.
               apply IHy.
           *** split.
               rewrite IHy.
               apply veblen_inflationary; auto.
               apply veblen_collapse; auto.
               apply IHy.
               simpl.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
               rewrite veblen_onePlus; auto.
               rewrite addOrd_zero_r.
               rewrite veblen_zero.
               reflexivity.
           *** simpl.
               apply veblen_collapse'; auto.
               rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
               rewrite veblen_zero.
               rewrite veblen_onePlus; auto.
               rewrite addOrd_zero_r.
               reflexivity.

    (* y => W b y case *)
    + apply (veblen_compare_correct); auto.
      apply (IHa b). apply (IHx y). apply IHx.
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
  | Z => True
  | V a b => VF_isNormal a /\
             VF_isNormal b /\
             match b with
             | Z => match a with | W _ _ => False | _ => True end
             | V x _ => VF_denote a >= VF_denote x
             | W _ _ => VF_denote a >= VF_denote b
             end
  | W a b => a <> Z /\
             VF_isNormal a /\
             VF_isNormal b /\
             match b with
             | W x _ => VF_denote a >= VF_denote x
             | _ => True
             end
  end.

Definition VF_subterm_shrink x :=
  match x with
  | Z => True
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
    destruct x1; simpl; intuition.
    + apply veblen_nonzero; auto.
    + apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + apply veblen_subterm1_nonzero; auto.
      apply veblen_nonzero; auto.
    + apply veblen_subterm1_nonzero; auto.
      apply veblen_nonzero; auto.
  - destruct x2; simpl; intuition.
    + apply veblen_nonzero; auto.
    + apply veblen_increasing'; simpl in *; intuition.
    + simpl in H2. rewrite H2 at 1.
      apply veblen_subterm1_nonzero; auto.
      apply veblen_nonzero; auto.
  - destruct x2; simpl; intuition.
    + destruct x1; simpl; intuition.
      * apply ord_le_lt_trans with (veblen (expOrd ω) (VF_denote x1_1) (VF_denote x1_2)).
        apply veblen_monotone_func; auto.
        intros; apply onePlus_least_normal; auto.
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
      * apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + apply veblen_subterm1_nonzero; auto.
      apply veblen_nonzero; auto.
    + apply veblen_subterm1_nonzero; auto.
      apply veblen_nonzero; auto.
  - destruct x2; simpl; intuition.
    + apply veblen_nonzero; auto.
    + simpl in *. intuition.
      apply veblen_collapse'; auto.
      eapply ord_lt_le_trans; [ apply H1 |].
      apply veblen_inflationary; auto.
      eapply ord_lt_le_trans; [ apply H7 |].
      apply veblen_inflationary; auto.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 2; auto.
      rewrite veblen_zero.
      reflexivity.
      destruct x1; simpl; intuition.
      apply veblen_nonzero; auto.
      apply veblen_nonzero; auto.
    + apply veblen_increasing'; simpl in *; intuition.
Qed.

Theorem VF_normal_forms_unique :
  forall x y,
    VF_isNormal x ->
    VF_isNormal y ->
    VF_denote x ≈ VF_denote y ->
    x = y.
Proof.
  induction x as [|a Ha x Hx|a Ha x Hx].
  - destruct y as [|b y|b y]; simpl; intuition.
    + elim (ord_lt_irreflexive 0).
      rewrite H1 at 2.
      apply veblen_nonzero; auto.
    + elim (ord_lt_irreflexive 0).
      rewrite H1 at 2.
      apply veblen_nonzero; auto.
  - destruct y as [|b y|b y]; simpl; intuition.
    + elim (ord_lt_irreflexive 0).
      rewrite <- H1 at 2.
      apply veblen_nonzero; auto.
    + assert (VF_denote a ≈ VF_denote b).
      { generalize (VF_compare_correct a b).
        destruct (VF_compare a b); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ onePlus_normal (VF_denote a) (VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (VF_normal_subterm_shrink (V a x)); simpl; intuition.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (veblen_fixpoints _ onePlus_normal (VF_denote b) (VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply (VF_normal_subterm_shrink (V b y)); simpl; intuition. }
      assert (VF_denote x ≈ VF_denote y).
      { generalize (VF_compare_correct x y).
        destruct (VF_compare x y); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          apply veblen_increasing'; auto.
          apply H4.
        - elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          apply veblen_increasing'; auto.
          apply H4. }
      f_equal; auto.
    + elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
      apply ord_lt_le_trans with (VF_denote (V (V a x) Z)).
      apply (VF_normal_subterm_shrink (V (V a x) Z)).
      simpl; intuition.
      rewrite H1.
      transitivity (veblen (expOrd ω) 0 (veblen (expOrd ω) (VF_denote b) (VF_denote y))).
      rewrite veblen_zero.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      apply expOrd_monotone; apply H1.
      apply (veblen_fixpoints _ powOmega_normal 0 (VF_denote b)); auto.
      destruct b; simpl; intuition.
      apply veblen_nonzero; auto.
      apply veblen_nonzero; auto.

  - destruct y as [|b y|b y]; simpl; intuition.
    + elim (ord_lt_irreflexive 0).
      rewrite <- H1 at 2.
      apply veblen_nonzero; auto.
    + elim (ord_lt_irreflexive (veblen (expOrd ω) (VF_denote a) (VF_denote x))).
      rewrite H1 at 1.
      apply ord_lt_le_trans with (VF_denote (V (V b y) Z)).
      apply (VF_normal_subterm_shrink (V (V b y) Z)).
      simpl; intuition.
      transitivity (veblen (expOrd ω) 0 (veblen (expOrd ω) (VF_denote a) (VF_denote x))).
      simpl.
      rewrite veblen_zero.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      apply expOrd_monotone; apply H1.
      apply (veblen_fixpoints _ powOmega_normal 0 (VF_denote a)); auto.
      destruct a; simpl; intuition.
      apply veblen_nonzero; auto.
      apply veblen_nonzero; auto.

    + assert (VF_denote a ≈ VF_denote b).
      { generalize (VF_compare_correct a b).
        destruct (VF_compare a b); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ powOmega_normal (VF_denote a) (VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (VF_normal_subterm_shrink (W a x)); simpl; intuition.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (veblen_fixpoints _ powOmega_normal (VF_denote b) (VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply (VF_normal_subterm_shrink (W b y)); simpl; intuition. }
      assert (VF_denote x ≈ VF_denote y).
      { generalize (VF_compare_correct x y).
        destruct (VF_compare x y); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          apply veblen_increasing'; auto.
          apply H6.
        - elim (ord_lt_irreflexive (veblen (expOrd ω) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          apply veblen_increasing'; auto.
          apply H6. }
      f_equal; auto.
Qed.

Definition Vnorm (a:VForm) (b:VForm) : VForm :=
  match b with
  | Z     => match a with
             | W _ _ => a
             | _ => V a Z
             end
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
  if VF_isZero a then Vnorm b Z else
  match b with
  | Z     => W a b
  | V _ _ => W a b
  | W x y => match VF_compare a x with
             | LT => b
             | _  => W a b
             end

  end.

Fixpoint VF_normalize (x:VForm) : VForm :=
  match x with
  | Z => Z
  | V a b => Vnorm (VF_normalize a) (VF_normalize b)
  | W a b => Wnorm (VF_normalize a) (VF_normalize b)
  end.

Lemma Vnorm_isNormal : forall a b, VF_isNormal a -> VF_isNormal b -> VF_isNormal (Vnorm a b).
Proof.
  unfold Vnorm; simpl; intros.
  destruct b; simpl in *.
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
  destruct (VF_isZero a).
  { destruct b; simpl in *; intuition. }
  destruct b; simpl in *; intuition.
  - subst a. apply (ord_lt_irreflexive 0); auto.
  - subst a. apply (ord_lt_irreflexive 0); auto.
  - generalize (VF_compare_correct a b1).
    destruct (VF_compare a b1); simpl; intuition.
    + subst a. apply (ord_lt_irreflexive 0); auto.
    + apply H3.
    + subst a. apply (ord_lt_irreflexive 0); auto.
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
  - destruct a; simpl; auto with ord.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    reflexivity.
    simpl in H. destruct a1; intuition; simpl.
    apply veblen_nonzero; auto.
    apply veblen_nonzero; auto.
  - generalize (VF_compare_correct a b1).
    destruct (VF_compare a b1); simpl; intuition.
    symmetry.
    apply veblen_fixpoints; auto.
  - generalize (VF_compare_correct a (W b1 b2)).
    destruct (VF_compare a (W b1 b2)); simpl; intuition.
    symmetry. apply VW_collapse; auto.
    simpl in *; intuition.
    destruct b1; intuition.
    apply veblen_nonzero; auto.
    apply veblen_nonzero; auto.
Qed.

Lemma Wnorm_equal : forall a b,
    VF_isNormal a -> VF_isNormal b ->
    VF_denote (Wnorm a b) ≈ (VF_denote (W a b)).
Proof.
  intros; unfold Wnorm; simpl.
  destruct (VF_isZero a).
  subst a. simpl.
  destruct b; simpl in *; intuition.
  + rewrite veblen_zero.
    rewrite veblen_zero.
    rewrite addOrd_zero_r.
    rewrite expOrd_zero.
    reflexivity.
  + rewrite veblen_zero.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    reflexivity.
  + rewrite veblen_zero.
    rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
    rewrite veblen_zero.
    reflexivity.
    destruct b1; simpl; intuition.
    apply veblen_nonzero; auto.
    apply veblen_nonzero; auto.
  + destruct b; simpl; auto with ord.
    generalize (VF_compare_correct a b1).
    destruct (VF_compare a b1); simpl; auto with ord.
    intros. symmetry; apply veblen_fixpoints; auto.
Qed.

Theorem VF_normalize_equal : forall x, VF_denote (VF_normalize x) ≈ VF_denote x.
Proof.
  induction x; simpl; auto with ord.
  - rewrite Vnorm_equal; auto.
    simpl.
    transitivity (veblen (addOrd 1) (VF_denote x1) (VF_denote (VF_normalize x2))).
    split; apply veblen_monotone_first; auto; apply IHx1.
    split; apply veblen_monotone; auto; apply IHx2.
    apply VF_normalize_isNormal.
    apply VF_normalize_isNormal.
  - rewrite Wnorm_equal; auto.
    transitivity (veblen (expOrd ω) (VF_denote x1) (VF_denote (VF_normalize x2))).
    split; apply veblen_monotone_first; auto; apply IHx1.
    split; apply veblen_monotone; auto; apply IHx2.
    apply VF_normalize_isNormal.
    apply VF_normalize_isNormal.
Qed.

Lemma VF_isNormal_dominates : forall (b a:VF),
    match b with
    | V b1 _ => VF_denote a >= VF_denote b1
    | W _ _  => VF_denote a >= VF_denote b
    | Z => True
    end ->
    VF_isNormal b ->
    exists n:ω, expOrd ω a * n ≥ b.
Proof.
  induction b; simpl; intuition.
  - exists 0%nat. auto with ord.
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
    apply normal_inflationary; auto.
Qed.

Fixpoint VF_add (x y:VForm) : VForm :=
  match x with
  | Z     => y
  | V a b => V a (VF_add b y)
  | W a b => if VF_isZero a then V b y else V x y
  end.

Lemma VF_add_correct x y : VF_denote (VF_add x y) ≈ VF_denote x + VF_denote y.
Proof.
  induction x; simpl.
  - rewrite addOrd_zero_l. reflexivity.
  - rewrite veblen_onePlus; auto.
    rewrite veblen_onePlus; auto.
    rewrite <- addOrd_assoc.
    rewrite IHx2; auto with ord.
  - destruct (VF_isZero x1).
    + subst x1. simpl.
      rewrite veblen_zero.
      rewrite veblen_onePlus; auto.
      reflexivity.
    + simpl.
      rewrite veblen_onePlus; auto.
      apply addOrd_eq_mor; auto with ord.
      symmetry.
      rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
      rewrite veblen_zero.
      reflexivity.
Qed.

Definition VF_one := V Z Z.
Definition VF_succ x := VF_add x VF_one.
Definition VF_expOmega x := V x Z.
Definition VF_epsilon x  := W VF_one x.

Lemma VF_one_correct : VF_denote VF_one ≈ 1.
Proof.
  simpl. rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite expOrd_zero.
  reflexivity.
Qed.

Lemma VF_succ_correct x : VF_denote (VF_succ x) ≈ succOrd (VF_denote x).
Proof.
  unfold VF_succ.
  rewrite VF_add_correct.
  rewrite VF_one_correct.
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

(* x * ωᵉ *)
Definition VF_mul_single (x:VForm) (e:VForm) : VForm :=
  if VF_isZero e then x else
    match x with
    (* x * ω⁰ = x *)
    | Z => Z
    (* (ωᵃ + q) * ωᵉ = ω^(a + e) otherwise *)
    | V a _ => V (VF_add a e) Z
    (* (W a b) * ωᵉ  = ω^(W a b) * ωᵉ = ω^(W a b + e) for a > 0 *)
    | W _ _ => V (VF_add x e) Z
    end.

Lemma VF_mul_single_correct : forall x e,
    VF_isNormal x ->
    VF_denote (VF_mul_single x e) ≈ VF_denote x * expOrd ω (VF_denote e).
Proof.
  unfold VF_mul_single. intros.
  destruct (VF_isZero e).
  - subst e. simpl.
    rewrite expOrd_zero.
    rewrite mulOrd_one_r.
    reflexivity.
  - destruct x; simpl.
    + symmetry. apply mulOrd_zero_l.
    + rewrite veblen_onePlus at 1; auto.
      rewrite addOrd_zero_r.
      rewrite VF_add_correct.
      rewrite expOrd_add.
      rewrite veblen_onePlus at 1; auto.
      destruct (VF_isNormal_dominates x2 x1) as [n Hn]; auto.
      simpl in H; intuition.
      destruct x2; intuition.
      simpl in H; intuition.
      split.
      apply mulOrd_monotone1.
      apply addOrd_le1.
      apply expOrd_omega_collapse with n; auto.
    + destruct (VF_isZero x1).
      { simpl in *; intuition. }
      simpl.
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
Qed.


Definition VF_mul x : VForm -> VForm :=
  let x' := VF_normalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | Z => Z
  | V b y' => VF_add (VF_mul_single x' b) (loop y')
  | W b y' => if VF_isZero b then VF_mul_single x' y' else VF_mul_single x' y
  end.

Lemma VF_mul_correct x y : VF_denote (VF_mul x y) ≈ VF_denote x * VF_denote y.
Proof.
  induction y; simpl.
  - rewrite mulOrd_zero_r; auto with ord.
  - rewrite VF_add_correct.
    rewrite VF_mul_single_correct.
    rewrite veblen_onePlus; auto.
    rewrite ordDistrib_left.
    apply addOrd_eq_mor; auto.
    apply mulOrd_eq_mor; auto with ord.
    apply VF_normalize_equal.
    apply VF_normalize_isNormal.
  - destruct (VF_isZero y1).
    + subst y1.
      simpl. rewrite veblen_zero.
      rewrite VF_mul_single_correct.
      apply mulOrd_eq_mor; auto with ord.
      apply VF_normalize_equal.
      apply VF_normalize_isNormal.
    + rewrite VF_mul_single_correct.
      apply mulOrd_eq_mor; auto with ord.
      apply VF_normalize_equal.
      simpl.
      symmetry.
      rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
      rewrite veblen_zero.
      reflexivity.
      apply VF_normalize_isNormal.
Qed.

Definition VF_isFinite x : { n:nat | VF_denote x ≈ sz n } + { 1 + VF_denote x ≈ VF_denote x }.
Proof.
  induction x; simpl.
  - left. exists 0%nat. simpl; reflexivity.
  - destruct (VF_isZero x1).
    + subst x1. simpl.
      destruct IHx2 as [ [n Hn] | Hinf ].
      * left. exists (n+1)%nat.
        rewrite veblen_onePlus; auto.
        rewrite expOrd_zero.
        rewrite natOrdSize_add.
        apply addOrd_eq_mor; simpl; auto with ord.
      * right.
        rewrite veblen_onePlus; auto.
        rewrite expOrd_zero.
        apply addOrd_eq_mor; auto with ord.
    + right.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_assoc.
      apply addOrd_eq_mor; auto with ord.
      split.
      apply additively_closed_collapse.
      apply expOmega_additively_closed; auto.
      apply ord_lt_le_trans with (expOrd ω 1).
      rewrite expOrd_one'; auto.
      apply expOrd_monotone.
      apply succ_least; auto.
      apply addOrd_le2.
  - destruct (VF_isZero x1).
    + subst x1.
      destruct (VF_isZero x2).
      * subst x2. simpl.
        left. exists 1%nat.
        rewrite veblen_zero.
        rewrite expOrd_zero.
        auto with ord.
      * right.
        split.
        apply additively_closed_collapse.
        apply veblen_additively_closed; auto.
        simpl. rewrite veblen_zero.
        apply ord_lt_le_trans with (expOrd ω 1).
        rewrite expOrd_one'; auto.
        apply expOrd_monotone.
        apply succ_least; auto.
        apply addOrd_le2.
    + right.
      split.
      apply additively_closed_collapse.
      apply veblen_additively_closed; auto.
      apply ord_lt_le_trans with (expOrd ω 1).
      rewrite expOrd_one'; auto.
      rewrite <- (veblen_fixpoints _ powOmega_normal 0); auto.
      rewrite veblen_zero.
      apply expOrd_monotone.
      apply succ_least; auto.
      apply veblen_nonzero; auto.
      apply addOrd_le2.
Qed.

Fixpoint VF_nat (n:nat) :=
  match n with
  | O => Z
  | S n' => V Z (VF_nat n')
  end.

Lemma VF_nat_correct : forall n,
    VF_denote (VF_nat n) ≈ sz n.
Proof.
  induction n; simpl; auto with ord.
  rewrite veblen_zero.
  transitivity (sz (n+1)%nat).
  rewrite natOrdSize_add.
  apply addOrd_eq_mor; auto with ord.
  replace (n+1)%nat with (1+n)%nat by lia.
  simpl. auto with ord.
Qed.

Lemma VF_expOmega_correct x : VF_denote (VF_expOmega x) ≈ expOrd ω (VF_denote x).
Proof.
  simpl.
  rewrite veblen_onePlus; auto.
  apply addOrd_zero_r.
Qed.

Definition VF_exp_single (x:VForm) (e:VForm) :=
  match VF_isFinite x with
  | inleft (exist _ n _ ) =>
    match n with
    | 0 => VF_one
    | 1 => VF_one
    | _ => match VF_isFinite e with
           | inleft (exist _ en _) =>
             match en with
             | 0 => x
             | S m => V (V (VF_nat m) Z) Z
             end
           | inright He => V (V e Z) Z
           end
    end

  | inright Hx =>
    if VF_isZero e then x else
      match x with
      | Z => VF_one
      | V a _ => V (VF_mul a (V e Z)) Z
      | W _ _ => V (VF_mul x (V e Z)) Z
      end
  end.

Local Opaque VF_mul.

Lemma VF_exp_single_correct x e :
  VF_isNormal x ->
  VF_denote (VF_exp_single x e) ≈ expOrd (VF_denote x) (expOrd ω (VF_denote e)).
Proof.
  unfold VF_exp_single. intros.
  destruct (VF_isFinite x) as [[n Hn]|Hinf]; simpl.
  - destruct n.
    { simpl. rewrite veblen_zero. rewrite addOrd_zero_r.
      rewrite Hn.
      simpl.
      split.
      apply succ_least. apply expOrd_nonzero.
      rewrite expOrd_unfold.
      apply lub_least; auto with ord.
      apply sup_least; intro.
      rewrite mulOrd_zero_r. auto with ord. }
    destruct n.
    { simpl. rewrite veblen_zero.
      rewrite addOrd_zero_r.
      rewrite Hn.
      symmetry. apply expOrd_one_base. }
    destruct (VF_isFinite e) as [[m Hm]|Hinfe].
    + destruct m.
      { simpl.
        rewrite Hm.
        simpl.
        rewrite expOrd_zero.
        rewrite expOrd_one'; auto with ord.
        rewrite Hn.
        simpl.
        apply succ_trans; auto with ord. }
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite Hm.
      symmetry.
      rewrite Hn.
      transitivity (expOrd (sz (S (S n))) (expOrd ω (1+sz m))).
      apply expOrd_eq_mor; auto with ord.
      apply expOrd_eq_mor; auto with ord.
      transitivity (sz (m+1)%nat).
      replace (m+1)%nat with (1+m)%nat by lia.
      simpl. auto with ord.
      rewrite natOrdSize_add; auto with ord.
      rewrite expNatToOmegaPow.
      rewrite VF_nat_correct. reflexivity.
      simpl.
      apply succ_trans.
      apply succ_least.
      apply succ_trans.
      auto with ord.
    + rewrite <- Hinfe.
      rewrite Hn.
      rewrite expNatToOmegaPow.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      reflexivity.
      simpl.
      apply succ_trans.
      apply succ_least.
      apply succ_trans.
      auto with ord.
  - destruct (VF_isZero e).
    + subst e. simpl.
      rewrite expOrd_zero.
      rewrite expOrd_one'; auto with ord.
      rewrite <- Hinf.
      rewrite <- addOrd_le1.
      apply succ_lt.
    + destruct x; simpl.
      * rewrite veblen_zero.
        rewrite addOrd_zero_r.
        rewrite expOrd_unfold.
        split.
        apply lub_le1.
        apply lub_least; auto with ord.
        apply sup_least; intro.
        rewrite mulOrd_zero_r. auto with ord.
      * rewrite veblen_onePlus; auto.
        rewrite addOrd_zero_r.
        rewrite VF_mul_correct.
        rewrite expOrd_mul.
        simpl.
        rewrite veblen_onePlus; auto.
        rewrite addOrd_zero_r.
        split.
        apply expOrd_monotone_base.
        rewrite veblen_onePlus; auto.
        apply addOrd_le1.
        rewrite veblen_onePlus; auto.
        destruct (VF_isNormal_dominates x2 x1) as [n Hn]; auto.
        simpl in H; intuition.
        destruct x2; auto.
        simpl in H; intuition.
        rewrite expToOmega_collapse_tower with n; auto with ord.
        transitivity (expOrd ω 1).
        { rewrite expOrd_one'.
          transitivity (natOrdSize (1+n)).
          rewrite natOrdSize_add. reflexivity.
          apply index_le.
          auto. }
        apply expOrd_monotone.
        apply succ_least.
        destruct (VF_isZero x1); auto.
        subst x1.
        simpl in Hinf.
        rewrite veblen_zero in Hinf.
        assert (forall n:ω, sz n + (1 + VF_denote x2) ≈ sz n + VF_denote x2 -> VF_isNormal (V Z x2) -> False).
        { clear. induction x2; simpl; intros.
          - rewrite addOrd_zero_r in H.
            rewrite addOrd_zero_r in H.
            apply (ord_lt_irreflexive (natOrdSize n)).
            rewrite <- H at 2.
            rewrite addOrd_succ.
            rewrite addOrd_zero_r.
            apply succ_lt.
          - simpl in H.
            rewrite addOrd_assoc in H.
            intuition.
            apply (IHx2_2 (S n)); simpl; intuition.
            transitivity
              (natOrdSize n + 1 + veblen (addOrd 1) (VF_denote x2_1) (VF_denote x2_2)).
            apply addOrd_eq_mor.
            rewrite addOrd_succ.
            rewrite addOrd_zero_r.
            reflexivity.
            rewrite veblen_onePlus; auto.
            apply addOrd_eq_mor; auto with ord.
            split. apply succ_least. apply expOrd_nonzero.
            rewrite H3.
            rewrite expOrd_zero. auto with ord.
            rewrite H.
            rewrite veblen_onePlus; auto.
            rewrite addOrd_assoc.
            apply addOrd_eq_mor.
            transitivity (natOrdSize n + 1).
            apply addOrd_eq_mor; auto  with ord.
            split.
            rewrite H3.
            rewrite expOrd_zero; auto with ord.
            apply succ_least. apply expOrd_nonzero.
            rewrite addOrd_succ. rewrite addOrd_zero_r.
            reflexivity.
            reflexivity.
            destruct x2_2; auto.
            rewrite H5; auto.
            rewrite H5; auto.

          - intuition.
            elim (ord_lt_irreflexive 0).
            rewrite <- H3 at 2.
            apply veblen_nonzero; auto. }
        elim (H0 1%nat); auto.
      * rewrite veblen_onePlus; auto.
        rewrite addOrd_zero_r.
        rewrite VF_mul_correct.
        rewrite expOrd_mul.
        simpl.
        rewrite veblen_onePlus; auto.
        rewrite addOrd_zero_r.
        apply expOrd_eq_mor; auto with ord.
        symmetry.
        rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto with ord.
        rewrite veblen_zero.
        reflexivity.
        simpl in  H.
        destruct x1; intuition; simpl.
        apply veblen_nonzero; auto.
        apply veblen_nonzero; auto.
Qed.


Definition VF_exp (x:VForm) : VForm -> VForm :=
  let x' := VF_normalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | Z      => VF_one
  | V b y' => VF_mul (VF_exp_single x' b) (loop y')
  | W b y' => if VF_isZero b then VF_exp_single x' y' else VF_exp_single x' y
  end.

Lemma VF_exp_correct : forall x y,
  VF_denote (VF_exp x y) ≈ expOrd (VF_denote x) (VF_denote y).
Proof.
  intro x. induction y; simpl.
  - rewrite veblen_zero.
    rewrite expOrd_zero.
    rewrite addOrd_zero_r. reflexivity.
  - rewrite VF_mul_correct.
    rewrite VF_exp_single_correct; auto.
    rewrite veblen_onePlus; auto.
    rewrite expOrd_add.
    apply mulOrd_eq_mor; auto.
    apply expOrd_eq_mor; auto with ord.
    apply VF_normalize_equal.
    apply VF_normalize_isNormal.
  - destruct (VF_isZero y1).
    + subst y1. simpl.
      rewrite veblen_zero.
      rewrite VF_exp_single_correct.
      apply expOrd_eq_mor; auto with ord.
      apply VF_normalize_equal.
      apply VF_normalize_isNormal.
    + rewrite VF_exp_single_correct.
      apply expOrd_eq_mor; auto.
      apply VF_normalize_equal.
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
  transitivity (veblen (expOrd ω) 1 (VF_denote x)).
  split; apply veblen_monotone_first; auto.
  rewrite veblen_zero. rewrite addOrd_zero_r. reflexivity.
  apply succ_least. apply veblen_nonzero; auto.
  rewrite veblen_succ; auto.
  unfold ε.
  split; apply enum_fixpoints_func_mono; auto.
  apply veblen_normal; auto.
  intros. rewrite veblen_zero. reflexivity.
  apply veblen_normal; auto.
  intros. rewrite veblen_zero. reflexivity.
Qed.

Theorem VF_reflects_zero : reflects VForm VF_denote ORD 0 Z.
Proof.
  simpl; auto with ord.
Qed.

Theorem VF_reflects_one : reflects VForm VF_denote ORD 1 VF_one.
Proof.
  simpl.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite expOrd_zero.
  reflexivity.
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

Theorem VF_reflects_veblen : reflects VForm VF_denote (ORD ==> ORD ==> ORD) (veblen (expOrd ω)) W.
Proof.
  red; intros.
  simpl.
  transitivity (veblen (expOrd ω) x (VF_denote a0)).
  split; apply veblen_monotone; auto; apply H0.
  split; apply veblen_monotone_first; auto; apply H.
Qed.


Lemma VF_below_Γ₀ : forall x, VF_denote x < Γ 0.
Proof.
  induction x; simpl VF_denote.
  - apply normal_nonzero. apply Γ_normal.
  - rewrite Γ_fixpoints; auto.
    rewrite <- (veblen_fixpoints _ powOmega_normal (VF_denote x1) (Γ 0) 0); auto.
    apply ord_le_lt_trans with
        (veblen powOmega (VF_denote x1) (VF_denote x2)).
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
  - rewrite Γ_fixpoints; auto.
    rewrite <- (veblen_fixpoints _ powOmega_normal (VF_denote x1) (Γ 0) 0); auto.
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
Qed.

Lemma VF_limit : limitOrdinal VF.
Proof.
  hnf. split.
  exact (inhabits Z).
  red; simpl; intros.
  exists (V a (V Z Z)).
  simpl.
  rewrite veblen_onePlus; auto.
  apply ord_le_lt_trans with (expOrd ω (VF_denote a)).
  apply normal_inflationary; auto.
  rewrite <- addOrd_zero_r at 1.
  apply addOrd_increasing.
  apply veblen_nonzero; auto.
Qed.

Lemma VF_veblen_closed : veblen powOmega VF 0 ≤ VF.
Proof.
  transitivity (veblen powOmega (boundedSup VF (fun x => x)) 0).
  { apply veblen_monotone_first.
    intros; apply expOrd_monotone; auto.
    apply (limit_boundedSup VF). apply VF_limit. }
  unfold boundedSup. unfold VF at 1.
  transitivity (supOrd (fun x => veblen powOmega (VF_denote x) 0)).
  { apply veblen_continuous_first; auto. exact Z. }
  apply sup_least. intro x.
  transitivity (VF_denote (W x Z)).
  simpl; reflexivity.
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


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VW_has_enough_notations (EM:excluded_middle) :
  forall x, x < Γ 0 -> exists v:VF, v ≈ x.
Proof.
  induction x as [x Hx] using ordinal_induction. intro H.
  destruct (classical.ordinal_discriminate EM x) as [Hzero|[Hsucc|Hlimit]].
  - (* Zero ordinal, exhibit Z *)
    exists Z. simpl.
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
      destruct (veblen_decompose EM powOmega powOmega_normal x) as [a [b [Hab [_[Ha Hb]]]]]; auto.

      (* invoke the induction hypotheses *)
      destruct (Hx a) as [va Hva]; auto.
      transitivity x; auto.
      destruct (Hx b) as [vb Hvb]; auto.
      transitivity x; auto.

      (* exhibit the W form and wrap up *)
      exists (W va vb).
      simpl. rewrite Hab.
      transitivity (veblen (expOrd ω) a (VF_denote vb)).
      split; apply veblen_monotone_first; auto with ord; apply Hva.
      split; apply veblen_monotone; auto; apply Hvb.

    (* x is not a epsilon number, find its V form *)
    * (* decompose the ordinal *)
      destruct (veblen_decompose EM (addOrd 1) (onePlus_normal) x) as [a [b [Hab[_[Ha Hb]]]]]; auto.

      (* invoke the induction hypotheses *)
      destruct (Hx a) as [va Hva]; auto.
      transitivity x; auto.
      destruct (Hx b) as [vb Hvb]; auto.
      transitivity x; auto.

      (* exhibit the V form and wrap up *)
      exists (V va vb).
      rewrite Hab. simpl.
      transitivity (veblen (addOrd 1) a (VF_denote vb)).
      split; apply veblen_monotone_first; auto; apply Hva.
      split; apply veblen_monotone; auto; apply Hvb.
Qed.
