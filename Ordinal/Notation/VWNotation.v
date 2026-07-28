Require Import Relations.Relation_Operators.
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
From Ordinal Require Import NaturalArith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.

From Ordinal Require Import Notation.CantorDecomposition.


Open Scope ord_scope.

Inductive VForm : Set :=
| Z : VForm
| V : VForm -> VForm -> VForm
| W : VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | V a x => veblen (addOrd 1) (VF_denote a) (VF_denote x)
  | W a x => veblen ε (VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x; simpl VF_denote; auto with ord.
Qed.

Fixpoint VF_size (x:VForm) : nat :=
  match x with
  | Z => O
  | V x y => S (VF_size x + VF_size y)
  | W x y => S (VF_size x + VF_size y)
  end.

Local Hint Unfold powOmega : core.
Local Hint Resolve VF_complete veblen_complete
        onePlus_normal powOmega_normal expOrd_complete addOrd_complete
        omega_complete succ_complete zero_complete
        normal_monotone normal_complete omega_gt0 omega_gt1 : core.

Definition VF_isZero x : { x = Z } + { 0 < VF_denote x }.
Proof.
  destruct x.
  - left. apply eq_refl.
  - right. simpl. apply veblen_nonzero; auto.
  - right. simpl. apply veblen_nonzero; auto with ord.
Qed.

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
  apply veblen_fixpoints; auto with ord.
Qed.

Lemma VW_collapse : forall a b c,
  VF_denote a < VF_denote (W b c) ->
  VF_denote (V a (W b c)) ≈ VF_denote (W b c).
Proof.
  simpl VF_denote.
  intros.
  split.
  2: { apply veblen_inflationary; auto with ord. }

  apply veblen_collapse; auto with ord.
  rewrite veblen_onePlus; auto with ord.
  rewrite addOrd_zero_r.
  destruct (VF_isZero b); subst; simpl.
  - rewrite veblen_zero at 2.
    unfold ε.
    rewrite enum_are_fixpoints; auto with ord.
    apply normal_monotone; auto with ord.
    rewrite veblen_zero. auto with ord.
  - rewrite <- veblen_fixpoints with (α := 0) at 2; auto with ord.
    rewrite veblen_zero in *.
    unfold ε.
    rewrite enum_are_fixpoints; auto with ord; simpl.
    unfold powOmega.
    apply normal_monotone; auto with ord.
    apply normal_inflationary; auto with ord.
Qed.

Lemma VW_collapse2 : forall b c,
  VF_denote (V (W b c) Z) ≈ VF_denote (W b c).
Proof.
  intros. simpl. split.
  - rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r.
    destruct (VF_isZero b); subst; simpl.
    + rewrite veblen_zero at 2.
      unfold ε.
      rewrite enum_are_fixpoints; auto with ord.
      apply normal_monotone; auto with ord.
      rewrite veblen_zero; auto with ord.
    + rewrite <- (veblen_fixpoints _ ε_normal 0) at 2; auto.
      rewrite veblen_zero.
      unfold ε.
      rewrite enum_are_fixpoints; auto with ord.
      apply normal_monotone; auto with ord.
      apply normal_inflationary; auto with ord.
  - apply normal_inflationary with (f:=fun x => veblen _ x _); auto with ord.
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
  induction x as [|a IHa x IHx|a IHa x IHx].
  (* x => Z case *)
  - destruct y as [|b y|b y]; simpl; auto with ord.
  (* x => V a x case *)
  - induction y as [|b IHb y IHy|b IHb y IHy].
    (* y => Z case *)
    + simpl. apply veblen_nonzero; auto.
    (* y => V b y case *)
    + simpl. apply (veblen_compare_correct); auto.
      apply (IHa b). apply (IHx y). apply IHx.

    (* y => W b y case *)
    + rewrite VW_compare_eq.
      * generalize (IHa (W b y)); simpl.
        destruct (VF_compare a (W b y)); intros Hasub.
        ** generalize (IHx (W b y)).
           destruct (VF_compare x (W b y)); intros Hxsub.
           *** apply veblen_collapse'; auto with ord.
               apply VW_collapse2.
           *** split.
               apply veblen_collapse; auto with ord.
               apply Hxsub.
               apply VW_collapse2.
               rewrite <- Hxsub.
               apply veblen_inflationary; auto.
           *** rewrite veblen_onePlus; auto.
               rewrite <- addOrd_le2. apply Hxsub.
        ** destruct (VF_isZero x); subst; simpl; auto with ord.
           *** rewrite Hasub.
               apply VW_collapse2.
           *** rewrite Hasub.
               apply veblen_subterm1; auto with ord.
        ** apply ord_lt_le_trans with (VF_denote a); auto.
           transitivity (veblen (addOrd 1) (VF_denote a) 0); auto with ord.
           apply normal_inflationary with (f:=fun x => veblen _ x _); auto with ord.

  (* x => W a x case *)
  - induction y as [|b IHb y IHy|b IHb y IHy].
    (* y => Z case *)
    + simpl; apply veblen_nonzero; auto with ord.
    (* y => V b y case *)
    + rewrite WV_compare_eq.
      * destruct (VF_compare (W a x) b).
        ** simpl.
           apply ord_lt_le_trans with (VF_denote b); auto.
           transitivity (veblen (addOrd 1) (VF_denote b) 0); auto with ord.
           apply normal_inflationary with (f:=fun x => veblen _ x _); auto with ord.

        ** destruct (VF_isZero y); subst; simpl.
           *** rewrite <- IHb. simpl.
               symmetry. apply (VW_collapse2 a x).
           *** apply ord_le_lt_trans with (veblen (addOrd 1) (VF_denote b) 0).
               rewrite <- IHb.
               apply VW_collapse2.
               apply normal_increasing; auto with ord.
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
               apply (VW_collapse2 a x); auto with ord.
           *** simpl.
               apply veblen_collapse'; auto with ord.
               apply (VW_collapse2 a x); auto with ord.

    (* y => W b y case *)
    + apply (veblen_compare_correct); auto with ord.
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

Lemma VF_lt_correct x y:
  VF_compare x y = LT <-> VF_denote x < VF_denote y.
Proof.
  generalize (VF_compare_correct x y); intro Hxy; intuition.
  - rewrite H in Hxy; auto.
  - destruct (VF_compare x y); auto.
    + elim (ord_lt_irreflexive (VF_denote x)).
      rewrite Hxy at 2.
      auto.
    + elim (ord_lt_irreflexive (VF_denote x)); eauto with ord.
Qed.

Lemma VF_le_correct x y:
  VF_compare y x <> LT <-> VF_denote x ≤ VF_denote y.
Proof.
  generalize (VF_compare_correct y x); intro Hxy; intuition.
  - destruct (VF_compare y x); intuition auto with ord.
    apply Hxy.
  - rewrite H0 in Hxy.
    elim (ord_lt_irreflexive (VF_denote x)).
    rewrite H at 1; auto.
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
  | W a b => VF_isNormal a /\
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
    + apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + apply veblen_subterm1; auto with ord.
    + apply veblen_subterm1; auto with ord.
  - destruct x2; simpl; intuition.
    + apply veblen_increasing'; simpl in *; intuition.
    + simpl in H2. rewrite H2 at 1.
      apply veblen_subterm1; auto with ord.
  - destruct x2; simpl; intuition.
    + destruct x1; simpl; intuition.
      * apply ord_le_lt_trans with (veblen ε (VF_denote x1_1) (VF_denote x1_2)).
        apply veblen_monotone_func; auto with ord.
        intros; apply onePlus_least_normal; auto with ord.
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
      * apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + apply veblen_subterm1; auto with ord.
    + apply veblen_subterm1; auto with ord.
  - destruct x2; simpl; intuition.
    + simpl in *. intuition.
      apply veblen_collapse'; auto with ord.
      eapply ord_lt_le_trans; [ apply H |].
      apply veblen_inflationary; auto with ord.
      eapply ord_lt_le_trans; [ apply H6 |].
      apply veblen_inflationary; auto with ord.
      apply (VW_collapse2 x1 (V x2_1 x2_2)).
    + apply veblen_increasing'; simpl in *; intuition.
Qed.

Lemma VF_isNormal_dec: forall x, { VF_isNormal x } + { ~VF_isNormal x }.
Proof.
  induction x; simpl; intros; auto.
  intuition; auto.
  destruct x2.
  - destruct x1; intuition.
  - generalize (VF_compare_correct x2_1 x1).
    destruct (VF_compare x2_1 x1); intuition.
    left; intuition. apply H.
    right; intuition.
    elim (ord_lt_irreflexive (VF_denote x1)).
    eapply ord_lt_le_trans; eauto.
  - generalize (VF_compare_correct (W x2_1 x2_2) x1).
    destruct (VF_compare (W x2_1 x2_2) x1); intuition.
    + simpl in H.
      left; intuition.
      apply H.
    + right; intuition.
      simpl in H.
      elim (ord_lt_irreflexive (VF_denote x1)).
      eapply ord_lt_le_trans; eauto.
  - intuition.
    destruct x2; intuition.
    generalize (VF_compare_correct x2_1 x1).
    destruct (VF_compare x2_1 x1); intuition.
    left; intuition. apply H.
    right; intuition.
    elim (ord_lt_irreflexive (VF_denote x1)).
    eapply ord_lt_le_trans; eauto.
Qed.    

Inductive redex : VForm -> VForm -> Prop:=
| redex_V : forall a b x,
    VF_compare a b = LT ->
    redex (V a (V b x)) (V b x)
| redex_W : forall a b x,
    VF_compare a b = LT ->
    redex (W a (W b x)) (W b x)
| redex_VW : forall a b c,
    VF_compare a (W b c) = LT ->
    redex (V a (W b c)) (W b c)
| redex_VW2 : forall b c,
    redex (V (W b c) Z) (W b c).

Lemma redex_sound: forall x y,
    redex x y ->
    VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. inversion H; subst.
  - apply V_collapse; auto.
    apply VF_lt_correct; auto.
  - apply W_collapse; auto.
    apply VF_lt_correct; auto.
  - apply VW_collapse; auto.
    apply VF_lt_correct; auto.
  - apply VW_collapse2; auto.
Qed.

Inductive one_step_reduce: VForm -> VForm -> Prop :=
| reduce_redex: forall x y, redex x y -> one_step_reduce x y
| reduce_Vcong1: forall x x' y, one_step_reduce x x' -> one_step_reduce (V x y) (V x' y)
| reduce_Vcong2: forall x y y', one_step_reduce y y' -> one_step_reduce (V x y) (V x y')
| reduce_Wcong1: forall x x' y, one_step_reduce x x' -> one_step_reduce (W x y) (W x' y)
| reduce_Wcong2: forall x y y', one_step_reduce y y' -> one_step_reduce (W x y) (W x y').

Lemma one_step_reduce_sound: forall x y, one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H.
  - apply redex_sound; auto.
  - simpl. apply veblen_eq_mor; auto with ord.
  - simpl. apply veblen_eq_mor; auto with ord.
  - simpl. apply veblen_eq_mor; auto with ord.
  - simpl. apply veblen_eq_mor; auto with ord.
Qed.

Lemma step_reduce_sound: forall x y,
    clos_refl_trans _ one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H; auto with ord.
  - apply one_step_reduce_sound; auto.
  - transitivity (VF_denote y); auto.
Qed.

Lemma VF_notIsNormal_reduce: forall x,
  ~VF_isNormal x <-> exists z, one_step_reduce x z.
Proof.
  induction x; simpl.
  - intuition.
    destruct H as [z H].
    inversion H; subst.
    inversion H1.
  - destruct (VF_isNormal_dec x1).
    2: { intuition.
         destruct H3 as [z Hz].
         econstructor.
         apply reduce_Vcong1; eauto. }
    destruct (VF_isNormal_dec x2).
    2:{ intuition.
        destruct H3 as [z Hz].
         econstructor.
         apply reduce_Vcong2; eauto. }
    intuition.
    + destruct x2.
      * destruct x1; intuition.
        eexists.
        apply reduce_redex.
        apply redex_VW2.
      * eexists.
        apply reduce_redex.
        apply redex_V.
        destruct (VF_decide_order x1 x2_1); intuition.
        apply VF_lt_correct; auto.
      * eexists.
        apply reduce_redex.
        apply redex_VW.
        destruct (VF_decide_order x1 (W x2_1 x2_2)); intuition.
        apply VF_lt_correct; auto.
    + destruct H3 as [z Hz].
      inversion Hz; subst.
      * inversion H3; subst; auto.
        ** elim (ord_lt_irreflexive (VF_denote x1)).
           eapply ord_lt_le_trans; eauto.
           apply VF_lt_correct; auto.
        ** elim (ord_lt_irreflexive (VF_denote x1)).
           eapply ord_lt_le_trans; eauto.
           apply VF_lt_correct; auto.   
      * apply H0; eauto.
      * apply H2; eauto.
  - intuition.
    + destruct (VF_isNormal_dec x1).
      2: { intuition.
           destruct H3 as [z Hz].
           econstructor.
           apply reduce_Wcong1; eauto. }
      destruct (VF_isNormal_dec x2).
      2:{ intuition.
          destruct H4 as [z Hz].
          econstructor.
          apply reduce_Wcong2; eauto. }
      intuition.
      destruct x2; intuition.
      eexists.
      apply reduce_redex.
      apply redex_W.
      destruct (VF_decide_order x1 x2_1); intuition.
      apply VF_lt_correct; auto.
    + destruct H3 as [z Hz].
      inversion Hz; subst.
      * inversion H3; subst.
        elim (ord_lt_irreflexive (VF_denote x1)).
        eapply ord_lt_le_trans; eauto.
        apply VF_lt_correct; auto.
      * apply H0; eauto.
      * apply H2; eauto.
Qed.   

Lemma VF_isNormal_no_reduce: forall x,
  VF_isNormal x <-> ~exists z, one_step_reduce x z.
Proof.
  intro x.
  generalize (VF_notIsNormal_reduce x).
  destruct (VF_isNormal_dec x); intuition.
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
      apply veblen_nonzero; auto with ord.
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
      simpl.
      rewrite H1.
      apply VW_collapse2.

  - destruct y as [|b y|b y]; simpl; intuition.
    + elim (ord_lt_irreflexive 0).
      rewrite <- H1 at 2.
      apply veblen_nonzero; auto with ord.
    + elim (ord_lt_irreflexive (veblen ε (VF_denote a) (VF_denote x))).
      rewrite H1 at 1.
      apply ord_lt_le_trans with (VF_denote (V (V b y) Z)).
      apply (VF_normal_subterm_shrink (V (V b y) Z)).
      simpl; intuition.
      simpl.
      rewrite <- (VW_collapse2 a x). simpl.
      apply veblen_monotone_first; auto with ord.
      apply H1.
    + assert (VF_denote a ≈ VF_denote b).
      { generalize (VF_compare_correct a b).
        destruct (VF_compare a b); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen ε (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ ε_normal (VF_denote a) (VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto with ord.
          rewrite <- H1.
          apply (VF_normal_subterm_shrink (W a x)); simpl; intuition.
        - elim (ord_lt_irreflexive (veblen ε (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (veblen_fixpoints _ ε_normal (VF_denote b) (VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto with ord.
          rewrite H1.
          apply (VF_normal_subterm_shrink (W b y)); simpl; intuition. }
      assert (VF_denote x ≈ VF_denote y).
      { generalize (VF_compare_correct x y).
        destruct (VF_compare x y); simpl; intros; auto.
        - elim (ord_lt_irreflexive (veblen ε (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          apply veblen_increasing'; auto with ord.
          apply H4.
        - elim (ord_lt_irreflexive (veblen ε (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          apply veblen_increasing'; auto with ord.
          apply H4. }
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
  destruct b; simpl in *; intuition.
  generalize (VF_compare_correct a b1).
  destruct (VF_compare a b1); simpl; intuition.
  apply H2.
Qed.

Lemma Vnorm_reduce : forall a b,
  clos_refl_trans _ one_step_reduce (V a b) (Vnorm a b).
Proof.
  intros a b. unfold Vnorm.
  destruct b; simpl.
  - destruct a; simpl; try apply rt_refl.
    apply rt_step. apply reduce_redex.
    apply redex_VW2.
  - generalize (VF_compare_correct a b1).
    destruct (VF_compare a b1); simpl; intros; try apply rt_refl.
    apply rt_step. apply reduce_redex.
    apply redex_V; auto.
    apply VF_lt_correct; auto.
  - generalize (VF_compare_correct a (W b1 b2)).
    destruct (VF_compare a (W b1 b2)); simpl; intros; try apply rt_refl.
    apply rt_step. apply reduce_redex.
    apply redex_VW; auto.
    apply VF_lt_correct; auto.
Qed.

Lemma Wnorm_reduce : forall a b,
  clos_refl_trans _ one_step_reduce (W a b) (Wnorm a b).
Proof.
  intros a b. unfold Wnorm.
  destruct b; simpl; try apply rt_refl.
  generalize (VF_compare_correct a b1).
  destruct (VF_compare a b1); simpl; intros; try apply rt_refl.
  apply rt_step. apply reduce_redex.
  apply redex_W; auto.
  apply VF_lt_correct; auto.
Qed.

Theorem VF_normalize_isNormal : forall x, VF_isNormal (VF_normalize x).
Proof.
  induction x; simpl; intuition.
  apply Vnorm_isNormal; auto.
  apply Wnorm_isNormal; auto.
Qed.

Lemma reduce_many_Vcong1 :
  forall x x' y,
    clos_refl_trans _ one_step_reduce x x' ->
    clos_refl_trans _ one_step_reduce (V x y) (V x' y).
Proof.
  intros x x' y H. induction H.
  - apply rt_step. apply reduce_Vcong1; auto.
  - apply rt_refl.
  - apply rt_trans with (V y0 y); auto.
Qed.

Lemma reduce_many_Vcong2 :
  forall x y y',
    clos_refl_trans _ one_step_reduce y y' ->
    clos_refl_trans _ one_step_reduce (V x y) (V x y').
Proof.
  intros x y y' H. induction H.
  - apply rt_step. apply reduce_Vcong2; auto.
  - apply rt_refl.
  - apply rt_trans with (V x y); auto.
Qed.

Lemma reduce_many_Wcong1 :
  forall x x' y,
    clos_refl_trans _ one_step_reduce x x' ->
    clos_refl_trans _ one_step_reduce (W x y) (W x' y).
Proof.
  intros x x' y H. induction H.
  - apply rt_step. apply reduce_Wcong1; auto.
  - apply rt_refl.
  - apply rt_trans with (W y0 y); auto.
Qed.

Lemma reduce_many_Wcong2 :
  forall x y y',
    clos_refl_trans _ one_step_reduce y y' ->
    clos_refl_trans _ one_step_reduce (W x y) (W x y').
Proof.
  intros x y y' H. induction H.
  - apply rt_step. apply reduce_Wcong2; auto.
  - apply rt_refl.
  - apply rt_trans with (W x y); auto.
Qed.

Lemma VF_normalize_reduce: forall x,
  clos_refl_trans _ one_step_reduce x (VF_normalize x).
Proof.
  induction x; simpl.
  - apply rt_refl.
  - apply rt_trans with (V (VF_normalize x1) x2).
    { apply reduce_many_Vcong1; auto. }
    apply rt_trans with (V (VF_normalize x1) (VF_normalize x2)).
    { apply reduce_many_Vcong2; auto. }
    apply Vnorm_reduce.
  - apply rt_trans with (W (VF_normalize x1) x2).
    { apply reduce_many_Wcong1; auto. }
    apply rt_trans with (W (VF_normalize x1) (VF_normalize x2)).
    { apply reduce_many_Wcong2; auto. }
    apply Wnorm_reduce.
Qed.

Lemma Vnorm_equal : forall a b ,
  VF_isNormal a -> VF_isNormal b ->
  VF_denote (Vnorm a b) ≈ (VF_denote (V a b)).
Proof.
  intros; unfold Vnorm; simpl.
  destruct b; simpl; auto with ord.
  - destruct a; simpl; auto with ord.
    rewrite (VW_collapse2 a1 a2); auto with ord.
  - generalize (VF_compare_correct a b1).
    destruct (VF_compare a b1); simpl; intuition.
    symmetry.
    apply veblen_fixpoints; auto.
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
  destruct (VF_compare a b1); simpl; auto with ord. intros.
  intros. symmetry; apply veblen_fixpoints; auto with ord.
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
  - rewrite Wnorm_equal; auto with ord.
    transitivity (veblen ε (VF_denote x1) (VF_denote (VF_normalize x2))).
    split; apply veblen_monotone_first; auto with ord; apply IHx1.
    split; apply veblen_monotone; auto with ord; apply IHx2.
    apply VF_normalize_isNormal.
    apply VF_normalize_isNormal.
Qed.

Theorem reduce_confluent: forall a b c,
    clos_refl_trans _ one_step_reduce a b ->
    clos_refl_trans _ one_step_reduce a c ->
    exists d,
      clos_refl_trans _ one_step_reduce b d /\
      clos_refl_trans _ one_step_reduce c d /\
      ~exists z, one_step_reduce d z.
Proof.
  intros a b c Hb Hc.
  assert (Hbc: VF_normalize b = VF_normalize c).
  { apply VF_normal_forms_unique; auto.
    - apply VF_normalize_isNormal.
    - apply VF_normalize_isNormal.
    - apply step_reduce_sound in Hb.
      apply step_reduce_sound in Hc.
      rewrite VF_normalize_equal.
      rewrite VF_normalize_equal.
      rewrite <- Hb. auto. }
  exists (VF_normalize b). repeat split.
  - apply VF_normalize_reduce.
  - rewrite Hbc. apply VF_normalize_reduce.
  - rewrite <- VF_isNormal_no_reduce.
    apply VF_normalize_isNormal.
Qed.

Inductive normalizes: VForm -> VForm -> Prop :=
| normal_normalizing:
  forall x,
    ~(exists y, one_step_reduce x y) ->
    normalizes x x
| step_normalizing:
  forall x y z,
    one_step_reduce x y ->
    normalizes y z ->
    normalizes x z.

Lemma redex_size: forall x y,
    redex x y ->
    (VF_size x > VF_size y)%nat.
Proof.
  intros x y H. inversion H; subst; simpl; lia.
Qed.

Lemma one_step_reduce_size: forall x y,
    one_step_reduce x y ->
    (VF_size x > VF_size y)%nat.
Proof.    
  intros x y H. induction H; simpl; intuition.
  apply redex_size; auto.
Qed.

Theorem strongly_normalizing: forall x, exists y, normalizes x y.
Proof.
  induction x as [x Hind] using (well_founded_induction (Wf_nat.well_founded_ltof _ VF_size)).
  destruct (VF_isNormal_dec x).
  - eexists.
    apply normal_normalizing.
    apply VF_isNormal_no_reduce; auto.
  - assert (exists y, one_step_reduce x y).
    { rewrite <- VF_notIsNormal_reduce. auto. }
    destruct H as [y Hy].
    destruct (Hind y) as [z Hz]; auto.
    { red. apply one_step_reduce_size; auto. }
    exists z.
    apply step_normalizing with y; auto.
Qed.

Lemma normalizes_correct: forall x y,
    normalizes x y ->
    VF_denote x ≈ VF_denote y /\ VF_isNormal y.
Proof.
  intros x y Hxy.
  induction Hxy.
  - split; auto with ord.
    rewrite VF_isNormal_no_reduce; auto.
  - intuition.
    transitivity (VF_denote y); auto.
    apply one_step_reduce_sound; auto.
Qed.    

Theorem normalizes_iff: forall x y,
    VF_denote x ≈ VF_denote y <-> exists z, normalizes x z /\ normalizes y z.
Proof.
  intuition.
  - destruct (strongly_normalizing x) as [z Hz].
    exists z; split; auto.
    destruct (strongly_normalizing y) as [z' Hz'].
    assert (z = z').
    { apply normalizes_correct in Hz.
      apply normalizes_correct in Hz'.
      apply VF_normal_forms_unique; intuition.
      rewrite <- H0.
      rewrite H. auto. }
    subst; auto.
  - destruct H as [z [Hz1 Hz2]].
    apply normalizes_correct in Hz1.
    apply normalizes_correct in Hz2.
    intuition.
    rewrite H. symmetry; auto.
Qed.

Lemma W_epsilon :
  forall x y,
    complete x ->
    complete y ->
    expOrd ω (veblen ε x y) ≈ veblen ε x y.
Proof.
  intros.
  destruct (complete_zeroDec x); auto.
  - split.
    rewrite veblen_unroll at 2.
    rewrite <- lub_le1.
    unfold ε.
    rewrite enum_are_fixpoints; auto with ord.
    apply normal_monotone; auto with ord.
    transitivity (veblen ε 0 y).
    apply veblen_monotone_first; auto with ord.
    rewrite veblen_zero.
    auto with ord.
    apply normal_inflationary; auto with ord.
  - split.
    rewrite <- veblen_fixpoints with (α:=0) at 2; auto with ord.
    rewrite veblen_zero.
    unfold ε.
    rewrite enum_are_fixpoints; auto with ord.
    apply normal_monotone; auto with ord.
    apply normal_inflationary; auto with ord.
    apply normal_inflationary; auto with ord.
Qed.

Fixpoint VF_decompose (x:VForm) : list VForm :=
  match x with
  | Z => []
  | V a b => a :: VF_decompose b
  | W _ _ => [x]
  end.

Fixpoint VF_recompose (xs:list VForm) : VForm :=
  match xs with
  | [] => Z
  | [x] =>
      match x with
      | Z     => V x Z
      | V _ _ => V x Z
      | W _ _ => x
      end
  | x::xs' => V x (VF_recompose xs')
  end.

Lemma VF_decompose_correct:
  forall x,
    VF_isNormal x ->
    each VF_isNormal (VF_decompose x) /\
    cantor_ordered VF_denote (VF_decompose x) /\
    VF_denote x ≈ cantor_denote VF_denote (VF_decompose x).
Proof.
  induction x; simpl; intuition.
  destruct x2; simpl; auto.
  rewrite veblen_onePlus; auto.
  rewrite H8. reflexivity.
  rewrite addOrd_zero_r.
  symmetry.
  apply W_epsilon; auto.
Qed.

Lemma VF_recompose_correct:
  forall xs,
    each VF_isNormal xs ->
    cantor_ordered VF_denote xs ->
    VF_isNormal (VF_recompose xs) /\ cantor_denote VF_denote xs ≈ VF_denote (VF_recompose xs).
Proof.
  induction xs; simpl in *; intuition.
  destruct xs; simpl; intuition.
  destruct a; simpl in *; intuition.

  simpl in *; intuition.
  destruct xs; simpl in *; intuition.
  destruct v; simpl in *; intuition.
  destruct xs; simpl in *; intuition.
  destruct a; simpl in *; intuition.
  rewrite veblen_onePlus; auto with ord.
  rewrite veblen_onePlus; auto with ord.
  rewrite veblen_onePlus; auto with ord.
  rewrite addOrd_zero_r.
  apply W_epsilon; auto.
  rewrite H5.
  rewrite veblen_onePlus; auto.
  reflexivity.
Qed.

Definition VF_has_cantor_decomposition : has_cantor_decomposition VF_denote VF_isNormal :=
  Build_has_cantor_decomposition
    VF_denote
    VF_isNormal
    VF_compare
    VF_decompose
    VF_recompose
    VF_complete
    (fun x y Hx Hy => VF_compare_correct x y)
    VF_decompose_correct
    VF_recompose_correct.

Definition VF_succ := cantor_succ VF_has_cantor_decomposition.
Definition VF_add := cantor_add VF_has_cantor_decomposition.
Definition VF_mul := cantor_mul VF_has_cantor_decomposition.
Definition VF_exp := cantor_exp VF_has_cantor_decomposition.

Definition VF_one := V Z Z.
Definition VF_expOmega x := Vnorm x Z.
Definition VF_epsilon x  := Wnorm Z x.

Theorem VF_reflects_zero : reflects VForm VF_denote VF_isNormal ORD 0 Z.
Proof.
  simpl; auto with ord.
Qed.

Theorem VF_reflects_one : reflects VForm VF_denote VF_isNormal ORD 1 VF_one.
Proof.
  simpl.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite expOrd_zero.
  intuition.
Qed.

Theorem VF_succ_reflects: reflects VForm VF_denote VF_isNormal (ORD ==> ORD) succOrd VF_succ.
Proof.
  apply cantor_succ_reflects.
Qed.

Theorem VF_add_reflects: reflects VForm VF_denote VF_isNormal (ORD ==> ORD ==> ORD) addOrd VF_add.
Proof.
  apply cantor_add_reflects.
Qed.

Theorem VF_mul_reflects: reflects VForm VF_denote VF_isNormal (ORD ==> ORD ==> ORD) mulOrd VF_mul.
Proof.
  apply cantor_mul_reflects.
Qed.

Theorem VF_exp_reflects: reflects VForm VF_denote VF_isNormal (ORD ==> ORD ==> ORD) expOrd VF_exp.
Proof.
  apply cantor_exp_reflects.
Qed.

Lemma VF_epsilon_correct : forall x,
    VF_isNormal x ->
    VF_denote (VF_epsilon x) ≈ ε (VF_denote x).
Proof.
  simpl; intros.
  unfold VF_epsilon.
  rewrite Wnorm_equal; simpl; auto.
  rewrite veblen_zero.
  auto with ord.
Qed.

Theorem VF_epsilon_reflects : reflects VForm VF_denote VF_isNormal (ORD ==> ORD) ε VF_epsilon.
Proof.
  red; intuition.
  rewrite VF_epsilon_correct; auto.
  unfold ε.
  split; apply enum_fixpoints_monotone; auto; apply H0.
  unfold VF_epsilon.
  apply Wnorm_isNormal; simpl; auto.
Qed.

Theorem VF_reflects_veblen : reflects VForm VF_denote VF_isNormal (ORD ==> ORD ==> ORD) (veblen ε) Wnorm.
Proof.
  red; simpl; intuition.
  rewrite Wnorm_equal; auto.
  simpl.
  transitivity (veblen ε x (VF_denote a0)).
  split; apply veblen_monotone; auto with ord; apply H2.
  split; apply veblen_monotone_first; auto with ord; apply H0.
  apply Wnorm_isNormal; auto.
Qed.

Lemma VF_below_Γ₀ : forall x, VF_denote x < Γ 0.
Proof.
  induction x; simpl VF_denote.
  - apply normal_nonzero. apply Γ_normal.
  - apply veblen_collapse'; auto with ord.
    apply normal_complete; auto with ord.
    apply Γ_normal.
    rewrite Γ_fixpoints at 2; auto.
    apply veblen_monotone_func; auto with ord.
    intros; apply onePlus_least_normal; auto with ord.
    apply normal_complete; auto with ord.
    apply Γ_normal.
  - apply veblen_collapse'; auto with ord.
    apply normal_complete; auto with ord.
    apply Γ_normal.
    rewrite Γalt at 2; auto with ord.
    rewrite enum_are_fixpoints; auto with ord.
    apply veblen_monotone_first; auto with ord.
    rewrite Γalt; auto with ord.
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

Lemma VF_veblen_closed : veblen ε VF 0 ≤ VF.
Proof.
  transitivity (veblen ε (boundedSup VF (fun x => x)) 0).
  { apply veblen_monotone_first; auto with ord.
    apply (limit_boundedSup VF). apply VF_limit. }
  unfold boundedSup.
  transitivity (supOrd (fun x => veblen ε (VF_denote x) 0)).
  { apply veblen_continuous_first; auto with ord. exact Z. }
  apply sup_least. intro x.
  transitivity (VF_denote (W x Z)).
  simpl; reflexivity.
  apply index_le.
Qed.

Theorem VF_is_complete: complete VF.
Proof.
  hnf; intuition.
  - hnf; simpl; intros.
    destruct (VF_decide_order a1 a2); auto with ord.
    exists a2. split; auto with ord.
    exists a1. split; auto with ord.
  - left. constructor. exact Z.
Qed.

Theorem VF_Γ₀ : VF ≈ Γ 0.
Proof.
  split.
  - rewrite ord_le_unfold. intro x.
    apply VF_below_Γ₀.
  - rewrite Γalt; auto.
    rewrite enum_fixpoints_zero; auto with ord.
    apply normal_fix_least; auto with ord.
    apply VF_is_complete.
    apply VF_veblen_closed.
Qed.

Lemma expOrd_interpolants:
  forall b,
    complete b ->
    has_interpolants VF_denote VF_isNormal b ->
    has_interpolants VF_denote VF_isNormal (expOrd ω b).
Proof.
  intros b Hb1 Hb2.
  assert (has_interpolants VF_denote VF_isNormal (veblen (addOrd 1) b 0)).
  { apply veblen_interpolants_first with (vr := Vnorm); auto.
    + apply VF_has_cantor_decomposition.
    + intros.
      intros. apply onePlus_interpolants with (zr:=Z) (pr:=VF_add VF_one); auto.
      apply VF_reflects_zero.
      hnf; intros; auto.
      apply VF_add_reflects; simpl in *; intuition.
      rewrite veblen_zero. rewrite addOrd_zero_r.
      reflexivity.
    + hnf; simpl; intuition.
      rewrite Vnorm_equal; simpl; auto.
      apply veblen_onePlus_eq_mor; auto.
      apply Vnorm_isNormal; auto. }
  rewrite veblen_onePlus in H; auto.
  rewrite addOrd_zero_r in H.
  assumption.
Qed.

Lemma ε_interpolants:
  forall b : Ord,
    complete b ->
    has_interpolants VF_denote VF_isNormal b ->
    has_interpolants VF_denote VF_isNormal (ε b).
Proof.
  intros. unfold ε.
  apply enum_fix_has_interpolants with (enum_gr := fun x => Wnorm Z x); auto with ord.
  - apply VF_has_cantor_decomposition.
  - intros. apply expOrd_interpolants; auto.
  - intros. apply normal_inflationary; auto with ord.
  - hnf; simpl; intuition.
    rewrite Wnorm_equal; simpl; auto.
    rewrite veblen_zero.
    split; apply enum_fixpoints_monotone; auto with ord; apply H2.
    apply Wnorm_isNormal; simpl; auto.
Qed.

Theorem VF_has_all_interpolants:
  has_all_interpolants VF_denote VF_isNormal.
Proof.
  intro x.
  induction x as [x Hindx] using (size_induction VF).
  intros Hnorm.
  destruct x as [|a b|a b].
  - hnf; simpl; intros i Hi. rewrite ord_lt_unfold in Hi. destruct Hi as [[] _].
  - apply veblen_interpolants
      with (f:=VF_denote) (P:=VF_isNormal) (g:=addOrd 1) (a:=a) (b:=VF_denote b) (vr:=Vnorm); auto.
    + apply VF_has_cantor_decomposition.
    + intros. apply onePlus_interpolants with (zr:=Z) (pr:=VF_add VF_one); auto.
      apply VF_reflects_zero.
      hnf; intros; auto.
      apply VF_add_reflects; simpl in *; intuition.
      rewrite veblen_zero. rewrite addOrd_zero_r.
      reflexivity.
    + hnf; simpl; intuition.
      rewrite Vnorm_equal; simpl; auto.
      apply veblen_onePlus_eq_mor; auto.
      apply Vnorm_isNormal; auto.
    + simpl in Hnorm; intuition.
    + intros; apply Hindx; auto.
      destruct (VF_normal_subterm_shrink _ Hnorm); auto.
      simpl in Hnorm; intuition.
    + apply Hindx; auto.
      destruct (VF_normal_subterm_shrink _ Hnorm); auto.
      simpl in Hnorm; intuition.

  - apply veblen_interpolants
      with (f:=VF_denote) (P:=VF_isNormal) (g:=ε) (a:=a) (b:=VF_denote b) (vr:=Wnorm); auto with ord.
    + apply VF_has_cantor_decomposition.
    + intros; apply ε_interpolants; auto.
    + hnf; simpl; intuition.
      rewrite Wnorm_equal; simpl; auto.
      destruct H0; destruct H2.
      split; apply veblen_monotone_full; auto with ord.
      apply Wnorm_isNormal; auto.
    + simpl in Hnorm; intuition.
    + intros; apply Hindx; auto.
      destruct (VF_normal_subterm_shrink _ Hnorm); auto.
      simpl in Hnorm; intuition.
    + apply Hindx; auto.
      destruct (VF_normal_subterm_shrink _ Hnorm); auto.
      simpl in Hnorm; intuition.
Qed.


Definition VF_nadd := cantor_nadd VF_has_cantor_decomposition.

Theorem VF_reflects_nadd: reflects VForm VF_denote VF_isNormal (ORD ==> ORD ==> ORD) naddOrd VF_nadd.
Proof.
  apply cantor_nadd_reflects.
  apply VF_has_all_interpolants.
Qed.


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VW_has_enough_notations (EM:excluded_middle) :
  forall x, x < Γ 0 -> exists v:VF, v ≈ x.
Proof.
  intros x H.
  rewrite <- VF_Γ₀ in H.
  assert (HVF: has_enough_notations VF_denote VF_isNormal).
  { apply has_interpolants_has_enough_notations with (A:=VForm) (f:=VF_denote) (P:=VF_isNormal); auto.
    apply VF_has_all_interpolants. }
  hnf in HVF.
  rewrite ord_lt_unfold in H.
  destruct H as [a Ha].
  destruct (HVF (VF_normalize a) x) as [c [Hc1 Hc2]].
  apply VF_normalize_isNormal.
  rewrite VF_normalize_equal. auto.
  exists c; auto.
Qed.

Theorem VW_has_enough_notations' (EM:excluded_middle) :
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
    exists (VF_succ (VF_normalize vo)).
    rewrite Ho. rewrite <- Hvo.
    destruct (VF_succ_reflects (VF_denote vo) (VF_normalize vo)).
    split. symmetry. apply VF_normalize_equal.
    apply VF_normalize_isNormal.
    symmetry. auto with ord.

  - (* x is a limit, it must be a fixpoint of (addOrd 1) *)
    assert (Hlimit' : 1 + x <= x). { apply limit_onePlus; auto. }

    destruct (classical.order_total EM (veblen (addOrd 1) x 0) x) as [Hepsilon|Hepsilon].
    (* x is an epsilon number, find its W form *)
    * rewrite veblen_onePlus in Hepsilon; auto.
      2:{ apply classical.ord_complete; auto. }
      rewrite addOrd_zero_r in Hepsilon.

      (* Is x a fixpoint of the epsilon function? *)
      destruct (classical.order_total EM (ε x) x); auto.
      + (* x is a fixpoint of epsilon *)

        (* x cannot be a Γ number, as it would be too large *)
        assert (Hgamma : x < veblen ε x 0).
        { destruct (classical.order_total EM (veblen ε x 0) x); auto.
          elim (ord_lt_irreflexive (Γ 0)).
          apply ord_le_lt_trans with x; auto.
          rewrite Γalt; auto; simpl.
          apply fixOrd_least; auto.
          intros; apply veblen_monotone_first; auto.
          intros; apply normal_monotone; auto with ord.
          rewrite ord_le_unfold; intros []. }

        (* decompose the ordinal *)
        destruct (veblen_decompose EM ε ε_normal x) as [a [b [Hab [_[Ha Hb]]]]]; auto.

        (* invoke the induction hypotheses *)
        destruct (Hx a) as [va Hva]; auto.
        transitivity x; auto.
        destruct (Hx b) as [vb Hvb]; auto.
        transitivity x; auto.

        (* exhibit the W form and wrap up *)
        exists (W va vb).
        simpl. rewrite Hab.
        transitivity (veblen ε a (VF_denote vb)).
        split; apply veblen_monotone_first; auto with ord; apply Hva.
        split; apply veblen_monotone; auto with ord; apply Hvb.

      + (* x is not a fixpoint of epsilon *)
        destruct (enum_fixpoint_decompose EM (expOrd ω) powOmega_normal x Hlimit) as [a [Ha1 Ha2]]; auto.
        destruct (Hx a) as [af Ha3]; auto with ord.
        transitivity x; auto.
        exists (W Z af); simpl; auto.
        rewrite veblen_zero.
        rewrite Ha1.
        split; apply enum_fixpoints_monotone; auto; apply Ha3.

    (* x is not a epsilon number, find its V form *)
    * (* decompose the ordinal *)
      destruct (veblen_decompose EM (addOrd 1) (onePlus_normal) x) as [a [b [Hab [_ [Ha Hb]]]]]; auto.

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
