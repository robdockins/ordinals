From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import Arith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Open Scope list.

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
From Ordinal Require Import AckermannTower.

From Ordinal Require Import Notation.CantorDecomposition.

Open Scope ord_scope.

Local Hint Resolve
      ackermann_tower_fin_normal
      veblen_complete
      veblen_normal
      veblen_first_normal
      veblen_first_onePlus_normal
      normal_monotone
      normal_complete
      onePlus_normal
      powOmega_normal
      addOrd_complete
      addOrd_increasing
      succ_complete
      zero_complete
      natOrdSize_complete
  : core.

Inductive VForm : Set :=
| Z : VForm
| V : nat -> VForm -> VForm -> VForm.

Fixpoint VF_size (x:VForm) : nat :=
  match x with
  | Z => O
  | V _ x y => S (VF_size x + VF_size y)
  end.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | V n a x => veblen (ackermann_tower_fin (addOrd 1) n) (VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x; auto.
  simpl; apply veblen_complete; auto.
Qed.

Local Hint Resolve VF_complete : core.

Definition VF_isZero x : { x = Z } + { 0 < VF_denote x }.
Proof.
  destruct x; auto.
  right. simpl. apply veblen_nonzero; auto.
Qed.

Theorem V_collapse :
  forall n a b x,
    VF_denote a < VF_denote b ->
    VF_denote (V n a (V n b x)) ≈ VF_denote (V n b x).
Proof.
  intros. simpl.
  apply veblen_fixpoints; auto.
Qed.

Theorem Vmn_collapse : forall n m a b c,
  (m < n)%nat ->
  VF_denote a < VF_denote (V n b c) ->
  VF_denote (V m a (V n b c)) ≈ VF_denote (V n b c).
Proof.
  simpl VF_denote.
  intros.
  split. 2: { apply veblen_inflationary; auto. }
  apply veblen_collapse; auto with ord.
  destruct (VF_isZero b); subst; simpl.
  { rewrite veblen_zero at 2.
    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
    apply veblen_monotone_first; auto with ord.
    rewrite veblen_zero; auto with ord. }
  rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
  rewrite veblen_zero.
  rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
  apply veblen_monotone_first; auto with ord.
  apply normal_inflationary; auto with ord.
Qed.

Theorem Vmn_collapse2 : forall n m b c,
  (m < n)%nat ->
  VF_denote (V m (V n b c) Z) ≈ VF_denote (V n b c).
Proof.
  intros. simpl. split.
  - destruct (VF_isZero b); subst; simpl.
    { rewrite veblen_zero at 2.
      rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
      apply veblen_monotone_first; auto with ord.
      rewrite veblen_zero; auto with ord. }
    rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
    rewrite veblen_zero.
    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
    apply veblen_monotone_first; auto with ord.
    apply normal_inflationary; auto with ord.
  - apply normal_inflationary with (f:= fun x => veblen _ x 0); auto with ord.
Qed.

Fixpoint VF_compare (x:VForm) : VForm -> ordering :=
  fix inner (y:VForm) : ordering :=
    match x, y with
    | Z, Z       => EQ
    | Z, V _ _ _ => LT
    | V _ _ _, Z => GT

    | V m a x', V n b y' =>
      match nat_compare m n with
      | LT =>
        match VF_compare a (V n b y') with
        | LT => VF_compare x' (V n b y')
        | EQ => if VF_isZero x' then EQ else GT
        | GT => GT
        end

      | EQ =>
        match VF_compare a b with
        | LT => VF_compare x' y
        | EQ => VF_compare x' y'
        | GT => inner y'
        end

      | GT =>
        match inner b with
        | LT => LT
        | EQ => if VF_isZero y' then EQ else LT
        | GT => inner y'
        end
      end
    end.

Lemma VF_compare_lt m n a x b y :
  (m < n)%nat ->
  VF_compare (V m a x) (V n b y) =
  match VF_compare a (V n b y) with
  | LT => VF_compare x (V n b y)
  | EQ => if VF_isZero x then EQ else GT
  | GT => GT
  end.
Proof.
  intro H.
  generalize (nat_compare_correct m n); intro.
  simpl. destruct (nat_compare m n); try lia.
  reflexivity.
Qed.

Lemma VF_compare_eq m a x b y :
  VF_compare (V m a x) (V m b y) =
  match VF_compare a b with
  | LT => VF_compare x (V m b y)
  | EQ => VF_compare x y
  | GT => VF_compare (V m a x) y
  end.
Proof.
  generalize (nat_compare_correct m m); intro.
  simpl. destruct (nat_compare m m); try lia.
  reflexivity.
Qed.

Lemma VF_compare_gt m n a x b y :
  (m > n)%nat ->
  VF_compare (V m a x) (V n b y) =
  match VF_compare (V m a x) b with
  | LT => LT
  | EQ => if VF_isZero y then EQ else LT
  | GT => VF_compare (V m a x) y
  end.
Proof.
  intro H.
  generalize (nat_compare_correct m n); intro.
  simpl.
  destruct (nat_compare m n); try lia.
  reflexivity.
Qed.

Fixpoint VF_isNormal (x:VForm) : Prop :=
  match x with
  | Z => True
  | V m a b => VF_isNormal a /\
               VF_isNormal b /\
               match b with
               | Z =>
                 match a with
                 | Z => True
                 | V n _ _ => (m >= n)%nat
                 end
               | V n x y =>
                 match nat_compare m n with
                 | LT => VF_denote a >= VF_denote b
                 | EQ => VF_denote a >= VF_denote x
                 | GT => True
                 end
               end
  end.

Definition subterm_shrink x :=
  match x with
  | Z => True
  | V m a b => VF_denote a < VF_denote (V m a b) /\
               VF_denote b < VF_denote (V m a b)
  end.

Lemma normal_subterm_shrink : forall x, VF_isNormal x -> subterm_shrink x.
Proof.
  induction x; simpl; intuition.
  - destruct x2.
    + destruct x1; simpl in *; intuition auto with ord.
      * apply ord_le_lt_trans with
            (veblen (ackermann_tower_fin (addOrd 1) n) (VF_denote x1_1) (VF_denote x1_2)).
        apply veblen_monotone_func; auto.
        intros. apply ackermann_tower_fin_monotone; auto with ord.
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + simpl in *.
      apply veblen_subterm1; auto with ord.
  - destruct x2; simpl in *; intuition auto with ord.
    + generalize (nat_compare_correct n n0).
      destruct (nat_compare n n0); intros; subst.
      * (* LT case *)
        rewrite H2 at 1.
        apply veblen_subterm1; auto with ord.
      * (* EQ case *)
        apply veblen_increasing'; auto.
      * (* GT case *)
        apply veblen_collapse'; auto.
        eapply ord_lt_le_trans; [ apply H |].
        apply veblen_inflationary; auto.
        eapply ord_lt_le_trans; [ apply H6 |].
        apply veblen_inflationary; auto.

        destruct (VF_isZero x1).
        { subst; simpl.
          rewrite veblen_zero at 2.
          rewrite <- ackermann_tower_fin_fixpoints with (m:=n0); auto with ord.
          apply veblen_monotone_first; auto with ord.
          rewrite veblen_zero. auto with ord. }
        rewrite <- veblen_fixpoints with (α:=0) (β:= VF_denote x1) at 2; auto with ord.
        rewrite veblen_zero.
        rewrite <- ackermann_tower_fin_fixpoints with (m:=n0); auto with ord.
        apply veblen_monotone_first; auto with ord.
        apply normal_inflationary; auto with ord.
Qed.

Lemma VF_compare_correct :
  forall x y,
    match VF_compare x y with
    | LT => VF_denote x < VF_denote y
    | EQ => VF_denote x ≈ VF_denote y
    | GT => VF_denote x > VF_denote y
    end.
Proof.
  induction x as [|m a Ha x Hx]; intros y.
  - destruct y as [|n b y].
    + simpl. reflexivity.
    + simpl. apply veblen_nonzero; auto.
  - induction y as [|n b Hb y Hy].
    + simpl. apply veblen_nonzero; auto.
    + generalize (nat_compare_correct m n).
      destruct (nat_compare m n); intro Hmn.
      * rewrite VF_compare_lt; auto.
        generalize (Ha (V n b y)).
        destruct (VF_compare a (V n b y)); intros.
        ** generalize (Hx (V n b y)).
           destruct (VF_compare x (V n b y)); intros.
           *** simpl.
               apply veblen_collapse'; simpl; auto.
               destruct (VF_isZero b); subst; simpl.
               **** rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero; auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    apply normal_inflationary; auto with ord.

           *** simpl. split.
               apply veblen_collapse; auto.
               apply H0; simpl; intuition.
               2:{ simpl in H0. rewrite <- H0; simpl; auto. apply veblen_inflationary; auto with ord. }
               destruct (VF_isZero b); subst; simpl.
               **** rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero; auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    apply normal_inflationary; auto with ord.
           *** simpl.
               simpl in H0.
               eapply ord_lt_le_trans; [ apply H0; simpl; auto |].
               intuition.
               apply veblen_inflationary; auto.

        ** destruct (VF_isZero x); subst; simpl.
           *** split. simpl in H.
               2:{ rewrite <- H.
                   apply (normal_inflationary (fun i => veblen _ i 0)); auto. }
               destruct (VF_isZero b); subst; simpl.
               **** rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    simpl in H.
                    rewrite veblen_zero in H.
                    apply H.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b); auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite H.
                    apply normal_inflationary; auto with ord.
           *** apply ord_le_lt_trans with (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) 0).
               rewrite <- H.
               apply (normal_inflationary (fun i => veblen _ i 0)); auto.
               apply veblen_increasing; auto with ord.

        ** apply ord_lt_le_trans with (VF_denote a).
           apply H; simpl; auto.
           simpl.
           transitivity (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) 0).
           apply (normal_inflationary (fun i => veblen _ i 0)); auto.
           apply veblen_monotone; auto with ord.

      * subst n.
        rewrite VF_compare_eq.
        simpl; apply veblen_compare_correct; auto.
        apply Ha; simpl; intuition.
        apply Hx; simpl; intuition.
        apply Hx; simpl; intuition.

      * rewrite VF_compare_gt; auto.
        destruct (VF_compare (V m a x) b); intros.
        ** apply ord_lt_le_trans with (VF_denote b); auto.
           simpl.
           transitivity (veblen (ackermann_tower_fin (addOrd 1) n) (VF_denote b) 0).
           apply (normal_inflationary (fun i => veblen _ i 0)); auto.
           apply veblen_monotone; auto with ord.

        ** destruct (VF_isZero y); subst; simpl.
           *** split. simpl in Hb.
               { rewrite Hb.
                 apply (normal_inflationary (fun i => veblen _ i 0)); auto. }
               destruct (VF_isZero a); subst; simpl.
               **** rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    simpl in Hb.
                    rewrite veblen_zero in Hb.
                    apply Hb.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote a); auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite <- Hb.
                    apply normal_inflationary; auto with ord.
           *** apply ord_le_lt_trans with (veblen (ackermann_tower_fin (addOrd 1) n) (VF_denote b) 0).
               rewrite Hb.
               apply (normal_inflationary (fun i => veblen _ i 0)); auto.
               apply veblen_increasing; auto with ord.

        ** destruct (VF_compare (V m a x) y); intros.
           *** apply ord_lt_le_trans with (VF_denote y); auto.
               simpl.
               apply normal_inflationary; auto.
           *** split.
               { rewrite Hy. simpl. apply normal_inflationary; auto. }
               simpl. apply veblen_collapse; auto.
               apply Hy.
               destruct (VF_isZero a); subst; simpl.
               **** rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero.
                    auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote a) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    apply normal_inflationary; auto with ord.
           *** simpl.
               apply veblen_collapse'; auto.
               destruct (VF_isZero a); subst; simpl.
               **** rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero.
                    auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote a) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fin_fixpoints with (m:=n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    apply normal_inflationary; auto with ord.
Qed.

Global Opaque VF_compare.

Theorem VF_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y).
  - intro. left; auto.
  - intros.
    right; auto. apply H.
  - intros. right; auto with ord.
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

Lemma VF_isNormal_dec: forall x, { VF_isNormal x } + { ~VF_isNormal x }.
Proof.
  induction x; simpl; intros; auto.
  intuition; auto.
  destruct x2.
  - destruct x1; auto.
    destruct (Compare_dec.ge_dec n n0); intuition.
  - generalize (nat_compare_correct n n0).
    destruct (nat_compare n n0); intuition.
    + generalize (VF_compare_correct (V n0 x2_1 x2_2) x1).
      destruct (VF_compare (V n0 x2_1 x2_2) x1); intuition auto with ord.
      left; intuition. apply H0.
      right; intuition.
      elim (ord_lt_irreflexive (VF_denote x1)).
      eapply ord_lt_le_trans; eauto.
    + subst.
      generalize (VF_compare_correct x2_1 x1).
      destruct (VF_compare x2_1 x1); intuition auto with ord.
      left; intuition. apply H.
      right; intuition.
      elim (ord_lt_irreflexive (VF_denote x1)).
      eapply ord_lt_le_trans; eauto.
Qed.

Inductive redex : VForm -> VForm -> Prop:=
| redex_V : forall n a b x,
    VF_compare a b = LT ->
    redex (V n a (V n b x)) (V n b x)
| redex_Vmn1 : forall m n a b c,
    (m < n)%nat ->
    VF_compare a (V n b c) = LT ->
    redex (V m a (V n b c)) (V n b c)
| redex_Vmn2 : forall m n b c,
    (m < n)%nat ->
    redex (V m (V n b c) Z) (V n b c).

Lemma redex_sound: forall x y,
    redex x y ->
    VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. inversion H; subst.
  - apply V_collapse; auto.
    apply VF_lt_correct; auto.
  - apply Vmn_collapse; auto.
    apply VF_lt_correct; auto.
  - apply Vmn_collapse2; auto.
Qed.

Inductive one_step_reduce: VForm -> VForm -> Prop :=
| reduce_redex: forall x y, redex x y -> one_step_reduce x y
| reduce_cong1: forall n x x' y, one_step_reduce x x' -> one_step_reduce (V n x y) (V n x' y)
| reduce_cong2: forall n x y y', one_step_reduce y y' -> one_step_reduce (V n x y) (V n x y').

Lemma one_step_reduce_sound: forall x y, one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H.
  - apply redex_sound; auto.
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


Fixpoint VF_onePlus (x:VForm) :=
  match x with
  | Z => V 0 Z Z
  | V 0 Z x' => V 0 Z (VF_onePlus x')
  | _ => x
  end.

Lemma VF_onePlus_equal: forall x, VF_denote (VF_onePlus x) ≈ 1 + VF_denote x.
Proof.
  induction x; simpl.
  - rewrite veblen_zero. auto with ord.
  - destruct n.
    + destruct x1; simpl.
      * repeat rewrite veblen_zero.
        rewrite IHx2; auto with ord.
      * symmetry. apply onePlus_veblen; auto with ord.
    + destruct (VF_isZero x1); subst; simpl.
      * repeat rewrite veblen_zero.
        rewrite enum_are_fixpoints; auto with ord.
        rewrite onePlus_veblen; auto with ord.
      * rewrite onePlus_veblen; auto with ord.
Qed.

Lemma VF_onePlus_normal : forall x, VF_isNormal x -> VF_isNormal (VF_onePlus x).
Proof.
  induction x; simpl; intuition.
  destruct n.
  - destruct x1; simpl in *; intuition.
    destruct x2; simpl in *; intuition auto with ord.
    destruct n; simpl.
    + destruct x2_1; simpl in *; intuition.
    + elim (ord_lt_irreflexive 0).
      eapply ord_lt_le_trans; [ | apply H2 ].
      apply veblen_nonzero; auto.
  - destruct x1; simpl in *; intuition.
Qed.

Lemma one_step_cong_helper1 : forall n x y,
  (exists z, one_step_reduce x z) -> exists z, one_step_reduce (V n x y) z.
Proof.
  intros n x y [z H].
  exists (V n z y).
  apply reduce_cong1; auto.
Qed.

Lemma one_step_cong_helper2 : forall n x y,
  (exists z, one_step_reduce y z) -> exists z, one_step_reduce (V n x y) z.
Proof.
  intros n x y [z H].
  exists (V n x z).
  apply reduce_cong2; auto.
Qed.

Lemma multi_reduce_conj1: forall m x x' y ,
  clos_refl_trans VForm one_step_reduce x x' ->
  clos_refl_trans VForm one_step_reduce (V m x y) (V m x' y).
Proof.
  intros m x x' y H. induction H.
  - apply rt_step.
    apply reduce_cong1; auto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma multi_reduce_conj2: forall m x y  y',
  clos_refl_trans VForm one_step_reduce y y' ->
  clos_refl_trans VForm one_step_reduce (V m x y) (V m x y').
Proof.
  intros m x y y' H. induction H.
  - apply rt_step.
    apply reduce_cong2; auto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma VF_notIsNormal_redex: forall x, ~VF_isNormal x <-> exists y, one_step_reduce x y.
Proof.
  induction x; simpl.
  - intuition.
    destruct H as [y H].
    inversion H; subst.
    inversion H1.
  - split.
    + intuition.
      destruct (VF_isNormal_dec x1).
      2:{ apply one_step_cong_helper1; auto. }
      destruct (VF_isNormal_dec x2).
      2:{ apply one_step_cong_helper2; auto. }
      intuition.
      destruct x2.
      * destruct x1; intuition.
        econstructor.
        apply reduce_redex.
        apply redex_Vmn2. lia.
      * generalize (nat_compare_correct n n0).
        destruct (nat_compare n n0); intuition.
        ** econstructor.
           apply reduce_redex.
           apply redex_Vmn1. lia.
           generalize (VF_compare_correct x1 (V n0 x2_1 x2_2)); intro.
           destruct (VF_compare x1 (V n0 x2_1 x2_2)); auto with ord.
           elim H; apply H5.
           elim H. auto with ord.
        ** subst.
           econstructor.
           apply reduce_redex.
           apply redex_V.
           generalize (VF_compare_correct x1 x2_1); intro.
           destruct (VF_compare x1 x2_1); auto with ord.
           elim H; apply H4.
           elim H. auto with ord.
    + intros [y Hy] [Hx1 [Hx2 H]].
      inversion Hy; subst.
      * inversion H0; subst.
        ** generalize (nat_compare_correct n n); intro.
           destruct (nat_compare n n); try lia.
           elim (ord_lt_irreflexive (VF_denote x1)).
           eapply ord_lt_le_trans; eauto.
           apply VF_lt_correct; auto.
        ** generalize (nat_compare_correct n n0); intro.
           destruct (nat_compare n n0); try lia.
           elim (ord_lt_irreflexive (VF_denote x1)).
           eapply ord_lt_le_trans; eauto.
           apply VF_lt_correct; auto.
        ** lia.
      * revert Hx1.
        rewrite IHx1.
        eauto.
      * revert Hx2.
        rewrite IHx2.
        eauto.
Qed.

Lemma VF_isNormal_no_redex: forall x, VF_isNormal x <-> ~exists y, one_step_reduce x y.
Proof.
  intros x.
  generalize (VF_notIsNormal_redex x).
  destruct (VF_isNormal_dec x); intuition.
Qed.

Definition Vnorm m a b :=
  match b with
  | Z =>
      match a with
      | Z => V m Z Z
      | V n c _  =>
          match nat_compare m n with
          | LT => a
          | _ => V m a b
          end
      end
  | V n x y =>
        match nat_compare m n with
        | LT => match VF_compare a b with
                | LT => b
                | _  => V m a b
                end
        | EQ => match VF_compare a x with
                | LT => b
                | _  => V m a b
                end
        | GT => V m a b
        end
  end.

Lemma Vnorm_reduce: forall m a b,
    clos_refl_trans VForm one_step_reduce (V m a b) (Vnorm m a b).
Proof.
  intros. unfold Vnorm.
  destruct b; simpl.
  - destruct a; simpl.
    + apply rt_refl.
    + generalize (nat_compare_correct m n); intro Hcomp.
      destruct (nat_compare m n); try apply rt_refl.
      apply rt_step.
      apply reduce_redex.
      apply redex_Vmn2; auto.
  - generalize (nat_compare_correct m n); intro Hcomp.
    destruct (nat_compare m n); try apply rt_refl.
    + generalize (VF_compare_correct a (V n b1 b2)); auto.
      destruct (VF_compare a (V n b1 b2)); intuition; try apply rt_refl.
      apply rt_step.
      apply reduce_redex.
      apply redex_Vmn1; auto.
      apply VF_lt_correct; auto.
    + subst.
      generalize (VF_compare_correct a b1); intuition.
      destruct (VF_compare a b1); intuition; try apply rt_refl.
      apply rt_step.
      apply reduce_redex.
      apply redex_V; auto.
      apply VF_lt_correct; auto.
Qed.

Lemma Vnorm_normal m a b :
  VF_isNormal a ->
  VF_isNormal b ->
  VF_isNormal (Vnorm m a b).
Proof.
  intros Ha Hb. unfold Vnorm.
  destruct b.
  destruct a; simpl; auto.
  - generalize (nat_compare_correct m n); simpl.
    destruct (nat_compare m n); simpl in *; intuition auto with ord arith.
    lia.
  - simpl in *. intuition.
    generalize (nat_compare_correct m n); simpl.
    case_eq (nat_compare m n); simpl in *; intuition.
    + generalize (VF_compare_correct a (V n b1 b2)).
      destruct (VF_compare a (V n b1 b2)); simpl.
      * intuition.
      * intuition.
        rewrite H0. rewrite H4.
        auto with ord.
      * intuition.
        rewrite H0. auto with ord.
    + generalize (VF_compare_correct a b1).
      destruct (VF_compare a b1); simpl in *; intuition.
      rewrite H0. apply H4.
      rewrite H0. auto with ord.
    + rewrite H0; auto.
Qed.

Lemma Vnorm_equal m a b :
  VF_isNormal a ->
  VF_isNormal b ->
  VF_denote (Vnorm m a b) ≈ VF_denote (V m a b).
Proof.
  intros. symmetry.
  apply step_reduce_sound; auto.
  apply Vnorm_reduce; apply normal_well_formed; auto.
Qed.

Fixpoint VF_normalize x :=
  match x with
  | Z => Z
  | V m a b => Vnorm m (VF_normalize a) (VF_normalize b)
  end.

Theorem VF_normalize_isNormal : forall x, VF_isNormal (VF_normalize x).
Proof.
  induction x; simpl; auto.
  apply Vnorm_normal; auto.
Qed.

Theorem VF_normalize_reduce: forall x,
  clos_refl_trans _ one_step_reduce x (VF_normalize x).
Proof.
  induction x; simpl.
  - apply rt_refl.
  - apply rt_trans with (V n (VF_normalize x1) x2).
    { apply multi_reduce_conj1; auto. }
    apply rt_trans with (V n (VF_normalize x1) (VF_normalize x2)).
    { apply multi_reduce_conj2; auto. }
    apply Vnorm_reduce.
Qed.

Theorem VF_normalize_equal : forall x, VF_denote (VF_normalize x) ≈ VF_denote x.
Proof.
  intros. symmetry.
  apply step_reduce_sound; auto.
  apply VF_normalize_reduce.
Qed.

Theorem normal_forms_unique :
  forall x y,
    VF_isNormal x ->
    VF_isNormal y ->
    VF_denote x ≈ VF_denote y ->
    x = y.
Proof.
  induction x as [|m a Ha x Hx].
  - intros [|n b y]; simpl; intuition.
    elim (ord_lt_irreflexive 0).
    rewrite H1 at 2.
    apply veblen_nonzero; auto.
  - intros [|n b y]; simpl; intuition.
    + elim (ord_lt_irreflexive 0).
      rewrite <- H1 at 2.
      apply veblen_nonzero; auto.
    + assert (Hmn : m = n).
      { generalize (nat_compare_correct m n); auto.
        destruct (nat_compare m n); intros; auto.
        - exfalso.
          elim (ord_lt_irreflexive (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (Vmn_collapse n m a b y); auto.
          simpl.
          apply veblen_increasing; auto with ord.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          simpl.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
        - exfalso.
          elim (ord_lt_irreflexive (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (Vmn_collapse m n b a x); auto.
          simpl.
          apply veblen_increasing; auto with ord.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto. }
      subst n.
      assert (a = b).
      { apply Ha; auto.
        destruct (VF_decide_order a b).
        { elim (ord_lt_irreflexive (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (V_collapse m a b y).
          simpl.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; intuition.
          auto. }
        destruct (VF_decide_order b a).
        { elim (ord_lt_irreflexive (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (V_collapse m b a x).
          simpl.
          apply veblen_increasing; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V m b y)); simpl; intuition.
          auto. }
        split; auto. }
      subst b.
      f_equal.
      apply Hx; auto.
      destruct (VF_decide_order x y).
      { elim (ord_lt_irreflexive (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) (VF_denote x))).
        rewrite H1 at 2.
        apply veblen_increasing'; auto with ord. }
      destruct (VF_decide_order y x).
      { elim (ord_lt_irreflexive (veblen (ackermann_tower_fin (addOrd 1) m) (VF_denote a) (VF_denote x))).
        rewrite H1 at 1.
        apply veblen_increasing'; auto with ord. }
      split; auto.
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
  { apply normal_forms_unique; auto.
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
  - rewrite <- VF_isNormal_no_redex.
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
  intros x y H. induction H; simpl; intuition auto with arith.
  apply redex_size; auto.
Qed.

Theorem strongly_normalizing: forall x, exists y, normalizes x y.
Proof.
  induction x as [x Hind] using (well_founded_induction (Wf_nat.well_founded_ltof _ VF_size)).
  destruct (VF_isNormal_dec x).
  - eexists.
    apply normal_normalizing.
    apply VF_isNormal_no_redex; auto.
  - assert (exists y, one_step_reduce x y).
    { rewrite <- VF_notIsNormal_redex. auto. }
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
    rewrite VF_isNormal_no_redex; auto.
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
      apply normal_forms_unique; intuition.
      rewrite <- H0.
      rewrite H. auto. }
    subst; auto.
  - destruct H as [z [Hz1 Hz2]].
    apply normalizes_correct in Hz1.
    apply normalizes_correct in Hz2.
    intuition.
    rewrite H. symmetry; auto.
Qed.

Lemma veblen_tower_epsilon :
  forall n x y,
    complete x ->
    complete y ->
    (n > 0)%nat ->
    expOrd ω (veblen (ackermann_tower_fin (addOrd 1) n) x y) ≈ veblen (ackermann_tower_fin (addOrd 1) n) x y.
Proof.
  intros.
  split.
  - transitivity (veblen (ackermann_tower_fin (addOrd 1) 0) (veblen (ackermann_tower_fin (addOrd 1) n) x y) 0).
    + simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r. auto with ord.
    + destruct (complete_zeroDec x); auto.
      * transitivity (ackermann_tower_fin (addOrd 1) n y).
        ** rewrite <- ackermann_tower_fin_fixpoints with (m := 0%nat); auto with ord.
           apply veblen_monotone_first; auto with ord.
           transitivity (veblen (ackermann_tower_fin (addOrd 1) n) 0 y).
           *** apply veblen_monotone_first; auto with ord.
           *** rewrite veblen_zero.
               auto with ord.
        ** rewrite veblen_unroll.
           auto with ord.
      * rewrite <- veblen_fixpoints with (α:=0) (β:=x) at 2; auto with ord.
        rewrite veblen_zero.
        rewrite <- ackermann_tower_fin_fixpoints with (m := 0%nat); auto with ord.
        simpl.
        apply veblen_monotone_first; auto with ord.
        apply normal_inflationary; auto with ord.
  - apply normal_inflationary; auto.
Qed.

Fixpoint VF_decompose (x:VForm) : list VForm :=
  match x with
  | Z => []
  | V m a b =>
      match m with
      | O => a :: VF_decompose b
      | _ => [x]
      end
  end.

Fixpoint VF_recompose (xs:list VForm) : VForm :=
  match xs with
  | [] => Z
  | [x] =>
      match x with
      | Z => V O Z Z
      | V O _ _ => V O x Z
      | _ => x
      end
  | x::xs' => V O x (VF_recompose xs')
  end.

Lemma VF_decompose_correct:
  forall x,
    VF_isNormal x ->
    each VF_isNormal (VF_decompose x) /\
    cantor_ordered VF_denote (VF_decompose x) /\
    VF_denote x ≈ cantor_denote VF_denote (VF_decompose x).
Proof.
  induction x; simpl; intuition auto with ord.
  destruct n.
  simpl; auto.
  simpl in *; intuition.
  destruct n; simpl; auto.
  split; auto.
  destruct x2; simpl; auto.
  destruct n; simpl in *; auto.

  destruct n.
  - rewrite veblen_onePlus; auto with ord.
    rewrite H8. reflexivity.

  - simpl in *. rewrite addOrd_zero_r.
    symmetry. apply (veblen_tower_epsilon (S n)); auto with arith.
Qed.

Lemma VF_recompose_correct:
  forall xs,
    each VF_isNormal xs ->
    cantor_ordered VF_denote xs ->
    VF_isNormal (VF_recompose xs) /\ cantor_denote VF_denote xs ≈ VF_denote (VF_recompose xs).
Proof.
  induction xs; simpl in *; intuition auto with ord.
  destruct xs; simpl; intuition.
  destruct a; simpl; intuition.
  destruct n; simpl; auto.

  simpl in *; intuition.
  destruct xs; simpl in *; intuition.
  destruct v; simpl in *; intuition.
  destruct n; simpl in *; intuition.
  destruct xs; simpl in *; intuition.
  destruct a; simpl in *; intuition.
  rewrite veblen_onePlus; auto with ord.
  destruct n; simpl; auto.
  rewrite veblen_onePlus; auto with ord.
  rewrite veblen_onePlus; auto with ord.
  rewrite addOrd_zero_r.
  apply (veblen_tower_epsilon (S n)); auto with ord arith.

  rewrite veblen_onePlus; auto.
  rewrite H5.
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

Theorem VF_ackermann_reflects n:
  reflects VForm VF_denote VF_isNormal
    (ORD ==> ORD ==> ORD)
    (veblen (ackermann_tower_fin (addOrd 1) n))
    (Vnorm n).
Proof.
  hnf; intros a b [H1 H2].
  hnf; intros x y [H3 H4].
  hnf. split.
  - rewrite Vnorm_equal; simpl; auto.
    destruct H1. destruct H3.
    split; apply veblen_monotone_full; auto with ord.
  - apply Vnorm_normal; auto.
Qed.

Theorem VF_has_all_interpolants:
  has_all_interpolants VF_denote VF_isNormal.
Proof.
  intro x.
  induction x as [x Hindx] using (size_induction VF).
  intros Hnorm.
  destruct x as [|n a b].
  - rewrite has_interpolants_unfold.
    simpl; intros i Hi. rewrite ord_lt_unfold in Hi. destruct Hi as [[] _].
  - simpl.
    apply veblen_interpolants
      with (f:=VF_denote) (P:=VF_isNormal) (g:=ackermann_tower_fin (addOrd 1) n) (a:=a) (b:=VF_denote b) (vr:=Vnorm n); auto.
    + apply VF_has_cantor_decomposition.
    + clear Hnorm.
      induction n as [n Hindn] using (size_induction ω).
      destruct n; intros.
      { apply onePlus_interpolants with (zr:=Z) (pr:=VF_add (VF_succ Z)); auto.
        hnf; simpl; intuition auto with ord.
        hnf; intros.
        apply VF_add_reflects; auto with ord.
        destruct (VF_succ_reflects 0 Z); simpl; intuition auto with ord. }
      simpl.
      eapply enum_fix_has_interpolants with (enum_gr := Vnorm (S n) Z); auto with ord.
      * apply VF_has_cantor_decomposition.
      * intros.
        apply veblen_interpolants_first with (vr:= Vnorm n); auto with ord.
        ** apply VF_has_cantor_decomposition.
        ** intros. apply Hindn; simpl; auto with ord.
           intros.
           apply Hindx; auto.
           eapply ord_lt_le_trans ; [ apply H5 |].
           apply veblen_monotone_func; simpl; auto with ord.
           intros.
           rewrite enum_are_fixpoints; auto with ord.
           rewrite <- veblen_fax; auto with ord.
           apply ackermann_tower_fin_monotone; auto with ord.
           rewrite addOrd_zero_r.
           apply normal_inflationary; auto with ord.
        ** simpl; intuition.
           rewrite Vnorm_equal; auto with ord.
           *** simpl.
               destruct H4.
               destruct H6.
               split; apply veblen_monotone_full; auto with ord.
           *** apply Vnorm_normal; auto.
      * intros.
        apply normal_inflationary with (f:= fun x => veblen _ x 0); auto with ord.
      * hnf; simpl; intuition.
        ** rewrite Vnorm_equal; simpl; auto.
           rewrite veblen_zero.
           destruct H2.
           split; apply enum_fixpoints_monotone; auto with ord.
        ** apply Vnorm_normal; simpl; auto.
    + apply VF_ackermann_reflects.
    + simpl in *; intuition.
    + apply Hindx; simpl in *; intuition.
      apply (normal_subterm_shrink (V n a b)).
      simpl; intuition.
    + apply Hindx; simpl in *; intuition.
      apply (normal_subterm_shrink (V n a b)).
      simpl; intuition.
Qed.

Definition VF_nadd := cantor_nadd VF_has_cantor_decomposition.

Theorem VF_reflects_nadd: reflects VForm VF_denote VF_isNormal (ORD ==> ORD ==> ORD) naddOrd VF_nadd.
Proof.
  apply cantor_nadd_reflects.
  apply VF_has_all_interpolants.
Qed.

Theorem VF_below_SAO : forall x:VF, x < SmallAckermannOrdinal.
Proof.
  induction x; simpl.
  - unfold SmallAckermannOrdinal.
    rewrite <- (sup_le _ _ 0%nat).
    simpl.
    rewrite addOrd_zero_r.
    apply succ_lt.
  - apply veblen_collapse'; auto.
    + unfold SmallAckermannOrdinal.
      apply sup_complete; auto.
      hnf; intros.
      exists (Nat.max a1 a2).
      split; apply ackermann_tower_fin_monotone; auto with arith ord.
      left. exists 0%nat.
      simpl.
      rewrite addOrd_zero_r.
      apply succ_lt.
    + unfold SmallAckermannOrdinal.
      etransitivity.
      apply veblen_continuous_first; auto.
      apply sup_least; intro i.
      rewrite <- (sup_le _ _ (S (Nat.max i n))).
      unfold ackermann_tower_fin; fold ackermann_tower_fin.
      rewrite enum_are_fixpoints; auto with ord.
      transitivity (veblen (ackermann_tower_fin (addOrd 1) (Nat.max i n)) (ackermann_tower_fin (addOrd 1) i 0) 0).
      { apply veblen_monotone_func; auto with ord.
        intros. apply ackermann_tower_fin_monotone; auto with ord.
        auto with arith. }
        apply veblen_monotone_first; auto.
      apply ackermann_tower_fin_monotone with (m:=i) (n:=S (Nat.max i n)); auto with ord arith.
Qed.

Theorem VF_SAO : VF ≈ SmallAckermannOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. apply VF_below_SAO.
  - unfold SmallAckermannOrdinal.
    apply sup_least. intro i.
    transitivity (VF_denote (V i Z Z)).
    2: { apply index_le. }
    simpl.
    rewrite veblen_zero; auto with ord.
Qed.

From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VF_has_enough_notations (EM:excluded_middle) :
  forall x, x < SmallAckermannOrdinal -> exists v:VF, v ≈ x.
Proof.
  intros x H.
  rewrite <- VF_SAO in H.
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
