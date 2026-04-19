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
      ackermann_tower_normal
      ackermann_tower_monotone
  : core.

Inductive VForm : Set :=
| Z : VForm
| V : VForm -> VForm -> VForm -> VForm.

Fixpoint VF_size (x:VForm) : nat :=
  match x with
  | Z => O
  | V n x y => S (VF_size n + VF_size x + VF_size y)
  end.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | V n a x => veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x; auto with ord.
  apply veblen_complete; auto.
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
  VF_denote m < VF_denote n ->
  VF_denote a < VF_denote (V n b c) ->
  VF_denote (V m a (V n b c)) ≈ VF_denote (V n b c).
Proof.
  simpl VF_denote.
  intros.
  split. 2: { apply veblen_inflationary; auto. }
  apply veblen_collapse; auto with ord.
  destruct (VF_isZero b); subst; simpl.
  { rewrite veblen_zero at 2.
    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
    apply veblen_monotone_first; auto with ord.
    rewrite veblen_zero; auto with ord. }
  rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
  rewrite veblen_zero.
  rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
  apply veblen_monotone_first; auto with ord.
  apply normal_inflationary; auto with ord.
Qed.

Theorem Vmn_collapse2 : forall n m b c,
  VF_denote m < VF_denote n ->
  VF_denote (V m (V n b c) Z) ≈ VF_denote (V n b c).
Proof.
  intros. simpl. split.
  - destruct (VF_isZero b); subst; simpl.
    { rewrite veblen_zero at 2.
      rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
      apply veblen_monotone_first; auto with ord.
      rewrite veblen_zero; auto with ord. }
    rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
    rewrite veblen_zero.
    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
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
      match VF_compare m n with
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
  VF_compare m n = LT ->
  VF_compare (V m a x) (V n b y) =
  match VF_compare a (V n b y) with
  | LT => VF_compare x (V n b y)
  | EQ => if VF_isZero x then EQ else GT
  | GT => GT
  end.
Proof.
  intro H.
  simpl. rewrite H. auto.
Qed.

Lemma VF_compare_gt m n a x b y :
  VF_compare m n = GT ->
  VF_compare (V m a x) (V n b y) =
  match VF_compare (V m a x) b with
  | LT => LT
  | EQ => if VF_isZero y then EQ else LT
  | GT => VF_compare (V m a x) y
  end.
Proof.
  intro H. simpl. rewrite H.
  auto.
Qed.

Lemma VF_compare_correct :
  forall x y,
    match VF_compare x y with
    | LT => VF_denote x < VF_denote y
    | EQ => VF_denote x ≈ VF_denote y
    | GT => VF_denote x > VF_denote y
    end.
Proof.
  induction x as [|m Hm a Ha x Hx]; intros y.
  - destruct y as [|n b y].
    + simpl. reflexivity.
    + simpl. apply veblen_nonzero; auto.
  - induction y as [|n Hn b Hb y Hy].
    + simpl. apply veblen_nonzero; auto.
    + generalize (Hm n); intro Hmn.
      simpl. destruct (VF_compare m n).
      * generalize (Ha (V n b y)).
        destruct (VF_compare a (V n b y)); intros.
        ** generalize (Hx (V n b y)).
           destruct (VF_compare x (V n b y)); intros.
           *** simpl.
               apply veblen_collapse'; simpl; auto.
               destruct (VF_isZero b); subst; simpl.
               **** rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero; auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    apply normal_inflationary; auto with ord.
           *** simpl. split.
               apply veblen_collapse; auto.
               apply H0; simpl; intuition.
               2:{ simpl in H0. rewrite <- H0; simpl; auto. apply veblen_inflationary; auto with ord. }
               destruct (VF_isZero b); subst; simpl.
               **** rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero; auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
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
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    simpl in H.
                    rewrite veblen_zero in H.
                    apply H.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote b); auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote m); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite H.
                    apply normal_inflationary; auto with ord.
           *** apply ord_le_lt_trans with (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) 0).
               rewrite <- H.
               apply (normal_inflationary (fun i => veblen _ i 0)); auto.
               apply veblen_increasing; auto with ord.
        ** apply ord_lt_le_trans with (VF_denote a).
           apply H; simpl; auto.
           simpl.
           transitivity (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) 0).
           apply (normal_inflationary (fun i => veblen _ i 0)); auto.
           apply veblen_monotone; auto with ord.

      * generalize (Ha b); intro Hab.
        destruct (VF_compare a b).
        ** generalize (Hx (V n b y)); intro Hx2.
           destruct (VF_compare x (V n b y)).
           *** apply ord_le_lt_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               { apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               rewrite <- veblen_fixpoints with (α:=VF_denote a) (β:=VF_denote b); auto with ord.
               apply veblen_increasing; auto with ord.
           *** transitivity
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               { split; apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               rewrite <- veblen_fixpoints with (α:=VF_denote a) (β:=VF_denote b); auto with ord.
               split; apply veblen_monotone; auto with ord; apply Hx2.
           *** apply ord_lt_le_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               2:{ apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               apply ord_lt_le_trans with (VF_denote x); auto.
               apply normal_inflationary; auto with ord.
        ** generalize (Hx y).
           destruct (VF_compare x y); intuition.
           *** apply ord_le_lt_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               { apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               apply ord_le_lt_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote x)).
               { apply veblen_monotone_first; auto with ord.
                 apply Hab. }
               apply veblen_increasing; auto.
           *** transitivity
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               { split; apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               transitivity
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote x)).
               { split; apply veblen_monotone_first; auto with ord; apply Hab. }
               split; apply veblen_monotone; auto with ord; apply H.
           *** apply ord_lt_le_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               2:{ apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               apply ord_lt_le_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote x)).
               2:{ apply veblen_monotone_first; auto with ord; apply Hab. }
               apply veblen_increasing; auto with ord.
        ** change (match VF_compare (V m a x) y with
                   | LT =>
                       veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x) <
                         veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote y)
                   | EQ =>
                       veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x)
                         ≈ veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote y)
                   | GT =>
                       veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote y) <
                         veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x)
                   end).
           destruct (VF_compare (V m a x) y).
           *** apply ord_le_lt_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               { apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               rewrite <- veblen_fixpoints with (α:=VF_denote b) (β:=VF_denote a); auto with ord.
               apply veblen_increasing; auto with ord.
               eapply ord_le_lt_trans; [ | apply Hy].
               simpl.
               apply veblen_monotone_func; auto with ord.
               intros. apply ackermann_tower_monotone; auto with ord.
               apply Hmn.
           *** transitivity
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               { split; apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               rewrite <- veblen_fixpoints with (α:=VF_denote b) (β:=VF_denote a); auto with ord.
               apply veblen_eq_mor; auto with ord.
               transitivity
                 (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x)).
               { split; apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               apply Hy.
           *** apply ord_lt_le_trans with
                 (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote a) (VF_denote x)).
               2: { apply veblen_monotone_func; auto with ord.
                 intros. apply ackermann_tower_monotone; auto with ord.
                 apply Hmn. }
               rewrite <- veblen_fixpoints with (α:=VF_denote b) (β:=VF_denote a); auto with ord.
               apply veblen_increasing; auto.
               apply ord_lt_le_trans with (VF_denote (V m a x)); auto.
               simpl.
               apply veblen_monotone_func; auto with ord.
               intros. apply ackermann_tower_monotone; auto with ord.
               apply Hmn.

      * change (match
                  match (VF_compare (V m a x) b) with
                  | LT => LT
                  | EQ => if VF_isZero y then EQ else LT
                  | GT => VF_compare (V m a x) y
                  end
                 with
                     | LT =>
                         veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x) <
                           veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote y)
                 | EQ =>
                     veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x)
                       ≈ veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote y)
                 | GT =>
                     veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) (VF_denote y) <
                       veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x)
                 end).
        destruct (VF_compare (V m a x) b).
        ** apply ord_lt_le_trans with (VF_denote b).
           apply Hb.
           transitivity (veblen (ackermann_tower (addOrd 1) (VF_denote n)) (VF_denote b) 0).
           apply (normal_inflationary (fun i => veblen _ i 0)); auto.
           apply veblen_monotone; auto with ord.
        ** destruct (VF_isZero y); subst.
           *** transitivity (VF_denote (V n (V m a x) Z)).
               2: { simpl. split; apply veblen_monotone_first; auto with ord; apply Hb. }
               simpl; split.
               { apply normal_inflationary with (f:= fun i => veblen _ i 0); auto with ord. }
               destruct (VF_isZero a).
               **** subst; simpl.
                    rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero. auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote a) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    apply normal_inflationary; auto with ord.
           *** apply ord_le_lt_trans with (VF_denote (V n b Z)).
               2:{ simpl. apply veblen_increasing; auto. }
               simpl.
               transitivity (VF_denote (V n (V m a x) Z)); simpl.
               **** apply normal_inflationary with (f:= fun i => veblen _ i 0); auto with ord.
               **** apply veblen_monotone_first; auto with ord.
                    apply Hb.

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
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero.
                    auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote a) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    apply normal_inflationary; auto with ord.
           *** simpl.
               apply veblen_collapse'; auto.
               destruct (VF_isZero a); subst; simpl.
               **** rewrite veblen_zero at 2.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote n); auto with ord.
                    apply veblen_monotone_first; auto with ord.
                    rewrite veblen_zero.
                    auto with ord.
               **** rewrite <- veblen_fixpoints with (α:=0) (β:=VF_denote a) at 2; auto with ord.
                    rewrite veblen_zero.
                    rewrite <- ackermann_tower_fixpoint with (a':=VF_denote n); auto with ord.
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

Lemma VF_eq_correct x y:
  VF_compare x y = EQ <-> VF_denote x ≈ VF_denote y.
Proof.
  generalize (VF_compare_correct x y); intro Hxy; intuition.
  rewrite H in Hxy; auto.
  destruct (VF_compare x y); auto.
  elim (ord_lt_irreflexive (VF_denote x)).
  apply ord_lt_le_trans with (VF_denote y); auto. apply H.
  elim (ord_lt_irreflexive (VF_denote y)).
  apply ord_lt_le_trans with (VF_denote x); auto. apply H.
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
  | V m a b => VF_isNormal m /\
               VF_isNormal a /\
               VF_isNormal b /\
               match b with
               | Z =>
                 match a with
                 | Z => True
                 | V n _ _ => VF_denote m >= VF_denote n
                 end
               | V n x y =>
                 match VF_compare m n with
                 | LT => VF_denote a >= VF_denote b
                 | EQ => VF_denote a >= VF_denote x
                 | GT => True
                 end
               end
  end.

Lemma VF_isNormal_dec: forall x, { VF_isNormal x } + { ~VF_isNormal x }.
Proof.
  induction x; simpl; intros; auto.
  intuition; auto.
  destruct x3.
  - destruct x2; intuition.
    destruct (VF_decide_order x1 x2_1); intuition.
    right; intuition.
    elim (ord_lt_irreflexive (VF_denote x1)).
    apply ord_lt_le_trans with (VF_denote x2_1); auto.
  - generalize (VF_compare_correct x1 x3_1).
    destruct (VF_compare x1 x3_1); intuition.
    + destruct (VF_decide_order x2 (V x3_1 x3_2 x3_3)); intuition.
      right; intuition.
      elim (ord_lt_irreflexive (VF_denote x2)).
      eapply ord_lt_le_trans; eauto.
    + destruct (VF_decide_order x2 x3_2); intuition.
      right; intuition.
      elim (ord_lt_irreflexive (VF_denote x2)).
      eapply ord_lt_le_trans; eauto.
Qed.

Definition subterm_shrink x :=
  match x with
  | Z => True
  | V m a b => VF_denote m < VF_denote (V m a b) /\
               VF_denote a < VF_denote (V m a b) /\
               VF_denote b < VF_denote (V m a b)
  end.

Lemma shrink_lemma1: forall x,
    VF_denote x < ackermann_tower (addOrd 1) (VF_denote x) 0.
Proof.
  induction x; simpl; intuition auto with ord.
  apply veblen_collapse'; auto with ord.
  apply normal_complete; auto with ord.
  - eapply ord_lt_le_trans; [ apply IHx2 |].
    apply ackermann_tower_monotone; auto with ord.
    transitivity (VF_denote (V x1 x2 Z)).
    + simpl. apply normal_inflationary with (f:= fun i => veblen _ i 0); auto with ord.
    + simpl. apply veblen_monotone; auto with ord.
  - eapply ord_lt_le_trans; [ apply IHx3 |].
    apply ackermann_tower_monotone; auto with ord.
    apply normal_inflationary; auto with ord.
  - rewrite <- ackermann_tower_fixpoint with (a':=(VF_denote x1)) at 2; auto with ord.
    eapply ord_lt_le_trans; [ apply IHx1 |].
    transitivity (VF_denote (V x1 Z Z)).
    + simpl. rewrite veblen_zero. auto with ord.
    + simpl. apply veblen_monotone_full; auto with ord.
Qed.

Lemma normal_subterm_shrink : forall x, VF_isNormal x -> subterm_shrink x.
Proof.
  induction x; simpl; intuition.
  - apply ord_lt_le_trans with (VF_denote (V x1 Z Z)).
    + simpl. rewrite veblen_zero. apply shrink_lemma1.
    + simpl. apply veblen_monotone_full; auto with ord.
  - destruct x3.
    + destruct x2; simpl in *; intuition auto with ord.
      apply ord_le_lt_trans with (VF_denote (V x1 x2_2 x2_3)).
      { simpl. apply veblen_monotone_func; auto with ord. }
      rewrite <- veblen_fixpoints with (α:=VF_denote x2_2) (β:=veblen _ _ _); auto with ord.
      simpl. apply veblen_increasing; auto with ord.
      eapply ord_lt_le_trans; eauto.
      apply normal_inflationary with (f:= fun i => veblen _ i 0); auto with ord.
    + apply veblen_subterm1; simpl; auto with ord.

  - destruct x3; simpl in *; intuition auto with ord.
    + generalize (VF_compare_correct x1 x3_1).
      destruct (VF_compare x1 x3_1); intros; subst.
      * (* LT case *)
        rewrite H3 at 1.
        apply veblen_subterm1; auto with ord.
      * (* EQ case *)
        apply ord_le_lt_trans with (VF_denote (V x1 x3_2 x3_3)).
        ** simpl. apply veblen_monotone_func; auto with ord.
           intros. apply ackermann_tower_monotone; auto with ord.
           apply H9.
        ** apply veblen_increasing'; auto.
      * (* GT case *)
        apply veblen_collapse'; auto.
        eapply ord_lt_le_trans; [ apply H7 |].
        apply veblen_inflationary; auto.
        eapply ord_lt_le_trans; [ apply H10 |].
        apply veblen_inflationary; auto.

        destruct (VF_isZero x2).
        { subst; simpl.
          rewrite veblen_zero at 2.
          rewrite <- ackermann_tower_fixpoint with (a':=VF_denote x3_1); auto with ord.
          apply veblen_monotone_first; auto with ord.
          rewrite veblen_zero. auto with ord. }
        rewrite <- veblen_fixpoints with (α:=0) (β:= VF_denote x2) at 2; auto with ord.
        rewrite veblen_zero.
        rewrite <- ackermann_tower_fixpoint with (a':=VF_denote x3_1); auto with ord.
        apply veblen_monotone_first; auto with ord.
        apply normal_inflationary; auto with ord.
Qed.

Inductive redex : VForm -> VForm -> Prop:=
| redex_V : forall m n a b x,
    VF_compare m n = EQ ->
    VF_compare a b = LT ->
    redex (V m a (V n b x)) (V n b x)
| redex_Vmn1 : forall m n a b c,
    VF_compare m n = LT ->
    VF_compare a (V n b c) = LT ->
    redex (V m a (V n b c)) (V n b c)
| redex_Vmn2 : forall m n b c,
    VF_compare m n = LT ->
    redex (V m (V n b c) Z) (V n b c).

Lemma redex_sound: forall x y,
    redex x y ->
    VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. inversion H; subst.
  - rewrite VF_eq_correct in H0.
    transitivity (VF_denote (V n a (V n b x0))).
    + simpl; split; apply veblen_monotone_func; auto.
      intros; apply ackermann_tower_monotone; auto with ord.
      apply H0.
      intros; apply ackermann_tower_monotone; auto with ord.
      apply H0.
    + apply V_collapse; auto.
      apply VF_lt_correct; auto.
  - apply Vmn_collapse; auto.
    apply VF_lt_correct; auto.
    apply VF_lt_correct; auto.
  - apply Vmn_collapse2; auto.
    apply VF_lt_correct; auto.
Qed.

Inductive one_step_reduce: VForm -> VForm -> Prop :=
| reduce_redex: forall x y, redex x y -> one_step_reduce x y
| reduce_cong0: forall n n' x y, one_step_reduce n n' -> one_step_reduce (V n x y) (V n' x y)
| reduce_cong1: forall n x x' y, one_step_reduce x x' -> one_step_reduce (V n x y) (V n x' y)
| reduce_cong2: forall n x y y', one_step_reduce y y' -> one_step_reduce (V n x y) (V n x y').

Lemma one_step_reduce_sound: forall x y, one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H.
  - apply redex_sound; auto.
  - simpl. split; apply veblen_monotone_func; auto with ord.
    intros; apply ackermann_tower_monotone; auto with ord.
    apply IHone_step_reduce.
    intros; apply ackermann_tower_monotone; auto with ord.
    apply IHone_step_reduce.
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

Theorem normal_forms_unique :
  forall x y,
    VF_isNormal x ->
    VF_isNormal y ->
    VF_denote x ≈ VF_denote y ->
    x = y.
Proof.
  induction x as [|m Hm a Ha x Hx].
  - intros [|n b y]; simpl; intuition.
    elim (ord_lt_irreflexive 0).
    rewrite H1 at 2.
    apply veblen_nonzero; auto.
  - intros [|n b y]; simpl; intuition.
    + elim (ord_lt_irreflexive 0).
      rewrite <- H1 at 2.
      apply veblen_nonzero; auto.
    + assert (Hmn : m = n).
      { generalize (VF_compare_correct m n); auto.
        destruct (VF_compare m n); intros; auto.
        - exfalso.
          elim (ord_lt_irreflexive (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x))).
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
          elim (ord_lt_irreflexive (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x))).
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
        { elim (ord_lt_irreflexive (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (V_collapse m a b y).
          simpl.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; intuition.
          auto. }
        destruct (VF_decide_order b a).
        { elim (ord_lt_irreflexive (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x))).
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
      { elim (ord_lt_irreflexive (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x))).
        rewrite H1 at 2.
        apply veblen_increasing'; auto with ord. }
      destruct (VF_decide_order y x).
      { elim (ord_lt_irreflexive (veblen (ackermann_tower (addOrd 1) (VF_denote m)) (VF_denote a) (VF_denote x))).
        rewrite H1 at 1.
        apply veblen_increasing'; auto with ord. }
      split; auto.
Qed.

Fixpoint VF_onePlus (x:VForm) :=
  match x with
  | Z => V Z Z Z
  | V Z Z x' => V Z Z (VF_onePlus x')
  | _ => x
  end.

Lemma VF_onePlus_equal: forall x, VF_denote (VF_onePlus x) ≈ 1 + VF_denote x.
Proof.
  induction x; simpl.
  - rewrite veblen_zero.
    rewrite ackermann_tower_zero.
    auto with ord.
  - destruct x1.
    + destruct x2; simpl.
      * repeat rewrite veblen_zero.
        repeat rewrite ackermann_tower_zero.
        rewrite IHx3; auto with ord.
      * symmetry. apply onePlus_veblen; auto with ord.
    + destruct (VF_isZero x2); subst; simpl.
      * repeat rewrite veblen_zero.
        split; auto with ord.
        rewrite <- ackermann_tower_fixpoint with (a':=0) (a:=veblen _ _ _) at 2; auto with ord.
        rewrite <- veblen_fixpoints with (α:=0) (β:=ackermann_tower _ _ _); auto with ord.
        rewrite veblen_zero. rewrite ackermann_tower_zero.
        apply addOrd_monotone; auto with ord.
        apply normal_inflationary with (f:= fun i => veblen _ i 0); auto with ord.
        apply normal_complete; auto with ord.
        apply normal_complete; auto with ord.
        apply normal_nonzero; auto with ord.
      * rewrite onePlus_veblen; auto with ord.
Qed.

Lemma VF_compare_refl: forall x, VF_compare x x = EQ.
Proof.
  intro x.
  generalize (VF_compare_correct x x); intro.
  destruct (VF_compare x x); auto.
  elim (ord_lt_irreflexive (VF_denote x)); auto.
  elim (ord_lt_irreflexive (VF_denote x)); auto.
Qed.

Lemma VF_onePlus_normal : forall x, VF_isNormal x -> VF_isNormal (VF_onePlus x).
Proof.
  induction x; simpl; intuition.
  destruct x1.
  - destruct x2; simpl in *; intuition.
    destruct x3; simpl in *; intuition.
    + rewrite VF_compare_refl; auto with ord.
    + destruct x3_1; simpl in *; intuition.
      destruct x3_2; simpl in *; intuition.
  - destruct x3; simpl in *; intuition.
Qed.

Lemma one_step_cong_helper0 : forall n x y,
  (exists z, one_step_reduce n z) -> exists z, one_step_reduce (V n x y) z.
Proof.
  intros n x y [z H].
  exists (V z x y).
  apply reduce_cong0; auto.
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

Lemma multi_reduce_conj0: forall m m' x y ,
  clos_refl_trans VForm one_step_reduce m m' ->
  clos_refl_trans VForm one_step_reduce (V m x y) (V m' x y).
Proof.
  intros m m' x y H. induction H.
  - apply rt_step.
    apply reduce_cong0; auto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
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
      2:{ apply one_step_cong_helper0; auto. }
      destruct (VF_isNormal_dec x2).
      2:{ apply one_step_cong_helper1; auto. }
      destruct (VF_isNormal_dec x3).
      2:{ apply one_step_cong_helper2; auto. }
      intuition.
      destruct x3.
      * destruct x2; intuition.
        econstructor.
        apply reduce_redex.
        apply redex_Vmn2.
        rewrite VF_lt_correct; auto.
        destruct (VF_decide_order x1 x2_1); intuition.
      * generalize (VF_compare_correct x1 x3_1).
        destruct (VF_compare x1 x3_1); intuition.
        ** econstructor.
           apply reduce_redex.
           apply redex_Vmn1.
           rewrite VF_lt_correct; auto.
           generalize (VF_compare_correct x2 (V x3_1 x3_2 x3_3)); intro.
           destruct (VF_compare x2 (V x3_1 x3_2 x3_3)); auto with ord.
           elim H; apply H7.
           elim H. auto with ord.
        ** assert (x1 = x3_1).
           { apply normal_forms_unique; simpl in *; intuition auto with ord. }
           subst x1.
           eexists.
           apply reduce_redex.
           apply redex_V.
           rewrite VF_eq_correct; auto.
           rewrite VF_lt_correct.
           generalize (VF_compare_correct x2 x3_2); intro.
           destruct (VF_compare x2 x3_2); auto with ord.
           elim H; apply H7.
           elim H. auto with ord.
    + intros [y Hy] [Hx1 [Hx2 H]].
      inversion Hy; subst.
      * inversion H0; subst.
        ** rewrite H5 in H. destruct H.
           elim (ord_lt_irreflexive (VF_denote x2)).
           eapply ord_lt_le_trans; eauto.
           apply VF_lt_correct; auto.
        ** rewrite H5 in H.
           destruct H.
           elim (ord_lt_irreflexive (VF_denote x2)).
           eapply ord_lt_le_trans; eauto.
           apply VF_lt_correct; auto.
        ** destruct H.
           elim (ord_lt_irreflexive (VF_denote x1)).
           eapply ord_lt_le_trans; eauto.
           apply VF_lt_correct; auto.
      * revert Hx1.
        rewrite IHx1.
        eauto.
      * revert Hx2.
        rewrite IHx2.
        eauto.
      * destruct H. revert H.
        rewrite IHx3.
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
          match VF_compare m n with
          | LT => a
          | _ => V m a b
          end
      end
  | V n x y =>
        match VF_compare m n with
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
    + generalize (VF_compare_correct m a1); intro Hcomp.
      destruct (VF_compare m a1); try apply rt_refl.
      apply rt_step.
      apply reduce_redex.
      apply redex_Vmn2; auto.
      rewrite VF_lt_correct; auto.
  - generalize (VF_compare_correct m b1); intro Hcomp.
    destruct (VF_compare m b1); try apply rt_refl.
    + generalize (VF_compare_correct a (V b1 b2 b3)); auto with ord.
      destruct (VF_compare a (V b1 b2 b3)); intuition; try apply rt_refl.
      apply rt_step.
      apply reduce_redex.
      apply redex_Vmn1; auto.
      apply VF_lt_correct; auto.
      apply VF_lt_correct; auto.
    + generalize (VF_compare_correct a b2); intuition.
      destruct (VF_compare a b2); intuition; try apply rt_refl.
      apply rt_step.
      apply reduce_redex.
      apply redex_V; auto.
      apply VF_eq_correct; auto.
      apply VF_lt_correct; auto.
Qed.

Lemma Vnorm_normal m a b :
  VF_isNormal m ->
  VF_isNormal a ->
  VF_isNormal b ->
  VF_isNormal (Vnorm m a b).
Proof.
  intros Ha Hb. unfold Vnorm.
  destruct b.
  - destruct a; simpl; auto with ord.
    intros.
    generalize (VF_compare_correct m a1).
    destruct (VF_compare m a1); simpl in *; intuition auto with ord.
    apply H0.
  - simpl; intuition.
    generalize (VF_compare_correct m b1); simpl.
    destruct (VF_compare m b1).
    + generalize (VF_compare_correct a (V b1 b2 b3)).
      destruct (VF_compare a (V b1 b2 b3)); simpl.
      * intuition.
      * intuition.
        rewrite <- VF_lt_correct in H4.
        rewrite H4.
        apply H2.
      * intuition.
        rewrite <- VF_lt_correct in H4.
        rewrite H4.
        rewrite H2. auto with ord.
    + rewrite <- VF_eq_correct. intro.
      generalize (VF_compare_correct a b2).
      destruct (VF_compare a b2); simpl in *; intuition.
      rewrite H2. apply H4.
      rewrite H2; auto with ord.
    + simpl; intuition.
      generalize (VF_compare_correct m b1).
      destruct (VF_compare m b1); intuition.
      elim (ord_lt_irreflexive (VF_denote m)); eauto with ord.
      elim (ord_lt_irreflexive (VF_denote m)).
      eapply ord_le_lt_trans; [ apply H4 | apply H2].
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
  | V m a b => Vnorm (VF_normalize m) (VF_normalize a) (VF_normalize b)
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
  - apply rt_trans with (V (VF_normalize x1) x2 x3).
    { apply multi_reduce_conj0; auto. }
    apply rt_trans with (V (VF_normalize x1) (VF_normalize x2) x3).
    { apply multi_reduce_conj1; auto. }
    apply rt_trans with (V (VF_normalize x1) (VF_normalize x2) (VF_normalize x3)).
    { apply multi_reduce_conj2; auto. }
    apply Vnorm_reduce.
Qed.

Theorem VF_normalize_equal : forall x, VF_denote (VF_normalize x) ≈ VF_denote x.
Proof.
  intros. symmetry.
  apply step_reduce_sound; auto.
  apply VF_normalize_reduce.
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
    complete n ->
    complete x ->
    complete y ->
    n > 0 ->
    expOrd ω (veblen (ackermann_tower (addOrd 1) n) x y) ≈ veblen (ackermann_tower (addOrd 1) n) x y.
Proof.
  intros.
  split.
  - transitivity (veblen (addOrd 1) (veblen (ackermann_tower (addOrd 1) n) x y) 0).
    + rewrite veblen_onePlus; auto with ord.
    + destruct (complete_zeroDec x); auto.
      * transitivity (ackermann_tower (addOrd 1) n y).
        ** transitivity (veblen (ackermann_tower (addOrd 1) 0) (veblen (ackermann_tower (addOrd 1) n) x y) 0).
           *** apply veblen_monotone_func; auto with ord.
               intros. rewrite ackermann_tower_zero; auto with ord.
           *** rewrite <- ackermann_tower_fixpoint with (a' := 0); auto with ord.
               apply veblen_monotone_first; auto with ord.
               transitivity (veblen (ackermann_tower (addOrd 1) n) 0 y).
               apply veblen_monotone_first; auto with ord.
               rewrite veblen_zero; auto with ord.
        ** rewrite veblen_unroll.
           auto with ord.
      * rewrite <- veblen_fixpoints with (α:=0) (β:=x) at 2; auto with ord.
        rewrite veblen_zero.
        rewrite <- ackermann_tower_fixpoint with (a' := 0); auto with ord.
        transitivity (veblen (ackermann_tower (addOrd 1) 0) (veblen (ackermann_tower (addOrd 1) n) x y) 0).
        ** apply veblen_monotone_func; auto with ord.
           intros. rewrite ackermann_tower_zero; auto with ord.
        ** apply veblen_monotone_first; auto with ord.
           apply normal_inflationary; auto with ord.
  - apply normal_inflationary; auto.
Qed.

Fixpoint VF_decompose (x:VForm) : list VForm :=
  match x with
  | Z => []
  | V m a b =>
      match m with
      | Z => a :: VF_decompose b
      | _ => [x]
      end
  end.

Fixpoint VF_recompose (xs:list VForm) : VForm :=
  match xs with
  | [] => Z
  | [x] =>
      match x with
      | Z => V Z Z Z
      | V Z _ _ => V Z x Z
      | _ => x
      end
  | x::xs' => V Z x (VF_recompose xs')
  end.

Lemma VF_decompose_correct:
  forall x,
    VF_isNormal x ->
    each VF_isNormal (VF_decompose x) /\
    cantor_ordered VF_denote (VF_decompose x) /\
    VF_denote x ≈ cantor_denote VF_denote (VF_decompose x).
Proof.
  induction x; simpl; intuition auto with ord.
  destruct x1.
  simpl; auto.
  simpl in *; intuition.
  destruct x1; simpl; auto.
  split; auto.
  destruct x3; simpl; auto.
  destruct x3_1; simpl in *; auto.

  destruct x1.
  - simpl.
    transitivity (veblen (addOrd 1) (VF_denote x2) (VF_denote x3)).
    { split; apply veblen_monotone_func; auto with ord.
      intros. rewrite ackermann_tower_zero; auto with ord.
      intros. rewrite ackermann_tower_zero; auto with ord. }
    rewrite veblen_onePlus; auto with ord.
    rewrite H12. reflexivity.
  - simpl in *. rewrite addOrd_zero_r.
    symmetry. apply veblen_tower_epsilon; auto with ord.
Qed.

Lemma veblen_ack0 x y:
  complete x ->
  complete y ->
  veblen (ackermann_tower (addOrd 1) 0) x y ≈ expOrd ω x + y.
Proof.
  transitivity (veblen (addOrd 1) x y).
  - split; apply veblen_monotone_func; auto with ord.
    intros; rewrite ackermann_tower_zero; auto with ord.
    intros; rewrite ackermann_tower_zero; auto with ord.
  - rewrite veblen_onePlus; auto with ord.
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
  destruct a1; simpl; auto.

  simpl in *; intuition auto with ord.
  destruct xs; simpl in *; intuition.
  destruct v; simpl in *; intuition.
  destruct v1; simpl in *; intuition.
  destruct xs; simpl in *; intuition.
  destruct a; simpl in *; intuition.
  { rewrite veblen_ack0; auto with ord. }
  rewrite addOrd_zero_r.
  destruct a1; simpl.
  { rewrite (veblen_ack0 (veblen _ _ _) 0); auto with ord.
    rewrite addOrd_zero_r. auto with ord. }
  apply veblen_tower_epsilon; auto with ord.
  rewrite veblen_ack0; auto with ord.
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

Theorem VF_ackermann_reflects:
  reflects VForm VF_denote VF_isNormal
    (ORD ==> ORD ==> ORD ==> ORD)
    (fun n => veblen (ackermann_tower (addOrd 1) n))
    Vnorm.
Proof.
  hnf; intros m n [H1 H2].
  hnf; intros a b [H3 H4].
  hnf; intros x y [H5 H6].
  hnf. split.
  - rewrite Vnorm_equal; simpl; auto.
    destruct H1. destruct H3. destruct H5.
    split; apply veblen_monotone_full; auto with ord.
  - apply Vnorm_normal; auto.
Qed.

Lemma ackermann_tower_has_interpolants:
  forall n b,
    VF_isNormal n ->
    has_interpolants VF_denote VF_isNormal (VF_denote n) ->
    complete b ->
    has_interpolants VF_denote VF_isNormal b ->
    has_interpolants VF_denote VF_isNormal (ackermann_tower (addOrd 1) (VF_denote n) b).
Proof.
  induction n as [n Hindn] using (size_induction VF).
  induction b as [b Hindb] using ordinal_induction.
  intros Hn1 Hn2 Hb1 Hb2. rewrite has_interpolants_unfold. intros i Hi.
  rewrite ackermann_tower_unroll in Hi.
  apply lub_lt in Hi.
  destruct Hi as [Hi|Hi].
  - assert (has_interpolants VF_denote VF_isNormal (1 + b)).
    { apply onePlus_interpolants with Z (VF_add (V Z Z Z)); auto.
      simpl; intuition auto with ord.
      hnf; simpl; intros. apply VF_add_reflects; intuition.
      symmetry. simpl.
      rewrite veblen_zero.
      rewrite ackermann_tower_zero.
      rewrite addOrd_zero_r. auto with ord.
      simpl; intuition. }
    rewrite has_interpolants_unfold in H.
    destruct H with i as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
    exists y; intuition.
    rewrite ackermann_tower_unroll.
    rewrite <- lub_le1.
    auto.
  - apply sup_lt in Hi.
    destruct Hi as [j Hi].
    set (b' := limOrd (fun x : b => ackermann_tower (addOrd 1) (VF_denote n) x)).

    assert (Hb' : has_interpolants VF_denote VF_isNormal b').
    { unfold b'.
      rewrite has_interpolants_unfold.
      intros.
      rewrite ord_lt_unfold in H. simpl in H.
      destruct H as [z Hz].

      rewrite has_interpolants_unfold in Hb2.
      destruct (Hb2 z) as [z' [?[?[??]]]]; auto with ord.
      exists (Vnorm (VF_normalize n) Z z'); intuition.
      - apply Vnorm_normal; auto with ord.
        apply VF_normalize_isNormal.
        simpl; auto.
      - rewrite Vnorm_equal.
        simpl.
        rewrite Hz.
        rewrite veblen_zero.
        apply ackermann_tower_monotone; auto with ord.
        rewrite VF_normalize_equal; auto with ord.
        simpl; auto.
        auto.
      - rewrite Vnorm_equal.
        simpl.
        rewrite veblen_zero.
        rewrite ord_lt_unfold in H1.
        destruct H1 as [q ?].
        rewrite ord_lt_unfold. exists q. simpl.
        apply ackermann_tower_monotone; auto with ord.
        rewrite VF_normalize_equal; auto with ord.
        simpl; auto.
        auto.
      - rewrite Vnorm_equal; simpl; auto with ord.
        rewrite veblen_zero.
        assert (Heq: ackermann_tower (addOrd 1) (VF_denote (VF_normalize n)) (VF_denote z') ≈
                  ackermann_tower (addOrd 1) (VF_denote n) (VF_denote z')).
        { split; apply ackermann_tower_monotone; auto with ord.
          apply VF_normalize_equal.
          apply VF_normalize_equal. }
        rewrite Heq.
        apply Hindb; auto with ord.
    }

    assert (Hb'': complete b').
    { unfold b'. apply lim_complete.
      - intros; apply normal_complete; auto with ord.
      - apply directed_monotone; auto with ord.
      - destruct b; apply Hb1. }

    rewrite has_interpolants_unfold in Hn2.
    destruct (Hn2 j) as [q [?[?[??]]]]; auto with ord.

    assert (Hfix: has_interpolants VF_denote VF_isNormal
                    (fixOrd (fun d : Ord => veblen (ackermann_tower (addOrd 1) (VF_denote q)) d 0) b')).
    { apply fix_has_interpolants; auto with ord.
      - intros. eapply veblen_interpolants_first with (Vnorm q); eauto with ord.
        + apply VF_has_cantor_decomposition.
        + hnf; simpl; intros.
          generalize (VF_ackermann_reflects (VF_denote q) q).
          intros. apply H7; intuition auto with ord. }

    rewrite has_interpolants_unfold in Hfix.
    destruct (Hfix i) as [k [?[?[??]]]]; auto with ord.
    + eapply ord_lt_le_trans; [ apply Hi |]. fold b'.
      apply fixOrd_monotone_func.
      intros. apply veblen_monotone_full; auto with ord.
      intros. apply veblen_monotone_full; auto with ord.
    + exists k; intuition.
      eapply ord_lt_le_trans; [ apply H5 |].
      rewrite ackermann_tower_unroll.
      rewrite <- lub_le2.
      rewrite ord_lt_unfold in H1.
      destruct H1 as [z ?].
      rewrite <- (sup_le _ _ z).
      fold b'.
      apply fixOrd_monotone_func.
      intros. apply veblen_monotone_full; auto with ord.
      intros. apply veblen_monotone_full; auto with ord.
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
      with (f:=VF_denote) (P:=VF_isNormal) (g:=ackermann_tower (addOrd 1) (VF_denote n)) (a:= a) (b:=VF_denote b) (vr:=Vnorm n); auto.
    + apply VF_has_cantor_decomposition.
    + simpl in Hnorm. intuition.
      apply ackermann_tower_has_interpolants; auto with ord.
      apply Hindx; auto.
      apply (normal_subterm_shrink (V n a b)); simpl; auto.
    + generalize VF_ackermann_reflects.
      intros. hnf; simpl; intros.
      hnf in H. simpl in *.
      apply H; auto.
      intuition auto with ord.
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

Lemma LAO_complete: complete LargeAckermannOrdinal.
Proof.
  unfold LargeAckermannOrdinal.
  apply normal_fix_complete; auto with ord.
  intros. apply normal_inflationary with (f:=fun i => ackermann_tower _ i 0); auto.
  apply ackermann_tower_normal_first; auto with ord.
Qed.

Theorem VF_below_LAO : forall x:VF, x < LargeAckermannOrdinal.
Proof.
  induction x; simpl.
  - unfold LargeAckermannOrdinal.
    rewrite normal_fixpoint; auto with ord.
    apply ackermann_tower_nonzero; auto with ord.
  - apply veblen_collapse'; auto with ord.
    apply LAO_complete.
    unfold LargeAckermannOrdinal.
    rewrite normal_fixpoint at 2; auto with ord.
    rewrite <- ackermann_tower_fixpoint with (a' := sz x1); auto with ord.
    apply veblen_monotone_first; auto with ord.
    apply normal_fixpoint; auto with ord.
    apply LAO_complete.
Qed.

Lemma VF_is_complete: complete VF.
Proof.
  simpl; intuition.
  - hnf; simpl; intros.
    destruct (VF_decide_order a1 a2).
    + exists a2. split; auto with ord.
    + exists a1; split; auto with ord.
  - left. constructor. exact Z.
Qed.

Theorem VF_LAO : VF ≈ LargeAckermannOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. apply VF_below_LAO.
  - unfold LargeAckermannOrdinal.
    apply normal_fix_least; auto with ord.
    { apply VF_is_complete. }
    rewrite normal_ord_decompose with (f:=fun i => ackermann_tower _ i 0); auto with ord.
    + apply sup_least; intro x.
      apply ord_lt_le.
      rewrite ord_lt_unfold.
      exists (V (VF_succ (VF_normalize x)) Z Z).
      simpl. rewrite veblen_zero.
      apply ackermann_tower_monotone; auto with ord.
      apply VF_succ_reflects; simpl.
      split.
      symmetry. apply VF_normalize_equal.
      apply VF_normalize_isNormal.
    + apply VF_is_complete.
    + rewrite ord_lt_unfold.
      exists Z.
      simpl. auto with ord.
Qed.

From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VF_has_enough_notations (EM:excluded_middle) :
  forall x, x < LargeAckermannOrdinal -> exists v:VF, v ≈ x.
Proof.
  intros x H.
  rewrite <- VF_LAO in H.
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
