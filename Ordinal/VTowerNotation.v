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

Open Scope ord_scope.

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

Inductive VForm : Set :=
| F : nat -> VForm
| V : nat -> VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | F n => natOrdSize n
  | V n a x => veblen (vtower_fin n) (1+VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x; simpl; auto.
Qed.

Local Hint Resolve VF_complete : core.

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
  split.
  2: { apply veblen_inflationary; auto. }
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal n) 0 (1+VF_denote b) (VF_denote c)) at 2; auto.
  rewrite veblen_zero.
  destruct n. inversion H.
  assert (m <= n)%nat by lia.
  simpl vtower_fin at 3.
  rewrite onePlus_veblen; auto.
  simpl in H0.
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal n) (1+VF_denote a) _ 0); auto.
  transitivity
    (veblen (vtower_fin n) (1+VF_denote a)
            (veblen (vtower_fin (S n)) (1+VF_denote b) (VF_denote c))).
  { apply veblen_monotone_func; auto.
    apply vtower_fin_index_monotone; auto. }

  apply veblen_monotone; auto.
  simpl.
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal (S n)) 0 (1+VF_denote b) (VF_denote c)) at 1; auto.
  rewrite veblen_zero.
  simpl.
  rewrite onePlus_veblen; auto.
  reflexivity.
  rewrite <- onePlus_veblen; auto.
Qed.

Theorem Vmn_collapse2 : forall n m b c,
  (m < n)%nat ->
  VF_denote (V m (V n b c) (F 0)) ≈ VF_denote (V n b c).
Proof.
  intros. simpl. split.
  - rewrite <- (veblen_fixpoints _ (vtower_fin_normal n) 0) at 2; auto.
    rewrite veblen_zero.
    destruct n. lia.
    simpl.
    apply veblen_monotone_func; auto.
    apply vtower_fin_index_monotone. lia.
    apply addOrd_complete; auto.
  - rewrite onePlus_veblen; auto.
    apply (normal_inflationary (fun x => veblen (vtower_fin m) x 0)); auto.
Qed.

Definition VF_isZero x : { x = F 0 } + { 0 < VF_denote x }.
Proof.
  destruct x. destruct n; auto.
  right; simpl. apply succ_trans; auto with ord.
  right; simpl. apply veblen_nonzero; auto.
Qed.

Fixpoint VF_compare (x:VForm) : VForm -> ordering :=
  fix inner (y:VForm) : ordering :=
    match x, y with
    | F m, F n     => nat_compare m n
    | F _, V _ _ _ => LT
    | V _ _ _, F _ => GT

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
  | F _ => True
  | V m a b => VF_isNormal a /\
               VF_isNormal b /\

               match b with
               | F 0 =>
                 match a with
                 | F _ => True
                 | V n _ _ => (m >= n)%nat
                 end
               | F _ => True

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
  | F _ => True
  | V m a b => VF_denote a < VF_denote (V m a b) /\
               VF_denote b < VF_denote (V m a b)
  end.

Lemma normal_subterm_shrink : forall x, VF_isNormal x -> subterm_shrink x.
Proof.
  induction x; simpl; intuition.
  - destruct x2.
    + destruct n0; simpl in *; intuition.
      * destruct x1; simpl; auto.
        ** apply finite_veblen_lt; auto.
        ** rewrite onePlus_veblen; auto.
           apply ord_le_lt_trans with
               (veblen (vtower_fin n) (1+VF_denote x1_1) (VF_denote x1_2)).
           apply veblen_monotone_func; auto.
           apply vtower_fin_index_monotone; auto.
           apply veblen_subterm1_zero_nest; simpl in *; intuition.
           rewrite <- onePlus_veblen; auto.
      * destruct x1; simpl; auto.
        ** apply finite_veblen_lt; auto.
        ** rewrite onePlus_veblen; auto.
           apply veblen_subterm1; auto with ord.
    + simpl; apply veblen_subterm1; auto with ord.
      apply veblen_nonzero; auto.
      apply addOrd_le2.
  - destruct x2; simpl in *; intuition.
    + apply finite_veblen_lt; auto.
    + generalize (nat_compare_correct n n0).
      destruct (nat_compare n n0); intros; subst.
      * (* LT case *)
        rewrite H2 at 1.
        apply veblen_subterm1; auto.
        apply veblen_nonzero; auto.
        apply addOrd_le2.
      * (* EQ case *)
        apply veblen_increasing'; auto.
      * (* GT case *)
        apply veblen_collapse'; auto.
        rewrite <- onePlus_veblen; auto. apply addOrd_increasing; auto.
        eapply ord_lt_le_trans; [ apply H |].
        apply veblen_inflationary; auto.
        eapply ord_lt_le_trans; [ apply H6 |].
        apply veblen_inflationary; auto.
        apply vtower_fin_fixpoints; auto.
Qed.

Lemma VF_compare_correct :
  forall x y,
    match VF_compare x y with
    | LT => VF_denote x < VF_denote y
    | EQ => VF_denote x ≈ VF_denote y
    | GT => VF_denote x > VF_denote y
    end.
Proof.
  induction x as [i|m a Ha x Hx].
  - intros [j|n b y].
    + simpl.
      generalize (nat_compare_correct i j).
      destruct (nat_compare i j); intros; subst; auto with ord.
      apply natOrdSize_increasing; auto.
      apply natOrdSize_increasing; auto.
    + simpl. apply finite_veblen_lt; auto.
  - induction y as [j|n b Hb y Hy].
    + simpl. apply finite_veblen_lt; auto.
    + generalize (nat_compare_correct m n).
      destruct (nat_compare m n); intro Hmn.
      * rewrite VF_compare_lt; auto.
        generalize (Ha (V n b y)).
        destruct (VF_compare a (V n b y)); intros.
        ** generalize (Hx (V n b y)).
           destruct (VF_compare x (V n b y)); intros.
           *** simpl.
               apply veblen_collapse'; auto.
               rewrite <- onePlus_veblen; auto.
               apply vtower_fin_fixpoints; auto.
           *** simpl. split.
               { apply veblen_collapse; auto.
                 rewrite <- onePlus_veblen; auto.
                 apply H0.
                 apply vtower_fin_fixpoints; auto. }
               { simpl in H0. rewrite <- H0; simpl; auto. apply veblen_inflationary; auto. }
           *** simpl.
               simpl in H0.
               eapply ord_lt_le_trans; [ apply H0; simpl; auto |].
               apply veblen_inflationary; auto.
        ** destruct (VF_isZero x); subst; simpl.
           rewrite (vtower_fin_fixpoints n m); auto.
           split; apply veblen_monotone_first; auto.
           rewrite <- onePlus_veblen; auto.
           apply addOrd_monotone; auto with ord; apply H.
           rewrite <- onePlus_veblen; auto.
           rewrite H. simpl. reflexivity.

           rewrite (vtower_fin_fixpoints n m); auto.
           apply veblen_increasing'; auto.
           rewrite <- onePlus_veblen; auto.
           apply addOrd_monotone; auto with ord; apply H.
        ** apply ord_lt_le_trans with (VF_denote a); auto.
           simpl.
           transitivity (veblen (vtower_fin m) (1+VF_denote a) 0).
           apply (normal_inflationary (fun i => veblen (vtower_fin m) (1+i) 0)); auto.
           apply veblen_monotone; auto with ord.

      * subst n.
        rewrite VF_compare_eq.
        simpl; apply veblen_compare_correct; auto.
        ** generalize (Ha b).
           destruct (VF_compare a b); simpl; auto with ord.
           intro H; rewrite H; auto with ord.
        ** apply Hx.
        ** apply Hx.

      * rewrite VF_compare_gt; auto.
        destruct (VF_compare (V m a x) b); intros.
        ** apply ord_lt_le_trans with (VF_denote b); auto.
           simpl.
           transitivity (veblen (vtower_fin n) (1+VF_denote b) 0).
           apply (normal_inflationary (fun i => veblen (vtower_fin n) (1+i) 0)); auto.
           apply veblen_monotone; auto with ord.
        ** destruct (VF_isZero y); subst; simpl.
           rewrite (vtower_fin_fixpoints m n); auto.
           rewrite <- Hb. simpl.
           rewrite onePlus_veblen; auto.
           reflexivity.
           rewrite (vtower_fin_fixpoints m n); auto.
           apply veblen_increasing'; auto.
           rewrite <- Hb.
           rewrite <- onePlus_veblen; auto.
           reflexivity.
        ** destruct (VF_compare (V m a x) y); intros.
           *** apply ord_lt_le_trans with (VF_denote y); auto.
               simpl.
               apply normal_inflationary; auto.
           *** split.
               { rewrite Hy. simpl. apply normal_inflationary; auto. }
               simpl. apply veblen_collapse; auto.
               rewrite <- onePlus_veblen; auto.
               apply Hy.
               apply (vtower_fin_fixpoints m n); auto.
           *** simpl.
               apply veblen_collapse'; auto.
               rewrite <- onePlus_veblen; auto.
               apply vtower_fin_fixpoints; auto.
Qed.

Global Opaque VF_compare.

Theorem VF_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y); intro H; auto.
  right. apply H.
  right. auto with ord.
Qed.

Definition Vnorm m a b :=
  match b with
  | F 0 => match a with
         | F _ => V m a b
         | V o _ _ => match nat_compare m o with
                      | LT => a
                      | _  => V m a b
                      end
         end

  | F _ => V m a b

  | V n x y => match nat_compare m n with
               | LT => match VF_compare a b with
                       | LT => b
                       | _  => V m a b
                       end
               | EQ => match VF_compare a x with
                       | LT => b
                       | _  => V m a b
                       end
               | GT =>  V m a b
               end
  end.

Fixpoint VF_normalize x :=
  match x with
  | F _     => x
  | V m a b => Vnorm m (VF_normalize a) (VF_normalize b)
  end.

Lemma Vnorm_normal m a b :
  VF_isNormal a ->
  VF_isNormal b ->
  VF_isNormal (Vnorm m a b).
Proof.
  unfold Vnorm; intros.
  destruct b; simpl.
  destruct n; simpl.
  - destruct a; simpl; auto.
    generalize (nat_compare_correct m n); intro.
    destruct (nat_compare m n); simpl in *; subst; intuition.
  - intuition.
  - generalize (nat_compare_correct m n); intro.
    destruct (nat_compare m n); simpl in *; subst; intuition.
    + generalize (VF_compare_correct a (V n b1 b2)).
      destruct (VF_compare a (V n b1 b2)); simpl in *; intuition.
      * generalize (nat_compare_correct m n).
        destruct (nat_compare m n); intuition; try lia.
        apply H3.
      * generalize (nat_compare_correct m n).
        destruct (nat_compare m n); intuition; try lia.
    + generalize (VF_compare_correct a b1).
      destruct (VF_compare a b1); simpl; intuition.
      * generalize (nat_compare_correct n n).
        destruct (nat_compare n n); intuition; try lia.
        apply H2.
      * generalize (nat_compare_correct n n).
        destruct (nat_compare n n); intuition; try lia.
    + generalize (nat_compare_correct m n).
      destruct (nat_compare m n); intuition; try lia.
Qed.

Lemma Vnorm_equal m a b :
  VF_denote (Vnorm m a b) ≈ VF_denote (V m a b).
Proof.
  unfold Vnorm; intros.
  destruct b; simpl.
  destruct n; simpl.
  - destruct a; simpl; auto with ord.
    generalize (nat_compare_correct m n).
    destruct (nat_compare m n); simpl; intuition.
    rewrite onePlus_veblen; auto.
    apply vtower_fin_fixpoints; auto.
  - reflexivity.
  - generalize (nat_compare_correct m n).
    destruct (nat_compare m n); intuition.
    + generalize (VF_compare_correct a (V n b1 b2)).
      destruct (VF_compare a (V n b1 b2)); simpl in *; intuition.
      * split. { apply veblen_inflationary; auto. }
        apply veblen_collapse; auto with ord.
        rewrite <- onePlus_veblen; auto.
        apply vtower_fin_fixpoints; auto.
    + subst m.
      generalize (VF_compare_correct a b1).
      destruct (VF_compare a b1); simpl; intuition.
      split. { apply veblen_inflationary; auto. }
      apply veblen_fixpoints; auto.
Qed.

Theorem VF_normalize_isNormal : forall x, VF_isNormal (VF_normalize x).
Proof.
  induction x; simpl; auto.
  apply Vnorm_normal; auto.
Qed.

Theorem VF_normalize_equal : forall x, VF_denote (VF_normalize x) ≈ VF_denote x.
Proof.
  induction x; simpl; auto with ord.
  rewrite Vnorm_equal; simpl; auto.
  apply veblen_eq_mor; auto.
  apply addOrd_eq_mor; auto with ord.
Qed.

Theorem normal_forms_unique :
  forall x y,
    VF_isNormal x ->
    VF_isNormal y ->
    VF_denote x ≈ VF_denote y ->
    x = y.
Proof.
  induction x as [i|m a Ha x Hx].
  - intros [j|n b y]; simpl; intuition.
    f_equal. apply natOrdSize_unique; auto.
    elim (ord_lt_irreflexive (natOrdSize i)).
    rewrite H1 at 2.
    apply finite_veblen_lt; auto.
  - intros [j|n b y]; simpl; intuition.
    + elim (ord_lt_irreflexive (natOrdSize j)).
      rewrite <- H1 at 2.
      apply finite_veblen_lt; auto.
    + assert (Hmn : m = n).
      { generalize (nat_compare_correct m n).
        destruct (nat_compare m n); intros; auto.
        - exfalso.
          elim (ord_lt_irreflexive (veblen (vtower_fin m) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite (vtower_fin_fixpoints n m); auto.
          apply veblen_subterm1_zero_nest; auto.
          rewrite <- H1.
          rewrite <- onePlus_veblen; auto.
          apply addOrd_increasing.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
        - elim (ord_lt_irreflexive (veblen (vtower_fin m) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite (vtower_fin_fixpoints m n); auto.
          apply veblen_subterm1_zero_nest; auto.
          rewrite H1.
          rewrite <- onePlus_veblen; auto.
          apply addOrd_increasing.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
      }
      subst n.
      assert (a = b).
      { apply Ha; auto.
        destruct (VF_decide_order a b).
        { elim (ord_lt_irreflexive (veblen (vtower_fin m) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ (vtower_fin_normal m) (1+VF_denote a) (1+VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; intuition. }
        destruct (VF_decide_order b a).
        { elim (ord_lt_irreflexive (veblen (vtower_fin m) (1+VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (veblen_fixpoints _ (vtower_fin_normal m) (1+VF_denote b) (1+VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V m b y)); simpl; intuition. }
        split; auto. }
      subst b.
      f_equal.
      apply Hx; auto.
      destruct (VF_decide_order x y).
      { elim (ord_lt_irreflexive (veblen (vtower_fin m) (1+VF_denote a) (VF_denote x))).
        rewrite H1 at 2.
        apply veblen_increasing'; auto with ord. }
      destruct (VF_decide_order y x).
      { elim (ord_lt_irreflexive (veblen (vtower_fin m) (1+VF_denote a) (VF_denote x))).
        rewrite H1 at 1.
        apply veblen_increasing'; auto with ord. }
      split; auto.
Qed.


Lemma SVO_complete : complete SmallVeblenOrdinal.
Proof.
 unfold SmallVeblenOrdinal.
 apply sup_complete; auto.
 hnf; intros.
 exists (Nat.max a1 a2).
 split; apply vtower_fin_index_monotone; auto with arith.
 left. exists 0%nat.
 simpl. auto.
Qed.

Lemma SVO_veblen_tower_closed n :
  veblen (vtower_fin n) SmallVeblenOrdinal 0 ≤ SmallVeblenOrdinal.
Proof.
  unfold SmallVeblenOrdinal.
  etransitivity.
  apply veblen_continuous_first; auto.
  apply sup_least; intro i.
  rewrite <- (sup_le _ _ (S (S (Nat.max i n)))).
  rewrite vtower_fin_succ.
  rewrite addOrd_zero_r.
  rewrite veblen_succ; auto.
  rewrite enum_are_fixpoints; auto.
  rewrite veblen_zero.
  transitivity (veblen (vtower_fin (Nat.max i n)) (vtower_fin i 0) 0).
  apply veblen_monotone_func; auto.
  apply vtower_fin_index_monotone; auto with arith.
  apply veblen_monotone_first; auto.
  rewrite enum_are_fixpoints; auto.
  rewrite veblen_zero.
  rewrite vtower_fin_succ.
  rewrite onePlus_veblen; auto.
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal _) 0); auto.
  rewrite veblen_zero.
  transitivity (vtower_fin (Nat.max i n) 0).
  apply vtower_fin_index_monotone; auto with arith.
  apply normal_monotone; auto with ord.
  apply addOrd_complete; auto.
  apply enum_fixpoints_complete; auto.
  intros. apply veblen_inflationary; auto.
  apply addOrd_complete; auto.
  apply enum_fixpoints_complete; auto.
  intros. apply veblen_inflationary; auto.
Qed.


Theorem VF_below_SVO : forall x:VF, x < SmallVeblenOrdinal.
Proof.
  induction x; simpl.
  - unfold SmallVeblenOrdinal.
    rewrite <- (sup_le _ _ 1%nat).
    simpl.
    rewrite veblen_onePlus; auto.
    do 2 rewrite addOrd_zero_r.
    rewrite expOrd_one'; auto with ord.
    apply omega_gt0.
  - apply veblen_collapse'; auto.
    apply SVO_complete.
    rewrite <- (SVO_veblen_tower_closed 0%nat).
    rewrite <- onePlus_veblen; auto.
    apply addOrd_increasing; auto.
    apply ord_lt_le_trans with SmallVeblenOrdinal; auto.
    apply (normal_inflationary (fun i => veblen (vtower_fin 0) i 0)); auto.
    apply SVO_complete.
    rewrite <- (SVO_veblen_tower_closed 0%nat); auto.
    apply veblen_nonzero; auto.
    apply SVO_complete.
    apply SVO_veblen_tower_closed.
Qed.

Theorem VF_SVO : VF ≈ SmallVeblenOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. apply VF_below_SVO.
  - unfold SmallVeblenOrdinal.
    apply sup_least. intro i.
    transitivity (VF_denote (V i (F 0) (F 0))).
    2: { apply index_le. }
    simpl.
    rewrite <- (veblen_fixpoints _ (vtower_fin_normal i) 0); auto with ord.
    rewrite veblen_zero.
    auto with ord.
Qed.

Fixpoint VF_add (x y:VForm) : VForm :=
  match x with
  | F m  => match y with
            | F n => F (n+m)
            | _   => y
            end
  | V 0 a x' => V 0 a (VF_add x' y)
  | _        => V 0 x y
  end.

Lemma VF_add_correct x y : VF_denote (VF_add x y) ≈ VF_denote x + VF_denote y.
Proof.
  induction x; simpl.
  - destruct y; simpl.
    rewrite natOrdSize_add. reflexivity.
    symmetry. apply finite_veblen; auto.
  - destruct n; simpl.
    + rewrite IHx2.
      rewrite veblen_onePlus; auto.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_assoc. reflexivity.
    + repeat (rewrite onePlus_veblen; auto).
      rewrite veblen_onePlus; auto.
      apply addOrd_eq_mor; auto with ord.
      split.
      rewrite <- (veblen_fixpoints _ (vtower_fin_normal (S n)) 0) at 2; auto.
      rewrite veblen_zero.
      simpl.
      rewrite onePlus_veblen; auto.
      transitivity
        (veblen (vtower_fin 0)
                (veblen (fun x : Ord => veblen (vtower_fin n) (1 + x) 0)
                        (1 + VF_denote x1) (VF_denote x2)) 0).
      simpl. rewrite veblen_onePlus; auto with ord.
      rewrite addOrd_zero_r. reflexivity.
      apply veblen_monotone_func; auto.
      intros; apply vtower_fin_index_monotone; auto with arith.
      apply normal_inflationary; auto.
Qed.


Definition VF_one := F 1.
Definition VF_succ x := VF_add x (F 1).
Definition VF_expOmega x :=
  match x with
  | F 0 => F 1
  | F (S n) => V 0 (F n) (F 0)
  | _ => V 0 x (F 0)
  end.
Definition VF_epsilon x  := V 1 (F 0) x.
Definition VF_Gamma x    := V 2 (F 0) x.

Lemma VF_one_correct : VF_denote VF_one ≈ 1.
Proof.
  simpl. auto with ord.
Qed.

Lemma VF_succ_correct x : VF_denote (VF_succ x) ≈ succOrd (VF_denote x).
Proof.
  unfold VF_succ.
  rewrite VF_add_correct.
  rewrite VF_one_correct.
  rewrite addOrd_succ.
  apply succ_congruence.
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
Qed.

(* VF_mul_single x e = x * ω^(1+e) *)
Definition VF_mul_single (x:VForm) (e:VForm) : VForm :=
  match x with
  (* 0 * ωᵉ = 0 *)
  | F O => F O
  | F (S m) => V 0 e (F 0)
  (* (ωᵃ + q) * ωᵉ = ω^(a + e) otherwise *)
  | V 0 a _ => V 0 (VF_add a (VF_onePlus e)) (F 0)
  | _       => V 0 (VF_add x (VF_onePlus e)) (F 0)
  end.

Lemma VF_isNormal_dominates : forall (b a:VF),
    match b with
    | V 0 b1 _ => VF_denote a >= VF_denote b1
    | V _ _ _  => VF_denote a >= VF_denote b
    | F _ => True
    end ->
    VF_isNormal b ->
    exists n:ω, expOrd ω (1+a) * n ≥ b.
Proof.
  induction b as [n|i b1 Hb1 b2 Hb2]; simpl; intuition.
  - exists 1%nat. simpl.
    rewrite mulOrd_one_r.
    transitivity (expOrd ω 1).
    rewrite expOrd_one'; auto.
    apply index_le.
    apply omega_gt0.
    apply expOrd_monotone.
    apply addOrd_le1.
  - destruct (Hb2 a) as [n Hn]; intuition.
    { destruct b2; simpl in *; intuition.
      generalize (nat_compare_correct i n).
      destruct (nat_compare i n); intros; subst; auto; try lia.
      destruct n. lia.
      rewrite H3.
      destruct i; auto.
      rewrite <- H.
      apply ord_lt_le.
      apply veblen_subterm1; auto.
      apply veblen_nonzero; auto.
      apply addOrd_le2.
      destruct n; auto.
      rewrite H3; auto.
      rewrite <- H.
      apply veblen_inflationary; auto.
      destruct i. lia.
      destruct n.
      rewrite <- H.
      transitivity (veblen (vtower_fin 0) (1 + VF_denote b2_1) (VF_denote b2_2)).
      transitivity (veblen (vtower_fin 0) (1 + VF_denote b2_1) 0).
      apply (normal_inflationary (fun i => veblen (vtower_fin 0) (1+i) 0)); auto.
      apply veblen_monotone; auto with ord.
      apply veblen_inflationary; auto.
      rewrite <- H.
      apply veblen_inflationary; auto. }

    exists (n+1)%nat.
    rewrite natOrdSize_add.
    rewrite ordDistrib_left.
    simpl.
    rewrite mulOrd_one_r.
    destruct i.
    + simpl.
      rewrite veblen_onePlus; auto.
      apply addOrd_monotone; auto.
    + rewrite H.
      rewrite <- addOrd_le1.
      apply (normal_inflationary (fun i => expOrd ω (1+i))); auto.
      apply compose_normal; auto.
Qed.

Lemma VF_mul_single_correct : forall x e,
    VF_isNormal x ->
    VF_denote (VF_mul_single x e) ≈ VF_denote x * expOrd ω (1+VF_denote e).
Proof.
  unfold VF_mul_single. intros.
  destruct x as [n|i x1 x2]; simpl.
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
  + destruct i.
    * simpl.
      rewrite VF_add_correct.
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
      destruct x2; simpl in *; intuition.
      destruct n; simpl; intuition.
      simpl in *; intuition.
      apply expOrd_omega_collapse with n; auto.
    * simpl.
      rewrite onePlus_veblen; auto.
      rewrite onePlus_veblen; auto.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite veblen_onePlus; auto.
      rewrite expOrd_add.
      apply mulOrd_eq_mor; auto with ord.
      symmetry.
      rewrite (vtower_fin_fixpoints (S i) 0) at 1; auto with arith.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      apply expOrd_eq_mor; auto with ord.
      rewrite (vtower_fin_fixpoints (S i) 0) at 1; auto with arith.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      reflexivity.
      rewrite VF_onePlus_correct.
      reflexivity.
      apply veblen_complete; auto.
      apply addOrd_complete; auto.
Qed.

Definition VF_mul x : VForm -> VForm :=
  let x' := VF_normalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | F n      => Nat.iter n (fun a => VF_add a x') (F 0)
  | V 0 b y' => VF_add (VF_mul_single x' b) (loop y')
  | _        => VF_mul_single x' y
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
  - destruct n.
    + rewrite VF_add_correct.
      rewrite VF_mul_single_correct.
      rewrite IHy2.
      rewrite veblen_onePlus; auto.
      rewrite ordDistrib_left.
      apply addOrd_eq_mor; auto with ord.
      apply mulOrd_eq_mor; auto with ord.
      apply VF_normalize_equal.
      apply VF_normalize_isNormal.
    + rewrite VF_mul_single_correct.
      simpl.
      rewrite onePlus_veblen; auto.
      apply mulOrd_eq_mor.
      apply VF_normalize_equal.
      symmetry.
      rewrite (vtower_fin_fixpoints (S n) 0) at 1; auto with arith.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
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
Qed.


(** Compute the value x^(ω¹⁺ᵉ). This algorithm has quite a few special cases,
    which are commented inline.
 *)
Definition VF_exp_single (x:VForm) (e:VForm) : VForm :=
  match x with
  | F 0     => VF_one (* 0 ^ (ω¹⁺ᵉ) = 1 *)
  | F 1     => VF_one (* 1 ^ (ω¹⁺ᵉ) = 1 *)
  | F _     => match e with
               | F 0     => V 0 (F 0) (F 0)
               | F (S m) => V 0 (V 0 (F m) (F 0)) (F 0)
               | _       => V 0 (V 0 e (F 0)) (F 0)
               end
  | V 0 a _ => V 0 (VF_mul_single (VF_onePlus a) e) (F 0)
  | _       => V 0 (VF_mul_single x e) (F 0)
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
      rewrite onePlus_veblen; auto.
      do 2 (rewrite veblen_onePlus; auto).
      repeat rewrite addOrd_zero_r.
      symmetry.
      rewrite <- onePlus_veblen; auto.
      rewrite (expNatToOmegaPow (S (S n))).
      rewrite onePlus_veblen; auto.
      reflexivity.
      simpl; apply succ_trans. apply succ_least; auto with ord.
  - destruct n; simpl.
    + rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      transitivity (expOrd ω (VF_denote (VF_mul_single (VF_onePlus x1) e))).
      apply expOrd_eq_mor; auto with ord.
      { destruct x1; simpl.
        apply onePlus_veblen; auto.
        destruct n; simpl.
        apply onePlus_veblen; auto.
        apply onePlus_veblen; auto.
        apply addOrd_complete; auto.
        apply veblen_complete; auto.
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
      { simpl in *; intuition.
        destruct x2; auto.
        simpl in H; intuition.
        destruct n; simpl in *; intuition. }
      simpl in H; intuition.
      apply expToOmega_collapse_tower with m; auto.
      transitivity (expOrd ω 1).
      { rewrite expOrd_one'; auto.
        transitivity (natOrdSize (1+m)).
        rewrite natOrdSize_add. reflexivity.
        apply index_le.
        apply omega_gt0. }
      apply expOrd_monotone.
      apply addOrd_le1.
      simpl in H; destruct x1; simpl in *; intuition.
    + repeat( rewrite onePlus_veblen; auto).
      repeat (rewrite veblen_onePlus; auto).
      repeat rewrite addOrd_zero_r.
      rewrite expOrd_add.
      rewrite expOrd_mul.
      rewrite VF_onePlus_correct.
      apply expOrd_eq_mor; auto with ord.
      symmetry.
      rewrite (vtower_fin_fixpoints (S n) 0) at 1; auto with arith.
      simpl.
      rewrite veblen_onePlus; auto. rewrite addOrd_zero_r.
      apply expOrd_eq_mor; auto with ord.
      rewrite (vtower_fin_fixpoints (S n) 0) at 1; auto with arith.
      simpl.
      rewrite veblen_onePlus; auto. rewrite addOrd_zero_r.
      apply expOrd_eq_mor; auto with ord.
      rewrite (vtower_fin_fixpoints (S n) 0) at 1; auto with arith.
      simpl.
      rewrite veblen_onePlus; auto. rewrite addOrd_zero_r.
      reflexivity.
      auto 20.
      auto 20.
      auto 20.
      auto 20.
Qed.


(** Compute xʸ. The terms on the right are used to exponentate the entire
    term on the left via VF_exp_single and all the results are multiplied together.
  *)
Definition VF_exp (x:VForm) : VForm -> VForm :=
  let x' := VF_normalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | F 0      => VF_one
  | F n      => if VF_isZero x then F 1 else Nat.iter n (fun a => VF_mul a x') (F 1)
  | V 0 b y' => VF_mul (VF_exp_single x' b) (loop y')
  | _        => VF_exp_single x' y
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
  - destruct n.
    + rewrite VF_mul_correct.
      rewrite VF_exp_single_correct.
      rewrite IHy2.
      rewrite veblen_onePlus; auto.
      rewrite (expOrd_add _ _ (VF_denote y2)).
      apply mulOrd_eq_mor; auto with ord.
      apply expOrd_eq_mor; auto with ord.
      apply VF_normalize_equal.
      apply VF_normalize_isNormal.
    + rewrite VF_exp_single_correct.
      apply expOrd_eq_mor.
      apply VF_normalize_equal.
      simpl.
      rewrite onePlus_veblen; auto.
      symmetry.
      rewrite (vtower_fin_fixpoints (S n) 0) at 1; auto with arith.
      simpl.
      rewrite veblen_onePlus; auto. rewrite addOrd_zero_r.
      reflexivity.
      apply VF_normalize_isNormal.
Qed.

Lemma VF_epsilon_correct : forall x,
    VF_denote (VF_epsilon x) ≈ ε (VF_denote x).
Proof.
  simpl; intros.
  rewrite (veblen_func_onePlus (fun i => veblen (addOrd 1) i 0)); auto.
  transitivity (veblen (fun i : Ord => veblen (addOrd 1) i 0) 1 (VF_denote x)).
  split; apply veblen_monotone_first; auto with ord.
  intros; apply veblen_monotone_first; auto.
  rewrite addOrd_zero_r; auto with ord.
  intros; apply veblen_monotone_first; auto.
  rewrite addOrd_zero_r; auto with ord.
  rewrite veblen_succ; auto.
  unfold ε.
  split; apply VeblenCon.enum_fixpoints_func_mono; auto.
  intros.
  rewrite veblen_zero.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r; reflexivity.
  intros.
  rewrite veblen_zero.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r; reflexivity.
Qed.

Lemma VF_Gamma_correct : forall x,
    VF_denote (VF_Gamma x) ≈ Γ (VF_denote x).
Proof.
  unfold VF_Gamma.
  intros.
  unfold Γ.
  transitivity (veblen (fun b : Ord => veblen powOmega b 0) (1+0) (VF_denote x)).
  rewrite <- veblen_func_onePlus; auto with ord.
  simpl.
  split; apply veblen_monotone_func; auto.
  intros.
  rewrite (veblen_func_onePlus (fun i => veblen (addOrd 1) i 0)); auto with ord.
  apply veblen_monotone_func; auto.
  intros.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r. reflexivity.
  intros.
  rewrite (veblen_func_onePlus (fun i => veblen (addOrd 1) i 0)); auto with ord.
  apply veblen_monotone_func; auto.
  intros.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r. reflexivity.
  transitivity (veblen (fun b : Ord => veblen powOmega b 0) 1 (VF_denote x)).
  apply veblen_eq_mor; auto with ord.
  intros; apply veblen_monotone_first; auto with ord.
  rewrite addOrd_zero_r; auto with ord.
  rewrite veblen_succ; auto.
  split; apply VeblenCon.enum_fixpoints_func_mono; auto.
  intros. rewrite veblen_zero. reflexivity.
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

Theorem VF_reflects_Gamma : reflects VForm VF_denote (ORD ==> ORD) Γ VF_Gamma.
Proof.
  red; intros.
  rewrite VF_Gamma_correct.
  unfold Γ.
  split; apply enum_fixpoints_monotone; auto.
  intros; apply veblen_monotone_first; auto.
  apply H.
  intros; apply veblen_monotone_first; auto.
  apply H.
Qed.


Require ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VF_has_enough_notations (EM:ClassicalFacts.excluded_middle) :
  forall x, x < SmallVeblenOrdinal -> exists v:VF, v ≈ x.
Proof.
  (* main induction on x *)
  induction x as [x Hx] using ordinal_induction; intros.

  (* Classify x as zero, successor or limit *)
  destruct (classical.ordinal_discriminate EM x) as [Hzero|[Hsucc|Hlimit]].
  - (* Zero ordinal, exhibit Z *)
    exists (F 0). simpl.
    apply ord_isZero in Hzero. symmetry; auto.

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
    rewrite Ho. rewrite <- Hvo.
    apply VF_succ_correct.

  - (* limit case *)
    (* massage our x < SVO hypothesis a bit so the induction goes more smoothly *)
    assert (Hbnd : exists i, x < vtower_fin i x).
    { unfold SmallVeblenOrdinal in H.
      apply sup_lt in H. destruct H as [i H].
      exists i. eapply ord_lt_le_trans; [ apply H | ].
      apply normal_monotone; auto with ord. }

    (* inner induction goes on the number of levels in the veblen tower we need *)
    destruct Hbnd as [i Hbnd].
    induction i.

    + (* Vacuous base case. We cannot get here because
           x is a limit and veblen_tower 0 is too small. *)
      simpl in *. elim (ord_lt_irreflexive x).
      apply ord_lt_le_trans with (1+x); auto.
      apply limit_onePlus; auto.

    + (* i successor case *)

      (* is x a fixpoint of the next lower level? *)
      destruct (classical.order_total EM (vtower_fin i x) x).
      * (* we have found the right level, decompose the ordinal *)
        destruct (veblen_decompose EM _ (vtower_fin_normal i) x)
          as [a [b [Hab [Ha0 [Ha Hb]]]]]; auto.
        { simpl in Hbnd. rewrite limit_onePlus in Hbnd; auto. }

        (* invoke the main induction hypothesis *)
        destruct (Hx a) as [va Hva]; auto.
        transitivity x; auto.
        destruct (Hx b) as [vb Hvb]; auto.
        transitivity x; auto.

        (* Adjust va *)
        assert (Hva' :  exists va', 1 + VF_denote va' ≈ VF_denote va).
        { destruct va as [n|j va1 va2]. destruct n.
          - elim (ord_lt_irreflexive a).
            rewrite <- Hva at 1. auto.
          - exists (F n). apply onePlus_finite_succ.
          - exists (V j va1 va2). apply onePlus_veblen; auto.
        }
        destruct Hva' as [va' Hva'].

        (* Exhibit the V form and wrap up *)
        exists (V i va' vb).
        rewrite Hab. simpl.
        rewrite Hva'.
        apply veblen_eq_mor; auto.

      * (* easy recursive case *)
        apply IHi; auto.
Qed.
