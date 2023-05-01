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
From Ordinal Require Import VTowerFin.

From Ordinal Require Import Notation.CantorDecomposition.

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
| Z : VForm
| V : nat -> VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | V n a x => veblen (vtower_fin n) (VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x; auto.
  simpl; apply veblen_complete; auto.
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

Theorem VZ_collapse :
  forall n a, VF_denote (V (S n) Z a) ≈ VF_denote (V n (V 0 Z a) Z).
Proof.
  simpl; intros.
  rewrite veblen_zero.
  rewrite veblen_onePlus; auto.
  rewrite expOrd_zero.
  reflexivity.
Qed.

Theorem Vmn_collapse : forall n m a b c,
  (m < n)%nat ->
  0 < VF_denote b ->
  VF_denote a < VF_denote (V n b c) ->
  VF_denote (V m a (V n b c)) ≈ VF_denote (V n b c).
Proof.
  simpl VF_denote.
  intros.
  split.
  2: { apply veblen_inflationary; auto. }
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal n) 0 (VF_denote b) (VF_denote c)) at 2; auto.
  rewrite veblen_zero.
  destruct n. inversion H.
  assert (m <= n)%nat by lia.
  simpl vtower_fin at 3.
  simpl in H1.
  rewrite onePlus_veblen; auto.
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal n) (VF_denote a) _ 0); auto.
  transitivity
    (veblen (vtower_fin n) (VF_denote a)
            (veblen (vtower_fin (S n)) (VF_denote b) (VF_denote c))).
  { apply veblen_monotone_func; auto.
    apply vtower_fin_index_monotone; auto. }

  apply veblen_monotone; auto.
  simpl.
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal (S n)) 0 (VF_denote b) (VF_denote c)) at 1; auto.
  rewrite veblen_zero.
  simpl.
  rewrite onePlus_veblen; auto with ord.
Qed.

Theorem Vmn_collapse2 : forall n m b c,
  (m < n)%nat ->
  0 < VF_denote b ->
  VF_denote (V m (V n b c) Z) ≈ VF_denote (V n b c).
Proof.
  intros. simpl. split.
  - rewrite <- (veblen_fixpoints _ (vtower_fin_normal n) 0) at 2; auto.
    rewrite veblen_zero.
    destruct n. lia.
    simpl.
    rewrite onePlus_veblen; auto.
    apply veblen_monotone_func; auto.
    apply vtower_fin_index_monotone. lia.
  - apply (normal_inflationary (fun x => veblen (vtower_fin m) x 0)); auto.
Qed.

Definition VF_isZero x : { x = Z } + { 0 < VF_denote x }.
Proof.
  destruct x; auto.
  right. simpl. apply veblen_nonzero; auto.
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
                 | Z => m = O
                 | V n _ _ => (m >= n)%nat
                 end

               | V n x y =>
                 match nat_compare m n with
                 | LT => VF_denote a >= VF_denote b
                 | EQ => VF_denote a >= VF_denote x
                 | GT => VF_denote a > 0
                 end
               end
  end.

Fixpoint locally_normal x :=
  match x with
  | Z => True
  | V n a x => locally_normal a /\
               locally_normal x /\
               if VF_isZero a then n = O else True
  end.

Definition subterm_shrink x :=
  match x with
  | Z => True
  | V m a b => VF_denote a < VF_denote (V m a b) /\
               VF_denote b < VF_denote (V m a b)
  end.

Lemma normal_locally_normal : forall x, VF_isNormal x -> locally_normal x.
Proof.
  induction x; simpl; intuition.
  destruct (VF_isZero x1); subst; simpl in *; auto.
  destruct x2; simpl in *; intuition.
  generalize (nat_compare_correct n n0).
  destruct (nat_compare n n0); intros; intuition.
  - elim (ord_lt_irreflexive 0).
    rewrite <- H2 at 2.
    apply veblen_nonzero; auto.
  - subst n0.
    destruct (VF_isZero x2_1); subst; auto.
    elim (ord_lt_irreflexive 0).
    rewrite <- H2 at 2; auto.
  - elim (ord_lt_irreflexive 0); auto.
Qed.


Lemma normal_subterm_shrink : forall x, VF_isNormal x -> subterm_shrink x.
Proof.
  induction x; simpl; intuition.
  - destruct x2.
    + destruct x1; simpl in *; intuition.
      * apply veblen_nonzero; auto.
      * apply ord_le_lt_trans with
            (veblen (vtower_fin n) (VF_denote x1_1) (VF_denote x1_2)).
        apply veblen_monotone_func; auto.
        apply vtower_fin_index_monotone; auto.
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + simpl in *.
      apply veblen_subterm1; auto with ord.
      apply veblen_nonzero; auto.
  - destruct x2; simpl in *; intuition.
    + apply veblen_nonzero; auto.
    + generalize (nat_compare_correct n n0).
      destruct (nat_compare n n0); intros; subst.
      * (* LT case *)
        rewrite H2 at 1.
        apply veblen_subterm1; auto with ord.
        apply veblen_nonzero; auto.
      * (* EQ case *)
        apply veblen_increasing'; auto.
      * (* GT case *)
        apply veblen_collapse'; auto.
        eapply ord_lt_le_trans; [ apply H |].
        apply veblen_inflationary; auto.
        eapply ord_lt_le_trans; [ apply H6 |].
        apply veblen_inflationary; auto.
        apply vtower_fin_fixpoints; auto.
Qed.

Lemma VF_compare_correct :
  forall x y,
    locally_normal x ->
    locally_normal y ->
    match VF_compare x y with
    | LT => VF_denote x < VF_denote y
    | EQ => VF_denote x ≈ VF_denote y
    | GT => VF_denote x > VF_denote y
    end.
Proof.
  induction x as [|m a Ha x Hx]; intros y Hlx Hly.
  - destruct y as [|n b y].
    + simpl. reflexivity.
    + simpl. apply veblen_nonzero; auto.
  - induction y as [|n b Hb y Hy].
    + simpl. apply veblen_nonzero; auto.
    + simpl in Hlx; destruct Hlx as [Hlx1 [Hlx2 Hlx3]].
      simpl in Hly; destruct Hly as [Hly1 [Hly2 Hly3]].
      generalize (nat_compare_correct m n).
      destruct (nat_compare m n); intro Hmn.
      * rewrite VF_compare_lt; auto.
        generalize (Ha (V n b y)).
        destruct (VF_compare a (V n b y)); intros.
        ** generalize (Hx (V n b y)).
           destruct (VF_compare x (V n b y)); intros.
           *** simpl.
               apply veblen_collapse'; auto.
               apply H; simpl; auto.
               apply H0; simpl; auto.
               apply vtower_fin_fixpoints; auto.
               destruct (VF_isZero b); auto. lia.
           *** simpl. split.
               { apply veblen_collapse; auto.
                 apply H; simpl; auto.
                 apply H0; simpl; auto.
                 apply (vtower_fin_fixpoints n m); auto.
                 destruct (VF_isZero b); auto. lia. }
               { simpl in H0. rewrite <- H0; simpl; auto. apply veblen_inflationary; auto. }
           *** simpl.
               simpl in H0.
               eapply ord_lt_le_trans; [ apply H0; simpl; auto |].
               apply veblen_inflationary; auto.
        ** destruct (VF_isZero x); subst; simpl.
           rewrite (vtower_fin_fixpoints n m); auto.
           split; apply veblen_monotone_first; auto; apply H; simpl; auto.
           destruct (VF_isZero b); auto. lia.

           rewrite (vtower_fin_fixpoints n m); auto.
           apply veblen_increasing'; auto.
           apply H; simpl; auto.
           destruct (VF_isZero b); auto. lia.
        ** apply ord_lt_le_trans with (VF_denote a).
           apply H; simpl; auto.
           simpl.
           transitivity (veblen (vtower_fin m) (VF_denote a) 0).
           apply (normal_inflationary (fun i => veblen (vtower_fin m) i 0)); auto.
           apply veblen_monotone; auto with ord.

      * subst n.
        rewrite VF_compare_eq.
        simpl; apply veblen_compare_correct; auto.
        apply Ha; simpl; auto.
        apply Hx; simpl; auto.
        apply Hx; simpl; auto.
        apply Hy; simpl; auto.

      * rewrite VF_compare_gt; auto.
        generalize (Hb Hly1).
        destruct (VF_compare (V m a x) b); intros.
        ** intros.
           apply ord_lt_le_trans with (VF_denote b); auto.
           simpl.
           transitivity (veblen (vtower_fin n) (VF_denote b) 0).
           apply (normal_inflationary (fun i => veblen (vtower_fin n) i 0)); auto.
           apply veblen_monotone; auto with ord.
        ** destruct (VF_isZero y); subst; simpl.
           rewrite (vtower_fin_fixpoints m n); auto.
           split; apply veblen_monotone_first; auto; apply H; simpl; auto.
           destruct (VF_isZero a); auto. lia.

           rewrite (vtower_fin_fixpoints m n); auto.
           apply veblen_increasing'; auto.
           apply H; simpl; auto.
           destruct (VF_isZero a); auto. lia.
        ** generalize (Hy Hly2).
           destruct (VF_compare (V m a x) y); intros.
           *** apply ord_lt_le_trans with (VF_denote y); auto.
               simpl.
               apply normal_inflationary; auto.
           *** split.
               { rewrite H0. simpl. apply normal_inflationary; auto. }
               simpl. apply veblen_collapse; auto.
               apply H0.
               apply (vtower_fin_fixpoints m n); auto.
               destruct (VF_isZero a); auto. lia.
           *** simpl.
               apply veblen_collapse'; auto.
               apply vtower_fin_fixpoints; auto.
               destruct (VF_isZero a); auto. lia.
Qed.

Global Opaque VF_compare.

Fixpoint VF_local_norm (x:VF) :=
  match x with
  | Z => Z
  | V O a b => V O (VF_local_norm a) (VF_local_norm b)
  | V (S n) a b =>
    if VF_isZero a then
      V n (V 0 Z (VF_local_norm b)) Z
    else
      V (S n) (VF_local_norm a) (VF_local_norm b)
  end.

Lemma VF_local_norm_eq x :
  VF_denote (VF_local_norm x) ≈ VF_denote x.
Proof.
  induction x; simpl; auto with ord.
  destruct n; simpl.
  - apply veblen_eq_mor; auto.
  - destruct (VF_isZero x1); subst.
    + destruct (VF_isZero x2); subst.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite expOrd_zero.
      rewrite addOrd_zero_r.
      rewrite veblen_zero.
      rewrite addOrd_zero_r.
      reflexivity.
      simpl.
      rewrite veblen_onePlus; auto.
      rewrite expOrd_zero.
      rewrite veblen_zero.
      rewrite IHx2.
      reflexivity.
    + apply veblen_eq_mor; auto.
      intros. apply veblen_monotone_first; auto.
Qed.

Lemma VF_local_norm_is_local_norm x :
  locally_normal (VF_local_norm x).
Proof.
  induction x; simpl; intuition.
  destruct n; simpl; intuition.
  - destruct (VF_isZero (VF_local_norm x1)); auto.
  - destruct (VF_isZero x1); subst; auto.
    + simpl; intuition.
      destruct (VF_isZero Z); auto.
      destruct (VF_isZero (V 0 Z (VF_local_norm x2))); auto.
      discriminate.
    + simpl; intuition.
      destruct (VF_isZero (VF_local_norm x1)); auto.
      rewrite <- VF_local_norm_eq in o.
      rewrite e in o.
      elim (ord_lt_irreflexive 0); auto.
Qed.

Theorem VF_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct (VF_local_norm x) (VF_local_norm y)
                                 (VF_local_norm_is_local_norm x)
                                 (VF_local_norm_is_local_norm y)).
  destruct (VF_compare (VF_local_norm x) (VF_local_norm y)).
  - intros.
    do 2 rewrite VF_local_norm_eq in H.
    left; auto.
  - intros.
    do 2 rewrite VF_local_norm_eq in H.
    right; auto. apply H.
  - intros.
    do 2 rewrite VF_local_norm_eq in H.
    right; auto with ord.
Qed.

Fixpoint VF_onePlus (x:VForm) :=
  match x with
  | Z => V 0 Z Z
  | V 0 Z x' => V 0 Z (VF_onePlus x')
  | V (S n) Z x' => V n (VF_onePlus x') Z
  | _ => x
  end.

Lemma VF_onePlus_normal : forall x, VF_isNormal x -> VF_isNormal (VF_onePlus x).
Proof.
  induction x; simpl; intuition.
  destruct n.
  - destruct x1; simpl in *; intuition.
    destruct x2; simpl in *; intuition.
    destruct n; simpl.
    + destruct x2_1; simpl in *; intuition.
    + elim (ord_lt_irreflexive 0).
      eapply ord_lt_le_trans; [ | apply H2 ].
      apply veblen_nonzero; auto.
  - destruct x1; simpl in *; intuition.
    destruct x2; simpl in *; intuition.
    destruct n0; simpl in *; intuition.
    elim (ord_lt_irreflexive 0); auto.
    destruct x2_1; simpl in *; intuition.
    generalize (nat_compare_correct n n0).
    destruct (nat_compare n n0); try lia.
    elim (ord_lt_irreflexive 0).
    eapply ord_lt_le_trans; [ | apply H2 ].
    apply veblen_nonzero; auto.

    elim (ord_lt_irreflexive 0); auto.
    destruct (nat_compare n n0); auto.
    eapply ord_lt_le_trans; [ | apply H2 ].
    apply veblen_nonzero; auto.
    eapply ord_lt_le_trans; [ | apply H2 ].
    apply veblen_nonzero; auto.
Qed.

Lemma VF_onePlus_correct x : VF_denote (VF_onePlus x) ≈ 1 + VF_denote x.
Proof.
  induction x; simpl.
  - rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    rewrite addOrd_zero_r.
    rewrite expOrd_zero.
    reflexivity.
  - destruct n.
    + destruct x1; simpl.
      rewrite veblen_onePlus; auto.
      rewrite expOrd_zero.
      rewrite veblen_zero.
      rewrite IHx2. reflexivity.
      rewrite onePlus_veblen; auto with ord.
      apply veblen_nonzero; auto.
    + destruct x1; simpl.
      rewrite veblen_zero.
      rewrite onePlus_veblen; auto with ord.
      rewrite IHx2. reflexivity.
      rewrite onePlus_veblen; auto with ord.
      apply veblen_nonzero; auto.
Qed.

Definition Vnorm m a b :=
  match b with
  | Z => match a with
         | Z => match m with
                | O => V O Z Z
                | S m' => V m' (V O Z Z) Z
                end
         | V o _ _ => match nat_compare m o with
                      | LT => a
                      | _  => V m a Z
                      end
         end

  | V n x y => match nat_compare m n with
               | LT => match VF_compare a b with
                       | LT => b
                       | _  => V m a b
                       end
               | EQ => match VF_compare a x with
                       | LT => b
                       | _  => V m a b
                       end
               | GT => if VF_isZero a then
                         V (pred m) (VF_onePlus b) Z
                       else
                         V m a b
               end
  end.

Fixpoint VF_normalize x :=
  match x with
  | Z => Z
  | V m a b => Vnorm m (VF_normalize a) (VF_normalize b)
  end.

Local Opaque VF_onePlus.

Lemma Vnorm_equal m a b :
  VF_isNormal a ->
  VF_isNormal b ->
  VF_denote (Vnorm m a b) ≈ VF_denote (V m a b).
Proof.
  unfold Vnorm; intros.
  destruct b; simpl.
  - destruct a; simpl in *; intuition.
    destruct m; simpl; auto with ord.
    rewrite veblen_zero.
    rewrite veblen_zero.
    reflexivity.
    generalize (nat_compare_correct m n).
    destruct (nat_compare m n); simpl; intuition.
    apply vtower_fin_fixpoints; auto.
    assert (locally_normal (V n a1 a2)).
    { apply normal_locally_normal. simpl; intuition. }
    simpl in H4. destruct (VF_isZero a1); intuition. lia.

  - generalize (nat_compare_correct m n).
    destruct (nat_compare m n); intuition.
    + generalize (VF_compare_correct a (V n b1 b2)
                                     (normal_locally_normal _ H)
                                     (normal_locally_normal _ H0)).
      destruct (VF_compare a (V n b1 b2)); simpl in *; intuition.
      * split. apply veblen_inflationary; auto.
        apply veblen_collapse; auto with ord.
        apply vtower_fin_fixpoints; auto.
        assert (locally_normal (V n b1 b2)).
        { apply normal_locally_normal. simpl; intuition. }
        simpl in H4. destruct (VF_isZero b1); intuition. lia.
    + subst n.
      simpl in H0; intuition.
      generalize (VF_compare_correct a b1
                                     (normal_locally_normal _ H)
                                     (normal_locally_normal _ H1)).
      destruct (VF_compare a b1); simpl; intuition.
      split. apply veblen_inflationary; auto.
      apply veblen_fixpoints; auto.
    + destruct (VF_isZero a).
      * subst a. simpl.
        destruct m. lia.
        rewrite veblen_zero. simpl.
        rewrite VF_onePlus_correct.
        reflexivity.
      * simpl; auto with ord.
Qed.

Lemma Vnorm_normal m a b :
  VF_isNormal a ->
  VF_isNormal b ->
  VF_isNormal (Vnorm m a b).
Proof.
  unfold Vnorm; intros.
  destruct b; simpl.
  - destruct a; simpl in *; intuition.
    destruct m; simpl; intuition.

    generalize (nat_compare_correct m n).
    destruct (nat_compare m n); simpl; intuition.
    subst m; auto with arith.
  - generalize (nat_compare_correct m n).
    destruct (nat_compare m n); intuition.
    + generalize (VF_compare_correct a (V n b1 b2)
                                     (normal_locally_normal _ H)
                                     (normal_locally_normal _ H0)).
      destruct (VF_compare a (V n b1 b2)); simpl in *; intuition.
      * generalize (nat_compare_correct m n).
        destruct (nat_compare m n); intuition; try lia.
        apply H2.
      * generalize (nat_compare_correct m n).
        destruct (nat_compare m n); intuition; try lia.
    + subst n.
      simpl in H0; intuition.
      generalize (VF_compare_correct a b1
                                     (normal_locally_normal _ H)
                                     (normal_locally_normal _ H1)).
      destruct (VF_compare a b1); simpl; intuition.
      * generalize (nat_compare_correct m m).
        destruct (nat_compare m m); intuition; try lia.
        apply H2.
      * generalize (nat_compare_correct m m).
        destruct (nat_compare m m); intuition; try lia.

    + simpl in *; intuition.
      destruct (VF_isZero a); subst.
      simpl; intuition.
      apply VF_onePlus_normal; simpl; intuition.
Transparent VF_onePlus.
      simpl.
      destruct n; simpl.
      destruct b1; simpl; try lia.
      destruct b1; simpl; try lia.
      simpl; intuition.
      generalize (nat_compare_correct m n).
      destruct (nat_compare m n); intuition; try lia.
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
  apply VF_normalize_isNormal.
  apply VF_normalize_isNormal.
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
      { generalize (nat_compare_correct m n).
        destruct (nat_compare m n); intros; auto.
        - exfalso.
          assert (Hlb: locally_normal (V n b y)).
          { apply normal_locally_normal. simpl; intuition. }
          simpl in Hlb.
          elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite (vtower_fin_fixpoints n m); auto.
          apply veblen_subterm1_zero_nest; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          destruct (VF_isZero b); auto.
          intuition; subst.
          inversion H4.
        - assert (Hla: locally_normal (V m a x)).
          { apply normal_locally_normal. simpl; intuition. }
          elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite (vtower_fin_fixpoints m n); auto.
          apply veblen_subterm1_zero_nest; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          simpl in Hla.
          destruct (VF_isZero a); auto.
          intuition; subst.
          inversion H4.
      }
      subst n.
      assert (a = b).
      { apply Ha; auto.
        destruct (VF_decide_order a b).
        { elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ (vtower_fin_normal m) (VF_denote a) (VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; intuition. }
        destruct (VF_decide_order b a).
        { elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (veblen_fixpoints _ (vtower_fin_normal m) (VF_denote b) (VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V m b y)); simpl; intuition. }
        split; auto. }
      subst b.
      f_equal.
      apply Hx; auto.
      destruct (VF_decide_order x y).
      { elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
        rewrite H1 at 2.
        apply veblen_increasing'; auto with ord. }
      destruct (VF_decide_order y x).
      { elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
        rewrite H1 at 1.
        apply veblen_increasing'; auto with ord. }
      split; auto.
Qed.


Theorem VF_below_SVO : forall x:VF, x < SmallVeblenOrdinal.
Proof.
  induction x; simpl.
  - unfold SmallVeblenOrdinal.
    rewrite <- (sup_le _ _ 0%nat).
    simpl.
    rewrite addOrd_zero_r.
    apply succ_lt.
  - apply veblen_collapse'; auto.
    unfold SmallVeblenOrdinal.
    apply sup_complete; auto.
    hnf; intros.
    exists (Nat.max a1 a2).
    split; apply vtower_fin_index_monotone; auto with arith.
    left. exists 0%nat.
    simpl.
    rewrite addOrd_zero_r.
    apply succ_lt.
    unfold SmallVeblenOrdinal.
    etransitivity.
    apply veblen_continuous_first; auto.
    apply sup_least; intro i.
    rewrite <- (sup_le _ _ (S (S (Nat.max i n)))).
    simpl.
    transitivity
      (veblen (fun x : Ord => veblen (vtower_fin (Nat.max i n)) (1 + x) 0) 1 0).
    rewrite veblen_succ; auto.
    rewrite enum_are_fixpoints; auto.
    rewrite veblen_zero.
    transitivity (veblen (vtower_fin (Nat.max i n)) (vtower_fin i 0) 0).
    apply veblen_monotone_func; auto.
    apply vtower_fin_index_monotone; auto with arith.
    apply veblen_monotone_first; auto.
    rewrite enum_are_fixpoints; auto.
    rewrite veblen_zero.
    rewrite <- (veblen_fixpoints _ (vtower_fin_normal _) 0); auto.
    rewrite veblen_zero.
    rewrite <- addOrd_le2.
    transitivity (vtower_fin (Nat.max i n) 0).
    apply vtower_fin_index_monotone; auto with arith.
    apply normal_monotone; auto with ord.
    apply addOrd_complete; auto.
    apply enum_fixpoints_complete; auto.
    intros. apply veblen_inflationary; auto.
    apply veblen_monotone_first; auto.
    intros.
    apply veblen_monotone_first; auto.
    apply addOrd_le1.
Qed.

Theorem VF_SVO : VF ≈ SmallVeblenOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. apply VF_below_SVO.
  - unfold SmallVeblenOrdinal.
    apply sup_least. intro i.
    transitivity (VF_denote (V i (V O Z Z) Z)).
    2: { apply index_le. }
    simpl.
    transitivity (veblen (vtower_fin i) 1 0).
    rewrite veblen_succ; auto.
    rewrite enum_fixpoints_zero; auto.
    rewrite normal_fixpoint; auto.
    rewrite veblen_zero.
    apply normal_monotone; auto with ord.
    apply veblen_monotone_first; auto.
    apply succ_least. apply veblen_nonzero; auto.
Qed.

Lemma veblen_tower_epsilon :
  forall n x y,
    complete x ->
    complete y ->
    (n > 0)%nat ->
    x > 0 ->
    expOrd ω (veblen (vtower_fin n) x y) ≈ veblen (vtower_fin n) x y.
Proof.
  intros.
  split.
  - transitivity (veblen (vtower_fin 0) (veblen (vtower_fin n) x y) 0).
    2: { apply vtower_fin_fixpoints; auto. }
    simpl.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r. auto with ord.
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
  induction x; simpl; intuition.
  destruct n.
  simpl; auto.
  simpl in *; intuition.
  destruct n; simpl; auto.
  split; auto.
  destruct x2; simpl; auto.
  destruct n; simpl in *; auto.

  assert (locally_normal (V n x1 x2)).
  { apply normal_locally_normal. simpl; auto. }

  destruct n.
  - rewrite veblen_onePlus; auto with ord.
    rewrite H8. reflexivity.

  - simpl in *. rewrite addOrd_zero_r.
    destruct (VF_isZero x1).
    intuition discriminate.
    symmetry. apply (veblen_tower_epsilon (S n)); auto with arith.
Qed.

Lemma VF_recompose_correct:
  forall xs,
    each VF_isNormal xs ->
    cantor_ordered VF_denote xs ->
    VF_isNormal (VF_recompose xs) /\ cantor_denote VF_denote xs ≈ VF_denote (VF_recompose xs).
Proof.
  induction xs; simpl in *; intuition.
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
  assert (locally_normal (V n a1 a2)).
  { apply normal_locally_normal; simpl in *; intuition. }
  simpl in *.
  destruct n; simpl; auto.
  rewrite veblen_onePlus; auto with ord.
  rewrite veblen_onePlus; auto with ord.
  apply addOrd_complete; auto.
  apply expOrd_complete; auto with ord.
  apply omega_gt0.
  apply omega_complete.
  rewrite addOrd_zero_r.
  apply (veblen_tower_epsilon (S n)); auto with ord arith.
  destruct (VF_isZero a1); auto.
  intuition discriminate.

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
    (fun x y Hx Hy => VF_compare_correct x y (normal_locally_normal x Hx) (normal_locally_normal y Hy))
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
      with (f:=VF_denote) (P:=VF_isNormal) (g:=vtower_fin n) (a:=a) (b:=VF_denote b) (vr:=Vnorm n); auto.
    + apply VF_has_cantor_decomposition.
    + clear Hnorm.
      induction n as [n Hindn] using (size_induction ω).
      destruct n; intros.
      { apply onePlus_interpolants with (zr:=Z) (pr:=VF_add (VF_succ Z)); auto.
        hnf; simpl; intuition.
        hnf; intros.
        apply VF_add_reflects; auto with ord.
        destruct (VF_succ_reflects 0 Z); simpl; intuition. }
      simpl.
      apply veblen_interpolants_first with (vr:=Vnorm n); auto.
      * apply VF_has_cantor_decomposition.
      * intros. apply Hindn; auto with ord.
        simpl. auto with ord.
        intros. apply Hindx; auto.
        eapply ord_lt_le_trans; [ apply H3 |].
        simpl.
        apply veblen_monotone_func; auto.
        intros. apply vtower_fin_succ_monotone; auto.
      * hnf; simpl; intuition.
        rewrite Vnorm_equal; auto with ord.
        simpl.
        split; apply veblen_monotone_full; auto with ord.
        apply H2. apply H4.
        apply H2. apply H4.
        apply Vnorm_normal; auto.
      * apply onePlus_interpolants with (zr:=Z) (pr:=VF_add (VF_succ Z)); auto.
        hnf; simpl; intuition.
        hnf; intros.
        apply VF_add_reflects; auto with ord.
        destruct (VF_succ_reflects 0 Z); simpl; intuition.
    + hnf; simpl; intuition.
      rewrite Vnorm_equal; auto with ord.
      simpl.
      split; apply veblen_monotone_full; auto with ord.
      apply H0. apply H2.
      apply H0. apply H2.
      apply Vnorm_normal; auto.
    + simpl in Hnorm; intuition.
    + apply Hindx.
      destruct (normal_subterm_shrink _ Hnorm); auto.
      simpl in Hnorm; intuition.
    + apply Hindx.
      destruct (normal_subterm_shrink _ Hnorm); auto.
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

Theorem VF_has_enough_notations (EM:excluded_middle) :
  forall x, x < SmallVeblenOrdinal -> exists v:VF, v ≈ x.
Proof.
  intros x H.
  rewrite <- VF_SVO in H.
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

Theorem VF_has_enough_notations' (EM:excluded_middle) :
  forall x, x < SmallVeblenOrdinal -> exists v:VF, v ≈ x.
Proof.
  (* main induction on x *)
  induction x as [x Hx] using ordinal_induction; intros.

  (* Classify x as zero, successor or limit *)
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
    destruct VF_succ_reflects with (VF_denote vo) (VF_normalize vo) .
    split. symmetry. apply VF_normalize_equal.
    apply VF_normalize_isNormal.
    rewrite <- H0.
    reflexivity.

  - (* limit case *)
    (* massage our x < SVO hypothesis a bit so the induction goes more smoothly *)
    assert (Hbnd : exists i, x < vtower_fin i x).
    { unfold SmallVeblenOrdinal in H.
      apply sup_lt in H. destruct H as [i H].
      exists i. eapply ord_lt_le_trans; [ apply H |].
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

        exists (V i va vb).
        rewrite Hab.
        simpl. apply veblen_eq_mor; auto.

      * (* easy recursive case *)
        apply IHi; auto.
Qed.
