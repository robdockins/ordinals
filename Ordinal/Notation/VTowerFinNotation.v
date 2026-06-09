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
From Ordinal Require Import VTowerFin.

From Ordinal Require Import Notation.CantorDecomposition.

Open Scope ord_scope.

Definition SmallAckermannOrdinal := supOrd (fun n:ω => vtower_fin n 0).

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

Lemma vtower_fin_Zcollapse:
  forall n a, complete a -> veblen (vtower_fin (S n)) 0 a ≈ veblen (vtower_fin n) (1+a) 0.
Proof.
  simpl; intros.
  rewrite veblen_zero.
  rewrite veblen_enum_fixpoints; auto with ord.
Qed.

Theorem VZ_collapse :
  forall n a, VF_denote (V (S n) Z a) ≈ VF_denote (V n (V 0 Z a) Z).
Proof.
  simpl; intros.
  rewrite veblen_zero.
  rewrite veblen_onePlus; auto.
  rewrite expOrd_zero.
  rewrite veblen_enum_fixpoints; auto with ord.
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

  rewrite (vtower_fin_fixpoints n m) at 2; auto with ord.
  rewrite <- (veblen_fixpoints _ (vtower_fin_normal m) (VF_denote a) _ 0); auto.
  apply veblen_monotone; auto with ord.
  apply normal_inflationary with (f := fun x => veblen _ x 0); auto with ord.
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
    apply veblen_monotone_func; auto with ord.
    intros.
    transitivity (vtower_fin n i).
    apply vtower_fin_index_monotone; auto. lia.
    rewrite enum_are_fixpoints; auto with ord.
    apply normal_monotone; auto with ord.
    apply normal_inflationary; auto with ord.
  - apply normal_inflationary with (f:= fun x => veblen _ x 0); auto with ord.
Qed.

Inductive redex : VForm -> VForm -> Prop:=
| redex_VZ : forall n a,
    redex (V (S n) Z a) (V n (V 0 Z a) Z)
| redex_V : forall n a b x,
    VF_denote a < VF_denote b ->
    redex (V n a (V n b x)) (V n b x)
| redex_Vmn1 : forall m n a b c,
    (m < n)%nat ->
    b <> Z ->
    VF_denote a < VF_denote (V n b c) ->
    redex (V m a (V n b c)) (V n b c)
| redex_Vmn2 : forall m n b c,
    (m < n)%nat ->
    b <> Z ->
    redex (V m (V n b c) Z) (V n b c).

Lemma redex_sound: forall x y,
    redex x y ->
    VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. inversion H; subst.
  - apply VZ_collapse.
  - apply V_collapse; auto.
  - apply Vmn_collapse; auto.
    destruct b; simpl; try contradiction.
    apply veblen_nonzero; auto.
  - apply Vmn_collapse2; auto.
    destruct b; simpl; try contradiction.
    apply veblen_nonzero; auto.
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

Fixpoint well_formed x :=
  match x with
  | Z => True
  | V n a x => well_formed a /\
               well_formed x /\
               if VF_isZero a then n = O else True
  end.

Definition subterm_shrink x :=
  match x with
  | Z => True
  | V m a b => VF_denote a < VF_denote (V m a b) /\
               VF_denote b < VF_denote (V m a b)
  end.

Lemma normal_well_formed : forall x, VF_isNormal x -> well_formed x.
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
      * apply ord_le_lt_trans with
            (veblen (vtower_fin n) (VF_denote x1_1) (VF_denote x1_2)).
        apply veblen_monotone_func; auto.
        apply vtower_fin_index_monotone; auto.
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + simpl in *.
      apply veblen_subterm1; auto with ord.
  - destruct x2; simpl in *; intuition.
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
        apply vtower_fin_fixpoints; auto.
Qed.

Lemma VF_compare_correct :
  forall x y,
    well_formed x ->
    well_formed y ->
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
               apply veblen_collapse'; simpl; auto.
               apply H; simpl; intuition.
               apply H0; simpl; intuition.
               destruct (VF_isZero b); [ lia |].
               apply vtower_fin_fixpoints; auto.

           *** simpl. split.
               apply veblen_collapse; auto.
               apply H; simpl; intuition.
               apply H0; simpl; intuition.
               apply (vtower_fin_fixpoints n m); auto.
               destruct (VF_isZero b); [ lia | auto ].
               simpl in H0. rewrite <- H0; simpl; auto. apply veblen_inflationary; auto with ord.
           *** simpl.
               simpl in H0.
               eapply ord_lt_le_trans; [ apply H0; simpl; auto |].
               intuition.
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
        apply Ha; simpl; intuition.
        apply Hx; simpl; intuition.
        apply Hx; simpl; intuition.
        apply Hy; simpl; intuition.

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

Fixpoint VF_onePlus (x:VForm) :=
  match x with
  | Z => V 0 Z Z
  | V 0 Z x' => V 0 Z (VF_onePlus x')
  | V (S n) Z x' => V n (VF_onePlus x') Z
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
    + destruct x1; simpl.
      * rewrite veblen_zero.
        rewrite <- veblen_enum_fixpoints; auto with ord.
        rewrite IHx2.
        symmetry. apply onePlus_veblen; auto with ord.
      * symmetry. apply onePlus_veblen; auto with ord.
Qed.

Lemma VF_onePlus_well_formed: forall x, well_formed x -> well_formed (VF_onePlus x).
Proof.
  induction x; simpl; intuition.
  destruct (VF_isZero Z); auto.
  destruct n.
  - destruct x1; simpl in *; intuition.
  - destruct x1; simpl in *; intuition.
    destruct (VF_isZero (VF_onePlus x2)); auto.
    destruct x2; simpl in *; intuition; try discriminate.
    destruct n0.
    destruct x2_1; auto; try discriminate.
    destruct x2_1; auto; try discriminate.
Qed.

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
    apply veblen_nonzero; auto with ord.

    elim (ord_lt_irreflexive 0); auto.
    destruct (nat_compare n n0); auto.
    eapply ord_lt_le_trans; [ | apply H2 ].
    apply veblen_nonzero; auto with ord.
    eapply ord_lt_le_trans; [ | apply H2 ].
    apply veblen_nonzero; auto.
Qed.

Fixpoint VF_wf (x:VF) :=
  match x with
  | Z => Z
  | V O a b => V O (VF_wf a) (VF_wf b)
  | V (S n) a b =>
    if VF_isZero a then
      V n (VF_onePlus (VF_wf b)) Z
    else
      V (S n) (VF_wf a) (VF_wf b)
  end.

Lemma VF_wf_eq x :
  VF_denote (VF_wf x) ≈ VF_denote x.
Proof.
  induction x; simpl; auto with ord.
  destruct n; simpl.
  - apply veblen_eq_mor; auto with ord.
  - destruct (VF_isZero x1); subst.
    + simpl.
      rewrite veblen_zero.
      rewrite <- veblen_enum_fixpoints; auto with ord.
      apply veblen_eq_mor; auto with ord.
      rewrite VF_onePlus_equal. auto with ord.
      rewrite IHx2; auto with ord.
    + intros. simpl.
      apply veblen_eq_mor; auto with ord.
Qed.

Lemma VF_wf_well_formed: forall x, well_formed (VF_wf x).
Proof.
  induction x; simpl; intuition.
  destruct n; simpl; intuition.
  - destruct (VF_isZero (VF_wf x1)); auto.
  - destruct (VF_isZero x1); simpl; subst; intuition.
    + apply VF_onePlus_well_formed; auto.
    + destruct (VF_isZero (VF_onePlus (VF_wf x2))); auto.
      destruct (VF_wf x2); simpl in *; try discriminate.
      destruct n0; destruct v1; simpl; discriminate.
    + destruct (VF_isZero (VF_wf x1)); auto.
      destruct x1; simpl in *.
      elim (ord_lt_irreflexive 0); auto.
      destruct n0; try discriminate.
      destruct (VF_isZero x1_1); try discriminate.
Qed.

Theorem VF_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct (VF_wf x) (VF_wf y)
                                 (VF_wf_well_formed x)
                                 (VF_wf_well_formed y)).
  destruct (VF_compare (VF_wf x) (VF_wf y)).
  - intros.
    do 2 rewrite VF_wf_eq in H.
    left; auto.
  - intros.
    do 2 rewrite VF_wf_eq in H.
    right; auto. apply H.
  - intros.
    do 2 rewrite VF_wf_eq in H.
    right; auto with ord.
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

Lemma VF_isNormal_no_redex: forall x, VF_isNormal x <-> ~exists y, one_step_reduce x y.
Proof.
  induction x; simpl.
  - intuition.
    inversion H0.
    inversion H1; subst.
    inversion H2.
  - split.
    + rewrite IHx1. rewrite IHx2.
      intros [Hn1 [Hn2 H]] [z Hz].
      inversion Hz; subst.
      * inversion H0; subst.
        ** destruct x2; [ discriminate |].
           generalize (nat_compare_correct (S n0) n). intro Hcomp.
           destruct (nat_compare (S n0) n).
           *** simpl in H.
               elim (ord_lt_irreflexive 0).
               rewrite <- H at 2.
               apply veblen_nonzero; auto with ord.
           *** subst. destruct x2_1.
               **** elim Hn2.
                    exists (V n0 (V 0%nat Z x2_2) Z).
                    apply reduce_redex.
                    apply redex_VZ.
               **** elim (ord_lt_irreflexive 0).
                    rewrite <- H at 2.
                    apply veblen_nonzero; auto with ord.
           *** elim (ord_lt_irreflexive 0). apply H.
        ** generalize (nat_compare_correct n n). intro Hcomp.
           destruct (nat_compare n n); try lia.
           elim (ord_lt_irreflexive (VF_denote x1)).
           eapply ord_lt_le_trans; [ | apply H ]; auto.
        ** generalize (nat_compare_correct n n0). intro Hcomp.
           destruct (nat_compare n n0); try lia.
           elim (ord_lt_irreflexive (VF_denote x1)).
           eapply ord_lt_le_trans; [ | apply H ]; assumption.
        ** lia.
      * apply Hn1. eauto.
      * apply Hn2. eauto.
    + intro Hz.
      repeat split.
      * rewrite IHx1.
        intro. apply Hz. apply one_step_cong_helper1. auto.
      * rewrite IHx2.
        intro. apply Hz. apply one_step_cong_helper2. auto.
      * destruct x2 as [| m a b].
        ** destruct x1 as [| r c d].
           *** destruct n; auto.
               elim Hz. econstructor.
               apply reduce_redex.
               apply redex_VZ.
           *** generalize (nat_compare_correct n r). intro Hcomp.
               destruct (nat_compare n r); try lia.
               destruct c.
               **** destruct r; try lia.
                    elim Hz. econstructor.
                    apply reduce_cong1.
                    apply reduce_redex.
                    apply redex_VZ.
               **** elim Hz. econstructor.
                    apply reduce_redex.
                    apply redex_Vmn2; auto.
                    discriminate.
        ** generalize (nat_compare_correct n m). intro Hcomp.
           destruct (nat_compare n m).
           *** destruct (VF_decide_order x1 (V m a b)); auto.
               destruct a.
               **** destruct m; try lia.
                    elim Hz. econstructor.
                    apply reduce_cong2.
                    apply reduce_redex.
                    apply redex_VZ.
               **** elim Hz. econstructor.
                    apply reduce_redex.
                    apply redex_Vmn1; auto.
                    discriminate.
           *** subst.
               destruct (VF_decide_order x1 a); auto.
               elim Hz. econstructor.
               apply reduce_redex.
               apply redex_V; auto.
           *** destruct x1; [ | apply veblen_nonzero; auto ].
               destruct n; try lia.
               elim Hz. econstructor.
               apply reduce_redex.
               apply redex_VZ.
Qed.

Definition Vnorm m a b :=
  match b with
  | Z =>
      match a with
      | Z =>
          match m with
          | 0 => V 0 Z Z
          | S m' => V m' (V 0 Z Z) Z
          end
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
        | GT => if VF_isZero a then
                  V (pred m) (VF_onePlus b) Z
                else
                  V m a b
        end
  end.

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

Lemma Vnorm_reduce: forall m a b,
    well_formed a ->
    well_formed b ->
    clos_refl_trans VForm one_step_reduce (V m a b) (Vnorm m a b).
Proof.
  intros. unfold Vnorm.
  destruct b; simpl.
  - destruct a; simpl.
    + destruct m; simpl.
      * apply rt_refl.
      * apply rt_step.
        apply reduce_redex.
        apply redex_VZ.
    + generalize (nat_compare_correct m n); intro Hcomp.
      destruct (nat_compare m n); try apply rt_refl.
      destruct (VF_isZero a1); subst.
      * destruct n; simpl in *; try lia.
        intuition.
        destruct (VF_isZero Z); auto with ord; try discriminate.
        elim (ord_lt_irreflexive 0); auto with ord.
      * apply rt_step.
        apply reduce_redex.
        apply redex_Vmn2; auto.
        destruct a1; simpl; auto; try discriminate.
        elim (ord_lt_irreflexive 0); auto.
  - generalize (nat_compare_correct m n); intro Hcomp.
    destruct (nat_compare m n); try apply rt_refl.
    + generalize (VF_compare_correct a (V n b1 b2)); auto.
      destruct (VF_compare a (V n b1 b2)); intuition.
      destruct (VF_isZero b1); auto.
      { subst. simpl in *. intuition.
        destruct (VF_isZero Z); subst. lia.
        elim (ord_lt_irreflexive 0); auto with ord. }
      apply rt_step.
      apply reduce_redex.
      apply redex_Vmn1; auto.
      intro. subst.
      elim (ord_lt_irreflexive 0); auto with ord.
    + subst. simpl in *; intuition.
      generalize (VF_compare_correct a b1); intuition.
      destruct (VF_compare a b1); intuition.
      apply rt_step.
      apply reduce_redex.
      apply redex_V; auto.
    + destruct (VF_isZero a); subst; try apply rt_refl.
      destruct m; try lia. simpl in *.
      intuition.
      apply rt_trans with (V m (V 0 Z (V n b1 b2)) Z).
      { apply rt_step.
        apply reduce_redex.
        apply redex_VZ; auto. }
      destruct n; simpl.
      ** destruct b1; simpl.
         *** apply multi_reduce_conj1.
             apply multi_reduce_conj2.
             induction b2; simpl; try apply rt_refl.
             destruct n; simpl.
             **** destruct b2_1; simpl in *.
                  apply multi_reduce_conj2; intuition.
                  apply rt_step.
                  apply reduce_redex.
                  apply redex_V; simpl.
                  apply veblen_nonzero; auto with ord.
             **** simpl in *.
                  intuition.
                  destruct (VF_isZero b2_1); try discriminate.
                  destruct b2_1.
                  { elim (ord_lt_irreflexive 0); auto with ord. }
                  apply rt_step.
                  apply reduce_redex.
                  apply redex_Vmn1; simpl; auto with ord arith.
                  discriminate.
         *** apply rt_step.
             apply reduce_cong1.
             apply reduce_redex.
             apply redex_V. simpl.
             apply veblen_nonzero; auto with ord.
      ** destruct (VF_isZero b1); subst; auto with ord; try discriminate.
         destruct b1; simpl.
         elim (ord_lt_irreflexive 0); auto.
         apply rt_step.
         apply reduce_cong1.
         apply reduce_redex.
         apply redex_Vmn1; auto with ord arith.
         discriminate.
         simpl. apply veblen_nonzero; auto with ord.
Qed.

Lemma Vnorm_normal m a b :
  VF_isNormal a ->
  VF_isNormal b ->
  VF_isNormal (Vnorm m a b).
Proof.
  intros Ha Hb. unfold Vnorm.
  generalize (normal_well_formed a Ha); intro Ha'.
  generalize (normal_well_formed b Hb); intro Hb'.
  destruct b.
  destruct a; simpl; auto.
  - destruct m; simpl; intuition.
  - generalize (nat_compare_correct m n); simpl.
    destruct (nat_compare m n); simpl in *; intuition.
    lia.
  - simpl in *. intuition.
    generalize (nat_compare_correct m n); simpl.
    case_eq (nat_compare m n); simpl in *; intuition.
    + generalize (VF_compare_correct a (V n b1 b2)).
      destruct (VF_compare a (V n b1 b2)); simpl.
      * intuition.
      * intuition.
        rewrite H2. apply H7.
      * intuition.
        rewrite H2. auto with ord.
    + generalize (VF_compare_correct a b1).
      destruct (VF_isZero b1); subst; intuition.
      * simpl. destruct (VF_compare a Z); intuition.
        elim (ord_lt_irreflexive 0); auto.
        apply ord_le_lt_trans with (VF_denote a); auto with ord.
        simpl; intuition.
        simpl; intuition.
      * destruct (VF_compare a b1); simpl in *; intuition.
        rewrite H2. apply H6.
        rewrite H2. auto with ord.
    + destruct m; try lia. simpl.
      destruct (VF_isZero a); subst.
      * destruct (VF_isZero b1); subst; auto.
        { simpl; intuition. apply VF_onePlus_normal; auto.
          destruct b2; simpl in *; auto with ord.
          destruct n; intuition.
          - destruct b2_1; simpl in *; auto with ord.
          - destruct b2_1; simpl in *; auto with ord.
            destruct (VF_isZero Z). discriminate.
            elim (ord_lt_irreflexive 0); auto. }
        destruct n; simpl.
        ** destruct b1; simpl; intuition.
           apply VF_onePlus_normal; auto.
           destruct b2; simpl in *; intuition.
           destruct n; simpl in *; intuition.
           destruct b2_1; simpl in *; intuition.
           destruct (VF_isZero b2_1); try discriminate.
           destruct b2_1; simpl in *; intuition.
           destruct n; simpl in *; intuition.
           elim (ord_lt_irreflexive 0); auto.
           elim (ord_lt_irreflexive 0); auto.
           simpl in *; intuition.
           simpl in *; intuition.
           destruct b1_2; simpl in *; intuition.
        ** destruct b1; simpl in *; intuition.
           apply VF_onePlus_normal; auto.
           destruct b2; simpl in *; intuition.
           destruct n0; simpl in *; intuition.
           destruct b2_1; simpl in *; intuition.
           destruct b2_1; simpl in *; intuition.
           destruct (VF_isZero Z); try discriminate.
           elim (ord_lt_irreflexive 0); auto.
           elim (ord_lt_irreflexive 0); auto.
           elim (ord_lt_irreflexive 0); auto.
      * simpl; intuition.
        destruct n; simpl; intuition.
        generalize (nat_compare_correct m n); intro.
        destruct (nat_compare m n); try lia; auto.
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
    apply normal_well_formed; apply VF_normalize_isNormal.
    apply normal_well_formed; apply VF_normalize_isNormal.
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
  intros x y Hx Hy.
  generalize (normal_well_formed x Hx).
  generalize (normal_well_formed y Hy).
  revert x y Hx Hy.
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
          elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite (vtower_fin_fixpoints n m); auto.
          apply veblen_subterm1_zero_nest; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          destruct (VF_isZero b); simpl in *; auto.
          lia.
        - exfalso.
          elim (ord_lt_irreflexive (veblen (vtower_fin m) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite (vtower_fin_fixpoints m n); auto.
          apply veblen_subterm1_zero_nest; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          destruct (VF_isZero a); simpl in *; auto.
          lia. }
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

  assert (well_formed (V n x1 x2)).
  { apply normal_well_formed. simpl; auto. }

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
  assert (well_formed (V n a1 a2)).
  { apply normal_well_formed; simpl in *; intuition. }
  simpl in *.
  destruct n; simpl; auto.
  rewrite veblen_onePlus; auto with ord.
  rewrite veblen_onePlus; auto with ord.
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
    (fun x y Hx Hy => VF_compare_correct x y (normal_well_formed x Hx) (normal_well_formed y Hy))
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

Theorem VF_enum_fix_tower n: reflects VForm VF_denote VF_isNormal (ORD ==> ORD) (enum_fixpoints (vtower_fin n)) (fun a => Vnorm n (VF_onePlus Z) a).
  hnf. intros.
  hnf. repeat rewrite Vnorm_equal. split.
  - simpl. rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r.
    rewrite expOrd_zero.
    rewrite veblen_succ; auto with ord.
    transitivity (enum_fixpoints (vtower_fin n) (VF_denote a)).
    { destruct H. split; apply enum_fixpoints_monotone; auto with ord; apply H. }
    split; apply enum_fixpoints_func_mono; auto with ord.
    intros; rewrite veblen_zero; auto with ord.
    intros; rewrite veblen_zero; auto with ord.
  - hnf in H; intuition.
    apply Vnorm_normal; auto.
    apply VF_onePlus_normal.
    simpl; auto.
  - apply VF_onePlus_normal.
    simpl; auto.
  - destruct H; auto.
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
      apply veblen_interpolants_first with (vr:= fun a => Vnorm n (VF_onePlus a)); auto with ord.
      * apply VF_has_cantor_decomposition.
      * intros.
        eapply enum_fix_has_interpolants; auto with ord.
        apply VF_has_cantor_decomposition.
        intros; apply Hindn; auto with ord.
        simpl. auto with ord.
        intros. apply Hindx; auto.
        eapply ord_lt_le_trans; [ apply H5 |].
        simpl.
        apply veblen_monotone_func; auto with ord.
        intros. apply vtower_fin_succ_monotone; auto.
        intros. apply normal_inflationary; auto with ord.
        apply VF_enum_fix_tower.
      * hnf; simpl; intuition.
        rewrite Vnorm_equal; auto with ord.
        simpl.
        rewrite VF_onePlus_equal.
        rewrite veblen_enum_fixpoints; auto with ord.
        split; apply veblen_monotone_full; auto with ord.
        apply H2. apply H4.
        apply H2. apply H4.
        apply VF_onePlus_normal; auto.
        apply Vnorm_normal; auto.
        apply VF_onePlus_normal; auto.
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

Theorem VF_below_SVO : forall x:VF, x < SmallAckermannOrdinal.
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
      split; apply vtower_fin_index_monotone; auto with arith.
      left. exists 0%nat.
      simpl.
      rewrite addOrd_zero_r.
      apply succ_lt.
    + unfold SmallAckermannOrdinal.
      etransitivity.
      apply veblen_continuous_first; auto.
      apply sup_least; intro i.
      rewrite <- (sup_le _ _ (S (S (Nat.max i n)))).
      simpl.
      rewrite veblen_zero.
      rewrite enum_are_fixpoints; auto with ord.
      rewrite <- veblen_enum_fixpoints; auto with ord.
      transitivity
        (veblen (fun x : Ord => veblen (vtower_fin (Nat.max i n)) (1 + x) 0) 1 0).
      { rewrite veblen_succ; auto.
        rewrite enum_are_fixpoints; auto.
        rewrite veblen_zero.
        transitivity (veblen (vtower_fin (Nat.max i n)) (vtower_fin i 0) 0).
        { apply veblen_monotone_func; auto.
          apply vtower_fin_index_monotone; auto with arith. }
        apply veblen_monotone_first; auto.
        rewrite <- addOrd_le2.
        rewrite enum_are_fixpoints; auto.
        rewrite veblen_zero.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply vtower_fin_index_monotone; auto with arith. }
    rewrite veblen_succ; auto with ord.
    rewrite veblen_enum_fixpoints; auto with ord.
    transitivity (enum_fixpoints (fun x : Ord => veblen (enum_fixpoints (vtower_fin (Nat.max i n))) x 0) 0).
    { apply enum_fixpoints_func_mono; auto with ord.
      intros. rewrite veblen_zero.
      rewrite veblen_enum_fixpoints; auto with ord. }
    apply normal_inflationary with (f := fun x => veblen _ x 0); auto with ord.
Qed.

Theorem VF_SVO : VF ≈ SmallAckermannOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. apply VF_below_SVO.
  - unfold SmallAckermannOrdinal.
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

Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VF_has_enough_notations (EM:excluded_middle) :
  forall x, x < SmallAckermannOrdinal -> exists v:VF, v ≈ x.
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
