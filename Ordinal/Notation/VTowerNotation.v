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
From Ordinal Require Import VTower.
From Ordinal Require Import Classical.

From Ordinal Require Import Notation.CantorDecomposition.


Open Scope ord_scope.

Local Hint Resolve
      vtower_normal
      vtower_complete
      vtower_monotone
      veblen_complete
      normal_complete
      normal_monotone
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

Notation vtower := (vtower (addOrd 1)).

Add Parametric Morphism : vtower
  with signature ord_le ==> ord_le ==> ord_le as vtower_le_mor.
Proof.
  intros; apply vtower_monotone; auto.
Qed.

Add Parametric Morphism : vtower
  with signature ord_eq ==> ord_eq ==> ord_eq as vtower_eq_mor.
Proof.
  unfold ord_eq; intuition.
Qed.

Add Parametric Morphism n : (veblen (vtower n))
    with signature ord_le ==> ord_le ==> ord_le
      as veblen_vtower_fin_le_mor.
Proof.
  intros.
  apply veblen_le_mor; auto with ord.
Qed.

Add Parametric Morphism n : (veblen (vtower n))
    with signature ord_eq ==> ord_eq ==> ord_eq
      as veblen_vtower_fin_eq_mor.
Proof.
  intros.
  apply veblen_eq_mor; auto with ord.
Qed.


Inductive VForm : Set :=
| Z : VForm
| V : VForm -> VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | V n a x => veblen (vtower (VF_denote n)) (VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Lemma VF_denote_complete : forall x, complete (VF_denote x).
Proof.
  induction x; auto with ord.
  simpl.
  apply veblen_complete; auto.
Qed.

Local Hint Resolve VF_denote_complete : core.

Theorem V_collapse :
  forall m n a b x,
    VF_denote m ≈ VF_denote n ->
    VF_denote a < VF_denote b ->
    VF_denote (V m a (V n b x)) ≈ VF_denote (V n b x).
Proof.
  intros. simpl.
  transitivity
    (veblen (vtower (VF_denote n)) (VF_denote a)
            (veblen (vtower (VF_denote n)) (VF_denote b) (VF_denote x))).
  split; apply veblen_monotone_func; auto with ord.
  intros; apply vtower_monotone; auto with ord. apply H.
  intros; apply vtower_monotone; auto with ord. apply H.
  apply veblen_fixpoints; auto.
Qed.

Theorem VZ_collapse :
  forall n n' x,
    VF_denote n ≈ succOrd (VF_denote n') ->
    VF_denote (V n Z x) ≈ VF_denote (V n' (V Z Z x) Z).
Proof.
  simpl; intros.
  rewrite veblen_zero.
  rewrite veblen_zero.
  rewrite vtower_zero.
  rewrite H.
  rewrite vtower_succ; auto.
  reflexivity.
Qed.

Theorem Vmn_collapse : forall n m a b c,
  (VF_denote m < VF_denote n) ->
  (limitOrdinal (VF_denote n) \/ 0 < VF_denote b) ->
  VF_denote a < VF_denote (V n b c) ->
  VF_denote (V m a (V n b c)) ≈ VF_denote (V n b c).
Proof.
  intros.
  split.
  - apply veblen_vtower_collapse; auto.
  - apply veblen_inflationary; auto.
Qed.

Theorem Vmn_collapse2 : forall n m b c,
  (VF_denote m < VF_denote n) ->
  (limitOrdinal (VF_denote n) \/ 0 < VF_denote b) ->
  VF_denote (V m (V n b c) Z) ≈ VF_denote (V n b c).
Proof.
  intros. simpl. split.
  - simpl. apply veblen_vtower_strongly_critical; auto.
  - apply (normal_inflationary (fun x => veblen (vtower (VF_denote m)) x 0)); auto.
Qed.


Lemma veblen_tower_epsilon :
  forall n x y,
    complete n ->
    complete x ->
    complete y ->
    n > 0 ->
    (limitOrdinal n \/ x > 0) ->
    expOrd ω (veblen (vtower n) x y) ≈ veblen (vtower n) x y.
Proof.
  intros.
  split.
  - transitivity (veblen (vtower 0) (veblen (vtower n) x y) 0).
    rewrite veblen_vtower_zero; auto. rewrite addOrd_zero_r. auto with ord.
    apply veblen_vtower_strongly_critical; auto.
  - apply normal_inflationary; auto.
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
  simpl. rewrite H. reflexivity.
Qed.

Lemma VF_compare_eq m n a x b y :
  VF_compare m n = EQ ->
  VF_compare (V m a x) (V n b y) =
  match VF_compare a b with
  | LT => VF_compare x (V n b y)
  | EQ => VF_compare x y
  | GT => VF_compare (V m a x) y
  end.
Proof.
  intros. simpl. rewrite H.
  reflexivity.
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
  intros. simpl. rewrite H. reflexivity.
Qed.

Definition stableVTerm m a :=
  m = Z \/ limitOrdinal (VF_denote m) \/ VF_denote a > 0.

Fixpoint VF_isNormal (x:VForm) : Prop :=
  match x with
  | Z => True
  | V m a b => VF_isNormal m /\
               VF_isNormal a /\
               VF_isNormal b /\
               stableVTerm m a /\

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


Lemma VF_compare_correct :
  forall x y,
    VF_isNormal x ->
    VF_isNormal y ->
    match VF_compare x y with
    | LT => VF_denote x < VF_denote y
    | EQ => VF_denote x ≈ VF_denote y
    | GT => VF_denote x > VF_denote y
    end.
Proof.
  induction x as [|m Hm a Ha x Hx]; intros y Hlx Hly.
  - destruct y as [|n b y].
    + simpl. reflexivity.
    + simpl. apply veblen_nonzero; auto.
  - induction y as [|n Hn b Hb y Hy].
    + simpl. apply veblen_nonzero; auto.
    + simpl in Hlx; destruct Hlx as [Hlx1 [Hlx2 [Hlx3 [Hlx4 Hlx5]]]].
      simpl in Hly; destruct Hly as [Hly1 [Hly2 [Hly3 [Hly4 Hly5]]]].
      generalize (Hm n Hlx1 Hly1).
      case_eq (VF_compare m n). intros Hcompare Hmn.
      * rewrite VF_compare_lt; auto.
        generalize (Ha (V n b y) Hlx2).
        destruct (VF_compare a (V n b y)); intros.
        ** generalize (Hx (V n b y) Hlx3).
           destruct (VF_compare x (V n b y)); intros.
           *** simpl.
               apply veblen_collapse'; auto.
               apply H; simpl; auto.
               apply H0; simpl; auto.
               apply Vmn_collapse2; auto.
               destruct (VF_isZero b); auto.
               assert (VF_denote b ≈ 0).
               { subst b; auto with ord. }
               left. clear -Hly4 Hmn H1.
               hnf in Hly4.
               intuition; subst; simpl in *.
               elim (ord_lt_irreflexive 0).
               apply ord_le_lt_trans with (VF_denote m); auto with ord.
               elim (ord_lt_irreflexive 0).
               rewrite <- H1 at 2. auto.

           *** simpl. split.
               { apply veblen_collapse; auto.
                 apply H; simpl; auto.
                 apply H0; simpl; auto.
                 apply Vmn_collapse2; auto.
                 destruct (VF_isZero b); auto.
                 assert (VF_denote b ≈ 0).
                 { subst b; auto with ord. }
                 left. clear -Hly4 Hmn H1.
                 hnf in Hly4.
                 intuition; subst; simpl in *.
                 elim (ord_lt_irreflexive 0).
                 apply ord_le_lt_trans with (VF_denote m); auto with ord.
                 elim (ord_lt_irreflexive 0).
                 rewrite <- H1 at 2. auto.
               }
               { simpl in H0. rewrite <- H0; simpl; auto. apply veblen_inflationary; auto. }
           *** simpl.
               simpl in H0.
               eapply ord_lt_le_trans; [ apply H0; simpl; auto |].
               apply veblen_inflationary; auto.
        ** destruct (VF_isZero x); subst; simpl.
           split.
           *** rewrite H; auto.
               apply Vmn_collapse2; auto.
               destruct (VF_isZero b); auto.
               assert (VF_denote b ≈ 0).
               { subst b; auto with ord. }
               left. clear -Hly4 Hmn H0.
               hnf in Hly4.
               intuition; subst; simpl in *.
               elim (ord_lt_irreflexive 0).
               apply ord_le_lt_trans with (VF_denote m); auto with ord.
               elim (ord_lt_irreflexive 0).
               rewrite <- H0 at 2; auto.
               simpl; intuition.

           *** rewrite H. simpl.
               apply (normal_inflationary (fun q => veblen (vtower (VF_denote m)) q 0)).
               apply veblen_first_normal; auto.
               apply veblen_complete; auto.
               simpl; intuition.

           *** apply ord_le_lt_trans with
                   (veblen (vtower (VF_denote m)) (VF_denote a) 0).
               rewrite H.
               simpl.
               apply (normal_inflationary (fun q => veblen (vtower (VF_denote m)) q 0)).
               apply veblen_first_normal; auto.
               apply veblen_complete; auto.
               simpl; intuition.
               apply veblen_increasing'; auto with ord.

        ** apply ord_lt_le_trans with (VF_denote a).
           apply H; simpl; auto.
           simpl.
           transitivity (veblen (vtower (VF_denote m)) (VF_denote a) 0).
           apply (normal_inflationary (fun i => veblen (vtower (VF_denote m)) i 0)); auto.
           apply veblen_monotone; auto with ord.

      * intros Hcompare Hmn.
        rewrite VF_compare_eq.
        assert (VF_denote (V n b y) ≈ VF_denote (V m b y)).
        { simpl; split; apply veblen_monotone_func; auto.
          intros; apply vtower_monotone; auto with ord.
          apply Hmn.
          intros; apply vtower_monotone; auto with ord.
          apply Hmn. }

        change (ordering_correct
                  (match VF_compare a b with
                   | LT => VF_compare x (V n b y)
                   | EQ => VF_compare x y
                   | GT => VF_compare (V m a x) y
                   end)
                  (VF_denote (V m a x)) (VF_denote (V n b y))).
        rewrite H.
        simpl.
        apply veblen_compare_correct; auto.
        apply Ha; auto.
        apply Hx; auto.
        rewrite <- H.
        apply Hx; auto.
        simpl; intuition.
        apply Hy; auto.
        auto.

      * intros.
        rewrite VF_compare_gt; auto.
        generalize (Hb Hly2).
        destruct (VF_compare (V m a x) b); intros.
        ** intros.
           apply ord_lt_le_trans with (VF_denote b); auto.
           simpl.
           transitivity (veblen (vtower (VF_denote n)) (VF_denote b) 0).
           apply (normal_inflationary (fun i => veblen (vtower (VF_denote n)) i 0)); auto.
           apply veblen_monotone; auto with ord.
        ** destruct (VF_isZero y); subst; simpl.
           split.
           *** rewrite <- H1.
               simpl.
               apply (normal_inflationary (fun q => veblen (vtower (VF_denote n)) q 0)).
               apply veblen_first_normal; auto.
               apply veblen_complete; auto.

           *** rewrite <- H1.
               apply Vmn_collapse2; auto.
               destruct (VF_isZero a); auto.
               assert (VF_denote a ≈ 0).
               { subst; auto with ord. }
               left. clear -Hlx4 H0 H2.
               hnf in Hlx4.
               intuition; subst; auto.
               elim (ord_lt_irreflexive 0).
               apply ord_le_lt_trans with (VF_denote n); auto with ord.
               elim (ord_lt_irreflexive 0).
               rewrite <- H2 at 2; auto with ord.

           *** apply ord_le_lt_trans with (veblen (vtower (VF_denote n)) (VF_denote b) 0).
               rewrite <- H1.
               apply (normal_inflationary (fun i => veblen (vtower (VF_denote n)) i 0)); auto.
               apply normal_increasing; auto.

        ** generalize (Hy Hly3).
           destruct (VF_compare (V m a x) y); intros.
           *** apply ord_lt_le_trans with (VF_denote y); auto.
               simpl.
               apply normal_inflationary; auto.
           *** split.
               { rewrite H2. simpl. apply normal_inflationary; auto. }
               simpl. apply veblen_collapse; auto.
               apply H2.
               apply Vmn_collapse2; auto.
               destruct (VF_isZero a); auto.
               assert (VF_denote a ≈ 0).
               { subst; auto with ord. }
               left. clear -Hlx4 H0 H3.
               hnf in Hlx4.
               intuition; subst; auto.
               elim (ord_lt_irreflexive 0).
               apply ord_le_lt_trans with (VF_denote n); auto with ord.
               elim (ord_lt_irreflexive 0).
               rewrite <- H3 at 2; auto with ord.

           *** simpl.
               apply veblen_collapse'; auto.
               apply Vmn_collapse2; auto.
               destruct (VF_isZero a); auto.
               assert (VF_denote a ≈ 0).
               { subst; auto with ord. }
               left. clear -Hlx4 H0 H3.
               hnf in Hlx4.
               intuition; subst; auto.
               elim (ord_lt_irreflexive 0).
               apply ord_le_lt_trans with (VF_denote n); auto with ord.
               elim (ord_lt_irreflexive 0).
               rewrite <- H3 at 2; auto with ord.
Qed.

Definition subterm_shrink x :=
  match x with
  | Z => True
  | V m a b => VF_denote m < VF_denote (V m a b) /\
               VF_denote a < VF_denote (V m a b) /\
               VF_denote b < VF_denote (V m a b)
  end.

Lemma normal_subterm_shrink : forall x, VF_isNormal x -> subterm_shrink x.
Proof.
  induction x; simpl; auto.
  intros [?[?[?[??]]]].
  - destruct x3; subst.
    destruct x2; subst.
    + simpl. repeat split; try (apply veblen_nonzero; auto).
      rewrite veblen_zero.
      hnf in H2.
      intuition; subst.
      * apply normal_nonzero; auto.
      * destruct x1; simpl in H4; intuition; try discriminate.
        { apply normal_nonzero; auto. }
        simpl.
        apply veblen_collapse'; auto.
        eapply ord_lt_le_trans; [ apply H4 | ].
        apply (normal_inflationary (fun q => vtower q 0)); auto.
        apply vtower_first_normal; auto.
        eapply ord_lt_le_trans; [ apply H9 | ].
        apply (normal_inflationary (fun q => vtower q 0)); auto.
        apply vtower_first_normal; auto.
        rewrite <- (vtower_fixpoint _ onePlus_normal (succOrd (VF_denote x1_1))) at 2; auto.
        rewrite vtower_succ; auto.
        apply veblen_monotone_first; auto.
        apply addOrd_le2.
        rewrite ord_isLimit in H2.
        destruct H2.
        destruct (H8 (VF_denote x1_1)) as [k [??]]; auto.
        apply ord_le_lt_trans with k; auto.
        apply succ_least; auto.
      * elim (ord_lt_irreflexive 0); auto.
    + clear H2; simpl.
      repeat split; try (apply veblen_nonzero; auto).
      * rewrite <- (veblen_fixpoints _ (vtower_normal _ onePlus_normal (VF_denote x1) (VF_denote_complete x1)) 0); auto.
        rewrite veblen_zero.
        apply ord_le_lt_trans with (vtower (VF_denote x1) 0).
        apply (normal_inflationary (fun q => vtower q 0)); auto.
        apply vtower_first_normal; auto.
        apply normal_increasing; auto.
        apply veblen_nonzero; auto.
        apply veblen_nonzero; auto.
      * destruct (IHx2 H0) as [?[??]].
        apply ord_le_lt_trans with
            (veblen (VTower.vtower (addOrd 1) (VF_denote x1))
                    (VF_denote x2_2) (VF_denote x2_3)).
        { apply veblen_mono_func; auto with ord. }
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + destruct (IHx3 H1) as [?[??]].
      repeat split.
      * apply ord_le_lt_trans with (veblen (VTower.vtower (addOrd 1) (VF_denote x1)) (VF_denote x2) 0).
        { rewrite veblen_unroll.
          rewrite <- lub_le1.
          apply (normal_inflationary (fun q => vtower q 0)); auto.
          apply vtower_first_normal; auto. }
        apply veblen_increasing; auto.
        simpl; apply veblen_nonzero; auto.
      * apply ord_le_lt_trans with (veblen (VTower.vtower (addOrd 1) (VF_denote x1)) (VF_denote x2) 0).
        apply (normal_inflationary (fun q => veblen (vtower (VF_denote x1)) q 0)); auto.
        apply veblen_increasing; auto.
        simpl; apply veblen_nonzero; auto.
      * simpl.
        destruct H1 as [?[?[?[??]]]].
        generalize (VF_compare_correct x1 x3_1 H H1).
        destruct (VF_compare x1 x3_1); intros; subst.
        ** (* LT case *)
          rewrite H3 at 1.
          apply veblen_subterm1; auto with ord.
          apply veblen_nonzero; auto.
        ** (* EQ case *)
          apply ord_le_lt_trans with
              (veblen (vtower (VF_denote x1)) (VF_denote x3_2) (VF_denote x3_3)).
          apply veblen_monotone_func; auto.
          intros; apply vtower_monotone; auto with ord.
          apply H11; auto.
          apply veblen_increasing'; auto.
        ** (* GT case *)
          apply veblen_collapse'; auto.
          eapply ord_lt_le_trans; [ apply H5 |].
          apply veblen_inflationary; auto.
          eapply ord_lt_le_trans; [ apply H6 |].
          apply veblen_inflationary; auto.
          apply (Vmn_collapse2 x1 x3_1 x2 (V x3_1 x3_2 x3_3)); auto with ord.
          clear -H2 H11.
          hnf in H2.
          intuition; subst.
          elim (ord_lt_irreflexive 0).
          apply ord_le_lt_trans with (VF_denote x3_1); auto with ord.
Qed.

Lemma vtower_limit_lemma :
  forall x y z w,
    complete w ->
    limitOrdinal (vtower (VF_denote (V x y z)) w).
Proof.
  intros.
  destruct z.
  2: { apply vtower_gt_one_limit; auto.
       apply ord_le_lt_trans with (VF_denote (V x y Z)).
       apply succ_least. simpl; apply veblen_nonzero; auto.
       simpl. apply normal_increasing; auto.
       apply veblen_nonzero; auto. }
  destruct y.
  2: { apply vtower_gt_one_limit; auto.
       apply ord_le_lt_trans with (VF_denote (V x Z Z)).
       apply succ_least. simpl; apply veblen_nonzero; auto.
       simpl.
       apply (normal_increasing (fun q => veblen (vtower (VF_denote x)) q 0)); auto.
       apply veblen_nonzero; auto. }
  destruct x.
  2: { apply vtower_gt_one_limit; auto.
       simpl.
       rewrite veblen_zero.
       apply ord_le_lt_trans with (vtower 0 0).
       apply succ_least. rewrite vtower_unroll.
       rewrite <- lub_le1.
       rewrite <- addOrd_le1.
       auto with ord.
       apply (normal_increasing (fun q => vtower q 0)); auto.
       apply vtower_first_normal; auto.
       apply veblen_nonzero; auto. }
  simpl.
  rewrite veblen_zero.
  rewrite vtower_zero.
  rewrite addOrd_zero_r.
  apply vtower_one_limit; auto.
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
  induction x; simpl; intuition.
  destruct x1.
  simpl; auto.
  simpl in *; intuition.
  destruct x1; simpl; auto.
  split; auto.
  destruct x3; simpl; auto.
  destruct x3_1; simpl in *; auto.
  destruct x1; simpl.

  - transitivity (veblen (addOrd 1) (VF_denote x2) (VF_denote x3)).
    { split; apply veblen_monotone_func; auto with ord.
      intros. rewrite vtower_zero; auto with ord.
      intros. rewrite vtower_zero; auto with ord. }
    rewrite veblen_onePlus; auto with ord.
    rewrite H13. reflexivity.

  -  symmetry.
     rewrite addOrd_zero_r.
     apply veblen_tower_epsilon; auto.
     apply veblen_nonzero; auto.
     hnf in H2. intuition.
     discriminate.
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
  hnf. auto.
  simpl in *; intuition.
  destruct a1; simpl in *; intuition.
  hnf; auto.
  hnf; auto.
  destruct xs; simpl in *; intuition.
  destruct v; simpl in *; intuition.
  destruct v1; simpl in *; intuition.
  destruct xs; simpl in *; intuition.
  destruct a; simpl in *; intuition.
  rewrite veblen_vtower_zero; auto with ord.
  destruct a1; simpl; auto.
  rewrite veblen_vtower_zero; auto with ord.
  rewrite veblen_vtower_zero; auto with ord.
  rewrite addOrd_zero_r.
  apply veblen_tower_epsilon; auto.
  apply veblen_nonzero; auto.
  hnf in H7; intuition.
  discriminate.
  rewrite veblen_vtower_zero; auto.
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
    VF_denote_complete
    VF_compare_correct
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

Fixpoint VF_onePlus (x:VForm) :=
  match x with
  | Z => V Z Z Z
  | V Z Z x' => V Z Z (VF_onePlus x')
  | _ => x
  end.

Lemma VF_onePlus_normal : forall x, VF_isNormal x -> VF_isNormal (VF_onePlus x).
Proof.
  induction x; simpl; intuition.
  { hnf; auto. }
  destruct x1; simpl in *; intuition.
  destruct x2; simpl in *; intuition.
  destruct x3; simpl in *; intuition.
  destruct x3_1; auto.
  destruct x3_2; auto.
Qed.

Lemma VF_onePlus_correct x : VF_denote (VF_onePlus x) ≈ 1 + VF_denote x.
Proof.
  induction x; simpl.
  - rewrite veblen_vtower_zero; auto.
    rewrite addOrd_zero_r.
    rewrite addOrd_zero_r.
    rewrite expOrd_zero.
    reflexivity.
  - destruct x1; simpl.
    + destruct x2; simpl.
      rewrite veblen_vtower_zero; auto.
      rewrite expOrd_zero.
      rewrite veblen_zero.
      rewrite vtower_zero.
      rewrite IHx3. reflexivity.
      rewrite onePlus_veblen; auto with ord.
      apply veblen_nonzero; auto.
    + split. apply addOrd_le2.
      apply limit_onePlus.
      apply veblen_limit; auto.
      intros. apply vtower_limit_lemma; auto.
Qed.


Definition Vnorm m a b :=
  match b with
  | Z => match a with
         | Z => match cantor_succ_test VF_has_cantor_decomposition m with
                | None => V m Z Z
                | Some m' => V m' (V Z Z Z) Z
                end
         | V o _ _ => match VF_compare m o with
                      | LT => a
                      | _  => V m a Z
                      end
         end

  | V n x y => match VF_compare m n with
               | LT => match VF_compare a b with
                       | LT => b
                       | _  => V m a b
                       end
               | EQ => match VF_compare a x with
                       | LT => b
                       | _  => V m a b
                       end
               | GT => if VF_isZero a then
                         match cantor_succ_test VF_has_cantor_decomposition m with
                         | Some m' => V m' (VF_onePlus b) Z
                         | None    => V m a b
                         end
                       else
                         V m a b
               end
  end.

Global Opaque VF_onePlus.

Lemma Vnorm_equal m a b :
  VF_isNormal m ->
  VF_isNormal a ->
  VF_isNormal b ->
  VF_denote (Vnorm m a b) ≈ VF_denote (V m a b).
Proof.
  unfold Vnorm; intros.
  destruct b; simpl.
  - destruct a; simpl in *; auto with ord.
    + generalize (cantor_succ_test_correct VF_has_cantor_decomposition m H).
      destruct (cantor_succ_test VF_has_cantor_decomposition m).
      * simpl; intuition.
        rewrite veblen_zero.
        rewrite veblen_zero.
        rewrite <- H4.
        rewrite vtower_succ; auto.
        rewrite vtower_zero.
        reflexivity.
      * simpl; intros.
        reflexivity.

    + destruct H0 as [?[?[?[??]]]].
      generalize (VF_compare_correct m a1 H H0).
      destruct (VF_compare m a1); simpl; intros; auto.
      * destruct H4; intros.
        ** subst a1.
           elim (ord_lt_irreflexive 0).
           apply ord_le_lt_trans with (VF_denote m); auto with ord.
        ** symmetry. apply Vmn_collapse2; auto.
      * reflexivity.
      * reflexivity.

  - generalize (VF_compare_correct m b1 H).
    destruct (VF_compare m b1); intuition.
    + generalize (VF_compare_correct a (V b1 b2 b3) H0 H1).
      destruct (VF_compare a (V b1 b2 b3)); simpl in *; intros; try reflexivity.
      symmetry. apply Vmn_collapse; auto. apply H2; tauto.
      unfold stableVTerm in H1; intuition; subst.
      elim (ord_lt_irreflexive 0).
      apply ord_le_lt_trans with (VF_denote m); auto with ord.
    + generalize (VF_compare_correct a b2 H0).
      destruct (VF_compare a b2); simpl; intuition.
      symmetry. apply V_collapse; simpl in *; intuition.
    + destruct (VF_isZero a).
      * subst a. simpl.
        generalize (cantor_succ_test_correct VF_has_cantor_decomposition m H).
        destruct (cantor_succ_test VF_has_cantor_decomposition m).
        simpl; intuition.
        rewrite veblen_zero.
        rewrite (VF_onePlus_correct (V b1 b2 b3)); auto.
        rewrite <- H5.
        rewrite vtower_succ; auto.
        reflexivity.
        reflexivity.
      * reflexivity.
Qed.

Lemma Vnorm_normal m a b :
  VF_isNormal m ->
  VF_isNormal a ->
  VF_isNormal b ->
  VF_isNormal (Vnorm m a b).
Proof.
  unfold Vnorm; intros.
  destruct b; simpl.
  - destruct a; simpl in *.
    + generalize (cantor_succ_test_correct VF_has_cantor_decomposition m H).
      destruct (cantor_succ_test VF_has_cantor_decomposition m); intuition.
      * simpl; intuition.
        hnf; auto.
        hnf. right. right. apply veblen_nonzero; auto.
      * simpl; intuition.
        hnf; auto.
        destruct m; auto.
        right. left.
        apply unreachable_limit; auto.
        apply veblen_nonzero; auto.
    + destruct H0 as [?[?[?[??]]]].
      generalize (VF_compare_correct m a1 H H0).
      destruct (VF_compare m a1); intros; simpl; repeat split; auto with ord.
      right. right.
      apply veblen_nonzero; auto.
      apply H6.
      right. right.
      apply veblen_nonzero; auto.

  - generalize (VF_compare_correct m b1 H).
    destruct (VF_compare m b1); simpl in *; intros; repeat split.
    + generalize (VF_compare_correct a (V b1 b2 b3) H0 H1).
      destruct (VF_compare a (V b1 b2 b3)); simpl in *; intuition.
      * hnf.
        right. right. rewrite H3.
        apply veblen_nonzero; auto.
      * generalize (VF_compare_correct m b1 H).
        destruct (VF_compare m b1); intuition.
        apply H3.
        rewrite H3.
        transitivity (veblen (vtower (VF_denote b1)) (VF_denote b2) 0).
        apply (normal_inflationary (fun i => veblen (vtower (VF_denote b1)) i 0)); auto.
        apply normal_monotone; auto with ord.
      * hnf. right. right.
        eapply ord_le_lt_trans; [ | apply H3 ]; auto with ord.
      * generalize (VF_compare_correct m b1 H H4).
        destruct (VF_compare m b1); auto with ord.
        intros.
        elim (ord_lt_irreflexive (VF_denote m)).
        rewrite H2 at 2; auto.
    + simpl in H1; intuition.
      generalize (VF_compare_correct a b1 H0 H3).
      destruct (VF_compare a b1); simpl; intuition.
      * generalize (VF_compare_correct a b2 H0 H1).
        destruct (VF_compare a b2).
        ** simpl; intuition.
        ** simpl; intuition.
           { hnf; hnf in H5; intuition.
             subst.
             elim (ord_lt_irreflexive 0).
             apply ord_le_lt_trans with (VF_denote a); auto with ord.
             rewrite H6; auto.
             rewrite H8; auto. }
           generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros; auto.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           apply H8.
        ** simpl; intuition.
           { hnf; hnf in H5; intuition.
             subst.
             elim (ord_lt_irreflexive 0).
             apply ord_le_lt_trans with (VF_denote a); auto with ord.
             rewrite H6; auto.
             right. right.
             eauto with ord. }
           generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros; auto.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           auto with ord.
      * generalize (VF_compare_correct a b2 H0 H1).
        destruct (VF_compare a b2); simpl; intuition.
        ** hnf in H5. hnf.
           rewrite H8. rewrite H6.
           intuition subst.
           destruct m; auto.
           elim (ord_lt_irreflexive 0).
           simpl in H6. rewrite <- H6 at 2.
           apply veblen_nonzero; auto.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros; auto.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           apply H8.
        ** hnf in H5. hnf.
           right. right.
           apply ord_le_lt_trans with (VF_denote b2); auto with ord.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros; auto.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           auto with ord.
      * generalize (VF_compare_correct a b2 H0 H1).
        destruct (VF_compare a b2); simpl; intuition.
        ** hnf. rewrite H8. rewrite H6.
           hnf in H5; intuition.
           subst.
           destruct m; auto.
           elim (ord_lt_irreflexive 0).
           simpl in H6. rewrite <- H6 at 2.
           apply veblen_nonzero; auto.

        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros; auto.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           apply H8.
        ** hnf. right. right.
           apply ord_le_lt_trans with (VF_denote b2); auto with ord.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros; auto.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           auto with ord.
    + simpl in *; intuition.
      destruct (VF_isZero a); subst.
      * generalize (cantor_succ_test_correct VF_has_cantor_decomposition m H).
        destruct (cantor_succ_test VF_has_cantor_decomposition m); intuition.
        **
           hnf. intuition.
           apply VF_onePlus_normal; auto.
           hnf. intuition.
           hnf; right. right.
           rewrite (VF_onePlus_correct (V b1 b2 b3)); auto.

           Transparent VF_onePlus.
           simpl.
           destruct b1; simpl; auto.
           destruct b2; simpl; auto with ord.
           rewrite <- H9 in H6.
           rewrite ord_lt_unfold in H6.
           destruct H6; auto.
        ** hnf; intuition.
           hnf; intuition.
           destruct m; auto.
           hnf; auto.
           hnf. right. left.
           apply unreachable_limit; auto.
           simpl. apply veblen_nonzero; auto.
           generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intuition.
           elim (ord_lt_irreflexive (VF_denote b1)); auto.
           transitivity (VF_denote m); auto.
           elim (ord_lt_irreflexive (VF_denote b1)); auto.
           rewrite <- H8 at 2. auto.
      * simpl; intuition.
        { hnf; auto. }
        generalize (VF_compare_correct m b1 H H3).
        destruct (VF_compare m b1); intuition.
        elim (ord_lt_irreflexive (VF_denote b1)); auto.
        transitivity (VF_denote m); auto.
        elim (ord_lt_irreflexive (VF_denote b1)); auto.
        rewrite <- H2 at 2. auto.
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

Theorem VF_normalize_equal : forall x, VF_denote (VF_normalize x) ≈ VF_denote x.
Proof.
  induction x; simpl; auto with ord.
  rewrite Vnorm_equal; simpl; auto.
  transitivity (veblen (vtower (VF_denote (VF_normalize x1))) (VF_denote x2) (VF_denote x3)).
  apply veblen_eq_mor; auto.
  split; apply veblen_monotone_func; auto.
  intros; apply vtower_monotone; auto with ord.
  apply IHx1.
  intros; apply vtower_monotone; auto with ord.
  apply IHx1.

  apply VF_normalize_isNormal.
  apply VF_normalize_isNormal.
  apply VF_normalize_isNormal.
Qed.

Theorem VF_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct (VF_normalize x) (VF_normalize y)
                                 (VF_normalize_isNormal x)
                                 (VF_normalize_isNormal y)).
  destruct (VF_compare (VF_normalize x) (VF_normalize y)).
  - intros.
    do 2 rewrite VF_normalize_equal in H.
    left; auto.
  - intros.
    do 2 rewrite VF_normalize_equal in H.
    right; auto. apply H.
  - intros.
    do 2 rewrite VF_normalize_equal in H.
    right; auto with ord.
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
      { generalize (VF_compare_correct m n H2 H).
        destruct (VF_compare m n); intros; auto.
        - exfalso.
          elim (ord_lt_irreflexive (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (Vmn_collapse2 n m b y); auto.
          simpl.
          apply veblen_subterm1_zero_nest; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; auto.
          destruct H7; auto.
          subst n.
          elim (ord_lt_irreflexive 0).
          apply ord_le_lt_trans with (VF_denote m); auto with ord.

        - exfalso.
          elim (ord_lt_irreflexive (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (Vmn_collapse2 m n a x); auto.
          simpl.
          apply veblen_subterm1_zero_nest; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          rewrite H1.
          apply (normal_subterm_shrink (V n b y)); simpl; auto.
          destruct H6; auto.
          subst m.
          elim (ord_lt_irreflexive 0).
          apply ord_le_lt_trans with (VF_denote n); auto with ord.
      }
      subst n.
      assert (a = b).
      { apply Ha; auto.
        destruct (VF_decide_order a b).
        { elim (ord_lt_irreflexive (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (V_collapse m m a b y); auto with ord.
          simpl.
          apply veblen_increasing; auto with ord.
          rewrite <- H1.
          apply (normal_subterm_shrink (V m a x)); simpl; intuition.
        }
        destruct (VF_decide_order b a).
        { elim (ord_lt_irreflexive (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
          rewrite H1 at 1.
          rewrite <- (V_collapse m m b a x); auto with ord.
          simpl.
          apply veblen_increasing; auto with ord.
          rewrite H1.
          apply (normal_subterm_shrink (V m b y)); simpl; intuition. }
        split; auto. }
      subst b.
      f_equal.
      apply Hx; auto.
      destruct (VF_decide_order x y).
      { elim (ord_lt_irreflexive (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
        rewrite H1 at 2.
        apply veblen_increasing'; auto with ord. }
      destruct (VF_decide_order y x).
      { elim (ord_lt_irreflexive (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
        rewrite H1 at 1.
        apply veblen_increasing'; auto with ord. }
      split; auto.
Qed.

Theorem VF_below_LVO : forall x:VF, x < LargeVeblenOrdinal.
Proof.
  generalize LVO_limit.
  rewrite ord_isLimit.
  intros [Hz Hl].
  induction x; simpl; auto.

  apply veblen_collapse'; auto.
  apply LVO_complete.

  unfold LargeVeblenOrdinal at 2.
  rewrite normal_fixpoint; auto.
  rewrite <- (vtower_fixpoint _ onePlus_normal (succOrd (sz x1)) LargeVeblenOrdinal 0); auto.
  rewrite vtower_succ; auto.
  apply veblen_monotone_first; auto.
  transitivity (1+LargeVeblenOrdinal).
  apply addOrd_le2.
  apply addOrd_monotone; auto with ord.
  unfold LargeVeblenOrdinal at 1.
  rewrite normal_fixpoint; auto with ord.
  apply vtower_first_normal; auto.
  apply vtower_complete; auto.
  apply LVO_complete.
  apply LVO_complete.

  destruct (Hl (sz x1)) as [k [??]]; auto.
  apply ord_le_lt_trans with k; auto.
  apply succ_least; auto.
  apply vtower_first_normal; auto.
Qed.

Lemma VF_complete : complete VF.
Proof.
  simpl; intuition.
  - hnf; simpl; intros.
    destruct (VF_decide_order a1 a2).
    exists a2; split; auto with ord.
    exists a1; split; auto with ord.
  - left. exact (inhabits Z).
Qed.

Theorem VF_LVO : VF ≈ LargeVeblenOrdinal.
Proof.
  split.
  { rewrite ord_le_unfold. apply VF_below_LVO. }

  unfold LargeVeblenOrdinal.
  apply normal_fix_least; auto with ord.
  apply vtower_first_normal; auto.
  apply VF_complete.

  rewrite (sup_succ_lim VForm VF_denote) at 1.
  transitivity (supOrd (fun x => vtower (succOrd (VF_denote x)) 0)).
  apply (normal_continuous (fun x => vtower x 0)); auto.
  apply vtower_first_normal; auto.
  exact Z.
  apply (directed_monotone VF); auto with ord.
  intros. apply succ_monotone; auto.
  apply VF_complete.

  apply sup_least; intro x.
  rewrite vtower_succ; auto.
  apply ord_lt_le.
  rewrite ord_lt_unfold.
  exists (V x (V Z Z Z) Z).
  simpl.
  rewrite veblen_vtower_zero; auto.
  rewrite expOrd_zero.
  reflexivity.
Qed.

Definition VF_one := V Z Z Z.
Definition VF_two := V Z Z (V Z Z Z).
Definition VF_expOmega x := V Z x Z.
Definition VF_omega      := V Z VF_one Z.
Definition VF_epsilon x  := V VF_one VF_one x.
Definition VF_Gamma x    := V VF_two VF_one x.
Definition VF_SVO        := V VF_omega Z Z.

Lemma VF_one_correct : VF_denote VF_one ≈ 1.
Proof.
  simpl. rewrite veblen_zero.
  rewrite vtower_zero.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Lemma VF_two_correct : VF_denote VF_two ≈ 2.
Proof.
  simpl.
  rewrite veblen_vtower_zero; auto.
  rewrite veblen_vtower_zero; auto.
  rewrite addOrd_zero_r.
  rewrite expOrd_zero.
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.


Lemma VF_succ_correct x : VF_isNormal x -> VF_denote (VF_succ x) ≈ succOrd (VF_denote x).
Proof.
  unfold VF_succ.
  symmetry.
  apply cantor_succ_reflects.
  simpl; auto with ord.
Qed.

Lemma VF_expOmega_correct x : VF_denote (VF_expOmega x) ≈ expOrd ω (VF_denote x).
Proof.
  simpl.
  rewrite veblen_vtower_zero; auto.
  rewrite addOrd_zero_r. reflexivity.
Qed.

Lemma VF_omega_correct : VF_denote (VF_omega) ≈ ω.
Proof.
  transitivity (VF_denote (VF_expOmega VF_one)).
  reflexivity.
  rewrite VF_expOmega_correct.
  rewrite VF_one_correct.
  rewrite expOrd_one'; auto with ord.
  apply omega_gt0.
Qed.

Opaque VF_one.
Opaque VF_two.
Opaque VF_omega.

Lemma VF_epsilon_correct x : VF_denote (VF_epsilon x) ≈ ε (VF_denote x).
Proof.
  simpl.
  transitivity
     (veblen (VTower.vtower (addOrd 1) 1) 1 (VF_denote x)).
  split; apply veblen_monotone_full; auto with ord.
  intros; apply vtower_monotone; auto with ord.
  apply VF_one_correct.
  apply VF_one_correct.
  intros; apply vtower_monotone; auto with ord.
  apply VF_one_correct.
  apply VF_one_correct.
  rewrite veblen_succ; auto with ord.
  unfold ε.
  transitivity (enum_fixpoints (fun i => powOmega (1+i)) (VF_denote x)).
  split; apply enum_fixpoints_func_mono; auto with ord.
  apply compose_normal.
  apply powOmega_normal.
  apply onePlus_normal.
  intros.
  rewrite veblen_zero; auto.
  rewrite vtower_succ; auto.
  rewrite veblen_vtower_zero; auto.
  rewrite addOrd_zero_r. reflexivity.
  apply compose_normal.
  apply powOmega_normal.
  apply onePlus_normal.
  intros.
  rewrite veblen_zero; auto.
  rewrite vtower_succ; auto.
  rewrite veblen_vtower_zero; auto.
  rewrite addOrd_zero_r. reflexivity.
  split.
  - generalize (VF_denote_complete x).
    generalize (VF_denote x).
    induction o as [A f Hind].
    intros.
    apply enum_least.
    apply compose_normal.
    apply powOmega_normal.
    apply onePlus_normal.
    apply enum_fixpoints_complete; auto.
    intros. apply normal_inflationary; auto with ord.
    rewrite enum_are_fixpoints at 2; auto.
    apply expOrd_monotone; auto.
    rewrite enum_are_fixpoints at 2; auto.
    apply onePlus_least_normal; auto.
    apply enum_fixpoints_complete; auto.
    intros. apply normal_inflationary; auto with ord.
    intros.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [a ?].
    apply ord_le_lt_trans with (enum_fixpoints (fun i : Ord => powOmega (1 + i)) (f a)).
    apply enum_fixpoints_monotone; auto.
    rewrite (Hind a); auto.
    apply enum_fixpoints_increasing; auto with ord.
    apply H.
  - apply enum_fixpoints_func_mono; auto with ord.
    apply compose_normal.
    apply powOmega_normal.
    apply onePlus_normal.
    intros. apply expOrd_monotone; auto.
    apply addOrd_le2.
Qed.

Lemma VF_Gamma_correct x : VF_denote (VF_Gamma x) ≈ Γ (VF_denote x).
Proof.
  simpl.
  transitivity (veblen (vtower 2) 1 (VF_denote x)).
  split; apply veblen_monotone_full; auto with ord.
  intros. rewrite VF_two_correct. reflexivity.
  apply VF_one_correct.
  intros. rewrite VF_two_correct. reflexivity.
  apply VF_one_correct.
  rewrite veblen_succ; auto.
  unfold Γ.
  transitivity (enum_fixpoints (fun b : Ord => veblen powOmega (1+b) 0) (VF_denote x)).
  { split; apply enum_fixpoints_func_mono; auto with ord.
    intros.
    rewrite veblen_zero.
    rewrite vtower_succ; auto.
    transitivity (veblen (fun i => powOmega (1+i)) (1+x0) 0).
    apply veblen_monotone_func; auto.
    apply compose_normal.
    apply powOmega_normal.
    apply onePlus_normal.
    intros. rewrite vtower_succ; auto.
    rewrite veblen_vtower_zero; auto.
    rewrite addOrd_zero_r. reflexivity.
    rewrite veblen_func_onePlus; auto with ord.

    intros.
    rewrite veblen_zero.
    rewrite vtower_succ; auto.
    transitivity (veblen (fun i => powOmega (1+i)) (1+x0) 0).
    rewrite veblen_func_onePlus; auto with ord.
    apply veblen_monotone_func; auto.
    apply compose_normal.
    apply powOmega_normal.
    apply onePlus_normal.
    intros. rewrite vtower_succ; auto.
    rewrite veblen_vtower_zero; auto.
    rewrite addOrd_zero_r. reflexivity. }
  split.
  - generalize (VF_denote_complete x).
    generalize (VF_denote x).
    induction o as [A f Hind].
    intros.
    apply enum_least.
    apply (compose_normal (fun o => veblen powOmega o 0) (addOrd 1)).
    apply veblen_first_normal.
    apply powOmega_normal.
    apply onePlus_normal.
    apply enum_fixpoints_complete; auto.
    intros. apply (normal_inflationary (fun o => veblen powOmega o 0)); auto with ord.
    intros; apply veblen_monotone_first; auto.
    rewrite enum_are_fixpoints at 2; auto.
    apply veblen_monotone_first; auto.
    rewrite enum_are_fixpoints at 2; auto.
    apply (onePlus_least_normal (fun o => veblen powOmega o 0)).
    apply veblen_first_normal.
    apply powOmega_normal.
    apply enum_fixpoints_complete; auto.
    intros. apply (normal_inflationary (fun o => veblen powOmega o 0)); auto with ord.
    intros; apply veblen_monotone_first; auto.

    intros.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [a ?].
    apply ord_le_lt_trans with
        (enum_fixpoints (fun b : Ord => veblen powOmega (1 + b) 0) (f a)); auto.
    apply enum_fixpoints_monotone; auto.
    intros. apply veblen_monotone_first; auto.
    rewrite (Hind a).
    apply enum_fixpoints_increasing; auto with ord.
    intros. apply veblen_monotone_first; auto.
    apply H.
  - apply enum_fixpoints_func_mono; auto with ord.
    intros. apply veblen_monotone_first; auto.
    apply addOrd_le2.
Qed.

Lemma VF_SVO_correct : VF_denote (VF_SVO) ≈ SmallVeblenOrdinal.
Proof.
  simpl.
  rewrite veblen_zero.
  rewrite VF_omega_correct.
  symmetry.
  apply SVO_vtower.
Qed.


Lemma vtower_interpolants:
  forall a b,
    VF_isNormal a ->
    has_interpolants VF_denote VF_isNormal (VF_denote a) ->
    complete b ->
    has_interpolants VF_denote VF_isNormal b ->
    has_interpolants VF_denote VF_isNormal (vtower (VF_denote a) b).
Proof.
  induction a as [a Hinda] using (size_induction VF).
  induction b as [b Hindb] using ordinal_induction.
  intros Ha1 Ha2 Hb1 Hb2. rewrite has_interpolants_unfold. intros i Hi.
  rewrite vtower_unroll in Hi.
  apply lub_lt in Hi.
  destruct Hi as [Hi|Hi].
  - assert (has_interpolants VF_denote VF_isNormal (1 + b)).
    { apply onePlus_interpolants with Z (VF_add VF_one); auto.
      simpl; intuition.
      hnf; simpl; intros. apply VF_add_reflects; intuition.
      symmetry. apply VF_one_correct.
      Transparent VF_one. simpl; intuition.
      hnf; auto. }
    rewrite has_interpolants_unfold in H.
    destruct H with i as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
    exists y; intuition.
    rewrite vtower_unroll.
    rewrite <- lub_le1.
    auto.
  - apply sup_lt in Hi.
    destruct Hi as [j Hi].
    set (b' := limOrd (fun x : b => vtower (VF_denote a) (b x))).
    assert (Hb' : has_interpolants VF_denote VF_isNormal b').
    { unfold b'. rewrite has_interpolants_unfold.
      intros i0 Hi0.
      rewrite ord_lt_unfold in Hi0. simpl in Hi0.
      destruct Hi0 as [k Hi0].
      rewrite has_interpolants_unfold in Hb2.
      destruct (Hb2 (b k)) as [q [Hq1 [Hq2 [Hq3 Hq4]]]]; auto with ord.
      exists (Vnorm a Z q).
      intuition.
      apply Vnorm_normal; auto.
      simpl; auto.
      rewrite Vnorm_equal; auto.
      simpl.
      rewrite veblen_zero.
      rewrite Hi0.
      apply vtower_monotone; auto with ord.
      simpl; auto.
      rewrite Vnorm_equal; simpl; auto.
      rewrite ord_lt_unfold; simpl.
      rewrite ord_lt_unfold in Hq3.
      destruct Hq3 as [k' Hq3].
      exists k'.
      rewrite veblen_zero.
      apply vtower_monotone; auto with ord.
      rewrite Vnorm_equal; simpl; auto.
      rewrite veblen_zero.
      apply Hindb; auto. }
    rewrite has_interpolants_unfold in Ha2.
    destruct Ha2 with (i:=j) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto with ord.
    assert (Hi' : i < nextCritical (vtower j) (1+b) b').
    { eapply ord_lt_le_trans; [ apply Hi |].
      apply nextCritical_mono; auto with ord. }

    assert (Hcrit: has_interpolants VF_denote VF_isNormal (nextCritical (vtower (sz y)) (1+b) b')).
    { rewrite has_interpolants_unfold.
      intros k Hk.
      unfold nextCritical in Hk.
      apply sup_lt in Hk.
      destruct Hk as [q Hk].
      assert (Hb: has_interpolants VF_denote VF_isNormal (1+b)).
      { apply onePlus_interpolants with Z (VF_add VF_one); auto.
        simpl; intuition.
        hnf; simpl; intros. apply VF_add_reflects; intuition.
        symmetry. apply VF_one_correct.
        simpl; intuition.
        hnf; auto. }
      rewrite has_interpolants_unfold in Hb.
      destruct (Hb q) as [r [Hr1 [Hr2 [Hr3 Hr4]]]]; auto with ord.

      assert (Hfix: has_interpolants VF_denote VF_isNormal
                                     (fixOrd (veblen (VTower.vtower (addOrd 1) (sz y)) (sz r)) b')).
      { apply fix_has_interpolants; auto.
        + intros. apply veblen_interpolants with (Vnorm y); auto with ord.
          * apply VF_has_cantor_decomposition.
          * hnf; simpl; intuition.
            rewrite Vnorm_equal; simpl; auto with ord.
            split; apply veblen_monotone_full; auto with ord.
            apply H2. apply H4.
            apply H2. apply H4.
            apply Vnorm_normal; auto.
        + unfold b'.
          apply lim_complete.
          intros.
          apply vtower_complete; auto.
          apply complete_subord; auto.
          apply directed_monotone; auto.
          destruct b. apply Hb1. }
      rewrite has_interpolants_unfold in Hfix.
      destruct (Hfix k) as [s [Hs1 [Hs2 [Hs3 Hs4]]]]; auto.
      eapply ord_lt_le_trans; [ apply Hk | ].
      apply fixOrd_monotone_func; auto with ord.
      intros.
      apply veblen_monotone_full; auto with ord.
      exists s; intuition.
      unfold nextCritical.
      rewrite ord_lt_unfold in Hr3.
      destruct Hr3 as [z Hr3].
      rewrite <- (sup_le _ _ z).
      eapply ord_lt_le_trans; [ apply Hs3 |].
      apply fixOrd_monotone_func; auto with ord.
      intros; apply veblen_monotone_first; auto with ord.
      intros; apply veblen_monotone; auto with ord. }

    rewrite has_interpolants_unfold in Hcrit.
    destruct (Hcrit i) as [z [Hz1 [Hz2 [Hz3 Hz4]]]]; auto.
    eapply ord_lt_le_trans; [ apply Hi' |].
    apply nextCritical_mono; auto with ord.
    exists z; intuition.
    eapply ord_lt_le_trans; [ apply Hz3 | ].
    rewrite vtower_unroll.
    rewrite <- lub_le2.
    rewrite ord_lt_unfold in Hy3.
    destruct Hy3 as [zq Hy3].
    rewrite <- (sup_le _ _ zq).
    apply nextCritical_mono; auto with ord.
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
      with (f:=VF_denote) (P:=VF_isNormal) (g:=vtower (VF_denote n)) (a:=a) (b:=VF_denote b) (vr:=Vnorm n); auto.
    + apply VF_has_cantor_decomposition.
    + intros. apply vtower_interpolants; auto.
      simpl in Hnorm; intuition.
      apply Hindx.
      destruct (normal_subterm_shrink _ Hnorm); auto.
      simpl in Hnorm; intuition.
    + hnf; simpl; intuition.
      rewrite Vnorm_equal; auto with ord.
      simpl.
      split; apply veblen_monotone_full; auto with ord.
      apply H0. apply H2.
      apply H0. apply H2.
      simpl in Hnorm; intuition.
      apply Vnorm_normal; auto.
      simpl in Hnorm; intuition.
    + simpl in Hnorm; intuition.
    + apply Hindx.
      destruct (normal_subterm_shrink _ Hnorm); intuition.
      simpl in Hnorm; intuition.
    + apply Hindx.
      destruct (normal_subterm_shrink _ Hnorm); intuition.
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
  forall x, x < LargeVeblenOrdinal -> exists v:VF, v ≈ x.
Proof.
  intros x H.
  rewrite <- VF_LVO in H.
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

Local Hint Resolve classical.ord_complete : core.

Theorem VF_has_enough_notations' (EM:excluded_middle) :
  forall x, x < LargeVeblenOrdinal -> exists v:VF, v ≈ x.
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
    rewrite VF_succ_correct; auto.
    rewrite VF_normalize_equal.
    auto with ord.
    apply VF_normalize_isNormal.

  - (* limit case *)
    (* massage our x < LVO hypothesis a bit so the induction goes more smoothly *)
    assert (Hbnd : exists i, i < x /\ x < vtower i x).
    { unfold LargeVeblenOrdinal in H.
      set (P a := x < vtower a 0).
      destruct (classical.ord_well_ordered EM P LargeVeblenOrdinal) as [i Hi].
      + hnf.
        eapply ord_lt_le_trans; [ apply H |].
        rewrite (normal_fixpoint (fun q => vtower q 0)); auto.
        apply vtower_monotone; auto with ord.
        apply vtower_first_normal; auto.
      + subst P. destruct Hi as [Hi1 Hi2].
        exists i; split; auto.
        * destruct (classical.order_total EM x i); auto.
          exfalso.
          apply (ord_lt_irreflexive x).
          eapply ord_lt_le_trans; [ apply H | ].
          apply normal_fix_least; auto with ord.
          apply vtower_first_normal; auto.
          transitivity (vtower (supOrd (fun i => x i)) 0).
          apply vtower_monotone; auto with ord.
          destruct x as [X f].
          apply ascending_sup_lim. apply Hlimit.
          transitivity (supOrd (fun i => vtower (x i) 0)).
          destruct x as [X f]. destruct Hlimit as [[x0] Hl].
          apply (normal_continuous (fun q => vtower q 0)); auto.
          apply vtower_first_normal; auto.
          apply classical.ord_directed; auto.
          apply sup_least; intro j.
          destruct (classical.order_total EM (vtower (x j) 0) x); auto.
          assert (i <= x j).
          { apply Hi2; auto. }
          elim (ord_lt_irreflexive (x j)).
          apply ord_lt_le_trans with x; eauto with ord.
        * eapply ord_lt_le_trans; [ apply Hi1 | ].
          apply vtower_monotone; auto with ord.
    }

    (* inner induction goes on the number of levels in the veblen tower we need *)
    destruct Hbnd as [i [Hix Hbnd]].
    induction i as [i Hi] using ordinal_induction; intros.

    (* Classify i as zero, successor or limit *)
    destruct (classical.ordinal_discriminate EM i) as [Hz|[Hs|Hl]].

    + (* Vacuous base case. We cannot get here because
           x is a limit and veblen_tower 0 is too small. *)
      simpl in *.
      elim (ord_lt_irreflexive x).
      apply ord_lt_le_trans with (1+x); auto.
      rewrite ord_isZero in Hz. rewrite Hz in Hbnd.
      rewrite vtower_zero in Hbnd; auto.
      apply limit_onePlus; auto.

    + (* i successor case *)
      rewrite ord_isSucc in Hs.
      destruct Hs as [i' Hi'].
      rewrite Hi' in Hbnd.
      rewrite vtower_succ in Hbnd; auto.

      (* is x a fixpoint of the next lower level? *)
      destruct (classical.order_total EM (vtower i' x) x).
      * (* we have found the right level, decompose the ordinal *)
        destruct (veblen_decompose EM _ (vtower_normal _ onePlus_normal i' (classical.ord_complete EM i')) x)
          as [a [b [Hab [Ha0 [Ha Hb]]]]]; auto.
        { eapply ord_lt_le_trans; [ apply Hbnd | ].
          apply veblen_monotone_first; auto with ord.
          apply limit_onePlus; auto. }

        (* invoke the main induction hypothesis *)
        destruct (Hx i') as [vi' Hvi']; auto.
        transitivity i; auto.
        rewrite Hi'. apply succ_lt.
        transitivity i; auto.
        rewrite Hi'. apply succ_lt.
        transitivity x; auto.
        destruct (Hx a) as [va Hva]; auto.
        transitivity x; auto.
        destruct (Hx b) as [vb Hvb]; auto.
        transitivity x; auto.

        exists (V vi' va vb).
        rewrite Hab.
        simpl.
        transitivity (veblen (vtower i') (VF_denote va) (VF_denote vb)).
        split; apply veblen_monotone_func; auto with ord.
        intros; apply vtower_monotone; auto with ord.
        apply Hvi'.
        intros; apply vtower_monotone; auto with ord.
        apply Hvi'.
        apply veblen_eq_mor; auto with ord.

      * (* recursive case *)
        apply (Hi i'); auto.
        rewrite Hi'. apply succ_lt.
        transitivity i; auto.
        rewrite Hi'. apply succ_lt.

    + (* i limit case *)
      assert (exists a, x < vtower i (x a)).
      { destruct x as [X g].
        rewrite (ascending_sup_lim _ g) in Hbnd at 2; auto.
        assert (vtower i (supOrd g) <= supOrd (fun a => vtower i (g a))).
        { destruct Hlimit as [[x0] ?]. apply normal_continuous; auto.
          apply classical.ord_directed; auto. }
        rewrite H0 in Hbnd.
        apply sup_lt in Hbnd.
        destruct Hbnd as [a Ha].
        exists a. auto.
        destruct Hlimit; auto. }
      destruct H0 as [a Ha].
      set (Q a := a < x /\ x <= vtower i a).
      destruct (classical.ord_well_ordered EM Q (x a)).
      { hnf. auto with ord. }
      subst Q; simpl in *.
      destruct H0 as [[H0 H1] H2].

      destruct (classical.order_total EM (vtower i x0) x).
      * assert (x ≈ vtower i x0).
        { split; auto. }

        destruct (Hx i) as [vi Hvi]; auto.
        transitivity x; auto.
        destruct (Hx x0) as [vx0 Hvx0]; auto.
        transitivity x; auto.

        exists (V vi Z vx0).

        simpl. rewrite veblen_zero.
        rewrite H4.
        apply vtower_eq_mor; auto.

      * rewrite vtower_limit in H3; auto.
        destruct i as [I h]. simpl in H3.
        apply sup_lt in H3. destruct H3 as [i H3].
        assert ((limOrd (fun i : x0 => vtower (ord I h) (x0 i))) <= x).
        { rewrite ord_le_unfold; intro q. simpl.
          destruct (classical.order_total EM x (vtower (ord I h) (x0 q))); auto.
          elim (ord_lt_irreflexive x0).
          apply ord_le_lt_trans with (x0 q); auto with ord.
          apply H2. split; auto.
          transitivity x0; auto with ord.
        }
        rewrite H4 in H3.
        apply (Hi (h i)); auto with ord.
        transitivity (ord I h); auto with ord.
Qed.
