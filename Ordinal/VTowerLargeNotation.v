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
From Ordinal Require Import VTower.
From Ordinal Require Import Classical.

Open Scope ord_scope.

Local Hint Resolve
      classical.ord_complete
      vtower_normal
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

Section vtower.
Variable EM:ClassicalFacts.excluded_middle.

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
  apply vtower_monotone; auto with ord.
  apply vtower_monotone; auto with ord.
Qed.

Add Parametric Morphism n : (veblen (vtower n))
    with signature ord_le ==> ord_le ==> ord_le
      as veblen_vtower_fin_le_mor.
Proof.
  intros.
  apply veblen_le_mor; auto.
Qed.

Add Parametric Morphism n : (veblen (vtower n))
    with signature ord_eq ==> ord_eq ==> ord_eq
      as veblen_vtower_fin_eq_mor.
Proof.
  intros.
  apply veblen_eq_mor; auto.
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
  split; apply veblen_monotone_func; auto.
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
  (successorOrdinal (VF_denote n) -> 0 < VF_denote b) ->
  VF_denote a < VF_denote (V n b c) ->
  VF_denote (V m a (V n b c)) ≈ VF_denote (V n b c).
Proof.
  simpl VF_denote.
  intros.
  split.
  2: { apply veblen_inflationary; auto. }
  destruct (classical.order_total EM (VF_denote b) 0).
  - apply veblen_collapse; auto with ord.
    assert (VF_denote b ≈ 0).
    { split; auto with ord. }
    assert (limitOrdinal (VF_denote n)).
    { destruct (classical.ordinal_discriminate EM (VF_denote n)) as [Hz|[Hs|Hz]]; auto.
      - rewrite ord_isZero in Hz. rewrite Hz in H.
        elim (ord_lt_irreflexive 0).
        apply ord_le_lt_trans with (VF_denote m); auto with ord.
      - elim (ord_lt_irreflexive 0).
        apply ord_lt_le_trans with (VF_denote b); auto with ord. }
    rewrite H3.
    rewrite veblen_zero at 1.
    rewrite veblen_zero at 1.
    rewrite (vtower_limit EM _ onePlus_normal (VF_denote n)) at 1; auto.
    rewrite (vtower_limit EM _ onePlus_normal (VF_denote n)) at 1; auto.
    destruct (VF_denote n) as [N h]. simpl.
    destruct H4 as [[n0] Hl].
    transitivity (supOrd (fun i => veblen (vtower (VF_denote m))
                                          (vtower (h i)
                                                  (limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0)))) 0)).
    apply (normal_continuous (fun q => veblen (vtower (VF_denote m)) q 0)); auto.
    apply classical.ord_directed; auto.
    apply sup_least; intro i.
    rewrite ord_lt_unfold in H.
    destruct H as [j Hj].
    destruct (classical.ord_directed EM N h i j) as [k [??]].
    destruct (Hl k) as [k' Hk'].
    destruct (Hl k') as [k'' Hk''].
    rewrite <- (sup_le _ _ k'').
    transitivity (vtower (succOrd (succOrd (h k)))
      (limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0)))).
    rewrite vtower_succ; auto.
    rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (succOrd (h k))) 0); auto.
    rewrite veblen_zero.
    rewrite vtower_succ; auto.
    rewrite onePlus_veblen; auto.
    transitivity (veblen (vtower (h k))
                         (vtower (h i)
                                 (limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0))))
                         0).
    apply veblen_monotone_func; auto.
    intros. apply vtower_monotone; auto with ord.
    rewrite Hj; auto.
    apply veblen_monotone_first; auto.
    rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (succOrd (h k))) 0); auto.
    rewrite veblen_zero.
    apply vtower_monotone; auto.
    rewrite H. auto with ord.
    transitivity (1 + limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0))).
    apply addOrd_le2.
    apply (normal_inflationary (fun i => veblen (vtower (succOrd (h k))) i 0)); auto.
    apply vtower_monotone; auto with ord.
    apply succ_least.
    eapply ord_le_lt_trans with (h k'); auto.
    apply succ_least; auto.
  - rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote n)) 0 (VF_denote b) (VF_denote c)) at 2; auto.
    rewrite veblen_zero.
    transitivity
      (vtower (succOrd (VF_denote m))
              (veblen (vtower (VF_denote n)) (VF_denote b) (VF_denote c))).
    rewrite vtower_succ; auto.
    rewrite onePlus_veblen; auto.
    rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote m)) (VF_denote a) _ 0); auto.
    apply normal_monotone; auto.
    apply (normal_inflationary (fun i => veblen (vtower (VF_denote m)) i 0)); auto.
    apply vtower_monotone; auto with ord.
    apply succ_least. auto.
Qed.

Theorem Vmn_collapse2 : forall n m b c,
  (VF_denote m < VF_denote n) ->
  (successorOrdinal (VF_denote n) -> 0 < VF_denote b) ->
  VF_denote (V m (V n b c) Z) ≈ VF_denote (V n b c).
Proof.
  intros. simpl. split.
  - destruct (classical.order_total EM (VF_denote b) 0).
    + assert (VF_denote b ≈ 0).
      { split; auto with ord. }
      assert (limitOrdinal (VF_denote n)).
      { destruct (classical.ordinal_discriminate EM (VF_denote n)) as [Hz|[Hs|Hz]]; auto.
        - rewrite ord_isZero in Hz. rewrite Hz in H.
          elim (ord_lt_irreflexive 0).
          apply ord_le_lt_trans with (VF_denote m); auto with ord.
        - elim (ord_lt_irreflexive 0).
          apply ord_lt_le_trans with (VF_denote b); auto with ord. }
      rewrite H2.
      rewrite veblen_zero at 1.
      rewrite veblen_zero at 1.
      rewrite (vtower_limit EM _ onePlus_normal (VF_denote n)) at 1; auto.
      rewrite (vtower_limit EM _ onePlus_normal (VF_denote n)) at 1; auto.
      destruct (VF_denote n) as [N h]. simpl.
      destruct H3 as [[n0] Hl].
      transitivity (supOrd (fun i => veblen (vtower (VF_denote m)) (vtower (h i) (limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0)))) 0)).
      apply (normal_continuous (fun q => veblen (vtower (VF_denote m)) q 0)); auto.
      apply classical.ord_directed; auto.
      apply sup_least; intro i.
      rewrite ord_lt_unfold in H.
      destruct H as [j Hj].
      destruct (classical.ord_directed EM N h i j) as [k [??]].
      destruct (Hl k) as [k' Hk'].
      destruct (Hl k') as [k'' Hk''].
      rewrite <- (sup_le _ _ k'').
      transitivity (vtower (succOrd (succOrd (h k))) (limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0)))).
      rewrite vtower_succ; auto.
      rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (succOrd (h k))) 0); auto.
      rewrite veblen_zero.
      rewrite vtower_succ; auto.
      rewrite onePlus_veblen; auto.
      transitivity (veblen (vtower (h k))
                           (vtower (h i)
                                   (limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0))))
                           0).
      apply veblen_monotone_func; auto.
      intros; apply vtower_monotone; auto with ord.
      rewrite Hj; auto.
      apply veblen_monotone_first; auto.
      rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (succOrd (h k))) 0); auto.
      rewrite veblen_zero.
      apply vtower_monotone; auto with ord.
      transitivity (1 + limOrd (fun i0 : VF_denote c => vtower (ord N h) (VF_denote c i0))).
      apply addOrd_le2.
      apply (normal_inflationary (fun q => veblen (vtower (succOrd (h k))) q 0)); auto.
      apply vtower_monotone; auto with ord.
      apply succ_least.
      apply ord_le_lt_trans with (h k'); auto.
      apply succ_least. auto.

    + rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote n)) 0) at 2; auto.
      rewrite veblen_zero.
      transitivity
        (vtower (succOrd (VF_denote m))
                (veblen (vtower (VF_denote n)) (VF_denote b) (VF_denote c))).
      rewrite vtower_succ; auto.
      rewrite onePlus_veblen; auto with ord.
      apply vtower_monotone; auto with ord.
      apply succ_least; auto.
  - apply (normal_inflationary (fun x => veblen (vtower (VF_denote m)) x 0)); auto.
Qed.

Lemma veblen_tower_epsilon :
  forall n x y,
    (successorOrdinal n -> x > 0) ->
    n > 0 ->
    expOrd ω (veblen (vtower n) x y) ≈ veblen (vtower n) x y.
Proof.
  intros.
  split.
  destruct (classical.order_total EM x 0).
  - assert (x ≈ 0).
    { split; auto with ord. }
    assert (limitOrdinal n).
    { destruct (classical.ordinal_discriminate EM n) as [Hz|[Hs|Hl]].
      - rewrite ord_isZero in Hz. rewrite Hz in H0.
        elim (ord_lt_irreflexive 0); auto.
      - elim (ord_lt_irreflexive 0); auto.
        apply ord_lt_le_trans with x; auto.
      - auto. }
    rewrite H2.
    rewrite veblen_zero at 1.
    rewrite veblen_zero at 1.
    destruct n as [N h].
    rewrite vtower_limit at 1; auto.
    destruct H3 as [[n0] Hl].
    etransitivity. apply normal_continuous; auto.
    apply classical.ord_directed; auto.
    apply sup_least; intro i.
    destruct (Hl i) as [j ?].
    destruct (Hl j) as [k ?].
    rewrite (vtower_limit EM _ onePlus_normal (ord N h) y); auto.
    simpl.
    rewrite <- (sup_le _ _ k).
    transitivity (vtower (succOrd (succOrd (h i))) (limOrd (fun i0 : y => vtower (ord N h) (y i0)))).
    rewrite vtower_succ; auto.
    rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (succOrd (h i))) 0); auto.
    rewrite veblen_zero.
    transitivity (vtower 1
      (veblen (vtower (succOrd (h i)))
         (1 + limOrd (fun i0 : y => vtower (ord N h) (y i0))) 0)).
    rewrite vtower_succ; auto.
    rewrite onePlus_veblen; auto.
    rewrite veblen_vtower_zero; auto.
    rewrite addOrd_zero_r.
    apply expOrd_monotone; auto.
    rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (succOrd (h i))) 0); auto.
    rewrite veblen_zero.
    apply vtower_monotone; auto with ord.
    transitivity (1 + limOrd (fun i0 : y => vtower (ord N h) (y i0))).
    apply addOrd_le2.
    apply (normal_inflationary (fun q => veblen (vtower (succOrd (h i))) q 0)).
    apply veblen_first_normal; auto.
    apply classical.ord_complete; auto.
    apply vtower_monotone; auto with ord.
    apply succ_least. apply succ_trans. auto with ord.
    apply vtower_monotone; auto with ord.
    apply succ_least; auto.
    apply ord_le_lt_trans with (h j); auto.
    apply succ_least; auto.
    split; auto.

  - rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal n) 0) at 2; auto.
    rewrite veblen_zero.
    transitivity (vtower 1 (veblen (vtower n) x y)).
    rewrite vtower_succ; auto.
    rewrite veblen_vtower_zero; auto.
    rewrite addOrd_zero_r.
    apply expOrd_monotone.
    apply addOrd_le2.
    apply vtower_monotone; auto with ord.
    apply succ_least; auto.

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

Fixpoint VF_isNormal (x:VForm) : Prop :=
  match x with
  | Z => True
  | V m a b => VF_isNormal m /\
               VF_isNormal a /\
               VF_isNormal b /\
               (successorOrdinal (VF_denote m) -> VF_denote a > 0) /\

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
                 | GT => True (*VF_denote a > 0   V m a (V n x y)   m > n *)
                 end
               end
  end.

Inductive succSpec : VForm -> VForm -> Prop :=
  | SuccOne : succSpec (V Z Z Z) Z
  | SuccRec : forall a x s,
      (VF_denote s > 0 \/
       match a with
       | Z => True
       | V n b y => n = Z
       end) ->
      succSpec x s ->
      succSpec (V Z a x) (V Z a s)
  | SuccCollapse : forall a x,
      expOrd ω (VF_denote a) ≈ VF_denote a ->
      succSpec x Z ->
      succSpec (V Z a x) a.

Fixpoint isSucc (x:VForm) : option VForm :=
  match x with
  | Z => None
  | V Z Z Z => Some Z
  | V Z a x' =>
    match isSucc x' with
    | Some s =>
      match s with
      | Z => match a with
             | V (V _ _ _) _ _ => Some a
             | _ => Some (V Z a Z)
             end
      | _ => Some (V Z a s)
      end
    | None => None
    end
  | _ => None
  end.

Lemma isSucc_spec : forall x,
    VF_isNormal x ->
    match isSucc x with
    | Some s => succSpec x s
    | None => True
    end.
Proof.
  intro x.
  induction x; simpl; intuition.
  destruct x1; auto.
  destruct x2; auto.
  destruct x3; auto.
  apply SuccOne.
  case_eq (isSucc (V x3_1 x3_2 x3_3)); intros.
  rewrite H7 in H6.
  destruct v; auto.
  apply SuccRec; auto.
  apply SuccRec; auto.
  auto.
  destruct (isSucc x3); auto.
  destruct v.
  destruct x2_1.
  apply SuccRec; auto.

  apply SuccCollapse; auto.
  simpl.
  apply veblen_tower_epsilon.
  simpl in H; intuition.
  apply veblen_nonzero; auto.

  apply SuccRec; auto.
  left. apply veblen_nonzero; auto.
Qed.

Lemma succSpec_normal : forall x s,
    VF_isNormal x ->
    succSpec x s ->
    VF_isNormal s.
Proof.
  intros. induction H0.
  simpl; auto.
  simpl in H.
  simpl; intuition.
  destruct s.
  elim (ord_lt_irreflexive 0); auto.
  inversion H1; subst; auto.
  destruct s1; simpl; auto.
  rewrite <- H6.
  simpl.
  transitivity (veblen (vtower 0) (VF_denote s2) 0).
  apply (normal_inflationary (fun q => veblen (vtower 0) q 0)); auto.
  apply normal_monotone; auto with ord.
  destruct s.
  destruct a; auto.
  destruct x; auto.
  subst; auto with ord.

  inversion H1; subst; auto.
  destruct s1; auto.
  rewrite <- H6.
  simpl.
  transitivity (veblen (vtower 0) (VF_denote s2) 0).
  apply (normal_inflationary (fun q => veblen (vtower 0) q 0)); auto.
  apply normal_monotone; auto with ord.

  simpl in H. intuition.
Qed.

Lemma isSucc_normal : forall x,
    VF_isNormal x ->
    match isSucc x with
    | Some s => VF_isNormal s
    | None   => True
    end.
Proof.
  intros.
  generalize (isSucc_spec x H).
  destruct (isSucc x); auto.
  apply succSpec_normal; auto.
Qed.

Lemma isSucc_correct : forall x,
    VF_isNormal x ->
    match isSucc x with
    | Some s => VF_denote x ≈ succOrd (VF_denote s)
    | None   => zeroOrdinal (VF_denote x) \/ limitOrdinal (VF_denote x)
    end.
Proof.
  induction x; simpl; intros.
  - left. intros [[]].
  - destruct x1.
    destruct x2.
    destruct x3.
    + simpl.
      rewrite veblen_zero.
      rewrite vtower_zero.
      rewrite addOrd_zero_r.
      reflexivity.
    + destruct (isSucc (V x3_1 x3_2 x3_3)).
      * destruct v; simpl.
        ** rewrite IHx3.
           rewrite veblen_zero.
           rewrite vtower_zero.
           rewrite veblen_zero.
           rewrite vtower_zero.
           simpl.
           rewrite addOrd_succ.
           reflexivity.
           intuition.

        ** rewrite IHx3.
           rewrite veblen_zero.
           rewrite vtower_zero.
           rewrite veblen_zero.
           rewrite vtower_zero.
           rewrite addOrd_succ.
           reflexivity.
           intuition.

      * simpl.
        right.
        rewrite veblen_zero.
        rewrite vtower_zero.
        destruct IHx3. intuition.
        { simpl in H0. rewrite ord_isZero in H0.
          elim (ord_lt_irreflexive 0).
          rewrite <- H0 at 2. apply veblen_nonzero; auto. }
        assert (1 + veblen (vtower (VF_denote x3_1)) (VF_denote x3_2) (VF_denote x3_3) ≈
                           veblen (vtower (VF_denote x3_1)) (VF_denote x3_2) (VF_denote x3_3)).
        { split. apply limit_onePlus; auto. apply addOrd_le2. }
        rewrite H1. auto.

    + destruct (isSucc x3).
      * destruct v.
        ** destruct x2_1.
           *** simpl.
               rewrite veblen_vtower_zero; auto.
               rewrite veblen_vtower_zero; auto.
               rewrite IHx3.
               rewrite addOrd_succ.
               rewrite veblen_vtower_zero; auto.
               rewrite addOrd_zero_r.
               rewrite addOrd_zero_r.
               reflexivity.
               intuition.

           *** simpl.
               rewrite veblen_vtower_zero; auto.
               rewrite IHx3. simpl.
               rewrite addOrd_succ.
               rewrite addOrd_zero_r.
               apply succ_congruence.
               apply veblen_tower_epsilon.
               simpl; intuition.
               simpl in H.
               intuition.
               apply veblen_nonzero; auto.
               intuition.

        ** simpl.
           rewrite veblen_vtower_zero; auto.
           rewrite veblen_vtower_zero; auto.
           rewrite IHx3.
           rewrite addOrd_succ.
           reflexivity.
           intuition.

      * simpl.
        right.
        rewrite veblen_vtower_zero; auto.
        destruct IHx3. intuition.
        rewrite ord_isZero in H0.
        rewrite H0.
        rewrite addOrd_zero_r.
        apply additively_closed_limit.
        apply ord_lt_le_trans with (expOrd ω 1).
        rewrite expOrd_one'; auto.
        apply omega_gt1.
        apply omega_gt0.
        apply expOrd_monotone.
        apply succ_least. apply veblen_nonzero. auto.
        apply expOmega_additively_closed.
        apply classical.ord_complete; auto.
        apply limit_add; auto.
    + right.
      apply vtower_nonzero_limit; auto.
      simpl. apply veblen_nonzero; auto.
Qed.


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
               destruct (classical.order_total EM (VF_denote b) 0).
               **** assert (VF_denote b ≈ 0).
                    { split; auto with ord. }
                    assert (limitOrdinal (VF_denote n)).
                    { generalize (isSucc_correct n Hly1).
                      destruct (isSucc n); intros.
                      elim (ord_lt_irreflexive 0).
                      rewrite <- H2 at 2.
                      apply Hly4. rewrite ord_isSucc; eauto.
                      destruct H3; auto.
                      rewrite ord_isZero in H3.
                      rewrite H3 in Hmn.
                      elim (ord_lt_irreflexive 0).
                      eapply ord_le_lt_trans with (VF_denote m); auto with ord. }
                    rewrite H2.
                    rewrite veblen_zero at 1.
                    rewrite veblen_zero at 1.
                    rewrite ord_isLimit in H3.
                    destruct H3 as [H3 H4].
                    destruct (H4 (VF_denote m)) as [m' [??]]; auto.
                    rewrite <- (vtower_fixpoint EM _ onePlus_normal m' (VF_denote n)) at 2.
                    transitivity (vtower (succOrd (VF_denote m)) (vtower (VF_denote n) (VF_denote y))).
                    rewrite vtower_succ; auto.
                    apply veblen_monotone_first.
                    intros; apply vtower_monotone; auto with ord.
                    apply addOrd_le2.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.
                    auto.
               **** rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote n)) 0 (VF_denote b)) at 2; auto.
                    rewrite veblen_zero.
                    transitivity (vtower (succOrd (VF_denote m))
                                    (veblen (vtower (VF_denote n)) (VF_denote b) (VF_denote y))).
                    rewrite vtower_succ; auto.
                    rewrite onePlus_veblen; auto.
                    reflexivity.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.

           *** simpl. split.
               { apply veblen_collapse; auto.
                 apply H; simpl; auto.
                 apply H0; simpl; auto.
                 destruct (classical.order_total EM (VF_denote b) 0).
                 **** assert (VF_denote b ≈ 0).
                      { split; auto with ord. }
                      assert (limitOrdinal (VF_denote n)).
                      { generalize (isSucc_correct n Hly1).
                        destruct (isSucc n); intros.
                        elim (ord_lt_irreflexive 0).
                        rewrite <- H2 at 2.
                        apply Hly4. rewrite ord_isSucc; eauto.
                        destruct H3; auto.
                        rewrite ord_isZero in H3.
                        rewrite H3 in Hmn.
                        elim (ord_lt_irreflexive 0).
                        eapply ord_le_lt_trans with (VF_denote m); auto with ord. }
                      rewrite H2.
                      rewrite veblen_zero at 1.
                      rewrite veblen_zero at 1.
                      rewrite ord_isLimit in H3.
                      destruct H3 as [H3 H4].
                      destruct (H4 (VF_denote m)) as [m' [??]]; auto.
                      rewrite <- (vtower_fixpoint EM _ onePlus_normal m' (VF_denote n)) at 2.
                      transitivity (vtower (succOrd (VF_denote m)) (vtower (VF_denote n) (VF_denote y))).
                      rewrite vtower_succ; auto.
                      apply veblen_monotone_first.
                      intros; apply vtower_monotone; auto with ord.
                      apply addOrd_le2.
                      apply vtower_monotone; auto with ord.
                      apply succ_least; auto.
                      auto.
                 **** rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote n)) 0 (VF_denote b)) at 2; auto.
                      rewrite veblen_zero.
                      transitivity (vtower (succOrd (VF_denote m))
                                           (veblen (vtower (VF_denote n)) (VF_denote b) (VF_denote y))).
                      rewrite vtower_succ; auto.
                      rewrite onePlus_veblen; auto.
                      reflexivity.
                      apply vtower_monotone; auto with ord.
                      apply succ_least; auto. }
               { simpl in H0. rewrite <- H0; simpl; auto. apply veblen_inflationary; auto. }
           *** simpl.
               simpl in H0.
               eapply ord_lt_le_trans; [ apply H0; simpl; auto |].
               apply veblen_inflationary; auto.
        ** destruct (VF_isZero x); subst; simpl.
           split.
           ***
                 destruct (classical.order_total EM (VF_denote b) 0).
                 **** assert (VF_denote b ≈ 0).
                      { split; auto with ord. }
                      assert (limitOrdinal (VF_denote n)).
                      { generalize (isSucc_correct n Hly1).
                        destruct (isSucc n); intros.
                        elim (ord_lt_irreflexive 0).
                        rewrite <- H1 at 2.
                        apply Hly4. rewrite ord_isSucc; eauto.
                        destruct H2; auto.
                        rewrite ord_isZero in H2.
                        rewrite H2 in Hmn.
                        elim (ord_lt_irreflexive 0).
                        eapply ord_le_lt_trans with (VF_denote m); auto with ord. }
                      rewrite H; simpl; auto.
                      rewrite H1.
                      rewrite veblen_zero at 1.
                      rewrite veblen_zero at 1.
                      rewrite ord_isLimit in H2.
                      destruct H2 as [H2 H3].
                      destruct (H3 (VF_denote m)) as [m' [??]]; auto.
                      rewrite <- (vtower_fixpoint EM _ onePlus_normal m' (VF_denote n)) at 2.
                      transitivity (vtower (succOrd (VF_denote m)) (vtower (VF_denote n) (VF_denote y))).
                      rewrite vtower_succ; auto.
                      apply veblen_monotone_first.
                      intros; apply vtower_monotone; auto with ord.
                      apply addOrd_le2.
                      apply vtower_monotone; auto with ord.
                      apply succ_least; auto.
                      auto.
                 **** rewrite H; simpl; auto.
                      rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote n)) 0 (VF_denote b)) at 2; auto.
                      rewrite veblen_zero.
                      transitivity (vtower (succOrd (VF_denote m))
                                           (veblen (vtower (VF_denote n)) (VF_denote b) (VF_denote y))).
                      rewrite vtower_succ; auto.
                      rewrite onePlus_veblen; auto.
                      reflexivity.
                      apply vtower_monotone; auto with ord.
                      apply succ_least; auto.
           *** rewrite H. simpl.
               apply (normal_inflationary (fun q => veblen (vtower (VF_denote m)) q 0)).
               apply veblen_first_normal; auto.
               apply classical.ord_complete; auto.
               simpl; intuition.

           *** apply ord_le_lt_trans with
                   (veblen (vtower (VF_denote m)) (VF_denote a) 0).
               rewrite H.
               simpl.
               apply (normal_inflationary (fun q => veblen (vtower (VF_denote m)) q 0)).
               apply veblen_first_normal; auto.
               apply classical.ord_complete; auto.
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
               apply classical.ord_complete; auto.

           *** destruct (classical.order_total EM (VF_denote a) 0).
               **** assert (VF_denote a ≈ 0).
                    { split; auto with ord. }
                    assert (limitOrdinal (VF_denote m)).
                    { generalize (isSucc_correct m Hlx1).
                      destruct (isSucc m); intros.
                      elim (ord_lt_irreflexive 0).
                      rewrite <- H3 at 2.
                      apply Hlx4. rewrite ord_isSucc; eauto.
                      destruct H4; auto.
                      rewrite ord_isZero in H4.
                      rewrite H4 in H0.
                      elim (ord_lt_irreflexive 0).
                      eapply ord_le_lt_trans with (VF_denote n); auto with ord. }
                    rewrite <- H1. simpl.
                    rewrite H3.
                    rewrite veblen_zero at 1.
                    rewrite veblen_zero at 1.
                    rewrite ord_isLimit in H4.
                    destruct H4 as [H4 H5].
                    destruct (H5 (VF_denote n)) as [n' [??]]; auto.
                    rewrite <- (vtower_fixpoint EM _ onePlus_normal n' (VF_denote m)) at 2.
                    transitivity (vtower (succOrd (VF_denote n)) (vtower (VF_denote m) (VF_denote x))).
                    rewrite vtower_succ; auto.
                    apply veblen_monotone_first.
                    intros; apply vtower_monotone; auto with ord.
                    apply addOrd_le2.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.
                    auto.
               **** rewrite <- H1; simpl.
                    rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote m)) 0 (VF_denote a)) at 2; auto.
                    rewrite veblen_zero.
                    transitivity (vtower (succOrd (VF_denote n))
                                         (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
                    rewrite vtower_succ; auto.
                    rewrite onePlus_veblen; auto.
                    reflexivity.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.

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

               destruct (classical.order_total EM (VF_denote a) 0).
               **** assert (VF_denote a ≈ 0).
                    { split; auto with ord. }
                    assert (limitOrdinal (VF_denote m)).
                    { generalize (isSucc_correct m Hlx1).
                      destruct (isSucc m); intros.
                      elim (ord_lt_irreflexive 0).
                      rewrite <- H3 at 2.
                      apply Hlx4. rewrite ord_isSucc; eauto.
                      destruct H5; auto.
                      rewrite ord_isZero in H5.
                      rewrite H5 in H0.
                      elim (ord_lt_irreflexive 0).
                      eapply ord_le_lt_trans with (VF_denote n); auto with ord. }

                    rewrite H4.
                    rewrite veblen_zero at 1.
                    rewrite veblen_zero at 1.
                    rewrite ord_isLimit in H5.
                    destruct H5 as [H5 H6].
                    destruct (H6 (VF_denote n)) as [n' [??]]; auto.
                    rewrite <- (vtower_fixpoint EM _ onePlus_normal n' (VF_denote m)) at 2.
                    transitivity (vtower (succOrd (VF_denote n)) (vtower (VF_denote m) (VF_denote x))).
                    rewrite vtower_succ; auto.
                    apply veblen_monotone_first.
                    intros; apply vtower_monotone; auto with ord.
                    apply addOrd_le2.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.
                    auto.
               **** rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote m)) 0 (VF_denote a)) at 2; auto.
                    rewrite veblen_zero.
                    transitivity (vtower (succOrd (VF_denote n))
                                         (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
                    rewrite vtower_succ; auto.
                    rewrite onePlus_veblen; auto.
                    reflexivity.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.

           *** simpl.
               apply veblen_collapse'; auto.

               destruct (classical.order_total EM (VF_denote a) 0).
               **** assert (VF_denote a ≈ 0).
                    { split; auto with ord. }
                    assert (limitOrdinal (VF_denote m)).
                    { generalize (isSucc_correct m Hlx1).
                      destruct (isSucc m); intros.
                      elim (ord_lt_irreflexive 0).
                      rewrite <- H3 at 2.
                      apply Hlx4. rewrite ord_isSucc; eauto.
                      destruct H5; auto.
                      rewrite ord_isZero in H5.
                      rewrite H5 in H0.
                      elim (ord_lt_irreflexive 0).
                      eapply ord_le_lt_trans with (VF_denote n); auto with ord. }

                    rewrite H4.
                    rewrite veblen_zero at 1.
                    rewrite veblen_zero at 1.
                    rewrite ord_isLimit in H5.
                    destruct H5 as [H5 H6].
                    destruct (H6 (VF_denote n)) as [n' [??]]; auto.
                    rewrite <- (vtower_fixpoint EM _ onePlus_normal n' (VF_denote m)) at 2.
                    transitivity (vtower (succOrd (VF_denote n)) (vtower (VF_denote m) (VF_denote x))).
                    rewrite vtower_succ; auto.
                    apply veblen_monotone_first.
                    intros; apply vtower_monotone; auto with ord.
                    apply addOrd_le2.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.
                    auto.

               **** rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote m)) 0 (VF_denote a)) at 2; auto.
                    rewrite veblen_zero.
                    transitivity (vtower (succOrd (VF_denote n))
                                         (veblen (vtower (VF_denote m)) (VF_denote a) (VF_denote x))).
                    rewrite vtower_succ; auto.
                    rewrite onePlus_veblen; auto.
                    reflexivity.
                    apply vtower_monotone; auto with ord.
                    apply succ_least; auto.
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
  induction x; simpl; intuition.
  - destruct x3.
    destruct x2; simpl in *; intuition.
    * rewrite veblen_zero.
      destruct x1; simpl in H3; intuition.
      + simpl.
        rewrite vtower_zero.
        rewrite addOrd_zero_r.
        apply succ_lt.
      + simpl.
        apply veblen_collapse'; auto.
        eapply ord_lt_le_trans; [ apply H3 | ].
        apply (normal_inflationary (fun q => vtower q 0)); auto.
        apply vtower_first_normal; auto.
        eapply ord_lt_le_trans; [ apply H9 | ].
        apply (normal_inflationary (fun q => vtower q 0)); auto.
        apply vtower_first_normal; auto.

        rewrite <- (vtower_fixpoint EM _ onePlus_normal (succOrd (VF_denote x1_1))) at 2.
        rewrite vtower_succ; auto.
        apply veblen_monotone_first; auto.
        apply addOrd_le2.
        assert (limitOrdinal (veblen (vtower (VF_denote x1_1)) (VF_denote x1_2) (VF_denote x1_3))).
        { generalize (isSucc_correct (V x1_1 x1_2 x1_3)).
          destruct (isSucc (V x1_1 x1_2 x1_3)).
          intros.
          elim (ord_lt_irreflexive 0). apply H2.
          rewrite ord_isSucc; eauto.
          intros [?|?]; auto.
          rewrite ord_isZero in H8.
          simpl in H8.
          elim (ord_lt_irreflexive 0). rewrite <- H8 at 2.
          apply veblen_nonzero; auto. }
        rewrite ord_isLimit in H8.
        destruct H8.
        destruct (H10 (VF_denote x1_1)) as [k [??]]; auto.
        apply ord_le_lt_trans with k; auto.
        apply succ_least; auto.
    * rewrite <- (veblen_fixpoints _ (vtower_normal EM _ onePlus_normal (VF_denote x1)) 0); auto.
      rewrite veblen_zero.
      apply ord_le_lt_trans with (vtower (VF_denote x1) 0).
      apply (normal_inflationary (fun q => vtower q 0)); auto.
      apply vtower_first_normal; auto.
      apply normal_increasing; auto.
      apply veblen_nonzero; auto.
      apply veblen_nonzero; auto.
    * rewrite veblen_unroll.
      rewrite <- lub_le1.
      apply ord_le_lt_trans with (vtower (VF_denote x1) 0).
      apply (normal_inflationary (fun q => vtower q 0)); auto.
      apply vtower_first_normal; auto.
      apply normal_increasing; auto.
      apply veblen_nonzero; auto.
  - destruct x3.
    + destruct x2; simpl in *; intuition.
      * rewrite veblen_zero.
        apply normal_nonzero; auto.

      * apply ord_le_lt_trans with
            (veblen (vtower (VF_denote x1)) (VF_denote x2_2) (VF_denote x2_3)).
        apply veblen_monotone_func; auto with ord.
        intros. apply vtower_monotone; auto with ord.
        apply veblen_subterm1_zero_nest; simpl in *; intuition.
    + simpl in *.
      apply veblen_subterm1; auto with ord.
      apply veblen_nonzero; auto.
  - destruct x3; simpl in *; intuition.
    + apply veblen_nonzero; auto.
    + generalize (VF_compare_correct x1 x3_1).
      destruct (VF_compare x1 x3_1); intros; subst.
      * (* LT case *)
        rewrite H4 at 1.
        apply veblen_subterm1; auto with ord.
        apply veblen_nonzero; auto.
      * (* EQ case *)
        apply ord_le_lt_trans with
            (veblen (vtower (VF_denote x1)) (VF_denote x3_2) (VF_denote x3_3)).
        apply veblen_monotone_func; auto.
        intros; apply vtower_monotone; auto with ord.
        apply H12; auto.
        apply veblen_increasing'; auto.
      * (* GT case *)
        apply veblen_collapse'; auto.
        eapply ord_lt_le_trans; [ apply H8 |].
        apply veblen_inflationary; auto.
        eapply ord_lt_le_trans; [ apply H11 |].
        apply veblen_inflationary; auto.
        apply (Vmn_collapse2 x1 x3_1 x2 (V x3_1 x3_2 x3_3)); auto with ord.
Qed.

Global Opaque VF_compare.

Fixpoint VF_onePlus (x:VForm) :=
  match x with
  | Z => V Z Z Z
  | V Z Z x' => V Z Z (VF_onePlus x')
  | _ => x
  end.

Lemma VF_onePlus_normal : forall x, VF_isNormal x -> VF_isNormal (VF_onePlus x).
Proof.
  induction x; simpl; intuition.
  { destruct H0 as [[] ?]. }
  destruct x1; simpl in *; intuition.
  destruct x2; simpl in *; intuition.
  destruct x3; simpl in *; intuition.
  { generalize (VF_compare_correct Z Z).
    destruct (VF_compare Z Z); simpl; intuition.
    elim (ord_lt_irreflexive 0); auto.
  }
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
    + destruct x2; simpl.
      rewrite veblen_zero.
      split. apply addOrd_le2.
      apply limit_onePlus.
      apply vtower_nonzero_limit; auto.
      apply veblen_nonzero; auto.
      rewrite onePlus_veblen; auto with ord.
      apply veblen_nonzero; auto.
Qed.

Definition Vnorm m a b :=
  match b with
  | Z => match a with
         | Z => match isSucc m with
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
                         match isSucc m with
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
  - destruct a; simpl in *; intuition.
    generalize (isSucc_correct m H).
    destruct (isSucc m). simpl; intros.
    rewrite veblen_zero.
    rewrite veblen_zero.
    rewrite H2.
    rewrite vtower_succ; auto.
    rewrite vtower_zero.
    reflexivity.

    simpl; intros.
    reflexivity.

    generalize (VF_compare_correct m a1 H H2).
    destruct (VF_compare m a1); simpl; intuition.
    symmetry. apply Vmn_collapse2; auto.

  - generalize (VF_compare_correct m b1 H).
    destruct (VF_compare m b1); intuition.
    + generalize (VF_compare_correct a (V b1 b2 b3) H0 H1).
      destruct (VF_compare a (V b1 b2 b3)); simpl in *; intuition.
      symmetry. apply Vmn_collapse; auto.
    + generalize (VF_compare_correct a b2 H0).
      destruct (VF_compare a b2); simpl; intuition.
      symmetry. apply V_collapse; simpl in *; intuition.
    + destruct (VF_isZero a).
      * subst a. simpl.
        generalize (isSucc_correct m H).
        case_eq (isSucc m); intros.
        rewrite veblen_zero.
        simpl.
        rewrite VF_onePlus_correct.
        rewrite H4.
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
  - destruct a; simpl in *; intuition.
    + generalize (isSucc_normal m H).
      generalize (isSucc_correct m H).
      destruct (isSucc m); auto.
      * simpl; intuition.
        destruct H4 as [[] _].
        apply veblen_nonzero; auto.
      * simpl; intuition.
        elim (zero_not_successor (VF_denote m)); auto.
        elim (successor_not_limit (VF_denote m)); auto.
    + generalize (VF_compare_correct m a1 H H2).
      destruct (VF_compare m a1); simpl; intuition.
      apply veblen_nonzero; auto.
      apply H5.
      apply veblen_nonzero; auto.

  - generalize (VF_compare_correct m b1 H).
    destruct (VF_compare m b1); intuition.
    + generalize (VF_compare_correct a (V b1 b2 b3) H0 H1).
      destruct (VF_compare a (V b1 b2 b3)); simpl in *; intuition.
      * rewrite H3.
        apply veblen_nonzero; auto.
      * generalize (VF_compare_correct m b1 H).
        destruct (VF_compare m b1); intuition.
        apply H3.
        rewrite H3.
        transitivity (veblen (vtower (VF_denote b1)) (VF_denote b2) 0).
        apply (normal_inflationary (fun i => veblen (vtower (VF_denote b1)) i 0)); auto.
        apply normal_monotone; auto with ord.
      * eapply ord_le_lt_trans; [ | apply H3 ]; auto with ord.
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
           rewrite H8.
           apply H5.
           rewrite <- H6. auto.
           generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           apply H8.
           auto.
        ** simpl; intuition.
           rewrite H6 in H9.
           apply H5 in H9.
           transitivity (VF_denote b2); auto.
           generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           auto with ord.
           auto.
      * generalize (VF_compare_correct a b2 H0 H1).
        destruct (VF_compare a b2); simpl; intuition.
        ** rewrite H8. apply H5.
           rewrite <- H6; auto.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           apply H8.
           auto.
        ** transitivity (VF_denote b2); auto.
           apply H5.
           rewrite <- H6; auto.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           auto with ord.
           auto.
      * generalize (VF_compare_correct a b2 H0 H1).
        destruct (VF_compare a b2); simpl; intuition.
        ** rewrite H8. apply H5.
           rewrite <-  H6; auto.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           apply H8.
           auto.
        ** transitivity (VF_denote b2); auto.
           apply H5.
           rewrite <- H6; auto.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intros.
           elim (ord_lt_irreflexive (VF_denote m)).
           rewrite H6 at 2; auto.
           auto with ord.
           auto.
    + simpl in *; intuition.
      destruct (VF_isZero a); subst.
      * generalize (isSucc_correct m H).
        generalize (isSucc_normal m H).
        destruct (isSucc m); simpl; intuition.
        ** apply VF_onePlus_normal; simpl; intuition.
        ** rewrite VF_onePlus_correct.
           apply ord_lt_le_trans with 1; auto with ord.
           apply addOrd_le1.
        ** Transparent VF_onePlus.
           simpl.
           destruct b1; simpl; auto.
           destruct b2; simpl; auto with ord.
           rewrite H8 in H6.
           rewrite ord_lt_unfold in H6.
           destruct H6; auto.
        ** elim (zero_not_successor (VF_denote m)); auto.
        ** rewrite ord_isZero in H9.
           rewrite H9 in H6.
           elim (ord_lt_irreflexive (VF_denote b1)); auto.
           apply ord_lt_le_trans with 0; auto with ord.
        ** elim (successor_not_limit (VF_denote m)); auto.
        ** generalize (VF_compare_correct m b1 H H3).
           destruct (VF_compare m b1); intuition.
           elim (ord_lt_irreflexive (VF_denote b1)); auto.
           transitivity (VF_denote m); auto.
           elim (ord_lt_irreflexive (VF_denote b1)); auto.
           rewrite <- H8 at 2. auto.
      * simpl; intuition.
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

Lemma LVO_limit : limitOrdinal LargeVeblenOrdinal.
Proof.
  unfold LargeVeblenOrdinal.
  rewrite normal_fixpoint; auto.
  apply vtower_nonzero_limit; auto.
  rewrite normal_fixpoint; auto.
  apply normal_nonzero; auto.
  apply vtower_first_normal; auto.
  apply vtower_first_normal; auto.
Qed.

Theorem VF_below_LVO : forall x:VF, x < LargeVeblenOrdinal.
Proof.
  generalize LVO_limit.
  rewrite ord_isLimit.
  intros [Hz Hl].
  induction x; simpl; auto.

  apply veblen_collapse'; auto.
  unfold LargeVeblenOrdinal at 2.
  rewrite normal_fixpoint; auto.
  rewrite <- (vtower_fixpoint EM _ onePlus_normal (succOrd (sz x1)) LargeVeblenOrdinal 0).
  rewrite vtower_succ; auto.
  apply veblen_monotone_first; auto.
  transitivity (1+LargeVeblenOrdinal).
  apply addOrd_le2.
  apply addOrd_monotone; auto with ord.
  unfold LargeVeblenOrdinal at 1.
  rewrite normal_fixpoint; auto with ord.
  apply vtower_first_normal; auto.
  destruct (Hl (sz x1)) as [k [??]]; auto.
  apply ord_le_lt_trans with k; auto.
  apply succ_least; auto.
  apply vtower_first_normal; auto.
Qed.

Theorem VF_LVO : VF ≈ LargeVeblenOrdinal.
Proof.
  split.
  { rewrite ord_le_unfold. apply VF_below_LVO. }

  unfold LargeVeblenOrdinal.
  apply normal_fix_least; auto with ord.
  apply vtower_first_normal; auto.

  rewrite (sup_succ_lim VForm VF_denote) at 1.
  transitivity (supOrd (fun x => vtower (succOrd (VF_denote x)) 0)).
  apply (normal_continuous (fun x => vtower x 0)); auto.
  apply vtower_first_normal; auto.
  exact Z.
  apply classical.ord_directed; auto.
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

Fixpoint VF_add (x y:VForm) : VForm :=
  match x with
  | Z       => y
  | V Z a b => V Z a (VF_add b y)
  | _       => V Z x y
  end.

Lemma VF_add_correct x y :
  VF_isNormal x ->
  VF_denote (VF_add x y) ≈ VF_denote x + VF_denote y.
Proof.
  induction x; simpl; intros.
  - rewrite addOrd_zero_l. reflexivity.
  - destruct x1; simpl.
    + rewrite veblen_vtower_zero; auto.
      rewrite veblen_vtower_zero; auto.
      rewrite <- addOrd_assoc.
      rewrite IHx3; auto with ord.
      intuition.
    + rewrite veblen_vtower_zero; auto.
      apply addOrd_eq_mor; auto with ord.
      apply veblen_tower_epsilon; auto.
      simpl in *; intuition.
      apply veblen_nonzero; auto.
Qed.

Definition VF_one := V Z Z Z.
Definition VF_succ x := VF_add (VF_normalize x) VF_one.
(*
Definition VF_expOmega x := V O x Z.
Definition VF_epsilon x  := V 1 VF_one x.
Definition VF_Gamma x    := V 2 VF_one x.
*)

Lemma VF_one_correct : VF_denote VF_one ≈ 1.
Proof.
  simpl. rewrite veblen_zero.
  rewrite vtower_zero.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Lemma VF_succ_correct x : VF_denote (VF_succ x) ≈ succOrd (VF_denote x).
Proof.
  unfold VF_succ.
  rewrite VF_add_correct.
  rewrite VF_one_correct.
  rewrite addOrd_succ.
  apply succ_congruence.
  rewrite addOrd_zero_r.
  apply VF_normalize_equal.
  apply VF_normalize_isNormal.
Qed.

Theorem VF_has_enough_notations :
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
    exists (VF_succ vo).
    rewrite Ho. rewrite <- Hvo.
    apply VF_succ_correct.

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
        destruct (veblen_decompose EM _ (vtower_normal EM _ onePlus_normal i') x)
          as [a [b [Hab [Ha0 [Ha Hb]]]]]; auto.
        { eapply ord_lt_le_trans; [ apply Hbnd | ].
          apply veblen_monotone_first; auto.
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
        apply veblen_eq_mor; auto.

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

End vtower.
