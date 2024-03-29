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
| V : VForm -> VForm -> VForm.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | V a x => veblen (addOrd 1) (VF_denote a) (VF_denote x)
  end.

Canonical Structure VF := ord VForm VF_denote.

Fixpoint VF_normal (x:VForm) : Prop :=
  match x with
  | Z => True
  | V a x => VF_normal a /\ VF_normal x /\
             match x with
             | Z => True
             | V b y => VF_denote a >= VF_denote b
             end
  end.

Lemma VF_complete (x:VForm) : complete (VF_denote x).
Proof.
  induction x.
  apply zero_complete.
  simpl.
  apply veblen_complete; auto.
  apply onePlus_normal.
  intros; apply addOrd_complete; auto.
  apply succ_complete; apply zero_complete.
Qed.

Lemma veblen_onePlus_complete a x :
  complete a -> complete x -> complete (veblen (addOrd 1) a x).
Proof.
  intros; apply veblen_complete; auto.
  apply onePlus_normal.
  intros; apply addOrd_complete; auto.
  apply succ_complete. apply zero_complete.
Qed.

Local Hint Resolve VF_complete onePlus_normal veblen_onePlus_complete
      succ_complete zero_complete : core.

Lemma VF_denote_shrink1 : forall a x,
  VF_denote a < VF_denote (V a x).
Proof.
  simpl; intros.
  apply ord_lt_le_trans with (veblen (addOrd 1) (VF_denote a) 0).
  - clear x.
    induction a; simpl; intuition.
    { apply veblen_nonzero; auto. }
    apply veblen_shrink_lemma; auto.
  - apply veblen_monotone; auto with ord.
    intros; apply addOrd_monotone; auto with ord.
Qed.

Lemma VF_denote_le2 : forall x a,
  VF_denote x <= VF_denote (V a x).
Proof.
  induction x; simpl; intuition.
  apply veblen_inflationary; auto.
Qed.

Lemma VF_denote_shrink2 : forall x a,
  VF_normal (V a x) ->
  VF_denote x < VF_denote (V a x).
Proof.
  induction x; simpl; intuition.
  { apply veblen_nonzero; auto. }
  apply veblen_increasing'; auto.
  apply IHx2. simpl; intuition.
Qed.

Lemma VNotation_below_ε₀ x :
  VF_denote x < ε 0.
Proof.
  induction x; simpl VF_denote.
  - rewrite ε_fixpoint.
    apply expOrd_nonzero.
  - rewrite veblen_onePlus; auto.
    apply epslion_additively_closed; auto.
    rewrite ε_fixpoint.
    apply expOrd_increasing; auto.
    apply (index_lt _ 1%nat).
Qed.

Fixpoint VF_compare (x:VForm) : VForm -> ordering :=
  fix inner (y:VForm) : ordering :=
    match x, y with
    | Z, Z  => EQ
    | Z, V _ _ => LT
    | V _ _, Z => GT
    | V a x' , V b y' =>
      match VF_compare a b with
      | LT => VF_compare x' y
      | EQ => VF_compare x' y'
      | GT => inner y'
      end
    end.

Lemma VF_compare_correct : forall x y,
    match VF_compare x y with
    | LT => VF_denote x < VF_denote y
    | EQ => VF_denote x ≈ VF_denote y
    | GT => VF_denote x > VF_denote y
    end.
Proof.
  induction x as [|a IHa x IHx].
  { destruct y as [|b y]; simpl; auto with ord.
    apply veblen_nonzero.
    apply onePlus_normal. }
  induction y as [|b IHb y IHy]; simpl.
  { apply veblen_nonzero.  apply onePlus_normal. }
  generalize (IHa b).
  destruct (VF_compare a b); intro Hab.
  - generalize (IHx (V b y)).
    destruct (VF_compare x (V b y)); intro Hxsub.
    + apply ord_lt_le_trans with (veblen (addOrd 1) (VF_denote a) (veblen (addOrd 1) (VF_denote b) (VF_denote y))).
      apply veblen_increasing; auto.
      apply veblen_fixpoints; auto.

    + transitivity (veblen (addOrd 1) (VF_denote a) (veblen (addOrd 1) (VF_denote b) (VF_denote y))).
      { split; (apply veblen_monotone; [ intros; apply addOrd_monotone; auto with ord | apply Hxsub ]). }
      apply veblen_fixpoints; auto.

    + apply ord_lt_le_trans with (VF_denote x); auto.
      apply veblen_inflationary; auto.

  - generalize (IHx y).
    destruct (VF_compare x y); intro Hxy.
    + eapply ord_lt_le_trans. apply veblen_increasing; auto. apply Hxy.
      apply veblen_monotone_first; auto.
      intros; apply addOrd_monotone; auto with ord.
      apply Hab.
    + split.
      etransitivity.
      apply veblen_monotone_first; auto.
      intros; apply addOrd_monotone; auto with ord.
      apply Hab.
      apply veblen_monotone; auto.
      intros; apply addOrd_monotone; auto with ord.
      apply Hxy.
      etransitivity.
      apply veblen_monotone_first; auto.
      intros; apply addOrd_monotone; auto with ord.
      apply Hab.
      apply veblen_monotone; auto.
      intros; apply addOrd_monotone; auto with ord.
      apply Hxy.
    + eapply ord_lt_le_trans. apply veblen_increasing; auto. apply Hxy.
      apply veblen_monotone_first; auto.
      intros; apply addOrd_monotone; auto with ord.
      apply Hab.

  - change (match (VF_compare (V a x) y) with
            | LT =>
              veblen (addOrd 1) (VF_denote a) (VF_denote x) <
              veblen (addOrd 1) (VF_denote b) (VF_denote y)
            | EQ =>
              veblen (addOrd 1) (VF_denote a) (VF_denote x)
                     ≈ veblen (addOrd 1) (VF_denote b) (VF_denote y)
            | GT =>
              veblen (addOrd 1) (VF_denote b) (VF_denote y) <
              veblen (addOrd 1) (VF_denote a) (VF_denote x)
            end).
    destruct (VF_compare (V a x) y).
    + apply ord_lt_le_trans with (VF_denote y); auto.
      apply veblen_inflationary; auto.
    + symmetry.
      transitivity
        (veblen (addOrd 1) (VF_denote b) (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
      { split; (apply veblen_monotone; [ intros; apply addOrd_monotone; auto with ord | apply IHy ]). }
      apply veblen_fixpoints; auto.
    + apply ord_lt_le_trans with (veblen (addOrd 1) (VF_denote b) (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
      apply veblen_increasing; auto.
      apply veblen_fixpoints; auto.
Qed.

Theorem V_decide_order (x y:VF) : {x < y} + {x ≥ y}.
Proof.
  simpl sz.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y); intros.
  - left; assumption.
  - right; apply H.
  - right; auto with ord.
Qed.

Theorem V_normal_forms_unique : forall x y,
  VF_normal x ->
  VF_normal y ->
  VF_denote x ≈ VF_denote y ->
  x = y.
Proof.
  induction x as [|a Ha x Hx].
  - simpl. intro y; destruct y; simpl; auto.
    intros.
    elim (ord_lt_irreflexive 0).
    rewrite H1 at 2.
    apply veblen_nonzero; auto.
  - destruct y as [|b y].
    + simpl; intros.
      elim (ord_lt_irreflexive 0).
      rewrite <- H1 at 2.
      apply veblen_nonzero; auto.
    + simpl; intuition.

      cut (VF_denote a ≈ VF_denote b /\ VF_denote x ≈ VF_denote y).
      { intros [??]. f_equal; auto. }
      clear Ha Hx.

      assert (VF_denote a ≈ VF_denote b).
      { generalize (VF_compare_correct a b).
        destruct (VF_compare a b); intros; auto.
        * elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
          rewrite H1 at 2.
          rewrite <- (veblen_fixpoints _ onePlus_normal (VF_denote a) (VF_denote b) (VF_denote y)); auto.
          apply veblen_increasing; auto.
          rewrite <- H1.
          apply VF_denote_shrink2. simpl; intuition.
        * elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote b) (VF_denote y))).
          rewrite <- H1 at 2.
          rewrite <- (veblen_fixpoints _ onePlus_normal (VF_denote b) (VF_denote a) (VF_denote x)); auto.
          apply veblen_increasing; auto.
          rewrite H1.
          apply VF_denote_shrink2. simpl; intuition. }
      split; auto.

      generalize (VF_compare_correct x y).
      destruct (VF_compare x y); intros; auto.
      * elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote a) (VF_denote x))).
        rewrite H1 at 2.
        apply ord_le_lt_trans with (veblen (addOrd 1) (VF_denote b) (VF_denote x)).
        apply veblen_monotone_first; auto.
        intros; apply addOrd_monotone; auto with ord.
        apply H4.
        apply veblen_increasing; auto.
      * elim (ord_lt_irreflexive (veblen (addOrd 1) (VF_denote b) (VF_denote y))).
        rewrite <- H1 at 2.
        apply ord_le_lt_trans with (veblen (addOrd 1) (VF_denote a) (VF_denote y)).
        apply veblen_monotone_first; auto.
        intros; apply addOrd_monotone; auto with ord.
        apply H4.
        apply veblen_increasing; auto.
Qed.

Definition Vnorm (a x:VForm) :=
  match x with
  | Z => V a Z
  | V b y =>
    match VF_compare a b with
    | GT => V a (V b y)
    | EQ => V a (V b y)
    | LT => V b y
    end
  end.

Lemma Vnorm_normal a x :
  VF_normal a -> VF_normal x -> VF_normal (Vnorm a x).
Proof.
  unfold Vnorm; simpl; intros.
  destruct x; simpl in *; intuition.
  generalize (VF_compare_correct a x1).
  destruct (VF_compare a x1); simpl; intuition.
  rewrite H2. reflexivity.
Qed.

Lemma Vnorm_V a x : VF_denote (V a x) ≈ VF_denote (Vnorm a x).
Proof.
  simpl. unfold Vnorm.
  destruct x; simpl; try reflexivity.
  generalize (VF_compare_correct a x1).
  destruct (VF_compare a x1); simpl; intuition.
  apply veblen_fixpoints; auto.
Qed.

Fixpoint Vnormalize (x:VForm) : VForm :=
  match x with
  | Z => Z
  | V a y => Vnorm (Vnormalize a) (Vnormalize y)
  end.

Lemma Vnormalize_normal : forall x, VF_normal (Vnormalize x).
Proof.
  induction x; simpl; intuition.
  apply Vnorm_normal; auto.
Qed.

Lemma Vnormalize_equal : forall x, VF_denote (Vnormalize x) ≈ VF_denote x.
Proof.
  induction x; simpl; intuition.
  rewrite <- Vnorm_V. simpl.
  transitivity (veblen (addOrd 1) (VF_denote x1) (VF_denote (Vnormalize x2))).
  - split; apply veblen_monotone_first; auto with ord.
    intros; apply addOrd_monotone; auto with ord.
    apply IHx1.
    intros; apply addOrd_monotone; auto with ord.
    apply IHx1.
  - split; apply veblen_monotone; auto with ord.
    intros; apply addOrd_monotone; auto with ord.
    apply IHx2.
    intros; apply addOrd_monotone; auto with ord.
    apply IHx2.
Qed.

Fixpoint VF_decompose (x:VForm) : list VForm :=
  match x with
  | Z => []
  | V a b => a :: VF_decompose b
  end.

Fixpoint VF_recompose (xs:list VForm) : VForm :=
  match xs with
  | [] => Z
  | x::xs' => V x (VF_recompose xs')
  end.

Lemma VF_decompose_correct:
  forall x,
    VF_normal x ->
    each VF_normal (VF_decompose x) /\
    cantor_ordered VF_denote (VF_decompose x) /\
    VF_denote x ≈ cantor_denote VF_denote (VF_decompose x).
Proof.
  induction x; simpl; intuition.
  destruct x2; simpl; auto.
  rewrite veblen_onePlus; auto.
  rewrite H8. reflexivity.
Qed.

Lemma VF_recompose_correct:
  forall xs,
    each VF_normal xs ->
    cantor_ordered VF_denote xs ->
    VF_normal (VF_recompose xs) /\ cantor_denote VF_denote xs ≈ VF_denote (VF_recompose xs).
Proof.
  induction xs; simpl in *; intuition.
  destruct xs; simpl; intuition.
  rewrite veblen_onePlus; auto with ord.
  rewrite H5.
  reflexivity.
Qed.

Definition VF_has_cantor_decomposition : has_cantor_decomposition VF_denote VF_normal :=
  Build_has_cantor_decomposition
    VF_denote
    VF_normal
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

Theorem VF_reflects_zero : reflects VForm VF_denote VF_normal ORD 0 Z.
Proof.
  simpl; auto with ord.
Qed.

Theorem VF_reflects_one : reflects VForm VF_denote VF_normal ORD 1 VF_one.
Proof.
  simpl.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite expOrd_zero.
  intuition.
Qed.

Theorem VF_succ_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD) succOrd VF_succ.
Proof.
  apply cantor_succ_reflects.
Qed.

Theorem VF_add_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) addOrd VF_add.
Proof.
  apply cantor_add_reflects.
Qed.

Theorem VF_mul_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) mulOrd VF_mul.
Proof.
  apply cantor_mul_reflects.
Qed.

Theorem VF_exp_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) expOrd VF_exp.
Proof.
  apply cantor_exp_reflects.
Qed.

Theorem VF_reflects_expOmega : reflects VForm VF_denote VF_normal (ORD ==> ORD) (expOrd ω) VF_expOmega.
Proof.
  simpl; intuition.
  rewrite veblen_onePlus; auto.
  rewrite addOrd_zero_r.
  rewrite H0.
  reflexivity.
Qed.

Theorem VF_ε₀ : VF ≈ ε 0.
Proof.
  split.
  - rewrite ord_le_unfold; intro x.
    apply VNotation_below_ε₀.
  - apply ε0_least_exp_closed with VF_normal Z VF_succ VF_expOmega.
    intro x. exists (Vnormalize x).
    split. symmetry. apply Vnormalize_equal.
    apply Vnormalize_normal.
    apply VF_reflects_zero.
    apply VF_succ_reflects.
    apply VF_reflects_expOmega.
Qed.

Theorem VF_has_all_interpolants:
  has_all_interpolants VF_denote VF_normal.
Proof.
  intro x.
  induction x as [x Hindx] using (size_induction VF).
  intros Hnorm.
  destruct x as [|a b].
  { rewrite has_interpolants_unfold.
    intros i Hi. rewrite ord_lt_unfold in Hi. destruct Hi as [[] _]. }

  apply veblen_interpolants 
    with (f:=VF_denote) (P:=VF_normal) (g:=addOrd 1) (a:=a) (b:=VF_denote b) (vr:=Vnorm); auto.
  - apply VF_has_cantor_decomposition.
  - intros. apply onePlus_interpolants with (zr:=Z) (pr:=VF_add VF_one); auto.
    apply VF_reflects_zero.
    hnf; intros; auto.
    apply VF_add_reflects; simpl in *; intuition.
    rewrite veblen_zero. rewrite addOrd_zero_r.
    reflexivity.
  - hnf; simpl; intuition.
    rewrite <- Vnorm_V. simpl; auto.
    apply veblen_onePlus_eq_mor; auto.
    apply Vnorm_normal; auto.
  - simpl in Hnorm; intuition.
  - intros; apply Hindx; auto.
    simpl. apply VF_denote_shrink1.
    simpl in Hnorm; intuition.
  - apply Hindx; auto.
    apply VF_denote_shrink2; auto.
    simpl in Hnorm; intuition.
Qed.


Definition VF_nadd := cantor_nadd VF_has_cantor_decomposition.

Theorem VF_reflects_nadd: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) naddOrd VF_nadd.
Proof.
  apply cantor_nadd_reflects.
  apply VF_has_all_interpolants.
Qed.

Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VF_has_enough_notations (EM:excluded_middle) :
  forall x:Ord, x < ε 0 -> exists c:VF, c ≈ x.
Proof.
  intros x H.
  rewrite <- VF_ε₀ in H.
  assert (HVF: has_enough_notations VF_denote VF_normal).
  { apply has_interpolants_has_enough_notations with (A:=VForm) (f:=VF_denote) (P:=VF_normal); auto.
    apply VF_has_all_interpolants. }
  hnf in HVF.
  rewrite ord_lt_unfold in H.
  destruct H as [a Ha].
  destruct (HVF (Vnormalize a) x) as [c [Hc1 Hc2]].
  apply Vnormalize_normal.
  rewrite Vnormalize_equal. auto.
  exists c; auto.
Qed.


Theorem VF_has_enough_notations' (EM:excluded_middle) :
  forall x:Ord, x < ε 0 -> exists c:VF, x ≈ c.
Proof.
  induction x as [x Hx] using ordinal_induction. intro H.
  destruct (classical.ordinal_discriminate EM x) as [Hzero|[Hsucc|Hlimit]].
  - (* Zero ordinal, exhibit Z *)
    exists Z. simpl.
    apply ord_isZero in Hzero. auto.

  - (* Successor ordinal *)
    apply ord_isSucc in Hsucc.
    destruct Hsucc as [o Ho].

    (* invoke the induction hypothesis *)
    destruct (Hx o) as [vo Hvo].
    rewrite Ho. apply succ_lt.
    transitivity x; auto.
    rewrite Ho. apply succ_lt.

    (* exhibit the successor V form and wrap up *)
    exists (VF_succ (Vnormalize vo)).
    rewrite Ho.
    apply VF_succ_reflects; auto.
    simpl. rewrite Hvo.
    split. symmetry. apply Vnormalize_equal.
    apply Vnormalize_normal.

  - (* x is a limit, it must be a fixpoint of (addOrd 1) *)
    assert (Hlimit' : 1 + x <= x).
    { apply limit_onePlus; auto. }

    (* x cannot be an ε number, as it would be too large *)
    assert (Hepsilon: x < veblen (addOrd 1) x 0).
    { destruct (classical.order_total EM (veblen (addOrd 1) x 0) x); auto.
      elim (ord_lt_irreflexive (ε 0)).
      apply ord_le_lt_trans with x; auto.
      unfold ε. simpl.
      apply fixOrd_least; auto.
      apply normal_monotone. apply powOmega_normal.
      rewrite ord_le_unfold; intros [].
      rewrite veblen_onePlus in H0; auto.
      rewrite addOrd_zero_r in H0. auto.
      apply classical.ord_complete; auto.
    }

    (* decompose the ordinal *)
    destruct (veblen_decompose EM (addOrd 1) (onePlus_normal) x) as [a [b [Hab[_[Ha Hb]]]]]; auto.

    (* invoke the induction hypotheses *)
    destruct (Hx a) as [va Hva]; auto.
    transitivity x; auto.
    destruct (Hx b) as [vb Hvb]; auto.
    transitivity x; auto.

    (* exhibit the V form and wrap up *)
    exists (V va vb).
    rewrite Hab. simpl; symmetry.
    transitivity (veblen (addOrd 1) a (VF_denote vb)).
    split; apply veblen_monotone_first; auto.
    apply normal_monotone; auto.
    apply Hva.
    apply normal_monotone; auto.
    apply Hva.
    split; apply veblen_monotone; auto.
    apply normal_monotone; auto.
    apply Hvb.
    apply normal_monotone; auto.
    apply Hvb.
Qed.
