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

Fixpoint VF_add (x y:VForm) : VForm :=
  match x with
  | Z => y
  | V a x' => V a (VF_add x' y)
  end.

Lemma VF_add_correct x y : VF_denote (VF_add x y) ≈ VF_denote x + VF_denote y.
Proof.
  induction x; simpl.
  - rewrite addOrd_zero_l. reflexivity.
  - repeat rewrite veblen_onePlus; auto.
    rewrite IHx2.
    apply addOrd_assoc.
Qed.

Definition VF_one := V Z Z.
Definition VF_succ x := VF_add x VF_one.
Definition VF_expOmega x := V x Z.

Definition VF_mul_single (x:VForm) (e:VForm) : VForm :=
  match x, e with
  (* 0 * ωᵉ = 0 *)
  | Z, _ => Z
  (* x * ω⁰ = x *)
  | _, Z => x
  (* (ωᵃ + q) * ωᵉ = ω^(a + e) otherwise *)
  | V a _, _ => V (VF_add a e) Z
  end.

Definition VF_mul x : VForm -> VForm :=
  let x' := Vnormalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | Z => Z
  | V b y' => VF_add (VF_mul_single x' b) (loop y')
  end.

Fixpoint VFIsFinite (x:VForm) : option nat :=
  match x with
  | Z => Some 0%nat
  | V Z x' =>
    match VFIsFinite x' with
    | Some n => Some (S n)
    | None => None
    end
  | _ => None
  end.

Lemma VFIsFinite_correct x :
  match VFIsFinite x with
  | Some n => VF_denote x ≈ sz n
  | None   => 1 + VF_denote x ≈ VF_denote x
  end.
Proof.
  induction x; simpl.
  - reflexivity.
  - destruct x1.
    destruct (VFIsFinite x2).
    + rewrite veblen_onePlus; auto.
      rewrite IHx2. simpl.
      rewrite expOrd_zero.
      transitivity (sz (n+1)%nat).
      rewrite natOrdSize_add. reflexivity.
      simpl.
      replace (n+1)%nat with (1+n)%nat by lia.
      simpl. reflexivity.
    + simpl.
      rewrite veblen_zero.
      rewrite IHx2.
      rewrite IHx2.
      reflexivity.
    + rewrite veblen_onePlus; auto.
      rewrite addOrd_assoc.
      apply addOrd_eq_mor; auto with ord.
      split.
      * apply additively_closed_collapse.
        apply expOmega_additively_closed; auto.
        apply ord_lt_le_trans with (expOrd ω 1).
        rewrite expOrd_one'.
        apply (index_lt _ 1%nat).
        apply (index_lt _ 0%nat).
        apply expOrd_monotone.
        apply succ_least.
        simpl. apply veblen_nonzero; auto.
      * apply addOrd_le2.
Qed.

Fixpoint VF_nat (n:nat) : VForm :=
  match n with
  | O => Z
  | S n' => VF_succ (VF_nat n')
  end.

Lemma VF_nat_correct n : sz n ≈ VF_denote (VF_nat n).
Proof.
  induction n; simpl; auto with ord.
  unfold VF_succ.
  rewrite VF_add_correct.
  unfold VF_one.
  simpl.
  rewrite veblen_zero.
  rewrite addOrd_zero_r.
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  rewrite IHn.
  reflexivity.
Qed.


(** Compute the value x^(ωᵉ). This algorithm has quite a few special cases,
    which are commented inline.
 *)
Definition VF_exp_single (x:VForm) (e:VForm) : VForm :=
  match x with

    (* 0 ^ (ω^e) = 1 *)
  | Z => VF_one

  | V x1 x2 =>
    match VFIsFinite (V x1 x2) with
    | Some 0 => VF_one  (* 0 ^ (ω^e) = 1 *)
    | Some 1 => VF_one  (* 1 ^ (ω^e) = 1 *)
    | Some n =>         (* x = n, for some finite n > 1 *)
      match VFIsFinite e with
      (* n ^ (ω^0) = n *)
      | Some 0 => x

      (* n ^ (ω^(1+m)) = ω^(ω^m) for finite n > 1, finite m *)
      | Some (S m) => VF_expOmega (VF_expOmega (VF_nat m))

      (* n ^ (ω^e) = ω^(ω^e)  for e >= ω, finite n > 1 *)
      | None => VF_expOmega (VF_expOmega e)
      end

    | None =>
      match e with
      (* x^ (ω^0) = x *)
      | Z => x

      (* (ω^x₁ + b) ^ (ω^e) = ω^(x₁ * ω^e)  when x₁ >= 1, e > 0 *)
      | V _ _ => VF_expOmega (VF_mul x1 (VF_expOmega e))

      end
    end
  end.

(** Compute xʸ. The terms on the right are used to exponentate the entire
    term on the left via VF_exp_single and all the results are multiplied together.
  *)
Definition VF_exp (x:VForm) :  VForm -> VForm :=
  let x' := Vnormalize x in
  fix loop (y:VForm) : VForm :=
  match y with
  | Z => VF_one
  | V b y' => VF_mul (VF_exp_single x' b) (loop y')
  end.


Lemma VF_normal_dominates : forall x a,
    VF_normal (V a x) ->
    exists n:ω, expOrd ω (VF_denote a) * n ≥ VF_denote x.
Proof.
  induction x; simpl; intuition.
  - exists 0%nat. auto with ord.
  - destruct x2; simpl.
    + exists 1%nat.
      simpl.
      rewrite mulOrd_one_r.
      rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      apply expOrd_monotone; auto.
    + destruct (IHx2 a) as [n Hn].
      simpl in *; intuition.
      rewrite H4. auto.
      exists (S n).
      simpl.
      rewrite mulOrd_succ.
      rewrite veblen_onePlus; auto.
      simpl in Hn. rewrite Hn.
      rewrite H2.
      clear.
      induction n; simpl.
      * rewrite mulOrd_zero_r.
        rewrite addOrd_zero_l.
        rewrite addOrd_zero_r.
        reflexivity.
      * rewrite mulOrd_succ.
        rewrite addOrd_assoc.
        apply addOrd_monotone; auto with ord.
Qed.

Lemma VF_mul_single_correct : forall x e,
    VF_normal x ->
    VF_denote (VF_mul_single x e) ≈ VF_denote x * expOrd ω (VF_denote e).
Proof.
  destruct x as [|a x]; intros; simpl.
  - rewrite mulOrd_zero_l. reflexivity.
  - destruct e as [|b y]; simpl.
    + rewrite expOrd_zero. rewrite mulOrd_one_r. reflexivity.
    + repeat rewrite veblen_onePlus; auto.
      rewrite addOrd_zero_r.
      rewrite VF_add_correct.
      split.
      rewrite expOrd_add.
      simpl. rewrite veblen_onePlus; auto.
      apply mulOrd_monotone1.
      apply addOrd_le1.

      destruct (VF_normal_dominates x a) as [n Hn]; auto.
      rewrite (expOrd_omega_collapse (expOrd ω (VF_denote a)) (VF_denote x) (expOrd ω (VF_denote b) + VF_denote y) n); auto.
      rewrite (expOrd_add ω (VF_denote a) (VF_denote (V b y))).
      simpl.
      rewrite veblen_onePlus; auto with ord.
      apply addOrd_complete; auto.
      apply expOrd_complete; auto.
      apply (index_lt _ 0%nat).
      apply omega_complete.
      rewrite <- addOrd_le1.
      apply expOrd_nonzero.
Qed.

Lemma VF_mul_correct : forall y x,
  VF_denote (VF_mul x y) ≈ VF_denote x * VF_denote y.
Proof.
  unfold VF_mul.
  induction y; simpl; intros.
  - rewrite mulOrd_zero_r. reflexivity.
  - rewrite VF_add_correct.
    rewrite VF_mul_single_correct; auto.
    rewrite veblen_onePlus; auto.
    rewrite ordDistrib_left.
    rewrite IHy2.
    apply addOrd_eq_mor.
    apply mulOrd_eq_mor; auto with ord.
    apply Vnormalize_equal.
    apply mulOrd_eq_mor; auto with ord.
    apply Vnormalize_normal.
Qed.

Lemma VF_expOmega_correct x : VF_denote (VF_expOmega x) ≈ expOrd ω (VF_denote x).
Proof.
  simpl.
  rewrite veblen_onePlus; auto.
  apply addOrd_zero_r.
Qed.

Lemma succ_cancel_le x y :
  succOrd x ≤ succOrd y -> x ≤ y.
Proof.
  intros.
  do 2 rewrite succ_unfold in H.
  destruct (ord_le_subord _ _ H tt); auto.
Qed.

Lemma succ_cancel x y :
  succOrd x ≈ succOrd y -> x ≈ y.
Proof.
  intro H. split; apply succ_cancel_le; apply H.
Qed.

Lemma add_cancel_finite (n:ω) x y :
  x + sz n ≈ y + sz n -> x ≈ y.
Proof.
  induction n; simpl; intro H.
  do 2 rewrite addOrd_zero_r in H; auto.
  do 2 rewrite addOrd_succ in H.
  apply succ_cancel in H.
  auto.
Qed.

(* This lemma seems surprisingly hard...
   I wonder if it can be simplified.
*)
Lemma normal_inf_lemma a x :
  VF_normal (V a x) ->
  1 + VF_denote (V a x) ≈ VF_denote (V a x) ->
  0 < VF_denote a.
Proof.
  destruct a; auto.
  - simpl; intuition.
    rewrite veblen_zero in H0.
    induction x.
    + simpl in H0.
      rewrite addOrd_zero_r in H0.
      elim (ord_lt_irreflexive 1).
      rewrite <- H0 at 2.
      rewrite addOrd_succ.
      apply succ_trans.
      apply addOrd_le1.
    + simpl in *. intuition.
      assert (x1 = Z).
      { destruct x1; auto.
        elim (ord_lt_irreflexive 0).
        rewrite <- H3 at 2.
        simpl. apply veblen_nonzero; auto. }
      subst x1.
      rewrite veblen_onePlus in H0; auto.
      simpl in H0.
      rewrite expOrd_zero in H0.
      repeat rewrite addOrd_assoc in H0.
      generalize (VFIsFinite_correct x2).
      destruct (VFIsFinite x2).
      * intro.
        rewrite H4 in H0.
        apply add_cancel_finite in H0.
        elim (ord_lt_irreflexive (1+1)).
        rewrite <- H0 at 2.
        rewrite addOrd_succ at 2.
        rewrite addOrd_succ.
        rewrite addOrd_succ.
        apply succ_trans.
        rewrite addOrd_zero_r.
        rewrite addOrd_zero_r.
        auto with ord.
      * intros. apply IHx2; auto.
        rewrite H4. auto.
  - intros; simpl. apply veblen_nonzero; auto.
Qed.

Lemma VF_exp_single_correct x e :
  VF_normal x ->
  VF_denote (VF_exp_single x e) ≈ expOrd (VF_denote x) (expOrd ω (VF_denote e)).
Proof.
  unfold VF_exp_single.
  destruct x. intros.
  - simpl.
    rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    rewrite expOrd_zero.
    split.
    apply succ_least. apply expOrd_nonzero.
    rewrite expOrd_unfold.
    apply lub_least; auto with ord.
    apply sup_least; intro.
    rewrite mulOrd_zero_r. auto with ord.
  - intro Hnorm.
    generalize (VFIsFinite_correct (V x1 x2)).
    destruct (VFIsFinite (V x1 x2)).
    + destruct n.
      { simpl. intros. elim (ord_lt_irreflexive 0).
        rewrite <- H at 2.
        apply veblen_nonzero; auto. }
      destruct n.
      { intro H. rewrite H. simpl.
        rewrite veblen_zero. rewrite addOrd_zero_r.
        symmetry; apply expOrd_one_base. }
      intros.
      generalize (VFIsFinite_correct e).
      destruct (VFIsFinite e).
      * destruct n0.
        { intro He. rewrite He.
          simpl sz.
          rewrite expOrd_zero.
          rewrite expOrd_one'.
          reflexivity.
          simpl. apply veblen_nonzero; auto. }
        intro He. rewrite He.
        rewrite H.
        transitivity (expOrd (sz (S (S n))) (expOrd ω (1 + sz n0))).
        rewrite expNatToOmegaPow.
        simpl.
        rewrite veblen_onePlus; auto.
        rewrite veblen_onePlus; auto.
        rewrite VF_nat_correct.
        do 2 rewrite addOrd_zero_r.
        reflexivity.
        simpl. apply succ_trans.
        apply succ_least. apply succ_trans; auto with ord.
        apply expOrd_eq_mor; auto with ord.
        apply expOrd_eq_mor; auto with ord.
        transitivity (sz (1 + n0)%nat).
        replace (1+n0)%nat with (n0+1)%nat by lia.
        rewrite natOrdSize_add.
        reflexivity.
        simpl. reflexivity.
      * intro He.
        rewrite H. rewrite <- He.
        rewrite expNatToOmegaPow.
        simpl.
        rewrite veblen_onePlus; auto.
        rewrite veblen_onePlus; auto.
        do 2 rewrite addOrd_zero_r.
        reflexivity.
        simpl.
        apply succ_trans.
        apply succ_least.
        apply succ_trans.
        auto with ord.

    + intro Hx.
      assert (Hx1 : 0 < VF_denote x1).
      { eapply normal_inf_lemma; eauto. }
      destruct e.
      * simpl.
        rewrite expOrd_zero.
        rewrite expOrd_one'.
        reflexivity.
        apply veblen_nonzero; auto.
      * rewrite VF_expOmega_correct.
        rewrite VF_mul_correct.
        rewrite VF_expOmega_correct.
        rewrite expOrd_mul.
        split.
        ** apply expOrd_monotone_base.
           simpl.
           rewrite veblen_onePlus; auto.
           apply addOrd_le1.
        ** destruct (VF_normal_dominates x2 x1) as [m Hm]; auto.
           simpl VF_denote at 1.
           rewrite veblen_onePlus; auto.
           apply expToOmega_collapse_tower with m; auto.
           transitivity (expOrd ω 1).
           { rewrite expOrd_one'.
             transitivity (natOrdSize (1+m)).
             rewrite natOrdSize_add. reflexivity.
             apply index_le.
             apply (index_lt _ 0%nat). }
           apply expOrd_monotone.
           apply succ_least. auto.
           simpl. apply veblen_nonzero; auto.
Qed.

Lemma VF_exp_correct : forall y x,
  VF_denote (VF_exp x y) ≈ expOrd (VF_denote x) (VF_denote y).
Proof.
  induction y; simpl; intros.
  - rewrite veblen_onePlus; auto.
    rewrite addOrd_zero_r.
    rewrite expOrd_zero.
    rewrite expOrd_zero.
    reflexivity.
  - rewrite VF_mul_correct.
    rewrite VF_exp_single_correct.
    rewrite Vnormalize_equal.
    rewrite veblen_onePlus; auto.
    rewrite expOrd_add.
    rewrite IHy2.
    reflexivity.
    apply Vnormalize_normal.
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
  simpl; intros.
  rewrite H.
  rewrite H0.
  symmetry.
  apply VF_exp_correct.
Qed.

Theorem VF_ε₀ : VF ≈ ε 0.
Proof.
  split.
  - rewrite ord_le_unfold; intro x.
    apply VNotation_below_ε₀.
  - apply ε0_least_exp_closed with Z VF_succ VF_expOmega.
    apply VF_reflects_zero.
    apply VF_reflects_succ.
    apply VF_reflects_expOmega.
Qed.

Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VF_has_enough_notations (EM:excluded_middle) :
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
    exists (VF_succ vo).
    rewrite Ho.
    apply VF_reflects_succ; auto.

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
