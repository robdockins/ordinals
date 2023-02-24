Require Import Lia.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import List.
Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.

Open Scope ord_scope.

Local Set Implicit Arguments.

Fixpoint cantor_denote (A:Type) (f:A -> Ord) (xs:list A) : Ord :=
  match xs with
  | [] => 0
  | (x::xs') => expOrd ω (f x) + cantor_denote f xs'
  end.

Fixpoint cantor_ordered (A:Type) (f:A -> Ord) (xs:list A) : Prop :=
  match xs with
  | [] => True
  | x1::xs1 =>
      match xs1 with
      | [] => True
      | x2::xs2 => f x1 >= f x2
      end /\ cantor_ordered f xs1
  end.

Record has_cantor_decomposition (A:Type) (f:A -> Ord) (P: A -> Prop) :=
  { cantor_decomp_compare : A -> A -> ordering
  ; cantor_decompose : A -> list A
  ; cantor_recompose : list A -> A

  ; cantor_decomp_complete: forall x, complete (f x)

  ; cantor_decomp_compare_correct :
    forall x y, P x -> P y -> ordering_correct (cantor_decomp_compare x y) (f x) (f y)

  ; cantor_decompose_correct :
    forall x, P x ->
              each P (cantor_decompose x) /\
                cantor_ordered f (cantor_decompose x) /\
                f x ≈ cantor_denote f (cantor_decompose x)

  ; cantor_recompose_correct :
    forall xs,
      each P xs ->
      cantor_ordered f xs ->
      P (cantor_recompose xs) /\ cantor_denote f xs ≈ f (cantor_recompose xs)
  }.


Lemma each_app A (P:A -> Prop) xs ys:
  each P (xs ++ ys) <-> each P xs /\ each P ys.
Proof.
  induction xs; simpl; intuition.
Qed.

Section cantor_arithmetic.
  Variable A: Type.
  Variable f: A -> Ord.
  Variable P: A -> Prop.
  Variable X: has_cantor_decomposition f P.

  Lemma cantor_denote_complete xs:
    complete (cantor_denote f xs).
  Proof.
    induction xs; simpl; auto with ord.
    apply zero_complete.
    apply addOrd_complete; auto.
    apply expOrd_complete; auto with ord.
    apply omega_gt0.
    apply omega_complete.
    apply cantor_decomp_complete with P; auto.
  Qed.


  Definition cantor_zero := cantor_recompose X [].

  Theorem cantor_zero_reflects: reflects A f P ORD 0 cantor_zero.
  Proof.
    unfold cantor_zero. simpl.
    destruct (cantor_recompose_correct X []); simpl; auto.
  Qed.

  Definition cantor_succ_list xs := xs ++ [ cantor_recompose X [] ].

  Definition cantor_succ x :=
    cantor_recompose X (cantor_succ_list (cantor_decompose X x)).

  Theorem cantor_succ_reflects : reflects A f P (ORD ==> ORD) succOrd cantor_succ.
  Proof.
    simpl; intros x a [Ha1 Ha2].
    destruct (cantor_decompose_correct X a) as [Ha3 [Ha4 Ha5]]; auto.
    destruct (cantor_recompose_correct X []) as [Hz1 Hz2]; simpl in *; auto.
    unfold cantor_succ.
    destruct (cantor_recompose_correct X (cantor_succ_list (cantor_decompose X a))) as [H1 H2].
    - unfold cantor_succ_list.
      rewrite each_app; split; simpl; auto.
    - revert Ha4. generalize (cantor_decompose X a).
      induction l; simpl; intuition.
      destruct l; simpl; auto.
      rewrite <- Hz2; auto with ord.
    - split; auto.
      rewrite <- H2.
      rewrite Ha1.
      rewrite Ha5.
      generalize (cantor_decompose X a). clear -Hz2.
      induction l; simpl; intros.
      rewrite addOrd_zero_r.
      rewrite <- Hz2.
      symmetry. apply expOrd_zero.
      transitivity (expOrd ω (f a) + succOrd (cantor_denote f l)).
      { rewrite addOrd_succ. reflexivity. }
      rewrite IHl.
      reflexivity.
  Qed.


  Fixpoint cantor_add_loop xs y ys :=
    match xs with
    | [] => y::ys
    | (x::xs') =>
        match cantor_decomp_compare X x y with
        | LT => y::ys
        | _  => x::cantor_add_loop xs' y ys
        end
    end.

  Definition cantor_add_list xs ys :=
    match ys with
    | [] => xs
    | (y::ys') => cantor_add_loop xs y ys'
    end.

  Definition cantor_add x y :=
    cantor_recompose X (cantor_add_list (cantor_decompose X x) (cantor_decompose X y)).

  Lemma cantor_add_prop :
    forall xs ys,
      each P xs ->
      each P ys ->
      each P (cantor_add_list xs ys).
  Proof.
    intros. destruct ys as [|y ys]; simpl in * ; auto.
    induction xs as [|x xs]; simpl in *; intuition.
    destruct (cantor_decomp_compare X x y); simpl; intuition.
  Qed.

  Lemma cantor_add_ordered:
    forall xs ys,
      cantor_ordered f xs ->
      cantor_ordered f ys ->
      each P xs ->
      each P ys ->
      cantor_ordered f (cantor_add_list xs ys).
  Proof.
    intros. destruct ys as [|y ys]; simpl in * ; auto.
    induction xs as [|x xs]; simpl in *; intuition.
    generalize (cantor_decomp_compare_correct X x y).
    destruct (cantor_decomp_compare X x y); simpl in *; intuition.
    case_eq (cantor_add_loop xs y ys); intros; auto.
    destruct xs; simpl in *. inversion H9; subst.
    apply H2.
    destruct (cantor_decomp_compare X a0 y).
    inversion H9; subst.
    apply H2.
    inversion H9; subst; assumption.
    inversion H9; subst; assumption.
    case_eq (cantor_add_loop xs y ys); intros; auto.
    destruct xs; simpl in *. inversion H9; subst.
    auto with ord.
    destruct (cantor_decomp_compare X a0 y).
    inversion H9; subst; auto with ord.
    inversion H9; subst; assumption.
    inversion H9; subst; assumption.
  Qed.

  Lemma cantor_add_list_correct:
    forall xs ys,
      cantor_ordered f xs ->
      cantor_ordered f ys ->
      each P xs ->
      each P ys ->
      cantor_denote f (cantor_add_list xs ys) ≈ cantor_denote f xs + cantor_denote f ys.
  Proof.
    intros. destruct ys as [|y ys]; simpl in * ; auto.
    { rewrite addOrd_zero_r. reflexivity. }
    induction xs as [|x xs]; simpl in *; intuition.
    { rewrite addOrd_zero_l. reflexivity. }
    generalize (cantor_decomp_compare_correct X x y).
    destruct (cantor_decomp_compare X x y); simpl in *; intuition.
    cut (forall xs x, cantor_ordered f (x::xs) -> f x < f y ->
                        cantor_denote f (x::xs) + cantor_denote f (y::ys) ≈ cantor_denote f (y::ys)).
    intro Hcut. rewrite (Hcut xs x); simpl; intuition.
    { clear - X. induction xs; simpl; intuition.
      rewrite addOrd_zero_r. rewrite addOrd_assoc.
      split.
      apply addOrd_monotone; auto with ord.
      apply expOrd_add_collapse; auto.
      apply (cantor_decomp_complete X); auto.
      apply addOrd_monotone; auto with ord.
      apply addOrd_le2.
      simpl in IHxs.
      rewrite <- addOrd_assoc.
      rewrite (IHxs a); auto.
      rewrite addOrd_assoc.
      split.
      apply addOrd_monotone; auto with ord.
      apply expOrd_add_collapse; auto.
      apply (cantor_decomp_complete X); auto.
      apply addOrd_monotone; auto with ord.
      apply addOrd_le2.
      rewrite H1. auto. }
    rewrite H8.
    rewrite addOrd_assoc.
    reflexivity.
    rewrite H8.
    rewrite addOrd_assoc.
    reflexivity.
  Qed.

  Global Opaque cantor_add_list.

  Theorem cantor_add_reflects : reflects A f P (ORD ==> ORD ==> ORD) addOrd cantor_add.
  Proof.
    simpl. intros x a [Ha1 Ha2] y b [Hb1 Hb2].
    unfold cantor_add.
    destruct (cantor_decompose_correct X a) as [Ha3 [Ha4 Ha5]]; auto.
    destruct (cantor_decompose_correct X b) as [Hb3 [Hb4 Hb5]]; auto.
    destruct (cantor_recompose_correct X (cantor_add_list (cantor_decompose X a) (cantor_decompose X b))) as [H1 H2]; auto.
    - apply cantor_add_prop; auto.
    - apply cantor_add_ordered; auto.
    - split; auto.
      rewrite <- H2.
      rewrite cantor_add_list_correct; auto.
      rewrite <- Ha5. rewrite <- Hb5.
      rewrite <- Ha1. rewrite <- Hb1.
      reflexivity.
  Qed.

  Fixpoint cantor_list_pred xs : option (list A) :=
    match xs with
    | [] => None
    | [x] =>
        match cantor_decompose X x with
        | [] => Some []
        | _  => None
        end
    | (x::xs') =>
        match cantor_list_pred xs' with
        | None => None
        | Some zs => Some (x::zs)
        end
    end.

  Lemma cantor_list_pred_correct xs:
    each P xs ->
    cantor_ordered f xs ->
    match cantor_list_pred xs with
    | None => succ_unreachable (cantor_denote f xs)
    | Some xs' => cantor_denote f xs ≈ succOrd (cantor_denote f xs') /\
                    each P xs' /\
                    match xs with [] => False | x::_ => cantor_ordered f (x::xs') end
    end.
  Proof.
    induction xs; simpl; intuition.
    { hnf; simpl; intros.
      elim (ord_lt_irreflexive 0).
      apply ord_le_lt_trans with a; auto with ord. }

    case_eq xs; intros.
    { subst xs; simpl in *.
      destruct (cantor_decompose_correct X a) as [Ha1 [Ha2 Ha3]]; auto.
      destruct (cantor_decompose X a); simpl.
      rewrite Ha3. simpl.
      rewrite addOrd_zero_r.
      rewrite expOrd_zero.
      intuition.
      rewrite addOrd_zero_r.
      apply limit_unreachable.
      apply additively_closed_limit.
      apply ord_lt_le_trans with (expOrd ω 1).
      rewrite expOrd_one'.
      apply omega_gt1.
      apply omega_gt0.
      apply expOrd_monotone.
      rewrite Ha3.
      simpl.
      rewrite <- addOrd_le1.
      apply succ_least.
      apply expOrd_nonzero.
      apply expOmega_additively_closed.
      eapply cantor_decomp_complete; eauto. }

    rewrite <- H0.
    destruct (cantor_list_pred xs).
    intuition.
    simpl.
    rewrite H5.
    rewrite addOrd_succ.
    reflexivity.
    simpl; auto.
    simpl; auto.
    destruct l0; split; auto.
    destruct xs; intuition.
    simpl in *. intuition.
    rewrite H4.
    inversion H0. subst.
    auto.
    destruct xs; intuition.
    simpl in *. intuition.

    apply limit_unreachable.
    apply limit_add.
    apply unreachable_limit; auto.
    rewrite H0. simpl.
    rewrite <- addOrd_le1.
    apply expOrd_nonzero.
  Qed.

  Definition cantor_succ_test x :=
    match cantor_list_pred (cantor_decompose X x) with
    | None => None
    | Some xs' => Some (cantor_recompose X xs')
    end.

  Lemma cantor_succ_test_correct : forall x, 
      P x ->    
      match cantor_succ_test x with
      | None => succ_unreachable (f x)
      | Some x' => P x' /\ succOrd (f x') ≈ f x
      end.
  Proof.
    unfold cantor_succ_test; intros x Hx.
    destruct (cantor_decompose_correct X x Hx) as [Hx1 [Hx2 Hx3]].
    generalize (cantor_list_pred_correct (cantor_decompose X x) Hx1 Hx2).
    case_eq (cantor_list_pred (cantor_decompose X x)); intuition.
    - apply cantor_recompose_correct; auto.
      destruct (cantor_decompose X x); intuition.
      simpl in *; intuition.
    - rewrite Hx3.
      rewrite H1.
      destruct (cantor_recompose_correct X l); auto.
      destruct (cantor_decompose X x); intuition.
      simpl in *; intuition.
      rewrite H4; auto with ord.
    - hnf; intros.
      rewrite Hx3 in *.
      auto.
  Qed.

  Definition cantor_decide :
    forall x,
      P x ->
      { x' | P x' /\ f x ≈ succOrd (f x') } + { f x ≈ 0 } + { limitOrdinal (f x) }.
  Proof.
    intros.
    destruct (cantor_decompose_correct X x) as [Hx1 [Hx2 Hx3]]; auto.
    generalize (cantor_list_pred_correct (cantor_decompose X x) Hx1 Hx2).
    destruct (cantor_list_pred (cantor_decompose X x)); intro.
    - left. left.
      destruct (cantor_recompose_correct X l) as [Hl1 Hl2]; intuition.
      destruct (cantor_decompose X x); simpl in *; intuition.
      exists (cantor_recompose X l).
      split; auto.
      rewrite Hx3.
      rewrite H1.
      rewrite Hl2; reflexivity.
    - destruct (cantor_decompose X x); simpl in *.
      + left. right; auto.
      + right.
        rewrite Hx3.
        apply unreachable_limit; auto.
        rewrite <- addOrd_le1.
        apply expOrd_nonzero.
  Qed.

  Definition cantor_list_is_finite xs : option nat :=
    match xs with
    | [] => Some 0%nat
    | (x::xs) =>
        match cantor_decompose X x with
        | [] => Some (S (length xs))
        | _  => None
        end
    end.

  Lemma cantor_list_if_finite_correct xs:
    each P xs ->
    cantor_ordered f xs ->
    match cantor_list_is_finite xs with
    | None => exists a b, cantor_denote f xs ≈ expOrd ω a + b /\ a > 0
    | Some n => cantor_denote f xs ≈ sz n
    end.
  Proof.
    intros. destruct xs; simpl; auto with ord.
    destruct (cantor_decompose_correct X a) as [Ha1 Ha2]; simpl in *; intuition.
    destruct (cantor_decompose X a); simpl in *.
    - rewrite H4.
      rewrite expOrd_zero.
      induction xs; simpl in *.
      rewrite addOrd_zero_r. reflexivity.
      intuition.
      assert (f a0 ≈ 0).
      split; auto with ord.
      rewrite H. apply H4.
      rewrite H8.
      rewrite expOrd_zero.
      rewrite H3; auto.
      rewrite addOrd_succ.
      apply succOrd_eq_mor.
      generalize (length xs). clear.
      induction n; simpl; auto.
      rewrite addOrd_zero_r. reflexivity.
      rewrite addOrd_succ.
      apply succOrd_eq_mor; auto.

      destruct xs; auto with ord.
      rewrite H2; auto.

    - exists (f a), (cantor_denote f xs).
      split; auto with ord.
      rewrite H4.
      rewrite <- addOrd_le1.
      apply expOrd_nonzero.
  Qed.


  (** This sub-algorithm computes the value x * ωᵉ, which is equal to ω^(x₁ + e),
      where x₁ is the exponent of the leading term of x, except for some special
      cases involving empty sequences.
   *)
  Definition cantor_mul_single (x:list A) (e:list A) : list A :=
    match x, e with
    | [], _ => []
    | _, [] => x
    | (x1::_), _ => [ cantor_recompose X (cantor_add_list (cantor_decompose X x1) e) ]
    end.

  Lemma cantor_mul_single_prop_ordered:
    forall x e,
      each P x ->
      each P e ->
      cantor_ordered f x ->
      cantor_ordered f e ->
      each P (cantor_mul_single x e) /\ cantor_ordered f (cantor_mul_single x e).
  Proof.
    unfold cantor_mul_single; intros.
    destruct x as [|x1 xs]; simpl; auto.
    destruct e as [|e1 es]; simpl; auto.
    intuition.
    destruct (cantor_decompose_correct X x1) as [Hx1 Hx2]; simpl in *; intuition.
    destruct (cantor_recompose_correct X (cantor_add_list (cantor_decompose X x1) (e1::es))); auto.
    apply cantor_add_prop; simpl; auto.
    apply cantor_add_ordered; simpl; auto.
  Qed.

  Lemma cantor_mul_single_correct:
    forall x e,
      each P x ->
      each P e ->
      cantor_ordered f x ->
      cantor_ordered f e ->
      cantor_denote f (cantor_mul_single x e) ≈ (cantor_denote f x) * expOrd ω (cantor_denote f e).
  Proof.
    unfold cantor_mul_single; intros.
    destruct x as [|x1 xs]; simpl.
    { rewrite mulOrd_zero_l. reflexivity. }
    destruct e as [|e1 es].
    { simpl.
      rewrite expOrd_zero.
      rewrite mulOrd_one_r.
      reflexivity. }
    simpl cantor_denote.
    rewrite addOrd_zero_r.
    destruct (cantor_decompose_correct X x1) as [Hx1 Hx2]; simpl in *; intuition.
    transitivity (expOrd ω (f x1 + cantor_denote f (e1::es))).
    { apply expOrd_eq_mor; auto with ord.
      destruct (cantor_recompose_correct X (cantor_add_list (cantor_decompose X x1) (e1 :: es))).
      apply cantor_add_prop; simpl; auto.
      apply cantor_add_ordered; simpl; auto.
      rewrite <- H10.
      rewrite cantor_add_list_correct; simpl; auto.
      rewrite <- H8.
      reflexivity. }
    rewrite expOrd_add. simpl.
    split.
    { apply mulOrd_le_mor; auto with ord.
      apply addOrd_le1. }
    apply expOrd_omega_collapse with (length xs).
    apply (cantor_denote_complete (e1::es)).
    rewrite <- addOrd_le1.
    apply expOrd_nonzero.

    clear -H0 H6.
    induction xs.
    { simpl; auto with ord. }
    replace (length (a::xs)) with (length xs + 1)%nat by (simpl; lia).
    simpl.
    rewrite natOrdSize_add.
    rewrite ordDistrib_left.
    simpl.
    rewrite mulOrd_one_r.
    apply addOrd_le_mor.
    apply expOrd_monotone; auto with ord.
    apply IHxs; simpl in *; intuition.
    destruct xs; auto.
    rewrite H. auto.
  Qed.

  (** Compute the multiplication of two normal forms.

      It is a sum of partial products, where each term on the right
      is multiplied by the entire sequence on the left, and the results
      are added together.
   *)
  Definition cantor_mul_list (xs:list A) (ys:list A) : list A :=
    fold_right (fun y s => cantor_add_list (cantor_mul_single xs (cantor_decompose X y)) s) [] ys.

  Lemma cantor_mul_list_prop_ordered xs ys:
    each P xs ->
    each P ys ->
    cantor_ordered f xs ->
    cantor_ordered f ys ->
    each P (cantor_mul_list xs ys) /\ cantor_ordered f (cantor_mul_list xs ys).
  Proof.
    induction ys; simpl; intuition.
    apply cantor_add_prop; auto.
    destruct (cantor_decompose_correct X a); intuition.
    apply cantor_mul_single_prop_ordered; auto.
    destruct (cantor_decompose_correct X a); intuition.
    apply cantor_add_ordered; auto.
    apply cantor_mul_single_prop_ordered; auto.
    apply cantor_mul_single_prop_ordered; auto.
  Qed.

  Lemma cantor_mul_list_correct xs ys:
    each P xs ->
    each P ys ->
    cantor_ordered f xs ->
    cantor_ordered f ys ->
    cantor_denote f (cantor_mul_list xs ys) ≈ cantor_denote f xs * cantor_denote f ys.
  Proof.
    induction ys as [|y1 ys Hys]; simpl; intuition.
    { rewrite mulOrd_zero_r. reflexivity. }
    destruct (cantor_decompose_correct X y1); intuition; auto with ord.
    rewrite cantor_add_list_correct; auto.
    rewrite ordDistrib_left.
    apply addOrd_eq_mor; auto.
    rewrite cantor_mul_single_correct; auto.
    rewrite H9; auto with ord.
    apply cantor_mul_single_prop_ordered; auto.
    apply cantor_mul_list_prop_ordered; auto.
    apply cantor_mul_single_prop_ordered; auto.
    apply cantor_mul_list_prop_ordered; auto.
  Qed.

  Definition cantor_mul x y :=
    cantor_recompose X (cantor_mul_list (cantor_decompose X x) (cantor_decompose X y)).

  Theorem cantor_mul_reflects : reflects A f P (ORD ==> ORD ==> ORD) mulOrd cantor_mul.
  Proof.
    simpl; intros x a [Ha1 Ha2] y b [Hb1 Hb2].
    destruct (cantor_decompose_correct X a) as [Ha3 [Ha4 Ha5]]; auto.
    destruct (cantor_decompose_correct X b) as [Hb3 [Hb4 Hb5]]; auto.
    unfold cantor_mul.
    destruct (cantor_recompose_correct X
                (cantor_mul_list (cantor_decompose X a) (cantor_decompose X b))) as [H1 H2].
    apply cantor_mul_list_prop_ordered; auto.
    apply cantor_mul_list_prop_ordered; auto.
    split; auto.
    rewrite <- H2.
    rewrite cantor_mul_list_correct; auto.
    rewrite <- Ha5. rewrite <- Hb5.
    rewrite <- Ha1. rewrite <- Hb1.
    reflexivity.
  Qed.


End cantor_arithmetic.
