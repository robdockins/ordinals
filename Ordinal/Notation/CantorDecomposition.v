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

Require Import ClassicalFacts.
From Ordinal Require Import Classical.

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

  Definition cantor_nat (n:nat) :=
    cantor_recompose X (repeat cantor_zero n).

  Theorem cantor_nat_correct n : f (cantor_nat n) ≈ sz n /\ P (cantor_nat n).
  Proof.
    unfold cantor_nat.
    destruct (cantor_recompose_correct X (repeat cantor_zero n)).
    - induction n; simpl; intuition.
      unfold cantor_zero.
      destruct (cantor_recompose_correct X []); simpl; auto.
    - induction n; simpl; intuition.
      destruct n; simpl; intuition.
    - split; auto.
      rewrite <- H0.
      clear H H0.
      induction n; simpl; auto with ord.
      unfold cantor_zero.
      destruct (cantor_recompose_correct X []); simpl; auto.
      rewrite <- H0. simpl.
      rewrite expOrd_zero.
      rewrite IHn; auto.
      apply onePlus_finite_succ.
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

  Lemma cantor_list_is_finite_correct xs:
    each P xs ->
    cantor_ordered f xs ->
    match cantor_list_is_finite xs with
    | None => exists a b, xs = a::b /\ f a > 0
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

    - exists a, xs.
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


  (** Compute the value x^(ωᵉ). This algorithm has quite a few special cases,
      which are commented inline.
   *)
  Definition cantor_exp_single (x:list A) (e:list A) : list A :=
    match x with

    (* 0 ^ (ω^e) = 1 *)
    | [] => [ cantor_zero ]

    | (x1::xs) =>
        match cantor_list_is_finite (x1::xs) with
        | Some 0 => [ cantor_zero ] (* shouldn't happen, but eh... *)
        | Some 1 => [ cantor_zero ]
        | Some (S _) =>
            match cantor_list_is_finite e with
            (* n ^ (ω^0) = n *)
            | Some 0 => x
            (* n ^ (ω^(1+m)) = ω^(ω^m) for finite n > 1, finite m *)
            | Some (S m) => [ cantor_recompose X [ cantor_nat m ] ]
            (* n ^ (ω^e) = ω^(ω^e)  for e >= ω, finite n > 1 *)
            | None => [ cantor_recompose X [ cantor_recompose X e ] ]
            end

        | None =>
            match e with

            (* x^ (ω^0) = x *)
            | [] => x

            (* (ω^x₁ + b) ^ (ω^e) = ω^(x₁ * ω^e)  when x₁ >= 1, e > 0 *)
            | _ => [ cantor_recompose X (cantor_mul_single (cantor_decompose X x1) e) ]
            end
        end
    end.

  Lemma cantor_exp_single_prop_ordered:
    forall x e,
      each P x ->
      each P e ->
      cantor_ordered f x ->
      cantor_ordered f e ->
      each P (cantor_exp_single x e) /\ cantor_ordered f (cantor_exp_single x e).
  Proof.
    unfold cantor_exp_single; intros.
    destruct x as [|x1 xs]; simpl; auto.
    { intuition. unfold cantor_zero.
      destruct (cantor_recompose_correct X []); auto. }
    case_eq (cantor_decompose X x1); simpl; intros.
    - case_eq (cantor_list_is_finite e); simpl; intros.
      case_eq (length xs); intros.
      simpl; intuition.
      unfold cantor_zero.
      destruct (cantor_recompose_correct X []); simpl; auto.
      destruct n; simpl in *; intuition.
      destruct (cantor_recompose_correct X [cantor_nat n]); simpl; intuition.
      apply cantor_nat_correct.
      case_eq (length xs); intros.
      simpl; intuition.
      unfold cantor_zero.
      destruct (cantor_recompose_correct X []); simpl; auto.
      destruct (cantor_recompose_correct X e); simpl; intuition.
      destruct (cantor_recompose_correct X [cantor_recompose X e]); simpl; intuition.
    - destruct e; simpl in *; intuition.
      apply cantor_recompose_correct; simpl; intuition.
      apply cantor_recompose_correct; simpl; intuition.
      apply cantor_add_prop; simpl; auto.
      apply cantor_decompose_correct; auto.
      destruct (cantor_decompose_correct X x1); auto.
      rewrite H3 in H2. simpl in *. intuition.
      apply cantor_add_ordered; simpl; intuition.
      apply cantor_decompose_correct; auto.
      destruct (cantor_decompose_correct X x1); auto.
      rewrite H3 in H2. simpl in *. intuition.
      apply cantor_decompose_correct; auto.
      destruct (cantor_decompose_correct X x1); auto.
      rewrite H3 in H2. simpl in *. intuition.
  Qed.

  Lemma leading_zero_finite:
    forall xs x,
      cantor_ordered f (x::xs) ->
      f x ≈ 0 ->
      cantor_denote f (x::xs) ≈ sz (length xs+1)%nat.
  Proof.
    induction xs; simpl; intuition.
    rewrite H0. rewrite addOrd_zero_r.
    rewrite expOrd_zero. auto with ord.
    rewrite H0.
    rewrite expOrd_zero.
    simpl in IHxs.
    rewrite IHxs; auto.
    apply (onePlus_finite_succ (length xs + 1)).
    split; auto with ord.
    rewrite H1. apply H0.
  Qed.

  Opaque cantor_mul_single.

  Lemma cantor_exp_single_correct:
    forall x e,
      each P x ->
      each P e ->
      cantor_ordered f x ->
      cantor_ordered f e ->
      cantor_denote f (cantor_exp_single x e) ≈ expOrd (cantor_denote f x) (expOrd ω (cantor_denote f e)).
  Proof.
    unfold cantor_exp_single. intros.
    destruct x; simpl.
    { rewrite addOrd_zero_r.
      unfold cantor_zero.
      destruct (cantor_recompose_correct X []); simpl; intuition.
      rewrite <- H4. simpl.
      rewrite expOrd_zero.
      split.
      apply succ_least. apply expOrd_nonzero.
      rewrite expOrd_unfold.
      apply lub_least; auto with ord.
      apply sup_least. intro i.
      rewrite mulOrd_zero_r.
      apply ord_lt_le; apply succ_lt. }
    simpl in *; intuition.
    destruct (cantor_decompose_correct X a); intuition.
    case_eq (cantor_decompose X a); intros.
    - case_eq (length x); intros.
      + simpl. rewrite H6 in H8.
        simpl in *.
        destruct x; simpl in *; try discriminate.
        repeat rewrite addOrd_zero_r.
        rewrite H8.
        rewrite expOrd_zero.
        unfold cantor_zero.
        destruct (cantor_recompose_correct X []); simpl; auto.
        rewrite <- H11. simpl.
        rewrite expOrd_zero.
        symmetry. apply expOrd_one_base.
      + generalize (cantor_list_is_finite_correct e H0 H2).
        destruct (cantor_list_is_finite e); intros.
        * destruct n0.
          ** rewrite H10; simpl.
             rewrite expOrd_zero.
             rewrite expOrd_one'.
             auto with ord.
             rewrite <- addOrd_le1.
             apply expOrd_nonzero.
          ** destruct (cantor_recompose_correct X [cantor_nat n0]); simpl; intuition.
             apply cantor_nat_correct.
             rewrite (@leading_zero_finite x a).
             rewrite H10.
             transitivity (expOrd (sz (length x + 1)%nat) (expOrd ω (1+sz n0))).
             rewrite expNatToOmegaPow.
             simpl.
             rewrite addOrd_zero_r.
             apply expOrd_eq_mor; auto with ord.
             rewrite <- H12.
             simpl.
             rewrite addOrd_zero_r.
             apply expOrd_eq_mor; auto with ord.
             apply cantor_nat_correct.
             simpl.
             replace (length x + 1)%nat with (S (length x)) by lia.
             simpl.
             apply succ_trans.
             rewrite H9.
             simpl.
             apply succ_monotone; auto with ord.
             simpl.
             rewrite onePlus_finite_succ. reflexivity.
             simpl; auto.
             destruct (cantor_decompose_correct X a); auto.
             destruct H14.
             rewrite H15.
             rewrite H6.
             simpl. reflexivity.
        * rewrite (@leading_zero_finite x a).
          destruct (cantor_recompose_correct X e); simpl; auto.
          destruct (cantor_recompose_correct X [cantor_recompose X e]); simpl; auto.
          rewrite addOrd_zero_r.
          rewrite <- H14.
          assert (cantor_denote f e ≈ 1 + cantor_denote f e).
          { destruct H10 as [s [t [??]]].
            rewrite H10.
            simpl.
            rewrite addOrd_assoc.
            apply addOrd_eq_mor; auto with ord.
            split. apply addOrd_le2.
            apply limit_onePlus.
            apply additively_closed_limit.
            apply ord_lt_le_trans with (expOrd ω 1).
            rewrite expOrd_one'.
            apply omega_gt1.
            apply omega_gt0.
            apply expOrd_monotone.
            apply succ_least; auto.
            apply expOmega_additively_closed; auto.
            apply (cantor_decomp_complete X). }
          rewrite H15.
          rewrite (expNatToOmegaPow).
          simpl.
          rewrite addOrd_zero_r.
          rewrite <- H12.
          reflexivity.
          simpl.
          replace (length x + 1)%nat with (1 + length x)%nat by lia.
          simpl. apply succ_increasing.
          rewrite H9.
          simpl.
          auto with ord.
          simpl; auto.
          rewrite H8.
          rewrite H6.
          simpl.
          reflexivity.
    - destruct e; simpl in *.
      { rewrite expOrd_zero.
        rewrite expOrd_one'; auto with ord.
        rewrite <- addOrd_le1.
        apply expOrd_nonzero. }
      rewrite addOrd_zero_r.
      rewrite H6 in *.
      destruct (cantor_recompose_correct X (cantor_mul_single (a0::l) (a1::e))).
      apply cantor_mul_single_prop_ordered; simpl in *; intuition.
      apply cantor_mul_single_prop_ordered; simpl in *; intuition.
      rewrite <- H10.
      rewrite cantor_mul_single_correct; simpl in *; intuition.
      rewrite expOrd_mul.
      split.
      + apply expOrd_monotone_base; auto with ord.
        rewrite H8.
        apply addOrd_le1.
      + rewrite H8.
        rewrite expToOmega_collapse_tower with (length x); auto with ord.
        transitivity (expOrd ω 1).
        { rewrite expOrd_one'; auto with ord.
          apply ord_lt_le.
          apply additively_closed_omega; auto with ord.
          apply omega_gt1. apply omega_gt0. }
        apply expOrd_monotone; auto with ord.
        apply succ_least. rewrite <- addOrd_le1. apply expOrd_nonzero.
        rewrite <- H8.
        { revert H H5; clear.
          induction x; simpl; intuition.
          rewrite IHx.
          rewrite <- onePlus_finite_succ.
          rewrite ordDistrib_left.
          rewrite mulOrd_one_r.
          apply addOrd_monotone; auto with ord.
          apply expOrd_monotone; auto with ord.
          destruct x; auto.
          eauto with ord.
          auto. }
        apply addOrd_complete; auto with ord.
        apply expOrd_complete.
        apply omega_gt0.
        apply omega_complete.
        apply (cantor_decomp_complete X).
        apply cantor_denote_complete.
        rewrite <- addOrd_le1.
        apply expOrd_nonzero.
  Qed.

  Definition cantor_exp_list (xs:list A) (ys:list A) : list A :=
    fold_right (fun y s => cantor_mul_list (cantor_exp_single xs (cantor_decompose X y)) s) [cantor_zero] ys.

  Lemma cantor_exp_list_prop_ordered xs ys :
    each P xs ->
    each P ys ->
    cantor_ordered f xs ->
    cantor_ordered f ys ->
    each P (cantor_exp_list xs ys) /\ cantor_ordered f (cantor_exp_list xs ys).
  Proof.
    intros. induction ys; simpl; auto.
    { intuition.
      unfold cantor_zero.
      destruct (cantor_recompose_correct X []); simpl; intuition. }
    simpl in *.
    destruct H0; destruct H2.
    destruct IHys; simpl in *; auto.
    destruct (cantor_decompose_correct X a) as [?[??]]; auto.
    destruct (cantor_exp_single_prop_ordered xs (cantor_decompose X a)); auto.
    apply cantor_mul_list_prop_ordered; auto.
  Qed.

  Lemma cantor_exp_list_correct xs ys :
    each P xs ->
    each P ys ->
    cantor_ordered f xs ->
    cantor_ordered f ys ->
    cantor_denote f (cantor_exp_list xs ys) ≈ expOrd (cantor_denote f xs) (cantor_denote f ys).
  Proof.
    intros; induction  ys; simpl; auto.
    { rewrite addOrd_zero_r.
      rewrite expOrd_zero.
      unfold cantor_zero.
      destruct (cantor_recompose_correct X []); auto.
      rewrite <- H4. simpl.
      rewrite expOrd_zero. reflexivity. }
    simpl in *. intuition.
    destruct (cantor_decompose_correct X a) as [?[??]]; auto.
    destruct (cantor_exp_list_prop_ordered xs ys); auto.
    destruct (cantor_exp_single_prop_ordered xs (cantor_decompose X a)); auto.
    rewrite cantor_mul_list_correct; auto.
    rewrite expOrd_add.
    rewrite H6.
    rewrite cantor_exp_single_correct; auto.
    rewrite <- H8.
    reflexivity.
  Qed.

  Definition cantor_exp (x y:A) :=
    cantor_recompose X (cantor_exp_list (cantor_decompose X x) (cantor_decompose X y)).

  Theorem cantor_exp_reflects : reflects A f P (ORD ==> ORD ==> ORD) expOrd cantor_exp.
  Proof.
    simpl; intros.
    destruct H, H0.
    unfold cantor_exp.
    destruct (cantor_decompose_correct X a) as [?[??]]; auto.
    destruct (cantor_decompose_correct X a0) as [?[??]]; auto.
    destruct (cantor_recompose_correct X (cantor_exp_list (cantor_decompose X a) (cantor_decompose X a0))); auto.
    apply cantor_exp_list_prop_ordered; auto.
    apply cantor_exp_list_prop_ordered; auto.
    split; auto.
    rewrite <- H10.
    rewrite cantor_exp_list_correct; auto.
    rewrite <- H5.
    rewrite <- H8.
    rewrite <- H.
    rewrite <- H0.
    reflexivity.
  Qed.

  Definition has_interpolants (z:Ord) :=
    forall i:Ord, i < z -> exists y:A, P y /\ i <= f y /\ f y < z.

  Definition has_all_interpolants :=
    forall (a:A), P a -> has_interpolants (f a).

  Definition has_enough_notations :=
    forall (a:A) (x:Ord), P a -> x <= f a -> exists b, P b /\ f b ≈ x.

  Lemma has_enough_notations_has_all_interpolants:
    has_enough_notations -> has_all_interpolants.
  Proof.
    intros H a Ha i Hi.
    destruct (H a i) as [x [Hx1 Hx2]]; auto with ord.
    exists x; split; auto.
    split. apply Hx2. rewrite Hx2. auto.
  Qed.

  Lemma has_enough_notations_EM: has_enough_notations -> excluded_middle.
  Proof.
    intros H Q.
    hnf in H.
    destruct (cantor_nat_correct 1%nat) as [Hn1 Hn2].
    destruct (H (cantor_nat 1%nat) (classical.truth_ord Q)) as [z [Hz1 Hz2]]; auto.
    - rewrite Hn1. simpl.
      rewrite ord_le_unfold; simpl; intros.
      apply succ_lt.
    - generalize (cantor_zero_reflects). simpl; intros [Hzero1 Hzero2].
      generalize (cantor_decomp_compare_correct X cantor_zero z Hzero2 Hz1).
      destruct (cantor_decomp_compare X cantor_zero z); simpl;
        rewrite <- Hzero1; rewrite Hz2; intro Hord.
      + rewrite ord_lt_unfold in Hord.
        destruct Hord as [HQ _]. auto.
      + right; intro HQ.
        destruct Hord as [Hord1 Hord2].
        rewrite ord_le_unfold in Hord2.
        specialize (Hord2 HQ).
        rewrite ord_lt_unfold in Hord2. destruct Hord2 as [[] _].
      + rewrite ord_lt_unfold in Hord. destruct Hord as [[] _].
  Qed.

  Lemma has_interpolants_has_enough_notations:
    excluded_middle ->
    has_all_interpolants ->
    has_enough_notations.
  Proof.
    intros EM Hinterp a i Ha Hi.

    set (Q:= fun o => exists v:A, P v /\ i <= f v /\ o ≈ f v).
    assert (HP: exists o, Q o).
    { subst Q. exists (f a), a; intuition. }
    destruct HP as [o0 Ho0].
    destruct (classical.ord_well_ordered EM Q o0) as [z [Hz1 Hz2]]; auto.
    destruct Hz1 as [v [Hv1[Hv2 Hv3]]].
    exists v; split; auto. split; auto.
    destruct (classical.order_total EM (f v) i); auto.
    destruct Hinterp with v i as [q [Hq1 [Hq2 Hq3]]]; auto.
    assert (HQq: Q (f q)).
    { hnf. exists q. intuition. }
    apply Hz2 in HQq.
    elim (ord_lt_irreflexive z).
    rewrite HQq at 1.
    rewrite Hv3.
    auto.
  Qed.

  Theorem has_all_interpolants_EM_iff_has_enough_notations:
    (has_all_interpolants /\ excluded_middle) <-> has_enough_notations.
  Proof.
    intuition.
    apply has_interpolants_has_enough_notations; auto.
    apply has_enough_notations_has_all_interpolants; auto.
    apply has_enough_notations_EM; auto.
  Qed.

End cantor_arithmetic.
