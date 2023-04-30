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
From Ordinal Require Import NaturalArith.

From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.

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

  Fixpoint has_interpolants_rec (z:Ord) (H:Acc ord_lt z) : Prop :=
    match H with
    | Acc_intro _ H' =>
        forall (i:Ord), i < z -> exists (y:A) (Hlt: f y < z), P y /\ i <= f y /\ has_interpolants_rec (H' _ Hlt)
    end.

  Lemma has_interpolants_rec_H_irrelevant : forall z H1 H2,
      @has_interpolants_rec z H1 -> @has_interpolants_rec z H2.
  Proof.
    induction z as [z Hindz] using ordinal_induction; simpl; intros H1 H2 H.
    destruct H1; destruct H2; simpl in *; intros i Hi.
    destruct (H i) as [y [Hy1 [Hy2 Hy3]]]; auto.
    exists y, Hy1; intuition.
    eapply Hindz; eauto.
  Qed.

  Lemma has_interpolants_rec_eq_mor : forall x y H1 H2,
      x ≈ y -> @has_interpolants_rec x H1 -> @has_interpolants_rec y H2.
  Proof.
    induction x as [x Hind] using ordinal_induction. intros y H1 H2 Hxy.
    destruct H1; destruct H2. simpl.
    intros Hx i Hi.
    destruct (Hx i) as [z [Hz1 [Hz2 [Hz3 Hz4]]]].
    rewrite Hxy. auto.
    exists z; intuition.
    assert (Hzy: f z < y).
    { generalize Hz1. rewrite Hxy. auto. }
    exists Hzy.
    intuition.
    eapply Hind; eauto with ord.
  Qed.

  Definition has_interpolants (z:Ord) : Prop := has_interpolants_rec (ord_lt_wf z).

  Lemma has_interpolants_unfold (z:Ord) :
    has_interpolants z <-> (forall (i:Ord), i < z -> exists y:A, P y /\ i <= f y /\ f y < z /\ has_interpolants (f y)).
  Proof.
    unfold has_interpolants; intuition.
    - destruct (ord_lt_wf z); simpl in *.
      destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
      exists y; intuition.
      eapply has_interpolants_rec_H_irrelevant; eauto.
    - destruct (ord_lt_wf z); simpl in *; intros.
      destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
      exists y, Hy3; intuition.
      eapply has_interpolants_rec_H_irrelevant; eauto.
  Qed.


  Global Add Parametric Morphism : has_interpolants with signature
    ord_eq ==> iff as has_interpolants_eq_mor.
  Proof.
    intros.
    unfold has_interpolants; split; apply has_interpolants_rec_eq_mor; auto with ord.
    symmetry. auto.
  Qed.

  Definition has_all_interpolants :=
    forall (a:A), P a -> has_interpolants (f a).

  Definition has_enough_notations :=
    forall (a:A) (x:Ord), P a -> x <= f a -> exists b, P b /\ f b ≈ x.

  Lemma has_enough_notations_has_all_interpolants:
    has_enough_notations -> has_all_interpolants.
  Proof.
    intros H a. induction a as [a Hinda] using (size_induction (ord A f)). intro Ha.
    rewrite has_interpolants_unfold. intros i Hi.
    destruct (H a i) as [x [Hx1 Hx2]]; auto with ord.
    exists x; intuition.
    apply Hx2. rewrite Hx2. auto.
    apply Hinda; auto.
    rewrite Hx2. auto.
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
    specialize (Hinterp v Hv1).
    rewrite has_interpolants_unfold in Hinterp.
    destruct Hinterp with i as [q [Hq1 [Hq2 [Hq3 _]]]]; auto.
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

  Section fix_interpolants.
    Variable g: Ord -> Ord.
    Hypothesis Hg1: forall b, complete b -> complete (g b).
    Hypothesis Hg2: forall b, complete b -> has_interpolants b -> has_interpolants (g b).

    Lemma iter_has_interpolants:
      forall m b,
        complete b ->
        has_interpolants b ->
        has_interpolants (iter_f g b m).
    Proof.
      induction m; simpl; auto with ord.
      intros b Hb1 Hb2.
      apply Hg2.
      apply iter_f_complete; auto.
      apply IHm; auto.
    Qed.

    Lemma fix_has_interpolants:
      forall b,
        complete b ->
        has_interpolants b ->
        has_interpolants (fixOrd g b).
    Proof.
      intros b Hb1 Hb2.
      rewrite has_interpolants_unfold. intros i Hi.
      unfold fixOrd in Hi.
      apply sup_lt in Hi.
      destruct Hi as [m Hi].
      generalize (iter_has_interpolants m b Hb1 Hb2).
      rewrite has_interpolants_unfold. intro H.
      destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
      exists y; intuition.
      unfold fixOrd.
      rewrite <- (sup_le _ _ m).
      auto.
    Qed.

  End fix_interpolants.

  Section onePlus_interpolants.
    Variable zr: A.
    Hypothesis Hzr: reflects A f P ORD 0 zr.

    Variable pr: A -> A.
    Hypothesis Hpr: reflects A f P (ORD ==> ORD) (addOrd 1) pr.

    Lemma onePlus_interpolants:
      forall b, has_interpolants b -> has_interpolants (1+b).
    Proof.
      induction b as [b Hindb] using ordinal_induction. intro Hb.
      rewrite has_interpolants_unfold. intros i Hi.
      rewrite addOrd_unfold in Hi.
      apply lub_lt in Hi.
      destruct Hi as [Hi|Hi].
      - rewrite ord_lt_unfold in Hi.
        destruct Hi as [[] Hi]; simpl in *.
        exists zr. destruct Hzr; intuition.
        rewrite Hi; auto with ord.
        rewrite <- H1.
        rewrite <- addOrd_le1.
        auto with ord.
        rewrite has_interpolants_unfold.
        intros i' Hi'.
        rewrite <- H in Hi'.
        rewrite ord_lt_unfold in Hi'.
        destruct Hi' as [[] _].
      - apply sup_lt in Hi.
        destruct Hi as [j Hi].
        rewrite ord_lt_unfold in Hi.
        destruct Hi as [[]  Hi]. simpl in Hi.
        rewrite has_interpolants_unfold in Hb.
        destruct (Hb j) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto with ord.
        exists (pr y).
        destruct Hpr with (f y) y as [Hpr1 Hpr2]; intuition auto with ord.
        rewrite <- Hpr1.
        rewrite Hi.
        apply addOrd_monotone; auto with ord.
        rewrite <- Hpr1.
        apply addOrd_increasing; auto with ord.
        rewrite <- Hpr1.
        apply Hindb; auto.
    Qed.

  End onePlus_interpolants.

  Section veblen_interpolants.
    Variable g: Ord -> Ord.

    Hypothesis Hg1: normal_function g.
    Hypothesis Hg2: forall b, complete b -> has_interpolants b -> has_interpolants (g b).

    Variable gr : A -> A.
    Hypothesis Hg_reflects: reflects A f P (ORD ==> ORD) g gr.

    Variable vr : A -> A -> A.
    Hypothesis Hvr_reflects: reflects A f P (ORD ==> ORD ==> ORD) (veblen g) vr.

    Lemma veblen_interpolants:
      forall a b,
        P a ->
        has_interpolants (f a) ->
        complete b ->
        has_interpolants b ->
        has_interpolants (veblen g (f a) b).
    Proof.
      induction a as [a Hinda] using (size_induction (ord A f)).
      induction b as [b Hindb] using ordinal_induction.
      intros Ha1 Ha2 Hb1 Hb2. rewrite has_interpolants_unfold. intros i Hi.
      rewrite veblen_unroll in Hi.
      apply lub_lt in Hi.
      destruct Hi as [Hi|Hi].
      - specialize (Hg2 b Hb1 Hb2).
        rewrite has_interpolants_unfold in Hg2.
        destruct Hg2 with i as [y [Hy1 [Hy2 Hy3]]]; auto.
        exists y; intuition.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        auto.
      - case_eq (f a). intros AA fa HA.
        rewrite HA in Hi. simpl in Hi.
        apply sup_lt in Hi.
        destruct Hi as [j Hi].
        set (b' := limOrd (fun x : b => veblen g (ord AA fa) (b x))).
        assert (Hb' : has_interpolants b').
        { unfold b'. rewrite has_interpolants_unfold.
          intros i0 Hi0.
          rewrite ord_lt_unfold in Hi0. simpl in Hi0.
          destruct Hi0 as [k Hi0].
          rewrite has_interpolants_unfold in Hb2.
          destruct (Hb2 (b k)) as [q [Hq1 [Hq2 [Hq3 Hq4]]]]; auto with ord.
          exists (vr a q).
          destruct Hvr_reflects with (f a) a (f q) q as [Hvr1 Hvr2]; intuition.
          rewrite <- Hvr1.
          rewrite Hi0.
          rewrite <- HA.
          apply veblen_monotone; auto with ord.
          apply normal_monotone; auto with ord.
          rewrite ord_lt_unfold; simpl.
          rewrite ord_lt_unfold in Hq3.
          destruct Hq3 as [k' Hq3].
          exists k'.
          rewrite <- HA.
          rewrite <- Hvr1.
          apply veblen_monotone; auto with ord.
          apply normal_monotone; auto.
          rewrite <- Hvr1.
          apply Hindb; auto.
          apply (cantor_decomp_complete X); auto. }
        rewrite has_interpolants_unfold in Ha2.
        destruct Ha2 with (i:=fa j) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto with ord.
        rewrite HA. auto with ord.
        assert (Hi' : i < fixOrd (veblen g (f y)) b').
        { eapply ord_lt_le_trans; [ apply Hi |].
          apply fixOrd_monotone_func.
          intros.
          apply veblen_monotone_first; auto with ord.
          apply normal_monotone; auto.
          intros; apply veblen_monotone; auto with ord.
          apply normal_monotone; auto. }

        assert (Hfix: has_interpolants (fixOrd (veblen g (f y)) b')).
        { apply fix_has_interpolants; auto.
          + intros. apply normal_complete; auto.
            apply veblen_normal; auto.
            apply (cantor_decomp_complete X).
          + unfold b'.
            apply lim_complete.
            intros.
            apply veblen_complete; auto.
            apply normal_complete; auto.
            rewrite <- HA.
            apply (cantor_decomp_complete X).
            apply complete_subord; auto.
            apply directed_monotone; auto.
            intros. apply veblen_monotone; auto with ord.
            apply normal_monotone; auto.
            destruct b. apply Hb1. }
        rewrite has_interpolants_unfold in Hfix.
        destruct (Hfix i) as [z [Hz1 [Hz2 [Hz3 Hz4]]]]; auto.
        exists z; intuition.
        eapply ord_lt_le_trans; [ apply Hz3 | ].
        rewrite veblen_unroll.
        rewrite <- lub_le2.
        simpl.
        rewrite HA in Hy3.
        rewrite ord_lt_unfold in Hy3.
        destruct Hy3 as [zq Hy3].
        rewrite <- (sup_le AA _ zq).
        apply fixOrd_monotone_func.
        intros. apply veblen_monotone_first; auto with ord.
        apply normal_monotone; auto.
        intros. apply veblen_monotone; auto with ord.
        apply normal_monotone; auto.
    Qed.

    Lemma veblen_interpolants_first:
      forall a,
        complete a ->
        has_interpolants a ->
        has_interpolants (veblen g a 0).
    Proof.
      induction a as [a Hinda] using ordinal_induction.
      intros Ha1 Ha2.
      rewrite has_interpolants_unfold. intros i Hi.
      rewrite veblen_unroll in Hi.
      apply lub_lt in Hi.
      destruct Hi as [Hi|Hi].
      - assert (has_interpolants (g 0)).
        { apply Hg2; auto with ord.
          apply zero_complete.
          rewrite has_interpolants_unfold.
          intros j Hj. rewrite ord_lt_unfold in Hj.
          destruct Hj as [[] _]. }
        rewrite has_interpolants_unfold in H.
        destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
        exists y; intuition.
        rewrite veblen_unroll. rewrite <- lub_le1. auto.
      - case_eq a. intros AA fa HA.
        rewrite HA in Hi. simpl in Hi.
        apply sup_lt in Hi.
        destruct Hi as [j Hi].
        rewrite HA in Ha2.
        rewrite has_interpolants_unfold in Ha2.
        destruct (Ha2 (fa j)) as [k [Hk1 [Hk2 [Hk3 Hk4]]]]; auto with ord.
        assert (Hi' : i < fixOrd (veblen g (f k)) 0).
        { eapply ord_lt_le_trans; [ apply Hi |].
          etransitivity; [ apply fixOrd_monotone | apply fixOrd_monotone_func ].
          intros; apply veblen_monotone; auto with ord.
          apply normal_monotone; auto.
          rewrite ord_le_unfold; simpl; intros [].
          intros; apply veblen_monotone_first; auto with ord.
          apply normal_monotone; auto.
          intros; apply veblen_monotone; auto with ord.
          apply normal_monotone; auto. }

        assert (Hfix: has_interpolants (fixOrd (veblen g (f k)) 0)).
        { apply fix_has_interpolants.
          + intros; apply veblen_complete; auto with ord.
            intros. apply normal_complete; auto.
            apply (cantor_decomp_complete X).
          + intros. apply veblen_interpolants; auto.
          + apply zero_complete.
          + rewrite has_interpolants_unfold.
            intros l Hl.
            rewrite ord_lt_unfold in Hl. destruct Hl as [[] _]. }
        rewrite has_interpolants_unfold in Hfix.
        destruct (Hfix i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
        exists y; intuition.
        rewrite veblen_unroll.
        rewrite <- lub_le2.
        simpl.
        rewrite ord_lt_unfold in Hk3.
        destruct Hk3 as [q Hq]. simpl in Hq.
        rewrite <- (sup_le _ _ q).
        eapply ord_lt_le_trans; [ apply Hy3 |].
        etransitivity; [ apply fixOrd_monotone | apply fixOrd_monotone_func ].
        intros; apply veblen_monotone; auto with ord.
        apply normal_monotone; auto.
        rewrite ord_le_unfold; simpl; intros [].
        intros; apply veblen_monotone_first; auto with ord.
        apply normal_monotone; auto.
        intros; apply veblen_monotone; auto with ord.
        apply normal_monotone; auto.
    Qed.

  End veblen_interpolants.


  Section reflects_nadd.
    Hypothesis Hinterp : has_all_interpolants.

    Lemma add_nadd_assoc2' :
      forall x y z,
        P z ->
        (forall q, P q -> f q <= f z -> x⊕f q <= x+f q) ->
        (x+y)⊕f z <= x+(y⊕f z).
    Proof.
      intro x.
      induction y as [y Hy] using ordinal_induction.
      induction z as [z Hz] using (size_induction (ord A f)).
      intros Hz2 H.
      apply naddOrd_least2.
      - rewrite addOrd_unfold. rewrite lub_unfold. rewrite sup_unfold. simpl.
        intros [i|[j []]]; simpl.
        + apply ord_lt_le_trans with (x⊕f z).
          apply naddOrd_increasing1. auto with ord.
          rewrite H; auto with ord.
          apply addOrd_monotone; auto with ord.
          apply naddOrd_le2.
        + rewrite Hy; auto with ord.
          apply addOrd_increasing.
          apply naddOrd_increasing1.
          auto with ord.
      - intros.
        specialize (@Hinterp z Hz2).
        rewrite has_interpolants_unfold in Hinterp.
        destruct Hinterp with j as [q [Hq1 [Hq2 [Hq3 Hq4]]]]; auto with ord.
        rewrite Hq2.
        rewrite Hz; auto with ord.
        apply addOrd_increasing.
        apply naddOrd_increasing2.
        auto with ord.
        intros.
        apply H; auto.
        rewrite H1; auto with ord.
    Qed.

    Section nadd_closed.
      Variable a:A.
      Hypothesis Ha: P a.
      Hypothesis Hnadd_closed_ind:
        forall a':A,
          P a' ->
          f a' ≤ f a ->
          forall x y:A,
            P x -> P y ->
            f x < expOrd ω (f a') ->
            f y < expOrd ω (f a') ->
            f x ⊕ f y < expOrd ω (f a').

      Lemma nadd_closed_technical1:
        forall
          n q r,
          P q ->
          P r ->
          f r < expOrd ω (f a) ->
          f q ≤ expOrd ω (f a) * succOrd (natOrdSize n) ->
          f r ⊕ f q < expOrd ω (f a) + f q.
      Proof.
        intros n.
        induction q as [q Hindq] using (size_induction (ord A f)); intros r Hq1 Hr1 Hr2 Hq2.
        assert (H: expOrd ω (f a) <= f q \/ expOrd ω (f a) > f q).
        { destruct (cantor_recompose_correct X [a]) as [H1 H2]; simpl; auto.
          generalize (cantor_decomp_compare_correct X (cantor_recompose X [a]) q H1 Hq1).
          destruct (cantor_decomp_compare X (cantor_recompose X [a]) q); simpl; auto with ord.
          rewrite <- H2. simpl.
          rewrite addOrd_zero_r. auto with ord.
          rewrite <- H2. simpl.
          rewrite addOrd_zero_r. intro H3. left. apply H3.
          rewrite <- H2. simpl.
          rewrite addOrd_zero_r. auto. }
        destruct H.
        + assert (Hq': exists q', P q' /\ f q' < f q /\ f q ≈ expOrd ω (f a) + f q').
          { destruct (cantor_decompose_correct X q) as [Hqs1 [Hqs2 Hqs3]]; auto.
            destruct (cantor_decompose X q) as [|h qs]; simpl in Hqs3.
            { rewrite Hqs3 in H.
              elim (ord_lt_irreflexive 0).
              rewrite <- H at 2.
              apply expOrd_nonzero. }
            assert (Hh: f h ≈ f a).
            { simpl in Hqs1. destruct Hqs1 as [Hh Hqs1].
              generalize (cantor_decomp_compare_correct X h a Hh Ha).
              destruct (cantor_decomp_compare X h a); simpl; auto; intro Hha.
              - rewrite Hqs3 in H.
                elim (ord_lt_irreflexive (expOrd ω (f a))).
                rewrite H at 1.
                rewrite (expOrd_unfold _ (f a)).
                rewrite <- lub_le2.
                rewrite ord_lt_unfold in Hha.
                destruct Hha as [j Hha].
                rewrite <- (sup_le _ _ j).
                rewrite mulOrd_unfold.
                rewrite <- (sup_le _ _ (S (length qs))); simpl.
                apply ord_le_lt_trans with
                  (expOrd ω (f a j) * succOrd (natOrdSize (length qs)) + 0).
                2: { apply addOrd_increasing. apply expOrd_nonzero. }
                rewrite addOrd_zero_r.
                revert Hqs2 Hha.
                generalize (f a j).
                clear.
                revert h.
                induction qs; simpl; intuition.
                rewrite addOrd_zero_r.
                rewrite mulOrd_one_r.
                apply expOrd_monotone; auto with ord.
                rewrite IHqs with (h:=a) (o:=o); simpl; intuition.
                transitivity (expOrd ω o * (sz (S (length qs) + 1)%nat)).
                rewrite natOrdSize_add.
                rewrite ordDistrib_left.
                simpl.
                apply addOrd_monotone; auto with ord.
                rewrite mulOrd_one_r.
                apply expOrd_monotone; auto with ord.
                replace (S (length qs) + 1)%nat with (S (S (length qs))) by lia.
                simpl; auto with ord.
                rewrite H; auto.
              - elim (ord_lt_irreflexive q).
                rewrite Hq2 at 1.
                rewrite Hqs3.
                rewrite <- addOrd_le1.
                rewrite ord_lt_unfold in Hha.
                destruct Hha as [j Hha].
                rewrite (expOrd_unfold _ (f h)).
                rewrite <- lub_le2.
                rewrite <- (sup_le _ _ j).
                rewrite Hha.
                apply mulOrd_increasing2.
                apply expOrd_nonzero.
                rewrite ord_lt_unfold.
                exists (S n). simpl.
                reflexivity. }

            destruct (cantor_recompose_correct X qs); simpl in *; intuition.
            exists (cantor_recompose X qs).
            split; auto.
            split.
            { rewrite <- H1.
              rewrite Hqs3.
              clear -h H4 H5.
              revert h H4 H5.
              induction qs; simpl; auto.
              intros. rewrite addOrd_zero_r.
              apply expOrd_nonzero.
              intuition.
              rewrite H4 at 1.
              apply addOrd_increasing.
              apply IHqs; auto. }
            rewrite Hqs3.
            rewrite <- H1.
            rewrite Hh.
            reflexivity. }

          destruct Hq' as [q' [Hq'1 [Hq'2 Hq'3]]].
          rewrite Hq'3.
          rewrite naddOrd_comm.
          rewrite add_nadd_assoc2'; auto.
          rewrite naddOrd_comm.
          apply addOrd_increasing.
          apply Hindq; auto.
          rewrite Hq'2. auto.

          intros. induction q0 as [q0 Hindq0] using (size_induction (ord A f)).
          apply naddOrd_least3.
          * intros.
            rewrite <- addOrd_le1.
            destruct (cantor_recompose_correct X [a]) as [Has1 Has2]; simpl; auto.
            simpl in Has2. rewrite addOrd_zero_r in Has2.
            rewrite Has2 in H2.
            specialize (@Hinterp (cantor_recompose X [a]) Has1).
            rewrite has_interpolants_unfold in Hinterp.
            destruct Hinterp with i as [z [Hz1 [Hz2 [Hz3 Hz4]]]]; auto.
            rewrite Hz2.
            apply Hnadd_closed_ind; auto with ord.
            rewrite Has2. auto.
            rewrite H1. auto.
          * intros.
            specialize (@Hinterp q0 H0).
            rewrite has_interpolants_unfold in Hinterp.
            destruct Hinterp with j as [t [Ht1 [Ht2 [Ht3 Ht4]]]]; auto.
            rewrite Ht2.
            rewrite Hindq0; auto with ord.
            apply addOrd_increasing; auto.
            rewrite Ht3; auto.

        + rewrite <- addOrd_le1.
          apply Hnadd_closed_ind; auto with ord.
      Qed.

      Lemma nadd_closed_technical2:
        forall m n q,
          P q ->
          f q ≤ expOrd ω (f a) * succOrd (natOrdSize n) ->
          expOrd ω (f a) * natOrdSize m ⊕ f q ≤ expOrd ω (f a) * natOrdSize m + f q.
      Proof.
        induction m as [m Hindm] using (size_induction ω).
        induction n as [n Hindn] using (size_induction ω).
        induction q as [q Hindq] using (size_induction (ord A f)).
        intros Hq1 Hq2.
        apply naddOrd_least3.
        - intros i Hi.
          destruct m.
          { simpl in Hi. rewrite mulOrd_zero_r in Hi.
            rewrite ord_lt_unfold in Hi.
            destruct Hi as [[] _]. }
          simpl in Hi.
          rewrite mulOrd_succ in Hi.
          rewrite addOrd_unfold in Hi.
          apply lub_lt in Hi.
          destruct Hi as [Hi|Hi].
          { apply ord_lt_le_trans with ((expOrd ω (f a) * sz m) ⊕ q).
            apply naddOrd_increasing1; auto.
            rewrite (Hindm m) with (n:=n) (q:=q); simpl; auto with ord.
            apply addOrd_monotone; auto with ord.
            apply mulOrd_monotone2; auto with ord. }
          apply sup_lt in Hi.
          destruct Hi as [r Hi].
          rewrite ord_lt_unfold in Hi. simpl in Hi.
          destruct Hi as [[] Hi].
          destruct (cantor_recompose_correct X [a]) as [Ha1 Ha2]; simpl; auto.
          generalize (@Hinterp (cantor_recompose X [a]) Ha1).
          intro Hinterp'. rewrite has_interpolants_unfold in Hinterp'.
          destruct Hinterp' with r as [s [Hs1 [Hs2 [Hs3 Hs4]]]]; auto.
          rewrite <- Ha2. simpl. rewrite addOrd_zero_r. auto with ord.
          rewrite Hi. clear i Hi.
          rewrite Hs2.
          rewrite add_nadd_assoc2'; auto.
          2:{ intros. apply Hindm with n; simpl; auto with ord.
              rewrite H0. auto. }
          simpl.
          rewrite mulOrd_succ.
          rewrite <- addOrd_assoc.
          apply addOrd_increasing.
          eapply nadd_closed_technical1; eauto with ord.
          rewrite <- Ha2 in Hs3.
          simpl in Hs3. rewrite addOrd_zero_r in Hs3; auto.
        - intros.
          generalize (@Hinterp q Hq1).
          rewrite has_interpolants_unfold. intro Hinterp'.
          destruct Hinterp' with j as [t [Ht1 [Ht2 [Ht3 Ht4]]]]; auto.
          rewrite Ht2.
          rewrite Hindq; auto with ord.
          apply addOrd_increasing; auto with ord.
          rewrite Ht3. auto.
      Qed.

      Lemma nadd_add_same_powers_step:
        forall m n,
          expOrd ω (f a) * sz (S m) ⊕ expOrd ω (f a) * sz (S n) ≤ expOrd ω (f a) * ω (m + n + 2)%nat.
      Proof.
        induction m as [m Hindm] using (size_induction ω).
        induction n as [n Hindn] using (size_induction ω).
        apply naddOrd_least3.
        - simpl; intros q Hq.
          rewrite mulOrd_succ in Hq.
          rewrite addOrd_unfold in Hq.
          apply lub_lt in Hq.
          destruct Hq as [Hq|Hq].
          { destruct m.
            - simpl in Hq. rewrite mulOrd_zero_r in Hq.
              rewrite ord_lt_unfold in Hq. destruct Hq as [[] _].
            - apply ord_lt_le_trans with ((expOrd ω (f a) * natOrdSize (S m)) ⊕ expOrd ω (f a) * succOrd (sz n)).
              apply naddOrd_increasing1. auto.
              rewrite (Hindm m) with (n:=n); simpl; auto with ord.
              apply mulOrd_monotone2; auto with ord. }
          apply sup_lt in Hq.
          destruct Hq as [r Hq].
          rewrite ord_lt_unfold in Hq. simpl in Hq.
          destruct Hq as [[] Hq].
          rewrite Hq.

          destruct (cantor_recompose_correct X [a]) as [Ha1 Ha2]; simpl; auto.
          simpl in Ha2. rewrite addOrd_zero_r in Ha2.
          generalize (@Hinterp (cantor_recompose X [a]) Ha1).
          rewrite has_interpolants_unfold. intro Hinterp'.
          destruct Hinterp' with r as [t [Ht1 [Ht2 [Ht3 Ht4]]]]; auto.
          rewrite <- Ha2. auto with ord.
          rewrite Ht2.
          destruct (cantor_recompose_correct X (repeat a (S n))).
          { simpl; intuition.
            clear - Ha.
            induction n; simpl; intuition. }
          { clear. generalize (S n). induction n0; simpl; intuition.
            destruct n0; simpl; auto with ord. }
          assert (Han: cantor_denote f (repeat a (S n)) ≈ expOrd ω (f a) * succOrd (natOrdSize n)).
          { clear. induction n; simpl.
            rewrite addOrd_zero_r.
            rewrite mulOrd_one_r.
            reflexivity.
            transitivity (expOrd ω (f a) * natOrdSize (S (S n))).
            replace (S (S n)) with (S n + 1)%nat by lia.
            rewrite natOrdSize_add.
            rewrite ordDistrib_left. simpl.
            rewrite mulOrd_one_r.
            rewrite <- IHn.
            simpl.
            reflexivity.
            simpl. reflexivity. }
          rewrite <- Han.
          rewrite H0.
          rewrite add_nadd_assoc2'; auto.
          + replace (m+n+2)%nat with (2+n+m)%nat by lia.
            rewrite natOrdSize_add.
            rewrite ordDistrib_left.
            apply addOrd_increasing.
            rewrite naddOrd_comm.
            rewrite (mulOrd_succ _ (succOrd (sz n))).
            rewrite <- H0.
            rewrite Han.

            change (expOrd ω (f a) * sz (S n) ⊕ f t <
                      expOrd ω (f a) * sz (S n) + expOrd ω (f a)).
            rewrite (nadd_closed_technical2) with (n:=S n); auto.
            apply addOrd_increasing; auto with ord.
            rewrite Ha2. auto.
            rewrite mulOrd_succ.
            rewrite <- addOrd_le2.
            rewrite Ha2.
            auto with ord.
          + intros.
            apply nadd_closed_technical2 with n; auto.
            rewrite H2.
            rewrite <- H0.
            rewrite Han.
            reflexivity.
        - simpl; intros q Hq.
          rewrite mulOrd_succ in Hq.
          rewrite addOrd_unfold in Hq.
          apply lub_lt in Hq.
          destruct Hq as [Hq|Hq].
          { destruct n.
            - simpl in Hq. rewrite mulOrd_zero_r in Hq.
              rewrite ord_lt_unfold in Hq. destruct Hq as [[] _].
            - apply ord_lt_le_trans with
                ((expOrd ω (f a) * succOrd (sz m)) ⊕ (expOrd ω (f a) * sz (S n))).
              apply naddOrd_increasing2. auto.
              rewrite (Hindn n).
              apply mulOrd_monotone2; auto with ord.
              apply natOrdSize_monotone. lia.
              simpl; auto with ord. }
          apply sup_lt in Hq.
          destruct Hq as [r Hq].
          rewrite ord_lt_unfold in Hq. simpl in Hq.
          destruct Hq as [[] Hq].
          rewrite Hq.

          rewrite naddOrd_comm.
          destruct (cantor_recompose_correct X [a]) as [Ha1 Ha2]; simpl; auto.
          simpl in Ha2. rewrite addOrd_zero_r in Ha2.
          generalize (@Hinterp (cantor_recompose X [a]) Ha1).
          rewrite has_interpolants_unfold; intro Hinterp'.
          destruct Hinterp' with r as [t [Ht1 [Ht2 [Ht3 Ht4]]]]; auto.
          rewrite <- Ha2. auto with ord.
          rewrite Ht2.
          destruct (cantor_recompose_correct X (repeat a (S m))).
          { simpl; intuition.
            clear - Ha.
            induction m; simpl; intuition. }
          { clear. generalize (S m). induction n; simpl; intuition.
            destruct n; simpl; auto with ord. }
          assert (Ham: cantor_denote f (repeat a (S m)) ≈ expOrd ω (f a) * succOrd (natOrdSize m)).
          { clear. induction m; simpl.
            rewrite addOrd_zero_r.
            rewrite mulOrd_one_r.
            reflexivity.
            transitivity (expOrd ω (f a) * natOrdSize (S (S m))).
            replace (S (S m)) with (S m + 1)%nat by lia.
            rewrite natOrdSize_add.
            rewrite ordDistrib_left. simpl.
            rewrite mulOrd_one_r.
            rewrite <- IHm.
            simpl.
            reflexivity.
            simpl. reflexivity. }
          rewrite <- Ham.
          rewrite H0.
          rewrite add_nadd_assoc2'; auto.

          + replace (m+n+2)%nat with (2+m+n)%nat by lia.
            rewrite natOrdSize_add.
            rewrite ordDistrib_left.
            apply addOrd_increasing.
            rewrite naddOrd_comm.
            rewrite (mulOrd_succ _ (succOrd (sz m))).
            rewrite <- H0.
            rewrite Ham.
            change (expOrd ω (f a) * sz (S m) ⊕ f t <
                      expOrd ω (f a) * sz (S m) + expOrd ω (f a)).
            rewrite (nadd_closed_technical2) with (n:=S m); auto.
            apply addOrd_increasing; auto with ord.
            rewrite Ha2. auto.
            rewrite mulOrd_succ.
            rewrite <- addOrd_le2.
            rewrite Ha2.
            auto with ord.
          + intros.
            apply nadd_closed_technical2 with m; auto.
            rewrite H2.
            rewrite <- H0.
            rewrite Ham.
            reflexivity.
      Qed.
    End nadd_closed.

    Lemma nadd_closed:
      forall a:A,
        P a ->
        forall x y:A,
          P x ->
          P y ->
          f x < expOrd ω (f a) ->
          f y < expOrd ω (f a) ->
          f x ⊕ f y < expOrd ω (f a).
    Proof.
      induction a as [a Hinda] using (size_induction (ord A f)).
      intros Ha x y HPx HPy Hx Hy.
      rewrite expOrd_unfold in Hx.
      apply lub_lt in Hx.
      destruct Hx as [Hx|Hx].
      { rewrite ord_lt_unfold in Hx.
        destruct Hx as [[] Hx].
        simpl in Hx.
        rewrite Hx.
        rewrite naddOrd_comm.
        rewrite <- naddOrd_zero.
        auto. }
      rewrite expOrd_unfold in Hy.
      apply lub_lt in Hy.
      destruct Hy as [Hy|Hy].
      { rewrite ord_lt_unfold in Hy.
        destruct Hy as [[] Hy].
        simpl in Hy.
        rewrite Hy.
        rewrite <- naddOrd_zero.
        rewrite expOrd_unfold.
        rewrite <- lub_le2.
        auto. }
      apply sup_lt in Hx.
      apply sup_lt in Hy.
      destruct Hx as [i Hx].
      destruct Hy as [j Hy].
      destruct (complete_directed a) with i j as [k [Hk1 Hk2]]; auto.
      apply (cantor_decomp_complete X).
      rewrite mulOrd_unfold in Hx.
      apply sup_lt in Hx.
      destruct Hx as [m Hx].
      rewrite mulOrd_unfold in Hy.
      apply sup_lt in Hy.
      destruct Hy as [n Hy].

      generalize (@Hinterp a Ha).
      rewrite has_interpolants_unfold. intro Hinterp'.
      destruct Hinterp' with (sz k) as [q [Hq1 [Hq2 [Hq3 Hq4]]]]; auto with ord.

      apply ord_lt_le_trans with (expOrd ω (f q) * ω (m + n + 2)%nat + 0).
      2:{ rewrite addOrd_zero_r.
          rewrite expOrd_unfold with _ (f a).
          rewrite <- lub_le2.
          rewrite ord_lt_unfold in Hq3.
          destruct Hq3 as [w Hw].
          rewrite <- (sup_le _ _ w).
          rewrite (mulOrd_unfold (expOrd _ (f a w))).
          rewrite <- (sup_le _ _ (m+n+2)%nat).
          rewrite <- addOrd_le1.
          apply mulOrd_monotone1; auto with ord.
          apply expOrd_monotone; auto with ord. }
      rewrite addOrd_zero_r.
      apply ord_lt_le_trans with
        ((expOrd ω (f a i) * ω m + expOrd ω (f a i)) ⊕ f y).
      apply naddOrd_increasing1; auto.
      rewrite Hy.
      rewrite Hk1.
      rewrite Hk2.
      rewrite Hq2.

      transitivity ((expOrd ω (f q) * sz (S m)) ⊕ (expOrd ω (f q) * sz (S n))).
      simpl. repeat rewrite mulOrd_succ. reflexivity.
      apply nadd_add_same_powers_step; auto with ord.

      intros; apply Hinda; auto with ord.
      rewrite H0. auto with ord.
    Qed.

    Lemma cantor_denote_app : forall xs ys,
        cantor_denote f (xs++ys) ≈ cantor_denote f xs + cantor_denote f ys.
    Proof.
      induction xs; simpl; auto.
      - intros. rewrite addOrd_zero_l. reflexivity.
      - intros.
        rewrite IHxs.
        rewrite addOrd_assoc.
        reflexivity.
    Qed.

    Lemma cantor_denote_nadd_add:
      forall xs b,
        each P xs ->
        (forall a, List.In a xs -> f a >= f b) ->
        forall q, P q -> f q <= expOrd ω (f b) ->
                  cantor_denote f xs ⊕ f q <= cantor_denote f xs + f q.
    Proof.
      induction xs as [|x xs] using List.rev_ind; simpl; auto with ord.
      { intros.
        rewrite naddOrd_comm. rewrite <- naddOrd_zero.
        rewrite addOrd_zero_l. reflexivity. }
      intros b Hxs1 Hxs2.
      intros q Hq1 Hq2.
      rewrite cantor_denote_app. simpl.
      rewrite addOrd_zero_r.
      rewrite add_nadd_assoc2'; auto.
      - rewrite <- addOrd_assoc.
        apply addOrd_monotone; auto with ord.
        revert Hq1 Hq2.
        induction q as [q Hindq] using (size_induction (ord A f)).
        intros.
        apply naddOrd_least3.
        + intros i Hi.
          destruct (cantor_recompose_correct X [x]) as [Hx1 Hx2]; simpl; auto.
          rewrite each_app in Hxs1. simpl in *; intuition.
          simpl in Hx2. rewrite addOrd_zero_r in Hx2.
          rewrite Hx2 in Hi.
          generalize (@Hinterp (cantor_recompose X [x]) Hx1).
          rewrite has_interpolants_unfold. intro Hinterp'.
          destruct Hinterp' with i as [z [Hz1 [Hz2 [Hz3 Hz4]]]]; auto.
          rewrite Hz2.
          eapply nadd_closed_technical1 with (n:=O); simpl; auto.
          rewrite each_app in Hxs1. simpl in *; intuition.
          intros; apply nadd_closed; auto.
          rewrite Hx2; auto.
          rewrite mulOrd_one_r.
          rewrite Hq2.
          apply expOrd_monotone.
          apply Hxs2.
          apply List.in_or_app.
          simpl; auto.
        + intros j Hj.
          generalize (@Hinterp q Hq1).
          rewrite has_interpolants_unfold. intro Hinterp'.
          destruct Hinterp' with j as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
          rewrite Hy2.
          rewrite Hindq; auto with ord.
          apply addOrd_increasing; auto.
          rewrite Hy3. auto.
      - intros.
        apply IHxs with b; simpl in *; intuition.
        rewrite each_app in Hxs1. simpl in *; intuition.
        rewrite H0. auto.
    Qed.


    Fixpoint cantor_denote_nadd (xs:list A) : Ord :=
      match xs with
      | nil => 0
      | x::xs' => expOrd ω (f x) ⊕ cantor_denote_nadd xs'
      end.


    Lemma cantor_denote_nadd_app: forall xs ys,
        cantor_denote_nadd (xs ++ ys) ≈ cantor_denote_nadd xs ⊕ cantor_denote_nadd ys.
    Proof.
      induction xs; simpl; intros.
      { rewrite naddOrd_comm. rewrite <- naddOrd_zero. reflexivity. }
      rewrite IHxs.
      rewrite naddOrd_assoc.
      reflexivity.
    Qed.

    Theorem cantor_denote_nadd_eq:
      forall xs,
        each P xs ->
        cantor_ordered f xs ->
        cantor_denote f xs ≈ cantor_denote_nadd xs.
    Proof.
      induction xs as [|x xs IHxs] using List.rev_ind; simpl; auto with ord.
      intros Hxs1 Hxs2.
      apply each_app in Hxs1.
      rewrite cantor_denote_app.
      rewrite cantor_denote_nadd_app.
      simpl.
      rewrite addOrd_zero_r.
      rewrite <- naddOrd_zero.
      rewrite <- IHxs.
      split.
      apply add_nadd_le.
      destruct (cantor_recompose_correct X [x]); simpl in *; intuition.
      rewrite addOrd_zero_r in H0. rewrite H0.
      apply cantor_denote_nadd_add with x; intuition auto with ord.
      { clear - Hxs2 H5.
        revert a H5.
        induction xs; simpl in *; intuition subst.
        destruct xs; simpl in *; intuition; subst.
        rewrite <- H.
        apply H1; auto.
        apply H1; auto. }

      apply H0.
      intuition.

      { clear - Hxs2.
        induction xs; simpl in *; intuition.
        destruct xs; simpl in *; intuition. }
    Qed.


    Fixpoint cantor_nadd_list (xs:list A) : list A -> list A :=
      fix inner (ys:list A) : list A :=
        match xs with
        | nil => ys
        | (x::xs') =>
            match ys with
            | nil => xs
            | y::ys' =>
                match cantor_decomp_compare X x y with
                | LT => y :: inner ys'
                | EQ => x :: cantor_nadd_list xs' ys
                | GT => x :: cantor_nadd_list xs' ys
                end
            end
        end.

    Definition cantor_nadd (x:A) (y:A) : A :=
      cantor_recompose X (cantor_nadd_list (cantor_decompose X x) (cantor_decompose X y)).

    Lemma cantor_nadd_list_correct:
      forall xs ys,
        each P xs ->
        each P ys ->
        cantor_ordered f xs ->
        cantor_ordered f ys ->
        each P (cantor_nadd_list xs ys) /\
          cantor_ordered f (cantor_nadd_list xs ys) /\
          cantor_denote_nadd (cantor_nadd_list xs ys) ≈ cantor_denote_nadd xs ⊕ cantor_denote_nadd ys.
    Proof.
      induction xs as [|x xs]; simpl.
      { intros.
        destruct ys; simpl in *; intuition.
        rewrite <- naddOrd_zero. reflexivity.
        rewrite (naddOrd_comm 0).
        rewrite <- naddOrd_zero.
        reflexivity. }
      induction ys as [|y ys]; simpl.
      { intuition.
        rewrite <- naddOrd_zero.
        reflexivity. }
      simpl; intros.
      generalize (cantor_decomp_compare_correct X x y).
      destruct (cantor_decomp_compare X x y); simpl in *; intuition.
      - destruct ys; simpl in *; intuition.
        generalize (cantor_decomp_compare_correct X x a).
        destruct (cantor_decomp_compare X x a); simpl; intuition.
      - rewrite H11.
        rewrite (naddOrd_comm (expOrd ω (f y))).
        rewrite <- naddOrd_assoc.
        rewrite <- (naddOrd_comm (expOrd ω (f y))).
        reflexivity.
      - destruct (IHxs (y::ys)); simpl; auto.
      - destruct xs; simpl; intuition.
        apply H3.
        generalize (cantor_decomp_compare_correct X a y).
        destruct (cantor_decomp_compare X a y); simpl; intuition.
        apply H3.
      - apply IHxs; simpl; auto.
      - destruct (IHxs (y::ys)) as [?[??]]; simpl; auto.
        rewrite H13.
        simpl.
        rewrite naddOrd_assoc.
        reflexivity.
      - apply IHxs; simpl; auto.
      - destruct xs; simpl; intuition.
        generalize (cantor_decomp_compare_correct X a y).
        destruct (cantor_decomp_compare X a y); simpl; intuition.
      - apply IHxs; simpl; auto.
      - destruct (IHxs (y::ys)) as [?[??]]; simpl; auto.
        rewrite H13.
        simpl.
        rewrite naddOrd_assoc.
        reflexivity.
    Qed.

    Lemma cantor_nadd_correct:
      forall x y, P x -> P y -> P (cantor_nadd x y) /\ f (cantor_nadd x y) ≈ f x ⊕ f y.
    Proof.
      intros x y Hx Hy.
      destruct (cantor_decompose_correct X x Hx) as [Hx1 [Hx2 Hx3]].
      destruct (cantor_decompose_correct X y Hy) as [Hy1 [Hy2 Hy3]].
      destruct (cantor_nadd_list_correct (cantor_decompose X x) (cantor_decompose X y)) as [H1 [H2 H3]]; auto.
      destruct (cantor_recompose_correct X (cantor_nadd_list (cantor_decompose X x) (cantor_decompose X y))) as [H4 H5]; auto.
      unfold cantor_nadd. split; auto.
      rewrite <- H5.
      rewrite cantor_denote_nadd_eq; auto.
      rewrite H3.
      rewrite <- cantor_denote_nadd_eq; auto.
      rewrite <- cantor_denote_nadd_eq; auto.
      rewrite <- Hx3.
      rewrite <- Hy3.
      reflexivity.
    Qed.

    Theorem cantor_nadd_reflects : reflects A f P (ORD ==> ORD ==> ORD) naddOrd cantor_nadd.
    Proof.
      simpl; intros.
      destruct (@cantor_nadd_correct a a0); intuition.
      rewrite H2.
      rewrite H3.
      rewrite H.
      reflexivity.
    Qed.
  End reflects_nadd.

End cantor_arithmetic.
