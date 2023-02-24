Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import List.
Import ListNotations.
Open Scope list.
Require Import Lia.
Require Import Program.Wf.

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
From Ordinal Require Import BHTower.
From Ordinal Require Import BHTowerFacts.

From Ordinal Require Import Notation.CantorDecomposition.


Open Scope ord_scope.

Local Hint Resolve
      bhtower_normal
      bhtower_first_normal
      bhtower_complete
      bhtower_monotone
      normal_complete
      normal_monotone
      normal_fix_complete
      normal_inflationary
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

Inductive BHForm := BH : list BHForm -> BHForm.

Fixpoint BH_termSize (x:BHForm) : nat :=
  match x with
  | BH l => 1%nat + fold_right Nat.add 0%nat (map BH_termSize l)
  end.

Definition BH_listSize (xs:list BHForm) : nat :=
  fold_right Nat.add 0%nat (map BH_termSize xs).


Fixpoint BH_denote (x:BHForm) : Ord :=
  match x with
  | BH l => BH_full_stack (map BH_denote l)
  end.


Fixpoint BH_each (P:list BHForm -> Prop) (x:BHForm) {struct x} : Prop :=
  match x with
  | BH xs => P xs /\
               (fix each xs : Prop :=
                  match xs with
                  | [] => True
                  | (x::xs) => BH_each P x /\ each xs
                  end) xs
  end.

Lemma BH_each_unfold P x :
  BH_each P x = match x with BH xs => P xs /\ each (BH_each P) xs end.
Proof.
  destruct x as [xs].
  simpl. f_equal.
  induction xs; simpl; f_equal; auto.
Qed.

Global Opaque BH_each.

Definition BHForm_induction : forall
  (P:BHForm -> Prop)
  (Hind: forall xs, each P xs -> P (BH xs)),
  forall x, P x :=

  fun P Hind =>
  fix outer (x:BHForm) : P x :=
    match x as x' return P x' with
    | BH xs0 =>
        Hind xs0
          ((fix inner (xs:list BHForm) : each P xs :=
              match xs as xs' return each P xs' with
              | nil => I
              | (y::ys) => conj (outer y) (inner ys)
              end
           ) xs0)
    end.

Lemma BHForm_complete: forall x:BHForm, complete (BH_denote x).
Proof.
  induction x using BHForm_induction.
  induction xs; simpl each in *; simpl BH_denote in *; auto with ord.
  apply BH_stack_complete; simpl; intuition.
  clear -H1.
  induction xs; simpl in *; intuition.
Qed.

Lemma BHForm_each_complete: forall xs, each complete (map BH_denote xs).
Proof.
  induction xs; simpl; intuition.
  apply BHForm_complete.
Qed.

Local Hint Resolve BHForm_complete BHForm_each_complete: core.


Theorem BHForm_bounded : forall x:BHForm, BH_denote x < BachmanHoward.
Proof.
  intro x.
  induction x using BHForm_induction.

  simpl.
  apply BH_full_stack_uneachable; auto.
  unfold each_lt.
  induction xs; simpl in *; intuition.
Qed.


Definition BH0    := BH [].
Definition BH1    := BH [BH0].
Definition BH2    := BH [BH1].
Definition BHω    := BH [BH1; BH0].
Definition BHε0   := BH [BH2; BH0; BH0].
Definition BHΓ0   := BH [BH2; BH1; BH0].
Definition BH_SVO := BH [BHω; BH0; BH0].
Definition BH_LVO := BH [BH2; BH0; BH0; BH0].

Lemma BH0_correct : BH_denote BH0 ≈ 0.
Proof.
  simpl; auto with ord.
Qed.

Lemma BH1_correct : BH_denote BH1 ≈ 1.
Proof.
  simpl; auto with ord.
  apply addOrd_zero_r.
Qed.

Lemma BH2_correct : BH_denote BH2 ≈ 2.
Proof.
  simpl; auto with ord.
  rewrite addOrd_zero_r.
  rewrite addOrd_succ.
  rewrite addOrd_zero_r.
  reflexivity.
Qed.

Lemma BHω_correct : BH_denote BHω ≈ ω.
Proof.
  simpl.
  rewrite bhtower_index_one; auto.
  rewrite addOrd_zero_r.
  rewrite veblen_onePlus; auto.
  rewrite expOrd_one'; auto.
  apply addOrd_zero_r.
  apply omega_gt0.
Qed.

Lemma BHε0_correct : BH_denote BHε0 ≈ ε 0.
Proof.
  transitivity (apex 0 (addOrd 1)); [ | apply apex0 ].
  simpl BH_denote.
  rewrite bhtower_zero.
  rewrite apex_alternate; auto with arith.
  split; apply bhtower_monotone; auto with ord.
  apply BH2_correct.
  apply BH2_correct.
Qed.

Lemma BHΓ0_correct : BH_denote BHΓ0 ≈ Γ 0.
Admitted. (* true, but annoying... *)

Lemma BH_SVO_correct : BH_denote BH_SVO ≈ SmallVeblenOrdinal.
Proof.
  transitivity (vtower (addOrd 1) ω 0).
  2: { symmetry; apply SVO_vtower. }
  simpl.
  rewrite bhtower_zero.
  rewrite bhtower_index_two; auto with ord.
  split; apply vtower_monotone; auto with ord.
  apply BHω_correct.
  apply BHω_correct.
Qed.

Lemma BH_LVO_correct : BH_denote BH_LVO ≈ LargeVeblenOrdinal.
Proof.
  transitivity (apex 1 (addOrd 1)); [ | apply apex1 ].
  rewrite apex_alternate; auto with arith.
  simpl BH_denote.
  rewrite bhtower_zero.
  rewrite bhtower_zero.
  split; apply bhtower_monotone; auto with ord.
  apply BH2_correct.
  apply BH2_correct.
Qed.



Definition bh_isZero (x:BHForm) : bool :=
  match x with
  | BH [] => true
  | _     => false
  end.

Fixpoint bh_allZero (xs: list BHForm) : bool :=
  match xs with
  | [] => true
  | (x::xs) => if bh_isZero x then bh_allZero xs else false
  end.

Definition isNil (xs:list BHForm) : bool :=
  match xs with
  | [] => true
  | _  => false
  end.


Inductive BH_compare_graph : BHForm -> BHForm -> ordering -> Prop :=

| BH_compare_node : forall xs ys o,
    BH_compare_phase1 xs ys o ->
    BH_compare_graph (BH xs) (BH ys) o

with BH_compare_phase1 : list BHForm -> list BHForm -> ordering -> Prop :=
| BH_compare_p1_zero_both:
    BH_compare_phase1 [] [] EQ

| BH_compare_p1_zero_l : forall y ys,
    BH_compare_phase1 [] (y::ys) LT

| BH_compare_p1_zero_r : forall x xs,
    BH_compare_phase1 (x::xs) [] GT

| BH_compare_p1_zero_head_l : forall x xs ys o,
    x = BH [] -> xs <> [] ->
    BH_compare_phase1 xs ys o ->
    BH_compare_phase1 (x::xs) ys o

| BH_compare_p1_zero_head_r : forall xs y ys o,
    y = BH [] -> ys <> [] ->
    BH_compare_phase1 xs ys o ->
    BH_compare_phase1 xs (y::ys) o

| BH_compare_p1_one : forall x xs y ys o,
    xs = nil -> ys = nil ->
    BH_compare_graph x y o ->
    BH_compare_phase1 (x::xs) (y::ys) o

| BH_compare_p1_length_l : forall x xs y ys o,
    y <> BH [] ->
    (length xs < length ys)%nat ->
    check_lt_graph x xs (BH (y::ys)) o ->
    BH_compare_phase1 (x::xs) (y::ys) o

| BH_compare_p1_length_r : forall x xs y ys o,
    x <> BH [] ->
    (length xs > length ys)%nat ->
    check_lt_graph y ys (BH (x::xs)) o ->
    BH_compare_phase1 (x::xs) (y::ys) (ordering_swap o)

| BH_compare_p1_length_eq : forall x xs y ys o,
    x <> BH [] ->
    y <> BH [] ->
    length xs = length ys ->
    BH_compare_phase2 (BH (x::xs)) x xs y ys (BH (y::ys)) o ->
    BH_compare_phase1 (x::xs) (y::ys) o

with BH_compare_phase2 : BHForm -> BHForm -> list BHForm -> BHForm -> list BHForm -> BHForm -> ordering -> Prop :=

| BH_compare_p2_one: forall xtop ytop x y o,
    BH_compare_graph x y o ->
    BH_compare_phase2 xtop x [] y [] ytop o

| BH_compare_p2_head_eq : forall xtop ytop x x1 xs y y1 ys o,
    BH_compare_graph x y EQ ->
    BH_compare_phase2 xtop x1 xs y1 ys ytop o ->
    BH_compare_phase2 xtop x (x1::xs) y (y1::ys) ytop o

| BH_compare_p2_head_lt : forall xtop ytop x x1 xs y y1 ys o,
    BH_compare_graph x y LT ->
    check_lt_graph x1 xs ytop o ->
    BH_compare_phase2 xtop x (x1::xs) y (y1::ys) ytop o

| BH_compare_p2_head_gt : forall xtop ytop x x1 xs y y1 ys o,
    BH_compare_graph x y GT ->
    check_lt_graph y1 ys xtop o ->
    BH_compare_phase2 xtop x (x1::xs) y (y1::ys) ytop (ordering_swap o)

with check_lt_graph : BHForm -> list BHForm -> BHForm -> ordering -> Prop :=
| check_lt0 : forall x ytop o,
    BH_compare_graph x ytop o ->
    check_lt_graph x [] ytop o

| check_lt1 : forall x x1 xs ytop o,
    BH_compare_graph x ytop LT ->
    check_lt_graph x1 xs ytop o ->
    check_lt_graph x (x1::xs) ytop o

| check_lt2 : forall x x1 xs ytop,
    BH_compare_graph x ytop GT ->
    check_lt_graph x (x1::xs) ytop GT

| check_lt3 : forall x x1 xs ytop,
    BH_compare_graph x ytop EQ ->
    bh_allZero (x1::xs) = true ->
    check_lt_graph x (x1::xs) ytop EQ

| check_lt4 : forall x x1 xs ytop,
    BH_compare_graph x ytop EQ ->
    bh_allZero (x1::xs) = false ->
    check_lt_graph x (x1::xs) ytop GT.

Scheme compare_graph_ind := Induction for BH_compare_graph Sort Prop
 with compare_phase1_ind := Induction for BH_compare_phase1 Sort Prop
 with compare_phase2_ind := Induction for BH_compare_phase2 Sort Prop
 with check_lt_ind := Induction for check_lt_graph Sort Prop.

Lemma compare_stack_lt1 :
  forall xs x q y f,
    normal_function f ->
    In q xs ->
    y < BH_denote q ->
    y < BH_stack f (BH_denote x) (map BH_denote xs).
Proof.
  induction xs; simpl; intuition; subst.
  - apply ord_lt_le_trans with (BH_denote q); auto.
    destruct xs.
    + simpl.
      apply normal_inflationary; auto.
    + transitivity (BH_stack (bhtower (S (length (map BH_denote (b::xs)))) f (BH_denote x)) (BH_denote q)
        (stackZeros (length xs) [0])).
      rewrite BH_stack_zeros.
      apply (normal_inflationary (fun z =>
             bhtower (S (length xs)) (bhtower (S (length (map BH_denote (b::xs)))) f (BH_denote x)) z 0)); auto with ord.
      apply BH_stack_monotone; auto with ord.
      clear. revert b. induction xs; simpl; intros.
      * constructor; auto with ord. constructor.
      * constructor; auto with ord.
        apply IHxs.
  - apply IHxs with q; auto.
Qed.

Lemma pairwise_le_refl xs : pairwise ord_le xs xs.
Proof.
  induction xs; constructor; auto with ord.
Qed.

(* wierdly annoying... *)
Lemma BH_small_dec (x:BHForm) :
  BH_denote x ≈ 0 \/ BH_denote x ≈ 1 \/ BH_denote x > 1.
Proof.
  induction x using BHForm_induction.
  induction xs; simpl in *; auto with ord.
  destruct H.

  destruct H.
  - destruct xs. simpl.
    { right. left. rewrite H. rewrite addOrd_zero_r. auto with ord. }

    assert (BH_stack (addOrd 1) (BH_denote a) (map BH_denote (b::xs)) ≈
            BH_stack (addOrd 1) 0 (map BH_denote (b::xs))).
    { split; apply BH_stack_monotone; auto with ord.
      destruct H; auto.
      apply pairwise_le_refl; auto.
      apply pairwise_le_refl; auto. }
    assert (BH_stack (addOrd 1) (BH_denote a) (map BH_denote (b::xs)) ≈
            BH_full_stack (map BH_denote (b::xs))).
    { rewrite H1.
      simpl map.
      rewrite BH_stack_leading_zero; auto with ord. }

    rewrite H2; auto.

  - right. right.
    destruct xs; simpl.
    + destruct H; auto with ord.
      rewrite H. rewrite addOrd_succ. rewrite addOrd_zero_r.
      auto with ord.
      rewrite <- addOrd_le2. auto.
    + rewrite <- BH_stack_fixpoint1 with (g := addOrd 1); auto with ord.
      rewrite <- addOrd_zero_r at 1.
      apply addOrd_increasing; auto with ord.
      apply BH_stack_nonzero.
      auto with ord.
      simpl; auto with ord.
      simpl; auto with ord.
      intros.
      rewrite <- bhtower_fixpoint with (a:=0) at 2; auto with ord arith.
      rewrite bhtower_zero. auto with ord.
      destruct H.
      rewrite H. auto with ord.
      transitivity 1; auto with ord.
Qed.

Definition rank (x:BHForm) :=
  match x with
  | BH xs => length xs
  end.


Inductive stable_list : list Ord -> Prop :=
| stable_short : forall xs, (length xs <= 2)%nat -> stable_list xs
| stable_zero_head : forall x xs, x ≈ 0 -> stable_list xs -> stable_list (x::xs)
| stable_limit_head : forall x xs, limitOrdinal x -> stable_list xs -> stable_list (x::xs)
| stable_succ_head: forall x xs, successorOrdinal x -> hasNonzeroIndex xs -> stable_list xs -> stable_list (x::xs).

Definition no_leading_zeros (xs:list Ord) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x::x'::xs => x > 0
  end.

Definition normal_list (xs:list Ord) : Prop :=
  no_leading_zeros xs /\ stable_list xs /\ each (fun x => x < BH_full_stack xs) xs.

Definition stable_form (x:BHForm) : Prop :=
  BH_each (fun xs => stable_list (map BH_denote xs)) x.

Definition normal_form (x:BHForm) : Prop :=
  BH_each (fun xs => normal_list (map BH_denote xs)) x.

Lemma stable_form_BH : forall xs,
    stable_form (BH xs) <-> (stable_list (map BH_denote xs) /\ each stable_form xs).
Proof.
  intros. unfold stable_form.
  rewrite BH_each_unfold.
  intuition.
Qed.

Lemma normal_form_BH : forall xs,
    normal_form (BH xs) <-> (normal_list (map BH_denote xs) /\ each normal_form xs).
Proof.
  intros. unfold normal_form.
  rewrite BH_each_unfold.
  intuition.
Qed.

Lemma stable_list_cons : forall x xs,
  stable_list (x::xs) -> stable_list xs.
Proof.
  intros. inversion H; auto.
  simpl in *. apply stable_short. lia.
Qed.

Lemma stable_form_cons : forall x xs,
  stable_form (BH (x::xs)) -> stable_form (BH xs).
Proof.
  intros.
  rewrite stable_form_BH in *.
  simpl in *; intuition.
  eapply stable_list_cons; eauto.
Qed.

Global Opaque stable_form.

Local Hint Resolve stable_form_cons stable_list_cons : core.

Lemma compare_stack_lt2:
  forall x y xs ys f ytop,
    normal_function f ->
    length xs = length ys ->
    BH_denote x < BH_denote y ->
    stable_list (map BH_denote (y::ys)) ->
    (forall x : BHForm, In x xs -> BH_denote x < BH_denote ytop) ->
    ((length ys <= 1)%nat \/ limitOrdinal (BH_denote ytop)) ->
    BH_denote ytop ≈ BH_stack f (BH_denote y) (map BH_denote ys) ->
    BH_stack f (BH_denote x) (map BH_denote xs) < BH_stack f (BH_denote y) (map BH_denote ys).
Proof.
  intros x y xs ys f ytop Hf Hlen Hxy Hstable Hlts H Heq.
  simpl in Hstable.
  assert (Hlts' : each_lt (BH_stack f (BH_denote y) (map BH_denote ys)) (map BH_denote xs)).
  { clear -Hlts Heq.
    unfold each_lt.
    induction xs; simpl in *; intuition.
    rewrite <- Heq.
    auto. }
  destruct H.
  { apply compare_stack_lt_short; simpl; intuition.
    repeat rewrite map_length; auto.
    repeat rewrite map_length; auto. }

  inversion Hstable; subst.
  - apply compare_stack_lt_short; simpl; intuition.
    repeat rewrite map_length; auto.
  - elim (ord_lt_irreflexive (BH_denote y)).
    rewrite H2 at 1.
    apply ord_le_lt_trans with (BH_denote x); auto with ord.
  - apply compare_stack_lt_long; simpl; intuition.
    repeat rewrite map_length; auto.
    rewrite <- Heq. auto.
  - apply compare_stack_lt_long; simpl; intuition.
    repeat rewrite map_length; auto.
    rewrite <- Heq. auto.
Qed.


Lemma BH_large_limit: forall x xs,
    x <> BH [] ->
    (1 < length xs)%nat ->
    limitOrdinal (BH_denote (BH (x :: xs))).
Proof.
  intros.
  destruct (BH_small_dec x) as [Hz|H1].
  - elim (ord_lt_irreflexive (BH_denote x)).
    rewrite Hz at 1.
    destruct x. destruct l. contradiction.
    simpl.
    apply BH_stack_nonzero; simpl; auto with ord.
  - simpl BH_denote.
    apply BH_full_stack_limit; simpl; auto.
    rewrite map_length. auto.
Qed.


Definition compare_phase2_invariant
  (f : Ord -> Ord)
  (xtop :BHForm) (x:BHForm) (xs:list BHForm)
  (y:BHForm) (ys:list BHForm) (ytop:BHForm) :=

  length xs = length ys /\
  ((length xs <= 1)%nat \/ (limitOrdinal (BH_denote xtop) /\ limitOrdinal (BH_denote ytop))) /\
  stable_form (BH (x::xs)) /\
  stable_form (BH (y::ys)) /\
  stable_form xtop /\
  stable_form ytop /\
  BH_denote xtop ≈ BH_stack f (BH_denote x) (map BH_denote xs) /\
  BH_denote ytop ≈ BH_stack f (BH_denote y) (map BH_denote ys).

Definition check_lt_invariant
  (f : Ord -> Ord)
  (x:BHForm) (xs:list BHForm) (ytop:BHForm) :=

  stable_form (BH (x::xs)) /\
  stable_form ytop /\
  0 < BH_denote ytop /\
  (xs = nil \/ limitOrdinal (BH_denote ytop)) /\
  (forall q, complete q -> q < BH_denote ytop ->
             bhtower (length xs) f q (BH_denote ytop) <= BH_denote ytop).

Lemma phase2_invariant_symmetric:
  forall f xtop x xs y ys ytop,
    compare_phase2_invariant f xtop x xs y ys ytop ->
    compare_phase2_invariant f ytop y ys x xs xtop.
Proof.
  unfold compare_phase2_invariant. intuition.
  rewrite <- H0; auto.
Qed.


Lemma phase2_check_lt_invariant x y x1 y1 xs ys xtop ytop f:
    normal_function f ->
    BH_denote x < BH_denote y ->
    compare_phase2_invariant f xtop x (x1::xs) y (y1::ys) ytop ->
    check_lt_invariant (bhtower (S (length xs)) f (BH_denote x)) x1 xs ytop.
Proof.
  unfold compare_phase2_invariant, check_lt_invariant.
  simpl; intros Hf Hxy H.
  decompose [and] H; clear H.
  split; eauto.
  split; eauto.
  split.
  { rewrite H8. apply BH_stack_nonzero; auto with ord. simpl; auto. }

  destruct xs.
  - simpl; split; auto.
    intros.
    rewrite bhtower_index_zero.
    rewrite bhtower_index_one; auto.
    rewrite H8 at 2.
    rewrite map_length.
    rewrite <- H0. simpl.
    destruct ys; simpl in *; try lia.
    rewrite bhtower_index_one; auto.
    rewrite <- veblen_fixpoints with (α:=BH_denote x) (β:=BH_denote y); auto with ord.
    apply veblen_monotone; auto with ord.
    rewrite H8.
    rewrite bhtower_index_one; auto. auto with ord.

  - simpl in *; intuition (try lia).

    assert (Hstable: stable_list (map BH_denote (y::y1::ys))).
    { rewrite stable_form_BH in *. intuition. }

    simpl in Hstable. inversion Hstable; subst; simpl in *.
    + rewrite map_length in *.
      destruct ys; simpl in *; try lia.
    + elim (ord_lt_irreflexive (BH_denote y)).
      rewrite H12 at 1.
      apply ord_le_lt_trans with (BH_denote x); auto with ord.

    + apply bhtower_collapse; auto with ord.
      rewrite H8 at 2.
      rewrite <- BH_stack_fixpoint1 with (g:=bhtower (S (S (length xs))) f (succOrd (BH_denote x)));
        simpl; auto with ord.
      rewrite map_length. rewrite <- H0.
      rewrite bhtower_succ; auto with ord arith.
      apply bhtower_monotone; auto with ord.
      rewrite H8; auto with ord.
      rewrite map_length. rewrite <- H0. auto with ord.
      apply addOrd_le2.
      apply BH_stack_complete; simpl; auto.

      intros.
      rewrite map_length. rewrite <- H0.
      apply bhtower_fixpoint; auto with ord arith.
      apply limit_unreachable; auto.

    + apply bhtower_collapse; auto with ord.
      rewrite H8 at 2.
      rewrite map_length. rewrite <- H0.
      rewrite <- BH_stack_fixpoint2; simpl; auto with ord.
      transitivity (bhtower (S (S (length xs))) f (succOrd (BH_denote x))
        (BH_stack (bhtower (S (S (length xs))) f (BH_denote y)) (BH_denote y1) (map BH_denote ys))).
      { rewrite bhtower_succ; auto with ord arith.
        apply bhtower_monotone; auto with ord arith.
        rewrite H8.
        rewrite map_length. rewrite <- H0.
        apply addOrd_le2.
        apply BH_stack_complete; simpl; auto. }
      apply bhtower_monotone; auto with ord.
      apply succ_least; auto.
Qed.

Lemma short_stack_check_lt_invariant x xs y ys:
  0 < BH_denote y ->
  (length xs < length ys)%nat ->
  stable_form (BH (x::xs)) ->
  stable_form (BH (y::ys)) ->
  check_lt_invariant (addOrd 1) x xs (BH (y :: ys)).
Proof.
  intros.

  assert (Hlim: xs = nil \/ (xs <> nil /\ limitOrdinal (BH_full_stack (map BH_denote (y::ys))))).
  { destruct xs; simpl; auto.
    simpl in *. right.
    split. discriminate.
    apply BH_large_limit.
    destruct y. destruct l.
    simpl in *.
    elim (ord_lt_irreflexive 0); auto.
    discriminate.
    lia. }

  hnf; simpl; intuition.
  + apply BH_stack_nonzero; simpl; auto.
  + subst xs; simpl.
    rewrite bhtower_index_zero.
    apply BH_stack_fixpoint2; simpl; auto.
    destruct ys; simpl in *. lia.
    left.
    destruct y. destruct l; auto.
  + apply BH_stack_nonzero; simpl; auto.
  + destruct xs. congruence. simpl.
    rewrite stable_form_BH in H2.
    destruct H2.
    simpl in H2.
    apply bhtower_collapse; auto with ord.
    apply BH_stack_complete; simpl; auto.
    apply BH_stack_complete; simpl; auto.
    inversion H2; subst.
    * simpl in *. rewrite map_length in *. lia.
    * elim (ord_lt_irreflexive (BH_denote y)).
      rewrite H10 at 1. auto.
    * destruct ys; simpl in *. lia.
      rewrite map_length.
      transitivity (bhtower (S (length ys)) (addOrd 1) 1
                      (BH_stack (bhtower (S (length ys)) (addOrd 1) (BH_denote y)) (BH_denote b0) (map BH_denote ys))).
      { rewrite bhtower_one; auto with ord arith.
        apply bhtower_monotone_strong; auto with ord arith.
        apply addOrd_le2.
        destruct ys; simpl in *; lia.
        apply BH_stack_complete; simpl; auto. }
      apply BH_stack_fixpoint1; simpl; auto.
      intros.
      apply bhtower_fixpoint; auto with ord arith.
      apply limit_unreachable; auto.
    * destruct ys; simpl in *. lia.
      rewrite map_length.
      rewrite <- BH_stack_fixpoint2 at 2; simpl; auto with ord.
      assert (exists y', BH_denote y ≈ succOrd y' /\ complete y').
      { clear - H10.
        assert (complete (BH_denote y)) by auto.
        destruct (BH_denote y) as [Y fy]; simpl in *.
        destruct H10 as [q ?].
        exists (fy q). split.
        split.
        rewrite ord_le_unfold; simpl; intros.
        rewrite ord_lt_unfold; simpl. exists tt. auto.
        apply succ_least.
        rewrite ord_lt_unfold. exists q. auto.
        apply H. }

      destruct H8 as [y' [??]].
      transitivity (bhtower (S (length ys)) (addOrd 1) (succOrd y')
                      (BH_stack (bhtower (S (length ys)) (addOrd 1) (BH_denote y)) (BH_denote b0) (map BH_denote ys))).
      { rewrite bhtower_succ; auto with ord arith.
        apply bhtower_monotone_strong; auto with ord.
        - intros. rewrite bhtower_unroll. auto with ord.
        - lia.
        - apply addOrd_le2.
        - lia.
        - apply BH_stack_complete; simpl; auto. }

      apply bhtower_monotone; auto with ord.
      apply H8.
Qed.

Lemma ordering_correct_normal:
  forall f x y o,
    normal_function f ->
    complete x ->
    complete y ->
    ordering_correct o x y ->
    ordering_correct o (f x) (f y).
Proof.
  intros. destruct o; simpl in *.
  apply normal_increasing; auto.
  destruct H2; split; auto with ord.
  apply normal_increasing; auto.
Qed.


Lemma compare_graph_correct :
  forall (x:BHForm) (y:BHForm) (o:ordering),
    BH_compare_graph x y o ->
    stable_form x ->
    stable_form y ->
    ordering_correct o (BH_denote x) (BH_denote y).
Proof.
  intros x0 y0 o0 Hstart.
  apply compare_graph_ind with
    (P := fun x y o H =>
            stable_form x ->
            stable_form y ->
            ordering_correct o (BH_denote x) (BH_denote y))
    (P0 := fun xs ys o H =>
             stable_form (BH xs) ->
             stable_form (BH ys) ->
             ordering_correct o (BH_full_stack (map BH_denote xs)) (BH_full_stack (map BH_denote ys)))
    (P1 := fun xtop x xs y ys ytop o H =>
             forall f,
               normal_function f ->
               compare_phase2_invariant f xtop x xs y ys ytop ->
               ordering_correct o
                 (BH_stack f (BH_denote x) (map BH_denote xs))
                 (BH_stack f (BH_denote y) (map BH_denote ys)))
    (P2 := fun x xs ytop o H =>
             forall f,
               normal_function f ->
               check_lt_invariant f x xs ytop ->
               ordering_correct o
                 (BH_stack f (BH_denote x) (map BH_denote xs)) (BH_denote ytop))
    ; auto.

  - simpl; intros. auto with ord.
  - simpl; intros. apply BH_stack_nonzero; simpl; auto with ord.
  - simpl; intros. apply BH_stack_nonzero; simpl; auto with ord.

  - simpl; intros.
    subst x. simpl.
    destruct xs. contradiction.
    simpl map.
    rewrite BH_stack_leading_zero; eauto.

  - simpl; intros.
    subst y. simpl.
    destruct ys. contradiction.
    simpl map.
    rewrite BH_stack_leading_zero; eauto.

  - intros; subst; simpl.
    apply ordering_correct_normal; auto.
    rewrite stable_form_BH in *; simpl in *; intuition.

  - simpl; intros.
    apply H; clear H; auto.
    apply short_stack_check_lt_invariant; auto.
    destruct y. destruct l0. congruence.
    simpl. apply BH_stack_nonzero; simpl; auto.

  - simpl; intros.
    cut (
      ordering_correct o (BH_stack (addOrd 1) (BH_denote y) (map BH_denote ys))
        (BH_stack (addOrd 1) (BH_denote x) (map BH_denote xs))).
    { destruct o; simpl; intros; auto with ord. symmetry; auto. }
    apply H; auto with ord.
    apply short_stack_check_lt_invariant; auto.
    destruct x. destruct l. congruence.
    simpl. apply BH_stack_nonzero; simpl; auto.

  - simpl; intros.
    apply H; auto with ord.
    hnf; intuition.
    destruct (Compare_dec.le_lt_dec (length xs) 1); auto.
    right; split.
    apply BH_large_limit; auto.
    apply BH_large_limit; auto.
    rewrite <- e. auto.

  - simpl; intros.
    apply ordering_correct_normal; auto.
    hnf in H1.
    repeat rewrite stable_form_BH in *.
    simpl in *; intuition.

  - simpl; intros.
    assert (BH_denote x ≈ BH_denote y).
    { apply H.
      hnf in H2; repeat rewrite stable_form_BH in *; simpl in *; intuition.
      hnf in H2; repeat rewrite stable_form_BH in *; simpl in *; intuition. }

    repeat rewrite map_length in *.
    replace (length xs) with (length ys) in *.
    assert ((BH_stack (bhtower (S (length ys)) f (BH_denote x)) (BH_denote x1) (map BH_denote xs))
              ≈
            (BH_stack (bhtower (S (length ys)) f (BH_denote y)) (BH_denote x1) (map BH_denote xs))).
    { destruct H3.
      split; apply BH_stack_monotone; auto with ord.
      apply pairwise_le_refl.
      apply pairwise_le_refl. }
    rewrite H4.
    apply H0; auto.
    hnf in H2; hnf.
    rewrite stable_form_BH in *. simpl in *.
    repeat rewrite map_length in *.
    replace (length xs) with (length ys) in *.
    intuition eauto; try lia.
    rewrite H12; auto.
    rewrite H12; auto.
    lia.
    hnf in H2. simpl in *. lia.

  - intros.
    assert (Hxy :BH_denote x < BH_denote y).
    { apply H.
      hnf in H2.
      repeat rewrite stable_form_BH in *.
      simpl in *. intuition.
      hnf in H2.
      repeat rewrite stable_form_BH in *.
      simpl in *. intuition. }

    assert (Hytop: BH_denote ytop ≈ (BH_stack f (BH_denote y) (map BH_denote (y1::ys)))).
    { hnf in H2. intuition. }

    assert (check_lt_invariant (bhtower (S (length xs)) f (BH_denote x)) x1 xs ytop).
    { eapply phase2_check_lt_invariant; eauto. }

    assert (ordering_correct o (BH_stack f (BH_denote x) (map BH_denote (x1::xs))) (BH_denote ytop)).
    { simpl. apply H0; auto.
      rewrite map_length. auto. }

    rewrite <- Hytop. assumption.

  - intros.
    assert (Hxy : BH_denote y < BH_denote x).
    { apply H.
      hnf in H2.
      repeat rewrite stable_form_BH in *.
      simpl in *. intuition.
      hnf in H2.
      repeat rewrite stable_form_BH in *.
      simpl in *. intuition. }

    assert (Hxtop: BH_denote xtop ≈ (BH_stack f (BH_denote x) (map BH_denote (x1::xs)))).
    { hnf in H2. intuition. }

    assert (check_lt_invariant (bhtower (S (length ys)) f (BH_denote y)) y1 ys xtop).
    { eapply phase2_check_lt_invariant; eauto.
      eapply phase2_invariant_symmetric. eauto. }

    assert (ordering_correct o (BH_stack f (BH_denote y) (map BH_denote (y1::ys))) (BH_denote xtop)).
    { simpl. apply H0; auto.
      rewrite map_length. auto. }

    rewrite <- Hxtop.
    destruct o; simpl in *; auto with ord.
    symmetry. auto.

  - intros.
    assert (bhtower 0 f 0 (BH_denote ytop) <= BH_denote ytop).
    { unfold check_lt_invariant in *; simpl in *; intuition. }
    rewrite bhtower_index_zero in H2.
    assert (BH_denote ytop ≈ f (BH_denote ytop)).
    { split; auto with ord. }
    rewrite H3.
    apply ordering_correct_normal; auto.
    apply H.
    unfold check_lt_invariant in H1;
    rewrite stable_form_BH in *; simpl in *; intuition.
    unfold check_lt_invariant in H1;  intuition.

  - simpl in *; intros.
    apply H0; auto with ord.
    rewrite map_length.
    unfold check_lt_invariant in H2. unfold check_lt_invariant.
    rewrite stable_form_BH in *; simpl in *; intuition.
    eapply stable_list_cons; eauto.
    discriminate.
    discriminate.
    eapply stable_list_cons; eauto.

    assert (exists q', BH_denote x <= q' /\ q <= q' /\ q' < BH_denote ytop /\ complete q').
    { rewrite ord_lt_unfold in H. rewrite ord_lt_unfold in H11.
      destruct H as [b1 ?]. destruct H11 as [b2 ?].
      destruct (complete_directed (BH_denote ytop) (BHForm_complete ytop) b1 b2) as [b3 [??]].
      exists b3. intuition eauto with ord.
      apply complete_subord; auto. }
    destruct H12 as [q' [?[?[??]]]].
    rewrite <- (H10 (succOrd q')) at 2; auto with ord.
    destruct (length xs); simpl.
    { rewrite bhtower_index_zero.
      apply bhtower_monotone; auto with ord. }
    rewrite bhtower_succ; auto with ord arith.
    rewrite <- bhtower_fixpoint with (a := q) (b:=1+BH_denote ytop); auto with ord arith.
    apply bhtower_monotone_strong; auto with ord.
    transitivity (1+BH_denote ytop); auto with ord.
    apply (normal_inflationary (fun z => bhtower (S n) _ z 0)); auto with ord.
    apply ord_lt_le_trans with (BH_denote ytop); auto with ord.
    apply limit_unreachable; auto with ord.

  - intros.
    apply ord_lt_le_trans with (BH_denote x).
    { unfold check_lt_invariant in *; rewrite stable_form_BH in *; simpl in *; apply H; intuition. }
    transitivity (BH_stack f (BH_denote x) (stackZeros (S (length xs)) [])).
    { clear -f H0. revert f H0. generalize (S (length xs)).
      induction n; simpl; intros.
      simpl; apply normal_inflationary; auto.
      rewrite (IHn f) at 1; auto.
      destruct n; simpl stackZeros.
      simpl.
      { destruct (complete_zeroDec (BH_denote x)); auto.
        transitivity (f 0); auto with ord.
        transitivity (bhtower 1 f 0 0).
        rewrite bhtower_zero; auto with ord.
        apply bhtower_monotone; auto with ord.
        rewrite <- bhtower_fixpoint with (a := 0) (b:=BH_denote x); auto with ord.
        rewrite bhtower_zero.
        apply normal_monotone; auto.
        apply (normal_inflationary (fun q => bhtower 1 f q 0)); auto with ord. }
      rewrite BH_stack_leading_zero; auto with ord.
      simpl in *.
      apply BH_stack_monotone; auto with ord.
      intros; apply bhtower_monotone_strong; auto with ord.
      apply pairwise_le_refl. }

    apply BH_stack_monotone; auto with ord.
    { clear. simpl.
      constructor; auto with ord.
      induction xs; simpl; constructor; auto with ord. }

  - unfold check_lt_invariant; intuition; try discriminate.
    assert (Hxytop : BH_denote x ≈ BH_denote ytop).
    { rewrite stable_form_BH in *;
        apply H; simpl in *; intuition. }

    transitivity (BH_stack f (BH_denote x) (stackZeros (length xs) [0])).
    { split; apply BH_stack_monotone; auto with ord.
      clear -e. revert x1 e. induction xs; simpl; intros.
      constructor.
      destruct x1 as [[|[?]]]; simpl in *; auto with ord. discriminate.
      constructor.
      constructor.
      destruct x1 as [[|[?]]]; simpl in *; auto with ord. discriminate.
      apply IHxs.
      destruct (bh_isZero x1); auto. discriminate.
      clear. revert x1; induction xs; simpl; intros.
      constructor. auto with ord. constructor.
      constructor; auto with ord. apply IHxs. }

    simpl.
    rewrite BH_stack_zeros.
    simpl in H6.
    split.
    + transitivity (bhtower (S (length xs)) f (BH_denote ytop) 0).
      { apply bhtower_monotone; auto with ord. apply Hxytop. }
      transitivity (bhtower (S (length xs)) f (boundedSup (BH_denote ytop) (fun x => x)) 0).
      { apply bhtower_monotone; auto with ord. apply limit_boundedSup; auto. }
      assert (complete (BH_denote ytop)) by auto.
      transitivity (supOrd (fun (x:BH_denote ytop) =>  bhtower (S (length xs)) f x 0)).
      { unfold limitOrdinal in *.
        destruct (BH_denote ytop); simpl in *; intuition.
        destruct H9.
        apply (normal_continuous (fun q => bhtower (S (length xs)) f q 0)); auto with ord. }
      apply sup_least; intros.
      transitivity (bhtower (S (length xs)) f a (BH_denote ytop)).
      { apply bhtower_monotone; auto with ord. }
      apply H6; auto with ord.
      apply complete_subord; auto.
    + rewrite <- Hxytop.
      apply (normal_inflationary (fun q => bhtower (S (length xs)) f q 0)); auto with ord.

  - unfold check_lt_invariant; intuition; try discriminate.
    assert (Hxytop : BH_denote x ≈ BH_denote ytop).
    { rewrite stable_form_BH in *;
        apply H; simpl in *; intuition. }

    apply ord_le_lt_trans with (BH_stack f (BH_denote x) (stackZeros (length xs) [0])).
    { rewrite BH_stack_zeros.
      rewrite <- Hxytop.
      apply (normal_inflationary (fun q =>  bhtower (S (length xs)) f q 0)); auto with ord. }


    cut (forall xs f x x1, normal_function f -> complete x ->
                           bh_allZero (x1::xs) = false ->
                           BH_stack f x (stackZeros (length xs) [0]) <
                           BH_stack f x (map BH_denote (x1::xs))).
    { intro Hcut. apply Hcut; auto. }
    clear.
    induction xs; intros.
    + simpl.
      destruct x1 as [[|[?]]]; simpl in *; auto with ord. discriminate.
      apply normal_increasing; auto with ord.
      apply BH_stack_complete; simpl; intuition; auto with ord.
      destruct l; simpl. apply zero_complete.
      apply BH_stack_complete; simpl; auto.
      apply BH_stack_nonzero; simpl; intuition; auto with ord.
      destruct l; simpl. apply zero_complete.
      apply BH_stack_complete; simpl; auto.
    + simpl stackZeros. simpl map.
      simpl in H1.
      destruct x1 as [[|?]]. simpl in H1.
      * simpl BH_denote.
        simpl BH_stack at 1.
        rewrite stackZeros_length. simpl length.
        apply ord_lt_le_trans with (BH_stack (bhtower (S (length xs + 1)) f x) 0 (map BH_denote (a::xs))).
        { apply IHxs; auto with ord. }
        simpl.
        apply BH_stack_monotone; auto with ord.
        intros. repeat rewrite bhtower_zero.
        rewrite map_length.
        apply bhtower_monotone_strong; auto with ord. lia.
        apply pairwise_le_refl.
      * apply ord_lt_le_trans with (BH_stack f x (BH_denote (BH (b::l)) :: stackZeros (length xs) [0])).
        { simpl. repeat rewrite BH_stack_zeros.
          apply (normal_increasing (fun q => bhtower _ _ q 0)); auto with ord.
          apply BH_stack_complete; simpl; auto.
          apply BH_stack_nonzero; simpl; auto with ord. }
        apply BH_stack_monotone; auto with ord.
        constructor. auto with ord.
        clear. revert a.
        induction xs; simpl; constructor; auto with ord.
        constructor.

Qed.

Lemma termSize_lemma1 : forall x xs ytop n,
  (BH_listSize (x::xs) + BH_termSize ytop < n)%nat ->
  (BH_termSize x + BH_termSize ytop < n)%nat.
Proof.
  intros. unfold BH_listSize in H. simpl in *. lia.
Qed.

Lemma termSize_lemma2 : forall x xs ytop n,
  (BH_listSize (x::xs) + BH_termSize ytop < n)%nat ->
  (BH_listSize xs + BH_termSize ytop < n)%nat.
Proof.
  intros. unfold BH_listSize in *. simpl in *. lia.
Qed.

Lemma termSize_lemma3 : forall x xs y ys n,
  (BH_listSize (x::xs) + BH_listSize (y::ys) < n)%nat ->
  (BH_termSize x + BH_termSize y < n)%nat.
Proof.
  intros. unfold BH_listSize in *. simpl in *. lia.
Qed.

Lemma termSize_lemma4 : forall x xs y ys n,
  (BH_listSize (x::xs) + BH_listSize (y::ys) < n)%nat ->
  (BH_listSize xs + BH_listSize ys < n)%nat.
Proof.
  intros. unfold BH_listSize in *. simpl in *. lia.
Qed.

Lemma termSize_lemma5: forall x xs ys n,
  (1 + BH_listSize (x :: xs) + BH_listSize ys < n)%nat ->
  (1 + BH_listSize xs + BH_listSize ys < n)%nat.
Proof.
  intros. unfold BH_listSize in *. simpl in *. lia.
Qed.

Lemma termSize_lemma6: forall xs y ys n,
  (1 + BH_listSize xs + BH_listSize (y::ys) < n)%nat ->
  (1 + BH_listSize xs + BH_listSize ys < n)%nat.
Proof.
  intros. unfold BH_listSize in *. simpl in *. lia.
Qed.


Section bhcompare_function.
  Variable n:nat.
  Variable compare_rec :
    forall x y, (BH_termSize x + BH_termSize y < n)%nat -> { o | BH_compare_graph x y o }.


  Fixpoint check_lt x xs ytop {struct xs} :
    (BH_listSize (x::xs) + BH_termSize ytop < n)%nat ->
    { o | check_lt_graph x xs ytop o }.

    refine (
        match xs as xs' return
              (BH_listSize (x::xs') + BH_termSize ytop < n)%nat ->
              { o | check_lt_graph x xs' ytop o }
        with
        | [] => fun H => let (r, Hr) := compare_rec x ytop _ in exist _ r _
        | x1::xs' =>
            fun H =>
              let (o, Ho) := compare_rec x ytop _ in
              match o as o' return
                    (BH_compare_graph x ytop o' -> { r | check_lt_graph x (x1::xs') ytop r })
              with
              | LT => fun Ho' => let (r, Hr) := check_lt x1 xs' ytop _ in exist _ r _
              | EQ => fun Ho' =>
                        match bh_allZero (x1::xs') as b return
                              (bh_allZero (x1::xs') = b ->
                               { r | check_lt_graph x (x1::xs') ytop r })
                        with
                        | true  => fun Hz => exist _ EQ _
                        | false => fun Hz => exist _ GT _
                        end (eq_refl _)
              | GT => fun Ho' => exist _ GT _
              end Ho
        end).

    - apply termSize_lemma1 with []; assumption.
    - apply check_lt0; assumption.
    - apply termSize_lemma1 with (x1::xs'); assumption.
    - apply termSize_lemma2 with x; assumption.
    - apply check_lt1; assumption.
    - apply check_lt3; assumption.
    - apply check_lt4; assumption.
    - apply check_lt2; assumption.
  Defined.


  Fixpoint compare_phase2 xtop x xs y ys ytop :
    (BH_listSize (x::xs) + BH_listSize (y::ys) < n)%nat ->
    (BH_listSize (x::xs) + BH_termSize ytop < n)%nat ->
    (BH_listSize (y::ys) + BH_termSize xtop < n)%nat ->
    length xs = length ys ->
    { o | BH_compare_phase2 xtop x xs y ys ytop o }.

    refine (
       match xs as xs', ys as ys' return
          (BH_listSize (x::xs') + BH_listSize (y::ys') < n)%nat ->
          (BH_listSize (x::xs') + BH_termSize ytop < n)%nat ->
          (BH_listSize (y::ys') + BH_termSize xtop < n)%nat ->
          length xs' = length ys' ->
          { o | BH_compare_phase2 xtop x xs' y ys' ytop o }
       with
       | [], [] => fun H0 H1 H2 _ => let (o,Ho) := compare_rec x y _ in exist _ o _
       | [], (y1::ys') => fun _ _ _ Hlen => _
       | (x1::xs'), [] => fun _ _ _ Hlen => _
       | (x1::xs'), (y1::ys') =>
           fun H0 H1 H2 Hlen =>
             let (o,Ho) := compare_rec x y _ in
             match o as o' return
                   BH_compare_graph x y o' ->
                   { r | BH_compare_phase2 xtop x (x1::xs') y (y1::ys') ytop r }
             with
             | LT => fun Ho' => let (r,Hr) := check_lt x1 xs' ytop _ in exist _ r _
             | EQ => fun Ho' => let (r,Hr) := compare_phase2 xtop x1 xs' y1 ys' ytop _ _ _ _ in exist _ r _
             | GT => fun Ho' => let (r,Hr) := check_lt y1 ys' xtop _ in exist _ (ordering_swap r) _
             end Ho
       end).

    - apply termSize_lemma3 with [] []; assumption.
    - apply BH_compare_p2_one; assumption.
    - simpl in *. discriminate.
    - simpl in *. discriminate.
    - apply termSize_lemma3 with (x1::xs') (y1::ys'); assumption.
    - apply termSize_lemma2 with x; assumption.
    - apply BH_compare_p2_head_lt; assumption.
    - apply termSize_lemma4 with x y; assumption.
    - apply termSize_lemma2 with x; assumption.
    - apply termSize_lemma2 with y; assumption.
    - simpl in Hlen. injection Hlen. trivial.
    - apply BH_compare_p2_head_eq; assumption.
    - apply termSize_lemma2 with y; assumption.
    - apply BH_compare_p2_head_gt; assumption.
  Defined.


  Definition hasLeadingZero x (xs:list BHForm) : ({ x <> BH [] } + { x = BH [] /\ xs = nil }) + { x = BH [] /\ xs <> nil }.
    case_eq xs; intros; auto.
    case_eq x; intros.
    case_eq l; intros; auto.
    left. left. discriminate.
    case_eq x; intros.
    case_eq l0; intros; auto.
    right. split; auto. discriminate.
    left. left. discriminate.
  Defined.

  Fixpoint compare_phase1 xs : forall ys,
      (1 + BH_listSize xs + BH_listSize ys < n)%nat ->
      { o | BH_compare_phase1 xs ys o }.
    refine (
        match xs as xs' return
              forall ys, (1 + BH_listSize xs' + BH_listSize ys < n)%nat -> { o | BH_compare_phase1 xs' ys o }
        with
        | [] => fun ys H =>
                  match ys as ys' return { o | BH_compare_phase1 [] ys' o }
                  with
                  | [] => exist _ EQ _
                  | _::_ => exist _ LT _
                  end

        | (x::xs') =>
            fix inner ys : (1 + BH_listSize (x::xs') + BH_listSize ys < n)%nat -> { o | BH_compare_phase1 (x::xs') ys o } :=
              match ys as ys' return
                    (1 + BH_listSize (x::xs') + BH_listSize ys' < n)%nat -> { o | BH_compare_phase1 (x::xs') ys' o }
              with
              | [] => fun _ => exist _ GT _
              | y::ys' => fun Hlen =>
                match hasLeadingZero x xs' with
                | inright (conj Hx1 Hx2) => let (r,Hr) := compare_phase1 xs' (y::ys') _ in exist _ r _
                | inleft Hx =>
                    match hasLeadingZero y ys' with
                    | inright (conj Hy1 Hy2) => let (r,Hr) := inner ys' _ in exist _ r _
                    | inleft Hy =>
                        match nat_compare (length xs') (length ys') as lo return
                              (match lo with
                               | LT => (length xs' < length ys')%nat
                               | EQ => length xs' = length ys'
                               | GT => (length xs' > length ys')%nat
                              end) ->
                              { r | BH_compare_phase1 (x::xs') (y::ys') r }
                        with
                        | LT => fun Hlt => let (r,Hr) := check_lt x xs' (BH (y::ys')) _ in exist _ r _
                        | EQ => fun Heq =>
                                  match Hx with
                                  | left Hx' =>
                                      match Hy with
                                      | left Hy' =>
                                          let (r,Hr) := compare_phase2 (BH (x::xs')) x xs' y ys' (BH (y::ys')) _ _ _ _ in
                                                        exist _ r _
                                      | right (conj Hy1 Hy2) => let (r,Hr) := compare_rec x y _ in exist _ r _
                                      end
                                  | right (conj Hx1 Hx2) => let (r,Hr) := compare_rec x y _ in exist _ r _
                                  end
                        | GT => fun Hgt => let (r,Hr) := check_lt y ys' (BH (x::xs')) _ in exist _ (ordering_swap r) _
                        end (nat_compare_correct (length xs') (length ys'))
                    end
                end
              end
        end).

    - apply BH_compare_p1_zero_both.
    - apply BH_compare_p1_zero_l.
    - apply BH_compare_p1_zero_r.

    - unfold BH_listSize in *. simpl in *. lia.
    - destruct Hy as [?|[??]].
      apply BH_compare_p1_length_l; auto.
      subst; simpl in *. lia.
    - lia.
    - unfold BH_listSize in *. simpl in *. lia.
    - unfold BH_listSize in *. simpl in *. lia.
    - exact Heq.

    - apply BH_compare_p1_length_eq; auto.

    - unfold BH_listSize in *. simpl in *. lia.

    - clear inner compare_phase1.
      apply BH_compare_p1_one; try assumption.
      destruct xs'; trivial.
      subst. simpl in *. discriminate.
    - unfold BH_listSize in *. simpl in *. lia.
    - clear inner compare_phase1.
      apply BH_compare_p1_one; auto.
      destruct ys'; auto.
      subst. simpl in *.  discriminate.
    - unfold BH_listSize in *. simpl in *. lia.
    - clear inner compare_phase1.
      destruct Hx as [?|[??]].
      apply BH_compare_p1_length_r; auto.
      subst; simpl in *. lia.
    - apply termSize_lemma6 with y; assumption.
    - apply BH_compare_p1_zero_head_r; assumption.
    - apply termSize_lemma5 with x; assumption.
    - apply BH_compare_p1_zero_head_l; assumption.
  Defined.
End bhcompare_function.

Fixpoint bhcompare_loop x y (Wf: Acc lt (BH_termSize x + BH_termSize y)%nat) {struct Wf} : { o | BH_compare_graph x y o }.
  refine (
  match Wf with
  | Acc_intro _ H =>
      match x as x', y as y' return x = x' -> y = y' -> { o | BH_compare_graph x' y' o }
      with
      | BH xs, BH ys =>
          fun Hx Hy =>
          let (r,Hr) := compare_phase1
                          ((BH_termSize x + BH_termSize y)%nat)
                          (fun a b Hab => bhcompare_loop a b (H _ Hab))
                          xs ys _ in
            exist _ r _
      end (eq_refl _) (eq_refl _)
  end).

  - rewrite Hx. rewrite Hy. unfold BH_listSize. simpl. lia.
  - apply BH_compare_node. assumption.
Defined.

Definition bhcompare x y : ordering :=
  proj1_sig (bhcompare_loop x y (Wf_nat.lt_wf (BH_termSize x + BH_termSize y)%nat)).

Theorem bhcompare_correct :
  forall x y,
    stable_form x ->
    stable_form y ->
    ordering_correct (bhcompare x y) (BH_denote x) (BH_denote y).
Proof.
  intros. unfold bhcompare.
  destruct (bhcompare_loop x y (Wf_nat.lt_wf (BH_termSize x + BH_termSize y)%nat)).
  apply compare_graph_correct; auto.
Qed.


Lemma each_implies A (P Q:A -> Prop) (xs: list A) :
  (forall x, P x -> Q x) ->
  each P xs -> each Q xs.
Proof.
  induction xs; simpl; intuition.
Qed.

Lemma unique_denote_lt_impossible:
  forall
    x1 xs y1 ys x y f
    (Hf : normal_function f)
    (Hx1 : stable_list (BH_denote x :: BH_denote x1 :: map BH_denote xs))
    (Hy1 : stable_list (BH_denote y :: BH_denote y1 :: map BH_denote ys))
    (Hx2 : BH_denote x <
             BH_stack (bhtower (S (length (map BH_denote xs))) f (BH_denote x))
               (BH_denote x1) (map BH_denote xs) /\
             BH_denote x1 <
               BH_stack (bhtower (S (length (map BH_denote xs))) f (BH_denote x))
                 (BH_denote x1) (map BH_denote xs) /\
             each
               (fun a : Ord =>
                  a <
                    BH_stack (bhtower (S (length (map BH_denote xs))) f (BH_denote x))
                      (BH_denote x1) (map BH_denote xs)) (map BH_denote xs))
    (Hy2 : BH_denote y <
             BH_stack (bhtower (S (length (map BH_denote ys))) f (BH_denote y))
               (BH_denote y1) (map BH_denote ys) /\
             BH_denote y1 <
               BH_stack (bhtower (S (length (map BH_denote ys))) f (BH_denote y))
                 (BH_denote y1) (map BH_denote ys) /\
             each
               (fun a : Ord =>
                  a <
                    BH_stack (bhtower (S (length (map BH_denote ys))) f (BH_denote y))
                      (BH_denote y1) (map BH_denote ys)) (map BH_denote ys))
    (Hx3 : stable_form x /\ stable_form x1 /\ each stable_form xs)
    (Hy3 : stable_form y /\ stable_form y1 /\ each stable_form ys)
    (Hlen : length xs = length ys)
    (Hlim : (S (length xs) <= 1)%nat \/
              limitOrdinal
                (BH_stack (bhtower (S (length (map BH_denote xs))) f (BH_denote x))
                   (BH_denote x1) (map BH_denote xs)) /\
                limitOrdinal
                  (BH_stack (bhtower (S (length (map BH_denote ys))) f (BH_denote y))
                     (BH_denote y1) (map BH_denote ys)))
    (Heq : BH_stack (bhtower (S (length (map BH_denote xs))) f (BH_denote x))
             (BH_denote x1) (map BH_denote xs)
             ≈ BH_stack (bhtower (S (length (map BH_denote ys))) f (BH_denote y))
             (BH_denote y1) (map BH_denote ys))
    (Hord : BH_denote x < BH_denote y)
    (P:Prop), P.
Proof.
  intros.

  repeat rewrite map_length in Heq.
  inversion Hlen. rewrite H0 in Heq.

  elim (ord_lt_irreflexive
          (BH_stack (bhtower (S (length ys)) f (BH_denote x)) (BH_denote x1) (map BH_denote xs))).
  rewrite Heq at 2.

  assert (Hlen2: (length xs = 0 \/ length xs > 0)%nat) by lia.
  destruct Hlen2.
  { simpl in H. destruct ys; [ | simpl in *; lia ].
    simpl.
    destruct xs; [ | simpl in *; lia ].
    simpl in *.
    rewrite <- bhtower_fixpoint with (a:= BH_denote x) (b:=BH_denote y); auto with ord arith.
    apply normal_increasing; auto with ord.
    rewrite <- Heq.
    intuition. }
  destruct Hlim as [?|[Hlim1 Hlim2]]; [ lia |].
  inversion Hy1.
  + simpl in *. rewrite map_length in H1. lia.
  + rewrite H3 in Hord.
    elim (ord_lt_irreflexive 0).
    apply ord_le_lt_trans with (BH_denote x); auto with ord.
  + generalize (compare_stack_lt_long (BH_denote x) (BH_denote y)
                  (map BH_denote (x1::xs)) (map BH_denote (y1::ys)) f).
    simpl. repeat rewrite map_length.
    rewrite H0.
    intro Hcut; apply Hcut; clear Hcut; intuition.
    rewrite map_length in Hlim2. auto.
    unfold each_lt. simpl; auto; split.
    * rewrite <- Heq.
      rewrite map_length in H13. rewrite <- H0.
      assumption.
    * revert H14.
      apply each_implies. intro q.
      rewrite map_length. rewrite H0.
      rewrite Heq. auto.
  + generalize (compare_stack_lt_long (BH_denote x) (BH_denote y)
                  (map BH_denote (x1::xs)) (map BH_denote (y1::ys)) f).
    simpl. repeat rewrite map_length.
    rewrite H0.
    intro Hcut; apply Hcut; clear Hcut; intuition.
    rewrite map_length in Hlim2. auto.
    unfold each_lt. simpl; split.
    * rewrite <- Heq.
      rewrite map_length in H14. rewrite <- H0.
      assumption.
    * revert H15.
      apply each_implies. intro q.
      rewrite map_length. rewrite H0.
      rewrite Heq. auto.
Qed.


Lemma normal_list_stack_unique_denotations:
  forall xs ys x y f,
    normal_function f ->
    stable_list (map BH_denote (x::xs)) ->
    stable_list (map BH_denote (y::ys)) ->
    each (fun a => a < BH_stack f (BH_denote x) (map BH_denote xs)) (map BH_denote (x::xs)) ->
    each (fun a => a < BH_stack f (BH_denote y) (map BH_denote ys)) (map BH_denote (y::ys)) ->
    each stable_form (x::xs) ->
    each stable_form (y::ys) ->
    length xs = length ys ->
    ((length xs <= 1)%nat \/
       (limitOrdinal (BH_stack f (BH_denote x) (map BH_denote xs)) /\
        limitOrdinal (BH_stack f (BH_denote y) (map BH_denote ys)))) ->
    BH_stack f (BH_denote x) (map BH_denote xs) ≈ BH_stack f (BH_denote y) (map BH_denote ys) ->
    pairwise (fun a b => BH_denote a ≈ BH_denote b) (x::xs) (y::ys).
Proof.
  induction xs as [|x1 xs Hind].
  { intros [|y1 ys] x y f Hf Hx1 Hy1 Hx2 Hy2 Hx3 Hy3 Hlen Hlim Heq.
    - simpl in *. constructor.
      assert (Hord: ordering_correct (bhcompare x y) (BH_denote x) (BH_denote y)).
      { apply bhcompare_correct; intuition. }
      destruct (bhcompare x y); simpl in *; auto.
      + elim (ord_lt_irreflexive (f (BH_denote x))).
        apply ord_lt_le_trans with (f (BH_denote y)); auto with ord.
        apply normal_increasing; auto.
        apply Heq.
      + elim (ord_lt_irreflexive (f (BH_denote y))).
        apply ord_lt_le_trans with (f (BH_denote x)); auto with ord.
        apply normal_increasing; auto.
        apply Heq.
      + constructor.
    - simpl in *. discriminate. }

  intros [|y1 ys] x y f Hf Hx1 Hy1 Hx2 Hy2 Hx3 Hy3 Hlen Hlim Heq.
  { simpl in *. discriminate. }

  assert (Hxy : BH_denote x ≈ BH_denote y).
  { clear Hind.
    assert (Hord: ordering_correct (bhcompare x y) (BH_denote x) (BH_denote y)).
    { apply bhcompare_correct; simpl in *; intuition. }
    destruct (bhcompare x y); simpl in *; auto.

    - apply (unique_denote_lt_impossible x1 xs y1 ys x y f); auto.
    - apply (unique_denote_lt_impossible y1 ys x1 xs y x f); auto with ord.
      lia.
      intuition. lia.
      symmetry. auto. }

  constructor; auto.

  apply Hind with (f := (bhtower (S (length (map BH_denote xs))) f (BH_denote x))); eauto.

  - apply Hx2.
  - cut (each (fun a => a <
                          BH_stack (bhtower (S (length (map BH_denote ys))) f (BH_denote y))
                            (BH_denote y1) (map BH_denote ys)) (map BH_denote (y1 :: ys))).
    { apply each_implies.
      intro q.
      repeat rewrite map_length.
      simpl in Hlen; inversion Hlen.
      rewrite H0.
      intros.
      eapply ord_lt_le_trans; [ apply H |].
      apply BH_stack_monotone; auto with ord.
      intros; apply bhtower_monotone; auto with ord.
      apply Hxy.
      apply pairwise_le_refl. }

    apply Hy2.

  - simpl in *; intuition.
  - simpl in *; intuition.
  - intuition.
    right. simpl in *.
    repeat rewrite map_length in *.
    inversion Hlen. rewrite <- H2 in H1.
    split; auto.
    assert
      (BH_stack (bhtower (S (length xs)) f (BH_denote x)) (BH_denote y1) (map BH_denote ys) ≈
       BH_stack (bhtower (S (length xs)) f (BH_denote y)) (BH_denote y1) (map BH_denote ys)).
    { split; apply BH_stack_monotone; auto with ord.
      intros. apply bhtower_monotone; auto with ord. apply Hxy. apply pairwise_le_refl.
      intros. apply bhtower_monotone; auto with ord. apply Hxy. apply pairwise_le_refl. }
    rewrite H.
    auto.

  - simpl in Heq.
    rewrite Heq.
    simpl in Hlen. inversion Hlen.
    repeat rewrite map_length. rewrite H0.
    split; apply BH_stack_monotone; auto with ord.
    intros. apply bhtower_monotone; auto with ord.
    apply Hxy.
    apply pairwise_le_refl.
    intros. apply bhtower_monotone; auto with ord.
    apply Hxy.
    apply pairwise_le_refl.
Qed.


Lemma leading_stack_zeros n x xs :
  BH_full_stack (stackZeros n (x::xs)) ≈ BH_full_stack (x::xs).
Proof.
  induction n; simpl; auto with ord.
  simpl in *.
  rewrite <- IHn.
  destruct n; simpl stackZeros.
  apply BH_stack_leading_zero; auto with ord.
  apply BH_stack_leading_zero; auto with ord.
Qed.


Lemma unique_denote_length_lt_impossible
    x xs y ys
    (Hxs : normal_list (BH_denote x :: map BH_denote xs))
    (Hys : normal_list (BH_denote y :: map BH_denote ys))
    (Hxs2 : stable_form x /\ each stable_form xs)
    (Hys2 : stable_form y /\ each stable_form ys)
    (Heq : BH_stack (addOrd 1) (BH_denote x) (map BH_denote xs)
      ≈ BH_stack (addOrd 1) (BH_denote y) (map BH_denote ys))
    (Hlen: (length xs < length ys)%nat) :
  forall (P:Prop), P.
Proof.
  assert (H: BH_stack (addOrd 1) (BH_denote x) (map BH_denote xs) ≈
            BH_full_stack (stackZeros (length ys - length xs) (map BH_denote (x::xs)))).
  { symmetry. apply leading_stack_zeros. }

  assert (Hlt: BH_stack (addOrd 1) (BH_denote x) (map BH_denote xs) <
            BH_stack (addOrd 1) (BH_denote y) (map BH_denote ys)).
  { rewrite H.
    case_eq (length ys - length xs); intros; [ lia | ].
    simpl.

    assert (Hlen2: (length ys <= 1 \/ length ys > 1)%nat) by lia.
    destruct Hlen2.

    { apply compare_stack_lt_short; simpl; auto.
      split. apply zero_complete.
      clear.
      induction n; simpl; auto.
      split; auto.
      apply zero_complete.
      rewrite stackZeros_length. simpl.
      repeat rewrite map_length.
      lia.
      rewrite map_length in *. lia.
      destruct Hys as [? [??]]. simpl in *.
      destruct ys; simpl in *; auto. discriminate.
      unfold each_lt.
      unfold normal_list in Hxs.
      destruct Hxs as [?[? Heach]].
      clear -Heach Heq.
      induction n; auto.
      revert Heach; apply each_implies; simpl; auto.
      intros. rewrite <- Heq; auto.
      simpl; split.
      apply BH_stack_nonzero; auto.
      simpl; auto.
      auto. }

    assert (Hlim:limitOrdinal (BH_stack (addOrd 1) (BH_denote y) (map BH_denote ys))).
    { assert (BH_denote y > 0).
      { destruct Hys as [?[??]]. simpl in *.
        destruct ys; simpl in *; try lia; auto. }

      assert (ordering_correct (bhcompare BH1 y) (BH_denote BH1) (BH_denote y)).
      { apply bhcompare_correct; auto.
        unfold BH1.
        rewrite stable_form_BH; simpl; intuition.
        constructor; simpl. auto with arith.
        unfold BH0.
        rewrite stable_form_BH; simpl; intuition.
        constructor; simpl; auto with arith.
        intuition. }

      destruct (bhcompare BH1 y); simpl in *.
      - rewrite addOrd_zero_r in *.
        apply BH_full_stack_limit2; simpl; auto.
        rewrite map_length. auto.
      - rewrite addOrd_zero_r in *.
        assert (BH_stack (addOrd 1) (BH_denote y) (map BH_denote ys) ≈
                  BH_stack (addOrd 1) 1 (map BH_denote ys)).
        { split; apply BH_stack_monotone; auto with ord.
          apply H3. apply pairwise_le_refl.
          apply H3. apply pairwise_le_refl. }
        rewrite H4.
        apply BH_full_stack_limit1; simpl; auto.
        rewrite map_length. auto.
      -  rewrite addOrd_zero_r in *.
         destruct ys; simpl in *; try lia.
         rewrite ord_lt_unfold in H3. destruct H3. simpl in *.
         elim (ord_lt_irreflexive 0).
         apply ord_lt_le_trans with (BH_denote y); auto.
    }

    unfold normal_list in Hys. destruct Hys as [? [Hstable ?]].
    inversion Hstable; simpl in *.

    - rewrite map_length in *. lia.

    - destruct ys; simpl in *. lia.
      elim (ord_lt_irreflexive 0).
      rewrite <- H6 at 2. auto.

    - apply compare_stack_lt_long; simpl; auto.
      split. apply zero_complete.
      clear.
      induction n; simpl; auto.
      split; auto.
      apply zero_complete.
      rewrite stackZeros_length. simpl.
      repeat rewrite map_length.
      lia.
      destruct ys; simpl in *; auto.
      lia.

      destruct Hxs as [?[? Heach]].
      unfold each_lt; simpl.

      clear -Heach Heq.
      induction n; simpl stackZeros.
      revert Heach; apply each_implies; simpl; auto.
      intros. rewrite <- Heq; auto.
      simpl; split.
      apply BH_stack_nonzero; auto.
      simpl; auto.
      auto.

    - apply compare_stack_lt_long; simpl; auto.
      split. apply zero_complete.
      clear.
      induction n; simpl; auto.
      split; auto.
      apply zero_complete.
      rewrite stackZeros_length. simpl.
      repeat rewrite map_length.
      lia.
      destruct ys; simpl in *; auto.
      lia.

      destruct Hxs as [?[? Heach]].
      unfold each_lt; simpl.

      clear -Heach Heq.
      induction n; simpl stackZeros.
      revert Heach; apply each_implies; simpl; auto.
      intros. rewrite <- Heq; auto.
      simpl; split.
      apply BH_stack_nonzero; auto.
      simpl; auto.
      auto.
  }

  elim (ord_lt_irreflexive (BH_stack (addOrd 1) (BH_denote x) (map BH_denote xs))).
  rewrite Heq at 2. auto.
Qed.


Lemma normal_list_full_stack_unique_denotations:
  forall xs ys,
    normal_list (map BH_denote xs) ->
    normal_list (map BH_denote ys) ->
    each stable_form xs ->
    each stable_form ys ->
    BH_full_stack (map BH_denote xs) ≈ BH_full_stack (map BH_denote ys) ->
    pairwise (fun a b => BH_denote a ≈ BH_denote b) xs ys.
Proof.
  intros [|x xs] [|y ys]; simpl; intros Hxs Hys Hxs2 Hys2 H.
  - constructor.
  - elim (ord_lt_irreflexive 0).
    rewrite H at 2.
    apply BH_stack_nonzero; simpl; auto.
  - elim (ord_lt_irreflexive 0).
    rewrite <- H at 2.
    apply BH_stack_nonzero; simpl; auto.
  - assert (Hlen: length xs = length ys).
    { generalize (nat_compare_correct (length xs) (length ys)).
      destruct (nat_compare (length xs) (length ys)); intros; auto.
      - apply (unique_denote_length_lt_impossible x xs y ys); auto.
      - apply (unique_denote_length_lt_impossible y ys x xs); auto.
        symmetry. auto. }

    unfold normal_list in *.
    apply normal_list_stack_unique_denotations with (f:=addOrd 1); intuition eauto.
    + simpl; auto.
    + simpl; auto.
    + assert (Hlen2: (length xs <= 1 \/ length xs > 1)%nat) by lia.
      destruct Hlen2; auto.
      right. split.

      * assert (ordering_correct (bhcompare BH1 x) (BH_denote BH1) (BH_denote x)).
        { apply bhcompare_correct; auto.
          unfold BH1.
          rewrite stable_form_BH; simpl; intuition.
          constructor; simpl. auto with arith.
          unfold BH0.
          rewrite stable_form_BH; simpl; intuition.
          constructor; simpl; auto with arith. }

        destruct (bhcompare BH1 x).
        ** simpl in *.
           rewrite addOrd_zero_r in *.
           apply BH_full_stack_limit2; simpl; auto.
           rewrite map_length. auto.
        ** simpl in *.
           rewrite addOrd_zero_r in *.
           assert (BH_stack (addOrd 1) (BH_denote x) (map BH_denote xs) ≈
                     BH_stack (addOrd 1) 1 (map BH_denote xs)).
           { split; apply BH_stack_monotone; auto with ord.
             apply H11. apply pairwise_le_refl.
             apply H11. apply pairwise_le_refl. }
           rewrite H12.
           apply BH_full_stack_limit1; simpl; auto.
           rewrite map_length. auto.
        ** simpl in *.
           rewrite addOrd_zero_r in *.
           destruct xs; simpl in *; try lia.
           rewrite ord_lt_unfold in H11. destruct H11. simpl in *.
           elim (ord_lt_irreflexive 0).
           apply ord_lt_le_trans with (BH_denote x); auto.

      * assert (ordering_correct (bhcompare BH1 y) (BH_denote BH1) (BH_denote y)).
        { apply bhcompare_correct; auto.
          unfold BH1.
          rewrite stable_form_BH; simpl; intuition.
          constructor; simpl. auto with arith.
          unfold BH0.
          rewrite stable_form_BH; simpl; intuition.
          constructor; simpl; auto with arith. }

        destruct (bhcompare BH1 y).
        ** simpl in *.
           rewrite addOrd_zero_r in *.
           apply BH_full_stack_limit2; simpl; auto.
           rewrite map_length. lia.
        ** simpl in *.
           rewrite addOrd_zero_r in *.
           assert (BH_stack (addOrd 1) (BH_denote y) (map BH_denote ys) ≈
                     BH_stack (addOrd 1) 1 (map BH_denote ys)).
           { split; apply BH_stack_monotone; auto with ord.
             apply H11. apply pairwise_le_refl.
             apply H11. apply pairwise_le_refl. }
           rewrite H12.
           apply BH_full_stack_limit1; simpl; auto.
           rewrite map_length. lia.
        ** simpl in *.
           rewrite addOrd_zero_r in *.
           destruct ys; simpl in *; try lia.
           rewrite ord_lt_unfold in H11. destruct H11. simpl in *.
           elim (ord_lt_irreflexive 0).
           apply ord_lt_le_trans with (BH_denote y); auto.
Qed.


Lemma normal_is_stable x: normal_form x -> stable_form x.
Proof.
  induction x as [xs Hind] using BHForm_induction.
  unfold normal_form; simpl; intros.
  rewrite stable_form_BH.
  rewrite BH_each_unfold in H.
  intuition.
  unfold normal_list in H0. intuition.
  clear H0.
  induction xs; simpl in *; intuition.
Qed.

Theorem normal_forms_unique : forall x y,
    normal_form x ->
    normal_form y ->
    BH_denote x ≈ BH_denote y ->
    x = y.
Proof.
  induction x as [xs Hind] using BHForm_induction.
  intros [ys].
  repeat rewrite normal_form_BH.
  simpl.
  intros [Hxs1 Hxs2] [Hys1 Hys] H.
  apply f_equal.

  assert (Hpw: pairwise (fun a b => BH_denote a ≈ BH_denote b) xs ys).
  { apply normal_list_full_stack_unique_denotations; auto.
    revert Hxs2. apply each_implies.
    apply normal_is_stable.
    revert Hys. apply each_implies.
    apply normal_is_stable. }

  clear Hxs1 Hys1 H.
  induction Hpw; simpl in *; intuition.
  f_equal; auto.
Qed.


Fixpoint BH_cantor_decompose (x:BHForm) : list BHForm :=
  match x with
  | BH xs =>
      match xs with
      | []    => []
      | [a]   => BH0 :: BH_cantor_decompose a
      | [a;b] => a :: BH_cantor_decompose b
      | _     => [x]
      end
  end.


Fixpoint BH_cantor_recompose (xs:list BHForm) : BHForm :=
  match xs with
  | [] => BH0
  | (BH [] :: xs') => BH [BH_cantor_recompose xs']
  | (x     :: [] ) =>
      match bhcompare x (BH [x; BH0]) with
      | LT => BH [x; BH0]
      | _ => x
      end
  | (x     :: xs') => BH [x; BH_cantor_recompose xs']
  end.

Lemma cantor_ordered_lt_left:
  forall xs x,
    each normal_form (x::xs) ->
    cantor_ordered BH_denote (x::xs) ->
    cantor_denote BH_denote xs < cantor_denote BH_denote (x::xs).
Proof.
  induction xs; simpl; intuition.
  - rewrite addOrd_zero_r.
    apply expOrd_nonzero.
  - assert (Hax : BH_denote a < BH_denote x \/ BH_denote a ≈ BH_denote x).
    { generalize (bhcompare_correct a x).
      destruct (bhcompare a x); simpl; intuition.
      left. apply H3; apply normal_is_stable; auto.
      right. apply H3; apply normal_is_stable; auto.
      elim (ord_lt_irreflexive (BH_denote a)).
      apply ord_le_lt_trans with (BH_denote x); auto.
      apply H3; apply normal_is_stable; auto. }
    destruct Hax.
    + apply ord_lt_le_trans with (expOrd ω (BH_denote a) + (expOrd ω (BH_denote x) + (expOrd ω (BH_denote a) + cantor_denote BH_denote xs))).
      * apply addOrd_increasing.
        rewrite <- addOrd_le2.
        apply IHxs; simpl; intuition.
      * rewrite addOrd_assoc.
        apply addOrd_monotone; auto with ord.
        apply expOrd_add_collapse; auto with ord.
    + rewrite H3 at 1.
      apply addOrd_increasing.
      apply IHxs; simpl; intuition.
Qed.


Lemma BHcantor_recomp_correct:
  forall xs,
    each normal_form xs ->
    cantor_ordered BH_denote xs ->
    normal_form (BH_cantor_recompose xs) /\
      cantor_denote BH_denote xs ≈ BH_denote (BH_cantor_recompose xs).
Proof.
  induction xs; simpl; intuition.
  - unfold BH0.
    rewrite normal_form_BH. simpl; intuition.
    hnf; simpl; intuition.
    constructor; simpl; auto.
  - destruct a as [ys].
    destruct ys; simpl; auto.
    rewrite normal_form_BH; simpl; intuition.
    hnf; simpl; intuition.
    constructor; simpl; auto.

    clear -H H3.
    induction xs; simpl in *; intuition.
    destruct a; simpl in *.
    destruct l; simpl in *.
    apply addOrd_increasing.
    apply IHxs; auto.
    elim (ord_lt_irreflexive 0).
    rewrite <- H at 2.
    apply BH_stack_nonzero; simpl; auto.

    destruct xs as [|x xs].

    + generalize (bhcompare_correct (BH (b :: ys)) (BH [BH (b :: ys); BH0])).
      destruct (bhcompare (BH (b :: ys)) (BH [BH (b :: ys); BH0])).
      * intros. rewrite normal_form_BH.
        split; simpl each; auto.
        hnf. split.
        simpl; auto.
        apply BH_stack_nonzero; auto with ord.
        simpl; auto.
        split.
        constructor; simpl; auto.
        simpl each.
        split.
        apply H4.
        apply normal_is_stable; auto.
        rewrite stable_form_BH.
        split; simpl each; auto.
        constructor; simpl; auto.
        intuition; apply normal_is_stable; auto.
        split; auto.
        apply bhtower_nonzero; auto with ord.
      * intros; auto.
      * intros; auto.
    + rewrite normal_form_BH.
      split.
      * hnf. simpl. intuition.
        ** apply BH_stack_nonzero; simpl; auto.
        ** constructor. simpl; auto.

        ** rewrite bhtower_index_one; auto.
           rewrite veblen_onePlus; auto with ord.
           apply ord_le_lt_trans with (expOrd ω (BH_stack (addOrd 1) (BH_denote b) (map BH_denote ys) ) + 0).
           { rewrite addOrd_zero_r.
             apply normal_inflationary; auto with ord.
             apply BH_stack_complete; simpl; auto with ord. }
           apply addOrd_increasing; auto with ord.
           destruct x. destruct l; simpl.
           rewrite <- addOrd_le1.
           auto with ord.
           destruct xs; simpl.
           destruct (bhcompare (BH (b0 :: l)) (BH [BH (b0 :: l); BH0])); simpl.
           apply bhtower_nonzero; auto with ord.
           apply BH_stack_nonzero; simpl; auto with ord.
           apply BH_stack_nonzero; simpl; auto with ord.
           apply bhtower_nonzero; auto with ord.
           apply BH_stack_complete; simpl; auto with ord.
        ** simpl in *.
           rewrite bhtower_index_one; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           rewrite <- H5.
           apply (cantor_ordered_lt_left (x :: xs) (BH (b::ys))); simpl; intuition.
           apply BH_stack_complete; simpl; auto.
      * simpl each; auto.
  - destruct a as [ys].
    destruct ys; simpl.
    + rewrite expOrd_zero.
      rewrite H5; auto with ord.
    + destruct xs; simpl.
      * generalize (bhcompare_correct (BH (b :: ys)) (BH [BH (b :: ys); BH0])).
        destruct (bhcompare (BH (b :: ys)) (BH [BH (b :: ys); BH0])); simpl; intros.
        ** rewrite bhtower_index_one; auto.
           rewrite veblen_onePlus; auto with ord.
           apply BH_stack_complete; simpl; auto.
        ** rewrite addOrd_zero_r.
           rewrite H4 at 2.
           rewrite bhtower_index_one; auto.
           rewrite veblen_onePlus; auto with ord.
           rewrite addOrd_zero_r. reflexivity.
           apply BH_stack_complete; simpl; auto.
           apply normal_is_stable. auto.
           rewrite stable_form_BH. split; simpl each; intuition.
           constructor; simpl; auto.
           apply normal_is_stable; auto.
           unfold BH0.
           rewrite stable_form_BH. simpl; intuition.
           constructor; simpl; auto.
        ** elim (ord_lt_irreflexive (BH_full_stack (map BH_denote (b::ys)))).
           apply ord_le_lt_trans with (bhtower 1 (addOrd 1) (BH_stack (addOrd 1) (BH_denote b) (map BH_denote ys)) 0).
           apply normal_inflationary with (f:= fun x => bhtower 1 _ x 0); auto with ord.
           apply BH_stack_complete; simpl; auto.
           apply H4.
           apply normal_is_stable; auto.
           rewrite stable_form_BH. split; simpl each; intuition.
           constructor; simpl; auto.
           apply normal_is_stable; auto.
           unfold BH0.
           rewrite stable_form_BH.
           simpl; intuition.
           constructor; simpl; auto.
      * simpl in *. rewrite H5.
        rewrite bhtower_index_one; auto with ord.
        rewrite veblen_onePlus; auto with ord.
        apply BH_stack_complete; simpl; auto.
Qed.


Lemma BHcantor_decomp_correct :
  forall x,
    normal_form x ->
    each normal_form (BH_cantor_decompose x) /\
    cantor_ordered BH_denote (BH_cantor_decompose x) /\
    BH_denote x ≈ cantor_denote BH_denote (BH_cantor_decompose x).
Proof.
  induction x as [xs Hind] using BHForm_induction.
  destruct xs as [|a xs].
  { simpl in *; intuition. }
  destruct xs as [|b xs].
  { simpl in *.
    unfold BH0.
    rewrite normal_form_BH in *; simpl; intuition.
    - rewrite normal_form_BH in *; simpl; auto.
      split; auto. hnf; simpl; intuition.
      constructor; simpl; auto with arith.
    -  hnf in H2. simpl in *.
       case_eq (BH_cantor_decompose a); intros; auto.
       rewrite H5 in *. simpl in *.
       intuition.
       rewrite H6 in H8.
       destruct b as [bs].
       destruct bs as [|b bs]; simpl; auto with ord.
       elim (ord_lt_irreflexive
               (expOrd ω (BH_denote (BH (b :: bs))) + cantor_denote BH_denote l)).
       eapply ord_lt_le_trans; [ apply H8 | ].
       rewrite addOrd_assoc.
       apply addOrd_monotone; auto with ord.
       apply additively_closed_collapse.
       apply expOmega_additively_closed; auto.
       apply ord_lt_le_trans with (expOrd ω 1).
       rewrite expOrd_one'; auto.
       apply omega_gt1.
       apply omega_gt0.
       apply expOrd_monotone; auto with ord.
       simpl.
       apply succ_least.
       apply BH_stack_nonzero; auto.
       simpl; auto.
    - rewrite expOrd_zero.
      rewrite H6. auto with ord. }
  destruct xs as [|c xs].
  { rewrite normal_form_BH in *.
    simpl in *; intuition; auto with ord.
    hnf in H2. simpl in *; intuition.
    destruct (BH_cantor_decompose b); auto.
    simpl in *.
    rewrite H10 in H12 at 1.
    rewrite bhtower_index_one in H12; auto with ord.
    rewrite veblen_onePlus in H12; auto with ord.
    rewrite H10 in H12.

    assert (stable_form b0).
    { apply normal_is_stable; intuition. }
    assert (stable_form a).
    { apply normal_is_stable; intuition. }
    generalize (bhcompare_correct b0 a).
    destruct (bhcompare b0 a); simpl; auto with ord.
    intros. apply H16; auto.
    intros.
    elim (ord_lt_irreflexive (expOrd ω (BH_denote b0) + cantor_denote BH_denote l)).
    eapply ord_lt_le_trans; [ apply H12 | ].
    rewrite addOrd_assoc.
    apply addOrd_monotone; auto with ord.
    apply expOrd_add_collapse; auto.

    rewrite bhtower_index_one; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    rewrite H10. reflexivity. }

  intuition; simpl; auto.
  rewrite addOrd_zero_r.
  split. apply normal_inflationary; auto.
  apply BH_stack_complete; simpl; auto with ord.

  assert (ordering_correct (bhcompare BH1 a) (BH_denote BH1) (BH_denote a)).
  { rewrite normal_form_BH in H. simpl in *; intuition.
    apply bhcompare_correct.
    unfold BH1.
    rewrite stable_form_BH. simpl; intuition.
    constructor; simpl; auto.
    unfold BH0.
    rewrite stable_form_BH. simpl; intuition.
    constructor; simpl; auto.
    apply normal_is_stable; auto. }
  destruct (bhcompare BH1 a); simpl in *.
  - rewrite addOrd_zero_r in H0.
    apply (BH_full_stack_epsilon2 (BH_denote a) (map BH_denote (b::c::xs))); simpl; auto with ord arith.
  - rewrite addOrd_zero_r in H0.
    apply (BH_full_stack_epsilon1' (BH_denote a) (map BH_denote (b::c::xs))); simpl; auto with ord arith; auto.
    rewrite normal_form_BH in H. intuition.
    hnf in H3. simpl in *; intuition.
    inversion H4; subst; auto.
    + simpl in *. lia.
    + elim (ord_lt_irreflexive (BH_denote a)).
      rewrite H22 at 1. auto.
    + rewrite <- H0 in H22.
      elim (successor_not_limit 1); auto.
      rewrite ord_isSucc.
      exists 0. reflexivity.
    + symmetry. assumption.
  - rewrite addOrd_zero_r in H0.
    rewrite ord_lt_unfold in H0.
    destruct H0. simpl in *.
    rewrite normal_form_BH in H.
    simpl in *; intuition.
    hnf in H3. simpl in *.
    intuition.
    elim (ord_lt_irreflexive (BH_denote a)).
    rewrite H0 at 1. auto.
Qed.


Definition BH_has_cantor_decomposition : has_cantor_decomposition BH_denote normal_form :=
  Build_has_cantor_decomposition
    BH_denote normal_form
    bhcompare
    BH_cantor_decompose
    BH_cantor_recompose
    BHForm_complete
    (fun x y Hx Hy => bhcompare_correct x y (normal_is_stable x Hx) (normal_is_stable y Hy))
    BHcantor_decomp_correct
    BHcantor_recomp_correct.


(* TODO: need to build and prove correct a normalization procedure.
   We can use the cantor_decide procedure to build the stabalization
   subroutine.
*)

(*
Fixpoint zerosAndArgument x xs : option (nat * BHForm) :=
  match xs with
  | [] => Some (0%nat, x)
  | x1::xs =>
      match x1 with
      | BH [] =>
          match zerosAndArgument x1 xs with
          | None => None
          | Some (n,arg) => Some (S n, arg)
          end
      | _ => None
      end
  end.


Fixpoint stabalize_zeros x n :=




Fixpoint stabalize x xs {struct xs} :=
  match xs with
  | [] => [x]
  | [x1] => [x;x1]
  | x1::xs =>
      match cantor_list_pred BH_has_cantor_decomposition (BH_cantor_decompose x) with
      | Some l =>
          match zerosAndArgument x1 xs with
          | None => x :: stabalize x1 xs
          | Some (n,arg) => BH_cantor_recompose l :: stabalize_zeros arg n
          end
      | None => x :: stabalize x1 xs
      end
  end.


Fixpoint dropLeadingZeros x xs :=
  match xs with
  | [] => [x]
  | x1::xs =>
      match x with
      | BH [] => dropLeadingZeros x1 xs
      | _     => stabalize x (x1::xs)
      end
  end.
*)


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem BH_has_enough_notations (EM:excluded_middle) :
  forall x:Ord, x < BachmanHoward -> exists a:BHForm, BH_denote a ≈ x.
Proof.
  induction x as [x Hind] using ordinal_induction; intros.
  destruct (classical.ordinal_discriminate EM x) as [Hz|[Hs|Hlim]].
  - exists (BH []).
    simpl. rewrite ord_isZero in Hz. symmetry; auto.

  - rewrite ord_isSucc in Hs. destruct Hs as [o Hs].
    destruct (Hind o) as [a Ha]; auto with ord.
    rewrite Hs; auto with ord.
    transitivity x; auto with ord.
    rewrite Hs; auto with ord.

    admit. (* annoying... we need a to be normal here *)

  - destruct (BachmanHoward_limit_decompose EM x Hlim H) as [xs [Hxs1 Hxs2]].
    assert (exists vs, pairwise ord_eq (map BH_denote vs) xs).
    { clear Hxs1. unfold each_lt in *.
      induction xs; simpl in *; intuition.
      exists []. constructor.
      destruct (Hind a) as [v Hv]; auto.
      transitivity x; auto.
      destruct H2 as [vs Hvs].
      exists (v::vs).
      constructor; auto. }
    destruct H0 as [vs Hvs].
    exists (BH vs).
    rewrite Hxs1.
    clear -Hvs. simpl.
    induction Hvs; simpl; auto with ord.
    split; apply BH_stack_monotone; auto with ord.
    apply H.
    clear -Hvs. induction Hvs; constructor; auto.
    apply H.
    apply H.
    clear -Hvs. induction Hvs; constructor; auto.
    apply H.
Abort.


(*

Fixpoint BH_compare (x:BHForm) : BHForm -> ordering :=
  fix inner (y:BHForm) : ordering :=
    match x, y with
    | BH xs0, BH ys0 =>
        (fix compare_sequence (xs:list BHForm) : list BHForm -> ordering :=
           fix compare_sequence_inner (ys:list BHForm) : ordering :=
             match xs with
             | []  => if bh_isZero y then EQ else LT
             | [x] =>  match ys with
                       | []  => GT
                       | [y] => BH_compare x y
                       | _   => LT
                       end
             | (x::xs) =>
                 if bh_isZero x then compare_sequence xs ys else
                   match ys with
                   | []  => GT
                   | (y::ytail) =>
                       if isNil ytail then LT else
                         if bh_isZero y then compare_sequence_inner ytail else
                           match nat_compare (length xs) (length ytail) with
                           | LT => LT
                           | EQ => match BH_compare x y with
                                   | LT => (fix check_lt (xs:list BHForm) :=
                                              match xs with
                                              | [] => LT
                                              | (x'::xs') =>
                                                  match BH_compare x' y with
                                                  | LT => check_lt xs'
                                                  | EQ => if bh_allZero (x'::xs') then EQ else GT
                                                  | GT => GT
                                                  end
                                              end
                                           ) xs
                                   | EQ => compare_sequence xs ytail
                                   | GT => (fix check_gt (ys':list BHForm) :=
                                              match ys' with
                                              | [] => GT
                                              | (y'::ys'') =>
                                                  match inner y' with
                                                  | LT => LT
                                                  | EQ => if bh_allZero ys' then EQ else LT
                                                  | GT => check_gt ys''
                                                  end
                                              end
                                           ) ytail
                                   end
                           | GT => GT
                           end
                   end
             end) xs0 ys0
    end.
*)
