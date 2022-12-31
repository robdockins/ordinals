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



(*
Fixpoint BH_normal (x:BHForm) : Prop :=
  match x with
  | BH xs0 =>
      (fix each_normal (xs:list BHForm) : Prop :=
         match xs with
         | [] => True
         | (x::xs') => BH_normal x /\ each_normal xs'
         end
      ) xs0 /\
        match xs0 with
        | []  => True
        | [x] => BH_denote x < ω
        | x::xs => BH_denote x > 0 /\ stable x xs
        end
  end.

Inductive BH_norm_graph : BHForm -> BHForm -> Prop :=
| 


Definition no_leading_zeros (xs:list BHForm) :=
  match xs with
  | [] => True
  | (x::_) => x <> BH []
  end.

Definition stable (x:BHForm) (xs:list BHForm) :=
  case xs of
  | [] => True
  | (y::ys) => 
             

*)



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

Fixpoint stable_form (x:BHForm) : Prop :=
  match x with
  | BH xs0 =>
      stable_list (map BH_denote xs0) /\
        (fix substable (xs:list BHForm) : Prop :=
           match xs with
           | [] => True
           | (x::xs') => stable_form x /\ substable xs'
           end
        ) xs0
  end.

Lemma stable_form_BH : forall xs,
    stable_form (BH xs) <-> (stable_list (map BH_denote xs) /\ each stable_form xs).
Proof.
  simpl; intuition.
  clear H0.
  induction xs; simpl in *; intuition.
  clear H0.
  induction xs; simpl in *; intuition.
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

Lemma bhcompare_correct :
  forall x y,
    stable_form x ->
    stable_form y ->
    ordering_correct (bhcompare x y) (BH_denote x) (BH_denote y).
Proof.
  intros. unfold bhcompare.
  destruct (bhcompare_loop x y (Wf_nat.lt_wf (BH_termSize x + BH_termSize y)%nat)).
  apply compare_graph_correct; auto.
Qed.


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
