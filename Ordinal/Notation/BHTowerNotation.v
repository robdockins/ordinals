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
From Ordinal Require Import BHTower.

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

Reserved Notation "{ x , y } ~~~> z" (at level 70, format "{ x , y }  ~~~>  z"). 
Reserved Notation "{ a , x , y , b } ~~> z" (at level 70, format "{ a , x , y , b }  ~~>  z"). 

Inductive BH_compare_graph : BHForm -> BHForm -> ordering -> Prop :=

| BH_compare_node : forall xs ys o,
    { BH xs, xs, ys, BH ys } ~~> o  ->
    { BH xs, BH ys } ~~~> o

where "{ x , y } ~~~> z" := (BH_compare_graph x y z)

with BH_compare_seq_graph : BHForm -> list BHForm -> list BHForm -> BHForm -> ordering -> Prop :=
| BH_compare_zero_eq: forall xtop ytop,
    { xtop, [], [], ytop } ~~> EQ

| BH_compare_zero_l: forall xtop ytop y ys,
    { xtop, [], (y::ys), ytop } ~~> LT

| BH_compare_zero_r: forall xtop ytop x xs,
    { xtop, (x::xs), [], ytop } ~~> GT

| BH_compare_one: forall xtop ytop x y o,
    { x, y } ~~~> o ->
    { xtop, [x], [y], ytop } ~~> o

| BH_compare_leading_zero_l : forall xtop ytop x xs ys o,
    x = BH [] ->
    xs <> [] ->
    { xtop, xs, ys, ytop } ~~> o ->
    { xtop, x::xs, ys, ytop } ~~> o

| BH_compare_leading_zero_r : forall xtop ytop xs y ys o,
    y = BH [] ->
    ys <> [] ->
    { xtop, xs, ys, ytop } ~~> o ->
    { xtop, xs, y::ys, ytop } ~~> o

| BH_compare_head_eq : forall xtop ytop x xs y ys o,
    length xs = length ys ->
    { x, y } ~~~> EQ ->
    { xtop, xs, ys, ytop } ~~> o ->
    { xtop, x::xs, y::ys, ytop } ~~> o

| BH_compare_head_lt : forall xtop ytop x xs y ys o,
    length xs = length ys ->
    xs <> [] ->
    { x, y } ~~~> LT ->
    check_lt_graph xs ytop o ->
    { xtop, x::xs, y::ys, ytop } ~~> o

(*
| BH_compare_length_lt : forall x xs y ys,
    y <> BH [] ->
    (length xs < length ys)%nat ->
    { x::xs, y::ys } ~~> LT

| BH_compare_length_gt : forall x xs y ys,
    x <> BH [] ->
    (length xs > length ys)%nat ->
    { x::xs, y::ys } ~~> GT

| BH_compare_head_gt : forall x xs y ys o,
    length xs = length ys ->
    xs <> [] ->
    { x, y } ~~~> GT ->
    check_gt_graph xs (BH (y::ys)) o ->
    { x::xs, y::ys } ~~> o
*)

where "{ a , x , y , b } ~~> z" := (BH_compare_seq_graph a x y b z)

with check_lt_graph : list BHForm -> BHForm -> ordering -> Prop :=

| check_lt0 : forall ytop,
     check_lt_graph [] ytop LT

| check_lt1 : forall x xs ytop o,
     { x, ytop } ~~~> LT ->
     check_lt_graph xs ytop o ->
     check_lt_graph (x::xs) ytop o

| check_lt2 : forall x xs ytop,
     { x, ytop } ~~~> GT ->
     check_lt_graph (x::xs) ytop GT

(*
with check_lt_graph : BHForm -> list BHForm -> ordering -> Prop :=
| whatever_lt: forall x ys o, check_lt_graph x ys o

with check_gt_graph : list BHForm -> BHForm -> ordering -> Prop :=
| whatever_gt: forall xs y o, check_gt_graph xs y o
*)
.

Scheme compare_graph_ind := Induction for BH_compare_graph Sort Prop
 with compare_seq_graph_ind := Induction for BH_compare_seq_graph Sort Prop
 with check_lt_ind := Induction for check_lt_graph Sort Prop.
(*

 with check_gt_ind := Induction for check_gt_graph Sort Prop.
*)

Lemma compare_graph_correct :
  (forall (x:BHForm) (y:BHForm) (o:ordering), { x, y } ~~~> o -> ordering_correct o (BH_denote x) (BH_denote y)).
Proof.
  apply compare_graph_ind with
    (P0 := fun xtop xs ys ytop o H => 
      match xs, ys with
      | [], [] => o = EQ
      | [], (_::_) => o = LT
      | (_::_), [] => o = GT
      | (x::xtail), (y::ytail) =>
          forall f,
            normal_function f ->
            BH_denote xtop ≈ BH_stack f (BH_denote x) (map BH_denote xtail) ->
            BH_denote ytop ≈ BH_stack f (BH_denote y) (map BH_denote ytail) ->
            ordering_correct o
              (BH_stack f (BH_denote x) (map BH_denote xtail))
              (BH_stack f (BH_denote y) (map BH_denote ytail))
      end)
    (P1 := fun xs ytop o H =>
             match o with
             | LT => forall x, In x xs -> BH_denote x < BH_denote ytop
             | EQ => False
             | GT => exists x, In x xs /\ BH_denote x > BH_denote ytop
             end); auto.

(*

    (P2 := fun ys x o H => True); auto.
*)

  - intros. destruct xs; destruct ys; simpl in *; subst; simpl; auto with ord.
    apply BH_stack_nonzero; simpl; auto with ord.
    apply BH_stack_nonzero; simpl; auto with ord.
  - intros. destruct o; simpl in *; auto with ord.
    apply normal_increasing; auto with ord.
    destruct H. split; auto with ord.
    apply normal_increasing; auto with ord.
  - simpl; intros. subst x.
    destruct xs; [ congruence |].
    destruct ys; auto.
    intros.
    simpl BH_denote.
    simpl map.
    rewrite BH_stack_leading_zero; auto with ord.
    apply H; auto with ord.
    rewrite H1.
    simpl BH_denote.
    simpl map.
    rewrite BH_stack_leading_zero; auto with ord.

  - simpl; intros. subst y.
    destruct ys; [ congruence |].
    destruct xs; auto.
    intros.
    simpl BH_denote.
    simpl map.
    rewrite BH_stack_leading_zero; auto with ord.
    apply H; auto with ord.
    rewrite H2.
    simpl BH_denote.
    simpl map.
    rewrite BH_stack_leading_zero; auto with ord.

  - simpl; intros.
    destruct xs.
    + destruct ys; subst; simpl.
      destruct H; split; auto with ord.
      simpl in *. congruence.
    + destruct ys; [simpl in *; congruence |].
      simpl in *.
      repeat rewrite map_length in *.
      rewrite e.
      assert ( (BH_stack (bhtower (S (length ys)) f (BH_denote x)) 
                  (BH_denote b1) (map BH_denote xs)) ≈
                 (BH_stack (bhtower (S (length ys)) f (BH_denote y)) 
                    (BH_denote b1) (map BH_denote xs))).
      { destruct H.
        split; apply BH_stack_monotone; auto with ord.
        { clear; induction xs; simpl; constructor; auto with ord. }
        { clear; induction xs; simpl; constructor; auto with ord. } }        
      rewrite H4.
      apply H0; auto with ord.
      rewrite H2. rewrite e. auto with ord.

  - intros. simpl in *.
    destruct o; simpl.
    + admit. (* maybe? non-trivial... *)
    + contradiction.
    + destruct H0 as [xbig [Hin Hbig]].
      apply ord_lt_le_trans with (BH_denote xbig).
      rewrite <- H3; auto.
      clear -Hin H1.
      revert x f H1.
      induction xs; simpl; intros.
      { elim Hin. }
      simpl in Hin. destruct Hin; auto with ord.
      subst a.
      case_eq (length xs); intros.
      * destruct xs; try (simpl in *; congruence).
        simpl. apply normal_inflationary; auto with ord.
      * transitivity (BH_stack
                      (bhtower (S (length (map BH_denote xs))) f (BH_denote x))
                      (BH_denote xbig) (stackZeros n [0])).
        rewrite BH_stack_zeros.
        apply (normal_inflationary (fun q => bhtower (S n)
                                              (bhtower (S (length (map BH_denote xs))) f (BH_denote x))
                                              q 0)); auto with ord.
        apply BH_stack_monotone; auto with ord.
        admit. (* very plausible *) 

  - simpl; intuition.

  - simpl; intros.
    destruct o.
    + simpl; intuition; subst; auto.
    + assumption.
    + destruct H0 as [q [??]].
      exists q; simpl; intuition.

  - simpl; intros.
    exists x. simpl; intuition.

Qed.


Require Import Program.Wf.

Print Acc.





Ltac go := unfold BH_listSize; simpl; intros; lia.

Lemma asdf1 : 
  forall a b xs y ys,
    (BH_termSize a + BH_termSize b <= 1 + BH_listSize xs + BH_listSize ys)%nat ->
    (BH_termSize a + BH_termSize b <= 1 + BH_listSize xs + BH_listSize (y::ys))%nat.
Proof.
  unfold BH_listSize; simpl; intros; lia.
Qed.

Lemma asdf2 : 
  forall a b x xs ys,
    (BH_termSize a + BH_termSize b <= 1 + BH_listSize xs + BH_listSize ys)%nat ->
    (BH_termSize a + BH_termSize b <= 1 + BH_listSize (x::xs) + BH_listSize ys)%nat.
Proof.
  unfold BH_listSize; simpl; intros; lia.
Qed.

Lemma asdf3 :
  forall a b x xs y ys,
    (BH_termSize a + BH_termSize b <= 1 + BH_listSize xs + BH_listSize ys)%nat ->
    (BH_termSize a + BH_termSize b <= 1 + BH_listSize (x::xs) + BH_listSize (y::ys))%nat.
Proof.
  unfold BH_listSize; simpl; intros; lia.
Qed.


Fixpoint BH_compare_seq
  (xs:list BHForm) :
  forall (ys:list BHForm),
  (forall a b (H:(BH_termSize a + BH_termSize b <= 1 + BH_listSize xs + BH_listSize ys)%nat), ordering) -> ordering :=
  
    match xs as xs' return
          forall ys, 
            (forall a b (H:(BH_termSize a + BH_termSize b <= 1 + BH_listSize xs' + BH_listSize ys)%nat), ordering) -> ordering with
    | [] =>
        fun ys => match ys with
                  | [] => fun _ => EQ
                  | (_::_) => fun _ => LT
                  end
    | x::xtail =>
        fix inner (ys:list BHForm) : 
        (forall a b (H:(BH_termSize a + BH_termSize b <= 1 + BH_listSize (x::xtail) + BH_listSize ys)%nat), ordering) -> ordering :=

          match ys as ys' return 
                (forall a b (H:(BH_termSize a + BH_termSize b <= 1 + BH_listSize (x::xtail) + BH_listSize ys')%nat), ordering) -> ordering with
          | []  => fun _ => GT
          | (y::ytail) =>
              fun rec =>
              if isNil xtail then
                if isNil ytail then rec x y ltac:(go) else
                   if bh_isZero y then (inner ytail (fun a b H => rec a b (asdf1 a b (x::xtail) y ytail H)))
                  else LT
              else
                if bh_isZero x then BH_compare_seq xtail (y::ytail) (fun a b H => rec a b (asdf2 a b x xtail (y::ytail) H)) else
                  if isNil ytail then GT else
                    if bh_isZero y then (inner ytail (fun a b H => rec a b (asdf1 a b (x::xtail) y ytail H))) else
                      (* x is nonzero, y is nonzero, xs is nonnil, ys is nonnil *)
                      match nat_compare (length xtail) (length ytail) with
                      | LT => LT
                      | EQ => match rec x y ltac:(go) with
                              | LT => LT
                              | EQ => BH_compare_seq xtail ytail (fun a b H => rec a b (asdf3 a b x xtail y ytail H))
                              | GT => GT
                              end
                      | GT => GT
                      end
          end
    end.


Lemma asdf0 : forall a b xs ys,
 (BH_termSize a + BH_termSize b <= 1 + BH_listSize xs + BH_listSize ys)%nat ->
 (BH_termSize a + BH_termSize b < BH_termSize (BH xs) + BH_termSize (BH ys))%nat.
Proof.
  unfold BH_listSize.
  simpl; intros. 
  lia.
Qed.

Definition BH_compare_def
  (x:BHForm) (y:BHForm) :
  (forall a b (H:(BH_termSize a + BH_termSize b < BH_termSize x + BH_termSize y)%nat), ordering) -> ordering :=

  match x as x', y as y' return 
        (forall a b (H:(BH_termSize a + BH_termSize b < BH_termSize x' + BH_termSize y')%nat), ordering) -> ordering with
  | BH xs, BH ys =>
      fun rec => BH_compare_seq xs ys (fun a b H => rec a b (asdf0 a b xs ys H))
  end.


Fixpoint BH_compare_WF (x:BHForm) (y:BHForm)
  (WF:Acc lt (BH_termSize x + BH_termSize y)%nat) {struct WF} : ordering :=

  match WF with
  | Acc_intro _ WF' => BH_compare_def x y (fun x' y' H => BH_compare_WF x' y' (WF' _ H))
  end.

Definition BH_compare (x:BHForm) (y:BHForm) : ordering :=
  BH_compare_WF x y (Wf_nat _).



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
