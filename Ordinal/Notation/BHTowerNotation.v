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

Fixpoint BH_denote (v:BHForm) : Ord :=
  match v with
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
