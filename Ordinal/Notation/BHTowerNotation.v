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
      bhtower_complete
      bhtower_monotone
      normal_complete
      normal_monotone
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

Definition BH0    := BH nil.
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
  transitivity (apex 1 (addOrd 1)); [ | apply apex1 ].
  simpl BH_denote.
  rewrite bhtower_zero.
  rewrite apex_alternate; auto with arith.
  split; apply bhtower_monotone; auto with ord.
  apply BH2_correct.
  apply BH2_correct.
Qed.

Lemma BHΓ0_correct : BH_denote BHΓ0 ≈ Γ 0.
Abort. (* true, I think, but kind of annoying *)


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
  transitivity (apex 2 (addOrd 1)); [ | apply apex2 ].
  rewrite apex_alternate; auto with arith.
  simpl BH_denote.
  rewrite bhtower_zero.
  rewrite bhtower_zero.
  split; apply bhtower_monotone; auto with ord.
  apply BH2_correct.
  apply BH2_correct.
Qed.
