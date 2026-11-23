From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import SchutteColumnFacts.
From Ordinal Require Import BachmannDefs.
From Ordinal Require Import BachmannNormal.
From Ordinal Require Import BachmannFacts.
From Ordinal Require Import Notation.SchutteMatrix.
From Ordinal Require Import Notation.CantorDecomposition.
From Ordinal Require Import Notation.Interpolants.
From Ordinal Require Import Notation.CantorProduct.
From Ordinal Require Import NaturalProduct.
From Ordinal Require Import Reflection.
From Ordinal Require Import NaturalArith.

From Ordinal Require Import Notation.BachmannNotation.

Open Scope ord_scope.
Open Scope bool_scope.

(** Part of the notation system up to the Bachmann–Howard ordinal; see @BachmannNotation.v@ for an overview. *)

(** * The upper bound: every normal form lies below the Bachmann–Howard ordinal

At the base 1+x the Bachmann–Howard ordinal is BHO₁ = φ_{ε_{Ω+1}}(0).
Every normal index is reachable below some level Ω+1, Ω^(Ω+1), … of the
tower whose limit is ε_{Ω+1}, relative to any infinite z above its
coefficients; this is part (B) of @nest@ applied along leading
exponents.  Since BHO₁ is a common fixpoint of the components of
ε_{Ω+1}, it is a fixpoint of every φ_T, and the bound follows by
induction on notations. *)

Definition BHO1 : Ord := bphi (addOrd 1) bεΩ1 0.

Lemma bεΩ1_inh : inhabited (bsmall bεΩ1 + bbig bεΩ1).
Proof. exact (inhabits (inl 0%nat)). Qed.

Lemma bεΩ1_good : bfam bεΩ1 /\ bgood (addOrd 1) bεΩ1.
Proof. apply (bcanon_good (addOrd 1) onePlus_normal); [ apply bcanon_bεΩ1 | apply bdec_bεΩ1 ]. Qed.

Lemma BHO1_complete : complete BHO1.
Proof. apply bphi_complete; [ apply onePlus_normal | apply bεΩ1_good | apply zero_complete ]. Qed.

Lemma BHO1_inf : oinf BHO1.
Proof.
  apply (bphi_value_inf (addOrd 1) onePlus_normal); auto using zero_complete, bεΩ1_inh.
  - intro; apply addOrd_le2.
  - intros; reflexivity.
  - apply bεΩ1_good.
Qed.

(** Every normal index is z-reachably below some level of the tower. *)
Lemma idx_height z : oinf z -> forall T, BI_nf T -> Klt z T -> exists n, zlt z (BI_denote T) (btower n).
Proof.
  intros Hz T. induction T as [|e IHe c r IHr]; intros HT HK.
  - exists 0%nat. apply zlt_bslt. change (bslt bzero (bsucc bOmega)).
    apply (bslt_small bzero (bsucc bOmega) tt), bsub_bzero_l.
  - destruct (IHe (proj1 HT) (proj1 HK)) as [m Hm].
    exists (S m).
    exact (proj2 (nest z Hz (S (BI_size (BIC e c r))) (BIC e c r) ltac:(lia) HT HK) (btower m) Hm).
Qed.

Lemma zlt_tower_top z x n : zlt z x (btower n) -> zlt z x bεΩ1.
Proof.
  intros [D [H1 H2]]. exists D. split; auto.
  apply (LZ_small z D bεΩ1 (n : bsmall bεΩ1)). exact H2.
Qed.

(** BHO₁ is a fixpoint of φ_T for every normal index whose coefficients lie below it. *)
Lemma BHO1_fix T : BI_nf T -> Klt BHO1 T -> bphi (addOrd 1) (BI_denote T) BHO1 ≤ BHO1.
Proof.
  intros HT HK.
  destruct (idx_height BHO1 BHO1_inf T HT HK) as [n Hn].
  apply (zlt_value (addOrd 1) onePlus_normal (BI_denote T) bεΩ1 0); auto using zero_complete, bεΩ1_inh.
  - apply (zlt_tower_top _ _ n Hn).
  - apply bεΩ1_good.
  - apply bεΩ1_good.
Qed.

Theorem BNotation_bounded :
  (forall x, BS_nf x -> BS_denote x < BHO1) /\ (forall T, BI_nf T -> Klt BHO1 T).
Proof.
  apply BNotation_mut.
  - intros _. apply (bphi_nonzero (addOrd 1) onePlus_normal).
  - intros T IHT y IHy [HT [Hy _]].
    eapply ord_lt_le_trans; [ | apply (BHO1_fix T HT (IHT HT)) ].
    apply normal_increasing; auto using BI_normal, BHO1_complete.
  - intros _. exact I.
  - intros e IHe c IHc r IHr [He [Hc [_ [Hr _]]]]. simpl. auto.
Qed.

(** Every normal form denotes an ordinal below the Bachmann–Howard
    ordinal (at the base 1+x). *)
Corollary BS_bounded x : BS_nf x -> BS_denote x < BHO1.
Proof. apply BNotation_bounded. Qed.

(** * Dominance: coefficients lie at or below φ_T(0)

Every coefficient k of a normal index T, at any depth, sits in a
strict context C with C k ⊑ ⟦T⟧ (@bctx@): the hole runs through the
right summand of an addition, the coefficient of Ω^e·_, or an
exponent.  So k ≤ φ_{C k}(0) ≤ φ_T(0).  Equality can occur, e.g.
φ_{Ω^d}(0) = d for d the Large Veblen Ordinal. *)

Lemma idx_term_bcd e c : bcd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))).
Proof. apply (proj1 (idx_ok_term _ _ (BI_ok e) (BS_complete c))). Qed.

(** All coefficients, at any depth, are positive. *)
Fixpoint BI_pos (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => BI_pos e /\ 0 < BS_denote c /\ BI_pos r
  end.

Lemma BI_nf_pos T : BI_nf T -> BI_pos T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; auto.
  intros [He [_ [Hc [Hr _]]]]. auto.
Qed.

Lemma Kge_ctx : forall T, BI_pos T -> forall z, Kge z T ->
  exists C ζ, bctx C /\ complete ζ /\ z ≤ ζ /\ bsub (C ζ) (BI_denote T).
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [He [Hc0 Hr]] z [Hz|[Hz|Hz]].
  - destruct (IHe He z Hz) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
    exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
    eapply bsub_trans; [ apply bsub_bexpΩ, Hsub | ].
    eapply bsub_trans; [ apply bsub_P_Pz, Hc0 | apply bsub_le_badd ].
  - exists (fun ξ => bmul (bexpΩ (BI_denote e)) (embed ξ)), (BS_denote c).
    split; [ | split; [ apply BS_complete | split; [ auto | apply bsub_le_badd ] ] ].
    apply bctx_mul; [ apply bcd_bexpΩ, BI_ok | apply bpos_bexpΩ | apply bctx_embed ].
  - destruct (IHr Hr z Hz) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
    exists (fun ξ => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (C ξ)), ζ.
    split; [ apply bctx_add; [ apply idx_term_bcd | auto ] | split; [ auto | split; [ auto | ] ] ].
    apply bsub_badd_r; auto.
Qed.

Theorem dominance T y z : BI_pos T -> Kge z T -> z ≤ BS_denote (BN T y).
Proof.
  intros HT Hz.
  destruct (Kge_ctx T HT z Hz) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
  transitivity ζ; auto.
  transitivity (bphi (addOrd 1) (C ζ) 0); [ apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ) | ].
  transitivity (bphi (addOrd 1) (BI_denote T) 0).
  - apply (proj2 (bphi_mono_index (addOrd 1) (normal_monotone _ onePlus_normal) _ (BI_bfam T))); auto.
  - simpl. apply normal_monotone; auto using BI_normal, zero_least.
Qed.
