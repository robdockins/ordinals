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
From Ordinal Require Import BachmannAssoc.
From Ordinal Require Import BachmannPower.
From Ordinal Require Import BachmannCfe.
From Ordinal Require Import BachmannNormal.
From Ordinal Require Import BachmannAgree.
From Ordinal Require Import BachmannFacts.
From Ordinal Require Import BachmannEnumeration.
From Ordinal Require Import Notation.SchutteMatrix.
From Ordinal Require Import Notation.CantorDecomposition.
From Ordinal Require Import Notation.Interpolants.
From Ordinal Require Import Notation.CantorProduct.
From Ordinal Require Import NaturalProduct.
From Ordinal Require Import Reflection.
From Ordinal Require Import NaturalArith.

From Ordinal Require Import Notation.BachmannNotation.
From Ordinal Require Import Notation.BachmannCantor.
From Ordinal Require Import Notation.BachmannBound.
From Ordinal Require Import Notation.BachmannNormalize.
From Ordinal Require Import Notation.BachmannInterpolants.

Open Scope ord_scope.
Open Scope bool_scope.

(** Part of the notation system up to the Bachmann–Howard ordinal; see @BachmannNotation.v@ for an overview. *)

(** * The natural product *)

Definition BS_nmul := cantor_nmul _ _ _ BS_has_cantor_decomposition.

Theorem BS_nmul_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) nmulOrd BS_nmul.
Proof. apply cantor_nmul_reflects. apply BS_has_all_interpolants. Qed.

(** * The order type of the normal forms

The normal forms are cofinal in BHO₁: their limit is a fixpoint of 1+x
and of the components φ_{tower n} of ε_{Ω+1}, since each component is
bounded by φ of a notation index tₙ (Ω+1, Ω^(Ω+1), …) and so takes
notations to notations. *)

Fixpoint BI_tower (n:nat) : BIdx :=
  match n with
  | O => BIC BI_one BS_one (BIC BIZ BS_one BIZ)
  | S n' => BIC (BI_tower n') BS_one BIZ
  end.

Lemma BS_one_proper : BS_proper BS_one.
Proof. apply (proj1 nf_proper), BS_one_nf. Qed.

Lemma BS_one_pos : 0 < BS_denote BS_one.
Proof. rewrite BS_one_denote. apply succ_lt. Qed.

Lemma BI_tower_proper n : BI_proper (BI_tower n).
Proof.
  induction n as [|n IH]; simpl.
  - repeat split; auto using BS_one_proper, BS_one_pos; constructor.
  - repeat split; auto using BS_one_proper, BS_one_pos.
Qed.

Lemma bequiv_mul_one P : bequiv (bmul P (embed (BS_denote BS_one))) P.
Proof.
  eapply bequiv_trans; [ apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_embed, BS_one_denote ] | ].
  split; apply bsub_bmul_one.
Qed.

Lemma bsub_succ_add x : bsub (bsucc x) (badd x (embed 1)).
Proof.
  apply bsub_intro; [ | intros [] ].
  intros [].
  destruct (badd_small_r x (embed 1) tt) as [t Ht].
  exists t. rewrite Ht. apply bsub_le_badd.
Qed.

Lemma bsub_tower n : bsub (btower n) (BI_denote (BI_tower n)).
Proof.
  induction n as [|n IH].
  - change (bsub (bsucc bOmega)
      (badd (bmul (bexpΩ (BI_denote BI_one)) (embed (BS_denote BS_one)))
            (badd (bmul (bexpΩ bzero) (embed (BS_denote BS_one))) bzero))).
    assert (H1 : bequiv (BI_denote BI_one) (embed 1)).
    { eapply bequiv_trans; [ apply (exp_equiv BI_one BS_one eq_refl) | apply bequiv_embed, BS_one_denote ]. }
    apply bsub_trans with (badd (bexpΩ (embed 1)) (embed 1)).
    + eapply bsub_trans; [ apply bsub_succ_add | ].
      apply bsub_badd_l. apply Ω_le_exp. apply succ_lt.
    + apply bsub_trans with (badd (bexpΩ (embed 1)) (badd (bmul (bexpΩ bzero) (embed (BS_denote BS_one))) bzero)).
      * apply bsub_badd_r.
        eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
        eapply bsub_trans; [ apply (proj2 (bequiv_embed _ _ BS_one_denote)) | ].
        apply (proj2 (bequiv_one_mul _)).
      * apply bsub_badd_l. eapply bsub_trans; [ | apply (proj2 (bequiv_mul_one _)) ].
        apply bsub_bexpΩ. apply (proj2 H1).
  - simpl. eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
    eapply bsub_trans; [ | apply (proj2 (bequiv_mul_one _)) ].
    apply bsub_bexpΩ; auto.
Qed.

Definition NFOrd : Ord := ord {x:BSmall | BS_nf x} (fun x => BS_denote (proj1_sig x)).

Lemma NF_below x : BS_nf x -> BS_denote x < NFOrd.
Proof. intro Hx. apply (index_lt NFOrd (exist _ x Hx)). Qed.

(** A normal function taking notations below notations fixes the limit
    of the normal forms. *)
Lemma NF_closed G : normal_function G ->
  (forall x, BS_nf x -> exists y, BS_nf y /\ G (BS_denote x) ≤ BS_denote y) ->
  G NFOrd ≤ NFOrd.
Proof.
  intros HG HGn.
  set (s := fun x:{x:BSmall | BS_nf x} => succOrd (BS_denote (proj1_sig x))).
  assert (Hdir : directed _ s).
  { intros [x1 H1] [x2 H2].
    destruct (BS_add_reflects (BS_denote x1) x1 (conj (ord_eq_refl _) H1)
                              (BS_denote x2) x2 (conj (ord_eq_refl _) H2)) as [E N].
    exists (exist _ (BS_add x1 x2) N). unfold s; simpl. rewrite <- E.
    split; apply succ_monotone; [ apply addOrd_le1 | apply addOrd_le2 ]. }
  assert (Hc : forall a, complete (s a)) by (intro; apply succ_complete, BS_complete).
  assert (Hle : NFOrd ≤ supOrd s).
  { rewrite ord_le_unfold. intro a. eapply ord_lt_le_trans; [ apply succ_lt | apply (sup_le _ s a) ]. }
  transitivity (G (supOrd s)); [ apply normal_monotone; auto | ].
  eapply ord_le_trans; [ apply (normal_continuous G HG _ s (exist _ BZ I) Hdir Hc) | ].
  apply sup_least. intros [x Hx]. unfold s; simpl.
  destruct (BS_succ_reflects (BS_denote x) x (conj (ord_eq_refl _) Hx)) as [E N].
  destruct (HGn _ N) as [y [Hy Hyl]].
  transitivity (BS_denote y); [ | apply ord_lt_le, NF_below; auto ].
  rewrite <- Hyl. apply normal_monotone; auto. apply E.
Qed.

(** The normal forms have order type BHO₁. *)
Theorem BS_order_type : NFOrd ≈ BHO1.
Proof.
  split.
  - rewrite ord_le_unfold. intros [x Hx]. apply BS_bounded; auto.
  - unfold BHO1.
    change (cfe (addOrd 1) (nat + False) (bphi_fam (addOrd 1) btower (False_rect (Ord -> BOrd))) 0 ≤ NFOrd).
    destruct bεΩ1_good as [Hfam Hg].
    assert (HF := bphi_fam_normal' _ onePlus_normal _ _ _ _ Hg).
    apply (cfe_least (addOrd 1) onePlus_normal _ _ HF).
    + transitivity (BS_denote BS_one); [ apply (BS_denote_onePlus BZ) | ].
      apply ord_lt_le, NF_below, BS_one_nf.
    + apply limit_least. intros [].
    + assert (H1 : 1 + NFOrd ≤ NFOrd).
      { apply NF_closed; [ apply onePlus_normal | ].
        intros x Hx. destruct (BS_onePlus_reflects (BS_denote x) x (conj (ord_eq_refl _) Hx)) as [E N].
        exists (BS_onePlus x). split; auto. apply E. }
      intros [n|[]]. split; auto.
      apply NF_closed; [ apply (HF (inl n)) | ].
      intros x Hx.
      assert (Hp : BS_proper (BN (BI_tower n) x)) by (split; [ apply BI_tower_proper | apply (proj1 nf_proper); auto ]).
      exists (normS (BN (BI_tower n) x)). split; [ apply normS_nf; auto | ].
      rewrite (normS_equal _ Hp). simpl.
      apply (proj2 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (BI_bfam _))).
      apply bsub_tower.
Qed.

(** * Base change: BHO₁ is the Bachmann–Howard ordinal

φ^{1+x}_T ≤ φ^{ω^x}_T gives one direction.  For the other, φ^{ω^x}_T ≤
φ^{1+x}_{Ω+T}, and Ω + tower n lies z-reachably below tower (n+2),
so BHO₁ is closed under ω^x and every φ^{ω^x}_{tower n}. *)

Theorem BHO1_BachmannHoward : BHO1 ≈ BachmannHoward.
Proof.
  split.
  - apply bphi_base_mono; auto using bcd_bεΩ1, zero_complete.
  - unfold BachmannHoward.
    assert (Hg := bcd_good _ powOmega_normal _ bcd_bεΩ1).
    change (cfe powOmega (nat + False) (bphi_fam powOmega btower (False_rect (Ord -> BOrd))) 0 ≤ BHO1).
    assert (Hcomp : forall n, bphi powOmega (btower n) BHO1 ≤ BHO1).
    { intro n. rewrite (bphi_powOmega_shift _ (bcd_btower n) _ BHO1_complete).
      destruct bεΩ1_good as [Hfam1 Hg1].
      assert (Hgt : bgood (addOrd 1) (btower (S (S n)))) by (apply (bgood_small _ bεΩ1 (S (S n))); auto).
      assert (Hft : bfam (btower (S (S n)))) by (apply (bfam_small bεΩ1 Hfam1 (S (S n)))).
      apply (zlt_nest _ onePlus_normal _ _ (btower (S (S n))) (zlt_Ω_tower n _ BHO1_inf) Hgt Hft BHO1_complete).
      apply bfix_of_fix; auto using onePlus_normal, BHO1_complete.
      apply (bphi_fix_small' _ onePlus_normal bεΩ1 (S (S n)) 0 Hg1 zero_complete). }
    assert (Hpow : powOmega BHO1 ≤ BHO1).
    { transitivity (bphi powOmega (btower 0) BHO1); [ | apply Hcomp ].
      transitivity (bphi powOmega bzero BHO1); [ apply (bphi_bzero _ powOmega_normal) | ].
      apply (proj2 (bphi_mono_index _ (normal_monotone _ powOmega_normal) _ (bfam_btower 0))).
      apply bsub_bzero_l. }
    apply (cfe_least powOmega powOmega_normal _ _ (bphi_fam_normal' _ powOmega_normal _ _ _ _ Hg)).
    + transitivity (powOmega BHO1); auto. apply normal_monotone; [ apply powOmega_normal | apply zero_least ].
    + apply limit_least. intros [].
    + intros [n|[]]. split; [ apply Hcomp | exact Hpow ].
Qed.

Corollary BS_order_type_BH : NFOrd ≈ BachmannHoward.
Proof. rewrite BS_order_type. apply BHO1_BachmannHoward. Qed.
