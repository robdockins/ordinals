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

Open Scope ord_scope.
Open Scope bool_scope.

(** Part of the notation system up to the Bachmann–Howard ordinal; see @BachmannNotation.v@ for an overview. *)

(** * Cantor decomposition

With base 1+x, φ_∅(y) = 1 + y and φ_{Ω^0·a}(y) = ω^a + y, while a
value whose index has a nonzero leading exponent is an ε-number:
ω^v = v.  So a normal form decomposes as a sum of powers of ω whose
exponents are again normal forms, and the generic Cantor arithmetic
applies. *)

(** ** Generic facts about Cantor sums *)

Section cantor_sums.
  Variable A : Type.
  Variable f : A -> Ord.
  Hypothesis Hf : forall x, complete (f x).

  Lemma cantor_lt_succ : forall xs a, cantor_ordered f (a :: xs) ->
    cantor_denote f (a :: xs) < expOrd ω (succOrd (f a)).
  Proof.
    induction xs as [|b xs IH]; intros a Hord; simpl in *.
    - rewrite addOrd_zero_r. apply expOrd_increasing; [ apply omega_gt1 | apply succ_lt ].
    - destruct Hord as [Hab Hord].
      apply expOmega_additively_closed; [ apply succ_complete; auto | | ].
      + apply expOrd_increasing; [ apply omega_gt1 | apply succ_lt ].
      + eapply ord_lt_le_trans; [ apply (IH b Hord) | ].
        apply expOrd_monotone. apply succ_least.
        apply ord_le_lt_trans with (f a); [ exact Hab | apply succ_lt ].
  Qed.

  Lemma cantor_lt_shift : forall xs a, cantor_ordered f xs ->
    match xs with [] => True | b :: _ => f b ≤ a end ->
    cantor_denote f xs < expOrd ω a + cantor_denote f xs.
  Proof.
    induction xs as [|b xs IH]; intros a Hord Hb; simpl in *.
    - rewrite addOrd_zero_r. apply expOrd_nonzero.
    - destruct Hord as [Hhead Hord].
      apply ord_lt_le_trans with (expOrd ω (f b) + (expOrd ω (f b) + cantor_denote f xs)).
      + apply addOrd_increasing. apply IH; auto.
      + apply addOrd_monotone; [ apply expOrd_monotone; auto | reflexivity ].
  Qed.
End cantor_sums.

(** u + (ω^b + r) = ω^b + r whenever u < ω^b. *)
Lemma lead_absorb u b r : complete b -> u < expOrd ω b -> u + (expOrd ω b + r) ≈ expOrd ω b + r.
Proof.
  intros Hb Hu. rewrite addOrd_assoc. split; [ | apply addOrd_monotone; [ apply addOrd_le2 | reflexivity ] ].
  apply addOrd_monotone; [ | reflexivity ].
  apply additively_closed_collapse; auto. apply expOmega_additively_closed; auto.
Qed.

(** ** The values of the three shapes *)

Lemma BS_denote_small a y : BS_denote (BN (BIC BIZ a BIZ) y) ≈ expOrd ω (BS_denote a) + BS_denote y.
Proof.
  transitivity (bphi (addOrd 1) (embed (BS_denote a)) (BS_denote y)).
  - apply (bphi_bequiv (addOrd 1) (normal_monotone _ onePlus_normal) _ _ _
             (exp_equiv (BIC BIZ a BIZ) a eq_refl) (BI_bfam _) (bfam_embed _)).
  - apply bphi_onePlus_embed; auto using BS_complete.
Qed.

(** A value whose index has a nonzero leading exponent is an ε-number:
    the family ξ ↦ Ω^0·ξ = ξ is reachable from Ω^e at the argument v
    itself, so φ_{Ω^0·v}(0) = ω^v lies below v. *)
Lemma BN_eps e c r y : BS_nf (BN (BIC e c r) y) -> e <> BIZ ->
  expOrd ω (BS_denote (BN (BIC e c r) y)) ≤ BS_denote (BN (BIC e c r) y).
Proof.
  intros Hx He.
  set (v := BS_denote (BN (BIC e c r) y)).
  destruct Hx as [HT [_ [_ _]]].
  assert (Hv : oinf v) by (apply BN_inf; auto; discriminate).
  assert (Hc : 0 < BS_denote c) by apply HT.
  assert (Hepos : bpos (BI_denote e)).
  { destruct e as [|e1 c1 r1]; [ tauto | ]. apply lead_pos. apply HT. }
  assert (HZ : bleZ v (bmul (bexpΩ bzero) (embed v)) (BI_denote (BIC e c r))).
  { eapply bleZ_mono_r; [ apply zlt_exp; [ apply zlt_bslt, Hepos | exact Hv ] | ].
    simpl. eapply bsub_trans; [ apply bsub_P_Pz, Hc | apply bsub_le_badd ]. }
  assert (Hfix : bphi (addOrd 1) (bmul (bexpΩ bzero) (embed v)) 0 ≤ v).
  { apply (bleZ_sound (addOrd 1) onePlus_normal v _ _ HZ (BI_denote (BIC e c r)) (bsub_refl _));
      auto using BI_good, BI_bfam.
    - apply (BS_complete (BN (BIC e c r) y)).
    - exact (bfix_value_full (addOrd 1) onePlus_normal (BI_denote (BIC e c r)) (BS_denote y)
               (BI_good _) (BI_inh e c r Hc) (BS_complete y)). }
  eapply ord_le_trans; [ | exact Hfix ].
  transitivity (bphi (addOrd 1) (embed v) 0).
  - transitivity (expOrd ω v + 0); [ apply addOrd_le1 | ].
    apply (bphi_onePlus_embed v 0 (BS_complete (BN (BIC e c r) y)) zero_complete).
  - apply (bphi_bequiv (addOrd 1) (normal_monotone _ onePlus_normal) _ _ _
             (bequiv_sym _ _ (bequiv_one_mul v)) (bfam_embed _)
             (bfam_bmul _ _ (bfam_bexpΩ _ bfam_bzero) (bfam_embed _))).
Qed.

(** ** Decomposition *)

Fixpoint BS_decompose (x:BSmall) : list BSmall :=
  match x with
  | BZ => []
  | BN BIZ y => BZ :: BS_decompose y
  | BN (BIC BIZ a BIZ) y => a :: BS_decompose y
  | _ => [x]
  end.


Theorem decompose_correct : forall x, BS_nf x ->
  each BS_nf (BS_decompose x) /\ cantor_ordered BS_denote (BS_decompose x) /\
  BS_denote x ≈ cantor_denote BS_denote (BS_decompose x).
Proof.
  induction x as [|T y IHy]; intro Hx; [ simpl; split; [ exact I | split; [ exact I | reflexivity ] ] | ].
  assert (Hx' := Hx). destruct Hx' as [HT [Hy [Hlt HK]]].
  destruct (IHy Hy) as [Hall [Hord Heq]].
  destruct T as [|[|e1 c1 r1] c r].
  - (* 1 + y *)
    simpl BS_decompose. split; [ split; [ exact I | exact Hall ] | split ].
    + split; auto.
      destruct (BS_decompose y) as [|b bs] eqn:E; auto.
      destruct b as [|Tb yb]; [ simpl; reflexivity | exfalso ].
      simpl in Heq.
      assert (Hb := BS_pos Tb yb).
      assert (Habs : 1 + (expOrd ω (BS_denote (BN Tb yb)) + cantor_denote BS_denote bs)
                     ≈ expOrd ω (BS_denote (BN Tb yb)) + cantor_denote BS_denote bs).
      { apply lead_absorb; [ apply BS_complete | ].
        apply ord_le_lt_trans with (expOrd ω 0); [ apply (proj2 (expOrd_zero ω)) | ].
        apply expOrd_increasing; auto. apply omega_gt1. }
      apply (ord_lt_irreflexive (BS_denote y)).
      eapply ord_lt_le_trans; [ exact Hlt | ].
      rewrite BS_denote_onePlus. rewrite Heq at 1. rewrite Habs. apply Heq.
    + simpl cantor_denote. rewrite BS_denote_onePlus. rewrite expOrd_zero. rewrite <- Heq. reflexivity.
  - destruct r as [|e2 c2 r2].
    + (* ω^c + y *)
      simpl BS_decompose.
      assert (Hc : BS_nf c) by apply HT.
      split; [ split; [ exact Hc | exact Hall ] | split ].
      * split; auto.
        destruct (BS_decompose y) as [|b bs] eqn:E; auto.
        destruct Hall as [Hb _].
        destruct (BS_decide_order c b Hc Hb) as [Hcb|Hbc]; auto.
        exfalso. simpl in Heq.
        assert (Habs : expOrd ω (BS_denote c) + (expOrd ω (BS_denote b) + cantor_denote BS_denote bs)
                       ≈ expOrd ω (BS_denote b) + cantor_denote BS_denote bs).
        { apply lead_absorb; [ apply BS_complete | ].
          apply expOrd_increasing; auto. apply omega_gt1. }
        apply (ord_lt_irreflexive (BS_denote y)).
        eapply ord_lt_le_trans; [ exact Hlt | ].
        rewrite BS_denote_small. rewrite Heq at 1. rewrite Habs. apply Heq.
      * simpl cantor_denote. rewrite BS_denote_small. rewrite <- Heq. reflexivity.
    + exfalso. destruct HT as [_ [_ [_ [_ Hl]]]]. inversion Hl.
  - (* an ε-number *)
    set (X := BN (BIC (BIC e1 c1 r1) c r) y).
    change (each BS_nf [X] /\ cantor_ordered BS_denote [X] /\
            BS_denote X ≈ expOrd ω (BS_denote X) + 0).
    split; [ split; [ exact Hx | exact I ] | split; [ simpl; auto | ] ].
    split.
    + transitivity (expOrd ω (BS_denote X)); [ | apply addOrd_le1 ].
      apply (normal_inflationary powOmega powOmega_normal), BS_complete.
    + apply ord_le_trans with (expOrd ω (BS_denote X)); [ apply addOrd_zero_r | ].
      apply BN_eps; auto. discriminate.
Qed.

(** A normal form that is not an ε-number lies below its ω-power. *)
Lemma not_eps_lt x :
  BS_nf x -> match x with BZ => False | BN (BIC (BIC _ _ _) _ _) _ => False | _ => True end ->
  BS_denote x < expOrd ω (BS_denote x).
Proof.
  intros Hx Hs.
  destruct (decompose_correct x Hx) as [_ [Hord Heq]].
  destruct x as [|T y]; [ contradiction | ].
  assert (Hx' := Hx). destruct Hx' as [HT [_ [_ HK]]].
  assert (Hhead : exists h rest, BS_decompose (BN T y) = h :: rest /\
                                 BS_denote h < BS_denote (BN T y)).
  { destruct T as [|[|e1 c1 r1] c r]; [ | | contradiction ].
    - exists BZ, (BS_decompose y). split; auto. apply BS_pos.
    - destruct r as [|e2 c2 r2]; [ | destruct HT as [_ [_ [_ [_ Hl]]]]; inversion Hl ].
      exists c, (BS_decompose y). split; auto. apply HK. }
  destruct Hhead as [h [rest [E Hh]]]. rewrite E in Hord, Heq.
  eapply ord_le_lt_trans; [ apply Heq | ].
  eapply ord_lt_le_trans; [ apply (cantor_lt_succ BSmall BS_denote BS_complete rest h Hord) | ].
  apply expOrd_monotone, succ_least; auto.
Qed.

(** ** Recomposition *)

Fixpoint BS_recompose (xs:list BSmall) : BSmall :=
  match xs with
  | [] => BZ
  | e :: xs' =>
      match e with
      | BZ => BN BIZ (BS_recompose xs')
      | BN (BIC (BIC _ _ _) _ _) _ =>
          match xs' with
          | [] => e
          | _ :: _ => BN (BIC BIZ e BIZ) (BS_recompose xs')
          end
      | _ => BN (BIC BIZ e BIZ) (BS_recompose xs')
      end
  end.

Lemma small_nf e r : BS_nf e -> 0 < BS_denote e -> BS_nf r ->
  BS_denote r < expOrd ω (BS_denote e) + BS_denote r ->
  BS_denote e < expOrd ω (BS_denote e) + BS_denote r ->
  BS_nf (BN (BIC BIZ e BIZ) r).
Proof.
  intros He He0 Hr H1 H2.
  split; [ simpl; auto | split; [ auto | split ] ].
  - eapply ord_lt_le_trans; [ exact H1 | apply BS_denote_small ].
  - simpl. split; auto. split; auto.
    eapply ord_lt_le_trans; [ exact H2 | apply BS_denote_small ].
Qed.

Theorem recompose_correct : forall xs, each BS_nf xs -> cantor_ordered BS_denote xs ->
  BS_nf (BS_recompose xs) /\ cantor_denote BS_denote xs ≈ BS_denote (BS_recompose xs).
Proof.
  induction xs as [|e xs IH]; [ simpl; split; [ exact I | reflexivity ] | ].
  intros [He Hall] [Hhead Hord].
  destruct (IH Hall Hord) as [Hr Heq].
  assert (Hshift := cantor_lt_shift BSmall BS_denote xs (BS_denote e) Hord Hhead).
  assert (Hshift' : BS_denote (BS_recompose xs) < expOrd ω (BS_denote e) + BS_denote (BS_recompose xs)).
  { rewrite <- Heq. exact Hshift. }
  (* the general case Ω^0·e *)
  assert (Hgen : 0 < BS_denote e -> BS_denote e < expOrd ω (BS_denote e) + BS_denote (BS_recompose xs) ->
                 BS_nf (BN (BIC BIZ e BIZ) (BS_recompose xs)) /\
                 cantor_denote BS_denote (e :: xs) ≈ BS_denote (BN (BIC BIZ e BIZ) (BS_recompose xs))).
  { intros He0 Hlt. split; [ apply small_nf; auto | ].
    simpl cantor_denote. rewrite BS_denote_small. rewrite Heq. reflexivity. }
  (* when the tail is nonempty, e lies below ω^e + rest *)
  assert (Hne : xs <> [] -> BS_denote e < expOrd ω (BS_denote e) + BS_denote (BS_recompose xs)).
  { intro Hxs. destruct xs as [|b bs]; [ tauto | ].
    apply ord_le_lt_trans with (expOrd ω (BS_denote e) + 0).
    - rewrite addOrd_zero_r. apply (normal_inflationary powOmega powOmega_normal), BS_complete.
    - apply addOrd_increasing. rewrite <- Heq. simpl.
      eapply ord_lt_le_trans; [ apply expOrd_nonzero | apply addOrd_le1 ]. }
  destruct e as [|T y].
  - (* 1 + rest *)
    simpl BS_recompose. split.
    + split; [ exact I | split; [ auto | split; [ | exact I ] ] ].
      eapply ord_lt_le_trans; [ exact Hshift' | ].
      rewrite BS_denote_onePlus. rewrite expOrd_zero. reflexivity.
    + simpl cantor_denote. rewrite BS_denote_onePlus. rewrite expOrd_zero. rewrite Heq. reflexivity.
  - destruct xs as [|b bs].
    + destruct T as [|[|e1 c1 r1] c r].
      * apply Hgen; [ apply BS_pos | ].
        apply ord_lt_le_trans with (expOrd ω (BS_denote (BN BIZ y))); [ | apply addOrd_le1 ].
        apply not_eps_lt; auto.
      * apply Hgen; [ apply BS_pos | ].
        apply ord_lt_le_trans with (expOrd ω (BS_denote (BN (BIC BIZ c r) y))); [ | apply addOrd_le1 ].
        apply not_eps_lt; auto.
      * set (X := BN (BIC (BIC e1 c1 r1) c r) y).
        change (BS_nf X /\ expOrd ω (BS_denote X) + 0 ≈ BS_denote X).
        split; auto. split.
        -- apply ord_le_trans with (expOrd ω (BS_denote X)); [ apply addOrd_zero_r | ].
           apply BN_eps; auto. discriminate.
        -- transitivity (expOrd ω (BS_denote X)); [ | apply addOrd_le1 ].
           apply (normal_inflationary powOmega powOmega_normal), BS_complete.
    + destruct T as [|[|e1 c1 r1] c r];
        (apply Hgen; [ apply BS_pos | apply Hne; discriminate ]).
Qed.

(** ** The Cantor decomposition and the derived arithmetic *)

Definition BS_has_cantor_decomposition : has_cantor_decomposition BS_denote BS_nf :=
  {| cantor_decomp_compare := BS_compare
   ; cantor_decompose := BS_decompose
   ; cantor_recompose := BS_recompose
   ; cantor_decomp_complete := BS_complete
   ; cantor_decomp_compare_correct := BS_compare_correct
   ; cantor_decompose_correct := decompose_correct
   ; cantor_recompose_correct := recompose_correct
   |}.

Definition BS_succ := cantor_succ BS_has_cantor_decomposition.
Definition BS_add  := cantor_add BS_has_cantor_decomposition.
Definition BS_mul  := cantor_mul BS_has_cantor_decomposition.
Definition BS_exp  := cantor_exp BS_has_cantor_decomposition.
Definition BS_nadd := cantor_nadd BS_has_cantor_decomposition.

Theorem BS_succ_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD) succOrd BS_succ.
Proof. apply cantor_succ_reflects. Qed.

Theorem BS_add_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) addOrd BS_add.
Proof. apply cantor_add_reflects. Qed.

Theorem BS_mul_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) mulOrd BS_mul.
Proof. apply cantor_mul_reflects. Qed.

Theorem BS_exp_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) expOrd BS_exp.
Proof. apply cantor_exp_reflects. Qed.

Theorem BS_nadd_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) naddOrd BS_nadd.
Proof. apply cantor_nadd_reflects. Qed.
