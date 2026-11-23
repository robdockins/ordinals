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

Open Scope ord_scope.
Open Scope bool_scope.

(** Part of the notation system up to the Bachmann–Howard ordinal; see @BachmannNotation.v@ for an overview. *)

(** * Interpolants

Every normal notation has interpolants: each ordinal below it is
bounded by a smaller normal notation which has interpolants in turn.
Under excluded middle this means that every ordinal below a notation
is denoted by a normal notation.  The proof has a semantic half
(@cfe_interp@/@bphi_interp@: everything below φ_T(u) lies below 1+u or
below a finite composition of the components of ⟦T⟧) and a syntactic
half (@cover@: each component is sandwiched, up to @bsub@, between
components given by normal notations, i.e. syntactic fundamental
sequences). *)

Abbreviation HI := (has_interpolants BS_denote BS_nf).

Lemma HI_zero : HI 0.
Proof.
  rewrite has_interpolants_unfold. intros i Hi.
  rewrite ord_lt_unfold in Hi. destruct Hi as [[] _].
Qed.

Lemma HI_below z γ : HI z -> γ < z ->
  exists n, BS_nf n /\ HI (BS_denote n) /\ γ ≤ BS_denote n /\ BS_denote n < z.
Proof.
  intros H Hγ. rewrite has_interpolants_unfold in H.
  destruct (H γ Hγ) as [n [H1 [H2 [H3 H4]]]]. exists n; auto.
Qed.

Lemma HI_succ m : BS_nf m -> HI (BS_denote m) -> HI (succOrd (BS_denote m)).
Proof.
  intros Hm H. rewrite has_interpolants_unfold. intros i Hi.
  rewrite ord_lt_unfold in Hi. destruct Hi as [[] Hi]. simpl in Hi.
  exists m. split; auto. split; auto. split; auto. apply succ_lt.
Qed.

Definition BS_onePlus (a:BSmall) : BSmall := normS (BN BIZ a).

Lemma BS_onePlus_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD) (addOrd 1) BS_onePlus.
Proof.
  intros x a [Hx Ha].
  assert (Hp : BS_proper (BN BIZ a)) by (split; [ exact I | apply (proj1 nf_proper); auto ]).
  split; [ | apply normS_nf; auto ].
  unfold BS_onePlus. rewrite normS_equal; auto. rewrite BS_denote_onePlus. rewrite Hx. reflexivity.
Qed.

Lemma HI_onePlus x : HI x -> HI (1 + x).
Proof.
  assert (Hz : reflects BSmall BS_denote BS_nf ORD 0 BZ) by (split; [ reflexivity | exact I ]).
  exact (onePlus_interpolants Hz BS_onePlus_reflects x).
Qed.

Lemma HI_eq x y : x ≈ y -> HI x -> HI y.
Proof. intro H. apply (proj1 (has_interpolants_eq_mor BS_denote BS_nf H)). Qed.

Lemma HI_one : HI (BS_denote BS_one).
Proof.
  apply HI_eq with (1 + 0).
  - rewrite BS_one_denote. apply addOrd_zero_r.
  - apply HI_onePlus, HI_zero.
Qed.

(** ** Syntactic covers of the children

Ω^e·0 is not a proper index term; @smartC@ drops a zero coefficient. *)

Definition smartC (e:BIdx) (c:BSmall) (r:BIdx) : BIdx :=
  match c with BZ => r | _ => BIC e c r end.

Lemma smartC_bequiv e c r : bequiv (BI_denote (smartC e c r)) (BI_denote (BIC e c r)).
Proof.
  destruct c as [|T y]; [ | apply bequiv_refl ].
  eapply bequiv_trans; [ apply bequiv_sym, bequiv_badd_zero_l | ].
  apply bequiv_badd; [ | apply bequiv_refl ].
  split; [ apply bsub_bzero_l | apply bsub_mul_zero ].
Qed.

Lemma smartC_nf e c r : BI_nf e -> BS_nf c -> BI_nf r -> lead_below r e -> BI_nf (smartC e c r).
Proof.
  destruct c as [|T y]; [ simpl; auto | ].
  intros He Hc Hr Hl. change (BI_nf e /\ BS_nf (BN T y) /\ 0 < BS_denote (BN T y) /\ BI_nf r /\ lead_below r e).
  split; [ | split; [ | split; [ apply BS_pos | ] ] ]; auto.
Qed.

Lemma Kin_smartC k e c r : Kin k (smartC e c r) -> Kin k (BIC e c r).
Proof. destruct c; simpl; tauto. Qed.

Lemma ilt_smartC e c r T0 : ilt (BIC e c r) T0 -> ilt r T0 -> ilt (smartC e c r) T0.
Proof. destruct c; auto. Qed.

Lemma ilt_trans a b c : ilt a b -> ilt b c -> ilt a c.
Proof.
  intro H. revert c.
  induction H as [e c r | e c r e' c' r' Hee IH | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr IH];
    intros t Ht; inversion Ht as [| ? ? ? e2 c2 r2 H1 | ? ? ? e2 c2 r2 H1 H2 | ? ? ? e2 c2 r2 H1 H2 H3]; subst.
  - constructor.
  - constructor.
  - constructor.
  - apply ilt_exp. auto.
  - apply ilt_exp. apply (ilt_ieq e e' Hee e e2); auto using ieq_refl.
  - apply ilt_exp. apply (ilt_ieq e e' Hee e e2); auto using ieq_refl.
  - apply ilt_exp. apply (ilt_ieq e' e2 H1 e e2); auto using ieq_refl, ieq_sym.
  - apply ilt_coef; [ eapply ieq_trans; eauto | eapply ord_lt_trans; eauto ].
  - apply ilt_coef; [ eapply ieq_trans; eauto | eapply ord_lt_le_trans; eauto; apply H2 ].
  - apply ilt_exp. apply (ilt_ieq e' e2 H1 e e2); auto using ieq_refl, ieq_sym.
  - apply ilt_coef; [ eapply ieq_trans; eauto | eapply ord_le_lt_trans; eauto; apply Hcc ].
  - apply ilt_tail; [ eapply ieq_trans; eauto | transitivity (BS_denote c'); auto | auto ].
Qed.

Lemma lead_below_ilt r' r e : ilt r' r -> lead_below r e -> lead_below r' e.
Proof.
  intros H Hl. destruct H as [e2 c2 r2 | e1 c1 r1 e2 c2 r2 H | e1 c1 r1 e2 c2 r2 H _ | e1 c1 r1 e2 c2 r2 H _ _];
    simpl in *; auto.
  - eapply ilt_trans; eauto.
  - apply (ilt_ieq e2 e Hl e1 e); auto using ieq_refl, ieq_sym.
  - apply (ilt_ieq e2 e Hl e1 e); auto using ieq_refl, ieq_sym.
Qed.

Definition KHI (T:BIdx) : Prop := forall k, Kin k T -> HI (BS_denote k).

(** Coefficient tracking for covers: a cover's coefficients stay below
    any infinite z that bounds the coefficients of T₀ in the Kend sense. *)
Lemma Kend_rest z e c r : r <> BIZ -> Kend z (BIC e c r) -> Klt z e /\ BS_denote c < z /\ Kend z r.
Proof. intros Hne H. destruct r as [|e2 c2 r2]; [ tauto | exact H ]. Qed.

Lemma Klt_smartC_coef z e c r n R : Kend z (BIC e c r) -> BS_denote n < BS_denote c -> Klt z R ->
  Klt z (smartC e n R).
Proof.
  intros H Hn HR. destruct n as [|T y]; [ exact HR | ].
  destruct (Kend_coef z e c r (BN T y) H Hn (BS_pos T y)) as [He Hc]. simpl. auto.
Qed.

Lemma Klt_smartC z e d r : Klt z e -> BS_denote d < z -> Klt z r -> Klt z (smartC e d r).
Proof. destruct d; simpl; auto. Qed.

Lemma Kend_cons z e c r : Klt z e -> BS_denote c < z -> Kend z r -> Kend z (BIC e c r).
Proof.
  intros He Hc Hr. destruct r as [|e2 c2 r2]; [ left; split; auto; apply ord_lt_le; auto | ].
  split; auto.
Qed.

Lemma Kend_smartC_coef z e c r n R : Kend z (BIC e c r) -> BS_denote n < BS_denote c -> Kend z R ->
  Kend z (smartC e n R).
Proof.
  intros H Hn HR. destruct n as [|T y]; [ exact HR | ].
  destruct (Kend_coef z e c r (BN T y) H Hn (BS_pos T y)) as [He Hc]. apply Kend_cons; auto.
Qed.

Lemma Kend_smartC_end z e x : Klt z e -> BS_denote x ≤ z -> Kend z (smartC e x BIZ).
Proof. intros He Hx. destruct x as [|T y]; [ exact I | left; auto ]. Qed.

Lemma ilt_ne r' r : ilt r' r -> r <> BIZ.
Proof. intros H E. subst. inversion H. Qed.

Lemma oinf_one z : oinf z -> 1 < z.
Proof. intro Hz. eapply ord_lt_le_trans; [ apply succ_lt | apply (Hz 2%nat) ]. Qed.

(** Every small child of ⟦T₀⟧ lies, up to @bsub@, below a normal index T
    which lies below another small child; every Ω-family member at a
    notation lies below a normal index which lies below another family's
    member at the same argument.  These are Bachmann's fundamental
    sequences up to @bsub@ in both directions. *)
Definition icov (T0:BIdx) : Prop :=
  (forall a, exists T, BI_nf T /\ KHI T /\ ilt T T0 /\
     (forall z, oinf z -> Kend z T0 -> Klt z T) /\
     bsub (bsmallSz (BI_denote T0) a) (BI_denote T) /\
     exists a', bsub (BI_denote T) (bsmallSz (BI_denote T0) a')) /\
  (forall d x, BS_nf x -> HI (BS_denote x) -> exists T, BI_nf T /\ KHI T /\ ilt T T0 /\
     (forall z, oinf z -> Kend z T0 -> BS_denote x ≤ z -> Kend z T) /\
     bsub (bbigSz (BI_denote T0) d (BS_denote x)) (BI_denote T) /\
     exists d', bsub (BI_denote T) (bbigSz (BI_denote T0) d' (BS_denote x))).

Lemma KHI_cons e c r : KHI (BIC e c r) -> KHI e /\ HI (BS_denote c) /\ KHI r.
Proof. intro H. split; [ | split ]; [ intros k Hk | | intros k Hk ]; apply H; simpl; auto. Qed.

Lemma KHI_intro e c r : KHI e -> HI (BS_denote c) -> KHI r -> KHI (BIC e c r).
Proof. intros H1 H2 H3 k [Hk|[Hk|Hk]]; [ auto | subst; auto | auto ]. Qed.

Lemma KHI_smartC e c r : KHI e -> HI (BS_denote c) -> KHI r -> KHI (smartC e c r).
Proof. intros H1 H2 H3 k Hk. apply (KHI_intro e c r); auto. apply Kin_smartC; auto. Qed.

Lemma KHI_nil : KHI BIZ.
Proof. intros k []. Qed.

(** A coefficient approximated from below by a notation n, itself
    below an immediate predecessor of the coefficient. *)
Lemma coef_approx c γ : HI (BS_denote c) -> γ < BS_denote c ->
  exists n, BS_nf n /\ HI (BS_denote n) /\ γ ≤ BS_denote n /\ BS_denote n < BS_denote c /\
    exists j, BS_denote n ≤ BS_denote c j.
Proof.
  intros H Hγ. destruct (HI_below _ _ H Hγ) as [n [Hn [HIn [H1 H2]]]].
  exists n. repeat split; auto.
  rewrite ord_lt_unfold in H2. exact H2.
Qed.

Lemma bsub_term_mono e e' γ n : bsub e e' -> γ ≤ n ->
  bsub (bmul (bexpΩ e) (embed γ)) (bmul (bexpΩ e') (embed n)).
Proof.
  intros He Hγ. eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed; exact Hγ | ].
  apply bsub_bmul_l, bsub_bexpΩ; auto.
Qed.

Theorem cover : forall T0, BI_nf T0 -> KHI T0 -> icov T0.
Proof.
  induction T0 as [|e IHe c r IHr]; intros HT HK.
  - split; [ intros [] | intros [] ].
  - destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
    destruct (KHI_cons _ _ _ HK) as [HKe [HKc HKr]].
    destruct (IHe He HKe) as [Se Fe]. destruct (IHr Hr HKr) as [Sr Fr].
    assert (Hnf : forall n x, BS_nf n -> BI_nf x -> lead_below x e -> BI_nf (smartC e n x)).
    { intros. apply smartC_nf; auto. }
    assert (Hilt : forall n x, BS_denote n < BS_denote c -> ilt x (BIC e c r) ->
                      ilt (smartC e n x) (BIC e c r)).
    { intros n x Hn Hx. apply ilt_smartC; auto. apply ilt_coef; auto using ieq_refl. }
    unfold icov.
    change (BI_denote (BIC e c r)) with
      (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r)).
    split.
    + intro a.
      destruct (badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a)
        as [[a' Ea]|[b Eb]]; rewrite ?Ea, ?Eb.
      * destruct (mul_small_form (bexpΩ (BI_denote e)) (BS_denote c) a') as [γ [Hγ [k Hk]]].
        rewrite Hk, bexpΩ_small_all.
        destruct (coef_approx c γ HKc Hγ) as [n [Hn [HIn [Hγn [Hnc [j Hj]]]]]].
        exists (smartC e n BIZ). split; [ apply Hnf; simpl; auto | split; [ apply KHI_smartC; auto using KHI_nil | ] ].
        split; [ apply Hilt; auto; constructor | ].
        split; [ intros z Hz HKz; apply (Klt_smartC_coef z e c r); simpl; auto | ].
        split.
        { eapply bsub_trans; [ | apply (proj2 (smartC_bequiv _ _ _)) ].
          apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl. }
        destruct (bexpΩ_small_zero (BI_denote e)) as [t0 Ht0].
        destruct (mul_small_back (bexpΩ (BI_denote e)) (BS_denote c) j t0) as [a0 Ha0].
        destruct (badd_small_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a0) as [a'' Ha''].
        exists a''. rewrite Ha'', Ha0, Ht0.
        eapply bsub_trans; [ apply (proj1 (smartC_bequiv _ _ _)) | ].
        apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl.
      * destruct (Sr b) as [r' [Hr' [HKr' [Hlt [Htr [Hlo [b' Hup]]]]]]].
        exists (BIC e c r'). split; [ simpl; repeat split; auto; eapply lead_below_ilt; eauto | ].
        split; [ apply KHI_intro; auto | ].
        split; [ apply ilt_tail; auto using ieq_refl; reflexivity | ].
        split; [ intros z Hz HKz; destruct (Kend_rest z e c r (ilt_ne _ _ Hlt) HKz) as [H1 [H2 H3]];
                 simpl; auto | ].
        split; [ simpl; apply bsub_badd_r; auto | ].
        destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) b') as [a'' Ha''].
        exists a''. rewrite Ha''. simpl. apply bsub_badd_r; auto.
    + intros d x Hx HIx.
      destruct (badd_big_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d)
        as [[d' Ed]|[d' Ed]]; rewrite Ed.
      * destruct (mul_big_form (bexpΩ (BI_denote e)) (BS_denote c) d') as [γ [Hγ [k Hk]]].
        rewrite Hk.
        destruct (coef_approx c γ HKc Hγ) as [n [Hn [HIn [Hγn [Hnc [j Hj]]]]]].
        destruct (bexpΩ_big_cases (BI_denote e) k) as [[q Hq]|[de Hde]].
        -- rewrite Hq. destruct (Se q) as [e' [He' [HKe' [Hlte [Htre [Hloe [q' Hupe]]]]]]].
           exists (smartC e n (smartC e' x BIZ)).
           split.
           { apply Hnf; auto. apply smartC_nf; simpl; auto. destruct x; simpl; auto. }
           split; [ apply KHI_smartC; auto; apply KHI_smartC; auto using KHI_nil | ].
           split; [ apply Hilt; auto; apply ilt_smartC; [ apply ilt_exp; auto | constructor ] | ].
           split; [ intros z Hz HKz Hxz; apply (Kend_smartC_coef z e c r); auto;
                    apply Kend_smartC_end; auto; apply Htre; auto; eapply Kend_exp; eauto | ].
           split.
           { eapply bsub_trans; [ | apply (proj2 (smartC_bequiv _ _ _)) ].
             simpl. apply bsub_trans with
               (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n))) (BI_denote (BIC e' x BIZ))).
             - apply bsub_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n)))
                                           (bmul (bexpΩ (bsmallSz (BI_denote e) q)) (embed (BS_denote x)))).
               + apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl.
               + apply bsub_badd_r. simpl. eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
                 apply bsub_term_mono; auto. reflexivity.
             - apply bsub_badd_r. apply (proj2 (smartC_bequiv _ _ _)). }
           destruct (bexpΩ_fam_s (BI_denote e) q') as [t0 Ht0].
           destruct (mul_big_back (bexpΩ (BI_denote e)) (BS_denote c) j t0) as [d0 Hd0].
           destruct (badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d0) as [d'' Hd''].
           exists d''. rewrite Hd'', Hd0, Ht0.
           eapply bsub_trans; [ apply (proj1 (smartC_bequiv _ _ _)) | ].
           simpl. apply bsub_trans with
             (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n))) (BI_denote (BIC e' x BIZ))).
           ++ apply bsub_badd_r. apply (proj1 (smartC_bequiv _ _ _)).
           ++ eapply bsub_trans; [ apply bsub_badd_l, bsub_term_mono; [ apply bsub_refl | exact Hj ] | ].
              apply bsub_badd_r. simpl. eapply bsub_trans; [ apply (proj1 (bequiv_badd_zero_r _)) | ].
              apply bsub_term_mono; auto. reflexivity.
        -- rewrite Hde. destruct (Fe de x Hx HIx) as [e' [He' [HKe' [Hlte [Htre [Hloe [de' Hupe]]]]]]].
           exists (smartC e n (BIC e' BS_one BIZ)).
           assert (H1 : bequiv (bmul (bexpΩ (BI_denote e')) (embed (BS_denote BS_one))) (bexpΩ (BI_denote e'))).
           { eapply bequiv_trans; [ apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_embed, BS_one_denote ] | ].
             split; apply bsub_bmul_one. }
           split.
           { apply Hnf; [ exact Hn | | exact Hlte ].
             change (BI_nf e' /\ BS_nf BS_one /\ 0 < BS_denote BS_one /\ BI_nf BIZ /\ lead_below BIZ e').
             split; [ exact He' | split; [ apply BS_one_nf | split; [ | split; exact I ] ] ].
             rewrite BS_one_denote. apply succ_lt. }
           split; [ apply KHI_smartC; auto; apply KHI_intro; auto using KHI_nil, HI_one | ].
           split; [ apply Hilt; auto; apply ilt_exp; auto | ].
           split; [ intros z Hz HKz Hxz; apply (Kend_smartC_coef z e c r); auto;
                    right; split; [ apply Htre; auto; eapply Kend_exp; eauto | apply BS_one_denote ] | ].
           split.
           { eapply bsub_trans; [ | apply (proj2 (smartC_bequiv _ _ _)) ].
             simpl. apply bsub_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n)))
                                                (bexpΩ (bbigSz (BI_denote e) de (BS_denote x)))).
             - apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl.
             - apply bsub_badd_r. eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
               eapply bsub_trans; [ | apply (proj2 H1) ]. apply bsub_bexpΩ; auto. }
           destruct (bexpΩ_big_b (BI_denote e) de') as [t0 Ht0].
           destruct (mul_big_back (bexpΩ (BI_denote e)) (BS_denote c) j t0) as [d0 Hd0].
           destruct (badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d0) as [d'' Hd''].
           exists d''. rewrite Hd'', Hd0, Ht0.
           eapply bsub_trans; [ apply (proj1 (smartC_bequiv _ _ _)) | ].
           simpl. apply bsub_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n)))
                                              (bexpΩ (BI_denote e'))).
           ++ apply bsub_badd_r. eapply bsub_trans; [ apply (proj1 (bequiv_badd_zero_r _)) | apply (proj1 H1) ].
           ++ eapply bsub_trans; [ apply bsub_badd_l, bsub_term_mono; [ apply bsub_refl | exact Hj ] | ].
              apply bsub_badd_r. apply bsub_bexpΩ; auto.
      * destruct (Fr d' x Hx HIx) as [r' [Hr' [HKr' [Hlt [Htr [Hlo [d'' Hup]]]]]]].
        exists (BIC e c r'). split; [ simpl; repeat split; auto; eapply lead_below_ilt; eauto | ].
        split; [ apply KHI_intro; auto | ].
        split; [ apply ilt_tail; auto using ieq_refl; reflexivity | ].
        split; [ intros z Hz HKz Hxz; destruct (Kend_rest z e c r (ilt_ne _ _ Hlt) HKz) as [H1 [H2 H3]];
                 apply Kend_cons; auto | ].
        split; [ simpl; apply bsub_badd_r; auto | ].
        destruct (badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d'') as [d0 Hd0].
        exists d0. rewrite Hd0. simpl. apply bsub_badd_r; auto.
Qed.

(** ** Interpolation

By induction on the index tree (in the well-founded order @blt@) and
then on the argument: below φ_T(u), everything lies below 1+u (handled
by the interpolants of 1+x), or below a word in f and the components
applied to 0 or to the successor of an earlier value.  Each component
is replaced by the φ of a covering normal index, which takes notations
to notations, has interpolants by induction (its tree lies below a
child of ⟦T⟧), and stays below φ_T(u) because it lies below another
component. *)

Lemma onePlus_mono : forall x y, x ≤ y -> 1 + x ≤ 1 + y.
Proof. apply normal_monotone, onePlus_normal. Qed.

Lemma nf_BN_proper T y : BI_nf T -> BS_nf y -> BS_proper (BN T y).
Proof. intros. split; [ apply (proj2 nf_proper) | apply (proj1 nf_proper) ]; auto. Qed.

Theorem interp_aux : forall U T, BI_nf T -> KHI T -> ble (BI_denote T) U ->
  forall u, complete u -> HI u -> HI (bphi (addOrd 1) (BI_denote T) u).
Proof.
  intro U. induction U as [U IHU] using (well_founded_induction blt_wf).
  intros T HT HK HU u. induction u as [u IHu] using ordinal_induction. intros Hu HIu.
  destruct (cover T HT HK) as [CS CF].
  assert (Hg := BI_good T). assert (Hfam := BI_bfam T).
  set (X := BI_denote T) in *.
  set (V := bphi (addOrd 1) X u).
  assert (Hcomp : forall T', BI_nf T' -> KHI T' -> blt (BI_denote T') X ->
             forall m, BS_nf m -> HI (BS_denote m) -> HI (bphi (addOrd 1) (BI_denote T') (BS_denote m))).
  { intros T' HT' HK' Hlt m Hm HIm.
    apply (IHU (BI_denote T')); auto using ble_refl, BS_complete.
    apply blt_le_trans with X; auto. }
  rewrite has_interpolants_unfold. intros i Hi.
  destruct (bphi_interp _ onePlus_normal X u i Hg Hu Hi) as [Hi1 | [Hinh [o [w [Hiw Hst]]]]].
  - destruct (HI_below _ _ (HI_onePlus u HIu) Hi1) as [n [Hn [HIn [H1 H2]]]].
    exists n. repeat split; auto.
    eapply ord_lt_le_trans; [ exact H2 | apply bphi_ge_f ].
  - destruct (bfix_value_full _ onePlus_normal X u Hg Hinh Hu) as [Hf1 [Hf2 Hf3]].
    fold V in Hf1, Hf2, Hf3.
    assert (Hchain : forall w x0 m, BS_nf m -> x0 ≤ BS_denote m -> BS_denote m ≤ V -> HI (BS_denote m) ->
      exists m', BS_nf m' /\ wev (addOrd 1) _ (bphi_fam (addOrd 1) (bsmallSz X) (bbigSz X)) w x0 ≤ BS_denote m' /\
                 BS_denote m' ≤ V /\ HI (BS_denote m')).
    { clear Hiw Hst. intro w0.
      induction w0 as [|[[a|c]|] w0 IHw]; intros x0 m Hm L0 U0 HI0; simpl.
      - exists m; auto.
      - destruct (IHw x0 m Hm L0 U0 HI0) as [m1 [Hm1 [L1 [U1 HI1]]]].
        destruct (CS a) as [T' [HT' [HK' [_ [_ [Hlo [a' Hup]]]]]]].
        assert (Hp := nf_BN_proper T' m1 HT' Hm1).
        exists (normS (BN T' m1)). split; [ apply normS_nf; auto | ].
        rewrite (normS_equal _ Hp). simpl.
        split; [ | split ].
        + transitivity (bphi (addOrd 1) (bsmallSz X a) (BS_denote m1)).
          * apply (proj1 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a))); auto.
          * apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam T'))); auto.
        + transitivity (bphi (addOrd 1) (bsmallSz X a') (BS_denote m1)).
          { apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a'))); auto. }
          transitivity (bphi (addOrd 1) (bsmallSz X a') V); auto.
          apply (proj1 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a'))); auto.
        + apply Hcomp; auto. apply (bsub_child_blt _ X (inl a')). auto.
      - destruct (IHw x0 m Hm L0 U0 HI0) as [m1 [Hm1 [L1 [U1 HI1]]]].
        destruct (CF c m1 Hm1 HI1) as [T' [HT' [HK' [_ [_ [Hlo [c' Hup]]]]]]].
        assert (Hp := nf_BN_proper T' BZ HT' I).
        exists (normS (BN T' BZ)). split; [ apply normS_nf; auto | ].
        rewrite (normS_equal _ Hp). simpl.
        split; [ | split ].
        + transitivity (bphi (addOrd 1) (bbigSz X c (BS_denote m1)) 0).
          * apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c _))).
            apply bfam_fam; auto.
          * apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam T'))); auto.
        + transitivity (bphi (addOrd 1) (bbigSz X c' (BS_denote m1)) 0).
          { apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c' _))); auto. }
          transitivity (bphi (addOrd 1) (bbigSz X c' V) 0); auto.
          apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c' _))).
          apply bfam_fam; auto.
        + apply (Hcomp T' HT' HK' (bsub_child_blt _ X (inr (c', BS_denote m1)) Hup) BZ I HI_zero).
      - destruct (IHw x0 m Hm L0 U0 HI0) as [m1 [Hm1 [L1 [U1 HI1]]]].
        destruct (BS_onePlus_reflects (BS_denote m1) m1 (conj (ord_eq_refl _) Hm1)) as [E1 N1].
        exists (BS_onePlus m1). split; auto.
        rewrite <- E1. split; [ | split ].
        + apply onePlus_mono; auto.
        + transitivity (1 + V); auto. apply onePlus_mono; auto.
        + apply HI_onePlus; auto. }
    assert (Hstart : exists m, BS_nf m /\
      match o with None => 0 | Some j => succOrd (bphi (addOrd 1) X (u j)) end ≤ BS_denote m /\
      BS_denote m ≤ V /\ HI (BS_denote m)).
    { destruct o as [j|].
      - assert (Hj : u j < u) by apply index_lt.
        destruct (HI_below _ _ HIu Hj) as [n [Hn [HIn [H1 H2]]]].
        assert (Hp := nf_BN_proper T n HT Hn).
        set (m0 := normS (BN T n)).
        assert (Hm0 : BS_nf m0) by (apply normS_nf; auto).
        assert (E0 : BS_denote m0 ≈ bphi (addOrd 1) X (BS_denote n)) by (apply normS_equal; auto).
        destruct (BS_succ_reflects (BS_denote m0) m0 (conj (ord_eq_refl _) Hm0)) as [E1 N1].
        exists (BS_succ m0). split; auto.
        rewrite <- E1. split; [ | split ].
        + apply succ_monotone. rewrite E0.
          apply (proj1 (bphi_mono_index _ onePlus_mono _ Hfam)); auto.
        + apply succ_least. rewrite E0.
          apply (normal_increasing _ (BI_normal T)); auto.
        + apply HI_succ; auto. apply HI_eq with (bphi (addOrd 1) X (BS_denote n)); [ symmetry; auto | ].
          apply IHu; auto using BS_complete.
      - exists BZ. split; [ exact I | ]. split; [ reflexivity | ]. split; [ apply zero_least | exact HI_zero ]. }
    destruct Hstart as [m [Hm [L0 [U0 HI0]]]].
    destruct (Hchain w _ m Hm L0 U0 HI0) as [m' [Hm' [L [U' HI']]]].
    destruct (HI_below _ i HI' (ord_lt_le_trans _ _ _ Hiw L)) as [n [Hn [HIn [H1 H2]]]].
    exists n. repeat split; auto. eapply ord_lt_le_trans; eauto.
Qed.

Lemma notation_KHI : (forall x, BS_nf x -> HI (BS_denote x)) /\ (forall T, BI_nf T -> KHI T).
Proof.
  apply BNotation_mut.
  - intros _. exact HI_zero.
  - intros T IHT y IHy [HT [Hy _]].
    apply (interp_aux (BI_denote T) T HT (IHT HT) (ble_refl _) _ (BS_complete y) (IHy Hy)).
  - intros _. exact KHI_nil.
  - intros e IHe c IHc r IHr [He [Hc [_ [Hr _]]]].
    apply KHI_intro; auto.
Qed.

Theorem BS_has_all_interpolants : has_all_interpolants BS_denote BS_nf.
Proof. intros x Hx. apply notation_KHI; auto. Qed.

Theorem BS_has_enough_notations : ClassicalFacts.excluded_middle -> has_enough_notations BS_denote BS_nf.
Proof.
  intro EM. apply has_interpolants_has_enough_notations; auto using BS_complete.
  apply BS_has_all_interpolants.
Qed.
