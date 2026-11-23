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
From Ordinal Require Import Notation.BachmannOrderType.
From Ordinal Require Import Notation.BachmannAbsorb.

Open Scope ord_scope.
Open Scope bool_scope.

(** Part of the notation system up to the Bachmann–Howard ordinal; see @BachmannNotation.v@ for an overview. *)

(** * Normal forms of improper index sums *)

Lemma ilt_ieq_false : forall a b, ilt a b -> ieq a b -> False.
Proof.
  intros a b H. induction H as [e c r | e c r e' c' r' Hee IH | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr IH];
    intro E; inversion E as [|? ? ? ? ? ? E1 E2 E3]; subst; auto.
  apply (ord_lt_irreflexive (BS_denote c)). rewrite E2 at 2. auto.
Qed.

Lemma ilt_irrefl a : ilt a a -> False.
Proof. intro H. apply (ilt_ieq_false a a H (ieq_refl a)). Qed.

Lemma ilt_asym a b : ilt a b -> ilt b a -> False.
Proof. intros H1 H2. apply (ilt_irrefl a). eapply ilt_trans; eauto. Qed.

Definition cmpIX (a b:BIdx) : ordering := cmpI (S (BI_size a + BI_size b)) a b.

Lemma cmpIX_spec a b : BI_nf a -> BI_nf b ->
  (ilt a b -> cmpIX a b = LT) /\ (ieq a b -> cmpIX a b = EQ) /\ (ilt b a -> cmpIX a b = GT).
Proof.
  intros Ha Hb. assert (H := proj2 (cmp_correct (S (BI_size a + BI_size b))) a b ltac:(lia) Ha Hb).
  unfold cmpIX. destruct (cmpI (S (BI_size a + BI_size b)) a b); simpl in H.
  - split; [ auto | split; intro H'; exfalso ].
    + apply (ilt_ieq_false a b H H').
    + eapply ilt_asym; eauto.
  - split; [ intro H'; exfalso | split; [ auto | intro H'; exfalso ] ].
    + apply (ilt_ieq_false a b H' H).
    + apply (ilt_ieq_false b a H'). apply ieq_sym; auto.
  - split; [ intro H'; exfalso | split; [ intro H'; exfalso | auto ] ].
    + eapply ilt_asym; eauto.
    + apply (ilt_ieq_false b a H). apply ieq_sym; auto.
Qed.

Lemma cmpIX_total a b : BI_nf a -> BI_nf b -> ilt a b \/ ieq a b \/ ilt b a.
Proof.
  intros Ha Hb. assert (H := proj2 (cmp_correct (S (BI_size a + BI_size b))) a b ltac:(lia) Ha Hb).
  destruct (cmpI (S (BI_size a + BI_size b)) a b); simpl in H; auto.
Qed.

(** Adding a term Ω^e·c in front of a normal index. *)
Definition addT (e:BIdx) (c:BSmall) (A:BIdx) : BIdx :=
  match A with
  | BIZ => BIC e c BIZ
  | BIC e2 c2 r2 =>
    match cmpIX e e2 with
    | LT => A
    | EQ => BIC e (BS_add c c2) r2
    | GT => BIC e c A
    end
  end.

Fixpoint normX (X:BIdx) : BIdx :=
  match X with
  | BIZ => BIZ
  | BIC e c r => addT (normX e) c (normX r)
  end.

(** Improper indices, at every depth of exponents, with positive normal
    coefficients. *)
Fixpoint imp_ok (X:BIdx) : Prop :=
  match X with
  | BIZ => True
  | BIC e c r => imp_ok e /\ BS_nf c /\ 0 < BS_denote c /\ imp_ok r
  end.

Lemma nf_imp_ok X : BI_nf X -> imp_ok X.
Proof. induction X as [|e IHe c r IH]; simpl; auto. intros [He [Hc [Hc0 [Hr _]]]]. auto. Qed.

Section addT.
  Variables (e:BIdx) (c:BSmall).
  Hypothesis He : BI_nf e.
  Hypothesis Hc : BS_nf c.
  Hypothesis Hc0 : 0 < BS_denote c.

  Lemma addT_lt e2 c2 r2 : BI_nf e2 -> ilt e e2 -> addT e c (BIC e2 c2 r2) = BIC e2 c2 r2.
  Proof. intros H2 H. unfold addT. rewrite (proj1 (cmpIX_spec e e2 He H2) H). reflexivity. Qed.

  Lemma addT_eq e2 c2 r2 : BI_nf e2 -> ieq e e2 -> addT e c (BIC e2 c2 r2) = BIC e (BS_add c c2) r2.
  Proof. intros H2 H. unfold addT. rewrite (proj1 (proj2 (cmpIX_spec e e2 He H2)) H). reflexivity. Qed.

  Lemma addT_gt e2 c2 r2 : BI_nf e2 -> ilt e2 e -> addT e c (BIC e2 c2 r2) = BIC e c (BIC e2 c2 r2).
  Proof. intros H2 H. unfold addT. rewrite (proj2 (proj2 (cmpIX_spec e e2 He H2)) H). reflexivity. Qed.

  Lemma add_reflect c2 : BS_nf c2 -> BS_denote (BS_add c c2) ≈ BS_denote c + BS_denote c2 /\ BS_nf (BS_add c c2).
  Proof.
    intro H2. destruct (BS_add_reflects _ c (conj (ord_eq_refl _) Hc) _ c2 (conj (ord_eq_refl _) H2)) as [E N].
    split; auto. symmetry; auto.
  Qed.

  Lemma addT_nf A : BI_nf A -> BI_nf (addT e c A).
  Proof.
    destruct A as [|e2 c2 r2]; [ intros _; repeat split; auto | ].
    intro HA. assert (HA' := HA). destruct HA' as [He2 [Hc2 [Hc20 [Hr2 Hl2]]]].
    destruct (cmpIX_total e e2 He He2) as [H|[H|H]].
    - rewrite addT_lt; auto.
    - rewrite addT_eq; auto. destruct (add_reflect c2 Hc2) as [E N].
      split; [ exact He | split; [ exact N | split; [ | split; [ exact Hr2 | ] ] ] ].
      + rewrite E. eapply ord_lt_le_trans; [ exact Hc0 | apply addOrd_le1 ].
      + apply (lead_below_ieq r2 r2 e2 e); auto using ieq_refl, ieq_sym.
    - rewrite addT_gt; auto. repeat split; auto.
  Qed.

  (** Ordinal addition is strictly monotone on the right. *)
  Lemma addT_mono A B : BI_nf A -> BI_nf B -> ilt A B -> ilt (addT e c A) (addT e c B).
  Proof.
    intros HA HB Hlt.
    destruct B as [|eB cB rB]; [ inversion Hlt | ].
    assert (HB' := HB). destruct HB' as [HeB [HcB [HcB0 _]]].
    destruct (add_reflect cB HcB) as [EB NB].
    destruct A as [|eA cA rA].
    - simpl addT at 1.
      destruct (cmpIX_total e eB He HeB) as [H|[H|H]].
      + rewrite addT_lt; auto. apply ilt_exp; auto.
      + rewrite addT_eq; auto. apply ilt_coef; auto using ieq_refl.
        rewrite EB. apply ord_le_lt_trans with (BS_denote c + 0); [ apply addOrd_zero_r | ].
        apply addOrd_increasing; auto.
      + rewrite addT_gt; auto. apply ilt_tail; auto using ieq_refl; try reflexivity; constructor.
    - assert (HA' := HA). destruct HA' as [HeA [HcA [HcA0 _]]].
      destruct (add_reflect cA HcA) as [EA NA].
      assert (HeAB : ilt eA eB \/ ieq eA eB).
      { inversion Hlt; subst; auto. }
      destruct (cmpIX_total e eA He HeA) as [H|[H|H]].
      + rewrite addT_lt; auto.
        rewrite addT_lt; auto. destruct HeAB as [H'|H']; [ eapply ilt_trans; eauto | ].
        apply (ilt_ieq e eA H e eB); auto using ieq_refl.
      + rewrite addT_eq; auto. destruct HeAB as [H'|H'].
        * assert (HeB' : ilt e eB) by (apply (ilt_ieq eA eB H' e eB); auto using ieq_refl, ieq_sym).
          rewrite addT_lt; auto. apply ilt_exp; auto.
        * assert (HeB' : ieq e eB) by (eapply ieq_trans; eauto).
          rewrite addT_eq; auto.
          inversion Hlt as [| ? ? ? ? ? ? Hx | ? ? ? ? ? ? Hx Hc' | ? ? ? ? ? ? Hx Hc' Hr']; subst.
          -- exfalso. apply (ilt_ieq_false eA eB); auto.
          -- apply ilt_coef; auto using ieq_refl. rewrite EA, EB. apply addOrd_increasing; auto.
          -- apply ilt_tail; auto using ieq_refl. rewrite EA, EB. rewrite Hc'. reflexivity.
      + rewrite addT_gt; auto.
        destruct (cmpIX_total e eB He HeB) as [H2|[H2|H2]].
        * rewrite addT_lt; auto. apply ilt_exp; auto.
        * rewrite addT_eq; auto. apply ilt_coef; auto using ieq_refl.
          rewrite EB. apply ord_le_lt_trans with (BS_denote c + 0); [ apply addOrd_zero_r | ].
          apply addOrd_increasing; auto.
        * rewrite addT_gt; auto. apply ilt_tail; auto using ieq_refl. reflexivity.
  Qed.
End addT.

Lemma normX_nf X : imp_ok X -> BI_nf (normX X).
Proof.
  induction X as [|e IHe c r IH]; simpl; auto.
  intros [He [Hc [Hc0 Hr]]]. apply addT_nf; auto.
Qed.

(** On normal indices, normX is the identity. *)
Lemma normX_id X : BI_nf X -> normX X = X.
Proof.
  induction X as [|e IHe c r IH]; simpl; auto.
  intros [He [Hc [Hc0 [Hr Hl]]]]. rewrite IH, IHe; auto.
  destruct r as [|e2 c2 r2]; [ reflexivity | ].
  apply addT_gt; auto. apply Hr.
Qed.

(** ** Covering the components of an improper index *)

Definition icovX (T0:BIdx) : Prop :=
  (forall a, exists T, imp_ok T /\ KHI T /\ ilt (normX T) (normX T0) /\
     (forall z, oinf z -> Kend z T0 -> Klt z T) /\
     bsub (bsmallSz (BI_denote T0) a) (BI_denote T) /\
     exists a', bsub (BI_denote T) (bsmallSz (BI_denote T0) a')) /\
  (forall d x, BS_nf x -> HI (BS_denote x) -> exists T, imp_ok T /\ KHI T /\ ilt (normX T) (normX T0) /\
     (forall z, oinf z -> Kend z T0 -> BS_denote x ≤ z -> Kend z T) /\
     bsub (bbigSz (BI_denote T0) d (BS_denote x)) (BI_denote T) /\
     exists d', bsub (BI_denote T) (bbigSz (BI_denote T0) d' (BS_denote x))).

Lemma normX_ne K r : ilt (normX K) (normX r) -> r <> BIZ.
Proof. intros H E. subst. inversion H. Qed.

Lemma imp_ok_smartC e n x : imp_ok e -> BS_nf n -> imp_ok x -> imp_ok (smartC e n x).
Proof.
  intros He Hn Hx. destruct n as [|T y]; [ exact Hx | ].
  exact (conj He (conj Hn (conj (BS_pos T y) Hx))).
Qed.

(** Anything below the leading term Ω^{normX e}·c is below normX (Ω^e·c + r). *)
Lemma ilt_below_head e c r K : imp_ok e -> BS_nf c -> 0 < BS_denote c -> imp_ok r ->
  ilt K (BIC (normX e) c BIZ) -> ilt K (normX (BIC e c r)).
Proof.
  intros He Hc Hc0 Hr HKl. simpl. assert (HnR := normX_nf r Hr). assert (HnE := normX_nf e He).
  destruct (normX r) as [|e2 c2 r2] eqn:Er; [ exact HKl | ].
  eapply ilt_trans; [ exact HKl | ].
  change (BIC (normX e) c BIZ) with (addT (normX e) c BIZ).
  apply addT_mono; auto. constructor. constructor.
Qed.

Lemma ilt_cover_term e c r n x : imp_ok e -> BS_nf c -> 0 < BS_denote c -> imp_ok r ->
  BS_nf n -> BS_denote n < BS_denote c -> imp_ok x -> lead_below (normX x) (normX e) ->
  ilt (normX (smartC e n x)) (normX (BIC e c r)).
Proof.
  intros He Hc Hc0 Hr Hn Hnc Hx Hl. apply ilt_below_head; auto.
  assert (HnE := normX_nf e He). assert (Hnx := normX_nf x Hx).
  destruct n as [|Tn yn].
  - change (smartC e BZ x) with x.
    destruct (normX x) as [|e2 c2 r2]; [ constructor | apply ilt_exp; exact Hl ].
  - change (normX (smartC e (BN Tn yn) x)) with (addT (normX e) (BN Tn yn) (normX x)).
    destruct (normX x) as [|e2 c2 r2] eqn:Ex.
    + simpl. apply ilt_coef; auto using ieq_refl.
    + rewrite addT_gt; auto; [ | apply Hnx ]. apply ilt_coef; auto using ieq_refl.
Qed.

Lemma lead_cover_small e e' x : imp_ok e' -> ilt (normX e') (normX e) ->
  lead_below (normX (smartC e' x BIZ)) (normX e).
Proof.
  intros He' Hl. destruct x as [|T y]; [ exact I | ].
  change (lead_below (addT (normX e') (BN T y) BIZ) (normX e)). exact Hl.
Qed.

Theorem coverX : forall T0, imp_ok T0 -> KHI T0 -> icovX T0.
Proof.
  induction T0 as [|e IHe c r IHr]; intros HT HK.
  - split; [ intros [] | intros [] ].
  - destruct HT as [He [Hc [Hc0 Hr]]].
    destruct (KHI_cons _ _ _ HK) as [HKe [HKc HKr]].
    destruct (IHr Hr HKr) as [Sr Fr].
    destruct (IHe He HKe) as [Se Fe].
    assert (HnR := normX_nf r Hr). assert (HnE := normX_nf e He).
    assert (Hmono : forall K, imp_ok K -> ilt (normX K) (normX r) ->
                      ilt (normX (BIC e c K)) (normX (BIC e c r))).
    { intros K HKo Hl. simpl. apply addT_mono; auto using normX_nf. }
    unfold icovX.
    change (BI_denote (BIC e c r)) with
      (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r)).
    split.
    + intro a.
      destruct (badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a)
        as [[a' Ea]|[b Eb]]; rewrite ?Ea, ?Eb.
      * destruct (mul_small_form (bexpΩ (BI_denote e)) (BS_denote c) a') as [γ [Hγ [k Hk]]].
        rewrite Hk, bexpΩ_small_all.
        destruct (coef_approx c γ HKc Hγ) as [n [Hn [HIn [Hγn [Hnc [j Hj]]]]]].
        exists (smartC e n BIZ). split; [ apply imp_ok_smartC; simpl; auto | ].
        split; [ apply KHI_smartC; auto using KHI_nil | ].
        split; [ apply ilt_cover_term; simpl; auto | ].
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
      * destruct (Sr b) as [K [HKo [HKK [HKl [Htr [Hlo [b' Hup]]]]]]].
        exists (BIC e c K). split; [ repeat split; auto | split; [ apply KHI_intro; auto | split ] ].
        { apply Hmono; auto. }
        split; [ intros z Hz HKz; intros;
                 destruct (Kend_rest z e c r (normX_ne _ _ HKl) HKz) as [H1 [H2 H3]];
                 first [ apply Kend_cons; auto | simpl; auto ] | ].
        split; [ apply bsub_badd_r; auto | ].
        destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) b') as [t Et].
        exists t. rewrite Et. apply bsub_badd_r; auto.
    + intros d x Hx HIx.
      destruct (badd_big_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d)
        as [[d' Ed]|[d' Ed]]; rewrite Ed.
      * destruct (mul_big_form (bexpΩ (BI_denote e)) (BS_denote c) d') as [γ [Hγ [k Hk]]].
        rewrite Hk.
        destruct (coef_approx c γ HKc Hγ) as [n [Hn [HIn [Hγn [Hnc [j Hj]]]]]].
        destruct (bexpΩ_big_cases (BI_denote e) k) as [[q Hq]|[de Hde]].
        -- rewrite Hq. destruct (Se q) as [e' [He' [HKe' [Hlte [Htre [Hloe [q' Hupe]]]]]]].
           exists (smartC e n (smartC e' x BIZ)).
           split; [ apply imp_ok_smartC; auto; apply imp_ok_smartC; simpl; auto | ].
           split; [ apply KHI_smartC; auto; apply KHI_smartC; auto using KHI_nil | ].
           split; [ apply ilt_cover_term; auto; [ apply imp_ok_smartC; simpl; auto | apply lead_cover_small; auto ] | ].
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
           assert (Hx1 : imp_ok (BIC e' BS_one BIZ)).
           { split; [ exact He' | split; [ apply BS_one_nf | split; [ | exact I ] ] ].
             rewrite BS_one_denote. apply succ_lt. }
           split; [ apply imp_ok_smartC; auto | ].
           split; [ apply KHI_smartC; auto; apply KHI_intro; auto using KHI_nil, HI_one | ].
           split; [ apply ilt_cover_term; auto; exact Hlte | ].
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
      * destruct (Fr d' x Hx HIx) as [K [HKo [HKK [HKl [Htr [Hlo [d'' Hup]]]]]]].
        exists (BIC e c K). split; [ repeat split; auto | split; [ apply KHI_intro; auto | split ] ].
        { apply Hmono; auto. }
        split; [ intros z Hz HKz; intros;
                 destruct (Kend_rest z e c r (normX_ne _ _ HKl) HKz) as [H1 [H2 H3]];
                 first [ apply Kend_cons; auto | simpl; auto ] | ].
        split; [ apply bsub_badd_r; auto | ].
        destruct (badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d'') as [t Et].
        exists t. rewrite Et. apply bsub_badd_r; auto.
Qed.


(** ** Nesting for improper indices *)

Lemma ilt_lead r1 e1 e2 c2 r2 : lead_below r1 e1 -> ieq e1 e2 -> ilt r1 (BIC e2 c2 r2).
Proof.
  destruct r1 as [|e3 c3 r3]; simpl; [ constructor | ].
  intros H He. apply ilt_exp. apply (ilt_ieq e3 e1 H); auto using ieq_refl.
Qed.

(** Ω^E1·c1 + R ⊑ Ω^E·c + (Ω^E1·d + R) when E1 ≈ E and c1 ≤ c + d. *)
Lemma merge_bsub E1 E c c1 d R : bequiv E1 E -> c1 ≤ c + d ->
  bsub (badd (bmul (bexpΩ E1) (embed c1)) R)
       (badd (bmul (bexpΩ E) (embed c)) (badd (bmul (bexpΩ E1) (embed d)) R)).
Proof.
  intros [HE1 HE2] Hc.
  eapply bsub_trans; [ apply bsub_badd_l, (bsub_term_mono _ _ _ _ HE1 Hc) | ].
  eapply bsub_trans; [ apply (proj2 (bequiv_merge (bexpΩ E) c d R)) | ].
  apply bsub_badd_r, bsub_badd_l, bsub_term_mono; auto with ord.
Qed.



(** Coefficients below an additively principal z stay below z under normX
    (merged coefficients are sums of coefficients). *)
Lemma Klt_addT z e c A : (forall a, a < z -> a + z ≤ z) -> BI_nf e -> BS_nf c -> BI_nf A ->
  Klt z e -> BS_denote c < z -> Klt z A -> Klt z (addT e c A).
Proof.
  intros Hp He Hc HA HKe Hcz HKA. destruct A as [|e2 c2 r2]; [ simpl; auto | ].
  destruct HA as [He2 [Hc2 _]]. destruct HKA as [HKe2 [Hc2z HKr2]].
  destruct (cmpIX_total e e2 He He2) as [H|[H|H]].
  - rewrite addT_lt; auto. simpl; auto.
  - rewrite addT_eq; auto. destruct (add_reflect c Hc c2 Hc2) as [E _].
    simpl. split; [ auto | split; [ | auto ] ]. rewrite E.
    eapply ord_lt_le_trans; [ apply addOrd_increasing; exact Hc2z | apply Hp; auto ].
  - rewrite addT_gt; auto. simpl; auto.
Qed.

Lemma Klt_normX z : (forall a, a < z -> a + z ≤ z) -> forall X, imp_ok X -> Klt z X -> Klt z (normX X).
Proof.
  intros Hp X. induction X as [|e IHe c r IH]; simpl; auto.
  intros [He [Hc [Hc0 Hr]]] [HKe [Hcz HKr]]. apply Klt_addT; auto using normX_nf.
Qed.


(** ** Coefficient positions under normX *)

Lemma imp_ok_pos X : imp_ok X -> BI_pos X.
Proof.
  induction X as [|e IHe c r IH]; simpl; auto.
  intros [He [_ [Hc0 Hr]]]. auto.
Qed.

Lemma normX_BIZ X : normX X = BIZ -> X = BIZ.
Proof.
  destruct X as [|e c r]; simpl; auto. unfold addT.
  destruct (normX r) as [|e2 c2 r2]; [ discriminate | destruct (cmpIX (normX e) e2); discriminate ].
Qed.

Lemma Kend_ofX T z : imp_ok T -> (forall k, Kge k T -> k ≤ z) -> (forall k, Kgs k T -> k < z) -> Kend z T.
Proof.
  induction T as [|e IHe c r IHr]; intros HT H1 H2; [ exact I | ].
  destruct HT as [He [Hc [Hc0 Hr]]].
  destruct r as [|e2 c2 r2].
  - assert (Hcmp := BS_compare_correct c BS_one Hc BS_one_nf).
    destruct (BS_compare c BS_one); cbv beta iota delta [ordering_correct] in Hcmp.
    + exfalso. rewrite BS_one_denote in Hcmp. rewrite ord_lt_unfold in Hcmp. destruct Hcmp as [u Hle].
      apply (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ exact Hc0 | exact Hle ].
    + right. split; [ | rewrite Hcmp; apply BS_one_denote ].
      apply IHe; auto.
      * intros k Hk. apply H1. simpl. auto.
      * intros k Hk. apply H2. simpl. right. split; auto. rewrite Hcmp; apply BS_one_denote.
    + left. split.
      * apply Klt_of_Kge. intros k Hk. apply H2. simpl. left. split; auto.
        rewrite <- BS_one_denote. exact Hcmp.
      * apply H1. simpl. right. left. reflexivity.
  - split; [ | split ].
    + apply Klt_of_Kge. intros k Hk. apply H2. simpl. auto.
    + apply H2. simpl. right. left. reflexivity.
    + apply IHr; auto.
      * intros k Hk. apply H1. simpl. auto.
      * intros k Hk. apply H2. simpl. auto.
Qed.

(** Coefficients of an improper T lie below z except at the end, when
    φ_T(0) ≤ z. *)
Lemma Kend_of_valueX T z : imp_ok T -> PHI T 0 ≤ z -> Kend z T.
Proof.
  intros HT Hz. apply Kend_ofX; auto.
  - intros k Hk. rewrite <- Hz. apply (dominance T BZ k (imp_ok_pos T HT) Hk).
  - intros k Hk. eapply ord_lt_le_trans; [ apply (Kgs_lt T k (imp_ok_pos T HT) Hk) | exact Hz ].
Qed.

(** P2: for an additively principal infinite z, the Kend condition passes
    from X to its normal form. *)
Theorem Kend_normX z : oinf z -> (forall a, a < z -> a + z ≤ z) ->
  forall X, imp_ok X -> Kend z X -> Kend z (normX X).
Proof.
  intros Hz Hp X. induction X as [|e IHe c r IH]; [ auto | ].
  intros [He [Hc [Hc0 Hr]]] HK. simpl normX.
  assert (HE := normX_nf e He).
  assert (HN := normX_nf r Hr).
  destruct (normX r) as [|e2 c2 r2] eqn:EN.
  { rewrite (normX_BIZ r EN) in HK. simpl addT.
    destruct HK as [[H1 H2]|[H1 H2]]; [ left; split; auto; apply Klt_normX; auto | right; split; auto ]. }
  assert (Hne : r <> BIZ) by (intro E; subst; discriminate).
  destruct (Kend_rest z e c r Hne HK) as [HKe0 [Hcz HKr]].
  assert (HKe : Klt z (normX e)) by (apply Klt_normX; auto).
  specialize (IH Hr HKr).
  destruct HN as [He2 [Hc2 [Hc20 [Hr2 Hl2]]]].
  destruct (cmpIX_total (normX e) e2 HE He2) as [H|[H|H]].
  - rewrite addT_lt; auto.
  - rewrite addT_eq; auto. destruct (add_reflect c Hc c2 Hc2) as [E _].
    destruct r2 as [|e3 c3 r3].
    + left. split; auto. rewrite E.
      assert (Hc2z : BS_denote c2 ≤ z).
      { destruct IH as [[_ H']|[_ H']]; auto. rewrite H'. apply ord_lt_le, oinf_one; auto. }
      transitivity (BS_denote c + z); [ apply addOrd_monotone; auto with ord | apply Hp; auto ].
    + destruct IH as [_ [Hc2z HK3]].
      split; [ auto | split; [ | exact HK3 ] ]. rewrite E.
      eapply ord_lt_le_trans; [ apply addOrd_increasing; exact Hc2z | apply Hp; auto ].
  - rewrite addT_gt; auto. simpl. auto.
Qed.

(** The absorbed terms of X, at every depth: those Ω^e·c dropped by normX. *)
Fixpoint AbsLt (v:Ord) (X:BIdx) : Prop :=
  match X with
  | BIZ => True
  | BIC e c r => AbsLt v e /\ AbsLt v r /\ (lead_gt (normX r) (normX e) -> Klt v (BIC e c BIZ))
  end.

(** Given the absorbed coefficients below z, coefficients below z pass
    back from the normal form to X. *)
Lemma Klt_back z : forall X, imp_ok X -> AbsLt z X -> Klt z (normX X) -> Klt z X.
Proof.
  intro X. induction X as [|e IHe c r IH]; [ auto | ].
  intros [He [Hc [Hc0 Hr]]] [HAe [HAr HAt]] HK. simpl normX in HK.
  assert (HE := normX_nf e He). assert (HN := normX_nf r Hr).
  destruct (normX r) as [|e2 c2 r2] eqn:EN.
  { rewrite (normX_BIZ r EN). simpl in HK. destruct HK as [H1 [H2 _]]. simpl. auto. }
  destruct HN as [He2 [Hc2 _]].
  destruct (cmpIX_total (normX e) e2 HE He2) as [H|[H|H]].
  - rewrite addT_lt in HK; auto. destruct (HAt H) as [H1 [H2 _]]. simpl. auto.
  - rewrite addT_eq in HK; auto. destruct (add_reflect c Hc c2 Hc2) as [E _].
    destruct HK as [HKe [Hs HK3]]. rewrite E in Hs.
    simpl. split; [ auto | split ].
    + eapply ord_le_lt_trans; [ apply addOrd_le1 | exact Hs ].
    + apply IH; auto. split; [ apply (Klt_ieq z e2 (normX e)); auto using ieq_sym | split; auto ].
      eapply ord_le_lt_trans; [ apply addOrd_le2 | exact Hs ].
  - rewrite addT_gt in HK; auto. destruct HK as [HKe [Hcz HK2]]. simpl. auto.
Qed.

(** P1: given the absorbed coefficients below z, the Kend condition passes
    back from the normal form to X. *)
Theorem Kend_back z : oinf z -> forall X, imp_ok X -> AbsLt z X -> Kend z (normX X) -> Kend z X.
Proof.
  intros Hz X. induction X as [|e IHe c r IH]; [ auto | ].
  intros [He [Hc [Hc0 Hr]]] [HAe [HAr HAt]] HK. simpl normX in HK.
  assert (HE := normX_nf e He).
  assert (HN := normX_nf r Hr).
  destruct (normX r) as [|e2 c2 r2] eqn:EN.
  { rewrite (normX_BIZ r EN). simpl addT in HK.
    destruct HK as [[H1 H2]|[H1 H2]]; [ left; split; auto; apply Klt_back; auto | right; split; auto ]. }
  assert (Hne : r <> BIZ) by (intro E; subst; discriminate).
  destruct HN as [He2 [Hc2 [Hc20 [Hr2 Hl2]]]].
  assert (Goal : Klt z e -> BS_denote c < z -> Kend z (BIC e2 c2 r2) -> Kend z (BIC e c r)).
  { intros H1 H2 H3. specialize (IH Hr HAr H3).
    destruct r as [|e4 c4 r4]; [ tauto | ]. split; auto. }
  destruct (cmpIX_total (normX e) e2 HE He2) as [H|[H|H]].
  - rewrite addT_lt in HK; auto. destruct (HAt H) as [H1 [H2 _]]. auto.
  - rewrite addT_eq in HK; auto. destruct (add_reflect c Hc c2 Hc2) as [E _].
    assert (Hcc : BS_denote c < BS_denote c + BS_denote c2).
    { apply ord_le_lt_trans with (BS_denote c + 0); [ apply addOrd_zero_r | apply addOrd_increasing; auto ]. }
    destruct r2 as [|e3 c3 r3].
    + destruct HK as [[HKe Hs]|[_ Hs]].
      * rewrite E in Hs. apply Goal; auto.
        -- apply Klt_back; auto.
        -- eapply ord_lt_le_trans; eauto.
        -- left. split; [ apply (Klt_ieq z e2 (normX e)); auto using ieq_sym | ].
           transitivity (BS_denote c + BS_denote c2); auto. apply addOrd_le2.
      * exfalso. rewrite E in Hs.
        apply (ord_lt_irreflexive 1). apply ord_le_lt_trans with (BS_denote c); [ apply succ_least; auto | ].
        rewrite <- Hs. exact Hcc.
    + destruct HK as [HKe [Hs HK3]]. rewrite E in Hs.
      apply Goal; auto.
      * apply Klt_back; auto.
      * eapply ord_lt_trans; eauto.
      * split; [ apply (Klt_ieq z e2 (normX e)); auto using ieq_sym | split; [ | exact HK3 ] ].
        eapply ord_le_lt_trans; [ apply addOrd_le2 | exact Hs ].
  - rewrite addT_gt in HK; auto. destruct HK as [HKe [Hcz HK2]]. apply Goal; auto. apply Klt_back; auto.
Qed.

(** ** The largest absorbed coefficient *)

Definition absb (e A:BIdx) : bool :=
  match A with BIZ => false | BIC e2 _ _ => isLT (cmpIX e e2) end.

Lemma absb_true e A : BI_nf e -> BI_nf A -> absb e A = true -> lead_gt A e.
Proof.
  destruct A as [|e2 c2 r2]; [ discriminate | ]. intros He [He2 _] Hb. cbn [absb lead_gt] in *.
  destruct (cmpIX_spec e e2 He He2) as [_ [S2 S3]].
  destruct (cmpIX_total e e2 He He2) as [H|[H|H]]; auto.
  - rewrite (S2 H) in Hb. discriminate.
  - rewrite (S3 H) in Hb. discriminate.
Qed.

Lemma absb_false e A : BI_nf e -> BI_nf A -> absb e A = false -> lead_gt A e -> False.
Proof.
  destruct A as [|e2 c2 r2]; [ auto | ]. intros He [He2 _] Hb H. cbn [absb lead_gt] in *.
  rewrite (proj1 (cmpIX_spec e e2 He He2) H) in Hb. discriminate.
Qed.

Fixpoint absX (n:nat) (X:BIdx) : option BSmall :=
  match X with
  | BIZ => None
  | BIC e c r =>
      omax n (absX n e)
        (if absb (normX e) (normX r) then omax n (kmax n (BIC e c BIZ)) (absX n r) else absX n r)
  end.

Lemma Kin_nfX k T : Kin k T -> imp_ok T -> BS_nf k.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [He [Hc [_ Hr]]]; [ auto | subst; auto | auto ].
Qed.

Lemma kmax_specX n : forall T, imp_ok T -> (BI_size T + BI_size T < n)%nat -> kmax_ok T (kmax n T).
Proof.
  induction T as [|e IHe c r IHr]; intros HT Hsz; simpl; auto.
  simpl in Hsz. destruct HT as [He [Hc [Hc0 Hr]]].
  set (P := fun u => BS_nf u /\ (BS_size u <= BI_size (BIC e c r))%nat /\ Kin u (BIC e c r)).
  assert (HP : forall u v, P u -> P v -> ordering_correct (cmpS n u v) (BS_denote u) (BS_denote v)).
  { intros u v [Hu [Hsu _]] [Hv [Hsv _]]. apply (proj1 (cmp_correct n)); auto. simpl in Hsu, Hsv. lia. }
  assert (He' := IHe He ltac:(lia)). assert (Hr' := IHr Hr ltac:(lia)).
  assert (Pe : match kmax n e with None => True | Some u => P u end).
  { destruct (kmax n e) as [u|]; auto. destruct He' as [Hin Hle].
    split; [ apply (Kin_nfX u e); auto | split; [ pose proof (Kin_size' u e Hin); simpl; lia | simpl; auto ] ]. }
  assert (Pc : P c).
  { split; auto. split; [ simpl; lia | simpl; auto ]. }
  assert (Pr : match kmax n r with None => True | Some u => P u end).
  { destruct (kmax n r) as [u|]; auto. destruct Hr' as [Hin Hle].
    split; [ apply (Kin_nfX u r); auto | split; [ pose proof (Kin_size' u r Hin); simpl; lia | simpl; auto ] ]. }
  assert (S1 := omax_spec n (kmax n e) (Some c) P HP Pe Pc).
  destruct (omax n (kmax n e) (Some c)) as [w1|] eqn:E1; [ | destruct S1 as [_ D]; discriminate ].
  destruct S1 as [Pw1 [_ [Lw1e Lw1c]]].
  assert (S2 := omax_spec n (Some w1) (kmax n r) P HP Pw1 Pr).
  destruct (omax n (Some w1) (kmax n r)) as [w|] eqn:E2; [ | destruct S2 as [D _]; discriminate ].
  destruct S2 as [Pw [_ [Lw1 Lwr]]].
  split; [ apply Pw | ].
  simpl. split; [ | split ].
  - destruct (kmax n e) as [u|]; [ | simpl in He'; rewrite He'; exact I ].
    destruct He' as [_ Hle]. apply Kle_mono with (BS_denote u); auto. transitivity (BS_denote w1); auto.
  - transitivity (BS_denote w1); auto.
  - destruct (kmax n r) as [u|]; [ | rewrite Hr'; exact I ].
    destruct Hr' as [_ Hle]. apply Kle_mono with (BS_denote u); auto.
Qed.

Lemma Kgs_Kge k T : Kgs k T -> Kge k T.
Proof.
  induction T as [|e IHe c r IHr]; [ simpl; tauto | ].
  destruct r as [|e2 c2 r2].
  - intros [[H _]|[_ H]]; left; auto.
  - intros [H|[H|H]]; [ left; auto | right; left; auto | right; right; auto ].
Qed.

Lemma Kgs_cons k e c r : Kgs k r -> Kgs k (BIC e c r).
Proof. destruct r as [|e2 c2 r2]; simpl; [ tauto | auto ]. Qed.

Lemma Kgs_absorbed k e c r : r <> BIZ -> Kin k (BIC e c BIZ) -> Kgs (BS_denote k) (BIC e c r).
Proof.
  intros Hne H. apply Kin_Kge in H. destruct r as [|e2 c2 r2]; [ tauto | ].
  simpl in H |- *. tauto.
Qed.

Lemma Kgs_exp k e c r : BS_nf c -> 0 < BS_denote c -> Kgs k e -> Kgs k (BIC e c r).
Proof.
  intros Hc Hc0 H. destruct r as [|e2 c2 r2]; [ | left; apply Kgs_Kge; auto ].
  assert (Hcmp := BS_compare_correct c BS_one Hc BS_one_nf).
  destruct (BS_compare c BS_one); cbv beta iota delta [ordering_correct] in Hcmp.
  - exfalso. rewrite BS_one_denote in Hcmp. rewrite ord_lt_unfold in Hcmp. destruct Hcmp as [u Hle].
    apply (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ exact Hc0 | exact Hle ].
  - right. split; auto. rewrite Hcmp. apply BS_one_denote.
  - left. split; [ apply Kgs_Kge; auto | ]. rewrite <- BS_one_denote. exact Hcmp.
Qed.

(** The specification shape of a candidate maximum. *)
Definition ospec (n:nat) (P:Ord -> Prop) (K:BSmall -> Prop) (o:option BSmall) : Prop :=
  match o with
  | None => forall v, P v
  | Some m => BS_nf m /\ (BS_size m + BS_size m < n)%nat /\ K m /\ forall v, BS_denote m < v -> P v
  end.

Lemma ospec_mono n P1 P2 K1 K2 o : (forall v, P1 v -> P2 v) -> (forall m, K1 m -> K2 m) ->
  ospec n P1 K1 o -> ospec n P2 K2 o.
Proof. destruct o as [m|]; simpl; [ intuition | auto ]. Qed.

Lemma omax_join n Pa Pb K oa ob : ospec n Pa K oa -> ospec n Pb K ob ->
  ospec n (fun v => Pa v /\ Pb v) K (omax n oa ob).
Proof.
  destruct oa as [a|]; destruct ob as [b|]; intros Ha Hb; simpl in *.
  - destruct Ha as [Na [Sa [Ka Va]]]. destruct Hb as [Nb [Sb [Kb Vb]]].
    assert (Hcmp := proj1 (cmp_correct n) a b ltac:(lia) Na Nb).
    destruct (isLT_spec _ _ _ Hcmp) as [S1 S2].
    destruct (isLT (cmpS n a b)); simpl.
    + specialize (S1 eq_refl). repeat split; auto. apply Va. eapply ord_lt_trans; eauto.
    + specialize (S2 eq_refl). repeat split; auto. apply Vb. eapply ord_le_lt_trans; eauto.
  - destruct Ha as [Na [Sa [Ka Va]]]. repeat split; auto.
  - destruct Hb as [Nb [Sb [Kb Vb]]]. repeat split; auto.
  - auto.
Qed.

Lemma absX_spec n : forall X, imp_ok X -> (BI_size X + BI_size X < n)%nat ->
  ospec n (fun v => AbsLt v X) (fun m => Kgs (BS_denote m) X) (absX n X).
Proof.
  induction X as [|e IHe c r IH]; [ simpl; auto | ].
  intros HX Hsz. assert (HX' := HX). destruct HX' as [He [Hc [Hc0 Hr]]].
  simpl in Hsz. assert (Hr1 : (1 <= BI_size r)%nat) by (destruct r; simpl; lia).
  specialize (IHe He ltac:(lia)). specialize (IH Hr ltac:(lia)).
  assert (HN := normX_nf r Hr). assert (HE := normX_nf e He).
  cbn [absX AbsLt].
  eapply ospec_mono; [ | | apply (omax_join n (fun v => AbsLt v e)
      (fun v => AbsLt v r /\ (lead_gt (normX r) (normX e) -> Klt v (BIC e c BIZ)))
      (fun m => Kgs (BS_denote m) (BIC e c r))) ].
  - intros v [H1 H2]. split; auto.
  - auto.
  - eapply ospec_mono; [ | | exact IHe ]; auto. intros m Hm. apply Kgs_exp; auto.
  - destruct (absb (normX e) (normX r)) eqn:Eb.
    + assert (Hlg := absb_true (normX e) (normX r) HE HN Eb).
      assert (Hne : r <> BIZ) by (intro E; subst; contradiction).
      assert (HP : imp_ok (BIC e c BIZ)) by (repeat split; auto).
      assert (Hk := kmax_specX n (BIC e c BIZ) HP ltac:(cbn [BI_size]; lia)).
      destruct (kmax n (BIC e c BIZ)) as [k|]; [ | discriminate ].
      destruct Hk as [Hkin Hkle].
      eapply ospec_mono; [ | | apply (omax_join n (fun v => Klt v (BIC e c BIZ)) (fun v => AbsLt v r)
                                         (fun m => Kgs (BS_denote m) (BIC e c r))) ].
      * intros v [H1 H2]. split; auto.
      * auto.
      * simpl. split; [ apply (Kin_nfX k _ Hkin HP) | split; [ | split ] ].
        -- pose proof (Kin_size' k _ Hkin). cbn [BI_size] in *. lia.
        -- apply Kgs_absorbed; auto.
        -- intros v Hv. change (Klt v (BIC e c BIZ)). apply Kle_lt with (BS_denote k); auto.
      * eapply ospec_mono; [ | | exact IH ]; auto. intros m Hm. apply Kgs_cons; auto.
    + assert (Hna : lead_gt (normX r) (normX e) -> False) by (apply absb_false; auto).
      eapply ospec_mono; [ | | exact IH ].
      * intros v H. split; auto. intro H'. exfalso; auto.
      * intros m Hm. apply Kgs_cons; auto.
Qed.

Definition absM (X:BIdx) : option BSmall := absX (S (BI_size X + BI_size X)) X.

(** The offset of X: the least t with m_X < φ_{normX X}(t), or 0 when
    nothing is absorbed. *)
Definition offX (X:BIdx) : BSmall :=
  match absM X with None => BZ | Some m => BS_offset (normX X) m end.

Lemma absM_spec X : imp_ok X ->
  match absM X with
  | None => forall v, AbsLt v X
  | Some m => BS_nf m /\ Kgs (BS_denote m) X /\ forall v, BS_denote m < v -> AbsLt v X
  end.
Proof.
  intro HX. assert (H := absX_spec (S (BI_size X + BI_size X)) X HX ltac:(lia)).
  unfold absM. destruct (absX _ X); simpl in H; tauto.
Qed.

Lemma lead_big_addT e c A : BI_nf e -> BI_nf A -> lead_big A -> lead_big (addT e c A).
Proof.
  destruct A as [|e2 c2 r2]; [ contradiction | ]. intros He [He2 _] Hb. simpl in Hb.
  destruct (cmpIX_total e e2 He He2) as [H|[H|H]].
  - rewrite addT_lt; auto.
  - rewrite addT_eq; auto. simpl. intro E. subst. inversion H. subst. auto.
  - rewrite addT_gt; auto. simpl. intro E. subst. inversion H.
Qed.

Lemma lead_big_addT_e e c A : BI_nf e -> e <> BIZ -> BI_nf A -> lead_big (addT e c A).
Proof.
  intros He Hne HA. destruct A as [|e2 c2 r2]; [ exact Hne | ].
  destruct HA as [He2 _].
  destruct (cmpIX_total e e2 He He2) as [H|[H|H]].
  - rewrite addT_lt; auto. simpl. intro E. subst. inversion H.
  - rewrite addT_eq; auto.
  - rewrite addT_gt; auto.
Qed.

Lemma lead_gt_big' A e : lead_gt A e -> lead_big A.
Proof. destruct A as [|e2 c2 r2]; simpl; [ tauto | ]. intros H E. subst. inversion H. Qed.

Lemma omax_none n a b : omax n a b = None -> a = None /\ b = None.
Proof. destruct a; destruct b; simpl; auto; try destruct (isLT _); discriminate. Qed.

Lemma lead_big_ne A : lead_big A -> A <> BIZ.
Proof. intros H E. subst. contradiction. Qed.

(** Something is absorbed only if the normal form has a nonzero leading
    exponent. *)
Lemma absX_lead_big n : forall X, imp_ok X -> absX n X <> None -> lead_big (normX X).
Proof.
  induction X as [|e IHe c r IH]; [ simpl; tauto | ].
  intros [He [Hc [Hc0 Hr]]] Hn. assert (HN := normX_nf r Hr). assert (HE := normX_nf e He).
  simpl normX. cbn [absX] in Hn.
  destruct (absX n e) as [m|] eqn:Ee.
  { apply lead_big_addT_e; auto. apply lead_big_ne, IHe; auto. try discriminate; rewrite Ee; discriminate. }
  destruct (absb (normX e) (normX r)) eqn:Eb.
  - apply lead_big_addT; auto. apply (lead_gt_big' _ (normX e)). apply absb_true; auto.
  - apply lead_big_addT; auto.
Qed.

Lemma absM_lead_big X : imp_ok X -> absM X <> None -> lead_big (normX X).
Proof. apply absX_lead_big. Qed.


(** ** Hereditary absorption *)

(** Shifted enumeration, abstracting @absorb_enum@: if Fix(X) ⊆ Fix(R),
    the values of φ_X lie in an upward closed region U, and the common
    fixpoints of R at notations in U are common fixpoints of X, then φ_X
    is φ_R shifted by the least t with φ_R(t) ∈ U. *)
Section shift.
  Variables (X R:BIdx) (U:Ord -> Prop) (t:BSmall).
  Hypothesis HXinh : inhabited (bsmall (BI_denote X) + bbig (BI_denote X)).
  Hypothesis Hsub : forall z, complete z -> bfix (addOrd 1) (BI_denote X) z -> bfix (addOrd 1) (BI_denote R) z.
  Hypothesis Hreg : forall y, complete y -> U (PHI X y).
  Hypothesis Hup : forall a b, a ≤ b -> U a -> U b.
  Hypothesis Ht : BS_nf t.
  Hypothesis HUt : U (PHI R (BS_denote t)).
  Hypothesis Hleast : forall z, complete z -> bfix (addOrd 1) (BI_denote R) z -> U z -> PHI R (BS_denote t) ≤ z.
  Hypothesis Hprin : forall z, complete z -> bfix (addOrd 1) (BI_denote R) z -> U z -> BS_denote t + z ≤ z.
  Hypothesis ABS : forall s, BS_nf s -> U (PHI R (BS_denote s)) -> bfix (addOrd 1) (BI_denote X) (PHI R (BS_denote s)).

  Theorem shift_enum : forall y, BS_nf y -> PHI X (BS_denote y) ≈ PHI R (BS_denote t + BS_denote y).
  Proof.
    assert (Htc := BS_complete t).
    assert (Hgx := BI_good X). assert (Hgr := BI_good R).
    intro y. induction y as [y IH] using (size_induction (ord BSmall BS_denote)). intro Hy.
    assert (HIy := BS_has_all_interpolants y Hy).
    assert (Hyc := BS_complete y).
    destruct (BS_add_reflects _ t (conj (ord_eq_refl _) Ht) _ y (conj (ord_eq_refl _) Hy)) as [Es Ns].
    set (s := BS_add t y) in *.
    assert (EPs : PHI R (BS_denote s) ≈ PHI R (BS_denote t + BS_denote y))
      by (apply ord_eq_normal; [ apply BI_normal | symmetry; exact Es ]).
    assert (Hsc := BS_complete s).
    rewrite <- EPs. split.
    - rewrite (bphi_unfold _ (BI_denote X)).
      apply (cfe_least (addOrd 1) onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgx)).
      + transitivity (1 + BS_denote s); [ | apply bphi_ge_f ].
        apply onePlus_mono. rewrite <- Es. apply addOrd_le2.
      + apply limit_least. intro j. cbv beta. rewrite <- bphi_unfold.
        destruct (HI_below _ _ HIy (index_lt _ j)) as [n [Hn [HIn [Hjn Hny]]]].
        eapply ord_le_lt_trans; [ apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam X))); exact Hjn | ].
        rewrite (IH n Hny Hn).
        eapply ord_lt_le_trans; [ | apply (proj2 EPs) ].
        apply (normal_increasing _ (BI_normal R)); [ apply addOrd_complete; auto | ].
        apply addOrd_increasing; auto.
      + assert (HK : U (PHI R (BS_denote s))).
        { apply Hup with (PHI R (BS_denote t)); auto.
          apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam R))).
          rewrite <- Es. apply addOrd_le1. }
        destruct (ABS s Ns HK) as [H1 [H2 H3]].
        intros [k|k]; cbn [bphi_fam]; split; auto.
    - set (z := PHI X (BS_denote y)).
      assert (Hzc : complete z) by (apply BS_complete with (x := BN X y)).
      assert (Hzfix := Hsub z Hzc (bfix_value_full _ onePlus_normal _ _ Hgx HXinh Hyc)).
      assert (HUz : U z) by (apply Hreg; auto).
      assert (Hlz := Hleast z Hzc Hzfix HUz).
      assert (Hpr := Hprin z Hzc Hzfix HUz).
      rewrite (bphi_unfold _ (BI_denote R)).
      apply (cfe_least (addOrd 1) onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgr)).
      + transitivity (1 + z); [ apply onePlus_mono | apply Hzfix ].
        rewrite <- Es. rewrite <- Hpr. apply addOrd_monotone; [ reflexivity | ].
        apply normal_inflationary; auto using BI_normal.
      + apply limit_least. intro j. cbv beta. rewrite <- bphi_unfold.
        assert (Hj : BS_denote s j < BS_denote t + BS_denote y)
          by (eapply ord_lt_le_trans; [ apply index_lt | apply (proj2 Es) ]).
        assert (Hjc : complete (BS_denote s j)) by (apply complete_subord; auto).
        destruct (addOrd_lt_cases _ _ _ Hj) as [Ha|[j0 Ha]].
        * eapply ord_lt_le_trans; [ | exact Hlz ]. apply (normal_increasing _ (BI_normal R)); auto.
        * destruct (HI_below _ _ HIy (index_lt _ j0)) as [n [Hn [HIn [Hjn Hny]]]].
          apply ord_le_lt_trans with (PHI R (BS_denote t + BS_denote n)).
          { apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam R))).
            rewrite Ha. apply addOrd_monotone; [ reflexivity | exact Hjn ]. }
          rewrite <- (IH n Hny Hn).
          apply (normal_increasing _ (BI_normal X)); auto.
      + destruct Hzfix as [H1 [H2 H3]].
        intros [k|k]; cbn [bphi_fam]; split; auto.
  Qed.
End shift.

(** ⟦normX X⟧ ⊑ ⟦X⟧, with equality when nothing is absorbed. *)
Lemma merge_bequiv e c e2 c2 r2 : ieq e e2 -> BS_nf c -> BS_nf c2 ->
  bequiv (BI_denote (BIC e (BS_add c c2) r2))
         (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote (BIC e2 c2 r2))).
Proof.
  intros H Hc Hc2. destruct (add_reflect c Hc c2 Hc2) as [E _].
  change (bequiv (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote (BS_add c c2)))) (BI_denote r2))
                 (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
                       (badd (bmul (bexpΩ (BI_denote e2)) (embed (BS_denote c2))) (BI_denote r2)))).
  apply bequiv_sym.
  apply bequiv_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
             (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c2))) (BI_denote r2))).
  { apply bequiv_badd; [ apply bequiv_refl | ].
    apply bequiv_badd; [ | apply bequiv_refl ].
    apply bequiv_bmul; [ apply bequiv_bexpΩ, bequiv_sym, ieq_bequiv; auto | apply bequiv_refl ]. }
  eapply bequiv_trans; [ apply bequiv_merge | ].
  apply bequiv_badd; [ | apply bequiv_refl ].
  apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_embed; symmetry; auto ].
Qed.

Lemma bsub_normX X : imp_ok X -> bsub (BI_denote (normX X)) (BI_denote X).
Proof.
  induction X as [|e IHe c r IH]; [ intros; apply bsub_refl | ].
  intros [He0 [Hc [Hc0 Hr]]]. specialize (IH Hr). specialize (IHe He0). simpl normX.
  apply bsub_trans with (BI_denote (BIC (normX e) c r)).
  2: { change (bsub (badd (bmul (bexpΩ (BI_denote (normX e))) (embed (BS_denote c))) (BI_denote r))
                    (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r))).
       apply bsub_badd_l, bsub_term_mono; [ exact IHe | reflexivity ]. }
  assert (He := normX_nf e He0). set (E := normX e) in *. clearbody E. clear IHe He0.
  assert (HN := normX_nf r Hr).
  destruct (normX r) as [|e2 c2 r2] eqn:EN.
  { rewrite (normX_BIZ r EN). apply bsub_refl. }
  destruct HN as [He2 [Hc2 _]].
  change (BI_denote (BIC E c r)) with (badd (bmul (bexpΩ (BI_denote E)) (embed (BS_denote c))) (BI_denote r)).
  destruct (cmpIX_total E e2 He He2) as [H|[H|H]].
  - rewrite addT_lt; auto. eapply bsub_trans; [ exact IH | apply bsub_absorb ].
  - rewrite addT_eq; auto. eapply bsub_trans; [ apply (proj1 (merge_bequiv E c e2 c2 r2 H Hc Hc2)) | ].
    apply bsub_badd_r; auto.
  - rewrite addT_gt; auto. apply bsub_badd_r; auto.
Qed.

Lemma omax_some_l n u b : omax n (Some u) b <> None.
Proof. destruct b; simpl; [ destruct (isLT _) | ]; discriminate. Qed.

Lemma omax_some_r n a v : omax n a (Some v) <> None.
Proof. destruct a; simpl; [ destruct (isLT _) | ]; discriminate. Qed.

Lemma kmax_some n e c r : kmax n (BIC e c r) <> None.
Proof.
  cbn [kmax]. destruct (omax n (kmax n e) (Some c)) eqn:E.
  - apply omax_some_l.
  - exfalso. apply (omax_some_r n (kmax n e) c E).
Qed.

Lemma bequiv_normX n : forall X, imp_ok X -> absX n X = None -> bequiv (BI_denote (normX X)) (BI_denote X).
Proof.
  induction X as [|e IHe c r IH]; [ intros; apply bequiv_refl | ].
  intros [He0 [Hc [Hc0 Hr]]] Ha. cbn [absX] in Ha.
  destruct (omax_none _ _ _ Ha) as [Hae Ha'].
  specialize (IHe He0 Hae).
  assert (HN := normX_nf r Hr).
  assert (He := normX_nf e He0).
  destruct (absb (normX e) (normX r)) eqn:Eb.
  { exfalso. destruct (kmax n (BIC e c BIZ)) eqn:Ek.
    - apply (omax_some_l n b (absX n r)). exact Ha'.
    - apply (kmax_some n e c BIZ Ek). }
  specialize (IH Hr Ha'). simpl normX.
  apply bequiv_trans with (BI_denote (BIC (normX e) c r)).
  2: { change (bequiv (badd (bmul (bexpΩ (BI_denote (normX e))) (embed (BS_denote c))) (BI_denote r))
                      (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r))).
       apply bequiv_badd; [ | apply bequiv_refl ].
       apply bequiv_bmul; [ apply bequiv_bexpΩ; exact IHe | apply bequiv_refl ]. }
  set (E := normX e) in *. clearbody E. clear IHe He0 Hae.
  destruct (normX r) as [|e2 c2 r2] eqn:EN.
  { rewrite (normX_BIZ r EN). apply bequiv_refl. }
  assert (HNn := HN). destruct HN as [He2 [Hc2 _]].
  change (BI_denote (BIC E c r)) with (badd (bmul (bexpΩ (BI_denote E)) (embed (BS_denote c))) (BI_denote r)).
  destruct (cmpIX_total E e2 He He2) as [H|[H|H]].
  - exfalso. apply (absb_false E (BIC e2 c2 r2)); auto.
  - rewrite addT_eq; auto. eapply bequiv_trans; [ apply (merge_bequiv E c e2 c2 r2 H Hc Hc2) | ].
    apply bequiv_badd; auto using bequiv_refl.
  - rewrite addT_gt; auto. apply bequiv_badd; auto using bequiv_refl.
Qed.

Lemma imp_ok_KHI X : imp_ok X -> KHI X.
Proof.
  induction X as [|e IHe c r IH]; [ intros _; apply KHI_nil | ].
  intros [He [Hc [_ Hr]]]. apply KHI_intro; auto.
  apply (proj1 notation_KHI); auto.
Qed.



(** The Bachmann-rule clause for X at z. *)
Definition ClX (X:BIdx) (z:Ord) : Prop :=
  1 + z ≤ z /\ forall T', BI_nf T' -> ilt T' (normX X) -> Klt z T' -> PHI T' z ≤ z.

(** (⇐) at notation values: an additively principal z satisfying the
    coefficient condition and the clause is a common fixpoint for X. *)
Definition JX (X:BIdx) : Prop := forall w, BS_nf w ->
  Kend (BS_denote w) X -> (forall a, a < BS_denote w -> a + BS_denote w ≤ BS_denote w) ->
  ClX X (BS_denote w) -> bfix (addOrd 1) (BI_denote X) (BS_denote w).

(** The enumeration theorem. *)
Definition EX (X:BIdx) : Prop := forall y, BS_nf y ->
  PHI X (BS_denote y) ≈ PHI (normX X) (BS_denote (offX X) + BS_denote y).

Lemma EX_of_JX X : imp_ok X -> JX X -> EX X.
Proof.
  intros HX HJ. unfold EX, offX.
  assert (HN := normX_nf X HX). set (N := normX X) in *.
  assert (HA := absM_spec X HX). destruct (absM X) as [m|] eqn:Em.
  2: { intros y Hy. unfold absM in Em.
       transitivity (PHI N (BS_denote y)).
       - apply bphi_bequiv; auto using onePlus_mono, BI_bfam. apply bequiv_sym, (bequiv_normX _ X HX Em).
       - apply ord_eq_normal; [ apply BI_normal | ]. simpl BS_denote. symmetry. apply addOrd_zero_l. }
  destruct HA as [Hm [Hmg Hmv]].
  assert (Hlb : lead_big N) by (apply absM_lead_big; auto; rewrite Em; discriminate).
  assert (HNne : N <> BIZ) by (destruct N; simpl in Hlb; [ contradiction | discriminate ]).
  assert (HXne : X <> BIZ) by (intro E; subst; discriminate).
  destruct (BS_offset_correct N HN Hlb m Hm) as [Nt [Hmt [Htt Hleast]]].
  apply (shift_enum X N (fun z => BS_denote m < z)); auto.
  - destruct X as [|e c r]; [ contradiction | ]. apply BI_inh, HX.
  - intros z Hz Hf. apply (bfix_bsub _ onePlus_normal _ _ z (bsub_normX X HX) (BI_bfam X) Hf).
  - intros y Hy. eapply ord_lt_le_trans; [ apply (Kgs_lt X _ (imp_ok_pos X HX) Hmg) | ].
    apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam X))). apply zero_least.
  - intros a b Hab Ha. eapply ord_lt_le_trans; eauto.
  - intros z Hz Hf Hmz. apply (fix_principal N z _ HN Hlb Hz Hf).
    eapply ord_lt_le_trans; [ exact Htt | apply Hleast; auto ].
  - intros s Hs Hms.
    assert (Hp := nf_BN_proper N s HN Hs).
    set (w := normS (BN N s)).
    assert (Hw : BS_nf w) by (apply normS_nf; auto).
    assert (Ew : BS_denote w ≈ PHI N (BS_denote s)) by (apply normS_equal; auto).
    assert (Hvfix : bfix (addOrd 1) (BI_denote N) (PHI N (BS_denote s))).
    { apply bfix_value_full; auto using onePlus_normal, BI_good, BS_complete. apply Hinh_of; auto. }
    set (z := BS_denote w) in *.
    assert (Hzc : complete z) by apply BS_complete.
    assert (Hzfix : bfix (addOrd 1) (BI_denote N) z).
    { apply bfix_eq with (PHI N (BS_denote s)); auto using BI_good, BI_bfam. symmetry; auto. }
    assert (Hinf : oinf z) by exact (fix_onePlus_finite _ onePlus_normal z Hzc (proj1 Hzfix)).
    apply bfix_eq with z; auto using BI_good, BI_bfam.
    apply HJ; auto.
    + apply Kend_back; auto.
      * apply Hmv. eapply ord_lt_le_trans; [ exact Hms | apply Ew ].
      * apply Kend_of_value; auto. apply bphi_le_fix; auto using onePlus_normal, BI_good.
    + intros a Ha. apply (fix_principal N z a HN Hlb Hzc Hzfix Ha).
    + split; [ apply Hzfix | ]. intros T' HT' Hlt HK.
      assert (Hzlt := proj1 (nest z Hinf (S (BI_size T')) T' ltac:(lia) HT' HK) N HN Hlt).
      apply (zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good N) (BI_bfam N) Hzc Hzfix).
Qed.

Theorem JE_all : forall U X, ble (BI_denote X) U -> imp_ok X -> JX X /\ EX X.
Proof.
  intro U. induction U as [U IHU] using (well_founded_induction blt_wf).
  intros X HU HX.
  assert (IH : forall K, imp_ok K -> blt (BI_denote K) (BI_denote X) -> JX K /\ EX K).
  { intros K HK Hlt. apply (IHU (BI_denote K)); auto using ble_refl. eapply blt_le_trans; eauto. }
  assert (HJ : JX X).
  { intros w Hw HKX Hpr [Hf1 HCl].
    set (z := BS_denote w) in *.
    assert (Hzc : complete z) by apply BS_complete.
    assert (Hinf : oinf z) by exact (fix_onePlus_finite _ onePlus_normal z Hzc Hf1).
    destruct (coverX X HX (imp_ok_KHI X HX)) as [CS CF].
    assert (HIw := proj1 notation_KHI w Hw).
    split; [ exact Hf1 | split ].
    - intro a. destruct (CS a) as [K [HKo [HKK [HKl [Htr [Hlo [a' Hup]]]]]]].
      assert (HKz := Htr z Hinf HKX).
      assert (Hblt : blt (BI_denote K) (BI_denote X)) by (apply (bsub_child_blt _ _ (inl a')); auto).
      destruct (IH K HKo Hblt) as [_ HE].
      transitivity (PHI K z); [ apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam K))); exact Hlo | ].
      unfold z; rewrite (HE w Hw); fold z.
      assert (HN' := normX_nf K HKo). set (N' := normX K) in *.
      assert (HKN' : Klt z N') by (apply Klt_normX; auto).
      assert (HN'z : PHI N' z ≤ z) by (apply HCl; auto).
      transitivity (PHI N' z); [ | exact HN'z ].
      apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam N'))).
      unfold offX. assert (HA := absM_spec K HKo). destruct (absM K) as [m'|] eqn:Em'.
      + destruct HA as [Hm' [Hmg' _]].
        assert (Hlb' : lead_big N') by (apply absM_lead_big; auto; rewrite Em'; discriminate).
        destruct (BS_offset_correct N' HN' Hlb' m' Hm') as [_ [_ [Htt Hleast]]].
        assert (HfN' := bfix_of_fix _ onePlus_normal _ z (BI_good N') (BI_bfam N') Hzc HN'z).
        assert (Hmz : BS_denote m' < z) by (apply (Kge_lt _ _ K (Kgs_Kge _ _ Hmg') HKz)).
        apply Hpr. eapply ord_lt_le_trans; [ exact Htt | apply Hleast; auto ].
      + simpl BS_denote. apply addOrd_zero_l.
    - intro d. destruct (CF d w Hw HIw) as [K [HKo [HKK [HKl [Htr [Hlo [d' Hup]]]]]]].
      assert (HKz := Htr z Hinf HKX (ord_le_refl _)).
      assert (Hblt : blt (BI_denote K) (BI_denote X)) by (apply (bsub_child_blt _ _ (inr (d', z))); auto).
      destruct (IH K HKo Hblt) as [HJK _].
      assert (HfK : bfix (addOrd 1) (BI_denote K) z).
      { apply HJK; auto. split; [ exact Hf1 | ]. intros T' HT' Hlt HK.
        apply HCl; auto. eapply ilt_trans; eauto. }
      transitivity (PHI K 0); [ apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam K))); exact Hlo | ].
      apply bphi_le_fix; auto using onePlus_normal, BI_good. }
  split; [ exact HJ | apply EX_of_JX; auto ].
Qed.

(** Hereditary absorption: for an improper index X (normal exponents,
    positive normal coefficients), φ_X is φ_{normX X} shifted by offX X. *)
Theorem hereditary_absorption X : imp_ok X -> forall y, BS_nf y ->
  PHI X (BS_denote y) ≈ PHI (normX X) (BS_denote (offX X) + BS_denote y).
Proof. intro HX. apply (proj2 (JE_all (BI_denote X) X (ble_refl _) HX)). Qed.


(** ** Normalizing arbitrary notations

Every notation is accepted: index sums at any depth (including inside
exponents) may be improper, with terms in any order, repeated exponents
and zero coefficients; coefficients and arguments are normalized by
value.  Zero terms are dropped by @smartC@; the remaining improper index
is handled by @hereditary_absorption@. *)

Fixpoint normSX (x:BSmall) : BSmall :=
  match x with
  | BZ => BZ
  | BN T y => let X := normTX T in smartN (normX X) (BS_add (offX X) (normSX y))
  end
with normTX (T:BIdx) : BIdx :=
  match T with
  | BIZ => BIZ
  | BIC e c r => smartC (normTX e) (normSX c) (normTX r)
  end.

Lemma offX_nf X : imp_ok X -> BS_nf (offX X).
Proof.
  intro HX. unfold offX. destruct (absM X) as [m|] eqn:Em; [ | exact I ].
  assert (HA := absM_spec X HX). rewrite Em in HA. destruct HA as [Hm _].
  apply (BS_offset_correct (normX X) (normX_nf X HX)); auto.
  apply absM_lead_big; auto. rewrite Em; discriminate.
Qed.

Theorem normalizeX_correct :
  (forall x, BS_nf (normSX x) /\ BS_denote (normSX x) ≈ BS_denote x) /\
  (forall T, imp_ok (normTX T) /\ bequiv (BI_denote (normTX T)) (BI_denote T)).
Proof.
  apply BNotation_mut.
  - split; [ exact I | reflexivity ].
  - intros T [HX HXe] y [Hy' Hye].
    cbn [normSX]. set (X := normTX T) in *.
    assert (Ht := offX_nf X HX).
    destruct (BS_add_reflects _ (offX X) (conj (ord_eq_refl _) Ht) _ (normSX y) (conj (ord_eq_refl _) Hy'))
      as [Es Ns].
    destruct (smartN_correct (normX X) _ (normX_nf X HX) Ns) as [N1 N2].
    split; auto. rewrite N2.
    change (PHI (normX X) (BS_denote (BS_add (offX X) (normSX y))) ≈ PHI T (BS_denote y)).
    transitivity (PHI (normX X) (BS_denote (offX X) + BS_denote (normSX y))).
    { apply ord_eq_normal; [ apply BI_normal | symmetry; exact Es ]. }
    rewrite <- (hereditary_absorption X HX (normSX y) Hy').
    transitivity (PHI X (BS_denote y)); [ apply ord_eq_normal; [ apply BI_normal | exact Hye ] | ].
    apply bphi_bequiv; auto using onePlus_mono, BI_bfam.
  - split; [ exact I | apply bequiv_refl ].
  - intros e [He' Hee] c [Hc' Hce] r [Hr' Hre].
    cbn [normTX]. split.
    + destruct (normSX c) as [|Tc yc] eqn:Ec; [ exact Hr' | ].
      exact (conj He' (conj Hc' (conj (BS_pos Tc yc) Hr'))).
    + eapply bequiv_trans; [ apply smartC_bequiv | ].
      change (bequiv (badd (bmul (bexpΩ (BI_denote (normTX e))) (embed (BS_denote (normSX c)))) (BI_denote (normTX r)))
                     (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r))).
      apply bequiv_badd; auto.
      apply bequiv_bmul; [ apply bequiv_bexpΩ; auto | apply bequiv_embed; auto ].
Qed.

Corollary normSX_nf x : BS_nf (normSX x).
Proof. apply normalizeX_correct. Qed.

Corollary normSX_equal x : BS_denote (normSX x) ≈ BS_denote x.
Proof. apply normalizeX_correct. Qed.

(** Two notations denote the same ordinal iff they normalize to the same
    normal form (normal forms are unique). *)
Corollary normSX_complete x y : BS_denote x ≈ BS_denote y -> normSX x = normSX y.
Proof.
  intro H.
  assert (Hab : BS_denote (normSX x) ≈ BS_denote (normSX y)).
  { rewrite (normSX_equal x), (normSX_equal y). exact H. }
  set (n := S (BS_size (normSX x) + BS_size (normSX y))).
  assert (Hc := proj1 (cmp_correct n) (normSX x) (normSX y) ltac:(unfold n; lia) (normSX_nf x) (normSX_nf y)).
  apply (proj1 (cmp_eq n)); auto using normSX_nf; try (unfold n; lia).
  destruct (cmpS n (normSX x) (normSX y)); simpl in Hc; auto; exfalso.
  - apply (ord_lt_irreflexive (BS_denote (normSX x))). rewrite Hab at 2. exact Hc.
  - apply (ord_lt_irreflexive (BS_denote (normSX x))). rewrite Hab at 1. exact Hc.
Qed.

(** Examples (Γ₀ = φ_Ω(0)).  Γ₀ + Ω absorbs Γ₀ with offset 1, since
    Γ₀ = φ_Ω(0) is not above Γ₀: φ_{Γ₀+Ω}(0) = φ_Ω(1) = Γ₁. *)
Definition BS_Γ0 : BSmall := BN BI_Ω BZ.

Example normSX_Γ0_Ω : normSX (BN (BIC BIZ BS_Γ0 BI_Ω) BZ) = BN BI_Ω (BS_succ BZ).
Proof. vm_compute. reflexivity. Qed.

(** Hereditary: Γ₀ + Ω + Ω² at 0 is φ_{Ω²}(0) (both lower terms absorbed,
    offset 0 since Γ₀ < φ_{Ω²}(0)). *)
Example normSX_Γ0_Ω_Ω2 :
  normSX (BN (BIC BIZ BS_Γ0 (BIC BI_one BS_one (BIC (BIC BIZ (BS_succ BS_one) BIZ) BS_one BIZ))) BZ)
  = BN (BIC (BIC BIZ (BS_succ BS_one) BIZ) BS_one BIZ) BZ.
Proof. vm_compute. reflexivity. Qed.

(** Absorption inside an exponent: φ_{Ω^{Γ₀+Ω}}(0) = φ_{Ω^Ω}(0), the
    Large Veblen Ordinal (Γ₀ lies below it, so the offset is 0). *)
Example normSX_exp_absorb :
  normSX (BN (BIC (BIC BIZ BS_Γ0 BI_Ω) BS_one BIZ) BZ) = BN BI_ΩΩ BZ.
Proof. vm_compute. reflexivity. Qed.

(** Absorption below a merge: Ω + Γ₀ + Ω = Ω·2 as an index, offset 0. *)
Example normSX_Ω_Γ0_Ω :
  normSX (BN (BIC BI_one BS_one (BIC BIZ BS_Γ0 BI_Ω)) BZ) = BN (BIC BI_one (BS_succ BS_one) BIZ) BZ.
Proof. vm_compute. reflexivity. Qed.

(** ** All notations, proper or not, lie below BHO₁

Every term denotes the value of its normal form, so the full term
algebra has the same order type as the normal forms. *)

Theorem BS_bounded_all x : BS_denote x < BHO1.
Proof. rewrite <- (normSX_equal x). apply BS_bounded, normSX_nf. Qed.

Definition AllOrd : Ord := ord BSmall BS_denote.

Theorem BS_all_order_type : AllOrd ≈ BHO1.
Proof.
  split.
  - rewrite ord_le_unfold. intro x. apply BS_bounded_all.
  - rewrite <- BS_order_type. rewrite ord_le_unfold. intros [x Hx]. simpl.
    apply (index_lt AllOrd x).
Qed.

Corollary BS_all_order_type_BH : AllOrd ≈ BachmannHoward.
Proof. rewrite BS_all_order_type. apply BHO1_BachmannHoward. Qed.
