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
From Ordinal Require Import Notation.BachmannCantor.
From Ordinal Require Import Notation.BachmannBound.

Open Scope ord_scope.
Open Scope bool_scope.

(** Part of the notation system up to the Bachmann–Howard ordinal; see @BachmannNotation.v@ for an overview. *)

(** * Normalization by rewriting

Terms are required to be proper: indices are Ω-Cantor normal forms
(exponents strictly decreasing, coefficients positive), hereditarily.
As with @SchutteMatrix@'s properness, this is a precondition rather
than something to rewrite: with tree semantics, an index such as
Ω^0·c + Ω does not denote the same hierarchy as Ω, so absorption of
summands is not sound.  On proper terms there are two redexes, both
collapsing φ_T(y) to a proper subterm:

 - the argument is a fixpoint: φ_T(y) ≤ y, so φ_T(y) = y;
 - a coefficient k of T dominates: φ_T(y) ≤ k, so (by @dominance@)
   φ_T(y) = k.

Every reduction step strictly decreases size, so the system is
strongly normalizing, and its normal forms are exactly @BS_nf@. *)

(** ** Proper terms *)

Fixpoint BS_proper (x:BSmall) : Prop :=
  match x with
  | BZ => True
  | BN T y => BI_proper T /\ BS_proper y
  end
with BI_proper (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => BI_proper e /\ BS_proper c /\ 0 < BS_denote c /\ BI_proper r /\ lead_below r e
  end.

Lemma BI_proper_pos T : BI_proper T -> BI_pos T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; auto.
  intros [He [_ [Hc [Hr _]]]]. auto.
Qed.

Lemma nf_proper : (forall x, BS_nf x -> BS_proper x) /\ (forall T, BI_nf T -> BI_proper T).
Proof.
  apply BNotation_mut; simpl; auto.
  - intros T IHT y IHy [HT [Hy _]]. auto.
  - intros e IHe c IHc r IHr [He [Hc [Hc0 [Hr Hl]]]]. auto 10.
Qed.

(** Coefficient occurrences, at any depth. *)
Fixpoint Kin (k:BSmall) (T:BIdx) : Prop :=
  match T with
  | BIZ => False
  | BIC e c r => Kin k e \/ k = c \/ Kin k r
  end.

Lemma Kin_Kge k T : Kin k T -> Kge (BS_denote k) T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]]; [ left; auto | subst; right; left; reflexivity | right; right; auto ].
Qed.

Lemma Kin_proper k T : Kin k T -> BI_proper T -> BS_proper k.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [He [Hc [_ [Hr _]]]]; [ auto | subst; auto | auto ].
Qed.

Lemma Kin_size k T : Kin k T -> (BS_size k < BI_size T)%nat.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]]; [ specialize (IHe H) | subst | specialize (IHr H) ]; lia.
Qed.

(** ** The index equivalence *)

Lemma ieq_refl T : ieq T T.
Proof. induction T as [|e IHe c r IHr]; constructor; auto. reflexivity. Qed.

Lemma ieq_trans a b c : ieq a b -> ieq b c -> ieq a c.
Proof.
  intro H. revert c. induction H as [|e x r e' x' r' He IHe Hx Hr IHr]; intros c Hbc; inversion Hbc; subst; constructor; auto.
  transitivity (BS_denote x'); auto.
Qed.

Lemma ilt_ieq : forall a b, ilt a b -> forall a' b', ieq a a' -> ieq b b' -> ilt a' b'.
Proof.
  intros a b H. induction H as [e c r | e c r e' c' r' Hee IH | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr IH];
    intros a' b' Ha Hb.
  - inversion Ha; inversion Hb; subst. constructor.
  - inversion Ha as [|? ? ? e1 c1 r1 He1 Hc1 Hr1]; inversion Hb as [|? ? ? e2 c2 r2 He2 Hc2 Hr2]; subst.
    apply ilt_exp. apply IH; auto.
  - inversion Ha as [|? ? ? e1 c1 r1 He1 Hc1 Hr1]; inversion Hb as [|? ? ? e2 c2 r2 He2 Hc2 Hr2]; subst.
    apply ilt_coef.
    + apply ieq_trans with e; [ apply ieq_sym; exact He1 | apply ieq_trans with e'; auto ].
    + rewrite <- Hc1, <- Hc2. auto.
  - inversion Ha as [|? ? ? e1 c1 r1 He1 Hc1 Hr1]; inversion Hb as [|? ? ? e2 c2 r2 He2 Hc2 Hr2]; subst.
    apply ilt_tail.
    + apply ieq_trans with e; [ apply ieq_sym; exact He1 | apply ieq_trans with e'; auto ].
    + rewrite <- Hc1, <- Hc2. auto.
    + apply IH; auto.
Qed.

(** ** The rewrite relation *)

Inductive redex : BSmall -> BSmall -> Prop :=
| redex_arg : forall T y, BS_denote (BN T y) ≤ BS_denote y -> redex (BN T y) y
| redex_coef : forall T y k, Kin k T -> BS_denote (BN T y) ≤ BS_denote k -> redex (BN T y) k.

Inductive red_S : BSmall -> BSmall -> Prop :=
| red_top : forall x x', redex x x' -> red_S x x'
| red_idx : forall T T' y, red_I T T' -> red_S (BN T y) (BN T' y)
| red_arg : forall T y y', red_S y y' -> red_S (BN T y) (BN T y')
with red_I : BIdx -> BIdx -> Prop :=
| red_exp : forall e e' c r, red_I e e' -> red_I (BIC e c r) (BIC e' c r)
| red_coef : forall e c c' r, red_S c c' -> red_I (BIC e c r) (BIC e c' r)
| red_rest : forall e c r r', red_I r r' -> red_I (BIC e c r) (BIC e c r').

Scheme red_S_mut := Induction for red_S Sort Prop
with red_I_mut := Induction for red_I Sort Prop.
Combined Scheme red_mut from red_S_mut, red_I_mut.

Lemma redex_sound x x' : redex x x' -> BS_proper x -> BS_denote x ≈ BS_denote x'.
Proof.
  intros H Hx. destruct H as [T y H | T y k Hk H]; split; auto.
  - apply normal_inflationary; auto using BI_normal, BS_complete.
  - destruct Hx as [HT _]. apply dominance; auto using BI_proper_pos, Kin_Kge.
Qed.

Theorem red_sound :
  (forall x x', red_S x x' -> BS_proper x -> BS_denote x ≈ BS_denote x') /\
  (forall T T', red_I T T' -> BI_proper T -> ieq T T').
Proof.
  apply red_mut.
  - intros x x' H Hx. apply redex_sound; auto.
  - intros T T' y H IH [HT _]. apply bphi_ieq; auto.
  - intros T y y' H IH [_ Hy]. apply ord_eq_normal; auto using BI_normal.
  - intros e e' c r H IH [He _]. constructor; auto using ieq_refl. reflexivity.
  - intros e c c' r H IH [_ [Hc _]]. constructor; auto using ieq_refl.
  - intros e c r r' H IH [_ [_ [_ [Hr _]]]]. constructor; auto using ieq_refl. reflexivity.
Qed.

Lemma lead_below_ieq r r' e e' : ieq r r' -> ieq e e' -> lead_below r e -> lead_below r' e'.
Proof.
  intros Hr He. destruct Hr as [|e2 c2 r2 e2' c2' r2' He2 _ _]; simpl; auto.
  intro H. apply (ilt_ieq _ _ H); auto.
Qed.

Theorem red_proper :
  (forall x x', red_S x x' -> BS_proper x -> BS_proper x') /\
  (forall T T', red_I T T' -> BI_proper T -> BI_proper T').
Proof.
  apply red_mut.
  - intros x x' H Hx. destruct H as [T y H | T y k Hk H]; [ apply Hx | ].
    apply (Kin_proper k T); auto. apply Hx.
  - intros T T' y H IH [HT Hy]. split; auto.
  - intros T y y' H IH [HT Hy]. split; auto.
  - intros e e' c r H IH [He [Hc [Hc0 [Hr Hl]]]].
    assert (Hee := proj2 red_sound e e' H He).
    split; auto. split; auto. split; auto. split; auto.
    apply (lead_below_ieq r r e e'); auto using ieq_refl.
  - intros e c c' r H IH [He [Hc [Hc0 [Hr Hl]]]].
    assert (Hcc := proj1 red_sound c c' H Hc).
    split; auto. split; auto. split; [ rewrite <- Hcc; auto | auto ].
  - intros e c r r' H IH [He [Hc [Hc0 [Hr Hl]]]].
    assert (Hrr := proj2 red_sound r r' H Hr).
    split; auto. split; auto. split; auto. split; auto.
    apply (lead_below_ieq r r' e e); auto using ieq_refl.
Qed.

(** ** Strong normalization *)

Theorem red_size :
  (forall x x', red_S x x' -> (BS_size x' < BS_size x)%nat) /\
  (forall T T', red_I T T' -> (BI_size T' < BI_size T)%nat).
Proof.
  apply red_mut; simpl; intros; try lia.
  destruct r as [T y H | T y k Hk H]; simpl; [ lia | ].
  pose proof (Kin_size k T Hk). lia.
Qed.

Theorem strongly_normalizing : well_founded (fun y x => red_S x y).
Proof.
  apply (Wf_nat.well_founded_lt_compat _ BS_size).
  intros y x H. apply (proj1 red_size); auto.
Qed.

(** ** Deciding the argument redex *)

Lemma Klt_mono z z' T : z ≤ z' -> Klt z T -> Klt z' T.
Proof.
  intro Hz. induction T as [|e IHe c r IHr]; simpl; auto.
  intros [H1 [H2 H3]]. split; auto. split; auto. eapply ord_lt_le_trans; eauto.
Qed.

(** Bachmann's rule, needing only the indices to be normal. *)
Lemma nest_lt_idx T a T' b :
  BI_nf T -> BI_nf T' -> ilt T T' ->
  BS_denote a < BS_denote (BN T' b) -> Klt (BS_denote (BN T' b)) T ->
  BS_denote (BN T a) < BS_denote (BN T' b).
Proof.
  intros HT HT' Hlt Ha Hc.
  set (z := BS_denote (BN T' b)) in *.
  assert (Hne : T' <> BIZ) by (intro E; subst; inversion Hlt).
  assert (Hz : zlt z (BI_denote T) (BI_denote T')).
  { apply (proj1 (nest z (BN_inf T' b HT' Hne) (S (BI_size T)) T ltac:(lia) HT Hc)); auto. }
  assert (Hi : inhabited (bsmall (BI_denote T') + bbig (BI_denote T'))).
  { destruct T' as [|e' c' r']; [ tauto | ]. apply BI_inh. apply HT'. }
  assert (Hfix := zlt_value (addOrd 1) onePlus_normal (BI_denote T) (BI_denote T') (BS_denote b)
                    Hz (BI_good T') (BI_bfam T') Hi (BS_complete b)).
  eapply ord_lt_le_trans; [ | exact Hfix ].
  apply normal_increasing; auto using BI_normal.
  apply (BS_complete (BN T' b)).
Qed.

(** y is a fixpoint of φ_T iff y = φ_{T''}(y'') with T < T'' and every
    coefficient of T below y. *)
Definition fix_test (n:nat) (T:BIdx) (y:BSmall) : bool :=
  match y with
  | BZ => false
  | BN T'' _ => match cmpI n T T'' with LT => coefs_below n T y | _ => false end
  end.

Theorem fix_test_correct T y : BI_nf T -> BS_nf y ->
  let n := S (BI_size T + BS_size y) in
  (fix_test n T y = true -> BS_denote (BN T y) ≤ BS_denote y) /\
  (fix_test n T y = false -> BS_denote y < BS_denote (BN T y)).
Proof.
  intros HT Hy n.
  destruct y as [|T'' y'']; [ split; [ discriminate | intros _; apply (BS_pos T BZ) ] | ].
  change (fix_test n T (BN T'' y'')) with
    (match cmpI n T T'' with LT => coefs_below n T (BN T'' y'') | _ => false end).
  assert (Hy' := Hy). destruct Hy' as [HT'' [Hy'' [Hlt'' HK'']]].
  assert (HI := proj2 (cmp_correct n) T T'' ltac:(unfold n; simpl; lia) HT HT'').
  set (y := BN T'' y'') in *.
  assert (Hyinf : T'' <> BIZ -> oinf (BS_denote y)) by (intro; apply BN_inf; auto).
  destruct (cmpI n T T'') eqn:E; simpl in HI.
  - destruct (coefs_below_spec n y T (fun c Hc Hcn => proj1 (cmp_correct n) c y ltac:(unfold n; lia) Hcn Hy) HT)
      as [C1 C2].
    destruct (coefs_below n T y) eqn:E2; split; intro H; try discriminate.
    + (* a fixpoint *)
      assert (HK := C1 eq_refl).
      assert (Hne : T'' <> BIZ) by (intro Ez; subst; inversion HI).
      assert (Hz : zlt (BS_denote y) (BI_denote T) (BI_denote T'')).
      { apply (proj1 (nest _ (Hyinf Hne) (S (BI_size T)) T ltac:(lia) HT HK)); auto. }
      assert (Hi : inhabited (bsmall (BI_denote T'') + bbig (BI_denote T''))).
      { destruct T'' as [|e' c' r']; [ tauto | ]. apply BI_inh. apply HT''. }
      exact (zlt_value (addOrd 1) onePlus_normal (BI_denote T) (BI_denote T'') (BS_denote y'')
               Hz (BI_good T'') (BI_bfam T'') Hi (BS_complete y'')).
    + (* a coefficient at least y: y ≤ φ_T(0) < φ_T(y) *)
      apply ord_le_lt_trans with (BS_denote (BN T BZ)).
      * apply dominance; [ apply BI_nf_pos; auto | apply C2; reflexivity ].
      * apply (normal_increasing _ (BI_normal T) 0 (BS_denote y) (BS_complete y) (BS_pos T'' y'')).
  - split; intro H; try discriminate.
    change (BS_denote y < bphi (addOrd 1) (BI_denote T) (BS_denote y)).
    rewrite (bphi_ieq T T'' (BS_denote y) HI).
    apply normal_increasing; auto using BI_normal, BS_complete.
  - split; intro H; try discriminate.
    apply nest_lt_idx; auto.
    + eapply ord_lt_le_trans; [ exact Hlt'' | ].
      apply normal_inflationary; auto using BI_normal, BS_complete.
    + apply Klt_mono with (BS_denote y); auto.
      apply normal_inflationary; auto using BI_normal, BS_complete.
Qed.

(** ** The coefficient redex: collapse at the end position

φ_T(0) collapses to its largest coefficient m exactly when T lies
below the index of m and m occurs only at the end of T (the coefficient
of the last summand, or, when that coefficient is 1, the end of its
exponent).  For collapse, a non-strict variant of @nest@ makes ⟦T⟧
m-reachable from the index of m; otherwise a strict context below ⟦T⟧
carries m (@Kgs_ctx@). *)

(** Every coefficient is below z, except an end occurrence, which is at most z. *)
Fixpoint Kend (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r =>
      match r with
      | BIZ => (Klt z e /\ BS_denote c ≤ z) \/ (Kend z e /\ BS_denote c ≈ 1)
      | _ => Klt z e /\ BS_denote c < z /\ Kend z r
      end
  end.

Lemma Klt_ieq z T T' : ieq T T' -> Klt z T' -> Klt z T.
Proof.
  intro H. induction H as [|e c r e' c' r' He IHe Hc Hr IHr]; simpl; auto.
  intros [H1 [H2 H3]]. split; auto. split; auto. rewrite Hc; auto.
Qed.

Lemma bleZ_bsub_l z x' x y : bsub x' x -> bleZ z x y -> bleZ z x' y.
Proof. intros H1 H2. eapply bleZ_trans; [ apply LZ_sub, H1 | exact H2 ]. Qed.

Lemma bsub_badd_zero x : bsub (badd x bzero) x.
Proof. apply bequiv_badd_zero_r. Qed.

Lemma BI_denote_cons e c r :
  BI_denote (BIC e c r) = badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r).
Proof. reflexivity. Qed.

(** The target's coefficients only need to satisfy @Kend@. *)
Lemma Klt_Kend z T : Klt z T -> Kend z T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; auto.
  intros [He [Hc Hr]]. destruct r as [|e2 c2 r2].
  - left. split; auto. apply ord_lt_le; auto.
  - split; auto.
Qed.

Lemma Kend_exp z e c r : oinf z -> Kend z (BIC e c r) -> Kend z e.
Proof.
  intros Hz H. destruct r as [|e2 c2 r2]; simpl in H.
  - destruct H as [[H _]|[H _]]; auto. apply Klt_Kend; auto.
  - apply Klt_Kend, H.
Qed.

Lemma Kend_coef z e' c' r' c : Kend z (BIC e' c' r') -> BS_denote c < BS_denote c' -> 0 < BS_denote c ->
  Klt z e' /\ BS_denote c < z.
Proof.
  intros H Hcc Hc0. destruct r' as [|e2 c2 r2]; simpl in H.
  - destruct H as [[H1 H2]|[H1 H2]].
    + split; auto. eapply ord_lt_le_trans; eauto.
    + exfalso. assert (H1' : BS_denote c < 1) by (eapply ord_lt_le_trans; [ exact Hcc | apply H2 ]).
      rewrite ord_lt_unfold in H1'. destruct H1' as [u Hle].
      apply (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ exact Hc0 | exact Hle ].
  - destruct H as [H1 [H2 _]]. split; auto. eapply ord_lt_trans; eauto.
Qed.

Lemma Kend_tail z e' c' r' : r' <> BIZ -> Kend z (BIC e' c' r') -> Kend z r'.
Proof. intros Hne H. destruct r' as [|e2 c2 r2]; [ tauto | ]. apply H. Qed.

Theorem nest_le z : oinf z -> forall n T, (BI_size T < n)%nat -> BI_nf T -> Kend z T ->
  (forall T', BI_nf T' -> Kend z T' -> ilt T T' -> bleZ z (BI_denote T) (BI_denote T')) /\
  (forall a, match T with
             | BIZ => True
             | BIC e _ _ => (Klt z e -> zlt z (BI_denote e) a) /\ (Kend z e -> bleZ z (BI_denote e) a)
             end -> bleZ z (BI_denote T) (bexpΩ a)).
Proof.
  intros Hz n. induction n as [|n IH]; intros T Hsz HT HK; [ lia | ].
  (* the reduction of a tail to its exponent *)
  assert (Tail : forall e r, (BI_size r < n)%nat -> BI_nf r -> Kend z r -> lead_below r e ->
                 BI_nf e -> Klt z e -> (BI_size e < n)%nat ->
                 bleZ z (BI_denote r) (bexpΩ (BI_denote e))).
  { intros e r Hr Hrn HrK Hl He HeK Hes.
    apply (proj2 (IH r Hr Hrn HrK)).
    destruct r as [|e2 c2 r2]; auto.
    simpl in Hl. destruct Hrn as [He2 _]. simpl in Hr.
    split.
    - intro HK2. apply (proj1 (nest z Hz (S (BI_size e2)) e2 ltac:(lia) He2 HK2)); auto.
    - intro HK2. apply (proj1 (IH e2 ltac:(lia) He2 HK2)); auto. apply Klt_Kend; auto. }
  assert (B : forall a, match T with
                        | BIZ => True
                        | BIC e _ _ => (Klt z e -> zlt z (BI_denote e) a) /\ (Kend z e -> bleZ z (BI_denote e) a)
                        end -> bleZ z (BI_denote T) (bexpΩ a)).
  { intros a Ha. destruct T as [|e c r].
    - apply LZ_sub, bsub_bzero_l.
    - destruct Ha as [Ha1 Ha2]. simpl in Hsz.
      destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
      destruct r as [|e2 c2 r2].
      + simpl in HK. destruct HK as [[HKe Hcz]|[HKe Hc1]].
        * apply bleZ_bsub_l with (bmul (bexpΩ (BI_denote e)) (embed z)); [ | apply zlt_exp; auto ].
          eapply bsub_trans; [ apply bsub_badd_zero | ]. apply bsub_bmul_r, bsub_embed; auto.
        * apply bleZ_bsub_l with (bexpΩ (BI_denote e)); [ | apply bleZ_exp; auto ].
          eapply bsub_trans; [ apply bsub_badd_zero | ].
          eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, (proj1 Hc1) | apply bsub_bmul_one ].
      + simpl in HK. destruct HK as [HKe [Hcz HKr]].
        assert (Hrb := Tail e (BIC e2 c2 r2) ltac:(simpl in *; lia) Hr HKr Hl He HKe ltac:(lia)).
        apply bleZ_trans with (bmul (bexpΩ (BI_denote e)) (embed z)); [ | apply zlt_exp; auto ].
        rewrite BI_denote_cons. eapply bleZ_mono_r; [ apply bleZ_shift, Hrb | ].
        eapply bsub_trans; [ apply bsub_mul_succ | apply bsub_bmul_r, bsub_embed, succ_least; auto ]. }
  split; auto.
  intros T' HT' HKT' Hlt.
  destruct Hlt as [e' c' r' | e c r e' c' r' Hee | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr].
  - apply LZ_sub, bsub_bzero_l.
  - simpl in Hsz. assert (HKe' := Kend_exp _ _ _ _ Hz HKT'). destruct HT' as [He' [_ [Hc0' _]]].
    assert (HTe := proj1 HT).
    eapply bleZ_mono_r; [ apply (B (BI_denote e')) | ].
    + split.
      * intro HKe. apply (proj1 (nest z Hz (S (BI_size e)) e ltac:(lia) HTe HKe)); auto.
      * intro HKe. apply (proj1 (IH e ltac:(lia) HTe HKe)); auto.
    + rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_P_Pz, Hc0' | apply bsub_le_badd ].
  - simpl in Hsz. destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
    destruct (Kend_coef _ _ _ _ _ HKT' Hcc Hc0) as [HKe' Hcz].
    assert (HKe := Klt_ieq z e e' Hee HKe').
    assert (Hsub : bsub (bmul (bexpΩ (BI_denote e)) (embed (succOrd (BS_denote c))))
                        (BI_denote (BIC e' c' r'))).
    { rewrite BI_denote_cons. eapply bsub_trans; [ | apply bsub_le_badd ].
      eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, succ_least, Hcc | ].
      apply bsub_bmul_l, bsub_bexpΩ, (ieq_bequiv _ _ Hee). }
    destruct r as [|e2 c2 r2].
    + apply LZ_sub. eapply bsub_trans; [ | exact Hsub ].
      rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_badd_zero | ].
      apply bsub_bmul_r, bsub_embed, ord_lt_le, succ_lt.
    + simpl in HK. destruct HK as [_ [_ HKr]].
      assert (Hrb := Tail e (BIC e2 c2 r2) ltac:(simpl in *; lia) Hr HKr Hl He HKe ltac:(lia)).
      rewrite BI_denote_cons. eapply bleZ_mono_r; [ apply bleZ_shift, Hrb | ].
      eapply bsub_trans; [ apply bsub_mul_succ | exact Hsub ].
  - simpl in Hsz. destruct HT as [He [Hc [Hc0 [Hr Hl]]]]. destruct HT' as [_ [_ [_ [Hr' _]]]].
    assert (Hne' : r' <> BIZ) by (intro E; subst r'; inversion Hrr).
    assert (HKr' := Kend_tail _ _ _ _ Hne' HKT').
    assert (Hterm : bsub (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
                         (bmul (bexpΩ (BI_denote e')) (embed (BS_denote c')))).
    { eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, (proj1 Hcc) | ].
      apply bsub_bmul_l, bsub_bexpΩ, (ieq_bequiv _ _ Hee). }
    destruct r as [|e2 c2 r2].
    + apply LZ_sub. rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_badd_zero | ].
      eapply bsub_trans; [ exact Hterm | apply bsub_le_badd ].
    + simpl in HK. destruct HK as [_ [_ HKr]].
      rewrite BI_denote_cons.
      apply (bleZ_mono_r z _ (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r'))).
      * apply bleZ_shift. apply (proj1 (IH (BIC e2 c2 r2) ltac:(simpl in *; lia) Hr HKr)); auto.
      * exact (bsub_badd_l _ _ Hterm (BI_denote r')).
Qed.

(** A coefficient at least z at a position that is not the end. *)
Fixpoint Kgs (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => False
  | BIC e c r =>
      match r with
      | BIZ => (Kge z e /\ 1 < BS_denote c) \/ (BS_denote c ≈ 1 /\ Kgs z e)
      | _ => Kge z e \/ z ≤ BS_denote c \/ Kgs z r
      end
  end.

Lemma bslt_P_Pc P c : bpos P -> 1 < c -> bslt P (bmul P (embed c)).
Proof.
  intros HP Hc. destruct c as [C k].
  rewrite ord_lt_unfold in Hc. destruct Hc as [j Hj].
  assert (Hj0 : 0 < k j) by (apply ord_lt_le_trans with 1; [ apply succ_lt | exact Hj ]).
  apply bslt_bsub_l with (bmul P (embed (k j))); [ apply bsub_P_Pz; auto | ].
  apply bslt_bsub_r with (badd (bmul P (embed (k j))) P); [ | apply (bsub_bmul_step P (embed (ord C k)) j) ].
  apply (bslt_badd_pos _ bzero); auto.
Qed.

Lemma Kgs_ctx : forall T, BI_pos T -> forall z, Kgs z T ->
  exists C ζ, bctx C /\ complete ζ /\ z ≤ ζ /\ bslt (C ζ) (BI_denote T).
Proof.
  induction T as [|e IHe c r IHr]; [ simpl; tauto | ].
  intros [He [Hc0 Hr]] z HK.
  assert (Hterm : bcd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))) by apply idx_term_bcd.
  destruct r as [|e2 c2 r2].
  - destruct HK as [[HKe Hc1]|[Hc1 HKe]].
    + destruct (Kge_ctx e He z HKe) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
      exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
      apply bslt_bsub_l with (bexpΩ (BI_denote e)); [ apply bsub_bexpΩ; auto | ].
      rewrite BI_denote_cons. apply bslt_bsub_r with (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))).
      * apply bslt_P_Pc; auto. apply bpos_bexpΩ.
      * apply bsub_le_badd.
    + destruct (IHe He z HKe) as [C [ζ [HC [Hζ [Hzζ Hlt]]]]].
      exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
      apply bslt_bsub_r with (bexpΩ (BI_denote e)); [ apply bslt_bexpΩ; auto | ].
      rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_P_Pz, Hc0 | apply bsub_le_badd ].
  - assert (Hrpos : bpos (BI_denote (BIC e2 c2 r2))) by (apply lead_pos; apply Hr).
    assert (Htail : forall X, bsub X (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) ->
                              bslt X (BI_denote (BIC e c (BIC e2 c2 r2)))).
    { intros X HX. rewrite BI_denote_cons.
      apply bslt_bsub_l with (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))); auto.
      apply (bslt_badd_pos _ bzero); auto. }
    destruct HK as [HKe|[Hzc|HKr]].
    + destruct (Kge_ctx e He z HKe) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
      exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
      apply Htail. eapply bsub_trans; [ apply bsub_bexpΩ, Hsub | apply bsub_P_Pz, Hc0 ].
    + exists (fun ξ => bmul (bexpΩ (BI_denote e)) (embed ξ)), (BS_denote c).
      split; [ apply bctx_mul; [ apply bcd_bexpΩ, BI_ok | apply bpos_bexpΩ | apply bctx_embed ] | ].
      split; [ apply BS_complete | split; [ auto | apply Htail, bsub_refl ] ].
    + destruct (IHr Hr z HKr) as [C [ζ [HC [Hζ [Hzζ Hlt]]]]].
      exists (fun ξ => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (C ξ)), ζ.
      split; [ apply bctx_add; auto | split; [ auto | split; [ auto | ] ] ].
      rewrite BI_denote_cons. apply bslt_badd_r; auto.
Qed.

(** All coefficients, at any depth, are at most z. *)
Fixpoint Kle (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => Kle z e /\ BS_denote c ≤ z /\ Kle z r
  end.

Lemma Kle_lt z w T : Kle z T -> z < w -> Klt w T.
Proof.
  intros H Hz. induction T as [|e IHe c r IHr]; simpl in *; auto.
  destruct H as [H1 [H2 H3]]. split; auto. split; auto. eapply ord_le_lt_trans; eauto.
Qed.

Lemma Kge_ieq z T T' : ieq T T' -> Kge z T -> Kge z T'.
Proof.
  intro H. induction H as [|e c r e' c' r' He IHe Hc Hr IHr]; simpl; auto.
  intros [H1|[H1|H1]]; auto. right; left. rewrite <- Hc; auto.
Qed.

Lemma Kin_nf k T : Kin k T -> BI_nf T -> BS_nf k.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [He [Hc [_ [Hr _]]]]; [ auto | subst; auto | auto ].
Qed.

Lemma Kin_size' k T : Kin k T -> (BS_size k <= BI_size T)%nat.
Proof. intro H. pose proof (Kin_size k T H). lia. Qed.

(** *** The largest coefficient *)

Definition omax (n:nat) (a b:option BSmall) : option BSmall :=
  match a, b with
  | None, x => x
  | x, None => x
  | Some u, Some v => if isLT (cmpS n u v) then Some v else Some u
  end.

Fixpoint kmax (n:nat) (T:BIdx) : option BSmall :=
  match T with
  | BIZ => None
  | BIC e c r => omax n (omax n (kmax n e) (Some c)) (kmax n r)
  end.

Definition kmax_ok (T:BIdx) (o:option BSmall) : Prop :=
  match o with
  | None => T = BIZ
  | Some m => Kin m T /\ Kle (BS_denote m) T
  end.

Lemma Kle_mono z z' T : z ≤ z' -> Kle z T -> Kle z' T.
Proof.
  intro Hz. induction T as [|e IHe c r IHr]; simpl; auto.
  intros [H1 [H2 H3]]. split; auto. split; auto. transitivity z; auto.
Qed.

(** The max of two coefficient candidates. *)
Lemma omax_spec n a b (P:BSmall -> Prop) :
  (forall u v, P u -> P v -> ordering_correct (cmpS n u v) (BS_denote u) (BS_denote v)) ->
  match a with None => True | Some u => P u end -> match b with None => True | Some v => P v end ->
  match omax n a b with
  | None => a = None /\ b = None
  | Some w => P w /\ (w = match a with Some u => u | None => w end \/ w = match b with Some v => v | None => w end) /\
              match a with None => True | Some u => BS_denote u ≤ BS_denote w end /\
              match b with None => True | Some v => BS_denote v ≤ BS_denote w end
  end.
Proof.
  intros Hc Ha Hb.
  destruct a as [u|]; destruct b as [v|]; simpl; auto.
  - destruct (isLT_spec _ _ _ (Hc u v Ha Hb)) as [S1 S2].
    destruct (isLT (cmpS n u v)) eqn:E.
    + split; auto. split; [ right; auto | split; [ apply ord_lt_le; auto | reflexivity ] ].
    + split; auto. split; [ left; auto | split; [ reflexivity | auto ] ].
  - split; auto. split; [ left; auto | split; reflexivity ].
  - split; auto. split; [ right; auto | split; reflexivity ].
Qed.

Lemma kmax_spec n : forall T, BI_nf T -> (BI_size T + BI_size T < n)%nat -> kmax_ok T (kmax n T).
Proof.
  induction T as [|e IHe c r IHr]; intros HT Hsz; simpl; auto.
  simpl in Hsz. destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
  set (P := fun u => BS_nf u /\ (BS_size u <= BI_size (BIC e c r))%nat /\ Kin u (BIC e c r)).
  assert (HP : forall u v, P u -> P v -> ordering_correct (cmpS n u v) (BS_denote u) (BS_denote v)).
  { intros u v [Hu [Hsu _]] [Hv [Hsv _]]. apply (proj1 (cmp_correct n)); auto. simpl in Hsu, Hsv. lia. }
  assert (He' := IHe He ltac:(lia)). assert (Hr' := IHr Hr ltac:(lia)).
  assert (Pe : match kmax n e with None => True | Some u => P u end).
  { destruct (kmax n e) as [u|]; auto. destruct He' as [Hin Hle].
    split; [ apply (Kin_nf u e); auto | split; [ pose proof (Kin_size' u e Hin); simpl; lia | simpl; auto ] ]. }
  assert (Pc : P c).
  { split; auto. split; [ simpl; lia | simpl; auto ]. }
  assert (Pr : match kmax n r with None => True | Some u => P u end).
  { destruct (kmax n r) as [u|]; auto. destruct Hr' as [Hin Hle].
    split; [ apply (Kin_nf u r); auto | split; [ pose proof (Kin_size' u r Hin); simpl; lia | simpl; auto ] ]. }
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

(** *** The end test *)

(** c ≤ 1, for a positive normal coefficient: c = 1. *)
Definition le_one (n:nat) (c:BSmall) : bool :=
  match cmpS n c BS_one with GT => false | _ => true end.

Fixpoint end_test (n:nat) (m:BSmall) (T:BIdx) : bool :=
  match T with
  | BIZ => true
  | BIC e c r =>
      match r with
      | BIZ => coefs_below n e m || (le_one n c && end_test n m e)
      | _ => coefs_below n e m && isLT (cmpS n c m) && end_test n m r
      end
  end.

Lemma BS_one_nf : BS_nf BS_one.
Proof.
  split; [ exact I | split; [ exact I | split; [ apply BS_pos | exact I ] ] ].
Qed.

Lemma BS_one_denote : BS_denote BS_one ≈ 1.
Proof.
  unfold BS_one. rewrite BS_denote_onePlus. rewrite addOrd_zero_r. reflexivity.
Qed.

Lemma le_one_spec n c : BS_nf c -> 0 < BS_denote c -> (BS_size c + 3 < n)%nat ->
  (le_one n c = true -> BS_denote c ≈ 1) /\ (le_one n c = false -> 1 < BS_denote c).
Proof.
  intros Hc Hc0 Hsz.
  assert (H := proj1 (cmp_correct n) c BS_one ltac:(simpl; lia) Hc BS_one_nf).
  unfold le_one. destruct (cmpS n c BS_one); simpl in H; split; intro E; try discriminate.
  - split; [ rewrite <- BS_one_denote; apply ord_lt_le; auto | ].
    apply succ_least; auto.
  - rewrite H. apply BS_one_denote.
  - rewrite <- BS_one_denote. auto.
Qed.

Lemma end_test_spec n m : BS_nf m -> forall T, BI_nf T -> Kle (BS_denote m) T ->
  (BI_size T + BS_size m + 3 < n)%nat ->
  (end_test n m T = true -> Kend (BS_denote m) T) /\ (end_test n m T = false -> Kgs (BS_denote m) T).
Proof.
  intros Hm. induction T as [|e IHe c r IHr]; intros HT HK Hsz; [ simpl; split; auto; discriminate | ].
  simpl in Hsz. assert (HT' := HT). destruct HT' as [He [Hc [Hc0 [Hr Hl]]]].
  destruct HK as [HKe [HKc HKr]].
  destruct (IHe He HKe ltac:(lia)) as [E1 E2].
  destruct (coefs_below_spec n m e
              (fun c0 H0 Hc0' => proj1 (cmp_correct n) c0 m ltac:(lia) Hc0' Hm) He) as [C1 C2].
  destruct (isLT_spec _ _ _ (proj1 (cmp_correct n) c m ltac:(lia) Hc Hm)) as [L1 L2].
  destruct (le_one_spec n c Hc Hc0 ltac:(lia)) as [O1 O2].
  destruct r as [|e2 c2 r2].
  - change ((coefs_below n e m || (le_one n c && end_test n m e) = true ->
             (Klt (BS_denote m) e /\ BS_denote c ≤ BS_denote m) \/
             (Kend (BS_denote m) e /\ BS_denote c ≈ 1)) /\
            (coefs_below n e m || (le_one n c && end_test n m e) = false ->
             (Kge (BS_denote m) e /\ 1 < BS_denote c) \/ (BS_denote c ≈ 1 /\ Kgs (BS_denote m) e))).
    destruct (coefs_below n e m); destruct (le_one n c); destruct (end_test n m e); simpl;
      split; intro H; try discriminate; intuition.
  - destruct (IHr Hr HKr ltac:(simpl in *; lia)) as [R1 R2].
    change ((coefs_below n e m && isLT (cmpS n c m) && end_test n m (BIC e2 c2 r2) = true ->
             Klt (BS_denote m) e /\ BS_denote c < BS_denote m /\ Kend (BS_denote m) (BIC e2 c2 r2)) /\
            (coefs_below n e m && isLT (cmpS n c m) && end_test n m (BIC e2 c2 r2) = false ->
             Kge (BS_denote m) e \/ BS_denote m ≤ BS_denote c \/ Kgs (BS_denote m) (BIC e2 c2 r2))).
    destruct (coefs_below n e m); destruct (isLT (cmpS n c m)); destruct (end_test n m (BIC e2 c2 r2)); simpl;
      split; intro H; try discriminate; intuition.
Qed.

(** *** Deciding the coefficient redex *)

Definition coll_test (n:nat) (T:BIdx) : option BSmall :=
  match kmax n T with
  | None => None
  | Some m =>
      match m with
      | BZ => None
      | BN Tm _ =>
          match cmpI n T Tm with
          | LT => if end_test n m T then Some m else None
          | _ => None
          end
      end
  end.

Theorem coll_test_correct T : BI_nf T ->
  let n := S (4 * BI_size T + 4) in
  (forall m, coll_test n T = Some m -> Kin m T /\ BS_denote (BN T BZ) ≤ BS_denote m) /\
  (coll_test n T = None -> Klt (BS_denote (BN T BZ)) T).
Proof.
  intros HT n.
  assert (HK := kmax_spec n T HT ltac:(unfold n; lia)).
  unfold coll_test.
  destruct (kmax n T) as [m|] eqn:Ek; [ | simpl in HK; subst; split; [ discriminate | intros _; exact I ] ].
  destruct HK as [Hin Hle].
  assert (Hm : BS_nf m) by (apply (Kin_nf m T); auto).
  assert (Hms := Kin_size m T Hin).
  assert (Hdom : BS_denote m ≤ BS_denote (BN T BZ)) by (apply dominance; auto using BI_nf_pos, Kin_Kge).
  destruct m as [|Tm ym].
  - split; [ discriminate | intros _ ].
    apply Kle_lt with (BS_denote BZ); auto. apply BS_pos.
  - assert (Hm' := Hm). destruct Hm' as [HTm [Hym [Hymlt HKm]]].
    simpl in Hms.
    assert (HI := proj2 (cmp_correct n) T Tm ltac:(unfold n; lia) HT HTm).
    (* m below the value suffices for the coefficient condition *)
    assert (Hlt_ok : BS_denote (BN Tm ym) < BS_denote (BN T BZ) -> Klt (BS_denote (BN T BZ)) T).
    { intro H. apply Kle_lt with (BS_denote (BN Tm ym)); auto. }
    destruct (cmpI n T Tm) eqn:EI; simpl in HI.
    + destruct (end_test_spec n (BN Tm ym) Hm T HT Hle ltac:(unfold n; simpl; lia)) as [N1 N2].
      destruct (end_test n (BN Tm ym) T) eqn:Ee.
      * split; [ | discriminate ].
        intros m' Em'. injection Em' as <-. split; auto.
        assert (Hne : Tm <> BIZ) by (intro E; subst; inversion HI).
        assert (Hz := BN_inf Tm ym HTm Hne).
        assert (HB := proj1 (nest_le _ Hz (S (BI_size T)) T ltac:(lia) HT (N1 eq_refl)) Tm HTm (Klt_Kend _ _ HKm) HI).
        assert (Hi : inhabited (bsmall (BI_denote Tm) + bbig (BI_denote Tm))).
        { destruct Tm as [|e' c' r']; [ tauto | ]. apply BI_inh. apply HTm. }
        exact (bleZ_sound (addOrd 1) onePlus_normal _ _ _ HB (BI_denote Tm) (bsub_refl _) (BI_good Tm)
                 (BI_bfam Tm) (BS_complete (BN Tm ym))
                 (bfix_value_full (addOrd 1) onePlus_normal _ _ (BI_good Tm) Hi (BS_complete ym))).
      * split; [ discriminate | intros _ ].
        apply Hlt_ok.
        destruct (Kgs_ctx T (BI_nf_pos T HT) _ (N2 eq_refl)) as [C [ζ [HC [Hζ [Hmζ Hlt]]]]].
        apply ord_le_lt_trans with (bphi (addOrd 1) (C ζ) 0).
        -- transitivity ζ; auto. apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ).
        -- apply (bphi_strict (addOrd 1) onePlus_normal); auto using BI_good, BI_bfam.
    + split; [ discriminate | intros _ ].
      exfalso. apply (ord_lt_irreflexive (BS_denote (BN Tm ym))).
      apply (Kge_lt _ _ Tm); auto.
      apply (Kge_ieq _ T); auto. apply Kin_Kge; auto.
    + split; [ discriminate | intros _ ].
      apply Hlt_ok. apply nest_lt_idx; auto.
      * eapply ord_lt_le_trans; [ exact Hymlt | exact Hdom ].
      * apply Klt_mono with (BS_denote (BN Tm ym)); auto.
Qed.

(** ** The normalizer *)

Definition smartN (T:BIdx) (y:BSmall) : BSmall :=
  if fix_test (S (BI_size T + BS_size y)) T y then y
  else match y with
       | BZ => match coll_test (S (4 * BI_size T + 4)) T with
               | Some m => m
               | None => BN T BZ
               end
       | _ => BN T y
       end.

Fixpoint normS (x:BSmall) : BSmall :=
  match x with
  | BZ => BZ
  | BN T y => smartN (normI T) (normS y)
  end
with normI (T:BIdx) : BIdx :=
  match T with
  | BIZ => BIZ
  | BIC e c r => BIC (normI e) (normS c) (normI r)
  end.

(** Coefficients of T lie below φ_T(y) once y is positive. *)
Lemma Klt_of_Kge w T : (forall z, Kge z T -> z < w) -> Klt w T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; intro H; auto.
  split; [ apply IHe; auto | split; [ apply H; right; left; reflexivity | apply IHr; auto ] ].
Qed.

Lemma Klt_pos_arg T y : BI_nf T -> 0 < BS_denote y -> Klt (BS_denote (BN T y)) T.
Proof.
  intros HT Hy. apply Klt_of_Kge. intros z Hz.
  apply ord_le_lt_trans with (BS_denote (BN T BZ)).
  - apply dominance; auto using BI_nf_pos.
  - apply (normal_increasing _ (BI_normal T) 0 (BS_denote y) (BS_complete y) Hy).
Qed.

Lemma smartN_correct T y : BI_nf T -> BS_nf y ->
  BS_nf (smartN T y) /\ BS_denote (smartN T y) ≈ BS_denote (BN T y).
Proof.
  intros HT Hy. unfold smartN.
  destruct (fix_test_correct T y HT Hy) as [F1 F2].
  destruct (fix_test (S (BI_size T + BS_size y)) T y) eqn:Ef.
  - split; auto. split; [ apply normal_inflationary; auto using BI_normal, BS_complete | apply F1; auto ].
  - assert (Hlt := F2 eq_refl).
    destruct y as [|Ty yy].
    + destruct (coll_test_correct T HT) as [C1 C2].
      destruct (coll_test (S (4 * BI_size T + 4)) T) as [m|] eqn:Ec.
      * destruct (C1 m eq_refl) as [Hin Hle].
        split; [ apply (Kin_nf m T); auto | ].
        split; [ apply dominance; auto using BI_nf_pos, Kin_Kge | auto ].
      * split; [ | reflexivity ].
        exact (conj HT (conj I (conj (BS_pos T BZ) (C2 eq_refl)))).
    + split; [ | reflexivity ].
      exact (conj HT (conj Hy (conj Hlt (Klt_pos_arg T (BN Ty yy) HT (BS_pos Ty yy))))).

Qed.

Theorem normalize_correct :
  (forall x, BS_proper x -> BS_nf (normS x) /\ BS_denote (normS x) ≈ BS_denote x) /\
  (forall T, BI_proper T -> BI_nf (normI T) /\ ieq (normI T) T).
Proof.
  apply BNotation_mut.
  - intros _. split; [ exact I | reflexivity ].
  - intros T IHT y IHy [HT Hy].
    destruct (IHT HT) as [HT' HTe]. destruct (IHy Hy) as [Hy' Hye].
    destruct (smartN_correct _ _ HT' Hy') as [N1 N2].
    split; auto. simpl. rewrite N2. simpl.
    rewrite (bphi_ieq _ _ _ HTe). apply ord_eq_normal; auto using BI_normal.
  - intros _. split; [ exact I | constructor ].
  - intros e IHe c IHc r IHr [He [Hc [Hc0 [Hr Hl]]]].
    destruct (IHe He) as [He' Hee]. destruct (IHc Hc) as [Hc' Hce]. destruct (IHr Hr) as [Hr' Hre].
    split; [ | constructor; auto ].
    simpl. split; auto. split; auto. split; [ rewrite Hce; auto | split; auto ].
    apply (lead_below_ieq r (normI r) e (normI e)); auto using ieq_sym.
Qed.

Corollary normS_nf x : BS_proper x -> BS_nf (normS x).
Proof. apply normalize_correct. Qed.

Corollary normS_equal x : BS_proper x -> BS_denote (normS x) ≈ BS_denote x.
Proof. apply normalize_correct. Qed.

(** ** Reduction to the normal form *)

From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.

Definition reds := clos_refl_trans BSmall red_S.
Definition redsI := clos_refl_trans BIdx red_I.

Lemma reds_trans x y z : reds x y -> reds y z -> reds x z.
Proof. intros; eapply rt_trans; eauto. Qed.

Lemma reds_BN_idx T T' y : redsI T T' -> reds (BN T y) (BN T' y).
Proof.
  intro H. induction H; [ apply rt_step, red_idx; auto | apply rt_refl | eapply rt_trans; eauto ].
Qed.

Lemma reds_BN_arg T y y' : reds y y' -> reds (BN T y) (BN T y').
Proof.
  intro H. induction H; [ apply rt_step, red_arg; auto | apply rt_refl | eapply rt_trans; eauto ].
Qed.

Lemma redsI_exp e e' c r : redsI e e' -> redsI (BIC e c r) (BIC e' c r).
Proof. intro H. induction H; [ apply rt_step, red_exp; auto | apply rt_refl | eapply rt_trans; eauto ]. Qed.

Lemma redsI_coef e c c' r : reds c c' -> redsI (BIC e c r) (BIC e c' r).
Proof. intro H. induction H; [ apply rt_step, red_coef; auto | apply rt_refl | eapply rt_trans; eauto ]. Qed.

Lemma redsI_rest e c r r' : redsI r r' -> redsI (BIC e c r) (BIC e c r').
Proof. intro H. induction H; [ apply rt_step, red_rest; auto | apply rt_refl | eapply rt_trans; eauto ]. Qed.

Lemma smartN_reds T y : BI_nf T -> BS_nf y -> reds (BN T y) (smartN T y).
Proof.
  intros HT Hy. unfold smartN.
  destruct (fix_test_correct T y HT Hy) as [F1 _].
  destruct (fix_test (S (BI_size T + BS_size y)) T y) eqn:Ef.
  - apply rt_step, red_top, redex_arg, F1; auto.
  - destruct y as [|Ty yy]; [ | apply rt_refl ].
    destruct (coll_test_correct T HT) as [C1 _].
    destruct (coll_test (S (4 * BI_size T + 4)) T) as [m|] eqn:Ec; [ | apply rt_refl ].
    destruct (C1 m eq_refl) as [Hin Hle].
    apply rt_step, red_top, redex_coef; auto.
Qed.

Theorem normalize_reds :
  (forall x, BS_proper x -> reds x (normS x)) /\ (forall T, BI_proper T -> redsI T (normI T)).
Proof.
  apply BNotation_mut.
  - intros _. apply rt_refl.
  - intros T IHT y IHy [HT Hy]. simpl.
    apply reds_trans with (BN (normI T) y); [ apply reds_BN_idx; auto | ].
    apply reds_trans with (BN (normI T) (normS y)); [ apply reds_BN_arg; auto | ].
    apply smartN_reds; [ apply (proj2 normalize_correct); auto | apply (proj1 normalize_correct); auto ].
  - intros _. apply rt_refl.
  - intros e IHe c IHc r IHr [He [Hc [_ [Hr _]]]]. simpl.
    eapply rt_trans; [ apply redsI_exp; auto | ].
    eapply rt_trans; [ apply redsI_coef; auto | ].
    apply redsI_rest; auto.
Qed.

(** ** Normal forms are exactly the irreducible terms *)

Lemma Kin_Klt k z T : Kin k T -> Klt z T -> BS_denote k < z.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [H1 [H2 H3]]; [ auto | subst; auto | auto ].
Qed.

Theorem nf_irreducible :
  (forall x x', red_S x x' -> ~ BS_nf x) /\ (forall T T', red_I T T' -> ~ BI_nf T).
Proof.
  apply red_mut.
  - intros x x' H Hx. destruct H as [T y H | T y k Hk H].
    + destruct Hx as [_ [_ [Hlt _]]]. apply (ord_lt_irreflexive (BS_denote y)).
      eapply ord_lt_le_trans; eauto.
    + destruct Hx as [_ [_ [_ HK]]]. apply (ord_lt_irreflexive (BS_denote k)).
      eapply ord_lt_le_trans; [ apply (Kin_Klt k _ T Hk HK) | exact H ].
  - intros T T' y H IH [HT _]. auto.
  - intros T y y' H IH [_ [Hy _]]. auto.
  - intros e e' c r H IH [He _]. auto.
  - intros e c c' r H IH [_ [Hc _]]. auto.
  - intros e c r r' H IH [_ [_ [_ [Hr _]]]]. auto.
Qed.

Theorem nf_iff_irreducible x : BS_proper x -> BS_nf x <-> ~ exists x', red_S x x'.
Proof.
  intro Hx. split.
  - intros Hn [x' H]. apply ((proj1 nf_irreducible) x x' H Hn).
  - intro Hirr.
    assert (Hr := proj1 normalize_reds x Hx).
    apply clos_rt_rt1n in Hr.
    assert (Hn := normS_nf x Hx).
    remember (normS x) as w eqn:Ew.
    destruct Hr as [|x1 Hstep]; auto.
    elim Hirr. eexists; eauto.
Qed.

(** ** Unique normal forms and confluence *)

Theorem reds_sound x y : BS_proper x -> reds x y -> BS_proper y /\ BS_denote x ≈ BS_denote y.
Proof.
  intros Hx H. induction H as [x y H | x | x y z H1 IH1 H2 IH2].
  - split; [ apply (proj1 red_proper) with x | apply (proj1 red_sound) ]; auto.
  - split; [ auto | reflexivity ].
  - destruct (IH1 Hx) as [Hy Hxy]. destruct (IH2 Hy) as [Hz Hyz]. split; auto. rewrite Hxy; auto.
Qed.

Definition normalizes (x y:BSmall) : Prop := reds x y /\ BS_nf y.

Theorem normalizes_iff x y : BS_proper x -> normalizes x y <-> BS_nf y /\ BS_denote x ≈ BS_denote y.
Proof.
  intro Hx. split.
  - intros [H Hy]. split; auto. apply (reds_sound x y Hx H).
  - intros [Hy Heq]. split; auto.
    replace y with (normS x); [ apply normalize_reds; auto | ].
    apply BS_nf_unique; auto using normS_nf. rewrite normS_equal; auto.
Qed.

Theorem normalizes_unique x : BS_proper x -> exists! y, normalizes x y.
Proof.
  intro Hx. exists (normS x). split.
  - split; [ apply normalize_reds; auto | apply normS_nf; auto ].
  - intros y Hy. apply (normalizes_iff x y Hx) in Hy. destruct Hy as [Hy Heq].
    apply BS_nf_unique; auto using normS_nf. rewrite normS_equal; auto.
Qed.

Theorem reduce_confluent x y1 y2 : BS_proper x -> reds x y1 -> reds x y2 ->
  exists w, reds y1 w /\ reds y2 w.
Proof.
  intros Hx H1 H2.
  destruct (reds_sound x y1 Hx H1) as [Hy1 E1]. destruct (reds_sound x y2 Hx H2) as [Hy2 E2].
  exists (normS y1). split; [ apply normalize_reds; auto | ].
  replace (normS y1) with (normS y2); [ apply normalize_reds; auto | ].
  apply BS_nf_unique; auto using normS_nf.
  rewrite !normS_equal; auto. rewrite <- E1, <- E2. reflexivity.
Qed.

(** ** Examples, by computation *)

(** φ_1(ε₀) = ω + ε₀ = ε₀: the argument is a fixpoint. *)
Example normalize_arg : normS (BN BI_one (BN BI_Ω BZ)) = BN BI_Ω BZ.
Proof. reflexivity. Qed.

(** φ_{Ω^0·ε₀}(0) = ω^{ε₀} = ε₀: collapse to the coefficient. *)
Example normalize_coef : normS (BN (BIC BIZ (BN BI_Ω BZ) BIZ) BZ) = BN BI_Ω BZ.
Proof. reflexivity. Qed.

(** ε₀ + 1 = ω^{ε₀} + 1 is normal, and φ_{Ω^0·(ε₀+1)}(0) = ω^{ε₀+1}
    does not collapse. *)
Definition BS_ε0_plus1 : BSmall := BN (BIC BIZ (BN BI_Ω BZ) BIZ) BS_one.

Example normalize_ε0_plus1 : normS BS_ε0_plus1 = BS_ε0_plus1.
Proof. reflexivity. Qed.

Example normalize_nocollapse :
  normS (BN (BIC BIZ BS_ε0_plus1 BIZ) BZ) = BN (BIC BIZ BS_ε0_plus1 BIZ) BZ.
Proof. reflexivity. Qed.
