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

(** * The offset of a threshold

For a normal index R with a nonzero leading exponent and a normal
notation m, @BS_offset R m@ is the least t with m < φ_R(t): the least
value of φ_R above m is φ_R(t).  It is computed by recursion on m:
if m < φ_R(0) then t = 0; otherwise m = φ_{T'}(y') with
 - T' = R: t = y' + 1;
 - T' > R: if R's coefficients lie below m, m is a fixpoint of φ_R and
   t = m + 1; otherwise m = φ_R(0) and t = 1;
 - T' < R: the values of φ_R above max(y', coefficients of T') are the
   values above m, so recurse on that maximum. *)

Abbreviation PHI R := (bphi (addOrd 1) (BI_denote R)).

Definition lead_big (R:BIdx) : Prop :=
  match R with BIC e _ _ => e <> BIZ | BIZ => False end.

Lemma Ω_le_R R : BI_nf R -> lead_big R -> bsub bOmega (BI_denote R).
Proof.
  destruct R as [|e c r]; [ contradiction | ]. destruct e as [|e1 c1 r1]; [ contradiction | ].
  intros [He [_ [Hc0 _]]] _. destruct He as [_ [_ [Hc10 _]]].
  change (bsub bOmega (badd (bmul (bexpΩ (BI_denote (BIC e1 c1 r1))) (embed (BS_denote c))) (BI_denote r))).
  eapply bsub_trans; [ | apply bsub_le_badd ].
  eapply bsub_trans; [ | apply bsub_P_Pz; auto ].
  destruct (bsmall_mul_embed_inh (BI_denote e1) (BS_denote c1) Hc10) as [t].
  destruct (badd_small_l (bmul (bexpΩ (BI_denote e1)) (embed (BS_denote c1))) (BI_denote r1) t) as [a _].
  apply (Ω_le_bexp _ a).
Qed.

(** Common fixpoints of the components of such an R are additively principal. *)
Lemma fix_principal R z a : BI_nf R -> lead_big R -> complete z -> bfix (addOrd 1) (BI_denote R) z ->
  a < z -> a + z ≤ z.
Proof.
  intros HR Hl Hz Hfix Ha.
  assert (Ha' := Ha). rewrite ord_lt_unfold in Ha'. destruct Ha' as [j Hj].
  assert (Hc : complete (z j)) by (apply complete_subord; auto).
  transitivity (z j + z); [ apply addOrd_monotone; [ exact Hj | reflexivity ] | ].
  transitivity (expOrd ω (z j) + z); [ apply addOrd_monotone; [ apply le_expOmega | reflexivity ] | ].
  transitivity (bphi (addOrd 1) (embed (z j)) z); [ apply (proj2 (bphi_onePlus_embed _ _ Hc Hz)) | ].
  apply (zlt_nest _ onePlus_normal z (embed (z j)) (BI_denote R)); auto using BI_good, BI_bfam.
  apply zlt_mono_r with bOmega; [ apply zlt_embed_Ω, index_lt | apply Ω_le_R; auto ].
Qed.

Lemma fix_succ_lt R z a : BI_nf R -> lead_big R -> complete z -> bfix (addOrd 1) (BI_denote R) z ->
  a < z -> succOrd a < z.
Proof.
  intros HR Hl Hz Hfix Ha.
  assert (Hinf := fix_onePlus_finite _ onePlus_normal z Hz (proj1 Hfix)).
  apply ord_le_lt_trans with (a + 1).
  { rewrite addOrd_succ. apply succ_monotone, addOrd_le1. }
  eapply ord_lt_le_trans; [ apply addOrd_increasing | apply (fix_principal R z a); auto ].
  apply ord_lt_le_trans with (natOrdSize 2); [ apply succ_lt | apply Hinf ].
Qed.

Definition off_max (y':BSmall) (T':BIdx) : BSmall :=
  match kmax (S (BI_size T' + BI_size T')) T' with
  | None => y'
  | Some k => match BS_compare k y' with LT => y' | _ => k end
  end.

Lemma off_max_spec T' y' : BS_nf (BN T' y') ->
  BS_nf (off_max y' T') /\ (BS_size (off_max y' T') < BS_size (BN T' y'))%nat /\
  BS_denote (off_max y' T') < BS_denote (BN T' y') /\
  (forall z, BS_denote (off_max y' T') < z -> BS_denote y' < z /\ Klt z T').
Proof.
  intro Hm. assert (Hm' := Hm). destruct Hm' as [HT' [Hy' [Hylt HK]]].
  assert (Hk := kmax_spec (S (BI_size T' + BI_size T')) T' HT' ltac:(lia)).
  unfold off_max. destruct (kmax (S (BI_size T' + BI_size T')) T') as [k|]; simpl in Hk.
  - destruct Hk as [Hkin HKle].
    assert (Hkn := Kin_nf k T' Hkin HT').
    assert (Hkm : BS_denote k < BS_denote (BN T' y')) by (apply (Kge_lt _ _ T' (Kin_Kge k T' Hkin) HK)).
    assert (Hks := Kin_size' k T' Hkin).
    assert (Hc := BS_compare_correct k y' Hkn Hy').
    destruct (BS_compare k y'); simpl in Hc.
    + split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
      intros w Hw. split; auto. apply Kle_lt with (BS_denote k); auto. eapply ord_lt_trans; eauto.
    + split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
      intros w Hw. split; [ rewrite <- Hc; auto | ]. apply Kle_lt with (BS_denote k); auto.
    + split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
      intros w Hw. split; [ eapply ord_lt_trans; eauto | ]. apply Kle_lt with (BS_denote k); auto.
  - subst T'. split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
    intros w Hw. split; [ auto | exact I ].
Qed.

Definition offStep (rec:BSmall -> BSmall) (R:BIdx) (m:BSmall) : BSmall :=
  match m with
  | BZ => BZ
  | BN T' y' =>
    match cmpI (S (BI_size T' + BI_size R)) T' R with
    | EQ => BS_succ y'
    | LT => rec (off_max y' T')
    | GT => if coefs_below (S (BI_size R + BS_size m)) R m then BS_succ m else BS_one
    end
  end.

Fixpoint offN (fuel:nat) (R:BIdx) (m:BSmall) : BSmall :=
  match fuel with
  | O => BZ
  | S fuel' =>
    match BS_compare m (normS (BN R BZ)) with
    | LT => BZ
    | _ => offStep (offN fuel' R) R m
    end
  end.

Definition BS_offset (R:BIdx) (m:BSmall) : BSmall := offN (S (BS_size m)) R m.

Definition OffSpec (R:BIdx) (m t:BSmall) : Prop :=
  BS_nf t /\ BS_denote m < PHI R (BS_denote t) /\ BS_denote t < PHI R (BS_denote t) /\
  (forall z, complete z -> bfix (addOrd 1) (BI_denote R) z -> BS_denote m < z -> PHI R (BS_denote t) ≤ z).

Lemma Hinh_of T : BI_nf T -> T <> BIZ -> inhabited (bsmall (BI_denote T) + bbig (BI_denote T)).
Proof. destruct T as [|e c r]; [ tauto | ]. intros HT _. apply BI_inh, HT. Qed.

Section offset.
  Variable R : BIdx.
  Hypothesis HR : BI_nf R.
  Hypothesis HRl : lead_big R.

  Let HRpos : BI_pos R := BI_nf_pos R HR.
  Let Hinh : inhabited (bsmall (BI_denote R) + bbig (BI_denote R)).
  Proof. destruct R as [|e c r]; [ contradiction | ]. apply BI_inh, HR. Qed.

  Let Hvfix x : complete x -> bfix (addOrd 1) (BI_denote R) (PHI R x).
  Proof. intro Hx. apply bfix_value_full; auto using onePlus_normal, BI_good. Qed.

  Let Hvc x : complete x -> complete (PHI R x).
  Proof. intro Hx. apply normal_complete; auto using BI_normal. Qed.

  Let Hinc x y : complete y -> x < y -> PHI R x < PHI R y.
  Proof. intros. apply (normal_increasing _ (BI_normal R)); auto. Qed.

  (** If φ_R(a) lies below m, then φ_R(a+1) is the least common fixpoint above m. *)
  Let succ_case m a t : BS_nf t -> BS_denote t ≈ succOrd a -> complete a ->
    PHI R a ≤ BS_denote m -> BS_denote m < PHI R (succOrd a) -> OffSpec R m t.
  Proof.
    intros Ht Et Ha Hle Hlt.
    assert (E : PHI R (BS_denote t) ≈ PHI R (succOrd a)) by (apply ord_eq_normal; auto using BI_normal).
    split; [ exact Ht | split; [ rewrite E; exact Hlt | split ] ].
    - rewrite E, Et. apply (fix_succ_lt R); auto using succ_complete.
      eapply ord_le_lt_trans; [ | apply Hinc; [ apply succ_complete; auto | apply succ_lt ] ].
      apply normal_inflationary; auto using BI_normal.
    - intros z Hz Hfix Hmz. rewrite E.
      apply bphi_succ_le; auto using onePlus_normal, BI_good.
      eapply ord_le_lt_trans; eauto.
  Qed.

  Lemma offStep_correct rec m : BS_nf m -> PHI R 0 ≤ BS_denote m ->
    (forall m', BS_nf m' -> (BS_size m' < BS_size m)%nat -> OffSpec R m' (rec m')) ->
    OffSpec R m (offStep rec R m).
  Proof.
    intros Hm Hge IH.
    destruct m as [|T' y'].
    { elim (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ apply bphi_nonzero, onePlus_normal | exact Hge ]. }
    assert (Hm' := Hm). destruct Hm' as [HT' [Hy' [Hylt HK]]].
    unfold offStep.
    assert (Hc := proj2 (cmp_correct (S (BI_size T' + BI_size R))) T' R ltac:(lia) HT' HR).
    destruct (cmpI (S (BI_size T' + BI_size R)) T' R); simpl in Hc.
    - (* T' < R: recurse on the maximum of y' and the coefficients of T' *)
      destruct (off_max_spec T' y' Hm) as [Hmx [Hsz [Hlt Habove]]].
      destruct (IH _ Hmx Hsz) as [Nt [Hm1 [Ht1 Hmin]]].
      assert (Lz : forall z, complete z -> bfix (addOrd 1) (BI_denote R) z ->
                     BS_denote (off_max y' T') < z -> BS_denote (BN T' y') < z).
      { intros z Hz Hfix Hxz. destruct (Habove z Hxz) as [Hyz HKz].
        assert (Hinf := fix_onePlus_finite _ onePlus_normal z Hz (proj1 Hfix)).
        assert (Hzlt := proj1 (nest z Hinf (S (BI_size T')) T' ltac:(lia) HT' HKz) R HR Hc).
        assert (Hfz := zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good R) (BI_bfam R) Hz Hfix).
        eapply ord_lt_le_trans; [ | exact Hfz ].
        apply (normal_increasing _ (BI_normal T')); auto. }
      split; [ exact Nt | split; [ | split; [ exact Ht1 | ] ] ].
      + apply Lz; auto using BS_complete.
      + intros z Hz Hfix Hmz. apply Hmin; auto. exact (ord_lt_trans _ _ _ Hlt Hmz).
    - (* T' = R *)
      destruct (BS_succ_reflects (BS_denote y') y' (conj (ord_eq_refl _) Hy')) as [E1 N1].
      apply (succ_case _ (BS_denote y') _ N1 ltac:(symmetry; exact E1) (BS_complete y')).
      + apply (proj2 (bphi_ieq _ _ _ Hc)).
      + eapply ord_le_lt_trans; [ apply (proj1 (bphi_ieq _ _ _ Hc)) | ].
        apply Hinc; [ apply succ_complete, BS_complete | apply succ_lt ].
    - (* R < T' *)
      assert (HT'ne : T' <> BIZ) by (intro E; subst; inversion Hc).
      assert (Hcb := coefs_below_spec (S (BI_size R + BS_size (BN T' y'))) (BN T' y') R
                       (fun c Hs Hcn => proj1 (cmp_correct (S (BI_size R + BS_size (BN T' y')))) c (BN T' y') ltac:(lia) Hcn Hm) HR).
      destruct (coefs_below (S (BI_size R + BS_size (BN T' y'))) R (BN T' y')).
      + assert (HK' := proj1 Hcb eq_refl).
        assert (Hz := proj1 (nest _ (BN_inf T' y' HT' HT'ne) (S (BI_size R)) R ltac:(lia) HR HK') T' HT' Hc).
        assert (Hfix := zlt_value _ onePlus_normal _ _ (BS_denote y') Hz (BI_good T') (BI_bfam T')
                          (Hinh_of T' HT' HT'ne) (BS_complete y')).
        destruct (BS_succ_reflects _ _ (conj (ord_eq_refl _) Hm)) as [E1 N1].
        apply (succ_case _ (BS_denote (BN T' y')) _ N1 ltac:(symmetry; exact E1) (BS_complete _)).
        * exact Hfix.
        * eapply ord_le_lt_trans; [ apply normal_inflationary; auto using BI_normal, BS_complete | ].
          apply Hinc; [ apply succ_complete, BS_complete | apply succ_lt ].
      + assert (Hd := dominance R BZ _ HRpos (proj2 Hcb eq_refl)).
        apply (succ_case _ 0 _ BS_one_nf BS_one_denote zero_complete Hge).
        eapply ord_le_lt_trans; [ exact Hd | ].
        apply Hinc; [ apply succ_complete, zero_complete | apply succ_lt ].
  Qed.

  Theorem offN_correct : forall fuel m, (BS_size m < fuel)%nat -> BS_nf m -> OffSpec R m (offN fuel R m).
  Proof.
    induction fuel as [|fuel IH]; intros m Hsz Hm; [ lia | ].
    assert (Hp : BS_proper (BN R BZ)) by (split; [ apply (proj2 nf_proper); auto | exact I ]).
    assert (Hm0 := normS_nf _ Hp). assert (E0 := normS_equal _ Hp).
    assert (Hc := BS_compare_correct m _ Hm Hm0).
    change (OffSpec R m (match BS_compare m (normS (BN R BZ)) with
                         | LT => BZ | _ => offStep (offN fuel R) R m end)).
    destruct (BS_compare m (normS (BN R BZ))); cbv beta iota delta [ordering_correct] in Hc.
    - split; [ exact I | split; [ eapply ord_lt_le_trans; [ exact Hc | apply E0 ] | split ] ].
      + apply bphi_nonzero, onePlus_normal.
      + intros z Hz Hfix _. apply bphi_le_fix; auto using onePlus_normal, BI_good.
    - apply offStep_correct; auto.
      + transitivity (BS_denote (normS (BN R BZ))); [ apply E0 | apply Hc ].
      + intros m' Hm' Hs. apply IH; auto. lia.
    - apply offStep_correct; auto.
      + transitivity (BS_denote (normS (BN R BZ))); [ apply E0 | apply ord_lt_le, Hc ].
      + intros m' Hm' Hs. apply IH; auto. lia.
  Qed.

  Corollary BS_offset_correct m : BS_nf m -> OffSpec R m (BS_offset R m).
  Proof. intro Hm. apply offN_correct; auto. Qed.
End offset.

(** ** Examples, by computation *)

(** Above 1, the first ε-number is ε₀ = φ_Ω(0). *)
Example offset_one : BS_offset BI_Ω BS_one = BZ.
Proof. reflexivity. Qed.

(** Above ε₀ = φ_Ω(0), the next one is φ_Ω(1). *)
Example offset_eps0 : BS_offset BI_Ω (BN BI_Ω BZ) = BS_succ BZ.
Proof. reflexivity. Qed.

(** Above ε₀ + 1 = ω^{ε₀} + 1, still φ_Ω(1). *)
Example offset_eps0_plus1 : BS_offset BI_Ω BS_ε0_plus1 = BS_succ BZ.
Proof. reflexivity. Qed.

(** φ_{Ω·2}(0) is a fixpoint of φ_Ω, so the least φ_Ω-value above it is φ_Ω(φ_{Ω·2}(0) + 1). *)
Example offset_fix : BS_offset BI_Ω (BN (BIC BI_one (BN BIZ BS_one) BIZ) BZ) =
                     BS_succ (BN (BIC BI_one (BN BIZ BS_one) BIZ) BZ).
Proof. reflexivity. Qed.

(** * One absorption step

P = Ω^e·c is a normal summand and R a normal index whose leading
exponent exceeds e.  The index P + R is improper.  Its common
fixpoints are those of R that lie above the coefficients of P, so
φ_{P+R}(y) = φ_R(t + y) with t = BS_offset R m, m the largest
coefficient of P. *)

Definition lead_gt (R:BIdx) (e:BIdx) : Prop :=
  match R with BIC e' _ _ => ilt e e' | BIZ => False end.

Section absorb.
  Variables (e:BIdx) (c:BSmall) (R:BIdx).
  Hypothesis HP : BI_nf (BIC e c BIZ).
  Hypothesis HR : BI_nf R.
  Hypothesis HRe : lead_gt R e.

  Let P := BIC e c BIZ.
  Let X := BIC e c R.

  Lemma R_lead_big : lead_big R.
  Proof. destruct R as [|e' c' r']; [ contradiction | ]. simpl in *. intro E; subst. inversion HRe. Qed.

  Lemma X_pos : BI_pos X.
  Proof. destruct HP as [_ [_ [Hc0 _]]]. simpl. split; [ apply BI_nf_pos, HP | split; auto ]. apply BI_nf_pos; auto. Qed.

  Lemma X_inh : inhabited (bsmall (BI_denote X) + bbig (BI_denote X)).
  Proof. apply BI_inh, HP. Qed.

  (** (⊆) Every common fixpoint for P + R is one for R: R's children
      sit below P + (R's children). *)
  Lemma absorb_sub z : complete z -> bfix (addOrd 1) (BI_denote X) z -> bfix (addOrd 1) (BI_denote R) z.
  Proof.
    intros Hz [H1 [H2 H3]]. split; [ exact H1 | split ].
    - intro a. destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) a) as [k Hk].
      eapply ord_le_trans; [ | exact (H2 k) ].
      apply (proj2 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (bfam_small _ (BI_bfam X) k))).
      change (bsmallSz (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) k) with
        (bsmallSz (BI_denote X) k) in Hk.
      rewrite Hk. apply bsub_absorb.
    - intro d. destruct (badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) d) as [k Hk].
      eapply ord_le_trans; [ | exact (H3 k) ].
      apply (proj2 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (bfam_big _ (BI_bfam X) k z))).
      change (bbigSz (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) k z) with
        (bbigSz (BI_denote X) k z). rewrite Hk. apply bsub_absorb.
  Qed.

  (** The values of φ_{P+R} lie above the coefficients of P, which occur
      at positions that are not the end. *)
  Lemma absorb_region y : complete y -> Klt (PHI X y) P.
  Proof.
    intro Hy. apply Klt_of_Kge. intros z Hz.
    assert (HK : Kgs z X).
    { destruct R as [|e' c' r']; [ contradiction | ]. simpl in Hz |- *.
      destruct Hz as [H|[H|[]]]; auto. }
    destruct (Kgs_ctx X X_pos _ HK) as [C [ζ [HC [Hζ [Hzζ Hlt]]]]].
    apply ord_le_lt_trans with (bphi (addOrd 1) (C ζ) 0).
    - transitivity ζ; auto. apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ).
    - eapply ord_lt_le_trans; [ apply (bphi_strict (addOrd 1) onePlus_normal _ (BI_denote X) Hlt (BI_good X) (BI_bfam X)) | ].
      apply (proj1 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (BI_bfam X))). apply zero_least.
  Qed.

  Let n0 := S (BI_size P + BI_size P).
  Definition absorb_max : BSmall := match kmax n0 P with Some k => k | None => BZ end.

  Lemma absorb_max_spec : BS_nf absorb_max /\ Kin absorb_max P /\ Kle (BS_denote absorb_max) P.
  Proof.
    assert (H := kmax_spec n0 P HP ltac:(unfold n0; lia)).
    unfold absorb_max. destruct (kmax n0 P) as [k|]; simpl in H; [ | discriminate ].
    destruct H as [H1 H2]. split; [ apply (Kin_nf k P H1 HP) | split; auto ].
  Qed.

  Definition absorb_offset : BSmall := BS_offset R absorb_max.

  (** The hard direction, at notation values: common fixpoints for R above
      the coefficients of P are common fixpoints for P + R.  Assumed here;
      it is proved below (@ABS_all@). *)
  Hypothesis ABS : forall s, BS_nf s -> Klt (PHI R (BS_denote s)) P ->
    bfix (addOrd 1) (BI_denote X) (PHI R (BS_denote s)).

  Theorem absorb_enum : forall y, BS_nf y ->
    PHI X (BS_denote y) ≈ PHI R (BS_denote absorb_offset + BS_denote y).
  Proof.
    destruct absorb_max_spec as [Hm [Hmin HmK]].
    destruct (BS_offset_correct R HR R_lead_big _ Hm) as [Nt [Hmt [Htt Hleast]]].
    fold absorb_offset in Nt, Hmt, Htt, Hleast.
    set (t := absorb_offset) in *.
    assert (Htc := BS_complete t).
    assert (Hgx := BI_good X). assert (Hgr := BI_good R).
    intro y. induction y as [y IH] using (size_induction (ord BSmall BS_denote)). intro Hy.
    assert (HIy := BS_has_all_interpolants y Hy).
    assert (Hyc := BS_complete y).
    destruct (BS_add_reflects _ t (conj (ord_eq_refl _) Nt) _ y (conj (ord_eq_refl _) Hy)) as [Es Ns].
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
      + assert (HK : Klt (PHI R (BS_denote s)) P).
        { apply Kle_lt with (BS_denote absorb_max); auto.
          eapply ord_lt_le_trans; [ exact Hmt | ].
          apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam R))).
          rewrite <- Es. apply addOrd_le1. }
        destruct (ABS s Ns HK) as [H1 [H2 H3]].
        intros [k|k]; cbn [bphi_fam]; split; auto.
    - set (z := PHI X (BS_denote y)).
      assert (Hzc : complete z) by (apply BS_complete with (x := BN X y)).
      assert (Hzfix := absorb_sub z Hzc (bfix_value_full _ onePlus_normal _ _ Hgx X_inh Hyc)).
      assert (Hreg := absorb_region _ Hyc). fold z in Hreg.
      assert (Hmz : BS_denote absorb_max < z) by (apply (Kge_lt _ _ P (Kin_Kge _ _ Hmin) Hreg)).
      assert (Hlz := Hleast z Hzc Hzfix Hmz).
      assert (Htz : BS_denote t < z) by (eapply ord_lt_le_trans; eauto).
      assert (Hpr := fix_principal R z _ HR R_lead_big Hzc Hzfix Htz).
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
End absorb.

(** ** The hard direction of absorption *)

Lemma bfix_eq T z z' : bgood (addOrd 1) T -> bfam T -> z ≈ z' ->
  bfix (addOrd 1) T z -> bfix (addOrd 1) T z'.
Proof.
  intros Hg Hf E [H1 [H2 H3]]. split; [ | split ].
  - transitivity (1 + z); [ apply onePlus_mono, E | transitivity z; [ exact H1 | apply E ] ].
  - intro a. transitivity (bphi (addOrd 1) (bsmallSz T a) z).
    + apply (proj1 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hf a))). apply E.
    + transitivity z; [ exact (H2 a) | apply E ].
  - intro d. transitivity (bphi (addOrd 1) (bbigSz T d z) 0).
    + apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hf d z))).
      apply bfam_fam; auto. apply E.
    + transitivity z; [ exact (H3 d) | apply E ].
Qed.

Lemma Kgs_lt T k : BI_pos T -> Kgs k T -> k < PHI T 0.
Proof.
  intros HT HK. destruct (Kgs_ctx T HT _ HK) as [C [ζ [HC [Hζ [Hkζ Hlt]]]]].
  apply ord_le_lt_trans with (bphi (addOrd 1) (C ζ) 0).
  - transitivity ζ; auto. apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ).
  - apply (bphi_strict (addOrd 1) onePlus_normal _ _ Hlt (BI_good T) (BI_bfam T)).
Qed.

Lemma Kend_of T z : BI_nf T -> (forall k, Kge k T -> k ≤ z) -> (forall k, Kgs k T -> k < z) -> Kend z T.
Proof.
  induction T as [|e IHe c r IHr]; intros HT H1 H2; [ exact I | ].
  destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
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

(** Coefficients of T lie below z except at the end, when φ_T(0) ≤ z. *)
Lemma Kend_of_value T z : BI_nf T -> PHI T 0 ≤ z -> Kend z T.
Proof.
  intros HT Hz. apply Kend_of; auto.
  - intros k Hk. rewrite <- Hz. apply (dominance T BZ k (BI_nf_pos T HT) Hk).
  - intros k Hk. eapply ord_lt_le_trans; [ apply (Kgs_lt T k (BI_nf_pos T HT) Hk) | exact Hz ].
Qed.

Lemma Klt_of_value T z : BI_nf T -> PHI T 0 < z -> Klt z T.
Proof.
  intros HT Hz. apply Klt_of_Kge. intros k Hk.
  eapply ord_le_lt_trans; [ apply (dominance T BZ k (BI_nf_pos T HT) Hk) | exact Hz ].
Qed.

Section abs_all.
  Variables (e:BIdx) (c:BSmall).
  Hypothesis HP : BI_nf (BIC e c BIZ).

  Definition ABSw (R:BIdx) : Prop := forall w, BS_nf w ->
    bfix (addOrd 1) (BI_denote R) (BS_denote w) -> Klt (BS_denote w) (BIC e c BIZ) ->
    bfix (addOrd 1) (BI_denote (BIC e c R)) (BS_denote w).

  Lemma lead_gt_big R : lead_gt R e -> lead_big R.
  Proof. destruct R as [|e' c' r']; [ contradiction | ]. simpl. intros H E. subst. inversion H. Qed.

  Lemma lead_gt_ilt R c'' r'' : lead_gt R e -> ilt (BIC e c'' r'') R.
  Proof. destruct R as [|e' c' r']; [ contradiction | ]. intro H. apply ilt_exp, H. Qed.

  Lemma ABSw_ABS R : BI_nf R -> lead_gt R e -> ABSw R ->
    forall s, BS_nf s -> Klt (PHI R (BS_denote s)) (BIC e c BIZ) ->
    bfix (addOrd 1) (BI_denote (BIC e c R)) (PHI R (BS_denote s)).
  Proof.
    intros HR HRe HA s Hs HK.
    assert (Hp := nf_BN_proper R s HR Hs).
    assert (Ew : BS_denote (normS (BN R s)) ≈ PHI R (BS_denote s)) by (apply normS_equal; auto).
    assert (Hne : R <> BIZ) by (intro E; subst; contradiction).
    apply bfix_eq with (BS_denote (normS (BN R s))); auto using BI_good, BI_bfam.
    apply HA; [ apply normS_nf; auto | | ].
    - apply bfix_eq with (PHI R (BS_denote s)); auto using BI_good, BI_bfam.
      + symmetry; auto.
      + apply bfix_value_full; auto using onePlus_normal, BI_good, BS_complete. apply Hinh_of; auto.
    - apply Klt_mono with (PHI R (BS_denote s)); auto. apply Ew.
  Qed.

  Theorem ABS_all : forall U R, ble (BI_denote R) U -> BI_nf R -> lead_gt R e -> ABSw R.
  Proof.
    intro U. induction U as [U IHU] using (well_founded_induction blt_wf).
    intros R HU HR HRe w Hw Hfix HK.
    assert (HP' := HP). destruct HP' as [He [Hc [Hc0 _]]].
    set (z := BS_denote w) in *.
    assert (Hzc : complete z) by apply BS_complete.
    assert (Hinf := fix_onePlus_finite _ onePlus_normal z Hzc (proj1 Hfix)).
    assert (Hz0 : 0 < z) by (apply ord_lt_le_trans with (natOrdSize 1); [ apply succ_lt | apply Hinf ]).
    assert (Hprin : forall a, a < z -> a + z ≤ z)
      by (intros; apply (fix_principal R z); auto; apply lead_gt_big; auto).
    assert (HKendR : Kend z R).
    { apply Kend_of_value; auto. apply bphi_le_fix; auto using onePlus_normal, BI_good. }
    assert (HKe : Klt z e) by apply HK.
    assert (Hcz : BS_denote c < z) by apply HK.
    (* P fixes z, by nesting *)
    assert (HPz : PHI (BIC e c BIZ) z ≤ z).
    { assert (Hzlt := proj1 (nest z Hinf (S (BI_size (BIC e c BIZ))) (BIC e c BIZ) ltac:(lia) HP HK) R HR
                       (lead_gt_ilt R c BIZ HRe)).
      apply (zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good R) (BI_bfam R) Hzc Hfix). }
    assert (HfixP := bfix_of_fix _ onePlus_normal _ z (BI_good _) (BI_bfam _) Hzc HPz).
    (* nesting for a normal N below R *)
    assert (Nest : forall N, BI_nf N -> ilt N R -> Klt z N -> PHI N z ≤ z).
    { intros N HN Hlt HKN.
      assert (Hzlt := proj1 (nest z Hinf (S (BI_size N)) N ltac:(lia) HN HKN) R HR Hlt).
      apply (zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good R) (BI_bfam R) Hzc Hfix). }
    assert (NestLe : forall N, BI_nf N -> ilt N R -> Kend z N -> PHI N 0 ≤ z).
    { intros N HN Hlt HKN.
      assert (HB := proj1 (nest_le z Hinf (S (BI_size N)) N ltac:(lia) HN HKN) R HR HKendR Hlt).
      apply (bleZ_sound _ onePlus_normal z _ _ HB (BI_denote R) (bsub_refl _) (BI_good R) (BI_bfam R) Hzc Hfix). }
    (* the classification of P + K' for a normal K' below R *)
    assert (Hcls : forall K', BI_nf K' -> blt (BI_denote K') (BI_denote R) -> bfix (addOrd 1) (BI_denote K') z ->
              (PHI K' z ≤ z -> PHI (BIC e c K') z ≤ z) /\ PHI (BIC e c K') 0 ≤ z).
    { intros K' HK' Hblt HfK.
      assert (HK'0 : PHI K' 0 ≤ z) by (apply bphi_le_fix; auto using onePlus_normal, BI_good).
      assert (HKendK := Kend_of_value K' z HK' HK'0).
      destruct K' as [|e2 c2 r2].
      { split; [ intros _; exact HPz | ].
        eapply ord_le_trans; [ | exact HPz ].
        apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam _))). apply zero_least. }
      assert (HK'' := HK'). destruct HK'' as [He2 [Hc2 [Hc20 [Hr2 Hl2]]]].
      assert (Hsmall_Klt : PHI (BIC e2 c2 r2) z ≤ z -> Klt z (BIC e2 c2 r2)).
      { intro H. apply Klt_of_value; auto. eapply ord_lt_le_trans; [ | exact H ].
        apply (normal_increasing _ (BI_normal _)); auto. }
      assert (Hcmp := proj2 (cmp_correct (S (BI_size e2 + BI_size e))) e2 e ltac:(lia) He2 He).
      destruct (cmpI (S (BI_size e2 + BI_size e)) e2 e); simpl in Hcmp.
      - (* lead(K') < e: P + K' is normal *)
        assert (HN : BI_nf (BIC e c (BIC e2 c2 r2))) by (repeat split; auto).
        split.
        + intro H. apply Nest; auto using lead_gt_ilt. split; [ exact HKe | split; [ exact Hcz | auto ] ].
        + apply NestLe; auto using lead_gt_ilt. split; [ exact HKe | split; [ exact Hcz | exact HKendK ] ].
      - (* lead(K') = e: merge the coefficients *)
        destruct (BS_add_reflects _ c (conj (ord_eq_refl _) Hc) _ c2 (conj (ord_eq_refl _) Hc2)) as [Ea Na].
        set (N := BIC e (BS_add c c2) r2).
        assert (HN : BI_nf N).
        { split; [ exact He | split; [ exact Na | split; [ | split; [ exact Hr2 | ] ] ] ].
          - rewrite <- Ea. eapply ord_lt_le_trans; [ exact Hc0 | apply addOrd_le1 ].
          - apply (lead_below_ieq r2 r2 e2 e); auto using ieq_refl. }
        assert (Heq : bequiv (BI_denote (BIC e c (BIC e2 c2 r2))) (BI_denote N)).
        { change (bequiv (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
                              (badd (bmul (bexpΩ (BI_denote e2)) (embed (BS_denote c2))) (BI_denote r2)))
                         (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote (BS_add c c2)))) (BI_denote r2))).
          apply bequiv_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
                     (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c2))) (BI_denote r2))).
          { apply bequiv_badd; [ apply bequiv_refl | ].
            apply bequiv_badd; [ | apply bequiv_refl ].
            apply bequiv_bmul; [ apply bequiv_bexpΩ, ieq_bequiv; auto | apply bequiv_refl ]. }
          eapply bequiv_trans; [ apply bequiv_merge | ].
          apply bequiv_badd; [ | apply bequiv_refl ].
          apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_embed; auto ]. }
        assert (EN : forall y, PHI (BIC e c (BIC e2 c2 r2)) y ≈ PHI N y)
          by (intro y; apply bphi_bequiv; auto using onePlus_mono, BI_bfam).
        split.
        + intro H. rewrite EN. apply Nest; [ exact HN | apply lead_gt_ilt; auto | ].
          destruct (Hsmall_Klt H) as [HKe2 [Hc2z HKr2]].
          unfold N. split; [ exact HKe | split; [ | exact HKr2 ] ].
          rewrite <- Ea. eapply ord_lt_le_trans; [ apply addOrd_increasing; exact Hc2z | apply Hprin; auto ].
        + rewrite EN. apply NestLe; [ exact HN | apply lead_gt_ilt; auto | ].
          assert (Hc2le : BS_denote c2 ≤ z).
          { destruct r2 as [|e3 c3 r3]; simpl in HKendK.
            - destruct HKendK as [[_ H]|[_ H]]; auto. rewrite H. apply (Hinf 1%nat).
            - apply ord_lt_le, HKendK. }
          assert (Hsum : BS_denote (BS_add c c2) ≤ z).
          { rewrite <- Ea. rewrite <- (Hprin _ Hcz). apply addOrd_monotone; [ reflexivity | exact Hc2le ]. }
          unfold N. destruct r2 as [|e3 c3 r3].
          * left. split; auto.
          * simpl in HKendK. destruct HKendK as [_ [Hc2z HKr3]].
            split; [ exact HKe | split; [ | exact HKr3 ] ].
            rewrite <- Ea. eapply ord_lt_le_trans; [ apply addOrd_increasing; exact Hc2z | apply Hprin; auto ].
      - (* lead(K') > e: absorption with a smaller R-part *)
        assert (Hgt : lead_gt (BIC e2 c2 r2) e) by exact Hcmp.
        assert (HA : ABSw (BIC e2 c2 r2)).
        { apply (IHU (BI_denote (BIC e2 c2 r2))); auto using ble_refl.
          apply blt_le_trans with (BI_denote R); auto. }
        split.
        + intro H.
          assert (Eabs := absorb_enum e c _ HP HK' Hgt (ABSw_ABS _ HK' Hgt HA) w Hw).
          fold z in Eabs. rewrite Eabs.
          destruct (absorb_max_spec e c HP) as [Hm [Hmin _]].
          destruct (BS_offset_correct _ HK' (lead_gt_big _ Hgt) _ Hm) as [Nt [_ [Htt Hleast]]].
          assert (Hmz : BS_denote (absorb_max e c) < z) by (apply (Kge_lt _ _ _ (Kin_Kge _ _ Hmin) HK)).
          assert (Htz : BS_denote (absorb_offset e c (BIC e2 c2 r2)) < z).
          { eapply ord_lt_le_trans; [ exact Htt | apply Hleast; auto ]. }
          eapply ord_le_trans; [ | exact H ].
          apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam _))). apply Hprin; auto.
        + apply bphi_le_fix; auto using onePlus_normal, BI_good. apply HA; auto. }
    (* now the components of P + R *)
    destruct (cover R HR (proj2 notation_KHI R HR)) as [CS CF].
    assert (HIw := proj1 notation_KHI w Hw).
    destruct HfixP as [_ [HP2 HP3]].
    destruct Hfix as [Hf1 [Hf2 Hf3]].
    split; [ exact Hf1 | split ].
    - intro a.
      change (BI_denote (BIC e c R)) with
        (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) in a |- *.
      destruct (badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) a)
        as [[a' E]|[b E]]; rewrite E.
      + destruct (badd_small_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero a') as [k Ek].
        specialize (HP2 k). change (BI_denote (BIC e c BIZ)) with
          (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero) in HP2.
        rewrite Ek in HP2. exact HP2.
      + destruct (CS b) as [K' [HK' [_ [_ [_ [Hlo [b' Hup]]]]]]].
        assert (HK'z : PHI K' z ≤ z).
        { eapply ord_le_trans; [ | exact (Hf2 b') ].
          apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_small _ (BI_bfam R) b'))); auto. }
        assert (Hblt : blt (BI_denote K') (BI_denote R)) by (apply (bsub_child_blt _ _ (inl b')); auto).
        assert (HfK := bfix_of_fix _ onePlus_normal _ z (BI_good K') (BI_bfam K') Hzc HK'z).
        eapply ord_le_trans; [ | apply (proj1 (Hcls K' HK' Hblt HfK)); exact HK'z ].
        apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam (BIC e c K')))).
        apply bsub_badd_r; auto.
    - intro d.
      change (BI_denote (BIC e c R)) with
        (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) in d |- *.
      destruct (badd_big_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) d)
        as [[d' E]|[d' E]]; rewrite E.
      + destruct (badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero d') as [k Ek].
        specialize (HP3 k). change (BI_denote (BIC e c BIZ)) with
          (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero) in HP3.
        rewrite Ek in HP3. exact HP3.
      + destruct (CF d' w Hw HIw) as [K' [HK' [_ [_ [_ [Hlo [d'' Hup]]]]]]].
        fold z in Hlo, Hup.
        assert (Hmem := bfix_member _ onePlus_normal _ d'' z (BI_good R) (BI_bfam R) Hzc (Hf3 d'')).
        assert (HfK := bfix_bsub _ onePlus_normal _ _ z Hup (bfam_big _ (BI_bfam R) d'' z) Hmem).
        assert (Hblt : blt (BI_denote K') (BI_denote R)) by (apply (bsub_child_blt _ _ (inr (d'', z))); auto).
        eapply ord_le_trans; [ | apply (proj2 (Hcls K' HK' Hblt HfK)) ].
        apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam (BIC e c K')))).
        apply bsub_badd_r; auto.
  Qed.

  (** Absorption, unconditionally. *)
  Theorem absorb : forall R, BI_nf R -> lead_gt R e -> forall y, BS_nf y ->
    PHI (BIC e c R) (BS_denote y) ≈ PHI R (BS_denote (absorb_offset e c R) + BS_denote y).
  Proof.
    intros R HR HRe. apply absorb_enum; auto.
    apply ABSw_ABS; auto. apply (ABS_all (BI_denote R)); auto using ble_refl.
  Qed.
End abs_all.

(** Example: the index 1 + Ω (= Ω^0·1 + Ω) absorbs into Ω with offset 0,
    since ε₀ = φ_Ω(0) already exceeds 1: φ_{1+Ω}(y) = φ_Ω(0 + y). *)
Example absorb_offset_one_Ω : absorb_offset BIZ BS_one BI_Ω = BZ.
Proof. reflexivity. Qed.

(** With coefficient ε₀ = φ_Ω(0) the threshold is ε₀ itself, so the offset
    is 1: φ_{ε₀+Ω}(y) = φ_Ω(1 + y). *)
Example absorb_offset_eps0_Ω : absorb_offset BIZ (BN BI_Ω BZ) BI_Ω = BS_succ BZ.
Proof. reflexivity. Qed.
