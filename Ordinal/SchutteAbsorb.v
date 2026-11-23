From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.

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

Open Scope ord_scope.

(** * Absorption of Schütte columns

A column (b,a) followed by a strictly higher column (β,α) is absorbed:
the higher column built over [schutte_column P b a] enumerates a final
segment of what it enumerates over P, namely the part above a.  This
file proves that fact constructively, for ordinals, in terms of the
critical predicates [schutte_critical]; the actual offset of the shift
is supplied by the caller (it is computed on notations).  It also
proves that adjacent columns of equal height merge.

Main results:
- [schutte_column_merge]: (c,a),(c,a') ↦ (c, a + a').
- [absorb_critical]: in the principal regime, the critical points of
  (β,α) over [schutte_column P b a] are those over P that exceed a.
- [absorb_shift]: hence the column over [schutte_column P b a] is the
  column over P shifted by the least argument whose value exceeds a. *)

Local Hint Resolve
  schutte_column_normal
  schutte_column_normal_arg
  schutte_column_monotone
  schutte_column_inflationary1
  schutte_column_inflationary2
  schutte_column_nonzero
  normal_inflationary
  normal_complete
  normal_monotone
  addOrd_complete
  succ_complete
  zero_complete
  complete_subord
  ord_le_refl
  zero_least
  : core.

Lemma addOrd_lt_cases' t y a : a < t + y -> a < t \/ exists j:y, a ≤ t + y j.
Proof.
  rewrite addOrd_unfold. intro H. apply lub_lt in H. destruct H as [H|H]; [ left; auto | right ].
  apply sup_lt in H. destruct H as [j Hj]. exists j.
  rewrite ord_lt_unfold in Hj. destruct Hj as [[] Hj]. exact Hj.
Qed.

Lemma col_normal_mono f : normal_function f -> forall a b, a ≤ b -> f a ≤ f b.
Proof. intros Hf a b H. apply normal_monotone; auto. Qed.

Local Hint Resolve col_normal_mono : core.

(** A column at height 0 is a translation of its base. *)
Lemma col0 P a x : normal_function P -> schutte_column P 0 a x ≈ P (a + x).
Proof. intros. apply schutte_column0. Qed.

(** Columns respect pointwise inequality of normal bases. *)
Lemma col_base_le f g β α x :
  normal_function f -> normal_function g ->
  (forall y, complete y -> f y ≤ g y) ->
  complete β -> complete α -> complete x ->
  schutte_column f β α x ≤ schutte_column g β α x.
Proof. intros. apply schutte_column_monotone_func'; auto. Qed.

(** The fixpoint clause, specialised: values of (β,α) are fixed by
    [schutte_column P β a] for a < α. *)
Lemma col_value_fix P β α a x :
  normal_function P -> complete β -> complete α -> complete a -> complete x ->
  0 < β -> a < α ->
  schutte_column P β a (schutte_column P β α x) ≤ schutte_column P β α x.
Proof.
  intros HP Hβ Hα Ha Hx Hβ0 Hlt.
  rewrite <- (schutte_column_fixpoint β α x P 0 a) at 2; auto.
  rewrite schutte_column0. apply normal_monotone; auto.
  rewrite addOrd_zero_r. reflexivity.
Qed.

(** * Merging equal heights *)

Theorem schutte_column_merge_le : forall c x y a P,
  normal_function P -> complete c -> complete a -> complete x -> complete y ->
  schutte_column (schutte_column P c a) c x y ≤ schutte_column P c (a + x) y.
Proof.
  intros c x. induction x as [x IHx] using ordinal_induction.
  intro y. induction y as [y IHy] using ordinal_induction.
  intros a P HP Hc Ha Hx Hy.
  assert (HQ : normal_function (schutte_column P c a)) by auto.
  set (V := schutte_column P c (a + x) y).
  assert (HV : complete V) by (apply normal_complete; auto).
  rewrite schutte_column_unroll. apply lub_least.
  - (* the base term *)
    destruct (complete_zeroDec x Hx) as [Hx0|Hx0].
    + unfold V. transitivity (schutte_column P c a y).
      * apply normal_monotone; auto. transitivity (0 + y); [ apply addOrd_monotone; auto with ord | ].
        apply addOrd_zero_l.
      * apply schutte_column_monotone; auto. apply addOrd_le1.
    + destruct (complete_zeroDec c Hc) as [Hc0|Hc0].
      * unfold V.
        rewrite (schutte_column_monotoneβ c 0) by auto.
        rewrite schutte_column0.
        transitivity (schutte_column P 0 (a + x) y).
        2: { apply schutte_column_monotoneβ; auto with ord. }
        rewrite schutte_column0. apply normal_monotone; auto.
        rewrite addOrd_assoc. reflexivity.
      * transitivity (schutte_column P c a V).
        { apply normal_monotone; auto.
          unfold V. rewrite <- (schutte_column_le_f c (a + x) y P); auto.
          transitivity (a + x + y); [ apply addOrd_monotone; [ apply addOrd_le2 | reflexivity ] | ].
          apply normal_inflationary; auto. }
        unfold V. apply col_value_fix; auto.
        rewrite <- (addOrd_zero_r a) at 1. apply addOrd_increasing; auto.
  - apply sup_least; intro b4. apply sup_least; intro a4.
    apply normal_fix_least; auto.
    + apply limit_least. intro i.
      eapply ord_le_lt_trans; [ apply IHy; auto with ord | ].
      apply schutte_column_increasing; auto with ord.
    + transitivity (schutte_column (schutte_column P c (a + x a4)) (c b4) V 0).
      * apply col_base_le; auto.
        intros w Hw. apply IHx; auto with ord.
      * unfold V. apply schutte_column_fixpoint; auto with ord.
        apply addOrd_increasing; auto with ord.
Qed.

(** * Additively principal ordinals and the principal regime *)

Definition principal (z:Ord) : Prop := forall c, c < z -> c + z ≤ z.

Lemma principal_eq z z' : z ≈ z' -> principal z -> principal z'.
Proof.
  intros E H c Hc. transitivity (c + z); [ apply addOrd_monotone; [ reflexivity | apply E ] | ].
  transitivity z; [ apply H; rewrite E; exact Hc | apply E ].
Qed.

(** z with φ_z(0) ≤ z at height 1 over any normal base is principal. *)
Lemma principal_of_col1 P z : normal_function P -> complete z ->
  schutte_column P 1 z 0 ≤ z -> principal z.
Proof.
  intros HP Hz H c Hc. rewrite ord_lt_unfold in Hc. destruct Hc as [i Hi].
  transitivity (z i + z); [ apply addOrd_monotone; auto | ].
  transitivity (schutte_column P 1 (z i) z).
  { transitivity (P (z i + z)); [ apply normal_inflationary; auto | apply schutte_column_le_f; auto ]. }
  transitivity (schutte_column P 1 (z i) (schutte_column P 1 z 0)).
  { apply schutte_column_monotone; auto. }
  rewrite col_value_fix; auto with ord.
Qed.

(** A fixpoint of [schutte_column P b · 0] is fixed by every
    [schutte_column P b a] with a below it. *)
Lemma col_fix_below P b a z : normal_function P -> complete b -> complete a -> complete z ->
  0 < b -> schutte_column P b z 0 ≤ z -> a < z -> schutte_column P b a z ≤ z.
Proof.
  intros HP Hb Ha Hz Hb0 H Haz.
  transitivity (schutte_column P b a (schutte_column P b z 0)).
  { apply schutte_column_monotone; auto. }
  rewrite col_value_fix; auto.
Qed.

Lemma principal_succ a z : principal z -> 1 < z -> a < z -> succOrd a < z.
Proof.
  intros Hp H1 Ha.
  apply ord_le_lt_trans with (a + 1).
  { rewrite addOrd_succ. apply succ_monotone. rewrite addOrd_zero_r. reflexivity. }
  eapply ord_lt_le_trans; [ apply addOrd_increasing; exact H1 | apply Hp; auto ].
Qed.

Lemma fix_gt1 P z : normal_function P -> complete z -> P z ≤ z -> 1 < z.
Proof.
  intros HP Hz H.
  assert (H1 : 1 + z ≤ z) by (rewrite <- H at 2; apply onePlus_least_normal; auto).
  assert (H0 : 1 ≤ z) by (rewrite <- H1; apply addOrd_le1).
  eapply ord_lt_le_trans; [ | exact H1 ].
  apply ord_lt_le_trans with (1 + 1).
  { rewrite <- (addOrd_zero_r 1) at 1. apply addOrd_increasing. apply succ_lt. }
  apply addOrd_monotone; auto.
Qed.

(** Fixpoints of P are principal. *)
Definition Prin (P:Ord -> Ord) : Prop := forall z, complete z -> P z ≤ z -> principal z.

(** The principal regime for a column at height β over P. *)
Definition Reg (P:Ord -> Ord) (β:Ord) : Prop := Prin P \/ 1 < β.

Lemma crit_base P β α z : normal_function P -> complete β -> complete α -> complete z ->
  0 < β -> 0 < α -> schutte_critical P β α z -> P z ≤ z.
Proof.
  intros HP Hβ Hα Hz Hβ0 Hα0 H.
  destruct (H 0 0 zero_complete zero_complete Hβ0 Hα0) as [H1 _].
  transitivity (schutte_column (schutte_column P β 0) 0 z 0); [ | exact H1 ].
  transitivity (schutte_column P β 0 (z + 0)); [ | apply schutte_column0 ].
  transitivity (P (0 + (z + 0))); [ | apply schutte_column_le_f; auto ].
  apply normal_monotone; auto. rewrite addOrd_zero_l, addOrd_zero_r. reflexivity.
Qed.

Lemma crit_principal P β α z : normal_function P -> complete β -> complete α -> complete z ->
  Reg P β -> 0 < β -> 0 < α -> schutte_critical P β α z -> principal z.
Proof.
  intros HP Hβ Hα Hz Hreg Hβ0 Hα0 H.
  destruct Hreg as [Hpr|H1].
  - apply Hpr; auto. apply (crit_base P β α); auto.
  - apply (principal_of_col1 P); auto.
    destruct (H 1 0 (succ_complete _ zero_complete) zero_complete H1 Hα0) as [H2 _].
    rewrite <- H2 at 2. apply col_base_le; auto.
    intros y Hy. apply (schutte_column_arg0 β y P); auto.
Qed.

Lemma crit_value P β α x : normal_function P -> complete β -> complete α -> complete x ->
  0 < β -> 0 < α -> schutte_critical P β α (schutte_column P β α x).
Proof.
  intros. apply (enumerates_included _ _ (schutte_column_enumerates P β α H H0 H1 H3 H4)); auto.
Qed.

(** A common upper bound below β for two ordinals below a complete β. *)
Lemma below_join β b b' : complete β -> b < β -> b' < β ->
  exists c, complete c /\ b ≤ c /\ b' ≤ c /\ c < β.
Proof.
  intros Hβ Hb Hb'. rewrite ord_lt_unfold in Hb, Hb'.
  destruct Hb as [i Hi]. destruct Hb' as [j Hj].
  destruct β as [B g]. destruct Hβ as [Hdir [_ Hc]].
  destruct (Hdir i j) as [k [Hk1 Hk2]].
  exists (g k). split; [ apply Hc | split; [ rewrite Hi; auto | split; [ rewrite Hj; auto | apply (index_lt (ord B g)) ] ] ].
Qed.

(** * Absorption: critical points *)

(** (⇐) In the principal regime, a critical point of (β,α) over P that
    is principal and lies above a is also critical over
    [schutte_column P b a], for any b < β.  By induction on β, then α;
    the shift bound [UB] for smaller α keeps the lower columns under
    control, and equal heights are reduced to [schutte_column_merge_le]
    through a common upper bound below β (no comparison of heights is
    needed). *)
Theorem absorb_critical : forall β, complete β -> forall α, complete α -> forall P b a z,
  normal_function P -> complete b -> complete a -> complete z ->
  b < β -> Reg P β -> principal z -> 1 < z -> a < z ->
  schutte_critical P β α z -> schutte_critical (schutte_column P b a) β α z.
Proof.
  intros β. induction β as [β IHβ] using ordinal_induction. intros Hβ α.
  induction α as [α IHα] using ordinal_induction.
  intros Hα P b a z HP Hb Ha Hz Hbβ Hreg Hpz H1z Haz Hcrit.
  assert (Hβ0 : 0 < β) by (apply ord_le_lt_trans with b; auto with ord).
  assert (Hz0 : 0 < z) by (apply ord_le_lt_trans with 1; auto with ord).
  set (Q := schutte_column P b a).
  assert (HQ : normal_function Q) by (unfold Q; auto).
  intros b' a' Hb' Ha' Hb'β Ha'α.
  assert (Hα0 : 0 < α) by (apply ord_le_lt_trans with a'; auto with ord).
  split; [ | apply schutte_column_inflationary1; auto ].
  destruct (complete_zeroDec a' Ha') as [Ha'0|Ha'0].
  - (* a' = 0: compare with the merged column at a common height c *)
    destruct (below_join β b b' Hβ Hbβ Hb'β) as [c [Hc [Hbc [Hb'c Hcβ]]]].
    transitivity (schutte_column Q b' z 0).
    { apply col_base_le; auto. intros y Hy.
      transitivity (schutte_column Q β 0 y); [ apply schutte_column_monotone; auto | apply schutte_column_arg0; auto ]. }
    transitivity (schutte_column (schutte_column P c a) c z 0).
    { apply schutte_column_monotone_full; auto. intro y. unfold Q. apply schutte_column_monotoneβ; auto. }
    transitivity (schutte_column P c (a + z) 0); [ apply schutte_column_merge_le; auto | ].
    transitivity (schutte_column P c z 0); [ apply schutte_column_monotone; auto | ].
    destruct (Hcrit c 0 Hc zero_complete Hcβ Hα0) as [H _].
    transitivity (schutte_column (schutte_column P β 0) c z 0); [ | exact H ].
    apply col_base_le; auto. intros y Hy. apply schutte_column_arg0; auto.
  - (* a' > 0 *)
    assert (Hka : succOrd a < z) by (apply principal_succ; auto).
    (* the shift bound for (β,a') *)
    assert (UB : forall y, complete y -> schutte_column Q β a' y ≤ schutte_column P β a' (succOrd a + y)).
    { intro y. induction y as [y IHy] using ordinal_induction. intro Hy.
      set (v := schutte_column P β a' (succOrd a + y)).
      assert (Hv : complete v) by (unfold v; auto).
      assert (Hcv : schutte_critical P β a' v) by (apply crit_value; auto).
      apply (enumerates_least _ _ (schutte_column_enumerates Q β a' HQ Hβ Ha' Hβ0 Ha'0)); auto.
      - apply (IHα a' Ha'α Ha' P b a v); auto.
        + apply (crit_principal P β a'); auto.
        + apply (fix_gt1 P); auto. apply (crit_base P β a'); auto.
        + apply ord_lt_le_trans with (succOrd a); [ apply succ_lt | ]. unfold v.
          transitivity (succOrd a + y); [ apply addOrd_le1 | apply schutte_column_inflationary2; auto ].
      - intros y' Hy'. rewrite ord_lt_unfold in Hy'. destruct Hy' as [i Hi].
        apply ord_le_lt_trans with (schutte_column Q β a' (y i)); [ apply schutte_column_monotone; auto | ].
        eapply ord_le_lt_trans; [ apply IHy; auto with ord | ].
        unfold v. apply schutte_column_increasing; auto. apply addOrd_increasing, index_lt. }
    destruct (complete_zeroDec b' Hb') as [Hb'0|Hb'0].
    + (* b' = 0 *)
      transitivity (schutte_column (schutte_column Q β a') 0 z 0); [ apply schutte_column_monotoneβ; auto | ].
      rewrite schutte_column0.
      transitivity (schutte_column Q β a' z); [ apply schutte_column_monotone; auto; rewrite addOrd_zero_r; reflexivity | ].
      transitivity (schutte_column P β a' (succOrd a + z)); [ apply UB; auto | ].
      transitivity (schutte_column P β a' z); [ apply schutte_column_monotone; auto | ].
      destruct (Hcrit 0 a' zero_complete Ha' Hβ0 Ha'α) as [H _].
      transitivity (schutte_column (schutte_column P β a') 0 z 0); [ | exact H ].
      rewrite schutte_column0. apply schutte_column_monotone; auto. rewrite addOrd_zero_r. reflexivity.
    + (* b' > 0: a 0-column over P' = (β,a') absorbed at height b' *)
      set (P' := schutte_column P β a').
      assert (HP' : normal_function P') by (unfold P'; auto).
      transitivity (schutte_column (schutte_column P' 0 (succOrd a)) b' z 0).
      { apply col_base_le; auto. intros y Hy. rewrite schutte_column0. apply UB; auto. }
      destruct (Hcrit b' a' Hb' Ha' Hb'β Ha'α) as [Hsc _].
      assert (Hsup : schutte_supercritical P' b' z).
      { apply schutte_supercritical_alt; auto. split; [ exact Hsc | apply schutte_column_inflationary1; auto ]. }
      destruct Hsup as [_ Hcz].
      assert (Hres : schutte_critical (schutte_column P' 0 (succOrd a)) b' z z).
      { apply (IHβ b' Hb'β Hb' z Hz P' 0 (succOrd a) z); auto.
        left. intros w Hw Hfw.
        apply principal_eq with (P' w); [ split; [ exact Hfw | apply normal_inflationary; auto ] | ].
        unfold P'. apply (crit_principal P β a'); auto. apply crit_value; auto. }
      assert (Hsup' : schutte_supercritical (schutte_column P' 0 (succOrd a)) b' z) by (split; auto).
      apply (schutte_supercritical_alt _ b' z) in Hsup'; auto. apply Hsup'.
Qed.

Lemma col_ge_base P b a y : normal_function P -> P y ≤ schutte_column P b a y.
Proof.
  intro HP. transitivity (P (a + y)); [ apply normal_monotone; auto; apply addOrd_le2 | ].
  apply schutte_column_le_f; auto.
Qed.

(** (⇒) Critical points over [schutte_column P b a] are critical over P
    and lie above a. *)
Lemma absorb_critical_inv P β α b a z :
  normal_function P -> complete β -> complete α -> complete b -> complete a -> complete z ->
  0 < β -> 0 < α ->
  schutte_critical (schutte_column P b a) β α z -> schutte_critical P β α z /\ a < z.
Proof.
  intros HP Hβ Hα Hb Ha Hz Hβ0 Hα0 H. split.
  - intros b' a' Hb' Ha' Hb'β Ha'α. split; [ | apply schutte_column_inflationary1; auto ].
    destruct (H b' a' Hb' Ha' Hb'β Ha'α) as [H1 _]. rewrite <- H1 at 2.
    apply col_base_le; auto. intros y Hy.
    apply col_base_le; auto. intros w Hw. apply col_ge_base; auto.
  - assert (HQz := crit_base _ β α z (schutte_column_normal b a P Hb Ha HP) Hβ Hα Hz Hβ0 Hα0 H).
    assert (Hz0 : 0 < z) by (eapply ord_lt_le_trans; [ apply (normal_nonzero _ (schutte_column_normal b a P Hb Ha HP) z) | exact HQz ]).
    apply ord_lt_le_trans with (a + z).
    { apply ord_le_lt_trans with (a + 0); [ rewrite addOrd_zero_r; reflexivity | apply addOrd_increasing; auto ]. }
    transitivity (schutte_column P b a z); [ | exact HQz ].
    transitivity (P (a + z)); [ apply normal_inflationary; auto | apply schutte_column_le_f; auto ].
Qed.

(** * Absorption as a shift *)

Section absorb_shift.
  Variables (P:Ord -> Ord) (β α b a s : Ord).
  Hypothesis HP : normal_function P.
  Hypotheses (Hβ : complete β) (Hα : complete α) (Hb : complete b) (Ha : complete a) (Hs : complete s).
  Hypothesis Hbβ : b < β.
  Hypothesis Hα0 : 0 < α.
  Hypothesis Hreg : Reg P β.
  (** s is the least argument whose value exceeds a. *)
  Hypothesis Hs1 : a < schutte_column P β α s.
  Hypothesis Hs2 : forall z, complete z -> schutte_critical P β α z -> a < z -> schutte_column P β α s ≤ z.

  Theorem absorb_shift : forall x, complete x ->
    schutte_column (schutte_column P b a) β α x ≈ schutte_column P β α (s + x).
  Proof.
    assert (Hβ0 : 0 < β) by (apply ord_le_lt_trans with b; auto with ord).
    set (Q := schutte_column P b a).
    assert (HQ : normal_function Q) by (unfold Q; auto).
    assert (EQ := schutte_column_enumerates Q β α HQ Hβ Hα Hβ0 Hα0).
    assert (EP := schutte_column_enumerates P β α HP Hβ Hα Hβ0 Hα0).
    intro x. induction x as [x IH] using ordinal_induction. intro Hx.
    split.
    - set (v := schutte_column P β α (s + x)).
      assert (Hv : complete v) by (unfold v; auto).
      assert (Hcv : schutte_critical P β α v) by (apply crit_value; auto).
      apply (enumerates_least _ _ EQ); auto.
      + apply absorb_critical; auto.
        * apply (crit_principal P β α); auto.
        * apply (fix_gt1 P); auto. apply (crit_base P β α); auto.
        * eapply ord_lt_le_trans; [ exact Hs1 | ]. unfold v. apply schutte_column_monotone; auto. apply addOrd_le1.
      + intros y Hy. rewrite ord_lt_unfold in Hy. destruct Hy as [i Hi].
        apply ord_le_lt_trans with (schutte_column Q β α (x i)); [ apply schutte_column_monotone; auto | ].
        rewrite (IH (x i) (index_lt _ _) (complete_subord _ Hx i)).
        unfold v. apply schutte_column_increasing; auto. apply addOrd_increasing, index_lt.
    - set (w := schutte_column Q β α x).
      assert (Hw : complete w) by (unfold w; auto).
      destruct (absorb_critical_inv P β α b a w HP Hβ Hα Hb Ha Hw Hβ0 Hα0
                  (enumerates_included _ _ EQ x Hx)) as [Hcw Haw].
      apply (enumerates_least _ _ EP); auto.
      intros y Hy. destruct (addOrd_lt_cases' _ _ _ Hy) as [Hy1|[j Hj]].
      + eapply ord_lt_le_trans; [ apply (schutte_column_increasing β α s y P); auto | apply Hs2; auto ].
      + apply ord_le_lt_trans with (schutte_column P β α (s + x j)); [ apply schutte_column_monotone; auto | ].
        rewrite <- (IH (x j) (index_lt _ _) (complete_subord _ Hx j)).
        unfold w. apply schutte_column_increasing; auto with ord.
  Qed.
End absorb_shift.

(** * Merging equal heights: the other direction *)

Theorem schutte_column_merge_ge : forall c x y a P,
  normal_function P -> complete c -> complete a -> complete x -> complete y ->
  schutte_column P c (a + x) y ≤ schutte_column (schutte_column P c a) c x y.
Proof.
  intros c x. induction x as [x IHx] using ordinal_induction.
  intro y. induction y as [y IHy] using ordinal_induction.
  intros a P HP Hc Ha Hx Hy.
  assert (HQ : normal_function (schutte_column P c a)) by auto.
  set (W := schutte_column (schutte_column P c a) c x y).
  assert (HW : complete W) by (apply normal_complete; auto).
  assert (HWb : schutte_column P c a (x + y) ≤ W) by (apply schutte_column_le_f; auto).
  destruct (complete_zeroDec x Hx) as [Hx0|Hx0].
  { transitivity (schutte_column P c a y).
    - apply schutte_column_monotone; auto. rewrite Hx0. rewrite addOrd_zero_r. reflexivity.
    - rewrite <- HWb. apply schutte_column_monotone; auto. apply addOrd_le2. }
  rewrite schutte_column_unroll. apply lub_least.
  - rewrite <- HWb. rewrite <- schutte_column_le_f; auto.
    apply normal_monotone; auto. rewrite addOrd_assoc. reflexivity.
  - apply sup_least; intro b4. apply sup_least; intro a4.
    apply normal_fix_least; auto.
    + apply limit_least. intro i.
      eapply ord_le_lt_trans; [ apply IHy; auto with ord | ].
      apply schutte_column_increasing; auto with ord.
    + assert (Ha4 : complete ((a + x) a4)) by (apply complete_subord; auto).
      assert (Hb4 : complete (c b4)) by auto.
      assert (Hc0 : 0 < c) by (apply ord_le_lt_trans with (c b4); auto with ord).
      destruct (addOrd_lt_cases' a x ((a + x) a4) (index_lt _ a4)) as [H|[j Hj]].
      * (* below a: W is a value of [schutte_column P c a] *)
        assert (HfixW : schutte_column P c a W ≤ W).
        { transitivity (schutte_column (schutte_column P c a) c 0 W).
          - apply (schutte_column_arg0 c W (schutte_column P c a)); auto.
          - unfold W. apply col_value_fix; auto. }
        transitivity (schutte_column (schutte_column P c ((a + x) a4)) (c b4) (schutte_column P c a W) 0).
        { apply schutte_column_monotone; auto. }
        rewrite <- HfixW at 2. apply schutte_column_fixpoint; auto with ord.
      * transitivity (schutte_column (schutte_column P c (a + x j)) (c b4) W 0).
        { apply schutte_column_monotone_full; auto. }
        transitivity (schutte_column (schutte_column (schutte_column P c a) c (x j)) (c b4) W 0).
        { apply col_base_le; auto. intros w Hw. apply IHx; auto with ord. }
        unfold W. apply schutte_column_fixpoint; auto with ord.
Qed.

Corollary schutte_column_merge c x y a P :
  normal_function P -> complete c -> complete a -> complete x -> complete y ->
  schutte_column (schutte_column P c a) c x y ≈ schutte_column P c (a + x) y.
Proof. intros. split; [ apply schutte_column_merge_le | apply schutte_column_merge_ge ]; auto. Qed.

(** * The low regime: a height-1 column over a translation

Over the base y ↦ d + y, with ω^m ≤ d < ω^(m+1), the Veblen functions
of positive index are those of 1 + y shifted in index by m: the first
fixpoints of d + · are ω^(m+1) + y.  This is the case excluded by
[absorb_critical] (d + · is not [Prin], and β = 1). *)

Lemma low_regime_veblen : forall e y d m,
  complete d -> complete m -> complete e -> complete y -> 0 < e ->
  expOrd ω m ≤ d -> d < expOrd ω (succOrd m) ->
  veblen (addOrd d) e y ≈ expOrd ω (m + e) + y.
Proof.
  assert (Hω : complete ω) by apply omega_complete.
  intros e. induction e as [e IHe] using ordinal_induction.
  intro y. induction y as [y IHy] using ordinal_induction.
  intros d m Hd Hm He Hy He0 Hmd Hdm.
  assert (Hd0 : 0 < d) by (eapply ord_lt_le_trans; [ apply expOrd_nonzero | exact Hmd ]).
  assert (Hdn : normal_function (addOrd d)) by (apply normal_addOrd; auto).
  assert (Hme : complete (m + e)) by auto.
  assert (Hdlt : d < expOrd ω (m + e)).
  { eapply ord_lt_le_trans; [ exact Hdm | apply expOrd_monotone ].
    transitivity (succOrd (m + 0)); [ apply succ_monotone; rewrite addOrd_zero_r; reflexivity | ].
    rewrite <- addOrd_succ. apply addOrd_monotone; [ reflexivity | apply succ_least; exact He0 ]. }
  split.
  - rewrite veblen_unroll. apply lub_least.
    + apply addOrd_monotone; [ apply ord_lt_le; exact Hdlt | reflexivity ].
    + apply sup_least; intro i.
      assert (Hi : complete (e i)) by auto.
      set (V := expOrd ω (m + e) + y).
      assert (HV : complete V) by (unfold V; apply addOrd_complete; auto using expOrd_complete, omega_gt0).
      apply normal_fix_least; auto.
      * apply veblen_normal; auto.
      * apply limit_least. intro j.
        rewrite (IHy (y j) (index_lt _ _) d m); auto with ord.
        apply addOrd_increasing, index_lt.
      * destruct (complete_zeroDec (e i) Hi) as [Hi0|Hi0].
        -- transitivity (veblen (addOrd d) 0 V); [ apply veblen_monotone_first; auto with ord | ].
           rewrite veblen_zero. unfold V. rewrite addOrd_assoc.
           apply addOrd_monotone; [ | reflexivity ].
           apply additively_closed_collapse; auto using expOmega_additively_closed.
        -- rewrite (IHe (e i) (index_lt _ _) V d m); auto.
           unfold V. rewrite addOrd_assoc. apply addOrd_monotone; [ | reflexivity ].
           apply expOrd_add_collapse; auto.
           apply addOrd_increasing, index_lt.
  - (* compare with the Veblen hierarchy of 1 + y from index m *)
    assert (H1 : normal_function (addOrd 1)) by apply onePlus_normal.
    transitivity (veblen (addOrd 1) (m + e) y); [ apply veblen_onePlus; auto | ].
    rewrite <- (schutte_column_veblen (m + e) y (addOrd 1)); auto.
    rewrite <- (schutte_column_veblen e y (addOrd d)); auto.
    rewrite <- schutte_column_merge; auto with ord.
    apply col_base_le; auto with ord.
    intros w Hw. rewrite schutte_column_veblen; auto.
    rewrite veblen_onePlus; auto. apply addOrd_monotone; auto.
Qed.
