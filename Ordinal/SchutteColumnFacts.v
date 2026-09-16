From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import NArith.
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
From Ordinal Require Import Reflection.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import AckermannTower.
From Ordinal Require Import SchutteColumn.

Open Scope ord_scope.

Local Hint Resolve
  schutte_column_monotone
  schutte_column_inflationary1
  schutte_column_inflationary2
  schutte_column_nonzero
  normal_inflationary
  normal_addOrd
  : core.

Lemma schutte_column_veblen:
  forall α x f,
    normal_function f ->
    complete α ->
    complete x ->
    schutte_column f 1 α x ≈ veblen f α x.
Proof.
  induction α as [α Hindα] using ordinal_induction.
  induction x as [x Hindx] using ordinal_induction.
  intros f Hf.
  split.
  - rewrite schutte_column_unroll.
    apply lub_least.
    + apply veblen_fax; auto.
    + simpl.
      apply sup_least. intros [].
      apply sup_least. intros a.
      apply normal_fix_least; auto with ord.
      * apply limit_least; intro i.
        rewrite Hindx; auto with ord.
        apply veblen_increasing; auto with ord.
      * rewrite schutte_column0.
        rewrite Hindα; auto with ord.
        rewrite <- (veblen_fixpoints f Hf a α) at 2; auto with ord.
        apply veblen_monotone; auto with ord.
        rewrite addOrd_zero_r. reflexivity.
  - rewrite veblen_unroll.
    apply lub_least.
    + rewrite schutte_column_unroll.
      rewrite <- lub_le1; auto with ord.
    + apply sup_least; intro a.
      apply normal_fix_least; auto with ord.
      * apply limit_least. intro i.
        rewrite <- Hindx; auto with ord.
        apply normal_increasing; auto with ord.
      * rewrite <- (schutte_column_fixpoint 1 α x f 0 a) at 2; auto with ord.
        rewrite schutte_column0.
        rewrite <- Hindα; auto with ord.
Qed.

Lemma schutte_column_add_closed:
  forall f β α x p q,
    normal_function f ->
    complete β ->
    complete α ->
    complete x ->
    1 < β ->
    0 < α ->
    p < schutte_column f β α x ->
    q < schutte_column f β α x ->
    p + q < schutte_column f β α x.
Proof.
  intros.
  rewrite <- (schutte_column_fixpoint β α x f 1 0); auto with ord.
  rewrite schutte_column_veblen; auto with ord.
  - apply ord_lt_le_trans with (veblen (addOrd 1) (schutte_column f β α x) 0).
    2: { apply veblen_monotone_func; auto with ord.
         intros; apply onePlus_least_normal; auto with ord. }
    rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r.
    apply expOmega_additively_closed; auto with ord.
    rewrite <- normal_inflationary; auto with ord.
    rewrite <- normal_inflationary; auto with ord.
Qed.

Lemma schutte_column_preserves_add_closed:
  forall f,
    normal_function f ->
    (forall x p q, complete x -> p < f x -> q < f x -> p + q < f x) ->
    (forall x β α p q,
        complete x ->
        complete β ->
        complete α ->
        p < schutte_column f β α x ->
        q < schutte_column f β α x ->
        p + q < schutte_column f β α x).
Proof.
  intros f Hf Hf2.
  intros x β α p q Hx Hβ Hα Hp Hq.
  destruct (complete_zeroDec β); auto.
  { assert (Heq: schutte_column f β α x ≈ f (α+x)).
    split.
    - transitivity (schutte_column f 0 α x); [ apply schutte_column_monotoneβ; auto with ord |].
      rewrite schutte_column0; auto with ord.
    - rewrite schutte_column_unroll; auto with ord.
    - rewrite Heq.
      rewrite Heq in Hp, Hq.
      apply Hf2; auto with ord. }
  destruct (complete_zeroDec α); auto.
  { assert (Heq: schutte_column f β α x ≈ f x).
    split.
    - transitivity (schutte_column f β 0 x); auto with ord.
      rewrite schutte_column_arg0; auto with ord.
    - rewrite schutte_column_unroll; auto with ord.
      rewrite <- lub_le1.
      apply normal_monotone; auto with ord.
    - rewrite Heq.
      rewrite Heq in Hp, Hq.
      apply Hf2; auto. }
  assert (Heq: schutte_column f β α x ≈ f (schutte_column f β α x)).
  { split.
    - apply normal_inflationary; auto with ord.
    - rewrite <- (schutte_column_fixpoint β α x f 0 0) at 2; auto with ord.
      rewrite schutte_column0.
      rewrite schutte_column_arg0; auto with ord. }
  rewrite Heq.
  rewrite Heq in Hp, Hq.
  apply Hf2; auto with ord.
Qed.

Definition schutte_critical f β α x :=
  forall b a,
    complete b ->
    complete a ->
    b < β ->
    a < α ->
    schutte_column (schutte_column f β a) b x 0 ≈ x.

Definition schutte_supercritical f β α :=
  α > 0 /\ schutte_critical f β α α.

Definition schutte_hypercritical f β :=
  β > 0 /\ schutte_critical f β 1 β.

Definition schutte_unreachable f E :=
  E > 0 /\
  (forall β α x,
      complete β ->
      complete α ->
      complete x ->
      β < E ->
      α < E ->
      x < E ->
      schutte_column f β α x < E).

Lemma schutte_supercritical_alt f β α:
  normal_function f ->
  complete β ->
  complete α ->
  0 < β ->
  schutte_supercritical f β α <-> schutte_column f β α 0 ≈ α.
Proof.
  intros Hf Hcβ Hcα Hβ.
  unfold schutte_supercritical, schutte_critical.
  split; intro H.
  - split; auto with ord.
    rewrite schutte_column_gt0; auto with ord.
    apply sup_least; intro b.
    apply sup_least; intro a.
    apply normal_fix_least; auto with ord.
    apply limit_least; intros [].
    apply H; auto with ord.
    intuition.
  - intros. split.
    { rewrite <- H; auto with ord. }
    intros. split; auto with ord.
    rewrite <- H at 2.
    rewrite <- (schutte_column_fixpoint β α 0 f b a); auto with ord.
Qed.

Lemma schutte_hypercritical_alt f β:
  normal_function f ->
  complete β ->
  schutte_hypercritical f β <-> schutte_column f β 1 0 ≈ β.
Proof.
  intros Hf Hcβ.
  unfold schutte_hypercritical.
  split; intro H.
  - destruct H as [H0 H].
    unfold schutte_critical in H.
    split.
    2: { apply normal_inflationary with (f := fun x => schutte_column f x 1 0); auto with ord. }
    rewrite schutte_column_gt0; auto with ord.
    apply sup_least; intro b.
    apply sup_least; intro a.
    apply normal_fix_least; auto with ord.
    + apply limit_least; intros [].
    + apply H; auto with ord.
  - split.
    { rewrite <- H.
      apply normal_nonzero; auto with ord. }
    hnf. intros; split; auto with ord.
    rewrite <- H at 3.
    rewrite <- (schutte_column_fixpoint β 1 0 f b a); auto with ord.
    apply schutte_column_monotone; auto with ord.
    apply H.
Qed.

Lemma schutte_column_enumerates f β α:
  normal_function f ->
  complete β ->
  complete α ->
  0 < β ->
  0 < α ->
  enumerates (schutte_column f β α) (schutte_critical f β α).
Proof.
  intros. unfold schutte_critical. constructor; auto with ord.
  + intros. split; auto with ord.
    apply schutte_column_fixpoint; auto with ord.
  + apply normal_increasing; auto with ord.
  + intros x z Hx Hz Hfix Hlt.
    rewrite schutte_column_unroll.
    apply lub_least.
    * rewrite ord_lt_unfold in H2.
      rewrite ord_lt_unfold in H3.
      destruct H2 as [b _].
      destruct H3 as [a _].
      rewrite <- (Hfix b a); auto with ord.
      rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      rewrite <- (addOrd_le2 a).
      rewrite addOrd_zero_r.
      rewrite addOrd_unfold.
      apply lub_least; auto with ord.
      ** rewrite ord_le_unfold; intro a'.
         rewrite <- (Hfix b a'); auto with ord.
         rewrite schutte_column_unroll.
         rewrite <- lub_le1.
         apply ord_le_lt_trans with (schutte_column f β a' 0); auto with ord.
         apply normal_increasing; auto with ord.
         rewrite addOrd_zero_r.
         rewrite <- (Hfix b a'); auto with ord.
      ** apply sup_least; intro i.
         apply succ_least.
         eapply ord_le_lt_trans; [ | apply (Hlt i); auto with ord ].
         rewrite schutte_column_unroll.
         rewrite <- lub_le1.
         apply normal_inflationary; auto with ord.
    * apply sup_least; intro b.
      apply sup_least; intro a.
      apply normal_fix_least; intros; auto with ord.
      ** apply limit_least. intro i.
         apply Hlt; auto with ord.
      ** apply Hfix; auto with ord.
Qed.

Lemma enum_supercritical f β :
  normal_function f ->
  complete β ->
  0 < β ->
  enumerates (enum_fixpoints (fun α => schutte_column f β α 0)) (schutte_supercritical f β).
Proof.
  intros Hf Hcβ Hβ.
  constructor; auto with ord.
  - intros. rewrite schutte_supercritical_alt; auto with ord.
    rewrite enum_are_fixpoints at 2; auto with ord.
  - intros; apply normal_increasing; auto with ord.
  - intros. apply enum_least; auto with ord.
    rewrite schutte_supercritical_alt in H1; auto with ord.
    apply H1.
Qed.

Lemma enum_hypercritical f:
  normal_function f ->
  enumerates (E_number f) (schutte_hypercritical f).
Proof.
  intro Hf.
  unfold E_number.
  constructor; auto with ord.
  - intros. rewrite schutte_hypercritical_alt; auto with ord.
    rewrite enum_are_fixpoints at 2; auto with ord.
  - intros; apply normal_increasing; auto with ord.
  - intros. apply enum_least; auto with ord.
    rewrite schutte_hypercritical_alt in H1; auto with ord.
    apply H1.
Qed.

Lemma schutte_column_unreachable:
    forall f b a x β α y,
      normal_function f ->
      complete b ->
      complete a ->
      complete β ->
      complete α ->
      complete y ->
      1 < β ->
      0 < α ->
      b < β ->
      a < schutte_column f β α y ->
      x < schutte_column f β α y ->
      schutte_column f b a x < schutte_column f β α y.
Proof.
  intros.
  destruct (complete_zeroDec b); auto.
  { apply ord_le_lt_trans with (f (a + x)).
    { rewrite schutte_column_unroll; apply lub_least; auto with ord.
      apply sup_least; intro b'.
      elim (zero_lt b').
      apply ord_lt_le_trans with b; auto with ord. }
    rewrite <- (schutte_column_fixpoint β α y f 0 0); auto with ord.
    rewrite schutte_column0.
    rewrite schutte_column_arg0; auto with ord.
    apply normal_increasing; auto with ord.
    rewrite addOrd_zero_r.
    apply schutte_column_add_closed; auto with ord.
    transitivity 1; auto with ord. }

  rewrite <- (schutte_column_fixpoint β α y f b 0); auto with ord.
  apply ord_lt_le_trans with (schutte_column f b (schutte_column f β α y) 0).
  2: { apply schutte_column_monotone_func; auto with ord.
       intro. rewrite schutte_column_arg0; auto with ord. }
  rewrite <- (schutte_column_fixpoint b _ 0 f 0 a); auto with ord.
  rewrite schutte_column0.
  apply schutte_column_increasing; auto with ord.
  apply addOrd_complete; auto with ord.
  rewrite addOrd_zero_r.
  apply ord_lt_le_trans with (schutte_column f β α y); auto with ord.
Qed.

Lemma schutte_column_unreachable_apex:
  forall f β α x b,
    normal_function f ->
    complete b ->
    complete α ->
    complete β ->
    1 < β ->
    b < β ->
    α < schutte_column f β 1 0 ->
    x < schutte_column f β 1 0 ->
    schutte_column f b α x < schutte_column f β 1 0.
Proof.
  intros. apply schutte_column_unreachable; auto with ord.
Qed.

Lemma schutte_column_fix_unreachable:
  forall E f β α x,
    normal_function f ->
    complete E ->
    complete β ->
    complete α ->
    schutte_column f E 1 0 ≤ E ->
    β < E ->
    α < E ->
    x < E ->
    schutte_column f β α x < E.
Proof.
  intros E f β α x Hf HE Hβ Hα Hfix HβE HαE HxE.
  rewrite <- Hfix.
  apply schutte_column_unreachable_apex; auto with ord.
  * rewrite <- Hfix.
    apply ord_le_lt_trans with (1+0).
    { rewrite addOrd_zero_r; auto with ord. }
    rewrite <- onePlus_least_normal with (f:=fun x => schutte_column f x 1 0); auto with ord.
    apply addOrd_increasing.
    rewrite <- Hfix.
    apply normal_nonzero; auto with ord.
  * apply ord_lt_le_trans with E; auto.
    apply normal_inflationary  with (f:=fun x => schutte_column f x 1 0); auto with ord.
  * apply ord_lt_le_trans with E; auto.
    apply normal_inflationary with (f:=fun x => schutte_column f x 1 0); auto with ord.
Qed.

Lemma unreachable_E_number:
  forall E f,
    complete E ->
    normal_function f ->
    schutte_unreachable f E ->
    schutte_column f E 1 0 ≤ E.
Proof.
  intros E f HE Hf [HE0 H].
  assert (HE1: 1 < E).
  { apply ord_le_lt_trans with (schutte_column f 0 0 0).
    apply succ_least.
    apply normal_nonzero.
    apply schutte_column_normal; auto with ord.
    apply H; auto with ord. }
  rewrite schutte_column_unroll.
  apply lub_least.
  - apply ord_lt_le.
    apply ord_le_lt_trans with (schutte_column f 0 1 0).
    rewrite schutte_column_unroll.
    apply lub_le1.
    apply H; auto with ord.
  - apply sup_least; intro b.
    apply sup_least; intros []. simpl.
    apply normal_fix_least; auto with ord.
    { apply limit_least; intros []. }
    transitivity (schutte_column f b E 0).
    { apply schutte_column_monotone_func; auto with ord.
      intros. rewrite schutte_column_arg0; auto with ord. }
    rewrite normal_ord_decompose with (f := fun x => schutte_column f b x 0); auto with ord.
    apply sup_least; intro i.
    apply ord_lt_le.
    apply H; auto with ord.
    apply ord_le_lt_trans with (i+1).
    { rewrite addOrd_succ.
      apply succ_monotone.
      rewrite addOrd_zero_r. auto with ord. }
    apply ord_le_lt_trans with (schutte_column f 1 i 1).
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    apply normal_inflationary; auto with ord.
    apply H; auto with ord.
Qed.

Lemma E_number_iff_unreachable:
  forall E f,
    normal_function f ->
    complete E ->
    schutte_column f E 1 0 ≈ E <-> schutte_unreachable f E.
Proof.
  intros E f Hf He.
  split; intros H.
  - split.
    + rewrite <- H. apply schutte_column_nonzero; auto.
    + intros. apply schutte_column_fix_unreachable; auto with ord.
      apply H.
  - split.
    + apply unreachable_E_number; intuition.
    + apply normal_inflationary with (f := fun x => schutte_column f x 1 0); auto with ord.
Qed.

Lemma hypercritical_iff_unreachable:
  forall E f,
    normal_function f ->
    complete E ->
    schutte_hypercritical f E <-> schutte_unreachable f E.
Proof.
  intros E f Hf HE.
  rewrite schutte_hypercritical_alt; auto.
  apply E_number_iff_unreachable; auto.
Qed.

Lemma E_number_enumerates_unreachable f:
  normal_function f ->
  enumerates (E_number f) (schutte_unreachable f).
Proof.
  intros. apply enumerates_equiv_pred with (schutte_hypercritical f).
  - apply E_number_normal; auto.
  - intros. apply hypercritical_iff_unreachable; auto.
  - apply enum_hypercritical; auto.
Qed.

Lemma schutte_column_omega_sup f:
  normal_function f ->
  schutte_column f ω 1 0 ≈ supOrd (fun i:ω => schutte_column f i 1 0).
Proof.
  split.
  - rewrite schutte_column_gt0; auto with ord.
    apply sup_least; intro i.
    apply sup_least; intros []; simpl.
    rewrite <- (sup_le _ _ (S i)).
    apply normal_fix_least; auto with ord.
    + apply limit_least; intros [].
    + rewrite <- (schutte_column_fixpoint (natOrdSize (S i)) 1 0 f (natOrdSize i) 0) at 2; auto with ord.
      apply schutte_column_monotone_full; auto with ord.
      intros. rewrite schutte_column_arg0; auto with ord.
      intros. rewrite schutte_column_arg0; auto with ord.
  - apply sup_least; intro i.
    apply schutte_column_monotone_full; auto with ord.
Qed.  

Lemma fixpoint_schutte_unreachable f x:
  normal_function f ->
  complete x ->
  schutte_unreachable f (fixOrd (fun β => schutte_column f β 1 0) x).
Proof.
  intros. split.
  - rewrite normal_fixpoint; auto with ord.

  - intros.
    apply schutte_column_fix_unreachable; auto with ord.
    { apply normal_fix_complete; auto with ord.
      intros. apply normal_inflationary with (f:=fun x => schutte_column _ x 1 0); auto with ord.
      intros; apply schutte_column_monotoneβ; auto with ord. }
    apply normal_prefixpoint with (f:= fun x => schutte_column _ x 1 0); auto with ord.
Qed.

Lemma fixpoint_schutte_least_unreachable:
  forall f E,
    normal_function f ->
    complete E ->
    schutte_unreachable f E ->
    fixOrd (fun β => schutte_column f β 1 0) 0 <= E.
Proof.
  intros f E Hf HcE [HE0 HE].
  apply normal_fix_least; auto with ord.
  apply unreachable_E_number; auto with ord.
  split; auto.
Qed.


Definition SmallVeblenOrdinal := schutte_column (expOrd ω) ω 1 0.
Definition LargeVeblenOrdinal := fixOrd (fun β => schutte_column (expOrd ω) β 1 0) 0.

Lemma SVO_nonzero: 0 < SmallVeblenOrdinal.
Proof.
  unfold SmallVeblenOrdinal.
  apply normal_nonzero; auto with ord.
Qed.

Lemma SVO_complete: complete SmallVeblenOrdinal.
Proof.
  unfold SmallVeblenOrdinal.
  apply normal_complete; auto with ord.
Qed.

Lemma SVO_sup:
  SmallVeblenOrdinal ≈ supOrd (fun i:ω => schutte_column (expOrd ω) i 1 0).
Proof.
  unfold SmallVeblenOrdinal. apply schutte_column_omega_sup; auto with ord.
Qed.  

Lemma SVO_finite_unreachable: forall i α x,
    complete α ->
    complete x ->
    α < SmallVeblenOrdinal ->
    x < SmallVeblenOrdinal ->
    schutte_column (expOrd ω) (natOrdSize i) α x < SmallVeblenOrdinal.
Proof.    
  unfold SmallVeblenOrdinal. intros.
  apply schutte_column_unreachable_apex; auto with ord.
Qed.

Lemma SVO_least_finite_unreachable: forall X,
    complete X ->
    0 < X ->
    (forall i α x,
        complete α ->
        complete x ->
        α < X ->
        x < X ->
        schutte_column (expOrd ω) (natOrdSize i) α x < X) ->
    SmallVeblenOrdinal ≤ X.
Proof.
  intros X HX1 HX2 HX3.
  rewrite SVO_sup.
  apply sup_least; intro i.
  apply ord_lt_le.
  apply HX3; auto with ord.
  apply ord_le_lt_trans with (schutte_column (expOrd ω) (natOrdSize 0) 0 0).
  { simpl. rewrite schutte_column0.
    rewrite addOrd_zero_r.
    rewrite expOrd_zero.
    auto with ord. }
  apply HX3; auto with ord.
Qed.

Lemma LVO_nonzero: 0 < LargeVeblenOrdinal.
Proof.
  unfold LargeVeblenOrdinal.
  unfold fixOrd.
  rewrite <- (sup_le _ _ 1%nat); simpl.
  auto with ord.
Qed.

Lemma LVO_complete: complete LargeVeblenOrdinal.
Proof.
  unfold LargeVeblenOrdinal.
  apply normal_fix_complete; auto with ord.
  - intros. apply normal_inflationary with (f:= fun x => schutte_column _ x 1 0); auto with ord.
  - intros; apply schutte_column_monotoneβ; auto with ord.
Qed.

Lemma LVO_unreachable: schutte_unreachable (expOrd ω) LargeVeblenOrdinal.
Proof.
  unfold LargeVeblenOrdinal.
  apply fixpoint_schutte_unreachable; auto with ord.
Qed.

Lemma LVO_least_unreachable:
  forall E,
    complete E ->
    schutte_unreachable (expOrd ω) E ->
    LargeVeblenOrdinal ≤ E.
Proof.
  intros. unfold LargeVeblenOrdinal.
  apply fixpoint_schutte_least_unreachable; auto with ord.
Qed.

Lemma schutte_column_2_ackermann_tower:
  forall f a x,
    normal_function f ->
    complete a ->
    complete x ->
    schutte_column f 2 a x ≈ ackermann_tower f a x.
Proof.  
  intros f.
  induction a as [a Hinda] using ordinal_induction.
  induction x as [x Hindx] using ordinal_induction.
  intros Hf Ha Hx.
  split.
  - rewrite schutte_column_unroll.
    apply lub_least.
    + apply ackermann_tower_fax; auto with ord.
    + apply sup_least; simpl. intros [].
      apply sup_least; intro a'.
      apply normal_fix_least; auto with ord.
      * apply limit_least; intro i.
        rewrite Hindx; auto with ord.
        apply normal_increasing; auto with ord.
      * rewrite schutte_column_veblen; auto with ord.
        transitivity (veblen (ackermann_tower f a') (ackermann_tower f a x) 0).
        { apply veblen_monotone_func; auto with ord.
          intros. apply Hinda; auto with ord. }
        apply ackermann_tower_fixpoint; auto with ord.
  - rewrite ackermann_tower_unroll.
    apply lub_least.
    { rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto with ord. }
    apply sup_least; intros a'.
    apply normal_fix_least; auto with ord.
    + apply limit_least; intro x'.
      rewrite <- Hindx; auto with ord.
      apply normal_increasing; auto with ord.
    + rewrite <- (schutte_column_fixpoint 2 a x f 1 a') at 2; auto with ord.
      rewrite schutte_column_veblen; auto with ord.
      apply veblen_monotone_func; auto with ord.
      intros. apply Hinda; auto with ord.
Qed.

Lemma schutte_column_2_succ:
  forall f a x,
    normal_function f ->
    complete a ->
    complete x ->
    schutte_column f 2 (succOrd a) x ≈
      enum_fixpoints (fun i => veblen (schutte_column f 2 a) i 0) x.
Proof.
  intros f a.
  induction x as [x Hindx] using ordinal_induction.
  intros Hf Ha Hx.
  split.
  - rewrite schutte_column_gt0; auto with ord.
    apply sup_least; intros [].
    apply sup_least; intros [].
    simpl in *.
    apply normal_fix_least; auto with ord.
    + apply normal_complete; auto with ord.
      apply enum_fixpoints_normal; auto with ord.
    + apply limit_least; intro i.
      rewrite Hindx; auto with ord.
      apply normal_increasing; auto with ord.
      apply enum_fixpoints_normal; auto with ord.
    + rewrite schutte_column_veblen; auto with ord.
      rewrite enum_are_fixpoints at 2; auto with ord.
      apply normal_complete; auto with ord.
      apply enum_fixpoints_normal; auto with ord.
  - apply enum_least'; auto with ord.
    + rewrite <- (schutte_column_fixpoint 2 (succOrd a) x f 1 a) at 2; auto with ord.
      rewrite schutte_column_veblen; auto with ord.
    + intros.
      rewrite <- Hindx; auto with ord.
      apply normal_increasing; auto with ord.
Qed.

Lemma schutte_column_2_1:
  forall x, complete x -> schutte_column (addOrd 1) 2 1 x ≈ ε x.
Proof.
  intros. unfold ε.
  rewrite schutte_column_2_succ; auto with ord.
  split; apply enum_fixpoints_func_mono'; auto with ord.
  - intros. apply fixOrd_monotone_func''; auto with ord.
    intros. transitivity (veblen (addOrd 1) x1 0).
    { apply veblen_monotone_func; auto with ord.
      intros. rewrite schutte_column_arg0; auto with ord. }
    rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r. auto with ord.
  - intros. apply fixOrd_monotone_func''; auto with ord.
    intros. transitivity (veblen (addOrd 1) x1 0).
    { rewrite veblen_onePlus; auto with ord. }
    apply veblen_monotone_func; auto with ord.
    intros. rewrite schutte_column_arg0; auto with ord.
    intros; apply normal_complete; auto with ord.
Qed.

Lemma schutte_column_2_2:
  forall x, complete x -> schutte_column (addOrd 1) 2 2 x ≈ Γ x.
Proof.
  intros. rewrite Γalt; auto.
  rewrite schutte_column_2_succ; auto with ord.
  split; apply enum_fixpoints_func_mono'; auto with ord.
  - intros. intros. apply fixOrd_monotone_func''; auto with ord.
    intros. apply veblen_monotone_func; auto with ord.
    intros. apply schutte_column_2_1; auto.
  - intros. intros. apply fixOrd_monotone_func''; auto with ord.
    intros. apply veblen_monotone_func; auto with ord.
    intros. apply schutte_column_2_1; auto.
    intros; apply normal_complete; auto with ord.
Qed.

Lemma schutte_column_succ:
  forall f β α x,
    normal_function f ->
    complete β ->
    complete α ->
    complete x ->
    schutte_column f (succOrd β) α x ≈
      f x ⊔
      supOrd (fun a:α => 
                fixOrd (fun δ => schutte_column (schutte_column f (succOrd β) a) β δ 0)
                  (limOrd (fun i:x => schutte_column f (succOrd β) α i))).
Proof.
  intros. split.
  - destruct (complete_zeroDec α); auto.
    + transitivity (schutte_column f (succOrd β) 0 x); auto with ord.
      rewrite schutte_column_arg0; auto with ord.
    + rewrite schutte_column_gt0; auto with ord.
      apply sup_least; intros []; simpl.
      auto with ord.
  - rewrite schutte_column_unroll.
    apply lubOrd_monotone; auto with ord.
    rewrite <- (sup_le _ _ tt).
    auto with ord.
Qed.

Lemma schutte_column_tower_base_le: forall b a x,
    complete b ->
    complete a ->
    complete x ->
    1 < b ->
    schutte_column (expOrd ω) b a x <= schutte_column (addOrd 1) b (1+a) x.
Proof.
  intro b.
  induction a as [a Hinda] using ordinal_induction.
  induction x as [x Hindx] using ordinal_induction.
  intros Hb Ha Hx Hb2.
  rewrite schutte_column_unroll.
  apply lub_least.
  - rewrite <- (schutte_column_fixpoint b (1+a) x (addOrd 1) 1 0); auto with ord.
    rewrite schutte_column_veblen; auto with ord.
    transitivity (veblen (addOrd 1) (schutte_column (addOrd 1) b (1 + a) x) 0).
    + rewrite veblen_onePlus; auto with ord.
      rewrite addOrd_zero_r.
      apply expOrd_monotone.
      transitivity (schutte_column (addOrd 1) 2 (1 + a) x); auto with ord.
      * rewrite schutte_column_2_ackermann_tower; auto with ord.
        rewrite <- ackermann_tower_fax; auto with ord.
        rewrite <- (addOrd_le2 1).
        rewrite <- (addOrd_le2 1).
        auto with ord.
      * apply schutte_column_monotoneβ; auto with ord.
    + apply veblen_monotone_func; auto with ord.
      intros. rewrite schutte_column_arg0; auto with ord.
  - apply sup_least; intro b'.
    apply sup_least; intro a'.
    apply normal_fix_least; auto with ord.
    + apply limit_least; intro i.
      rewrite Hindx; auto with ord.
      apply normal_increasing; auto with ord.
    + rewrite <- (schutte_column_fixpoint b (1+a) x (addOrd 1) b' (1+a')) at 2; auto with ord.
      * apply schutte_column_monotone_func'; auto with ord.
      * apply addOrd_increasing; auto with ord.
Qed.

Lemma schutte_column_tower_base_eq: forall b a x,
    complete b ->
    complete a ->
    complete x ->
    1 < b ->
    1 + a ≤ a ->
    schutte_column (expOrd ω) b a x ≈ schutte_column (addOrd 1) b a x.
Proof.
  intros. split.
  - transitivity (schutte_column (addOrd 1) b (1+a) x).
    + apply schutte_column_tower_base_le; auto with ord.
    + apply schutte_column_monotone; auto with ord.
  - apply schutte_column_monotone_func'; auto with ord.
    intros. apply onePlus_least_normal; auto with ord.
Qed.

Lemma SVO_alt: SmallVeblenOrdinal ≈ schutte_column (addOrd 1) ω 1 0.
Proof.
  unfold SmallVeblenOrdinal.
  split.
  - rewrite schutte_column_unroll. apply lub_least.
    + rewrite addOrd_zero_r.
      rewrite expOrd_one'; auto with ord.
      apply normal_inflationary with (f:= fun x => schutte_column _ x 1 0); auto with ord.
    + apply sup_least; intro i.
      apply sup_least; intros [].
      simpl.
      apply normal_fix_least; auto with ord.
      { apply limit_least; intros []. }
      transitivity (schutte_column (expOrd ω) (natOrdSize i)
                      (schutte_column (addOrd 1) ω 1 0) 0).
      { apply schutte_column_monotone_func; auto with ord.
        intros. rewrite schutte_column_arg0; auto with ord. }
      rewrite <- (schutte_column_fixpoint ω 1 0 (addOrd 1) (natOrdSize i + 2) 0) at 2; auto with ord.
      transitivity (schutte_column (expOrd ω) (natOrdSize i + 2) (schutte_column (addOrd 1) ω 1 0) 0).
      { apply schutte_column_monotoneβ; auto with ord. }
      transitivity (schutte_column (addOrd 1) (natOrdSize i + 2)
                      (schutte_column (addOrd 1) ω 1 0) 0).
      { apply schutte_column_tower_base_eq; auto with ord.
        rewrite <- addOrd_le2.
        auto with ord.
        rewrite <- (schutte_column_fixpoint ω 1 0 (addOrd 1) 0 0) at 2; auto with ord.        
        rewrite schutte_column0.
        rewrite schutte_column_arg0; auto with ord. }
      apply schutte_column_monotone_func'; auto with ord.
      intros. apply onePlus_least_normal; auto with ord.
      apply ord_le_lt_trans with (natOrdSize (2+i)); auto with ord.
      rewrite natOrdSize_add. simpl; auto with ord.
  - apply schutte_column_monotone_func'; auto with ord.
    intros. apply onePlus_least_normal; auto with ord.
Qed.

Lemma omega_least_fix:
  forall f x,
    normal_function f ->
    complete x ->
    ω ≤ fixOrd f x.
Proof.
  intros. rewrite ord_le_unfold.
  simpl; intro i.
  induction i; simpl.
  - rewrite normal_fixpoint; auto with ord.
  - apply ord_le_lt_trans with (1 + natOrdSize i).
    + transitivity (natOrdSize (1+i)).
      rewrite natOrdSize_add. simpl.
      rewrite addOrd_succ.
      apply succ_monotone; auto with ord.
      assert (Hi: (1+i = i+1)%nat) by lia.
      rewrite Hi.
      rewrite natOrdSize_add. simpl. auto with ord.
    + rewrite normal_fixpoint; auto with ord.
      rewrite <- (onePlus_least_normal f); auto with ord.
      apply addOrd_increasing; auto with ord.
      apply normal_fix_complete; auto with ord.
Qed.

Lemma LVO_alt: LargeVeblenOrdinal ≈ fixOrd (fun x => schutte_column (addOrd 1) x 1 0) 0.
Proof.
  unfold LargeVeblenOrdinal.
  assert (Hc: complete (fixOrd (fun x : Ord => schutte_column (addOrd 1) x 1 0) 0)).
  { apply normal_fix_complete; auto with ord.
    intros. apply normal_inflationary with (f:=fun x => schutte_column _ x 1 0); auto with ord.
    intros; apply schutte_column_monotoneβ; auto with ord. }
  split.
  - apply normal_fix_least; auto with ord.
    rewrite schutte_column_unroll. apply lub_least.
    + rewrite addOrd_zero_r.
      rewrite expOrd_one'; auto with ord.
      apply omega_least_fix; auto with ord.
    + apply sup_least; intro b. simpl.
      apply sup_least; intros []. simpl.
      transitivity (fixOrd
                      (fun δ : Ord =>
                         schutte_column
                           (schutte_column (expOrd ω) (fixOrd (fun x : Ord => schutte_column (addOrd 1) x 1 0) 0) 0)
                           (sz b) δ 0) 0).
      { apply fixOrd_monotone; auto with ord.
        apply limit_least; intros []. }
      transitivity (fixOrd (fun δ : Ord => schutte_column (expOrd ω) (sz b) δ 0) 0).
      { apply fixOrd_monotone_func''; auto with ord.
        intros. rewrite schutte_column_monotone_func'; auto with ord.
        intros. rewrite schutte_column_arg0; auto with ord. }
      apply normal_fix_least; auto with ord.
      assert (Hb2: 1 + (1 + b) < fixOrd (fun x : Ord => schutte_column (addOrd 1) x 1 0) 0).
      { rewrite normal_fixpoint at 2; auto with ord.
        rewrite <- onePlus_least_normal with (f:=fun x => schutte_column _ x 1 0); auto with ord.
        apply addOrd_increasing; auto with ord.
        rewrite normal_fixpoint at 2; auto with ord.
        rewrite <- onePlus_least_normal with (f:=fun x => schutte_column _ x 1 0); auto with ord.
        apply addOrd_increasing; auto with ord. }
      transitivity (schutte_column (expOrd ω) (1+ (1+sz b)) (fixOrd (fun x : Ord => schutte_column (addOrd 1) x 1 0) 0) 0).
      { apply schutte_column_monotoneβ; auto with ord.
        rewrite <- addOrd_le2.
        rewrite <- addOrd_le2.
        auto with ord. }
      rewrite schutte_column_tower_base_eq; auto with ord.
      * rewrite normal_fixpoint at 3; auto with ord.
        rewrite ord_lt_unfold in Hb2.
        destruct Hb2 as [b' Hb2].
        rewrite <- (schutte_column_fixpoint _ 1 0 _ b' 0); auto with ord.
        transitivity (schutte_column (addOrd 1) (sz b')
                        (schutte_column (addOrd 1) (fixOrd (fun x : Ord => schutte_column (addOrd 1) x 1 0) 0) 1 0)
                        0).
        2:{ apply schutte_column_monotone_func'; auto with ord.
            intros. apply onePlus_least_normal; auto with ord. }
        transitivity (schutte_column (addOrd 1) b'
                        (fixOrd (fun x : Ord => schutte_column (addOrd 1) x 1 0) 0) 0).
        { apply schutte_column_monotoneβ; auto with ord. }
        apply schutte_column_monotone; auto with ord.
        apply normal_inflationary with (f:=fun x => schutte_column _ x 1 0); auto with ord.
      * apply ord_le_lt_trans with (1 + 0); auto with ord.
        apply addOrd_increasing; auto with ord.
      * rewrite normal_fixpoint at 2; auto with ord.
        apply onePlus_least_normal with (f:=fun x => schutte_column _ x 1 0); auto with ord.
  - apply fixOrd_monotone_func''; auto with ord.
    + intros. apply schutte_column_monotone_func'; auto with ord.
      intros. apply onePlus_least_normal; auto with ord.
    + intros. apply schutte_column_monotoneβ; auto with ord.
Qed.

Fixpoint schutte_stack (f:Ord -> Ord) (xs:list Ord) : Ord -> Ord :=
  match xs with
  | [] => f
  | α::xs' => schutte_stack (schutte_column f (sz (length xs')) α) xs'
  end.

Lemma schutte_stack_monotone_func xs:
   forall f g x,
     (forall a b, a ≤ b -> f a ≤ f b) ->
     (forall a b, a ≤ b -> g a ≤ g b) ->
     (forall a, f a ≤ g a) ->
     schutte_stack f xs x ≤ schutte_stack g xs x.
Proof.
  induction xs as [|a xs]; simpl; intros; auto with ord.
  apply IHxs; auto.
  - intros. apply schutte_column_monotone; auto with ord.
  - intros. apply schutte_column_monotone; auto with ord.
  - intros. apply schutte_column_monotone_func; auto with ord.
Qed.

Definition list_complete xs := each complete xs.

Lemma schutte_stack_normal: forall xs f,
  list_complete xs ->
  normal_function f ->
  normal_function (schutte_stack f xs).
Proof.
  unfold list_complete.
  induction xs as [|a xs']; simpl; intros; auto.
  apply IHxs'; intuition auto with ord.
Qed.

Global Hint Resolve schutte_stack_normal: ord.

Lemma schutte_stack_veblen: forall f α x y,
  normal_function f ->
  complete α ->
  complete x ->
  complete y ->
  schutte_stack f [α;x] y ≈ veblen f α (x+y).
Proof.
  simpl. intros. rewrite schutte_column0.
  apply schutte_column_veblen; auto.
  apply addOrd_complete; auto with ord.
Qed.

Lemma schutte_stack_zero_column: forall f x y,
  schutte_stack f [x] y ≈ f (x+y).
Proof.
  simpl; intros.
  rewrite schutte_column0.
  auto with ord.
Qed.

Lemma schutte_stack_leading_zero: forall f xs y,
  normal_function f ->
  schutte_stack f (0 :: xs) y ≈ schutte_stack f xs y.
Proof.
  intros; simpl; split; apply schutte_stack_monotone_func; auto with ord.
  - intros; rewrite schutte_column_arg0; auto with ord.
  - intros; rewrite schutte_column_arg0; auto with ord.
Qed.    
  
Definition schutte_stack_proper xs α := each (fun x => x < α) xs.

Lemma schutte_stack_proper_monotone:
  forall xs α α',
  α ≤ α' ->
  schutte_stack_proper xs α ->
  schutte_stack_proper xs α'.
Proof.
  unfold schutte_stack_proper.
  induction xs as [|a xs]; simpl; auto.
  intuition.
  apply ord_lt_le_trans with α; auto with ord.
  apply (IHxs α α'); auto with ord.
Qed.

Lemma schutte_stack_zeros: forall i f x,
  (forall a b, a <= b -> f a <= f b) ->
  schutte_stack f (repeat 0 i) x ≈ f x.
Proof.
  induction i; simpl; auto with ord.
  intros.
  rewrite IHi.
  rewrite schutte_column_arg0; auto with ord.
  intros.
  rewrite schutte_column_arg0; auto with ord.
  rewrite schutte_column_arg0; auto with ord.
Qed.

Lemma schutte_column_to_stack: forall f i a x,
  (forall a b, a <= b -> f a <= f b) ->
  schutte_column f (sz i) a x ≈ schutte_stack f (a::repeat 0 i) x.
Proof.
  simpl; intros.
  rewrite repeat_length.
  rewrite schutte_stack_zeros; auto with ord.
Qed.

Lemma list_complete_cons: forall x xs,
    complete x ->
    list_complete xs ->
    list_complete (x::xs).
Proof.
  unfold list_complete.
  simpl; intuition.
Qed.

Lemma proper_stack_unreachable:
  forall xs f a δ x,
    normal_function f ->
    complete a ->
    complete x ->
    complete δ ->
    list_complete xs ->
    schutte_stack_proper xs δ ->
    x < δ ->
    schutte_stack f xs x < schutte_column f (sz (length xs)) δ 0.
Proof.
  unfold list_complete, schutte_stack_proper.
  induction xs as [|a xs]; simpl.
  - intros.
    rewrite schutte_column0.
    apply normal_increasing; auto with ord.
    rewrite addOrd_zero_r.
    auto.
  - simpl; intros.
    rewrite <- (schutte_column_fixpoint _ δ 0 f (sz (length xs)) a); intuition auto with ord.
    eapply ord_lt_le_trans; [ apply IHxs with (a:=a) (δ:=δ); intuition auto with ord |].
    apply schutte_column_monotone_full; auto with ord.
    intros. apply schutte_column_monotoneβ; auto with ord.
Qed.

Lemma proper_stack_apex_unreachable:
  forall xs f β x,
    normal_function f ->
    complete β ->
    complete x ->
    list_complete xs ->
    β > sz (length xs) ->
    schutte_stack_proper xs (schutte_column f β 1 0) ->
    x < schutte_column f β 1 0 ->
    schutte_stack f xs x < schutte_column f β 1 0.
Proof.
  unfold list_complete.
  intros.
  destruct xs; simpl in *.
  - rewrite <- (schutte_column_fixpoint β 1 0 f 0 0); auto with ord.
    rewrite schutte_column0.
    rewrite schutte_column_arg0; auto with ord.
    apply normal_increasing; auto with ord.
    rewrite addOrd_zero_r.
    auto.
  - rewrite <- (schutte_column_fixpoint β 1 0 f (succOrd (sz (length xs))) 0); auto with ord.
    generalize (proper_stack_unreachable (o::xs) f); simpl.
    intro Hxs.
    eapply ord_lt_le_trans; [ apply Hxs with (a:=o) (δ:=schutte_column f β 1 0); auto with ord |].
    intuition.
    apply schutte_column_monotone_func; auto with ord.
    intro. rewrite schutte_column_arg0; auto with ord.
Qed.    
    
Lemma schutte_stack_unreachable:
  forall f xs x,
    normal_function f ->
    list_complete xs ->
    complete x ->
    x < schutte_column f ω 1 0 ->
    schutte_stack_proper xs (schutte_column f ω 1 0) ->
    schutte_stack f xs x < schutte_column f ω 1 0.
Proof.
  intros.
  apply proper_stack_apex_unreachable; auto with ord.
Qed.

Lemma schutte_stack_least_unreachable:
  forall f X,
    normal_function f ->
    complete X ->
    0 < X ->
    (forall xs x, 
        list_complete xs ->
        complete x ->
        x < X ->
        schutte_stack_proper xs X ->
        schutte_stack f xs x < X) ->
    schutte_column f ω 1 0 <= X.
Proof.
  unfold list_complete.
  intros f X Hf HXc HX0 HX.
  assert (HX1: 1 < X).
  { apply ord_le_lt_trans with (schutte_stack f [] 0).
    - simpl. apply succ_least.
      apply normal_nonzero; auto with ord.
    - apply HX; auto with ord.
      simpl; auto.
      unfold schutte_stack_proper; simpl; auto. }
  rewrite schutte_column_omega_sup; auto with ord.
  apply sup_least; intro i.
  rewrite schutte_column_to_stack; auto with ord.
  apply ord_lt_le.
  apply HX; auto with ord.
  { apply list_complete_cons; auto with ord.
    unfold list_complete, repeat, each.
    induction i; intuition auto with ord. }
  simpl; intuition.
  unfold schutte_stack_proper; simpl.
  induction i; simpl; intuition.
Qed.

Lemma SVO_stack_unreachable:
  forall xs x,
    list_complete xs ->
    complete x ->
    x < SmallVeblenOrdinal ->
    schutte_stack_proper xs SmallVeblenOrdinal ->
    schutte_stack (expOrd ω) xs x < SmallVeblenOrdinal.
Proof.    
  intros.
  unfold SmallVeblenOrdinal in *.
  apply proper_stack_apex_unreachable; auto with ord.
Qed.

Lemma SVO_stack_unreachable':
  forall xs x,
    list_complete xs ->
    complete x ->
    x < SmallVeblenOrdinal ->
    schutte_stack_proper xs SmallVeblenOrdinal ->
    schutte_stack (addOrd 1) xs x < SmallVeblenOrdinal.
Proof.    
  intros.
  rewrite SVO_alt in *.
  assert (schutte_stack_proper xs (schutte_column (addOrd 1) ω 1 0)).
  { apply schutte_stack_proper_monotone with SmallVeblenOrdinal; auto.
    rewrite SVO_alt. auto with ord. }
  apply proper_stack_apex_unreachable; auto with ord.
Qed.

Lemma SVO_least_stack_unreachable:
  forall X,
    complete X ->
    0 < X ->
    (forall xs x, 
        list_complete xs ->
        complete x ->
        x < X ->
        schutte_stack_proper xs X ->
        schutte_stack (expOrd ω) xs x < X) ->
    SmallVeblenOrdinal <= X.
Proof.
  intros X HXc HX0 HX.
  apply schutte_stack_least_unreachable; auto with ord.
Qed.

Lemma SVO_least_stack_unreachable':
  forall X,
    complete X ->
    0 < X ->
    (forall xs x, 
        list_complete xs ->
        complete x ->
        x < X ->
        schutte_stack_proper xs X ->
        schutte_stack (addOrd 1) xs x < X) ->
    SmallVeblenOrdinal <= X.
Proof.
  intros X HXc HX0 HX.
  rewrite SVO_alt.
  apply schutte_stack_least_unreachable; auto with ord.
Qed.

Fixpoint schutte_matrix (f: Ord -> Ord) (m: list (Ord * Ord)) : Ord -> Ord :=
  match m with
  | [] => f
  | (β,α)::m' => schutte_matrix (schutte_column f β α) m'
  end.

Lemma schutte_matrix_monotone_func m:
   forall f g x,
     (forall a b, a ≤ b -> f a ≤ f b) ->
     (forall a b, a ≤ b -> g a ≤ g b) ->
     (forall a, f a ≤ g a) ->
     schutte_matrix f m x ≤ schutte_matrix g m x.
Proof.
  induction m as [|[p q]]; simpl; intros; auto with ord.
  apply IHm; auto.
  - intros. apply schutte_column_monotone; auto with ord.
  - intros. apply schutte_column_monotone; auto with ord.
  - intros. apply schutte_column_monotone_func; auto with ord.
Qed.

Fixpoint all_complete (m: list (Ord * Ord)) : Prop :=
  match m with
  | [] => True
  | (β,α)::m' => complete β /\ complete α /\ all_complete m'
  end.

Lemma schutte_matrix_normal: forall m f,
  all_complete m ->
  normal_function f ->
  normal_function (schutte_matrix f m).
Proof.
  induction m as [|[a b] m']; simpl; intros; auto.
  apply IHm'; intuition auto with ord.
Qed.

Global Hint Resolve schutte_matrix_normal: ord.

Lemma schutte_matrix_veblen: forall f α x y,
  normal_function f ->
  complete α ->
  complete x ->
  complete y ->
  schutte_matrix f [(1,α); (0,x)] y ≈ veblen f α (x+y).
Proof.
  simpl. intros. rewrite schutte_column0.
  apply schutte_column_veblen; auto.
  apply addOrd_complete; auto with ord.
Qed.

Lemma schutte_matrix_zero_column: forall f x y,
  schutte_matrix f [(0,x)] y ≈ f (x+y).
Proof.
  simpl; intros.
  rewrite schutte_column0.
  auto with ord.
Qed.

Lemma schutte_matrix_app M: forall N f x,
  schutte_matrix f (M++N) x = schutte_matrix (schutte_matrix f M) N x.
Proof.
  induction M as [|[p q] H]; simpl; intros; auto with ord.
Qed.

Lemma schutte_matrix_zero_arg:
  forall m1 m2 β f x,
    (forall a b, a ≤ b -> f a ≤ f b) ->
    complete β ->
    schutte_matrix f (m1++[(β,0)]++m2) x ≈ schutte_matrix f (m1++m2) x.
Proof.
  induction m1 as [|[p q]]; simpl; intros; auto.
  - split; apply schutte_matrix_monotone_func; intros; auto with ord.
    + rewrite schutte_column_arg0; auto with ord.
    + rewrite schutte_column_arg0; auto with ord.
  - apply IHm1; auto with ord.
Qed.

Lemma enumerates_func_equiv:
  forall f g (P: Ord -> Prop),
    (forall x, f x ≈ g x) ->
    (forall x y, x ≈ y -> P x -> P y) ->
    enumerates f P -> enumerates g P.
Proof.
  intros f g P Hfg HP Hf.
  constructor; intros.
  - apply HP with (f x); auto.
    apply enumerates_included; auto.
  - repeat rewrite <- Hfg.
    apply enumerates_monotone with P; auto.
  - repeat rewrite <- Hfg.
    apply enumerates_increasing with P; auto.
  - rewrite <-Hfg.
    apply enumerates_least with P; auto with ord.
    intros. rewrite Hfg; auto.
Qed.

Theorem schutte_matrix_enumerates:
  forall f m β α,
    0 < β ->
    0 < α ->
    normal_function f ->
    all_complete m ->
    complete β ->
    complete α ->
    enumerates (fun x => schutte_matrix f (m ++ [(β,α);(0,x)]) 0)
               (fun δ => forall b a, complete b -> b < β -> complete a -> a < α ->
                             schutte_matrix f (m ++ [(β,a);(b,δ)]) 0 ≈ δ).
Proof.
  simpl; intros f m β α Hβ Hα Hf Hm Hcβ Hcα.
  apply enumerates_func_equiv with (fun x => schutte_column (schutte_matrix f m) β α x); auto with ord.
  - intros.
    rewrite schutte_matrix_app; simpl.
    rewrite schutte_column0.
    split; apply schutte_column_monotone; auto with ord.
    rewrite addOrd_zero_r; auto with ord.
  - intros.
    rewrite schutte_matrix_app; simpl.
    rewrite <- H at 2; auto.
    rewrite <- (H0 b a); auto.
    rewrite schutte_matrix_app; simpl; auto with ord.
    split; apply schutte_column_monotone; auto with ord; apply H.
  - apply enumerates_equiv_pred with (schutte_critical (schutte_matrix f m) β α); auto with ord.
    + intros.
      unfold schutte_critical.
      split; intros.
      rewrite schutte_matrix_app; simpl.
      apply H0; auto with ord.
      rewrite <- (H0 b a) at 2; auto.
      rewrite schutte_matrix_app; simpl; auto with ord.
    + apply schutte_column_enumerates; auto with ord.
Qed.

Fixpoint schutte_matrix_proper (m: list (Ord * Ord)) (β:Ord) (α:Ord) :=
  match m with
  | [] => True
  | ((b,a)::m') => b < β /\ 0 < a /\ a < α /\ schutte_matrix_proper m' b α
  end.

Lemma schutte_matrix_proper_monotone:
  forall m β β' α α',
  β ≤ β' ->
  α ≤ α' ->
  schutte_matrix_proper m β α ->
  schutte_matrix_proper m β' α'.
Proof.
  induction m as [|[b a]m]; simpl; auto.
  intuition.
  apply ord_lt_le_trans with β; auto with ord.
  apply ord_lt_le_trans with α; auto with ord.
  apply (IHm b b α α'); auto with ord.
Qed.

Lemma proper_matrix_unreachable:
  forall m f b a δ x,
    normal_function f ->
    complete b ->
    complete a ->
    complete x ->
    complete δ ->
    all_complete m ->
    schutte_matrix_proper m b δ ->
    (x ≈ 0 \/ additively_closed δ) ->
    a < δ ->
    x < δ ->
    schutte_matrix f ((b,a)::m) x < schutte_column f b δ 0.
Proof.
  induction m as [|[b1 a1]m]; simpl.
  - intros.
    destruct (complete_zeroDec b); auto.
    + apply ord_le_lt_trans with (f (a+x)).
      { rewrite schutte_column_unroll.
        apply lub_least; auto with ord.
        apply sup_least; intro b'.
        elim (zero_lt b').
        apply ord_lt_le_trans with b; auto with ord. }
      rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      apply normal_increasing; auto with ord.
      rewrite addOrd_zero_r.
      unfold additively_closed in *. intuition.
      rewrite H10. rewrite addOrd_zero_r. auto.
    + rewrite <- (schutte_column_fixpoint b δ 0 f 0 a); auto with ord.
      rewrite schutte_column0.
      apply normal_increasing; auto with ord.
      rewrite addOrd_zero_r.
      apply ord_lt_le_trans with δ; auto with ord.
  - intros f b a δ x ? ? ? ? ? [?[??]] [?[?[??]]] ? ? ?.
    rewrite <- (schutte_column_fixpoint b δ 0 f b1 a); auto with ord.
    eapply ord_lt_le_trans; [ apply (IHm _ b1 a1 δ x); auto with ord | auto with ord ].
Qed.

Lemma proper_matrix_apex_unreachable:
  forall m f β x,
    normal_function f ->
    complete β ->
    complete x ->
    all_complete m ->
    (x ≈ 0 \/ β > 1) ->
    β > 0 ->
    schutte_matrix_proper m β (schutte_column f β 1 0) ->
    x < schutte_column f β 1 0 ->
    schutte_matrix f m x < schutte_column f β 1 0.
Proof.
  intros.
  destruct m as [|[b1 a1]m]; simpl in *.
  - intros.
    rewrite <- (schutte_column_fixpoint β 1 0 f 0 0); auto with ord.
    rewrite schutte_column0.
    rewrite schutte_column_arg0; auto with ord.
    apply normal_increasing; auto with ord.
    rewrite addOrd_zero_r; auto.
  - rewrite <- (schutte_column_fixpoint β 1 0 f b1 0); auto with ord.
    apply ord_lt_le_trans with (schutte_column f b1 (schutte_column f β 1 0) 0); auto with ord.
    2:{ apply schutte_column_monotone_func; auto with ord.
        intros. rewrite schutte_column_arg0; auto with ord. }
    apply proper_matrix_unreachable; intuition auto with ord.
    right. hnf; intros. apply schutte_column_add_closed; auto with ord.
    intuition.
    intuition.
Qed.

Lemma proper_matrix_E_unreachable:
  forall m f x E,
    normal_function f ->
    complete E ->
    complete x ->
    all_complete m ->
    schutte_matrix_proper m E E ->
    x < E ->
    schutte_column f E 1 0 ≤ E ->
    schutte_matrix f m x < E.
Proof.
  intros m f x E Hf He Hx Hm Hproper HxE Hfix.
  rewrite <- Hfix.
  apply proper_matrix_apex_unreachable; auto with ord.
  - right. rewrite <- Hfix.
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    apply ord_le_lt_trans with (1+0).
    rewrite addOrd_zero_r. auto with ord.
    apply ord_lt_le_trans with (1+(1+0)).
    apply addOrd_increasing; auto with ord.
    apply onePlus_least_normal; auto with ord.
  - rewrite <- Hfix; auto with ord.
  - apply schutte_matrix_proper_monotone with E E; auto with ord.
    apply normal_inflationary with (f:=fun x => schutte_column f x 1 0); auto with ord.
  - apply ord_lt_le_trans with E; auto.
    apply normal_inflationary with (f:=fun x => schutte_column f x 1 0); auto with ord.
Qed.

Definition proper_matrix_is_unreachable f E :=
  E > 0 /\
  (forall m,
     all_complete m ->
     schutte_matrix_proper m E E ->
     schutte_matrix f m 0 < E).

Lemma proper_matrix_is_unreachable_iff:
  forall f E,
    normal_function f ->
    complete E ->
    schutte_unreachable f E <-> proper_matrix_is_unreachable f E.
Proof.
  intros f E Hf HE. split; intro H.
  - rewrite <- E_number_iff_unreachable in H; auto.
    split.
    + rewrite <- H; auto with ord.
    + intros m Hcm Hm.
      apply proper_matrix_E_unreachable; auto with ord.
      rewrite <- H; auto with ord.
      apply H.
  - destruct H as [HE0 H].
    split; auto.
    intros β α x ? ? ? ? ? ?.
    destruct (complete_zeroDec α); auto.
    + destruct (complete_zeroDec x); auto.
      * eapply ord_le_lt_trans; [| apply (H [])]; simpl; auto with ord.
        rewrite schutte_column_unroll.
        apply lub_least; auto.
        ** apply normal_monotone; auto with ord.
           rewrite H6.
           rewrite addOrd_zero_l. auto.
        ** apply sup_least; intro b.
           apply sup_least; intro a.
           elim (zero_lt a).
           apply ord_lt_le_trans with α; auto with ord.
      * eapply ord_le_lt_trans; [| apply (H [(0,x)])]; auto with ord.
        ** simpl. rewrite schutte_column0.
           rewrite schutte_column_unroll.
           apply lub_least; auto.
           *** apply normal_monotone; auto with ord.
               rewrite H6.
               rewrite addOrd_zero_l.
               rewrite addOrd_zero_r.
               auto with ord.
           *** apply sup_least; intro b.
               apply sup_least; intro a.
               elim (zero_lt a).
               apply ord_lt_le_trans with α; auto with ord.
        ** simpl. split.
           apply zero_complete.
           split; auto.
        ** simpl; intuition.
    + destruct (complete_zeroDec β); auto with ord.
      * destruct (complete_zeroDec x); auto with ord.
        ** eapply ord_le_lt_trans; [| apply (H [(0,α)])]; auto with ord.
          ***  simpl.
               rewrite schutte_column0.
               rewrite schutte_column_unroll.
               apply lub_least.
               **** apply normal_monotone; auto with ord.
               **** apply sup_least; intro b.
                    elim (zero_lt b).
                    apply ord_lt_le_trans with β; auto with ord.
          *** repeat (split; auto with ord).
          *** simpl; intuition.
        ** eapply ord_le_lt_trans; [| apply (H [(1,α);(0,x)])]; auto with ord.
           *** simpl.
               rewrite schutte_column0.
               rewrite schutte_column_unroll.
               apply lub_least.
               **** rewrite schutte_column_unroll.
                    rewrite <- lub_le1.
                    apply normal_monotone; auto with ord.
               **** apply sup_least; intro b.
                    elim (zero_lt b).
                    apply ord_lt_le_trans with β; auto with ord.
           *** repeat (split; auto with ord).
           *** simpl; intuition.
               eapply ord_le_lt_trans; [| apply (H [])]; simpl; auto with ord.
               apply succ_lt.
      * destruct (complete_zeroDec x); auto.
        ** eapply ord_le_lt_trans; [| apply (H [(β,α)])]; simpl; auto with ord.
        ** eapply ord_le_lt_trans; [| apply (H [(β,α);(0,x)])]; auto with ord.
           *** simpl. rewrite schutte_column0.
               apply schutte_column_monotone; auto with ord.
           *** repeat (split; auto with ord).
           *** simpl; intuition.
Qed.

Lemma E_number_iff_matrix_unreachable:
  forall (E : Ord) (f : Ord -> Ord),
    normal_function f ->
    complete E ->
    schutte_column f E 1 0 ≈ E <-> proper_matrix_is_unreachable f E.
Proof.
  intros.
  rewrite E_number_iff_unreachable; auto.
  apply proper_matrix_is_unreachable_iff; auto.
Qed.

Lemma LVO_matrix_unreachable:
  proper_matrix_is_unreachable (expOrd ω) LargeVeblenOrdinal.
Proof.
  apply proper_matrix_is_unreachable_iff; auto with ord.
  apply LVO_complete.
  apply LVO_unreachable.
Qed.

Lemma LVO_least_matrix_unreachable:
  forall E,
    complete E ->
    proper_matrix_is_unreachable (expOrd ω) E ->
    LargeVeblenOrdinal ≤ E.
Proof.
  intros E HcE HE.
  rewrite <- proper_matrix_is_unreachable_iff in HE; auto with ord.
  apply LVO_least_unreachable; auto.
Qed.

Lemma LVO_matrix_unreachable':
  proper_matrix_is_unreachable (addOrd 1) LargeVeblenOrdinal.
Proof.
  apply proper_matrix_is_unreachable_iff; auto with ord.
  apply LVO_complete.
  split.
  apply LVO_nonzero.
  intros.
  rewrite LVO_alt in *.
  apply fixpoint_schutte_unreachable; auto with ord.
Qed.

Lemma LVO_least_matrix_unreachable':
  forall E,
    complete E ->
    proper_matrix_is_unreachable (addOrd 1) E ->
    LargeVeblenOrdinal ≤ E.
Proof.
  intros E HcE HE.
  rewrite <- proper_matrix_is_unreachable_iff in HE; auto with ord.
  rewrite LVO_alt.
  apply fixpoint_schutte_least_unreachable; auto with ord.
Qed.
