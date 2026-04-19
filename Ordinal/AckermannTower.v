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

Open Scope ord_scope.

Local Hint Resolve
      zero_complete
      succ_complete
      addOrd_complete
      complete_subord : core.

Fixpoint ackermann_tower (f: Ord -> Ord) (a:Ord) {struct a} : Ord -> Ord :=
  fix inner (x:Ord) : Ord :=
    match a, x with
    | ord A fa, ord X fx =>
        f (ord X fx) ⊔
          supOrd (fun a':A => fixOrd (fun d => veblen (ackermann_tower f (fa a')) d 0)
                                     (ord X (fun x' => inner (fx x'))))
    end.

Lemma ackermann_tower_unroll f a x:
  ackermann_tower f a x =
    f x ⊔ supOrd (fun a':a =>
                    fixOrd (fun d => veblen (ackermann_tower f a') d 0)
                      (limOrd (fun x':x => ackermann_tower f a x'))).
Proof.
  destruct a; destruct x; reflexivity.
Qed.

Global Opaque ackermann_tower.

Lemma ackermann_tower_monotone_x:
  forall f a,
    (forall x y, x ≤ y -> f x ≤ f y) ->
    forall x y, x ≤ y -> ackermann_tower f a x ≤ ackermann_tower f a y.
Proof.
  intros f.
  induction a as [a Hinda] using ordinal_induction.
  intros Hf.
  induction x as [x Hindx] using ordinal_induction.
  intros y Hxy.
  rewrite ackermann_tower_unroll.
  apply lub_least.
  - rewrite ackermann_tower_unroll.
    rewrite <- lub_le1.
    apply Hf; auto.
  - apply sup_least; intro a'.
    rewrite ackermann_tower_unroll.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ a').
    apply fixOrd_monotone; auto with ord.
    apply limit_least. intro i.
    rewrite ord_lt_unfold. simpl.
    rewrite ord_le_unfold in Hxy.
    generalize (Hxy i).
    rewrite ord_lt_unfold.
    intros [j Hj].
    exists j.
    apply (Hindx i); auto with ord.
Qed.

Lemma ackermann_tower_monotone_a:
  forall f a b,
    a ≤ b ->
    (forall x y, x ≤ y -> f x ≤ f y) ->
    forall x, ackermann_tower f a x ≤ ackermann_tower f b x.
Proof.
  intros f.
  induction a as [a Hinda] using ordinal_induction.
  intros b Hab Hf.
  induction x as [x Hindx] using ordinal_induction.
  rewrite ackermann_tower_unroll.
  apply lub_least.
  - rewrite ackermann_tower_unroll; auto with ord.
  - apply sup_least; intro a'.
    rewrite ord_le_unfold in Hab.
    generalize (Hab a').
    rewrite ord_lt_unfold.
    intros [b' Hb'].
    rewrite ackermann_tower_unroll.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ b').
    transitivity
      (fixOrd (fun d : Ord => veblen (ackermann_tower f (sz b')) d 0)
         (limOrd (fun x' : x => ackermann_tower f a (sz x')))).
    { apply fixOrd_monotone_func; auto with ord.
      intros. apply veblen_mono_func; auto with ord.
      intros; apply ackermann_tower_monotone_x; auto.
      intros; apply veblen_monotone_first; auto with ord.
      intros; apply ackermann_tower_monotone_x; auto. }
    apply fixOrd_monotone; auto with ord.
    intros; apply veblen_monotone_first; auto with ord.
    intros; apply ackermann_tower_monotone_x; auto.
    apply limit_least. intro i.
    rewrite ord_lt_unfold. simpl.
    exists i.
    apply Hindx; auto with ord.
Qed.

Lemma ackermann_tower_monotone:
  forall f,
    (forall x y, x ≤ y -> f x ≤ f y) ->
    forall a b x y,
      a ≤ b -> x ≤ y ->
      ackermann_tower f a x ≤ ackermann_tower f b y.
Proof.
  intros. transitivity (ackermann_tower f a y).
  apply ackermann_tower_monotone_x; auto.
  apply ackermann_tower_monotone_a; auto.
Qed.

Global Hint Resolve ackermann_tower_monotone: ord.

Lemma ackermann_tower_increasing:
  forall f a,
    normal_function f ->
    complete a ->
    forall x y, complete y -> x < y ->
    ackermann_tower f a x < ackermann_tower f a y.
Proof.
  intros f. induction a as [a Hinda] using ordinal_induction.
  intros Hf Ha x y Hy Hxy.
  destruct (complete_zeroDec a); auto.
  - rewrite (ackermann_tower_unroll f a y).
    rewrite <- lub_le1.
    apply ord_le_lt_trans with (f x); auto.
    rewrite ackermann_tower_unroll.
    apply lub_least; auto with ord.
    apply sup_least; intro i.
    elim (ord_lt_irreflexive 0).
    apply ord_lt_le_trans with a; auto.
    apply ord_le_lt_trans with i; auto with ord.
    apply normal_increasing; auto.
  - rewrite (ackermann_tower_unroll f a y).
    rewrite ord_lt_unfold in H.
    destruct H as [i Hi].
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    rewrite <- fixOrd_above.
    rewrite ord_lt_unfold in Hxy.
    destruct Hxy as [y' Hy'].
    rewrite ord_lt_unfold.
    exists y'; simpl.
    apply ackermann_tower_monotone_x; auto.
    apply normal_monotone; auto.
Qed.

Lemma ackermann_tower_nonzero:
  forall f a x,
    normal_function f ->
    0 < ackermann_tower f a x.
Proof.
  intros. rewrite ackermann_tower_unroll.
  rewrite <- lub_le1.
  apply normal_nonzero; auto.
Qed.

Lemma ackermann_tower_inflationary:
  forall f a x,
    normal_function f ->
    complete x ->
    x ≤ ackermann_tower f a x.
Proof.
  intros. rewrite ackermann_tower_unroll.
  rewrite <- lub_le1.
  apply normal_inflationary; auto with ord.
Qed.

Section ackermann_tower.
  Variable f: Ord -> Ord.
  Hypothesis Hf_normal: normal_function f.

  Variable a: Ord.
  Hypothesis Hacomplete: complete a.
  Hypothesis Hinduct_a: forall i, complete i -> i < a -> normal_function (ackermann_tower f i).

  Lemma ackermann_tower_complete_le:
    forall x i,
      i <= a ->
      i > 0 ->
      complete i ->
      complete x ->
      f x ≤
        supOrd (fun i':i =>
                      fixOrd (fun d => veblen (ackermann_tower f i') d 0)
                        (limOrd (fun x':x => ackermann_tower f i x'))) /\
      complete (ackermann_tower f i x).
  Proof.
    induction x as [x Hindx] using ordinal_induction.
    intros i Hia Hi0 Hi Hx.
    assert (Hlim_complete: complete (limOrd (fun x' : x => ackermann_tower f i (sz x')))).
    { apply lim_complete; auto with ord.
      * intro x'. apply Hindx; auto with ord.
      * apply directed_monotone; auto with ord.
      * destruct x; apply Hx. }
    assert (Hfx: f x
                   ≤ supOrd
                   (fun i' : i =>
                      fixOrd (fun d : Ord => veblen (ackermann_tower f (sz i')) d 0)
                        (limOrd (fun x' : x => ackermann_tower f i (sz x'))))).
    { rewrite ord_lt_unfold in Hi0.
      destruct Hi0 as [i' ?].
      rewrite <- (sup_le _ _ i').
      unfold fixOrd.
      rewrite <- (sup_le _ _ 1%nat). simpl.
      rewrite <- veblen_fax; auto with ord.
      + rewrite ackermann_tower_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite addOrd_zero_r.
        rewrite ord_le_unfold; intro x'.
        rewrite ord_lt_unfold. exists x'; simpl.
        apply ackermann_tower_inflationary; auto with ord.
      + apply Hinduct_a; auto with ord.
        apply ord_lt_le_trans with i; auto with ord. }

    split; auto.
    rewrite ackermann_tower_unroll.
    apply lub_complete2; auto with ord.
    apply sup_complete; auto with ord.
    - intros. apply normal_fix_complete; auto with ord.
      + intros. apply normal_inflationary with (f := fun x => veblen _ x 0); auto with ord.
        apply veblen_first_normal; auto with ord.
        apply Hinduct_a; auto with ord.
        apply ord_lt_le_trans with i; auto with ord.
      + intros. apply veblen_complete; auto with ord.
        apply Hinduct_a; auto with ord.
        apply ord_lt_le_trans with i; auto with ord.
        intros. apply normal_complete; auto with ord.
        apply Hinduct_a; auto with ord.
        apply ord_lt_le_trans with i; auto with ord.
    - apply directed_monotone; auto with ord.
      intros. apply fixOrd_monotone_func; auto with ord.
      intros. apply veblen_monotone_full; auto with ord.
    - left. rewrite ord_lt_unfold in Hi0.
      destruct Hi0 as [i' _].
      exists i'.
      unfold fixOrd.
      rewrite <- (sup_le _ _ 1%nat). simpl.
      rewrite veblen_unroll. rewrite <- lub_le1.
      apply ackermann_tower_nonzero; auto.
  Qed.

  Lemma ackermann_tower_unroll_nonzero:
    forall x i,
      i <= a ->
      i > 0 ->
      complete i ->
      complete x ->
      ackermann_tower f i x ≈
        supOrd (fun i':i =>
                      fixOrd (fun d => veblen (ackermann_tower f i') d 0)
                        (limOrd (fun x':x => ackermann_tower f i x'))).
  Proof.
    intros. rewrite ackermann_tower_unroll. split; auto with ord.
    apply lub_least; auto with ord.
    apply ackermann_tower_complete_le; auto.
  Qed.

  Lemma ackermann_tower_complete:
    forall x i,
      i <= a ->
      complete i ->
      complete x ->
      complete (ackermann_tower f i x).
  Proof.
    intros.
    destruct (complete_zeroDec i); auto.
    - rewrite ackermann_tower_unroll.
      assert (Hi: forall i':i, False).
      { intro i'.
        elim (ord_lt_irreflexive 0).
        apply ord_le_lt_trans with i'; auto with ord.
        apply ord_lt_le_trans with i; auto with ord. }
      apply lub_complete1; auto with ord.
      + apply sup_least; intro i'; intuition.
      + apply sup_complete; unfold directed; intuition.
    - apply ackermann_tower_complete_le; auto with ord.
  Qed.

  Lemma ackermann_tower_fixpoint_aux:
    forall i i' x,
      i <= a ->
      i' < i ->
      complete i ->
      complete i' ->
      complete x ->
      veblen (ackermann_tower f i') (ackermann_tower f i x) 0 ≤ ackermann_tower f i x.
  Proof.
    intros i i'. induction x as [x Hindx] using ordinal_induction.
    intros Hia Hi'i Hi Hi' Hx.

    assert (Hq: forall q, complete q -> q < ackermann_tower f i x ->
                          fixOrd (veblen (ackermann_tower f i') q) 0 ≤ ackermann_tower f i x).
    { intros q Hqc Hq.
      rewrite ackermann_tower_unroll_nonzero in Hq; auto with ord.
      2: { apply ord_le_lt_trans with i'; auto with ord. }
      apply sup_lt in Hq. destruct Hq as [i'' Hq].
      rewrite ord_lt_unfold in Hi'i.
      destruct Hi'i as [z Hz].
      transitivity (fixOrd (veblen (ackermann_tower f z) q) 0).
      { apply fixOrd_monotone_func; auto with ord.
        intros. apply veblen_monotone_full; auto with ord. }
      rewrite ackermann_tower_unroll.
      rewrite <- lub_le2.
      destruct (complete_directed i Hi z i'') as [t [??]].
      rewrite <- (sup_le _ _ t).
      apply normal_fix_least; auto with ord.
      - apply veblen_normal; auto with ord.
        apply Hinduct_a; auto with ord.
        apply ord_lt_le_trans with i; auto with ord.
      - apply normal_fix_complete; auto with ord.
        + apply lim_complete.
          * intros; apply ackermann_tower_complete; auto with ord.
          * apply directed_monotone; auto with ord.
          * destruct x; apply Hx.
        + intros. apply normal_inflationary with (f:= fun x => veblen _ x 0); auto with ord.
          apply veblen_first_normal; auto with ord.
          apply Hinduct_a; auto with ord.
          apply ord_lt_le_trans with i; auto with ord.
        + intros. apply normal_complete; auto with ord.
          apply veblen_normal; auto with ord.
          apply Hinduct_a; auto with ord.
          apply ord_lt_le_trans with i; auto with ord.
      - apply veblen_collapse; auto with ord.
        + apply Hinduct_a; auto with ord.
          apply ord_lt_le_trans with i; auto with ord.
        + apply normal_fix_complete; auto with ord.
          * apply lim_complete.
            ** intros; apply ackermann_tower_complete; auto with ord.
            ** apply directed_monotone; auto with ord.
            ** destruct x; apply Hx.
          * intros. apply normal_inflationary with (f:= fun x => veblen _ x 0); auto with ord.
            apply veblen_first_normal; auto with ord.
            apply Hinduct_a; auto with ord.
            apply ord_lt_le_trans with i; auto with ord.
          * intros. apply normal_complete; auto with ord.
            apply veblen_normal; auto with ord.
            apply Hinduct_a; auto with ord.
            apply ord_lt_le_trans with i; auto with ord.

        + apply normal_fix_complete; auto with ord.
          * apply lim_complete.
            ** intros; apply ackermann_tower_complete; auto with ord.
            ** apply directed_monotone; auto with ord.
            ** destruct x; apply Hx.
          * intros. apply normal_inflationary with (f:= fun x => veblen _ x 0); auto with ord.
            apply veblen_first_normal; auto with ord.
            apply Hinduct_a; auto with ord.
            apply ord_lt_le_trans with i; auto with ord.
          * intros. apply normal_complete; auto with ord.
            apply veblen_normal; auto with ord.
            apply Hinduct_a; auto with ord.
            apply ord_lt_le_trans with i; auto with ord.
        + eapply ord_lt_le_trans; [ apply Hq | ].
          apply fixOrd_monotone_func; auto with ord.
          intros; apply veblen_monotone_full; auto with ord.
        + rewrite normal_fixpoint at 2; auto with ord.
          * apply veblen_monotone_full; auto with ord.
          * apply veblen_first_normal; auto with ord.
            apply Hinduct_a; auto with ord.
            apply ord_lt_le_trans with i; auto with ord.
          * apply lim_complete.
            ** intros; apply ackermann_tower_complete; auto with ord.
            ** apply directed_monotone; auto with ord.
            ** destruct x; apply Hx.
    }
    rewrite veblen_unroll_nonzero; auto with ord.
    - unfold boundedSup. apply sup_least; simpl; intro q.
      transitivity (fixOrd (veblen (ackermann_tower f i') (sz q)) 0).
      { apply fixOrd_monotone; auto with ord.
        apply limit_least; intros []. }
      apply Hq; auto with ord.
      apply complete_subord.
      apply ackermann_tower_complete; auto.
    - apply Hinduct_a; auto with ord.
      apply ord_lt_le_trans with i; auto with ord.
    - apply ackermann_tower_nonzero; auto with ord.
  Qed.

  Lemma ackermann_tower_continuous:
    forall i,
      i <= a ->
      complete i ->
      scott_continuous (ackermann_tower f i).
  Proof.
    intros i Hia Hi. unfold scott_continuous.
    intros A fa a0 Hdir Hfa.
    rewrite ackermann_tower_unroll.
    apply lub_least.
    - transitivity (supOrd (fun x => f (fa x))).
      { apply normal_continuous; auto with ord. }
      apply sup_least; intro z.
      rewrite <- (sup_le _ _ z).
      rewrite ackermann_tower_unroll; auto with ord.
    - apply sup_least; intro i'.
      apply normal_fix_least; auto with ord.
      + apply veblen_first_normal.
        apply Hinduct_a; auto with ord.
        apply ord_lt_le_trans with i; auto with ord.
      + apply sup_complete; auto with ord.
        * intros; apply ackermann_tower_complete; auto with ord.
        * apply (directed_monotone (ord A fa)); simpl; auto with ord.
        * left. exists a0.
          rewrite ackermann_tower_unroll.
          rewrite <- lub_le1.
          apply normal_nonzero; auto with ord.
      + rewrite sup_unfold. simpl.
        apply limit_least.
        intros [z q]; simpl.
        rewrite <- (sup_le _ _ z).
        apply ackermann_tower_increasing; auto with ord.
      + transitivity (supOrd (fun z =>
            veblen (ackermann_tower f (sz i')) (ackermann_tower f i (fa z)) 0)).
        { apply normal_continuous with (f:= fun z => veblen _ z 0); auto with ord.
          - apply veblen_first_normal; auto with ord.
            apply Hinduct_a; auto with ord.
            apply ord_lt_le_trans with i; auto with ord.
          - apply (directed_monotone (ord A fa)); simpl; auto with ord.
          - intros; apply ackermann_tower_complete; auto with ord. }
        apply sup_least; intro z.
        rewrite <- (sup_le A _ z).
        apply ackermann_tower_fixpoint_aux; auto with ord.
  Qed.
End ackermann_tower.

Theorem ackermann_tower_normal:
  forall f a, normal_function f -> complete a -> normal_function (ackermann_tower f a).
Proof.
  intro f. induction a as [a Hinda] using ordinal_induction.
  intros Hf Ha.
  constructor.
  - intros; apply ackermann_tower_monotone; auto with ord.
  - intros; apply ackermann_tower_increasing; auto with ord.
  - intros; apply ackermann_tower_continuous with a; auto with ord.
  - intros; apply ackermann_tower_complete with a; auto with ord.
  - intros; apply ackermann_tower_nonzero; auto with ord.
Qed.

Global Hint Resolve ackermann_tower_normal: ord.

Theorem ackermann_tower_fixpoint:
  forall f a a' x,
    normal_function f ->
    complete a ->
    complete a' ->
    complete x ->
    a' < a ->
    veblen (ackermann_tower f a') (ackermann_tower f a x) 0 ≤ ackermann_tower f a x.
Proof.
  intros. apply ackermann_tower_fixpoint_aux with a; auto with ord.
Qed.

Theorem ackermann_tower_normal_first:
  forall f, normal_function f -> normal_function (fun a => ackermann_tower f a 0).
Proof.
  intros f Hf.
  constructor.
  - intros; apply ackermann_tower_monotone; auto with ord.
  - intros x y Hy Hxy.
    rewrite (ackermann_tower_unroll f y 0).
    rewrite <- lub_le2.
    rewrite ord_lt_unfold in Hxy.
    destruct Hxy as [i Hi].
    rewrite <- (sup_le _ _ i).
    apply ord_lt_le_trans with
      (fixOrd (fun d : Ord => veblen (ackermann_tower f (sz i)) d 0) 0).
    2:{ apply fixOrd_monotone; auto with ord. }
    unfold fixOrd.
    rewrite <- (sup_le _ _ 2%nat). simpl.
    rewrite <- veblen_fax; auto with ord.
    apply ord_le_lt_trans with (ackermann_tower f i 0).
    { apply ackermann_tower_monotone; auto with ord. }
    apply ackermann_tower_increasing; auto with ord.
    apply addOrd_complete; auto with ord.
    rewrite addOrd_zero_r.
    apply veblen_nonzero; auto with ord.
  - red. intros A fa a0 Hdir Hc.
    rewrite ackermann_tower_unroll.
    apply lub_least.
    { rewrite <- (sup_le _ _ a0).
      rewrite ackermann_tower_unroll.
      auto with ord. }
    apply sup_least.
    rewrite (sup_unfold A fa). simpl.
    intros [a z]; simpl.
    rewrite <- (sup_le _ _ a).
    rewrite ackermann_tower_unroll.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ z).
    apply fixOrd_monotone; auto with ord.
    apply limit_least; intros [].
  - intros. auto with ord.
  - intros. apply ackermann_tower_nonzero; auto.
Qed.

Global Hint Resolve ackermann_tower_normal_first: ord.

  
Lemma ackermann_tower_monotone_func: forall f g a x,
    normal_function f ->
    normal_function g ->
    complete a ->
    complete x ->
    (forall x, complete x -> f x ≤ g x) ->
    ackermann_tower f a x ≤ ackermann_tower g a x.
Proof.
  intros f g.
  induction a as [a Hinda] using ordinal_induction.
  induction x as [x Hindx] using ordinal_induction.
  intros Hf Hg Ha Hx Hfg.
  rewrite ackermann_tower_unroll. apply lub_least.
  - rewrite ackermann_tower_unroll.
    rewrite <- lub_le1.
    apply Hfg; auto.
  - apply sup_least; intro a'.
    apply normal_fix_least; auto with ord.
    + apply limit_least. intro i.
      rewrite Hindx; auto with ord.
      apply ackermann_tower_increasing; auto with ord.
    + rewrite <- (ackermann_tower_fixpoint g a a' x) at 2; auto with ord.
      apply veblen_monotone_func; auto with ord.
Qed.  

Lemma ackermann_tower_fax:
  forall f a x,
    normal_function f ->
    complete a ->
    complete x ->
    f (a + x) ≤ ackermann_tower f a x.
Proof.
  intros f a x.
  intros Hf Ha Hx.
  destruct (complete_zeroDec a); auto.
  { transitivity (f x).
    apply normal_monotone; auto with ord.
    rewrite H. apply addOrd_zero_l; auto with ord.
    rewrite ackermann_tower_unroll; auto with ord. }
  rewrite <- (ackermann_tower_fixpoint f a 0); auto with ord.
  rewrite <- veblen_fax; auto with ord.
  rewrite ackermann_tower_unroll. rewrite <- lub_le1.
  apply normal_monotone; auto with ord.
  rewrite addOrd_zero_r.
  revert x Hx.
  induction x as [x Hindx] using ordinal_induction.
  intro Hx.
  rewrite addOrd_unfold.
  apply lub_least; intros.
  - transitivity (ackermann_tower f a 0).
    + apply normal_inflationary with (f := fun a => ackermann_tower f a 0); auto.
      apply ackermann_tower_normal_first; auto.
    + apply ackermann_tower_monotone; auto with ord.
  - apply sup_least; intro i.
    apply succ_least.
    rewrite Hindx; auto with ord.
    apply ackermann_tower_increasing; auto with ord.
Qed.

Lemma ackermann_tower_zero f x:
  ackermann_tower f 0 x ≈ f x.
Proof.
  rewrite ackermann_tower_unroll.
  split; auto with ord.
  apply lub_least; auto with ord.
  apply sup_least; intros [].
Qed.

Lemma ackermann_tower_succ:
  forall f a x,
    normal_function f ->
    complete a ->
    complete x ->
    ackermann_tower f (succOrd a) x ≈
      enum_fixpoints (fun i => veblen (ackermann_tower f a) i 0) x.
Proof.
  intros f a.
  induction x as [x Hindx] using ordinal_induction.
  intros Hf Ha Hx.
  split.
  - rewrite ackermann_tower_unroll_nonzero with (succOrd a); auto with ord.
    apply sup_least; intros [].
    simpl in *.
    apply normal_fix_least; auto with ord.
    + apply limit_least; intro i.
      rewrite Hindx; auto with ord.
      apply normal_increasing; auto with ord.
    + rewrite enum_are_fixpoints at 2; auto with ord.
  - apply enum_least'; auto with ord.
    + rewrite <- (ackermann_tower_fixpoint f (succOrd a) a x) at 2; auto with ord.
    + intros. rewrite <- (Hindx x' H0); auto with ord.
      apply normal_increasing; auto with ord.
Qed.

Lemma ackermann_tower_add_closed:
  forall f α x p q,
    normal_function f ->
    complete α ->
    complete x ->
    0 < α ->
    p < ackermann_tower f α x ->
    q < ackermann_tower f α x ->
    p + q < ackermann_tower f α x.
Proof.
  intros.
  rewrite <- (ackermann_tower_fixpoint f α 0 ); auto with ord.
  apply ord_lt_le_trans with (veblen (addOrd 1) (ackermann_tower f α x) 0).
  - rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r.
    apply expOmega_additively_closed; auto with ord.
    rewrite <- normal_inflationary; auto with ord.
    rewrite <- normal_inflationary; auto with ord.
  - apply veblen_monotone_func; auto with ord.
    intros. apply onePlus_least_normal; auto with ord.
Qed.

Fixpoint ackermann_tower_fin (f: Ord -> Ord) (a:nat) : Ord -> Ord :=
  match a with
  | O => f
  | S a' => enum_fixpoints (fun x => veblen (ackermann_tower_fin f a') x 0)
  end.

Lemma ackermann_tower_fin_normal a:
  forall f, normal_function f -> normal_function (ackermann_tower_fin f a).
Proof.
  induction a; simpl; auto with ord.
Qed.

Global Hint Resolve ackermann_tower_fin_normal: ord.

Lemma ackermann_tower_fin_monotone_S f n x:
  normal_function f ->
  complete x ->
  ackermann_tower_fin f n x <= ackermann_tower_fin f (S n) x.
Proof.
  intros. simpl.
  rewrite enum_are_fixpoints; auto with ord.
  rewrite <- veblen_fax; auto with ord.
  apply normal_monotone; auto with ord.
  rewrite addOrd_zero_r.
  apply normal_inflationary; auto with ord.
Qed.

Lemma ackermann_tower_fin_monotone1 f m n x:
  normal_function f ->
  (m <= n)%nat ->
  complete x ->
  ackermann_tower_fin f m x <= ackermann_tower_fin f n x.
Proof.
  intros Hf Hmn.
  revert x Hf.
  induction Hmn; auto with ord.
  intros. rewrite IHHmn; auto with ord.
  apply ackermann_tower_fin_monotone_S; auto.
Qed.

Lemma ackermann_tower_fin_monotone f m n x y:
  normal_function f ->
  (m <= n)%nat ->
  x <= y ->
  complete x ->
  ackermann_tower_fin f m x <= ackermann_tower_fin f n y.
Proof.
  intros. transitivity (ackermann_tower_fin f n x).
  apply ackermann_tower_fin_monotone1; auto with ord.
  apply normal_monotone; auto with ord.
Qed.

Lemma ackermann_tower_fin_eq f a x:
  normal_function f ->
  complete x ->
  ackermann_tower_fin f a x ≈ ackermann_tower f (natOrdSize a) x.
Proof.
  revert f x. induction a; simpl; intros.
  - intros. rewrite ackermann_tower_zero. auto with ord.
  - intros. rewrite ackermann_tower_succ; auto with ord.
    split; apply enum_fixpoints_func_mono; auto with ord.
    + intros. apply veblen_monotone_func; auto with ord.
      intros; apply IHa; auto.
    + intros. apply veblen_monotone_func; auto with ord.
      intros; apply IHa; auto.
Qed.

Lemma ackermann_tower_fin_fixpoints:
  forall n f m x,
    normal_function f ->
    (m < n)%nat ->
    complete x ->
    veblen (ackermann_tower_fin f m) (ackermann_tower_fin f n x) 0 ≤ ackermann_tower_fin f n x.
Proof.
  induction n; intros. lia.
  simpl.
  rewrite enum_are_fixpoints at 2; auto with ord.
  apply veblen_monotone_func; auto with ord.
  intros. apply ackermann_tower_fin_monotone; auto with ord.
  lia.
Qed.

Definition SmallAckermannOrdinal := supOrd (fun n:ω => ackermann_tower_fin (addOrd 1) n 0).

Definition LargeAckermannOrdinal := fixOrd (fun x => ackermann_tower (addOrd 1) x 0) 0.

Lemma ackermann_tower_base_le: forall a x,
    complete a ->
    complete x ->
    ackermann_tower (expOrd ω) a x <= ackermann_tower (addOrd 1) (1+a) x.
Proof.
  induction a as [a Hinda] using ordinal_induction.
  induction x as [x Hindx] using ordinal_induction.
  intros Ha Hx.
  rewrite ackermann_tower_unroll.
  apply lub_least.
  - rewrite <- ackermann_tower_fixpoint with (a':=0); auto with ord.
    transitivity (veblen (addOrd 1) (ackermann_tower (addOrd 1) (1 + a) x) 0).
    + rewrite veblen_onePlus; auto with ord.
      rewrite addOrd_zero_r.
      apply expOrd_monotone.
      apply normal_inflationary; auto with ord.
    + apply veblen_monotone_func; auto with ord.
      intros; apply onePlus_least_normal; auto with ord.

  - apply sup_least; intro a'.
    apply normal_fix_least; auto with ord.
    + apply limit_least; intro i.
      rewrite Hindx; auto with ord.
      apply ackermann_tower_increasing; auto with ord.
    + rewrite <- ackermann_tower_fixpoint with (a':= 1+a') at 2; auto with ord.
      apply veblen_monotone_func; auto with ord.
      apply addOrd_increasing; auto with ord.
Qed.

Lemma ackermann_tower_fix_limit: forall f x,
    normal_function f ->
    complete x ->
    limitOrdinal (fixOrd (fun x => ackermann_tower f x 0) x).
Proof.
  intros.
  apply additively_closed_limit; auto with ord.
  - rewrite normal_fixpoint; auto with ord.
    rewrite <- ackermann_tower_fax; auto with ord.
    2:{ apply normal_fix_complete; auto with ord.
        apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord. }
    apply ord_le_lt_trans with (1+0); auto with ord.
    apply ord_le_lt_trans with (f 0).
    { apply onePlus_least_normal; auto with ord. }
    apply normal_increasing; auto with ord.
    { apply addOrd_complete; auto with ord.
      apply normal_fix_complete; auto with ord.
      intros.
      apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord. }
    rewrite addOrd_zero_r.
    rewrite normal_fixpoint; auto with ord.
    apply normal_nonzero with (f:=fun x => ackermann_tower _ x 0); auto with ord.

  - hnf; intros.
    rewrite normal_fixpoint; auto with ord.
    apply ackermann_tower_add_closed; auto with ord.
    + apply normal_fix_complete; auto with ord.
      apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
    + rewrite normal_fixpoint; auto with ord.
      apply normal_nonzero with (f:=fun x => ackermann_tower _ x 0); auto with ord.
    + rewrite <- normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
      apply normal_fix_complete; auto with ord.
      apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
    + rewrite <- normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
      apply normal_fix_complete; auto with ord.
      apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
Qed.

Lemma LargeAckermannOrdinal_limit: limitOrdinal LargeAckermannOrdinal.
Proof.
  unfold LargeAckermannOrdinal.
  apply ackermann_tower_fix_limit; auto with ord.
Qed.

Lemma ackermann_tower_base_eq: forall a x,
    complete a ->
    complete x ->
    1 + a ≤ a ->
    ackermann_tower (addOrd 1) a x ≈ ackermann_tower (expOrd ω) a x. 
Proof.
  intros a.
  induction x as [x Hindx] using ordinal_induction.
  intros Hac Hxc Ha.
  split.
  - apply ackermann_tower_monotone_func; auto with ord.
    intros. apply onePlus_least_normal; auto with ord.
  - rewrite ackermann_tower_unroll. apply lub_least.
    + transitivity (ackermann_tower (expOrd ω) 0 x).
      { rewrite ackermann_tower_unroll; auto with ord. }
      transitivity (ackermann_tower (addOrd 1) (1 + 0) x).
      apply ackermann_tower_base_le; auto with ord.
      apply ackermann_tower_monotone; auto with ord.
      rewrite <- Ha.
      apply addOrd_monotone; auto with ord.
    + apply sup_least; intro a'.
      apply normal_fix_least; auto with ord.
      * apply limit_least; intro i.
        rewrite <- Hindx; auto with ord.
        apply normal_increasing; auto with ord.
      * assert (Hlt: 1 + a' < a).
        { apply ord_lt_le_trans with (1 + a); auto.
          apply addOrd_increasing; auto with ord. }
        rewrite <- ackermann_tower_fixpoint with (a':=1+a') at 2; auto with ord.
        apply veblen_monotone_func; auto with ord.
        intros.
        apply ackermann_tower_base_le; auto with ord.
Qed.

Lemma SmallAckermannOrdinal_alt :
  SmallAckermannOrdinal ≈ ackermann_tower (addOrd 1) ω 0.
Proof.
  unfold SmallAckermannOrdinal. split.
  - apply sup_least; intro i.
    rewrite ackermann_tower_fin_eq; auto with ord.
  - rewrite ackermann_tower_unroll.
    apply lub_least.
    { rewrite addOrd_zero_r. apply succ_least.
      rewrite <- (sup_le _ _ O).
      apply normal_nonzero; auto with ord. }
    apply sup_least; intro i.
    rewrite <- (sup_le _ _ (S i)).
    rewrite ackermann_tower_fin_eq; auto with ord.
    apply normal_fix_least; auto with ord.
    { apply limit_least; intros []. }
    simpl.
    rewrite <- ackermann_tower_fixpoint with (a':=natOrdSize i) at 2; auto with ord.
Qed.

Lemma SmallAckermannOrdinal_alt2 :
  SmallAckermannOrdinal ≈ ackermann_tower (expOrd ω) ω 0.
Proof.
  rewrite SmallAckermannOrdinal_alt.
  apply ackermann_tower_base_eq; auto with ord.
  apply additively_closed_collapse; auto with ord.
  apply additively_closed_omega.
Qed.

Lemma LargeAckermannOrdinal_alt:
  LargeAckermannOrdinal ≈ fixOrd (fun x => ackermann_tower (expOrd ω) x 0) 0.
Proof.
  unfold LargeAckermannOrdinal.
  split.
  - apply normal_fix_least; auto with ord.
    + apply normal_fix_complete; auto with ord.
      intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
    + rewrite normal_fixpoint at 2; auto with ord.
      apply ackermann_tower_base_eq; auto with ord.
      * apply normal_fix_complete; auto with ord.
        intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
      * rewrite normal_fixpoint at 2; auto with ord.
        apply onePlus_least_normal with (f:=fun x => ackermann_tower _ x 0); auto with ord.
        apply normal_fix_complete; auto with ord.
        intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
  - apply normal_fix_least; auto with ord.
    + apply normal_fix_complete; auto with ord.
      intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
    + rewrite normal_fixpoint at 2; auto with ord.
      apply ackermann_tower_base_eq; auto with ord.
      * apply normal_fix_complete; auto with ord.
        intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
      * rewrite normal_fixpoint at 2; auto with ord.
        apply onePlus_least_normal with (f:=fun x => ackermann_tower _ x 0); auto with ord.
        apply normal_fix_complete; auto with ord.
        intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
Qed.
