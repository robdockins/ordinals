Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import List.
Import ListNotations.
Open Scope list.
Require Import Lia.

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
From Ordinal Require Import VTowerFin.

Open Scope ord_scope.

Section vtower.

Local Hint Resolve
      zero_complete
      succ_complete
      addOrd_complete
      complete_subord : core.

Section nextCritical.
Definition nextCritical (f: Ord -> Ord) (y x:Ord) :=
  supOrd (fun z:y => fixOrd (veblen f z) x).

Lemma nextCritical_mono f g y' y x' x :
  (forall x, f x <= g x) ->
  (forall x y, x <= y -> g x <= g y) ->
  y' <= y ->
  x' <= x ->
  nextCritical f y' x' <= nextCritical g y x.
Proof.
  intros.
  unfold nextCritical.
  apply sup_least; intro z.
  destruct (ord_le_subord y' y H1 z) as [z' ?].
  rewrite <- (sup_le _ _ z').
  unfold fixOrd.
  apply sup_ord_le_morphism.
  intro n. induction n; simpl; auto.
  transitivity
    (veblen g (sz z) (iter_f (veblen f (sz z)) x' n)).
  { apply veblen_mono_func; auto with ord. }
  apply veblen_le_mor; auto with ord.
Qed.

Lemma nextCritical_complete : forall f y x,
    normal_function f ->
    complete y ->
    complete x ->
    complete (nextCritical f y x).
Proof.
  intros. unfold nextCritical.
  apply sup_complete.
  - intro a. apply normal_fix_complete; auto.
    intros. apply veblen_inflationary; auto.
    intros. apply veblen_monotone; auto.
    intros. apply normal_monotone; auto.
    intros; apply normal_complete; auto.
    apply veblen_normal; auto.
  - hnf; intros.
    destruct (complete_directed y H0 a1 a2) as [a' [??]].
    exists a'.
    split.
    apply normal_fix_least; auto.
    apply veblen_normal; auto.
    + apply normal_fix_complete; auto.
      * intros; apply normal_inflationary; auto.
        apply veblen_normal; auto.
      * intros. apply veblen_monotone; auto.
        apply normal_monotone; auto.
      * intros. apply veblen_complete; auto.
        apply normal_complete; auto.
    + apply fixOrd_above.
    + transitivity (veblen f a' (fixOrd (veblen f a') x)).
      apply veblen_monotone_first; auto with ord.
      intros; apply normal_monotone; auto.
      apply normal_fixpoint; auto.
      apply veblen_normal; auto.
    + apply normal_fix_least; auto.
      apply veblen_normal; auto.
      { apply normal_fix_complete; auto.
        * intros; apply normal_inflationary; auto.
          apply veblen_normal; auto.
        * intros. apply veblen_monotone; auto.
          apply normal_monotone; auto.
        * intros. apply veblen_complete; auto.
          apply normal_complete; auto. }
      apply fixOrd_above.
      transitivity (veblen f a' (fixOrd (veblen f a') x)).
      apply veblen_monotone_first; auto with ord.
      intros; apply normal_monotone; auto.
      apply normal_fixpoint; auto.
      apply veblen_normal; auto.
  - destruct (complete_zeroDec y H0).
    + right. intro a.
      destruct (ord_le_subord y 0 H2 a) as [[] _].
    + rewrite ord_lt_unfold in H2. destruct H2 as [a ?].
      left. exists a.
      rewrite normal_fixpoint; auto.
      apply veblen_nonzero; auto.
      apply veblen_normal; auto.
Qed.

Lemma nextCritical_above : forall f y x, 0 < y -> x <= nextCritical f y x.
Proof.
  intros. unfold nextCritical.
  rewrite ord_lt_unfold in H.
  destruct H as [y0 _].
  rewrite <- (sup_le _ _ y0).
  apply fixOrd_above.
Qed.

Lemma directed_monotone :
  forall (a:Ord) f,
    (forall (x y:a), sz x <= sz y -> f x <= f y) ->
    complete a ->
    directed a f.
Proof.
  intros.
  hnf; simpl; intros.
  destruct (complete_directed a H0 a1 a2) as [a' [??]].
  exists a'.
  split; apply H; auto.
Qed.

Lemma nextCritical_critical :
  forall f y x y',
    normal_function f ->
    complete y' ->
    complete y ->
    complete x ->
    y' < y ->
    veblen f y' (nextCritical f y x) ≈ nextCritical f y x.
Proof.
  intros f y x y' Hf Hcy' Hcy Hcx.
  split.
  - intros. unfold nextCritical at 1.
    generalize H; intro.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [y0  ?].
    etransitivity.
    { apply normal_continuous; auto.
      apply veblen_normal; auto.
      apply directed_monotone; auto.
      intros; apply fixOrd_monotone_func; auto.
      intros; apply veblen_monotone_first; auto.
      apply normal_monotone; auto.
      intros; apply veblen_monotone; auto.
      apply normal_monotone; auto.
      intros. apply normal_fix_complete; auto.
      intros; apply normal_inflationary; auto.
      apply veblen_normal; auto.
      intros. apply veblen_monotone; auto.
      apply normal_monotone; auto.
      apply normal_complete.
      apply veblen_normal; auto. }

    apply sup_least; intro y1.
    destruct (complete_directed y Hcy y0 y1) as [y2 [??]].
    unfold nextCritical.
    rewrite <- (sup_le _ _ y2).
    rewrite (normal_fixpoint (veblen f (sz y2))); auto.
    transitivity (veblen f y2 (fixOrd (veblen f (sz y1)) x)).
    apply veblen_monotone_first; auto.
    intros; apply normal_monotone; auto.
    rewrite H0; auto.
    apply veblen_monotone; auto.
    intros; apply normal_monotone; auto.
    apply normal_fix_least; auto.
    apply veblen_normal; auto.
    { apply normal_fix_complete; auto.
      intros. apply veblen_inflationary; auto.
      intros; apply veblen_monotone; auto.
      apply normal_monotone; auto.
      apply normal_complete.
      apply veblen_normal; auto. }
    apply fixOrd_above; auto.
    rewrite (normal_fixpoint (veblen f y2)) at 2; auto.
    apply veblen_monotone_first; auto.
    intros; apply normal_monotone; auto.
    apply veblen_normal; auto.
    apply veblen_normal; auto.
  - apply normal_inflationary; auto.
    apply veblen_normal; auto.
    apply nextCritical_complete; auto.
Qed.


Lemma nextCritical_least : forall f y x z,
    normal_function f ->
    complete y ->
    complete z ->
    x <= z ->
    (forall y', complete y' ->
        y' < y -> veblen f y' z <= z) ->
    nextCritical f y x <= z.
Proof.
  intros.
  unfold nextCritical.
  apply sup_least; intro y0.
  apply normal_fix_least; auto.
  apply veblen_normal; auto.
  apply H3; auto with ord.
Qed.

Lemma nextCritical_fix : forall f y x,
    normal_function f ->
    complete x ->
    complete y ->
    0 < y ->
    f (nextCritical f y x) <= nextCritical f y x.
Proof.
  intros.
  rewrite <- veblen_zero.
  apply nextCritical_critical; auto.
Qed.

End nextCritical.

Section vtower_def.
  Variable f : Ord -> Ord.
  Variable normal_f : normal_function f.

  Fixpoint vtower (b:Ord) : Ord -> Ord :=
    fix inner (y:Ord) : Ord :=
      match b, y with
      | ord B g, ord Y h =>
        f (ord Y h) ⊔
          supOrd (fun a:B =>
                    nextCritical
                      (vtower (g a))
                      (1 + ord Y h)
                      (limOrd (fun x:Y => inner (h x))))

      end.

  Lemma vtower_unroll : forall b y,
      vtower b y = f y ⊔ supOrd (fun a:b => nextCritical (vtower a) (1+y) (limOrd (fun x => vtower b (y x)))).
  Proof.
    destruct b as [B g].
    destruct y as [Y h].
    reflexivity.
  Qed.

  Global Opaque vtower.

  Theorem vtower_monotone : forall a b x y, a <= b -> x <= y -> vtower a x <= vtower b y.
  Proof.
    intros a b x y. revert y a x.
    induction b as [b Hb] using ordinal_induction.
    induction y as [y Hy] using ordinal_induction.
    intros.

    rewrite (vtower_unroll a x).
    rewrite (vtower_unroll b y).
    apply lub_least.
    { rewrite <- lub_le1. apply normal_monotone; auto. }
    apply sup_least. intro ia.
    rewrite <- lub_le2.
    destruct (ord_le_subord a b H ia) as [ib ?].
    rewrite <- (sup_le _ _ ib).
    unfold nextCritical.
    apply sup_least; intro ix.
    assert (1 + x <= 1 + y).
    { apply addOrd_monotone; auto with ord; auto. }
    destruct (ord_le_subord (1+x) (1+y) H2 ix) as [iy ?].
    rewrite <- (sup_le _ _ iy).
    unfold fixOrd. apply sup_ord_le_morphism.
    intro n.
    induction n; simpl.
    - rewrite ord_le_unfold; simpl; intro q.
      destruct (ord_le_subord x y H0 q) as [q' ?].
      rewrite ord_lt_unfold. simpl. exists q'.
      apply Hy; auto with ord.
    - etransitivity; [ apply (veblen_mono_func (vtower ia) (vtower ib)); auto with ord |].
      apply veblen_le_mor; auto with ord.
  Qed.

  Global Add Parametric Morphism : vtower
      with signature ord_le ==> ord_le ==> ord_le
        as vtower_le_mor.
  Proof.
    intros; apply vtower_monotone; auto.
  Qed.

  Global Add Parametric Morphism : vtower
      with signature ord_eq ==> ord_eq ==> ord_eq
        as vtower_eq_mor.
  Proof.
    unfold ord_eq.
    intros; split; apply vtower_monotone; intuition.
  Qed.

  Section vtower_normal.
    Variable b:Ord.
    Hypothesis Hcomplete_b : complete b.
    Hypothesis vtower_normal : forall a, a < b -> complete a -> normal_function (vtower a).

    Lemma vtower_complete x :
      complete b ->
      complete x ->
      complete (vtower b x).
    Proof.
      induction x as [X h Hind].
      intros.
      rewrite vtower_unroll.
      destruct (complete_zeroDec b H).
      - apply lub_complete1.
        + apply sup_least. intro.
          destruct (ord_le_subord b 0 H1 a) as [[] _].
        + apply normal_complete; auto.
        + assert (forall (P:Prop) (a:b), P).
          { intros. destruct (ord_le_subord b 0 H1 a) as [[] _]. }
          apply sup_complete; auto.
          * intros; apply (H2 _ a).
          * hnf; intros. apply (H2 _ a1).
          * right; intros; auto.
            apply (H2 _ a).
      - apply lub_complete2.
        + rewrite ord_lt_unfold in H1.
          destruct H1 as [a ?].
          rewrite <- (sup_le _ _ a).
          rewrite <- nextCritical_critical; auto.
          rewrite veblen_zero.
          rewrite vtower_unroll.
          rewrite <- lub_le1.
          apply normal_monotone; auto.
          rewrite <- nextCritical_above; auto.
          rewrite ord_le_unfold; intro q.
          rewrite ord_lt_unfold; exists q; simpl.
          rewrite vtower_unroll.
          rewrite <- lub_le1.
          apply normal_inflationary; auto.
          apply H0.
          rewrite <- addOrd_le1; auto with ord.
          apply vtower_normal; auto with ord.
          apply zero_complete.
          { apply lim_complete; auto.
            intros. apply Hind; auto.
            apply H0.
            apply directed_monotone; auto.
            intros; apply vtower_monotone; auto with ord.
            apply H0.
          }
          rewrite <- addOrd_le1; auto with ord.
        + apply normal_complete; auto.
        + apply sup_complete.
          * intros.
            apply nextCritical_complete.
            apply vtower_normal; auto with ord.
            apply addOrd_complete; auto.
            apply lim_complete.
            ** intros. apply Hind; auto.
               apply H0.
            ** apply directed_monotone; auto.
               intros; apply vtower_monotone; auto with ord.
            ** apply H0.
          * apply directed_monotone; auto.
            intros.
            apply nextCritical_mono; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            intros; apply vtower_monotone; auto with ord.
          * left.
            rewrite ord_lt_unfold in H1.
            destruct H1 as [b0 ?].
            exists b0.
            rewrite <- nextCritical_critical; auto.
            rewrite veblen_zero.
            apply normal_nonzero; auto with ord.
            auto with ord.
            apply zero_complete.
            { apply lim_complete; auto.
              intros. apply Hind; auto.
              apply H0.
              apply directed_monotone; auto.
              intros; apply vtower_monotone; auto with ord.
              apply H0.
            }
            rewrite <- addOrd_le1; auto with ord.
    Qed.

    Lemma vtower_complete_lemma1 x :
      complete x ->
      complete (limOrd (fun i : x => vtower b (x i))).
    Proof.
      intros.
      apply lim_complete.
      intros. apply vtower_complete; auto.
      apply directed_monotone; auto.
      intros. apply vtower_monotone; auto with ord.
      destruct x; apply H.
    Qed.

    Lemma vtower_complete_lemma2 x (a:b) : 
      complete x ->
      complete
          (nextCritical (vtower (sz a)) (1 + x)
                        (limOrd (fun i : x => vtower b (x i)))).
    Proof.
      intros.
      apply nextCritical_complete; auto.
      apply vtower_normal; auto with ord.
      apply vtower_complete_lemma1; auto.
    Qed.

    Lemma vtower_complete_lemma3 x :
      complete x ->
      complete
        (supOrd
           (fun a : b =>
              nextCritical (vtower (sz a)) (1 + x)
                           (limOrd (fun i : x => vtower b (x i))))).
    Proof.
      intros.
      apply sup_complete.
      - intro. apply vtower_complete_lemma2; auto.
      - apply directed_monotone; auto.
        intros. apply nextCritical_mono; auto with ord.
        intros; apply vtower_monotone; auto with ord.
        intros; apply vtower_monotone; auto with ord.
      - destruct (complete_zeroDec b Hcomplete_b).
        + right. intro.
          destruct (ord_le_subord b 0 H0 a) as [[] _].
        + rewrite ord_lt_unfold in H0.
          destruct H0 as [a ?].
          left. exists a.
          rewrite <- nextCritical_critical; auto.
          rewrite veblen_zero.
          apply normal_nonzero; auto.
          apply vtower_normal; auto with ord.
          apply vtower_normal; auto with ord.
          apply zero_complete.
          apply vtower_complete_lemma1; auto.
          rewrite <- addOrd_le1.
          auto with ord.
    Qed.

    Lemma vtower_nextCritical_directed x :
      complete x ->
      directed b
               (fun a : b =>
                  nextCritical (vtower (sz a)) (1 + x)
                               (limOrd (fun i : x => vtower b (x i)))).
    Proof.
      intros.
      apply directed_monotone; auto.
      intros. apply nextCritical_mono; auto with ord.
      intros; apply vtower_monotone; auto with ord.
      intros; apply vtower_monotone; auto with ord.
    Qed.

    Local Hint Resolve
          vtower_complete
          vtower_complete_lemma1 vtower_complete_lemma2
          vtower_complete_lemma3
          vtower_nextCritical_directed : core.

    Lemma nextCritical_strongly_critical : forall a y x,
        forall a',
          complete a' ->
          complete a ->
          complete x ->
          complete y ->
          y > 0 -> a < b ->
          a' < a -> veblen (vtower a') (nextCritical (vtower a) y x) 0 <= nextCritical (vtower a) y x.
    Proof.
      intros a y x.
      revert a y.
      induction x as [X g Hx].
      intros a y a' Hca' Hca Hcx Hcy Hy Hb Ha.
      unfold nextCritical.
      rewrite ord_lt_unfold in Hy.
      destruct Hy as [y0 _].
      etransitivity.
      { apply (normal_continuous (fun q => veblen (vtower a') q 0)); auto.
        + apply veblen_first_normal; auto.
          apply vtower_normal; auto.
          transitivity a; auto.
        + apply directed_monotone; auto.
          intros; apply fixOrd_monotone_func; auto.
          intros; apply veblen_monotone_first; auto.
          intros; apply vtower_monotone; auto with ord.
          intros; apply veblen_monotone; auto.
          intros; apply vtower_monotone; auto with ord.
        + intro. apply normal_fix_complete; auto.
          * apply normal_inflationary.
            apply veblen_normal; auto.
          * apply veblen_monotone; auto.
            intros; apply vtower_monotone; auto with ord.
          * apply normal_complete; auto.
            apply veblen_normal; auto. }

      apply sup_least; intro i.
      rewrite <- (sup_le _ _ i).
      rewrite (normal_fixpoint) at 2; auto.

      transitivity (vtower a (fixOrd (veblen (vtower a) (sz i)) (ord X g))).
      rewrite vtower_unroll.
      rewrite <- lub_le2.
      generalize Ha; intros.
      rewrite ord_lt_unfold in Ha0.
      destruct Ha0.
      rewrite <- (sup_le _ _ x).

      rewrite veblen_unroll.
      apply lub_least.
      rewrite <- (nextCritical_critical _ _ _ 0); auto.
      rewrite veblen_zero.
      transitivity (vtower x 0).
      apply vtower_monotone; auto with ord.
      apply normal_monotone; auto with ord.
      apply vtower_normal; auto with ord.
      transitivity a; auto with ord.
      apply vtower_normal; auto with ord.
      transitivity a; auto with ord.
      { apply addOrd_complete; auto.
        apply normal_fix_complete; auto.
        apply veblen_inflationary; auto with ord.
        intros; apply veblen_monotone; auto with ord.
        intros; apply vtower_monotone; auto with ord.
        apply veblen_complete; auto.
        apply normal_complete; auto. }
      { assert (complete (fixOrd (veblen (vtower a) (sz i)) (ord X g))).
        { apply normal_fix_complete; auto.
          apply normal_inflationary.
          apply veblen_normal; auto with ord.
          intros; apply normal_monotone; auto with ord.
          apply veblen_normal; auto with ord.
          apply normal_complete.
          apply veblen_normal; auto with ord. }
        apply lim_complete; auto.
        simpl. intro.
        apply normal_complete; auto.
        apply directed_monotone; auto.
        intros; apply vtower_monotone; auto with ord.
        apply H0.
      }

      rewrite <- addOrd_le1. auto with ord.

      simpl.
      apply sup_least; intro.
      apply normal_fix_least; auto.
      apply veblen_normal; auto.
      apply vtower_normal; auto with ord.
      transitivity a; auto.
      apply complete_subord.
      apply iter_f_complete; auto.
      apply normal_complete; auto with ord.
      apply veblen_normal; auto.
      apply nextCritical_complete; auto with ord.
      apply vtower_normal; auto with ord.
      transitivity a; auto with ord.
      { apply addOrd_complete; auto.
        apply normal_fix_complete; auto.
        apply veblen_inflationary; auto with ord.
        intros; apply veblen_monotone; auto with ord.
        intros; apply vtower_monotone; auto with ord.
        apply veblen_complete; auto.
        apply normal_complete; auto. }
      { apply lim_complete; auto.
        simpl. intro.
        apply normal_complete; auto.
        apply complete_subord.
        apply normal_fix_complete; auto.
        apply normal_inflationary.
        apply veblen_normal; auto with ord.
        intros; apply veblen_monotone; auto.
        intros; apply vtower_monotone; auto with ord.
        apply normal_complete.
        apply veblen_normal; auto with ord.
        assert (complete (fixOrd (veblen (vtower a) (sz i)) (ord X g))).
        { apply normal_fix_complete; auto.
          apply normal_inflationary.
          apply veblen_normal; auto with ord.
          intros; apply normal_monotone; auto with ord.
          apply veblen_normal; auto with ord.
          apply normal_complete.
          apply veblen_normal; auto with ord. }
        apply directed_monotone; auto.
        intros; apply vtower_monotone; auto with ord.
      }
      rewrite ord_le_unfold; intros [].

      rewrite <- (nextCritical_critical _ _ _) at 2; auto.
      apply veblen_monotone_func; auto.
      apply vtower_normal; auto.
      transitivity a; auto.
      apply vtower_normal.
      transitivity a; auto with ord.
      apply complete_subord; auto.
      intros; apply vtower_monotone; auto with ord.
      { apply complete_subord.
        apply iter_f_complete; auto.
        apply normal_complete.
        apply veblen_normal; auto with ord. }
      { apply nextCritical_complete; auto with ord.
        apply vtower_normal; auto with ord.
        transitivity a; auto with ord.
        { apply addOrd_complete; auto.
          apply normal_fix_complete; auto.
          apply veblen_inflationary; auto with ord.
          intros; apply veblen_monotone; auto with ord.
          intros; apply vtower_monotone; auto with ord.
          apply veblen_complete; auto.
          apply normal_complete; auto. }
        { apply lim_complete; auto.
          simpl. intro.
          apply normal_complete; auto.
          apply complete_subord.
          apply normal_fix_complete; auto.
          apply normal_inflationary.
          apply veblen_normal; auto with ord.
          intros; apply veblen_monotone; auto.
          intros; apply vtower_monotone; auto with ord.
          apply normal_complete.
          apply veblen_normal; auto with ord.
          assert (complete (fixOrd (veblen (vtower a) (sz i)) (ord X g))).
          { apply normal_fix_complete; auto.
            apply normal_inflationary.
            apply veblen_normal; auto with ord.
            intros; apply normal_monotone; auto with ord.
            apply veblen_normal; auto with ord.
            apply normal_complete.
            apply veblen_normal; auto with ord. }
          apply directed_monotone; auto.
          intros; apply vtower_monotone; auto with ord.
        }
      }

      apply vtower_normal; auto.
      transitivity a; auto with ord.

      { apply complete_subord.
        apply iter_f_complete; auto.
        apply normal_complete.
        apply veblen_normal; auto with ord. }
      { apply addOrd_complete.
        apply succ_complete. apply zero_complete; auto.
        apply normal_fix_complete; auto.
        apply normal_inflationary.
        apply veblen_normal; auto with ord.
        intros; apply normal_monotone; auto with ord.
        apply veblen_normal; auto with ord.
        apply normal_complete.
        apply veblen_normal; auto with ord. }
      { apply lim_complete; auto.
        simpl. intro.
        apply normal_complete; auto.
        apply complete_subord.
        apply normal_fix_complete; auto.
        apply normal_inflationary.
        apply veblen_normal; auto with ord.
        intros; apply veblen_monotone; auto.
        intros; apply vtower_monotone; auto with ord.
        apply normal_complete.
        apply veblen_normal; auto with ord.
        assert (complete (fixOrd (veblen (vtower a) (sz i)) (ord X g))).
        { apply normal_fix_complete; auto.
          apply normal_inflationary.
          apply veblen_normal; auto with ord.
          intros; apply normal_monotone; auto with ord.
          apply veblen_normal; auto with ord.
          apply normal_complete.
          apply veblen_normal; auto with ord. }
        apply directed_monotone; auto.
        intros; apply vtower_monotone; auto with ord.
      }

      rewrite <- addOrd_le2.
      rewrite ord_lt_unfold. exists a0; auto with ord.

      rewrite <- veblen_zero.
      apply veblen_monotone_first; auto with ord.
      intros. apply normal_monotone; auto with ord.
      apply veblen_normal; auto.
    Qed.

    Lemma vtower_inc : forall x y, complete y -> x < y -> vtower b x < vtower b y.
    Proof.
      intros x y. revert x.
      induction y as [Y h Hy]. intros.
      rewrite (vtower_unroll b (ord Y h)).
      destruct (complete_zeroDec b Hcomplete_b).
      - assert (b ≈ 0).
        { split; auto with ord. }
        rewrite <- lub_le1.
        apply ord_le_lt_trans with (f x); auto.
        rewrite (vtower_unroll b x).
        apply lub_least; auto with ord.
        apply sup_least; intro.
        destruct (ord_le_subord b 0 H1 a) as [[] _].
        apply normal_increasing; auto.
      - rewrite ord_lt_unfold in H1.
        destruct H1 as [q _].
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ q).
        rewrite <- nextCritical_above.
        rewrite ord_lt_unfold. simpl.
        rewrite ord_lt_unfold in H0.
        destruct H0 as [i ?].
        exists i.
        apply vtower_monotone; auto with ord.
        rewrite <- addOrd_le1.
        auto with ord.
    Qed.

    Lemma vtower_inflate : forall x, complete x -> x <= vtower b x.
    Proof.
      intros.
      rewrite vtower_unroll.
      rewrite <- lub_le1.
      apply normal_inflationary; auto.
    Qed.

    Lemma nextCritical_inflate_lemma : forall x (a0:b),
        complete x ->
        vtower b x <= supOrd (fun a:b => nextCritical (vtower a) (1+x) (limOrd (fun i => vtower b (x i)))).
    Proof.
      intros.
      rewrite (vtower_unroll b x).
      apply lub_least; auto with ord.
      rewrite <- (sup_le _ _ a0).
      rewrite <- nextCritical_critical; auto.
      rewrite veblen_zero.
      rewrite vtower_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      rewrite <- nextCritical_above.
      rewrite ord_le_unfold. intro i.
      rewrite ord_lt_unfold. exists i. simpl.
      apply vtower_inflate; auto.
      rewrite <- addOrd_le1.
      auto with ord.
      apply vtower_normal; auto with ord.
      apply zero_complete.
      rewrite <- addOrd_le1.
      auto with ord.
    Qed.

    Lemma vtower_fixpoint' : forall a x,
      complete a -> complete x ->
      a < b -> vtower a (vtower b x) <= vtower b x.
    Proof.
      induction a as [A g Hinda].
      intros x Hca Hcx H.
      rewrite (vtower_unroll (ord A g)).
      apply lub_least.
      { rewrite ord_lt_unfold in H. destruct H as [b0 ?].
        etransitivity.
        { apply normal_monotone; auto.
          apply (nextCritical_inflate_lemma x b0); auto.
        }
        etransitivity.
        { apply normal_continuous; auto. }
        apply sup_least; intro i.
        rewrite (vtower_unroll b x).
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ i).
        rewrite <- nextCritical_critical at 2; auto.
        rewrite veblen_zero.
        rewrite vtower_unroll.
        apply lub_le1.
        apply vtower_normal; auto with ord.
        apply zero_complete.
        rewrite <- addOrd_le1.
        auto with ord. }

      apply sup_least; intro q.
      apply nextCritical_least; auto.
      + apply vtower_normal; auto with ord.
        transitivity (ord A g); auto with ord.
      + rewrite ord_le_unfold. simpl.
        intros.
        rewrite (vtower_unroll b).
        rewrite <- lub_le2.
        rewrite ord_lt_unfold in H.
        destruct H as [m ?].
        apply ord_le_lt_trans with (vtower (b m) (vtower b x a)).
        apply vtower_monotone; auto with ord.
        apply ord_lt_le_trans with
            (vtower (b m)
            (supOrd
               (fun a1 : b =>
                  nextCritical (vtower (sz a1)) (1 + x) (limOrd (fun x0 : x => vtower b (x x0)))))).
        apply normal_increasing; auto.
        apply vtower_normal; auto with ord.
        apply ord_lt_le_trans with (vtower b x); auto with ord.
        apply nextCritical_inflate_lemma; auto with ord.
        etransitivity.
        { apply normal_continuous; auto.
          apply vtower_normal; auto with ord.
        }
        apply sup_least; intros i.
        destruct (complete_directed b Hcomplete_b m i) as [k [??]].
        rewrite <- (sup_le _ _ k).
        rewrite <- (nextCritical_critical (vtower (sz k))); auto.
        rewrite veblen_zero.
        transitivity (vtower (sz k)
                             (nextCritical (vtower (sz i)) (1 + x) (limOrd (fun x0 : x => vtower b (x x0))))).
        apply vtower_monotone; auto with ord.
        apply normal_monotone; auto with ord.
        apply nextCritical_mono; auto with ord.
        intros; apply vtower_monotone; auto with ord.
        intros; apply vtower_monotone; auto with ord.
        apply vtower_normal; auto with ord.
        apply zero_complete.
        rewrite <- addOrd_le1.
        apply succ_lt.

      + induction y' as [Y h Hindy].
        intros.

        rewrite veblen_unroll.
        apply lub_least.
        * apply Hinda; auto with ord.
          apply Hca.
          transitivity (ord A g); auto with ord.
        * simpl. apply sup_least. intros.
          apply normal_fix_least; auto.
          apply veblen_normal; auto.
          apply vtower_normal; auto.
          transitivity (ord A g); auto with ord.
          apply Hca.
          apply H0.
          rewrite ord_le_unfold. simpl. intros.
          assert (vtower b x a0 < vtower b x).
          auto with ord.
          rewrite (vtower_unroll b x) in H2 at 2.
          apply lub_lt in H2.
          destruct H2.

          { apply ord_lt_le_trans with (veblen (vtower (sz q)) (ord Y h) (f x)).
            apply veblen_increasing; auto.
            apply vtower_normal; auto.
            transitivity (ord A g); auto with ord.
            apply normal_complete; auto.
            rewrite (vtower_unroll b x).
            rewrite ord_lt_unfold in H.
            destruct H as [i2 ?].
            rewrite <- lub_le2.

            apply veblen_collapse; auto with ord.
            apply vtower_normal; auto.
            transitivity (ord A g); auto with ord.
            rewrite ord_lt_unfold; eauto.
            apply normal_complete; auto.
            eapply ord_lt_le_trans; [ apply H1 | ].

            transitivity (vtower 0 (vtower b x)).
            { rewrite (vtower_unroll 0).
              rewrite <- lub_le1.
              apply onePlus_least_normal; auto.
            }
            transitivity (vtower (g q) (vtower b x)).
            { apply vtower_monotone; auto with ord. }
            rewrite Hinda; auto with ord.
            apply nextCritical_inflate_lemma; auto with ord.
            apply Hca.
            rewrite ord_lt_unfold. exists i2; auto with ord.
            transitivity (ord A g); auto with ord.

            rewrite <- (sup_le _ _ i2).
            rewrite <- (nextCritical_critical (vtower (sz i2)) _ _ 0); auto.
            rewrite veblen_zero.
            rewrite vtower_unroll.
            rewrite <- lub_le1.
            apply normal_monotone; auto.
            rewrite <- nextCritical_above.
            rewrite ord_le_unfold. intros r.
            rewrite ord_lt_unfold; exists r. simpl.
            apply vtower_inflate; auto.
            rewrite <- addOrd_le1.
            apply succ_lt.
            apply vtower_normal; auto with ord.
            rewrite <- addOrd_le1.
            apply succ_lt; auto.

            etransitivity.
            { apply (normal_continuous (fun z => veblen (vtower (sz q)) z 0)); auto.
              apply veblen_first_normal; auto with ord.
              apply vtower_normal.
              transitivity (ord A g); auto with ord.
              rewrite ord_lt_unfold; eauto.
              apply complete_subord; auto.
            }

            apply sup_least; intro i1.
            destruct (complete_directed b Hcomplete_b i1 i2) as [i' [??]].
            rewrite <- (sup_le _ _ i').

            rewrite <- (nextCritical_strongly_critical (sz i') _ _ (sz q)); auto.
            apply veblen_monotone_first; auto with ord.
            intros; apply normal_monotone; auto with ord.
            apply vtower_normal; auto.
            transitivity (ord A g); auto with ord.
            rewrite ord_lt_unfold; eauto.
            apply nextCritical_mono; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            rewrite <- addOrd_le1; auto with ord.
            auto with ord.
            rewrite <- H4.
            apply ord_lt_le_trans with (ord A g); auto with ord.
          }

          apply sup_lt in H2.
          destruct H2 as [i1 ?].
          apply ord_lt_le_trans with
            (veblen (vtower (sz q)) (ord Y h)
                    (nextCritical (vtower (sz i1)) (1 + x) (limOrd (fun x0 : x => vtower b (x x0))))).
          apply veblen_increasing; auto.
          apply vtower_normal; auto.
          transitivity (ord A g); auto with ord.
          { rewrite ord_lt_unfold in H.
            destruct H as [i2 ?].
            destruct (complete_directed b Hcomplete_b i1 i2) as [i' [??]].
            rewrite (vtower_unroll b x).
            rewrite <- lub_le2.
            
            apply veblen_collapse; auto with ord.
            apply vtower_normal.
            transitivity (ord A g); auto with ord.
            rewrite ord_lt_unfold. exists i2; auto.
            apply complete_subord; auto.
            eapply ord_lt_le_trans; [ apply H1 |].
            
            transitivity
              (vtower i' (
               supOrd
               (fun a1 : b =>
                  nextCritical (vtower (sz a1)) (1 + x) (limOrd (fun x1 : x => vtower b (x x1)))))).
            rewrite (vtower_unroll (sz i')).
            rewrite <- lub_le1.
            transitivity (f (vtower b x)).
            { apply onePlus_least_normal; auto. }
            apply normal_monotone; auto.
            apply nextCritical_inflate_lemma; auto with ord.
            { etransitivity.
              apply normal_continuous; auto.
              apply vtower_normal; auto with ord.
              apply sup_least; intro i3.
              destruct (complete_directed b Hcomplete_b i' i3) as [i'' [??]].
              rewrite <- (sup_le _ _ i'').
              rewrite <- (nextCritical_critical (vtower (sz i'')) _ _ 0); auto.
              rewrite veblen_zero.
              transitivity (vtower (sz i'')
                                   (nextCritical (vtower (sz i3)) (1 + x) (limOrd (fun x1 : x => vtower b (x x1))))).
              apply vtower_monotone; auto with ord.
              apply normal_monotone; auto with ord.
              apply nextCritical_mono; auto with ord.
              intros; apply vtower_monotone; auto with ord.
              intros; apply vtower_monotone; auto with ord.
              apply vtower_normal; auto with ord.
              rewrite <- addOrd_le1.
              apply succ_lt; auto.
            }

            rewrite <- (sup_le _ _ i').
            apply nextCritical_mono; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            intros; apply vtower_monotone; auto with ord.

            etransitivity.
            { apply (normal_continuous (fun z => veblen (vtower (sz q)) z 0)); auto.
              apply veblen_first_normal; auto with ord.
              apply vtower_normal.
              transitivity (ord A g); auto with ord.
              rewrite ord_lt_unfold; eauto.
              apply complete_subord; auto.
            }

            apply sup_least; intro i3.
            destruct (complete_directed b Hcomplete_b i2 i3) as [i'' [??]].
            rewrite <- (sup_le _ _ i'').

            rewrite <- (nextCritical_strongly_critical (sz i'') _ _ (sz q)); auto.
            apply veblen_monotone_first; auto with ord.
            intros; apply normal_monotone; auto with ord.
            apply vtower_normal; auto.
            transitivity (ord A g) ; auto with ord.
            rewrite ord_lt_unfold; eauto.
            apply nextCritical_mono; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            rewrite <- addOrd_le1.
            apply succ_lt; auto.
            auto with ord.
            rewrite <- H5.
            apply ord_lt_le_trans with (ord A g); auto with ord. }

          apply Hindy; auto with ord.
          apply H0.
          transitivity (ord Y h); auto with ord.
    Qed.

    Lemma vtower_continuous : scott_continuous (vtower b).
    Proof.
      hnf; simpl; intros.
      rewrite vtower_unroll.
      apply lub_least.
      - etransitivity; [ apply normal_continuous | ]; auto.
        apply sup_least; intro i.
        rewrite <- (sup_le _ _ i).
        rewrite vtower_unroll.
        apply lub_le1.
      - apply sup_least; simpl; intros.
        apply nextCritical_least; auto.
        + apply vtower_normal; auto with ord.
        + rewrite addOrd_unfold.
          rewrite lub_unfold.
          rewrite sup_unfold. simpl.
          intuition.
          * hnf; intros.
            destruct a1; destruct a2; simpl in *.
            ** exists (inl _ tt); split; auto with ord.
            ** exists (inr _ s).
               split; auto with ord.
            ** exists (inr _ s).
               split; auto with ord.
            ** destruct s as [q1 []].
               destruct s0 as [q2 []]. simpl.
               revert q1 q2.
               rewrite sup_unfold. simpl.
               intros [a1 r1]. intros [a2 r2]. simpl.
               destruct (H a1 a2) as [a' [??]].
               destruct (ord_le_subord _ _ H1 r1) as [r1' ?].
               destruct (ord_le_subord _ _ H2 r2) as [r2' ?].
               destruct (complete_directed (f0 a') (H0 a') r1' r2') as [r' [??]].
               exists (inr _ (existT _ (existT _ a' r') tt)). simpl.
               split.
               apply addOrd_monotone; auto with ord.
               rewrite H3; auto.
               apply addOrd_monotone; auto with ord.
               rewrite H4; auto.

          * left. exact (inhabits (inl _ tt)).
          * destruct b0. simpl.
            apply addOrd_complete; auto.
            revert x. rewrite sup_unfold.
            simpl. intros [q r]. simpl.
            apply complete_subord.
            apply H0.

        + apply sup_complete; auto.
          hnf; intros.
          destruct (H a1 a2) as [a' [??]].
          exists a'; split; apply vtower_monotone; auto with ord.
          left. exists a0.
          rewrite vtower_unroll.
          rewrite <- lub_le1.
          apply normal_nonzero; auto.
        
        + apply limit_least. rewrite sup_unfold.
          simpl. intros [i j]. simpl.
          rewrite <- (sup_le _ _ i).
          apply vtower_inc; auto with ord.

        + intros.
          transitivity (supOrd (fun i => veblen (vtower (sz a)) y' (vtower b (f0 i)))).
          apply normal_continuous; auto with ord.
          apply veblen_normal; auto with ord.
          { hnf; intros.
            destruct (H a1 a2) as [a' [??]].
            exists a'; split; apply vtower_monotone; auto with ord. }

          apply sup_least; intro i.
          rewrite addOrd_unfold in H2.
          apply lub_lt in H2.
          destruct H2.
          * assert (y' ≈ 0).
            { split; auto with ord.
              rewrite ord_lt_unfold in H2. destruct H2; auto. }
            rewrite <- (sup_le _ _ i).
            transitivity (veblen (vtower (sz a)) 0 (vtower b (f0 i))).
            apply veblen_monotone_first; auto.
            intros; apply normal_monotone; auto with ord.
            apply H3.
            rewrite veblen_zero.
            apply vtower_fixpoint'; auto with ord.

          * apply sup_lt in H2.
            rewrite sup_unfold in H2. simpl in H2.
            destruct H2 as [[j q]?]. simpl in H2.
            assert (y' < 1 + f0 j).
            { eapply ord_lt_le_trans; [ apply H2 | ].
              apply succ_least.
              apply addOrd_increasing. auto with ord. }
            destruct (H i j) as [k [??]].
            rewrite <- (sup_le _ _ k).

            transitivity (veblen (vtower (sz a)) y' (vtower b (f0 k))).
            { apply veblen_monotone; auto with ord.
              intros. apply normal_monotone; auto.
              apply vtower_normal; auto with ord.
              apply vtower_monotone; auto with ord.
            }

            rewrite addOrd_unfold in H3.
            apply lub_lt in H3.
            destruct H3.
            { transitivity (veblen (vtower (sz a)) 0 (vtower b (f0 k))).
              apply veblen_monotone_first; auto with ord.
              intros. apply normal_monotone; auto.
              apply vtower_normal; auto with ord.
              rewrite ord_lt_unfold in H3.
              destruct H3; auto.
              rewrite veblen_zero.
              apply vtower_fixpoint'; auto with ord.
            }
            apply sup_lt in H3. destruct H3 as [r ?].
            rewrite ord_lt_unfold in H3.
            destruct H3; simpl in *.

            transitivity (veblen (vtower (sz a)) y' (supOrd
                                                     (fun a1 : b =>
                                                        nextCritical (vtower (sz a1)) (1 + f0 k)
                                                              (limOrd (fun x : f0 k => vtower b (f0 k x)))))).
            apply veblen_monotone; auto.
            intros; apply normal_monotone; auto.
            apply vtower_normal; auto with ord.
            rewrite nextCritical_inflate_lemma; auto with ord.

            etransitivity; [ apply normal_continuous | ]; auto.
            apply veblen_normal; auto.
            apply vtower_normal; auto with ord.
            apply sup_least; intro a2.

            destruct (complete_directed b Hcomplete_b a a2) as [a'[??]].
            rewrite (vtower_unroll b (f0 k)).
            rewrite <- lub_le2.
            rewrite <- (sup_le _ _ a').
            rewrite <- (nextCritical_critical (vtower (sz a')) (1 + f0 k) _ y'); auto.
            transitivity
              (veblen (vtower (sz a')) y'
                      (nextCritical (vtower (sz a2)) (1 + f0 k)
                             (limOrd (fun x : f0 k => vtower b (f0 k x))))).
            apply veblen_monotone_func; auto.
            apply vtower_normal; auto with ord.
            apply vtower_normal; auto with ord.
            intros.
            apply vtower_monotone; auto with ord.
            apply veblen_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.

            apply nextCritical_mono; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            intros; apply vtower_monotone; auto with ord.
            apply vtower_normal; auto with ord.
            rewrite <- H5.
            rewrite H3.
            apply addOrd_increasing; auto with ord.
    Qed.

  End vtower_normal.

  Theorem vtower_normal :
    forall b, complete b -> normal_function (vtower b).
  Proof.
    induction b using ordinal_induction.
    constructor.
    - intros; apply vtower_monotone; auto with ord.
    - intros; apply vtower_inc; auto.
    - apply vtower_continuous; auto.
    - intros; apply vtower_complete; auto.
    - intros. rewrite vtower_unroll.
      rewrite <- lub_le1.
      apply normal_nonzero; auto.
  Qed.

  Hint Resolve
       zero_complete succ_complete
       vtower_normal vtower_monotone vtower_complete
       vtower_complete
       vtower_complete_lemma1 vtower_complete_lemma2
       vtower_complete_lemma3
       vtower_nextCritical_directed : core.

  Theorem vtower_fixpoint : forall a b x,
      complete a ->
      complete b ->
      complete x ->
      a < b -> vtower a (vtower b x) ≈ vtower b x.
  Proof.
    intros; split.
    - apply vtower_fixpoint'; auto.
    - apply normal_inflationary; auto.
  Qed.

  Theorem vtower_first_normal : normal_function (fun a => vtower a 0).
  Proof.
    constructor.
    - intros; apply vtower_monotone; auto with ord.
    - intros.
      rewrite (vtower_unroll y 0).
      rewrite <- lub_le2.
      rewrite ord_lt_unfold in H0.
      destruct H0 as [y0 ?].
      rewrite <- (sup_le _ _ y0).
      rewrite <- nextCritical_critical; auto.
      rewrite veblen_zero.
      apply ord_le_lt_trans with (vtower y0 0).
      apply vtower_monotone; auto with ord.
      apply normal_increasing; auto.
      rewrite <- nextCritical_critical; auto.
      rewrite veblen_zero; auto.
      apply normal_nonzero; auto.
      apply zero_complete.
      rewrite <- addOrd_le1; auto with ord.
      apply zero_complete.
      rewrite <- addOrd_le1; auto with ord.
    - hnf; intros.
      rewrite vtower_unroll.
      apply lub_least.
      + rewrite <- (sup_le _ _ a0).
        rewrite vtower_unroll.
        apply lub_le1.
      + apply sup_least. rewrite sup_unfold. simpl; intros.
        destruct a as [a q]. simpl.
        rewrite <- (sup_le _ _ a).
        rewrite (vtower_unroll (f0 a) 0).
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ q).
        unfold sz.
        apply nextCritical_least; auto.
        * rewrite ord_le_unfold. intros [].
        * intros. apply nextCritical_critical; auto.
    - intros; auto.
    - intro.
      rewrite vtower_unroll.
      rewrite <- lub_le1.
      apply normal_nonzero. auto.
  Qed.

  Theorem vtower_zero :
    forall x, vtower 0 x ≈ f x.
  Proof.
    intros. rewrite vtower_unroll.
    split.
    - apply lub_least; auto with ord.
      apply sup_least; intros [].
    - apply lub_le1.
  Qed.

  Theorem vtower_succ :
    forall a x, 
      complete a ->
      complete x ->
      vtower (succOrd a) x ≈ veblen (vtower a) (1+x) 0.
  Proof.
    induction a as [a Hinda] using ordinal_induction.
    induction x using ordinal_induction.
    rewrite vtower_unroll.
    split.
    - apply lub_least.
      rewrite <- veblen_fixpoints; auto.
      rewrite veblen_zero.
      rewrite vtower_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      transitivity (1+x).
      apply addOrd_le2.
      apply (normal_inflationary (fun i => veblen (vtower a) i 0)); auto.
      apply veblen_first_normal; auto.
      apply zero_complete.
      rewrite <- addOrd_le1. auto with ord.
      simpl. apply sup_least; intros [].

      apply nextCritical_least; auto.
      + apply veblen_complete; auto.
      + rewrite ord_le_unfold. simpl; intro i.
        rewrite (H (x i)); auto with ord.
        apply (normal_increasing (fun q => veblen (vtower a) q 0)); auto.
        apply veblen_first_normal; auto.
        apply addOrd_increasing; auto with ord.
      + intros. apply veblen_fixpoints; auto.

    - rewrite <- lub_le2.
      rewrite <- (sup_le _ _ tt).
      simpl.

      destruct (complete_zeroDec x H1).
      + transitivity (veblen (vtower a) 1 0).
        apply veblen_monotone_first; auto with ord.
        rewrite H2. rewrite addOrd_zero_r. auto with ord.
        rewrite veblen_succ; auto.
        rewrite enum_fixpoints_zero; auto with ord.

        apply normal_fix_least; auto with ord.
        apply veblen_normal; auto.
        { apply nextCritical_complete; auto. }
        rewrite veblen_zero.
        apply nextCritical_fix; auto.
        rewrite <- addOrd_le1.
        apply succ_lt.
        apply veblen_normal; auto.

      + transitivity (veblen (vtower a) (supOrd (fun i : x => succOrd (1 + x i))) 0).
        { apply veblen_monotone_first; auto.
          intros; apply vtower_monotone; auto with ord.
          rewrite addOrd_unfold.
          apply lub_least; auto with ord.
          rewrite ord_lt_unfold in H2.
          destruct H2 as [q ?].
          rewrite <- (sup_le _ _ q).
          apply succ_least; apply succ_trans.
          auto with ord. }
        transitivity (supOrd (fun i:x => veblen (vtower a) (succOrd (1 + x i)) 0)).
        { rewrite ord_lt_unfold in H2.
          destruct H2 as [q ?].
          apply (normal_continuous (fun z => veblen (vtower a) z 0)); auto.
          apply veblen_first_normal; auto.
          apply directed_monotone; auto with ord.
          intros. apply succ_monotone.
          apply addOrd_monotone; auto with ord. }

        apply sup_least; intro i.
        rewrite veblen_succ; auto.
        rewrite enum_fixpoints_zero; auto.

        apply normal_fix_least; auto with ord.
        apply veblen_normal; auto.
        { apply nextCritical_complete; auto. }
        apply nextCritical_critical; auto.
        apply addOrd_increasing; auto with ord.
        apply veblen_normal; auto.
  Qed.

  Theorem vtower_limit :
    forall b x,
      complete b ->
      complete x ->
      limitOrdinal b ->
      vtower b x ≈ boundedSup b (fun a => vtower a (limOrd (fun i => vtower b (x i)))).
  Proof.
    intros b x Hcb Hcx H.
    rewrite vtower_unroll.
    split.
    apply lub_least.
    - destruct b as [B g].
      destruct H as [[b0] H].
      simpl.
      rewrite <- (sup_le _ _ b0).
      rewrite vtower_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      rewrite ord_le_unfold; intro j.
      rewrite ord_lt_unfold; exists j.
      apply normal_inflationary; auto.

    - destruct b as [B g].
      destruct H as [[b0] H].
      simpl. apply sup_least; intro i.
      destruct (H i) as [i' Hb'].
      destruct (H i') as [i'' Hb''].

      rewrite <- (sup_le _ _ i'').

      apply nextCritical_least; auto.
      + apply vtower_normal; auto with ord.
        apply Hcb.
      + apply vtower_complete; auto.
        apply Hcb.
      + apply normal_inflationary; auto.
        apply vtower_normal; auto with ord.
        apply Hcb.
      + intros.
        apply veblen_collapse; auto with ord.
        * apply vtower_normal; auto with ord.
          apply Hcb.
        * apply vtower_complete; auto with ord.
          apply Hcb.
        * apply vtower_complete; auto with ord.
          apply Hcb.
        * eapply ord_lt_le_trans; [ apply H1 | ].
          rewrite vtower_unroll.
          rewrite <- lub_le1.
          transitivity (f x).
          { apply onePlus_least_normal; auto. }
          apply normal_monotone; auto.
          rewrite ord_le_unfold; intro j.
          rewrite ord_lt_unfold; exists j.
          simpl. apply normal_inflationary; auto.
        * transitivity (vtower (succOrd (g i))
                             (vtower (g i'') (limOrd (fun i0 : x => vtower (ord B g) (x i0))))).
          { rewrite vtower_succ.
            apply veblen_monotone_first; auto.
            intros. apply vtower_monotone; auto with ord.
            apply addOrd_le2.
            apply Hcb.
            apply vtower_complete; auto.
            apply Hcb. }
          apply vtower_fixpoint.
          apply succ_complete. apply Hcb.
          apply Hcb.
          { apply lim_complete; auto.
            apply directed_monotone; auto with ord.
            destruct x; apply Hcx. }
          apply ord_le_lt_trans with (g i'); auto.
          apply succ_least; auto.

    - destruct b as [B g]. simpl.
      apply sup_least; intro i.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ i).
      rewrite <- nextCritical_fix; auto.
      apply vtower_monotone; auto with ord.
      apply nextCritical_above.
      rewrite <- addOrd_le1.
      apply succ_lt; auto.
      apply vtower_normal; auto.
      apply Hcb.
      rewrite <- addOrd_le1.
      apply succ_lt; auto.
  Qed.
End vtower_def.


Local Hint Resolve
      vtower_normal
      vtower_monotone
      vtower_complete
      veblen_complete
      veblen_normal
      veblen_complete
      veblen_first_normal
      veblen_first_onePlus_normal
      normal_monotone
      onePlus_normal
      powOmega_normal
      addOrd_complete
      addOrd_increasing
      succ_complete
      zero_complete
      natOrdSize_complete
      zero_lt_onePlus
  : core.


Lemma veblen_vtower_zero : forall a x,
    complete a ->
    complete x ->
    veblen (vtower (addOrd 1) 0) a x ≈ expOrd ω a + x.
Proof.
  intros.
  transitivity (veblen (addOrd 1) a x).
  split; apply veblen_monotone_func; auto.
  intros. rewrite vtower_zero. auto with ord.
  intros. rewrite vtower_zero. auto with ord.
  rewrite veblen_onePlus; auto.
  reflexivity.
Qed.


Lemma veblen_vtower_strongly_critical : forall f n m b c,
    normal_function f ->
    complete n ->
    complete m ->
    complete b ->
    complete c ->
    m < n ->
    (limitOrdinal n \/ 0 < b) ->
    veblen (vtower f m) (veblen (vtower f n) b c) 0 <= veblen (vtower f n) b c.
Proof.
  intros f n m b c Hf Hcn Hcm Hcb Hcc Hmn H.
  destruct (complete_zeroDec b Hcb).
  - destruct H; [ | elim (ord_lt_irreflexive 0); apply ord_lt_le_trans with b; auto ].
    assert (Hb : b ≈ 0).
    { split; auto with ord. }
    transitivity (veblen (vtower f m) (vtower f n c) 0).
    { apply veblen_monotone_first; auto with ord.
      transitivity (veblen (vtower f n) 0 c).
      { apply veblen_monotone_first; auto with ord. }
      apply veblen_zero. }
    etransitivity.
    { apply veblen_monotone_first. auto with ord.
      apply vtower_limit; auto. }
    transitivity (vtower f n c).
    2: { rewrite <- veblen_zero. apply veblen_monotone_first; auto with ord. }
    rewrite vtower_limit; auto.
    destruct n as [N h]. simpl.
    destruct H as [[n0] Hl].
    etransitivity.
    { apply (normal_continuous (fun q => veblen (vtower f m) q 0)); auto.
      hnf; intros.
      destruct (complete_directed (ord N h) Hcn a1 a2) as [a' [??]].
      exists a'. split; apply vtower_monotone; auto with ord.
      intros. apply vtower_complete; auto.
      apply Hcn.
      apply lim_complete; auto.
      apply directed_monotone; auto.
      destruct c; apply Hcc. }

    apply sup_least; intro i.
    rewrite ord_lt_unfold in Hmn.
    destruct Hmn as [j Hj].
    destruct (complete_directed (ord N h) Hcn i j) as [k [??]].
    destruct (Hl k) as [k' Hk'].
    destruct (Hl k') as [k'' Hk''].
    rewrite <- (sup_le _ _ k'').
    transitivity (vtower f (succOrd (h k')) (limOrd (fun i0 : c => vtower f (ord N h) (c i0)))).
    rewrite vtower_succ; auto.
    transitivity (
        vtower f (succOrd (h k))
               (veblen (vtower f (h k'))
                       (1 + limOrd (fun i0 : c => vtower f (ord N h) (c i0))) 0)).
    rewrite vtower_succ.
    transitivity (veblen (vtower f (h k))
                         (vtower f (h i) (limOrd (fun i0 : c => vtower f (ord N h) (c i0)))) 0).
    { apply veblen_mono_func; auto with ord.
      intros; apply vtower_monotone; auto with ord.
      rewrite Hj; auto. }
    apply veblen_monotone_first; auto with ord.
    rewrite onePlus_veblen; auto.
    transitivity 
      (veblen (vtower f (h k')) 0 
              (veblen (vtower f (h k'))
              (1 + limOrd (fun i0 : c => vtower f (ord N h) (c i0))) 0)).
    rewrite veblen_zero.
    apply vtower_monotone; auto with ord.
    rewrite H; auto with ord.
    transitivity (1 + limOrd (fun i0 : c => vtower f (ord N h) (c i0))).
    apply addOrd_le2.
    apply (normal_inflationary (fun q => veblen (vtower f ((h k'))) q 0)); auto with ord.
    apply veblen_first_normal; auto with ord.
    apply vtower_normal; auto.
    apply Hcn.
    apply addOrd_complete; auto.
    { apply lim_complete; auto.
      apply directed_monotone; auto.
      destruct c; apply Hcc. }
    apply veblen_fixpoints; auto with ord.
    apply vtower_normal; auto.
    apply Hcn.
    apply addOrd_complete; auto.
    { apply lim_complete; auto.
      apply directed_monotone; auto.
      destruct c; apply Hcc. }
    apply vtower_normal; auto.
    apply Hcn.
    apply addOrd_complete; auto.
    { apply lim_complete; auto.
      apply directed_monotone; auto.
      destruct c; apply Hcc. }
    auto.
    apply Hcn.
    apply veblen_complete; auto.
    apply vtower_normal; auto.
    apply Hcn.
    apply normal_complete; auto.
    apply vtower_normal; auto.
    apply Hcn.
    apply addOrd_complete; auto.
    { apply lim_complete; auto.
      apply directed_monotone; auto.
      destruct c; apply Hcc. }
    
    transitivity 
      (veblen (vtower f (h k')) 0
      (veblen (vtower f (h k'))
              (1 + limOrd (fun i0 : c => vtower f (ord N h) (c i0))) 0)).
    rewrite veblen_zero.
    apply vtower_monotone; auto with ord.
    apply succ_least; auto.
    apply veblen_fixpoints; auto.
    apply vtower_normal; auto.
    apply Hcn.
    apply addOrd_complete; auto.
    { apply lim_complete; auto.
      apply directed_monotone; auto.
      destruct c; apply Hcc. }
    apply Hcn.
    { apply lim_complete; auto.
      apply directed_monotone; auto.
      destruct c; apply Hcc. }
    apply vtower_monotone; auto with ord.
    apply succ_least; auto.
  - transitivity
      (veblen (vtower f n) 0 (veblen (vtower f n) b c)).
    rewrite veblen_zero.
    transitivity (vtower f (succOrd m) (veblen (vtower f n) b c)).
    rewrite vtower_succ; auto.
    apply veblen_monotone_first; auto.
    apply onePlus_veblen; auto with ord.
    apply vtower_monotone; auto with ord.
    apply succ_least; auto.
    apply veblen_fixpoints; auto.
Qed.

Theorem veblen_vtower_collapse : forall f n m a b c,
  normal_function f ->
  complete n ->
  complete m ->
  complete a ->
  complete b ->
  complete c ->
  (m < n) ->
  (limitOrdinal n \/ 0 < b) ->
  a < veblen (vtower f n) b c ->
  veblen (vtower f m) a (veblen (vtower f n) b c) <= veblen (vtower f n) b c.
Proof.
  intros f n m a b c Hf Hcn Hcm Hca Hcb Hcc Hmn H Ha.
  apply veblen_collapse; auto with ord.
  apply veblen_vtower_strongly_critical; auto.
Qed.


Lemma veblen_limit :
  forall f,
    normal_function f ->
    (forall x, complete x -> limitOrdinal (f x)) ->
    (forall a x, complete a -> complete x -> limitOrdinal (veblen f a x)).
Proof.
  intros f Hf Hl.
  induction a as [A g Hinda].
  set (a:=ord A g).
  intros x Hca Hcx.
  apply limitOrdinal_intro.
  { apply veblen_nonzero; auto. }
  intros i Hi.
  rewrite veblen_unroll in Hi.
  apply lub_lt in Hi.
  destruct Hi as [Hi|Hi].
  + assert ( Hl' : limitOrdinal (f x)) by auto.
    rewrite ord_isLimit in Hl'.
    destruct Hl' as [Hl1 Hl2].
    destruct (Hl2 i) as [j [??]]; auto.
    exists j. split; auto.
    rewrite veblen_unroll. rewrite <- lub_le1. auto.
  + apply sup_lt in Hi.
    destruct Hi as [ai Hi].
    rewrite normal_fixpoint in Hi; auto.
    assert (Hl' : limitOrdinal (
                     veblen f (g ai)
                         (fixOrd (veblen f (g ai))
                                 (limOrd (fun x0 : x => veblen f (ord A g) (x x0)))))).
    { apply Hinda; auto with ord.
      apply Hca.
      apply normal_fix_complete; auto.
      - apply lim_complete; auto.
        intro. apply veblen_complete; auto.
        apply normal_complete; auto.
        apply directed_monotone; auto.
        destruct x; apply Hcx.
      - intros. apply normal_inflationary; auto.
        apply veblen_normal; auto.
        apply Hca.
      - intros; apply veblen_monotone; auto.
      - intros. apply veblen_complete; auto.
        apply normal_complete; auto.
        apply Hca. }
    rewrite ord_isLimit in Hl'.
    destruct Hl' as [Hl1 Hl2].
    destruct (Hl2 i) as [j [??]]; auto.
    exists j; split; auto.
    rewrite veblen_unroll.
    rewrite <- lub_le2.
    simpl.
    rewrite <- (sup_le _ _ ai).
    rewrite normal_fixpoint; auto.
    apply veblen_normal; auto.
    apply Hca.
    { apply lim_complete; auto.
      intro; apply veblen_complete; auto.
      apply normal_complete; auto.
      apply directed_monotone; auto.
      destruct x; apply Hcx. }
    apply veblen_normal; auto.
    apply Hca.
    { apply lim_complete; auto.
      intro; apply veblen_complete; auto.
      apply normal_complete; auto.
      apply directed_monotone; auto.
      destruct x; apply Hcx. }
Qed.

Lemma vtower_one_limit :
  forall x, complete x -> limitOrdinal (vtower (addOrd 1) 1 x).
Proof.
  intros.
  rewrite vtower_succ; auto.
  rewrite veblen_vtower_zero; auto.
  rewrite addOrd_zero_r.
  apply additively_closed_limit.
  + apply ord_lt_le_trans with (expOrd ω 1).
    rewrite expOrd_one'.
    apply omega_gt1.
    apply omega_gt0.
    apply expOrd_monotone.
    apply addOrd_le1.
  + apply expOmega_additively_closed; auto.
Qed.

Lemma vtower_gt_one_limit :
  forall n x,
    complete n ->
    complete x ->
    n > 1 ->
    limitOrdinal (vtower (addOrd 1) n x).
Proof.
  intros.
  rewrite <- (vtower_fixpoint _ onePlus_normal 1); auto.
  apply vtower_one_limit; auto.
Qed.

Lemma vtower_onePlus_limit :
  forall n x,
    complete n ->
    complete x ->
    limitOrdinal (vtower (addOrd 1) (1+n) x).
Proof.
  intros.
  destruct (complete_zeroDec n); auto.
  - assert (vtower (addOrd 1) (1+n) x ≈ vtower (addOrd 1) 1 x).
    { apply vtower_eq_mor; auto with ord.
      split. rewrite H1. rewrite addOrd_zero_r. reflexivity.
      apply addOrd_le1. }
    rewrite H2.
    apply vtower_one_limit; auto.
  - apply vtower_gt_one_limit; auto.
    apply ord_lt_le_trans with (1 + 1).
    rewrite addOrd_succ.
    apply succ_trans. apply addOrd_le1.
    apply addOrd_monotone; auto with ord.
    apply succ_least; auto.
Qed.

Definition LargeVeblenOrdinal := fixOrd (fun x => vtower (addOrd 1) x 0) 0.

Lemma vtower_fin_eq : forall (i:ω) x,
    complete x ->
    vtower_fin i x ≈ vtower (addOrd 1) i x.
Proof.
  induction i; simpl; intros.
  - rewrite vtower_zero. reflexivity.
  - rewrite vtower_succ.
    split; apply veblen_monotone_func; auto.
    apply vtower_fin_normal.
    intros; apply IHi; auto.
    apply vtower_fin_normal.
    intros; apply IHi; auto.
    apply onePlus_normal.
    apply natOrdSize_complete.
    auto.
Qed.

Lemma SVO_vtower : SmallVeblenOrdinal ≈ vtower (addOrd 1) ω 0.
Proof.
  transitivity (supOrd (fun i:ω => vtower (addOrd 1) i 0)).
  + unfold SmallVeblenOrdinal.
    apply sup_ord_eq_morphism. intro i.
    apply vtower_fin_eq; auto.
  + split.
    apply sup_least; intro.
    apply vtower_monotone; auto with ord.
    transitivity (vtower (addOrd 1) (supOrd natOrdSize) 0).
    apply vtower_monotone; auto with ord.
    rewrite ord_le_unfold; intro i.
    rewrite <- (sup_le _ _ (S i)).
    simpl.
    apply succ_lt.
    apply (normal_continuous (fun i => vtower (addOrd 1) i 0)); auto.
    apply vtower_first_normal; auto.
    exact O.
    hnf; intros.
    apply (complete_directed ω) ; apply omega_complete.
Qed.

End vtower.



