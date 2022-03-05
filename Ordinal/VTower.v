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
    veblen f y' (nextCritical f y x) <= nextCritical f y x.
Proof.
  intros f y x y' Hf Hcy' Hcy Hcx.
  intros. unfold nextCritical at 1.
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

Lemma vtower_nonzero_limit :
  forall n,
    n > 0 ->
    (forall a x, limitOrdinal (veblen (vtower (addOrd 1) n) a x)) /\
    (forall x, limitOrdinal (vtower (addOrd 1) n x)).
  Admitted.
(*
  Proof.
    induction n as [n Hindn] using ordinal_induction; intros.
    cut (forall x, limitOrdinal (vtower n x)).
    - intuition.
      revert x. induction a as [a Hinda] using ordinal_induction.
      intros.
      apply limitOrdinal_intro.
      apply veblen_nonzero; auto.
      intros.

      rewrite veblen_unroll in H1.
      apply lub_lt in H1.
      destruct H1.
      assert (limitOrdinal (vtower n x)).
      { apply H0. }
      rewrite ord_isLimit in H2.
      destruct H2.
      destruct (H3 i) as [j [??]]; auto.
      exists j. split; auto.
      rewrite veblen_unroll. rewrite <- lub_le1. auto.

      destruct a as [A f]. simpl in *.
      apply sup_lt in H1.
      destruct H1 as [a ?].
      rewrite normal_fixpoint in H1; auto.
      assert (limitOrdinal (
                  veblen (vtower n) (f a)
                         (fixOrd (veblen (vtower n) (f a))
                                 (limOrd (fun x0 : x => veblen (vtower n) (ord A f) (x x0)))))).
      apply Hinda; auto with ord.
      rewrite ord_isLimit in H2.
      destruct H2.
      destruct (H3 i) as [j [??]]; auto.
      exists j; split; auto.
      rewrite veblen_unroll.
      rewrite <- lub_le2.
      simpl.
      rewrite <- (sup_le _ _ a).
      rewrite normal_fixpoint; auto.
    - induction x as [x Hindx] using ordinal_induction.
      apply limitOrdinal_intro.
      apply ord_lt_le_trans with (vtower 0 x).
      rewrite vtower_zero.
      rewrite <- addOrd_le1.
      apply succ_lt.
      apply vtower_monotone; auto with ord.
      intros.
      rewrite vtower_unfold in H0.
      apply lub_lt in H0.
      destruct H0.
      + apply sup_lt in H0.
        destruct H0 as [Hz ?].
        rewrite ord_isZero in Hz.
        rewrite Hz in H.
        elim (ord_lt_irreflexive 0); auto.
      + apply lub_lt in H0.
        destruct H0.
        * apply sup_lt in H0.
          destruct H0 as [Hs ?].
          apply sup_lt in H0.
          destruct H0 as [a ?].
          destruct (classical.order_total EM (n a) 0).
          assert (veblen (vtower (n a)) (1+x) 0 <= veblen (vtower 0) (1+x) 0).
          apply veblen_monotone_func; auto with ord.
          intros; apply vtower_monotone; auto with ord.
          rewrite H2 in H0.
          rewrite veblen_vtower_zero in H0.
          rewrite addOrd_zero_r in H0.
          assert (limitOrdinal (expOrd ω (1+x))).
          { apply additively_closed_limit.
            apply ord_lt_le_trans with (expOrd ω 1).
            rewrite expOrd_one'; auto with ord.
            apply omega_gt1.
            apply omega_gt0.
            apply expOrd_monotone; auto with ord.
            apply addOrd_le1.
            apply expOmega_additively_closed; auto. }
          rewrite ord_isLimit in H3.
          destruct H3.
          destruct (H4 i) as [j [??]]; auto.
          exists j; split; auto.
          eapply ord_lt_le_trans; [ apply H6 |].
          rewrite vtower_succ'; auto.
          rewrite <- (sup_le _ _ a).
          transitivity (veblen (vtower 0) (1+x) 0).
          rewrite veblen_vtower_zero.
          rewrite addOrd_zero_r; auto with ord.
          apply veblen_monotone_func; auto with ord.
          intros.
          apply vtower_monotone; auto with ord.

          assert (limitOrdinal (veblen (vtower (n a)) (1+x) 0)).
          apply Hindn; auto with ord.
          rewrite ord_isLimit in H2.
          destruct H2.
          destruct (H3 i) as [j [??]]; auto.
          exists j; split; auto.
          eapply ord_lt_le_trans; [ apply H5 |].
          rewrite vtower_succ'; auto.
          rewrite <- (sup_le _ _ a).
          reflexivity.
        * apply sup_lt in H0.
          destruct H0 as [Hl ?].
          apply sup_lt in H0.
          destruct H0 as [a ?].
          generalize Hl; intros Hl'.
          rewrite ord_isLimit in Hl'.
          destruct Hl'.
          destruct (H2 (n a)) as [k [??]]; auto with ord.
          assert (vtower (n a) (limOrd (fun j : x => vtower n (x j))) <=
                  vtower k (limOrd (fun j : x => vtower n (x j)))).
          apply vtower_monotone; auto with ord.
          rewrite H5 in H0.
          assert (limitOrdinal (vtower k (limOrd (fun j : x => vtower n (x j))))).
          apply Hindn; auto with ord.
          apply ord_le_lt_trans with (n a); auto with ord.
          rewrite ord_isLimit in H6.
          destruct H6.
          destruct (H7 i) as [q [??]]; auto.
          exists q. split; auto.
          eapply ord_lt_le_trans; [ apply H9 | ].
          rewrite (vtower_limit n); auto.
          destruct n as [N n]. simpl.
          rewrite ord_lt_unfold in H4.
          destruct H4 as [q' ?].
          rewrite <- (sup_le _ _ q').
          apply vtower_monotone; auto with ord.
  Qed.
*)


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





(*
Fixpoint vtower (b:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match b, y with
    | ord B f, ord Y g =>
      supOrd (fun Hz:~inhabited B => 1 + y) ⊔
      supOrd (fun Hs:hasMaxElement B f =>
                supOrd (fun a:B => veblen (vtower (f a)) (1+ord Y g) 0)) ⊔
      supOrd (fun Hl:inhabited B /\ ascendingSet B f =>
                supOrd (fun a:B => vtower (f a) (limOrd (fun i => inner (g i)))))
    end.

Lemma vtower_unfold b y :
  vtower b y =
  supOrd (fun Hz:zeroOrdinal b => 1+y) ⊔
  supOrd (fun Hs:successorOrdinal b => supOrd (fun i:b => veblen (vtower (b i)) (1+y) 0)) ⊔
  supOrd (fun Hl:limitOrdinal b => supOrd (fun i:b => vtower (b i) (limOrd (fun j => vtower b (y j))))).
Proof.
  destruct b as [B f].
  destruct y as [Y g]. simpl.
  reflexivity.
Qed.

Global Opaque vtower.

Lemma vtower_zero' : forall a x, zeroOrdinal a -> vtower a x ≈ 1+x.
Proof.
  intros; rewrite vtower_unfold.
  split.
  apply lub_least.
  apply sup_least; auto with ord.
  apply lub_least.
  apply sup_least; intro.
  elim (zero_not_successor a); auto.
  apply sup_least; intro.
  elim (zero_not_limit a); auto.
  rewrite <- lub_le1.
  rewrite <- (sup_le _ _ H).
  reflexivity.
Qed.

Lemma vtower_zero : forall x, vtower 0 x ≈ 1+x.
Proof.
  intros.
  apply vtower_zero'.
  rewrite ord_isZero. reflexivity.
Qed.

Lemma vtower_succ' :
  forall a x,
    successorOrdinal a ->
    vtower a x ≈ supOrd (fun i:a => veblen (vtower (a i)) (1+x) 0).
Proof.
  intros. rewrite vtower_unfold.
  split.
  - apply lub_least ; [ | apply lub_least ]; auto.
    + apply sup_least; intros Hz.
      elim (zero_not_successor a); auto.
    + apply sup_least; intros Hs.
      reflexivity.
    + apply sup_least; intros Hl.
      elim (successor_not_limit a); auto.
  - rewrite <- lub_le2.
    rewrite <- lub_le1.
    rewrite <- (sup_le _ _ H).
    reflexivity.
Qed.

Lemma vtower_succ :
  forall a x, vtower (succOrd a) x ≈ veblen (vtower a) (1+x) 0.
Proof.
  intros.
  rewrite vtower_succ'.
  split.
  apply sup_least. simpl. intros. reflexivity.
  simpl.
  rewrite <- (sup_le _ _ tt). reflexivity.
  rewrite ord_isSucc. eauto with ord.
Qed.

Lemma vtower_limit :
  forall b x,
    limitOrdinal b ->
    vtower b x ≈ boundedSup b (fun a => vtower a (limOrd (fun i => vtower b (x i)))).
Proof.
  intros.
  rewrite vtower_unfold.
  split.
  - apply lub_least ; [ | apply lub_least ]; auto.
    + apply sup_least; intros Hz.
      elim (zero_not_limit b); auto.
    + apply sup_least; intros Hs.
      elim (successor_not_limit b); auto.
    + apply sup_least; intro Hl'.
      destruct b; reflexivity.
  - rewrite <- lub_le2.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ H).
    destruct b; reflexivity.
Qed.

Section vtower_normal.
  Variable b:Ord.
  Hypothesis Hind : forall a, a < b -> normal_function (vtower a).
  Hypothesis Hind2 : forall a b' x,
      a <= b' -> b' < b -> vtower a x <= vtower b' x.

  Lemma vtower_mono :
    forall y x b', b' <= b -> x <= y -> vtower b' x <= vtower b' y.
  Proof.
    induction y using ordinal_induction.
    intros.
    rewrite (vtower_unfold b' x).
    rewrite (vtower_unfold b' y).
    apply lub_least ; [ | apply lub_least ].
    - apply sup_least; intro Hz.
      rewrite <- lub_le1.
      rewrite <- (sup_le _ _ Hz).
      apply addOrd_monotone; auto with ord.
    - apply sup_least; intro Hs. apply sup_least; intros i.
      rewrite <- lub_le2. rewrite <- lub_le1.
      rewrite <- (sup_le _ _ Hs).
      rewrite <- (sup_le _ _ i).
      apply veblen_monotone_first; auto.
      intros. apply normal_monotone; auto.
      apply Hind; auto with ord. rewrite <- H0. auto with ord.
      apply addOrd_monotone; auto with ord.
    - apply sup_least; intros Hl.
      apply sup_least; intros i.
      rewrite <- lub_le2.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ Hl).
      rewrite <- (sup_le _ _ i).
      apply normal_monotone; auto.
      apply Hind; auto with ord. rewrite <- H0; auto with ord.
      rewrite ord_le_unfold; simpl; intro j.
      destruct (ord_le_subord x y H1 j) as [k Hk].
      rewrite ord_lt_unfold; simpl; exists k.
      apply H; auto with ord.
  Qed.

  Lemma vtower_inc : forall b' x y, b' <= b -> x < y -> vtower b' x < vtower b' y.
  Proof.
    intros.
    destruct (classical.ordinal_discriminate EM b') as [Hz|[Hs|Hl]].
    - rewrite vtower_zero'; auto.
      rewrite vtower_zero'; auto.
      apply addOrd_increasing; auto.
    - rewrite vtower_succ'; auto.
      rewrite vtower_succ'; auto.
      destruct b' as [B g].
      destruct Hs as [i Hs]. simpl.
      apply ord_le_lt_trans with (veblen (vtower (g i)) (1+x) 0).
      apply sup_least; intro j.
      apply veblen_monotone_func; auto.
      apply Hind. rewrite <- H. auto with ord.
      apply Hind. rewrite <- H. auto with ord.
      intros. apply Hind2; auto with ord. rewrite <- H. auto with ord.
      apply classical.ord_complete; auto.
      apply zero_complete.
      rewrite <- (sup_le _ _ i).
      apply (normal_increasing (fun q => veblen (vtower (g i)) q 0)).
      apply veblen_first_normal; auto.
      apply Hind. rewrite <- H. auto with ord.
      apply classical.ord_complete; auto.
      apply addOrd_increasing; auto.
    - rewrite (vtower_limit b' y); auto.
      destruct b' as [B g]. simpl.
      destruct Hl as [[i] Hl].
      rewrite <- (sup_le _ _ i).
      apply ord_lt_le_trans with (limOrd (fun i0 : y => vtower (ord B g) (y i0))).
      rewrite ord_lt_unfold in  H0.
      destruct H0 as [j H0].
      rewrite ord_lt_unfold.
      exists j; simpl.
      apply vtower_mono; auto with ord.
      apply normal_inflationary; auto with ord.
      apply Hind. rewrite <- H. auto with ord.
      apply classical.ord_complete; auto.
  Qed.

  Lemma vtower_prefixpoint : forall b' a x, b' <= b -> a < b' -> vtower a (vtower b' x) <= vtower b' x.
  Proof.
    induction b' using ordinal_induction.
    intros.
    destruct (classical.ordinal_discriminate EM b') as [Hz|[Hs|Hl]].
    - rewrite ord_isZero in Hz.
      elim (ord_lt_irreflexive b').
      rewrite Hz at 1.
      apply ord_le_lt_trans with a; auto with ord.
    - rewrite (vtower_succ' b') at 2; auto.
      destruct b' as [B g].
      generalize Hs; intros [i Hi].
      rewrite <- (sup_le _ _ i). simpl.
      assert (Hnorm : normal_function (vtower (g i))).
      { apply Hind. apply ord_lt_le_trans with (ord B g); auto with ord. }
      rewrite <- (veblen_fixpoints (vtower (g i)) Hnorm 0 (1+x)); auto.
      rewrite veblen_zero.
      transitivity (vtower (g i) (vtower (ord B g) x)).
      apply Hind2; auto with ord.
      rewrite ord_lt_unfold in H1. destruct H1.
      rewrite H1. apply Hi.
      rewrite <- H0; auto with ord.
      apply normal_monotone; auto.
      rewrite (vtower_succ' (ord B g)); auto.
      apply sup_least. intro j. simpl.
      apply veblen_monotone_func; auto.
      apply Hind; auto with ord.
      rewrite <- H0; auto with ord.
      intros. apply Hind2; auto.
      rewrite <- H0; auto with ord.
      apply classical.ord_complete; auto.
      apply zero_complete.
      apply zero_complete.
      apply classical.ord_complete; auto.
      apply zero_complete.
      rewrite <- addOrd_le1.
      apply succ_lt.
    - etransitivity.
      apply normal_monotone; auto.
      apply Hind. rewrite <- H0; auto.
      apply (vtower_limit b' x); auto.
      rewrite (vtower_limit b' x).
      destruct b' as [B g].
      destruct Hl as [[i] Hl].
      etransitivity. apply normal_continuous; auto.
      apply Hind. rewrite <- H0; auto.
      apply classical.ord_directed; auto.
      intros; apply classical.ord_complete; auto.
      simpl. apply sup_least; intro b1.
      rewrite ord_lt_unfold in H1.
      destruct H1 as [b2 H1].
      destruct (classical.ord_directed EM B g b1 b2) as [b' [??]].
      destruct (Hl b') as [b'' ?].
      rewrite <- (sup_le _ _ b'').
      transitivity (vtower a (vtower (g b'') (limOrd (fun i0 : x => vtower (ord B g) (x i0))))).
      apply normal_monotone; auto.
      apply Hind. rewrite <- H0; auto with ord.
      rewrite ord_lt_unfold. exists b2; auto.
      apply Hind2; auto with ord.
      rewrite H2; auto with ord.
      rewrite <- H0; auto with ord.
      apply H; auto with ord.
      rewrite <- H0; auto with ord.
      rewrite H1. simpl.
      rewrite H3. auto.
      auto.
  Qed.

  Lemma vtower_continuous : scott_continuous (vtower b).
  Proof.
    hnf; intros.
    destruct (classical.ordinal_discriminate EM b) as [Hz|[Hs|Hl]].
    - rewrite vtower_zero'; auto.
      etransitivity. apply addOrd_continuous; auto.
      apply sup_least; intro i.
      rewrite <- (sup_le _ _ i).
      rewrite vtower_zero'; auto.
      reflexivity.
    - rewrite (vtower_succ' b); auto.
      apply sup_least; intro.
      transitivity (veblen (vtower (b a)) (supOrd (fun i => 1 + f i)) 0).
      apply veblen_monotone_first; auto.
      intros; apply normal_monotone; auto with ord.
      apply addOrd_continuous; auto.
      transitivity (supOrd (fun i => (veblen (vtower (b a)) (1 + f i) 0))).
      apply (normal_continuous (fun i => veblen (vtower (b a)) i 0)); auto.
      apply veblen_first_normal; auto.
      apply Hind. auto with ord.
      apply classical.ord_directed; auto.
      intros; apply classical.ord_complete; auto.
      apply sup_ord_le_morphism; intro i; simpl.
      rewrite vtower_succ'; auto.
      rewrite <- (sup_le _ _ a).
      reflexivity.
    - rewrite vtower_limit; auto.
      case_eq b; intros B g Hb. simpl.
      apply sup_least; intro b1.
      transitivity (vtower (g b1) (supOrd (fun i => vtower (ord B g) (f i)))).
      { apply normal_monotone; auto with ord.
        apply Hind. rewrite Hb. auto with ord.
        rewrite (sup_unfold A f). simpl.
        rewrite ord_le_unfold.
        simpl. intros [a q]. simpl.
        rewrite <- (sup_le _ _ a).
        rewrite <- Hb.
        apply vtower_inc; auto with ord. }
      etransitivity. apply normal_continuous; auto with ord.
      apply Hind. rewrite Hb; auto with ord.
      apply classical.ord_directed; auto.
      intros; apply classical.ord_complete; auto.
      apply sup_least; intro x.
      rewrite <- (sup_le _ _ x).
      rewrite <- Hb.
      apply vtower_prefixpoint; auto with ord.
      rewrite Hb. auto with ord.
  Qed.

  Lemma vtower_nonzero : forall x, 0 < vtower b x.
  Proof.
    intros.
    destruct (classical.ordinal_discriminate EM b) as [Hz|[Hs|Hl]].
    - rewrite vtower_zero'; auto.
      rewrite <- addOrd_le1.
      apply succ_lt.
    - rewrite vtower_succ'; auto.
      destruct b as [B g].
      destruct Hs as [i Hi].
      rewrite <- (sup_le _ _ i).
      apply veblen_nonzero.
      simpl. apply Hind. auto with ord.
    - rewrite vtower_limit; auto.
      destruct b as [B g].
      destruct Hl as [[i] Hl].
      simpl.
      rewrite <- (sup_le _ _ i).
      apply normal_nonzero.
      apply Hind; auto with ord.
  Qed.

  Lemma vtower_monotone_first :
    forall x a b', a <= b' -> b' <= b -> vtower a x <= vtower b' x.
  Proof.
    induction x as [x Hindx] using ordinal_induction.
    intros.
    destruct (classical.ordinal_discriminate EM b') as [Hz|[Hs|Hl]].
    - rewrite (vtower_zero' b' x); auto.
      rewrite (vtower_zero' a x); auto with ord.
      rewrite ord_isZero.
      rewrite ord_isZero in Hz.
      split; auto with ord.
      rewrite H. apply Hz.
    - rewrite (vtower_succ' b'); auto.
      destruct b' as [B g].
      destruct Hs as [i Hi].
      rewrite <- (sup_le _ _ i).
      simpl.
      assert (Hgi : normal_function (vtower (g i))).
      { apply Hind. rewrite <- H0; auto with ord. }
      rewrite (vtower_unfold a x).
      apply lub_least; [ | apply lub_least ].
      + apply sup_least; intro.
        apply (normal_inflationary (fun q => veblen (vtower (g i)) q 0)).
        apply veblen_first_normal; auto.
        apply classical.ord_complete; auto.
      + apply sup_least; intros Hs.
        apply sup_least; intro j.
        apply veblen_monotone_func; auto.
        apply Hind. rewrite <- H0. rewrite <- H. auto with ord.
        intros. apply Hind2; auto.
        destruct (ord_le_subord a _ H j) as [k Hk].
        rewrite Hk. apply Hi.
        rewrite <- H0; auto with ord.
        apply classical.ord_complete; auto.
        apply zero_complete.
      + apply sup_least; intros Hl.
        apply sup_least; intros j.
        assert (Ha : a <= g i).
        { rewrite ord_le_unfold; intros q.
          destruct a as [A h]. destruct Hl as [_ Hl].
          simpl.
          destruct (Hl q) as [q' Hq].
          apply ord_lt_le_trans with (h q'); auto.
          destruct (ord_le_subord _ _ H q') as [k ?].
          rewrite H1. apply Hi. }
        rewrite <- (veblen_fixpoints _ Hgi 0); auto.
        rewrite veblen_zero.
        transitivity (vtower (g i) (limOrd (fun j0 : x => vtower a (x j0)))).
        apply Hind2; auto with ord.
        transitivity a; auto with ord.
        rewrite <- H0; auto with ord.
        apply normal_monotone. apply Hind; auto.
        rewrite <- H0. auto with ord.
        rewrite ord_le_unfold; simpl; intro k.
        apply ord_le_lt_trans with (vtower (g i) (x k)).
        apply Hindx; auto with ord.
        rewrite <- H0; auto with ord.
        apply ord_lt_le_trans with (vtower (g i) x).
        apply normal_increasing; auto with ord.
        apply classical.ord_complete; auto.
        rewrite <- (veblen_fixpoints _ Hgi 0); auto.
        rewrite veblen_zero.
        apply normal_monotone; auto.
        transitivity (1+x); auto with ord.
        apply addOrd_le2.
        apply (normal_inflationary (fun q => veblen (vtower (g i)) q 0)).
        apply veblen_first_normal; auto.
        apply classical.ord_complete; auto.
        apply zero_complete.
        apply classical.ord_complete; auto.
        apply zero_complete.
        rewrite <- addOrd_le1. apply succ_lt.
        apply zero_complete.
        apply classical.ord_complete; auto.
        apply zero_complete.
        rewrite <- addOrd_le1. apply succ_lt.
    - rewrite (vtower_limit b' x); auto.
      destruct b' as [B g]. simpl.
      destruct Hl as [[b0] Hl].
      rewrite (vtower_unfold a x).
      apply lub_least; [ | apply lub_least ].
      + apply sup_least; intro.
        rewrite <- (sup_le _ _ b0).
        transitivity (vtower (g b0) x).
        apply onePlus_least_normal.
        apply Hind. rewrite <- H0; auto with ord.
        apply classical.ord_complete; auto.
        apply normal_monotone.
        apply Hind. rewrite <- H0. auto with ord.
        rewrite ord_le_unfold; intro i.
        rewrite ord_lt_unfold. exists i. simpl.
        apply increasing_inflationary.
        intros. apply vtower_inc; auto.
      + apply sup_least; intro Hs.
        apply sup_least; intro i.
        destruct a as [A h].
        destruct Hs as [j Hj].
        destruct (ord_le_subord _ _ H j) as [k Hk].
        simpl in *.
        destruct (Hl k) as [k' Hk'].
        rewrite <- (sup_le _ _ k').
        transitivity (vtower (succOrd (g k)) (limOrd (fun i0 : x => vtower (ord B g) (x i0)))).
        rewrite vtower_succ.
        transitivity (veblen (vtower (g k)) (1+x) 0).
        apply veblen_monotone_func; auto with ord.
        apply Hind. rewrite <- H0.
        rewrite <- H. auto with ord.
        apply Hind. rewrite <- H0. auto with ord.
        intros. apply Hind2; auto with ord.
        rewrite <- Hk. apply Hj.
        rewrite <- H0. auto with ord.
        apply classical.ord_complete; auto.
        apply zero_complete.
        apply veblen_monotone_first; auto.
        intros. apply normal_monotone; auto with ord.
        apply Hind. rewrite <- H0. auto with ord.
        apply addOrd_monotone; auto with ord.
        rewrite ord_le_unfold; intro q.
        rewrite ord_lt_unfold; exists q; simpl.
        apply increasing_inflationary.
        intros. apply vtower_inc; auto.
        apply Hind2.
        apply succ_least. auto.
        rewrite <- H0.
        auto with ord.
      + apply sup_least; intros Hl'.
        apply sup_least; intro i.
        destruct (ord_le_subord _ _ H i) as [j Hj].
        simpl in *.
        rewrite <- (sup_le _ _ j).
        transitivity (vtower (g j) (limOrd (fun j0 : x => vtower a (x j0)))).
        apply Hind2; auto.
        rewrite <- H0. auto with ord.
        apply normal_monotone; auto.
        apply Hind. rewrite <- H0. auto with ord.
        rewrite ord_le_unfold; intro q.
        rewrite ord_lt_unfold; exists q.
        simpl.
        apply Hindx; auto with ord.
  Qed.

End vtower_normal.

Lemma vtower_normal_mono : forall b,
    normal_function (vtower b) /\
    (forall a x, a <= b -> vtower a x <= vtower b x).
Proof.
  induction b using ordinal_induction.
  split. constructor.
  - intros; apply (vtower_mono b); auto with ord.
    intros; apply H; auto.
  - intros; apply (vtower_inc b); auto with ord.
    intros; apply H; auto.
    intros; apply H; auto.
  - intros; apply vtower_continuous.
    intros; apply H; auto.
    intros; apply H; auto.
  - intros. apply classical.ord_complete; auto.
  - intros. apply vtower_nonzero.
    intros; apply H; auto.
    intros; apply H; auto.
  - intros. apply (vtower_monotone_first b); auto with ord.
    intros; apply H; auto.
    intros; apply H; auto.
Qed.

Lemma vtower_normal : forall b, normal_function (vtower b).
Proof.
  apply vtower_normal_mono; auto.
Qed.

Lemma vtower_monotone : forall a b x y, a <= b -> x <= y -> vtower a x <= vtower b y.
Proof.
  intros.
  transitivity (vtower a y).
  apply normal_monotone; auto.
  apply vtower_normal.
  apply vtower_normal_mono; auto.
Qed.

Lemma vtower_fixpoint : forall a b x, a < b -> vtower a (vtower b x) ≈ vtower b x.
Proof.
  intros; split.
  - apply (vtower_prefixpoint b); auto with ord.
    intros; apply vtower_normal; auto.
    intros; apply vtower_monotone; auto with ord.
  - apply normal_inflationary; auto.
    apply vtower_normal.
    apply classical.ord_complete; auto.
Qed.

Add Parametric Morphism : vtower
  with signature ord_le ==> ord_le ==> ord_le as vtower_le_mor.
Proof.
  intros; apply vtower_monotone; auto.
Qed.

Add Parametric Morphism : vtower
  with signature ord_eq ==> ord_eq ==> ord_eq as vtower_eq_mor.
Proof.
  unfold ord_eq; intuition.
  apply vtower_monotone; auto with ord.
  apply vtower_monotone; auto with ord.
Qed.

Lemma vtower_first_normal : normal_function (fun a => vtower a 0).
Proof.
  constructor.
  - intros; apply vtower_monotone; auto with ord.
  - intros.
    destruct (classical.ordinal_discriminate EM y) as [Hz|[Hs|Hl]].
    + rewrite ord_isZero in Hz.
      rewrite Hz in H0.
      elim (ord_lt_irreflexive x).
      apply ord_lt_le_trans with 0; auto with ord.
    + rewrite ord_isSucc in Hs.
      destruct Hs as [o Hs]. rewrite Hs.
      rewrite vtower_succ.
      rewrite <- (veblen_fixpoints (vtower o) (vtower_normal o) 0) ; auto.
      rewrite veblen_zero.
      apply ord_le_lt_trans with (vtower o 0).
      apply vtower_monotone; auto with ord.
      rewrite Hs in H0.
      rewrite ord_lt_unfold in H0. destruct H0; auto.
      apply normal_increasing; auto.
      apply vtower_normal.
      apply classical.ord_complete; auto.
      apply veblen_nonzero.
      apply vtower_normal.
      apply zero_complete.
      apply classical.ord_complete; auto.
      apply zero_complete.
      rewrite addOrd_zero_r.
      apply succ_lt.
    + rewrite (vtower_limit y 0); auto.
      rewrite ord_lt_unfold in H0.
      destruct y as [Y f]. simpl.
      destruct H0 as [y H0]. simpl in H0.
      destruct Hl as [_ Hl].
      destruct (Hl y) as [y' Hy].
      rewrite <- (sup_le _ _ y').
      apply ord_lt_le_trans with (vtower x (vtower (f y')
                                     (limOrd (fun i : False => vtower (ord Y f) (False_rect Ord i))))).
      apply normal_increasing; auto.
      apply vtower_normal.
      apply classical.ord_complete; auto.
      apply normal_nonzero.
      apply vtower_normal.
      apply vtower_fixpoint.
      apply ord_le_lt_trans with (f y); auto.
  - hnf; simpl; intros.
    destruct (classical.max_or_ascending EM A f).
    + destruct H1 as [a Ha].
      transitivity (vtower (f a) 0).
      apply vtower_monotone; auto with ord.
      apply sup_least; intro; auto.
      rewrite <- (sup_le _ _ a).
      reflexivity.
    + rewrite vtower_limit.
      rewrite (sup_unfold A f). simpl.
      apply sup_least; intros [a q]. simpl.
      rewrite <- (sup_le _ _ a).
      apply vtower_monotone; auto with ord.
      rewrite ord_le_unfold; intros [].
      rewrite sup_unfold.
      simpl.
      split.
      * destruct (H1 a0) as [a ?].
        rewrite ord_lt_unfold in H2.
        destruct H2 as [q H2].
        exact (inhabits (existT _ a q)).
      * hnf; simpl; intros [a q]. simpl.
        destruct (H1 a) as [a' Ha].
        rewrite ord_lt_unfold in Ha.
        destruct Ha as [q' Ha].
        exists (existT _ a' q'). simpl.
        apply ord_lt_le_trans with (f a); auto with ord.
  - intros. apply classical.ord_complete; auto.
  - intro.
    apply ord_lt_le_trans with (vtower 0 0).
    rewrite vtower_zero.
    rewrite addOrd_zero_r.
    apply succ_lt.
    apply vtower_monotone; auto with ord.
Qed.

Definition LargeVeblenOrdinal := fixOrd (fun x => vtower x 0) 0.



Local Hint Resolve
      classical.ord_complete
      vtower_normal
      veblen_complete
      veblen_normal
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

Lemma veblen_vtower_zero : forall a x, veblen (vtower 0) a x ≈ expOrd ω a + x.
Proof.
  intros.
  transitivity (veblen (addOrd 1) a x).
  split; apply veblen_monotone_func; auto.
  intros. rewrite vtower_zero. auto with ord.
  intros. rewrite vtower_zero. auto with ord.
  rewrite veblen_onePlus; auto.
  reflexivity.
Qed.

Lemma vtower_nonzero_limit :
  forall n,
    n > 0 ->
    (forall a x, limitOrdinal (veblen (vtower n) a x)) /\
    (forall x, limitOrdinal (vtower n x)).
Proof.
  induction n as [n Hindn] using ordinal_induction; intros.
  cut (forall x, limitOrdinal (vtower n x)).
  - intuition.
    revert x. induction a as [a Hinda] using ordinal_induction.
    intros.
    apply limitOrdinal_intro.
    apply veblen_nonzero; auto.
    intros.

    rewrite veblen_unroll in H1.
    apply lub_lt in H1.
    destruct H1.
    assert (limitOrdinal (vtower n x)).
    { apply H0. }
    rewrite ord_isLimit in H2.
    destruct H2.
    destruct (H3 i) as [j [??]]; auto.
    exists j. split; auto.
    rewrite veblen_unroll. rewrite <- lub_le1. auto.

    destruct a as [A f]. simpl in *.
    apply sup_lt in H1.
    destruct H1 as [a ?].
    rewrite normal_fixpoint in H1; auto.
    assert (limitOrdinal (
              veblen (vtower n) (f a)
              (fixOrd (veblen (vtower n) (f a))
                      (limOrd (fun x0 : x => veblen (vtower n) (ord A f) (x x0)))))).
    apply Hinda; auto with ord.
    rewrite ord_isLimit in H2.
    destruct H2.
    destruct (H3 i) as [j [??]]; auto.
    exists j; split; auto.
    rewrite veblen_unroll.
    rewrite <- lub_le2.
    simpl.
    rewrite <- (sup_le _ _ a).
    rewrite normal_fixpoint; auto.
  - induction x as [x Hindx] using ordinal_induction.
    apply limitOrdinal_intro.
    apply ord_lt_le_trans with (vtower 0 x).
    rewrite vtower_zero.
    rewrite <- addOrd_le1.
    apply succ_lt.
    apply vtower_monotone; auto with ord.
    intros.
    rewrite vtower_unfold in H0.
    apply lub_lt in H0.
    destruct H0.
    + apply sup_lt in H0.
      destruct H0 as [Hz ?].
      rewrite ord_isZero in Hz.
      rewrite Hz in H.
      elim (ord_lt_irreflexive 0); auto.
    + apply lub_lt in H0.
      destruct H0.
      * apply sup_lt in H0.
        destruct H0 as [Hs ?].
        apply sup_lt in H0.
        destruct H0 as [a ?].
        destruct (classical.order_total EM (n a) 0).
        assert (veblen (vtower (n a)) (1+x) 0 <= veblen (vtower 0) (1+x) 0).
        apply veblen_monotone_func; auto with ord.
        intros; apply vtower_monotone; auto with ord.
        rewrite H2 in H0.
        rewrite veblen_vtower_zero in H0.
        rewrite addOrd_zero_r in H0.
        assert (limitOrdinal (expOrd ω (1+x))).
        { apply additively_closed_limit.
          apply ord_lt_le_trans with (expOrd ω 1).
          rewrite expOrd_one'; auto with ord.
          apply omega_gt1.
          apply omega_gt0.
          apply expOrd_monotone; auto with ord.
          apply addOrd_le1.
          apply expOmega_additively_closed; auto. }
        rewrite ord_isLimit in H3.
        destruct H3.
        destruct (H4 i) as [j [??]]; auto.
        exists j; split; auto.
        eapply ord_lt_le_trans; [ apply H6 |].
        rewrite vtower_succ'; auto.
        rewrite <- (sup_le _ _ a).
        transitivity (veblen (vtower 0) (1+x) 0).
        rewrite veblen_vtower_zero.
        rewrite addOrd_zero_r; auto with ord.
        apply veblen_monotone_func; auto with ord.
        intros.
        apply vtower_monotone; auto with ord.

        assert (limitOrdinal (veblen (vtower (n a)) (1+x) 0)).
        apply Hindn; auto with ord.
        rewrite ord_isLimit in H2.
        destruct H2.
        destruct (H3 i) as [j [??]]; auto.
        exists j; split; auto.
        eapply ord_lt_le_trans; [ apply H5 |].
        rewrite vtower_succ'; auto.
        rewrite <- (sup_le _ _ a).
        reflexivity.
      * apply sup_lt in H0.
        destruct H0 as [Hl ?].
        apply sup_lt in H0.
        destruct H0 as [a ?].
        generalize Hl; intros Hl'.
        rewrite ord_isLimit in Hl'.
        destruct Hl'.
        destruct (H2 (n a)) as [k [??]]; auto with ord.
        assert (vtower (n a) (limOrd (fun j : x => vtower n (x j))) <=
                vtower k (limOrd (fun j : x => vtower n (x j)))).
        apply vtower_monotone; auto with ord.
        rewrite H5 in H0.
        assert (limitOrdinal (vtower k (limOrd (fun j : x => vtower n (x j))))).
        apply Hindn; auto with ord.
        apply ord_le_lt_trans with (n a); auto with ord.
        rewrite ord_isLimit in H6.
        destruct H6.
        destruct (H7 i) as [q [??]]; auto.
        exists q. split; auto.
        eapply ord_lt_le_trans; [ apply H9 | ].
        rewrite (vtower_limit n); auto.
        destruct n as [N n]. simpl.
        rewrite ord_lt_unfold in H4.
        destruct H4 as [q' ?].
        rewrite <- (sup_le _ _ q').
        apply vtower_monotone; auto with ord.
Qed.

Lemma vtower_fin_eq : forall (i:ω) x, vtower_fin i x ≈ vtower i x.
Proof.
  induction i; simpl; intros.
  - rewrite vtower_zero. reflexivity.
  - rewrite vtower_succ.
    split; apply veblen_monotone_func; auto.
    apply vtower_fin_normal.
    intros; apply IHi.
    apply vtower_fin_normal.
    intros; apply IHi.
Qed.

Lemma SVO_vtower : SmallVeblenOrdinal ≈ vtower ω 0.
Proof.
  transitivity (supOrd (fun i:ω => vtower i 0)).
  + unfold SmallVeblenOrdinal.
    apply sup_ord_eq_morphism. intro i.
    apply vtower_fin_eq.
  + split.
    apply sup_least; intro.
    apply vtower_monotone; auto with ord.
    transitivity (vtower (supOrd natOrdSize) 0).
    apply vtower_monotone; auto with ord.
    rewrite ord_le_unfold; intro i.
    rewrite <- (sup_le _ _ (S i)).
    simpl.
    apply succ_lt.
    apply (normal_continuous (fun i => vtower i 0)); auto.
    apply vtower_first_normal.
    exact O.
    hnf; intros.
    apply (complete_directed ω) ; apply omega_complete.
Qed.

End vtower.
*)
