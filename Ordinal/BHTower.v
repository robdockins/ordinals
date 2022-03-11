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
From Ordinal Require Import VTower.

Open Scope ord_scope.


Fixpoint bhtower (n:nat) (f:Ord -> Ord) {struct n} : Ord -> Ord -> Ord :=
  let fixpointGadget (n:nat) (g:Ord -> Ord) (y:Ord) (x:Ord) : Ord :=
       match n with
       | O    => fixOrd g x
       | S n' => supOrd (fun z:y => fixOrd (bhtower n' g z) x)
       end in
  fix vtower (b:Ord) : Ord -> Ord :=
    fix inner (y:Ord) : Ord :=
      match b, y with
      | ord B g, ord Y h =>
        f (ord Y h) ⊔
          supOrd (fun a:B => fixpointGadget n
                               (vtower (g a))
                               (1 + ord Y h)
                               (limOrd (fun x:Y => inner (h x))))
      end.

Definition fixpointGadget (n:nat) (g:Ord -> Ord) (y:Ord) (x:Ord) : Ord :=
  match n with
  | O    => fixOrd g x
  | S n' => supOrd (fun z:y => fixOrd (bhtower n' g z) x)
  end.

Lemma bhtower_unroll : forall n f (b y:Ord),
    bhtower n f b y =
    f y ⊔ supOrd (fun a:b => fixpointGadget
                               n (bhtower n f a) (1+y)
                               (limOrd (fun x => bhtower n f b (y x)))).
Proof.
  intros.
  destruct n.
  destruct b as [B g].
  destruct y as [Y h].
  reflexivity.
  destruct b as [B g].
  destruct y as [Y h].
  reflexivity.
Qed.

Lemma bhtower_index_zero : forall f b y,
    bhtower 0 f b y = veblen f b y.
Proof.
  reflexivity.
Qed.

Lemma bhtower_index_one : forall f b y,
    bhtower 1 f b y = vtower f b y.
Proof.
  reflexivity.
Qed.

Global Opaque bhtower.

Theorem bhtower_monotone : forall n f g a b x y,
    (forall x y, x <= y -> g x <= g y) ->
    (forall x, f x <= g x) ->
    a <= b ->
    x <= y ->
    bhtower n f a x <= bhtower n g b y.
Proof.
  induction n.
  { intros. rewrite bhtower_index_zero.
    rewrite (bhtower_index_zero g b y).
    transitivity (veblen g a x).
    apply veblen_mono_func; auto.
    apply veblen_le_mor; auto. }

  intros f g a b x y Hg Hfg. revert y f g a x Hg Hfg.
  induction b as [b Hb] using ordinal_induction.
  induction y as [y Hy] using ordinal_induction.
  intros.

  rewrite (bhtower_unroll (S n) f a x).
  rewrite (bhtower_unroll (S n) g b y).
  apply lub_least.
  { rewrite <- lub_le1. transitivity (g x); auto. }
  apply sup_least. intro ia.
  rewrite <- lub_le2.
  destruct (ord_le_subord a b H ia) as [ib ?].
  rewrite <- (sup_le _ _ ib).
  unfold fixpointGadget.

  apply sup_least; intro ix.
  assert (1 + x <= 1 + y).
  { apply addOrd_monotone; auto with ord; auto. }
  destruct (ord_le_subord (1+x) (1+y) H2 ix) as [iy ?].
  rewrite <- (sup_le _ _ iy).
  unfold fixOrd. apply sup_ord_le_morphism.
  intro m.
  induction m; simpl.
  - rewrite ord_le_unfold; simpl; intro q.
    destruct (ord_le_subord x y H0 q) as [q' ?].
    rewrite ord_lt_unfold. simpl. exists q'.
    apply Hy; auto with ord.
  - apply IHn; auto with ord.
Qed.

Lemma bhtower_zero n f x :
  bhtower n f 0 x ≈ f x.
Proof.
  rewrite bhtower_unroll.
  split.
  - apply lub_least; auto with ord.
    apply sup_least; intros [].
  - apply lub_le1.
Qed.

Lemma bhtower_nonzero n f y x :
  normal_function f ->
  0 < bhtower n f y x.
Proof.
  intros.
  rewrite bhtower_unroll.
  rewrite <- lub_le1.
  apply normal_nonzero; auto.
Qed.

Lemma fixpointGadget_monotone n f g y' y x' x :
  (forall x, f x <= g x) ->
  (forall x y, x <= y -> g x <= g y) ->
  y' <= y ->
  x' <= x ->
  fixpointGadget n f y' x' <= fixpointGadget n g y x.
Proof.
  destruct n.
  - simpl; intros.
    transitivity (fixOrd g x').
    apply fixOrd_monotone_func; auto.
    apply fixOrd_monotone; auto.
  - simpl; intros.
    apply sup_least; intros.
    destruct (ord_le_subord y' y H1 a) as [a' ?].
    rewrite <- (sup_le _ _ a').
    transitivity (fixOrd (bhtower n g (sz a')) x').
    apply fixOrd_monotone_func; auto.
    intros; apply bhtower_monotone; auto with ord.
    intros; apply bhtower_monotone; auto with ord.
    apply fixOrd_monotone; auto.
    intros; apply bhtower_monotone; auto with ord.
Qed.

Local Hint Resolve bhtower_monotone fixpointGadget_monotone : core.
Local Hint Resolve
      zero_complete
      succ_complete
      addOrd_complete
      complete_subord
      normal_monotone
      normal_complete
  : core.

Section bhtower_normal.
  Parameter n : nat.

  Hypothesis bhtower_normal1 :
    forall f a,
      normal_function f ->
      complete a ->
      normal_function (bhtower n f a).

  Hypothesis bhtower_normal2 :
    forall f,
      normal_function f ->
      normal_function (fun a => bhtower n f a 0).


  Lemma fixpointGadget_complete : forall f y x,
    normal_function f ->
    complete y ->
    complete x ->
    complete (fixpointGadget (S n) f y x).
  Proof.
  intros. simpl.
  apply sup_complete.
  - intro a. apply normal_fix_complete; auto with ord.
    intros. apply normal_inflationary; auto with ord.
  - hnf; intros.
    destruct (complete_directed y H0 a1 a2) as [a' [??]].
    exists a'.
    split; apply fixOrd_monotone_func; auto with ord.
  - destruct (complete_zeroDec y H0).
    + right. intro a.
      destruct (ord_le_subord y 0 H2 a) as [[] _].
    + rewrite ord_lt_unfold in H2. destruct H2 as [a ?].
      left. exists a.
      rewrite normal_fixpoint; auto.
      apply bhtower_nonzero; auto.
  Qed.

  Lemma fixpointGadget_above : forall f y x, 0 < y -> x <= fixpointGadget (S n) f y x.
  Proof.
    intros. simpl.
    rewrite ord_lt_unfold in H.
    destruct H as [y0 _].
    rewrite <- (sup_le _ _ y0).
    apply fixOrd_above.
  Qed.

  Lemma fixpointGadget_critical :
  forall f y x y',
    normal_function f ->
    complete y' ->
    complete y ->
    complete x ->
    y' < y ->
    bhtower n f y' (fixpointGadget (S n) f y x) ≈ fixpointGadget (S n) f y x.
  Proof.
    intros f y x y' Hf Hcy' Hcy Hcx.
    split.
    - intros. simpl fixpointGadget at 1.
      generalize H; intro.
      rewrite ord_lt_unfold in H0.
      destruct H0 as [y0  ?].
      etransitivity.
      { apply normal_continuous; auto.
        apply directed_monotone; auto.
        intros; apply fixOrd_monotone_func; auto with ord.
        intros. apply normal_fix_complete; auto with ord.
        intros; apply normal_inflationary; auto with ord. }

      apply sup_least; intro y1.
      destruct (complete_directed y Hcy y0 y1) as [y2 [??]].
      simpl.
      rewrite <- (sup_le _ _ y2).
      rewrite (normal_fixpoint (bhtower n f (sz y2))); auto.
      transitivity (bhtower n f y2 (fixOrd (bhtower n f (sz y1)) x)).
      apply bhtower_monotone; auto with ord.
      rewrite H0; auto.
      apply bhtower_monotone; auto with ord.
      apply fixOrd_monotone_func; auto with ord.
    - apply normal_inflationary; auto.
      apply fixpointGadget_complete; auto.
  Qed.

  Lemma fixpointGadget_least : forall f y x z,
      normal_function f ->
      complete y ->
      complete z ->
      x <= z ->
      (forall y', complete y' -> y' < y -> bhtower n f y' z <= z) ->
      fixpointGadget (S n) f y x <= z.
  Proof.
    intros.
    simpl fixpointGadget.
    apply sup_least; intro y0.
    apply normal_fix_least; auto.
    apply H3; auto with ord.
  Qed.

  Lemma fixpointGadget_fix : forall f y x,
      normal_function f ->
      complete x ->
      complete y ->
      0 < y ->
      f (fixpointGadget (S n) f y x) <= fixpointGadget (S n) f y x.
  Proof.
    intros.
    transitivity (bhtower n f 0 (fixpointGadget (S n) f y x)).
    { rewrite bhtower_unroll. apply lub_le1. }
    apply fixpointGadget_critical; auto.
  Qed.

  Section bhtower_normal_inner.
    Parameter b : Ord.
    Hypothesis Hcomplete_b : complete b.
    Hypothesis bhtower_normal :
      forall f a,
        a < b ->
        complete a ->
        normal_function f ->
        normal_function (bhtower (S n) f a).

    Lemma bhtower_complete :
      forall f x,
        normal_function f ->
        complete x ->
        complete (bhtower (S n) f b x).
    Proof.
      intros.
      induction x as [X h Hind].
      rewrite bhtower_unroll.
      destruct (complete_zeroDec b Hcomplete_b).
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
          rewrite <- fixpointGadget_fix; auto.
          rewrite bhtower_unroll.
          rewrite <- lub_le1.
          apply normal_monotone; auto.
          rewrite <- fixpointGadget_above; auto with ord.
          rewrite ord_le_unfold; intro q.
          rewrite ord_lt_unfold; exists q; simpl.
          rewrite bhtower_unroll.
          rewrite <- lub_le1.
          apply normal_inflationary; auto.
          apply H0.
          rewrite <- addOrd_le1; auto with ord.
          apply bhtower_normal; auto with ord.
          { apply lim_complete; auto.
            intros. apply Hind; auto.
            apply H0.
            apply directed_monotone; auto.
            intros; apply bhtower_monotone; auto with ord.
            apply H0.
          }
          rewrite <- addOrd_le1; auto with ord.
        + apply normal_complete; auto.
        + apply sup_complete.
          * intros.
            apply fixpointGadget_complete.
            apply bhtower_normal; auto with ord.
            apply addOrd_complete; auto.
            apply lim_complete.
            ** intros. apply Hind; auto.
               apply H0.
            ** apply directed_monotone; auto.
               intros; apply bhtower_monotone; auto with ord.
            ** apply H0.
          * apply directed_monotone; auto.
            intros.
            apply fixpointGadget_monotone; auto with ord.
          * left.
            rewrite ord_lt_unfold in H1.
            destruct H1 as [b0 ?].
            exists b0.
            rewrite <- fixpointGadget_fix; auto.
            apply bhtower_nonzero; auto.
            apply bhtower_normal; auto with ord.
            { apply lim_complete; auto.
              intros. apply Hind; auto.
              apply H0.
              apply directed_monotone; auto.
              intros; apply bhtower_monotone; auto with ord.
              apply H0.
            }
            rewrite <- addOrd_le1; auto with ord.
    Qed.

    Lemma bhtower_complete_lemma1 :
      forall f x,
        normal_function f ->
        complete x ->
        complete (limOrd (fun i : x => bhtower (S n) f b (x i))).
    Proof.
      intros.
      apply lim_complete.
      intros. apply bhtower_complete; auto.
      apply directed_monotone; auto.
      intros. apply bhtower_monotone; auto with ord.
      destruct x; apply H0.
    Qed.

    Lemma bhtower_complete_lemma2 :
      forall f x (a:b),
        normal_function f ->
        complete x ->
        complete
          (fixpointGadget (S n) (bhtower (S n) f a) (1+x) (limOrd (fun i:x => bhtower (S n) f b (x i)))).
    Proof.
      intros.
      apply fixpointGadget_complete; auto.
      apply bhtower_normal; auto with ord.
      apply bhtower_complete_lemma1; auto.
    Qed.

    Lemma bhtower_fixpointGadget_directed :
      forall f x,
        normal_function f ->
        complete x ->
        directed b
                 (fun a : b =>
                    (fixpointGadget (S n) (bhtower (S n) f a) (1+x) (limOrd (fun i:x => bhtower (S n) f b (x i))))).
    Proof.
      intros.
      apply directed_monotone; auto.
      intros. apply fixpointGadget_monotone; auto with ord.
    Qed.

    Lemma bhtower_complete_lemma3 :
      forall f x,
        normal_function f ->
        complete x ->
        complete
          (supOrd (fun a:b =>
                     (fixpointGadget (S n) (bhtower (S n) f a) (1+x) (limOrd (fun i:x => bhtower (S n) f b (x i)))))).
    Proof.
      intros.
      apply sup_complete.
      - intro. apply bhtower_complete_lemma2; auto.
      - apply bhtower_fixpointGadget_directed; auto.
      - destruct (complete_zeroDec b Hcomplete_b).
        + right. intro.
          destruct (ord_le_subord b 0 H1 a) as [[] _].
        + rewrite ord_lt_unfold in H1.
          destruct H1 as [a ?].
          left. exists a.
          rewrite <- fixpointGadget_fix; auto.
          apply bhtower_nonzero; auto.
          apply bhtower_normal; auto with ord.
          apply bhtower_complete_lemma1; auto.
          rewrite <- addOrd_le1.
          auto with ord.
    Qed.

    Local Hint Resolve
          bhtower_complete
          bhtower_complete_lemma1
          bhtower_complete_lemma2
          bhtower_complete_lemma3
          bhtower_fixpointGadget_directed : core.

    Lemma fixpointGadget_strongly_critical : forall f a y x,
        forall a',
          normal_function f ->
          complete a' ->
          complete a ->
          complete x ->
          complete y ->
          y > 0 ->
          a < b ->
          a' < a ->
          bhtower n (bhtower (S n) f a') (fixpointGadget (S n) (bhtower (S n) f a) y x) 0
          <= fixpointGadget (S n) (bhtower (S n) f a) y x.
    Proof.
      intros f a y x.
      revert a y.
      induction x as [X g Hx].
      intros a y a' Hf Hca' Hca Hcx Hcy Hy Hb Ha.
      simpl fixpointGadget.
      rewrite ord_lt_unfold in Hy.
      destruct Hy as [y0 _].
      etransitivity.
      { apply (normal_continuous (fun q => bhtower n (bhtower (S n) f a') q 0)); auto.
        + apply bhtower_normal2.
          apply bhtower_normal; auto with ord.
          transitivity a; auto.
        + apply directed_monotone; auto.
          intros; apply fixOrd_monotone_func; auto.
          intros; apply bhtower_monotone; auto with ord.
        + intro. apply normal_fix_complete; auto.
          apply normal_inflationary; auto. }

      apply sup_least; intro i.
      rewrite <- (sup_le _ _ i).
      rewrite (normal_fixpoint) at 2; auto.

      transitivity (bhtower (S n) f a (fixOrd (bhtower n (bhtower (S n) f a) (sz i)) (ord X g))).
      2:{ rewrite (bhtower_unroll n). apply lub_le1. }

      rewrite (bhtower_unroll (S n) f a).
      rewrite <- lub_le2.
      generalize Ha; intros.
      rewrite ord_lt_unfold in Ha0.
      destruct Ha0.
      rewrite <- (sup_le _ _ x).

      rewrite (bhtower_unroll n).
      apply lub_least.
      - assert (complete (fixOrd (bhtower n (bhtower (S n) f a) (sz i)) (ord X g))).
        { apply normal_fix_complete; auto.
          apply normal_inflationary; auto. }
        rewrite <- fixpointGadget_fix; auto.
        apply bhtower_monotone; auto with ord.
        apply bhtower_normal; auto with ord.
        transitivity a; auto with ord.

        { apply lim_complete; auto with ord.
          apply directed_monotone; auto.
          apply H0. }
        rewrite <- addOrd_le1. auto with ord.

      - apply sup_least; intro.
        transitivity (fixpointGadget n (bhtower n (bhtower (S n) f a') (sz a0)) 1 0).
        { apply fixpointGadget_monotone; auto with ord.
          rewrite addOrd_zero_r. auto with ord.
          rewrite ord_le_unfold. simpl. intros []. }
        transitivity (fixOrd (bhtower n (bhtower (S n) f a') (sz a0)) 0).
        { destruct n; simpl; auto with ord.
          apply sup_least; intro.
          apply fixOrd_monotone_func; auto with ord.
          intro. rewrite bhtower_zero. reflexivity. }
        apply normal_fix_least; auto with ord.
        apply bhtower_normal1; auto with ord.
        apply bhtower_normal; auto with ord.
        transitivity a; auto.
        apply complete_subord.
        apply normal_fix_complete; auto with ord.
        apply normal_inflationary; auto with ord.
        apply fixpointGadget_complete; auto with ord.
        apply bhtower_normal; auto with ord.
        transitivity a; auto with ord.
        apply addOrd_complete; auto.
        apply normal_fix_complete; auto with ord.
        apply normal_inflationary; auto with ord.
        { apply lim_complete; auto.
          intros. apply normal_complete; auto with ord.
          apply complete_subord.
          apply normal_fix_complete; auto with ord.
          apply normal_inflationary; auto with ord.
          apply directed_monotone; auto.
          apply normal_fix_complete; auto with ord.
          apply normal_inflationary; auto with ord. }
        rewrite <- (fixpointGadget_critical _ _ _ (sz a0)) at 2; auto with ord.
        apply bhtower_normal; auto with ord.
        transitivity a; auto with ord.
        apply complete_subord; auto.
        apply normal_fix_complete; auto with ord.
        apply normal_inflationary; auto with ord.
        apply addOrd_complete; auto.
        apply normal_fix_complete; auto with ord.
        apply normal_inflationary; auto with ord.
        { apply lim_complete; auto.
          intros. apply normal_complete; auto with ord.
          apply complete_subord.
          apply normal_fix_complete; auto with ord.
          apply normal_inflationary; auto with ord.
          apply directed_monotone; auto.
          apply normal_fix_complete; auto with ord.
          apply normal_inflationary; auto with ord. }

        rewrite <- addOrd_le2.
        auto with ord.
    Qed.



  End bhtower_normal_inner.
End bhtower_normal.
