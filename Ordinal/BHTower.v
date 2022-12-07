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

Fixpoint bhtower (n:nat) : (Ord -> Ord) -> Ord -> Ord -> Ord :=
  match n with
  | O => fun f b y => f y
  | S m =>
    let nextCritical (f:Ord -> Ord) (y x:Ord) :=
         supOrd (fun z:y => fixOrd (bhtower m f z) x)
    in
    fun f =>
    fix vtower (b:Ord) : Ord -> Ord :=
      fix inner (y:Ord) : Ord :=
      match b, y with
      | ord B g, ord Y h =>
        f (ord Y h) ⊔
          supOrd (fun a:B => nextCritical (vtower (g a)) (1 + ord Y h)
                                 (limOrd (fun x:Y => inner (h x))))
      end
  end.

Definition nextCritical n (f:Ord -> Ord) (y x:Ord) :=
  supOrd (fun z:y => fixOrd (bhtower n f z) x).

Lemma bhtower_unroll : forall n f (b y:Ord),
    bhtower (S n) f b y =
    f y ⊔ supOrd (fun a:b => nextCritical n (bhtower (S n) f a) (1+y)
                               (limOrd (fun x:y => bhtower (S n) f b x))).
Proof.
  intros.
  destruct b as [B g].
  destruct y as [Y h].
  reflexivity.
Qed.

Lemma bhtower_index_zero : forall f b y,
    bhtower 0 f b y = f y.
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
    transitivity (g x); auto. }

  intros f g a b x y Hg Hfg. revert y f g a x Hg Hfg.
  induction b as [b Hb] using ordinal_induction.
  induction y as [y Hy] using ordinal_induction.
  intros.

  rewrite (bhtower_unroll n f a x).
  rewrite (bhtower_unroll n g b y).
  apply lub_least.
  { rewrite <- lub_le1. transitivity (g x); auto. }
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
  intro m.
  induction m; simpl.
  - rewrite ord_le_unfold; simpl; intro q.
    destruct (ord_le_subord x y H0 q) as [q' ?].
    rewrite ord_lt_unfold. simpl. exists q'.
    apply Hy; auto with ord.
  - apply IHn; auto with ord.
Qed.

(* TODO? is it possible to prove these together instead?
   It seems tricky to make it work out, even though the proofs
   are nearly identical.
 *)
Theorem bhtower_monotone_strong : forall m n f g a b x y,
    (forall x y, x <= y -> g x <= g y) ->
    (forall x, f x <= g x) ->
    (m <= n)%nat ->
    a <= b ->
    x <= y ->
    bhtower m f a x <= bhtower n g b y.
Proof.
  induction m.
  { intros. rewrite bhtower_index_zero.
    destruct n. rewrite bhtower_index_zero; auto with ord.
    transitivity (g x); auto.
    rewrite bhtower_unroll.
    rewrite <- lub_le1.
    transitivity (g x); auto. }

  intros n f g a b x y Hg Hfg. revert y f g a x Hg Hfg.
  induction b as [b Hb] using ordinal_induction.
  induction y as [y Hy] using ordinal_induction.
  intros.

  destruct n; [ lia | ].
  rewrite (bhtower_unroll m f a x).
  rewrite (bhtower_unroll n g b y).
  apply lub_least.
  { rewrite <- lub_le1. transitivity (g x); auto. }
  apply sup_least. intro ia.
  rewrite <- lub_le2.
  destruct (ord_le_subord a b H0 ia) as [ib ?].
  rewrite <- (sup_le _ _ ib).
  unfold nextCritical.

  apply sup_least; intro ix.
  assert (1 + x <= 1 + y).
  { apply addOrd_monotone; auto with ord; auto. }
  destruct (ord_le_subord (1+x) (1+y) H3 ix) as [iy ?].
  rewrite <- (sup_le _ _ iy).
  etransitivity; [ eapply fixOrd_monotone_func | eapply fixOrd_monotone ].
  + intros. apply IHm; auto with arith ord.
    intros. apply bhtower_monotone; auto with ord.
  + intros. apply bhtower_monotone; auto with ord.
    intros. apply bhtower_monotone; auto with ord.
  + intros. apply bhtower_monotone; auto with ord.
    intros. apply bhtower_monotone; auto with ord.
  + rewrite ord_le_unfold; simpl; intro q.
    destruct (ord_le_subord x y H1 q) as [q' ?].
    rewrite ord_lt_unfold. simpl. exists q'.
    apply Hy; auto with ord.
Qed.


Lemma nextCritical_monotone n f g y' y x' x :
  (forall x, f x <= g x) ->
  (forall x y, x <= y -> g x <= g y) ->
  y' <= y ->
  x' <= x ->
  nextCritical n f y' x' <= nextCritical n g y x.
Proof.
  intros. unfold nextCritical.
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

Local Hint Resolve bhtower_monotone nextCritical_monotone : core.
Local Hint Resolve
      zero_complete
      succ_complete
      addOrd_complete
      complete_subord
      normal_monotone
      normal_complete
  : core.

Lemma bhtower_first_cont_zero f :
  scott_continuous (fun q => bhtower 0 f q 0).
Proof.
  hnf; intros.
  rewrite bhtower_index_zero.
  rewrite <- (sup_le _ _ a0).
  rewrite bhtower_index_zero.
  reflexivity.
Qed.


Lemma bhtower_index_one : forall f b y,
    normal_function f ->
    bhtower 1 f b y ≈ veblen f b y.
Proof.
  intros f b y Hf.
  revert y.
  induction b as [B g Hb].
  induction y as [Y h Hy].
  rewrite bhtower_unroll.
  rewrite veblen_unroll.
  apply ord_lub_eq_mor; auto with ord.
  apply sup_ord_eq_morphism.
  hnf; intro i.
  unfold nextCritical.
  split.
  - apply sup_least; intros.
    transitivity
      (fixOrd (bhtower 0 (bhtower 1 f (g i)) (sz a))
              (limOrd (fun x : ord Y h => veblen f (ord B g) (sz x)))).
    { apply fixOrd_monotone.
      intros.
      rewrite bhtower_index_zero.
      rewrite bhtower_index_zero.
      apply bhtower_monotone; auto with ord.
      rewrite ord_le_unfold; intro x. simpl.
      rewrite ord_lt_unfold. simpl. exists x.
      apply Hy. }
    apply fixOrd_monotone_func.
    intros. rewrite bhtower_index_zero. apply Hb.
    intros. apply veblen_monotone; auto.
  - rewrite addOrd_unfold.
    rewrite lub_unfold. simpl.
    rewrite <- (sup_le _ _ (inl _ tt)).
    transitivity
      (fixOrd (bhtower 0 (bhtower 1 f (g i)) 0)
              (limOrd (fun x : ord Y h => veblen f (ord B g) (sz x)))).
    { apply fixOrd_monotone_func.
      intros. rewrite bhtower_index_zero.
      apply Hb.
      intros.
      rewrite bhtower_index_zero.
      rewrite bhtower_index_zero.
      apply bhtower_monotone; auto with ord. }
    apply fixOrd_monotone; auto.
    intros.
    rewrite bhtower_index_zero.
    rewrite bhtower_index_zero.
    apply bhtower_monotone; auto with ord.
    rewrite ord_le_unfold; intro x. simpl.
    rewrite ord_lt_unfold. simpl. exists x.
    apply Hy.
Qed.

Lemma bhtower_zero n f x :
  bhtower n f 0 x ≈ f x.
Proof.
  destruct n; simpl; auto.
  rewrite bhtower_index_zero. auto with ord.
  rewrite bhtower_unroll.
  split.
  - apply lub_least; auto with ord.
    apply sup_least; intros [].
  - apply lub_le1.
Qed.

Lemma bhtower_above_f n f b x :
  f x <= bhtower n f b x.
Proof.
  destruct n; simpl; auto.
  rewrite bhtower_index_zero. auto with ord.
  rewrite bhtower_unroll.
  apply lub_le1.
Qed.

Lemma bhtower_nonzero n f b x :
  normal_function f ->
  0 < bhtower n f b x.
Proof.
  intros.
  rewrite <- bhtower_above_f.
  apply normal_nonzero; auto.
Qed.

Lemma nextCritical_above : forall n f y x, 0 < y -> x <= nextCritical n f y x.
Proof.
  intros. simpl.
  rewrite ord_lt_unfold in H.
  destruct H as [y0 _].
  unfold nextCritical.
  rewrite <- (sup_le _ _ y0).
  apply fixOrd_above.
Qed.

Section bhtower_normal.
  Variable n : nat.

  Hypothesis bhtower_n_normal :
    forall f a,
      normal_function f ->
      complete a ->
      normal_function (bhtower n f a).

  Hypothesis bhtower_n_continuous :
    forall f,
      normal_function f ->
      scott_continuous (fun a => bhtower n f a 0).

  Lemma nextCritical_complete : forall f y x,
    normal_function f ->
    complete y ->
    complete x ->
    complete (nextCritical n f y x).
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

  Lemma nextCritical_least : forall f y x z,
      normal_function f ->
      complete y ->
      complete z ->
      x <= z ->
      (forall y', complete y' -> y' < y -> bhtower n f y' z <= z) ->
      nextCritical n f y x <= z.
  Proof.
    intros.
    unfold nextCritical.
    apply sup_least; intro y0.
    apply normal_fix_least; auto.
    apply H3; auto with ord.
  Qed.

  Lemma nextCritical_critical :
  forall f y x y',
    normal_function f ->
    complete y' ->
    complete y ->
    complete x ->
    y' < y ->
    bhtower n f y' (nextCritical n f y x) ≈ nextCritical n f y x.
  Proof.
    intros f y x y' Hf Hcy' Hcy Hcx.
    split.
    - intros. unfold nextCritical at 1.
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
      unfold nextCritical.
      rewrite <- (sup_le _ _ y2).
      rewrite (normal_fixpoint (bhtower n f (sz y2))); auto.
      transitivity (bhtower n f y2 (fixOrd (bhtower n f (sz y1)) x)).
      apply bhtower_monotone; auto with ord.
      rewrite H0; auto.
      apply bhtower_monotone; auto with ord.
      apply fixOrd_monotone_func; auto with ord.
    - apply normal_inflationary; auto.
      apply nextCritical_complete; auto.
  Qed.

  Lemma nextCritical_fix : forall f y x,
      normal_function f ->
      complete x ->
      complete y ->
      0 < y ->
      f (nextCritical n f y x) <= nextCritical n f y x.
  Proof.
    intros.
    transitivity (bhtower n f 0 (nextCritical n f y x)).
    { rewrite bhtower_zero. reflexivity. }
    apply nextCritical_critical; auto.
  Qed.

  Section bhtower_normal_inner.
    Variable b : Ord.
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
          rewrite <- nextCritical_fix; auto.
          rewrite bhtower_unroll.
          rewrite <- lub_le1.
          apply normal_monotone; auto.
          rewrite <- nextCritical_above; auto with ord.
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
            apply nextCritical_complete; auto.
            apply bhtower_normal; auto with ord.
            apply lim_complete.
            ** intros. apply Hind; auto.
               apply H0.
            ** apply directed_monotone; auto.
               intros; apply bhtower_monotone; auto with ord.
            ** apply H0.
          * apply directed_monotone; auto.
            intros.
            apply nextCritical_monotone; auto with ord.
          * left.
            rewrite ord_lt_unfold in H1.
            destruct H1 as [b0 ?].
            exists b0.
            rewrite <- nextCritical_fix; auto.
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
          (nextCritical n (bhtower (S n) f a) (1+x) (limOrd (fun i:x => bhtower (S n) f b (x i)))).
    Proof.
      intros.
      apply nextCritical_complete; auto.
      apply bhtower_normal; auto with ord.
      apply bhtower_complete_lemma1; auto.
    Qed.

    Lemma bhtower_nextCritical_directed :
      forall f x,
        normal_function f ->
        complete x ->
        directed b
                 (fun a : b =>
                    (nextCritical n (bhtower (S n) f a) (1+x) (limOrd (fun i:x => bhtower (S n) f b (x i))))).
    Proof.
      intros.
      apply directed_monotone; auto.
      intros. apply nextCritical_monotone; auto with ord.
    Qed.

    Lemma bhtower_complete_lemma3 :
      forall f x,
        normal_function f ->
        complete x ->
        complete
          (supOrd (fun a:b =>
                     (nextCritical n (bhtower (S n) f a) (1+x) (limOrd (fun i:x => bhtower (S n) f b (x i)))))).
    Proof.
      intros.
      apply sup_complete.
      - intro. apply bhtower_complete_lemma2; auto.
      - apply bhtower_nextCritical_directed; auto.
      - destruct (complete_zeroDec b Hcomplete_b).
        + right. intro.
          destruct (ord_le_subord b 0 H1 a) as [[] _].
        + rewrite ord_lt_unfold in H1.
          destruct H1 as [a ?].
          left. exists a.
          rewrite <- nextCritical_fix; auto.
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
          bhtower_nextCritical_directed : core.

    Lemma bhtower_inc : forall f x y,
        normal_function f ->
        complete y ->
        x < y ->
        bhtower (S n) f b x < bhtower (S n) f b y.
    Proof.
      intros f x y. revert x.
      induction y as [Y h Hy]. intros x Hf; intros.
      rewrite (bhtower_unroll n f b (ord Y h)).
      destruct (complete_zeroDec b Hcomplete_b).
      - assert (b ≈ 0).
        { split; auto with ord. }
        rewrite <- lub_le1.
        apply ord_le_lt_trans with (f x); auto.
        rewrite (bhtower_unroll n f b x).
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
        apply bhtower_monotone; auto with ord.
        rewrite <- addOrd_le1.
        auto with ord.
    Qed.

    Lemma bhtower_inflate :
      forall f x,
        normal_function f ->
        complete x ->
        x <= bhtower (S n) f b x.
    Proof.
      intros.
      rewrite bhtower_unroll.
      rewrite <- lub_le1.
      apply normal_inflationary; auto.
    Qed.

    Lemma nextCritical_inflate_lemma : forall f x (a0:b),
        normal_function f ->
        complete x ->
        bhtower (S n) f b x <= supOrd (fun a:b => nextCritical n (bhtower (S n) f a) (1+x) (limOrd (fun i => bhtower (S n) f b (x i)))).
    Proof.
      intros.
      rewrite (bhtower_unroll n f b x).
      apply lub_least; auto with ord.
      rewrite <- (sup_le _ _ a0).
      rewrite <- nextCritical_fix; auto.
      rewrite bhtower_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      rewrite <- nextCritical_above.
      rewrite ord_le_unfold. intro i.
      rewrite ord_lt_unfold. exists i. simpl.
      apply bhtower_inflate; auto.
      rewrite <- addOrd_le1.
      auto with ord.
      apply bhtower_normal; auto with ord.
      rewrite <- addOrd_le1.
      auto with ord.
    Qed.

    Lemma bhtower_fixpoint' : forall f a x,
      normal_function f ->
      complete a ->
      complete x ->
      a < b ->
      bhtower (S n) f a (bhtower (S n) f b x) <= bhtower (S n) f b x.
    Proof.
      intro f.
      induction a as [A g Hinda].
      intros x Hf Hca Hcx H.
      rewrite (bhtower_unroll n f (ord A g)).
      apply lub_least.
      { rewrite ord_lt_unfold in H. destruct H as [b0 ?].
        etransitivity.
        { apply normal_monotone; auto.
          apply (nextCritical_inflate_lemma f x b0); auto.
        }
        etransitivity.
        { apply normal_continuous; auto. }
        apply sup_least; intro i.
        rewrite (bhtower_unroll n f b x).
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ i).
        rewrite <- (nextCritical_fix
                      (bhtower (S n) f (sz i)) (1 + x)
                      (limOrd (fun x0 : x => bhtower (S n) f b (sz x0)))); auto.
        rewrite bhtower_unroll.
        apply lub_le1.
        apply bhtower_normal; auto with ord.
        rewrite <- addOrd_le1.
        auto with ord. }

      apply sup_least; intro q.
      apply nextCritical_least; auto.
      + apply bhtower_normal; auto with ord.
        transitivity (ord A g); auto with ord.
      + rewrite ord_le_unfold. simpl.
        intros.
        rewrite (bhtower_unroll n f b).
        rewrite <- lub_le2.
        rewrite ord_lt_unfold in H.
        destruct H as [m ?].
        apply ord_le_lt_trans with (bhtower (S n) f (b m) (bhtower (S n) f b x a)).
        apply bhtower_monotone; auto with ord.
        apply ord_lt_le_trans with
            (bhtower (S n) f (b m)
            (supOrd
               (fun a1 : b =>
                  nextCritical n (bhtower (S n) f (sz a1)) (1 + x) (limOrd (fun x0 : x => bhtower (S n) f b (x x0)))))).
        apply normal_increasing; auto.
        apply bhtower_normal; auto with ord.
        apply ord_lt_le_trans with (bhtower (S n) f b x); auto with ord.
        apply nextCritical_inflate_lemma; auto with ord.
        etransitivity.
        { apply normal_continuous; auto.
          apply bhtower_normal; auto with ord.
        }
        apply sup_least; intros i.
        destruct (complete_directed b Hcomplete_b m i) as [k [??]].
        rewrite <- (sup_le _ _ k).
        rewrite <- (nextCritical_fix (bhtower (S n) f (sz k))); auto.
        apply bhtower_monotone; auto with ord.
        apply bhtower_normal; auto with ord.
        rewrite <- addOrd_le1.
        apply succ_lt.

      + induction y' as [Y h Hindy].
        intros.
        assert (ord Y h < bhtower (S n) f b x).
        { eapply ord_lt_le_trans; [ apply H1 | ].
          transitivity (bhtower (S n) f (g q) (bhtower (S n) f b x)).
          apply onePlus_least_normal; auto with ord.
          apply bhtower_normal; auto.
          transitivity (ord A g); auto with ord.
          apply Hca.
          apply Hinda; auto.
          apply Hca.
          transitivity (ord A g); auto with ord. }
        assert (ord Y h < supOrd (fun a:b => nextCritical n (bhtower (S n) f a) (1+x) (limOrd (fun i => bhtower (S n) f b (x i))))).
        { rewrite ord_lt_unfold in H. destruct H.
          rewrite <- nextCritical_inflate_lemma; auto. }
        apply sup_lt in H3.
        destruct H3 as [b1 H3].
        unfold nextCritical in H3.
        apply sup_lt in H3.
        destruct H3 as [z1 H3].
        transitivity (bhtower n (bhtower (S n) f (sz q)) (ord Y h)
                              (supOrd (fun a:b => nextCritical n (bhtower (S n) f a) (1+x) (limOrd (fun i => bhtower (S n) f b (x i)))))).
        { apply bhtower_monotone; auto with ord.
          apply nextCritical_inflate_lemma; auto. }
        transitivity (supOrd (fun a:b =>
                                bhtower n (bhtower (S n) f (sz q)) (ord Y h)
                                        (nextCritical n (bhtower (S n) f (sz a)) (1 + x)
                                        (limOrd (fun i : x => bhtower (S n) f b (x i)))))).
        { apply normal_continuous; auto.
          apply bhtower_n_normal; auto.
          apply bhtower_normal; auto with ord.
          transitivity (ord A g); auto with ord. }
        apply sup_least; intro b2.
        unfold nextCritical.
        transitivity (supOrd (fun z:(1+x)%ord =>
                                bhtower n (bhtower (S n) f (sz q)) (ord Y h)
                                        (fixOrd (bhtower n (bhtower (S n) f (sz b2)) (sz z))
                                          (limOrd (fun i : x => bhtower (S n) f b (x i)))))).
        { apply normal_continuous; auto.
          apply bhtower_n_normal; auto.
          apply bhtower_normal; auto with ord.
          transitivity (ord A g); auto with ord.
          apply directed_monotone; auto with ord.
          intros. apply fixOrd_monotone_func; auto with ord.
          intros. apply normal_fix_complete; auto with ord.
          intros. apply normal_inflationary; auto with ord.
          intros. apply normal_complete; auto with ord. }

        apply sup_least. intro z2.
        assert (Hx1 : complete (1+x)).
        { auto with ord. }
        destruct (complete_directed b Hcomplete_b b1 b2) as [b' [??]].
        rewrite ord_lt_unfold in H. destruct H as [b3 H].
        destruct (complete_directed b Hcomplete_b b' b3) as [b'' [??]].
        destruct (complete_directed (1+x) Hx1 z1 z2) as [z' [??]].
        rewrite (bhtower_unroll n f b x).
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ b'').
        unfold nextCritical.
        rewrite <- (sup_le _ _ z').
        rewrite (normal_fixpoint (bhtower n (bhtower (S n) f (sz b'')) (sz z'))).
        rewrite <- (bhtower_above_f n (bhtower (S n) f b'')).
        assert (q < b'').
        { eapply ord_lt_le_trans with (ord A g); auto with ord.
          transitivity b3; auto. }
        rewrite (bhtower_unroll n f b'').
        rewrite <- lub_le2.
        rewrite ord_lt_unfold in H10.
        destruct H10 as [qb ?].
        rewrite <- (sup_le _ _ qb).
        assert (Hfixc : complete (fixOrd (bhtower n (bhtower (S n) f (sz b'')) (sz z'))
         (limOrd (fun x0 : x => bhtower (S n) f b (sz x0))))).
        { apply normal_fix_complete; auto with ord.
          intros; apply normal_inflationary; auto.
          apply bhtower_n_normal; auto.
          apply bhtower_normal; auto with ord. }

        rewrite <- (nextCritical_critical (bhtower (S n) f qb) _ _ (ord Y h)); auto with ord.
        apply bhtower_monotone; auto with ord.
        rewrite <- nextCritical_above.
        transitivity (fixOrd (bhtower n (bhtower (S n) f (sz b'')) (sz z'))
                (limOrd (fun x0 : x => bhtower (S n) f b (sz x0)))).
        { apply fixOrd_monotone_func; auto with ord.
          intros; apply bhtower_monotone; auto with ord.
          intros; apply bhtower_monotone; auto with ord.
          rewrite H5; auto. }
        rewrite ord_le_unfold. simpl; intro r.
        rewrite ord_lt_unfold. exists r. simpl.
        apply normal_inflationary.
        apply bhtower_normal; auto with ord.
        apply complete_subord; auto.
        rewrite <- addOrd_le1.
        auto with ord.
        apply bhtower_normal; auto with ord.
        transitivity b''; auto with ord.
        { apply lim_complete; auto with ord.
          apply directed_monotone; auto with ord.
          apply Hfixc. }
        eapply ord_lt_le_trans; [ apply H3 |].
        etransitivity; [ | apply addOrd_le2 ].
        { apply fixOrd_monotone_func; auto with ord.
          intros; apply bhtower_monotone; auto with ord.
          intros; apply bhtower_monotone; auto with ord.
          rewrite H4; auto. }
        apply bhtower_n_normal; auto.
        apply bhtower_normal; auto with ord.
        { apply lim_complete; auto.
          apply directed_monotone; auto with ord.
          destruct x; apply Hcx. }
    Qed.

    Lemma bhtower_continuous f :
      normal_function f ->
      scott_continuous (bhtower (S n) f b).
    Proof.
      intro Hf.
      hnf; simpl; intros.
      rewrite bhtower_unroll.
      apply lub_least.
      - etransitivity; [ apply normal_continuous | ]; auto.
        apply sup_least; intro i.
        rewrite <- (sup_le _ _ i).
        rewrite bhtower_unroll.
        apply lub_le1.
      - apply sup_least; simpl; intros.
        apply nextCritical_least; auto.
        + apply bhtower_normal; auto with ord.
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
          exists a'; split; apply bhtower_monotone; auto with ord.
          left. exists a0.
          apply bhtower_nonzero.
          auto.

        + apply limit_least. rewrite sup_unfold.
          simpl. intros [i j]. simpl.
          rewrite <- (sup_le _ _ i).
          apply bhtower_inc; auto with ord.

        + intros.
          transitivity (supOrd (fun i => bhtower n (bhtower (S n) f (sz a)) y' (bhtower (S n) f b (f0 i)))).
          apply normal_continuous; auto with ord.
          apply (directed_monotone (ord A f0)); auto.
          intros; apply bhtower_monotone; auto with ord.
          simpl; intuition.

          apply sup_least; intro i.
          rewrite addOrd_unfold in H2.
          apply lub_lt in H2.
          destruct H2.
          * assert (y' ≈ 0).
            { split; auto with ord.
              rewrite ord_lt_unfold in H2. destruct H2; auto. }
            rewrite <- (sup_le _ _ i).
            transitivity (bhtower n (bhtower (S n) f (sz a)) 0 (bhtower (S n) f b (f0 i))).
            apply bhtower_monotone; auto with ord.
            apply H3.
            rewrite bhtower_zero.
            apply bhtower_fixpoint'; auto with ord.

          * apply sup_lt in H2.
            rewrite sup_unfold in H2. simpl in H2.
            destruct H2 as [[j q]?]. simpl in H2.
            assert (y' < 1 + f0 j).
            { eapply ord_lt_le_trans; [ apply H2 | ].
              apply succ_least.
              apply addOrd_increasing. auto with ord. }
            destruct (H i j) as [k [??]].
            rewrite <- (sup_le _ _ k).

            transitivity (bhtower n (bhtower (S n) f (sz a)) y' (bhtower (S n) f b (f0 k))).
            { apply bhtower_monotone; auto with ord. }

            rewrite addOrd_unfold in H3.
            apply lub_lt in H3.
            destruct H3.
            { transitivity (bhtower n (bhtower (S n) f (sz a)) 0 (bhtower (S n) f b (f0 k))).
              apply bhtower_monotone; auto with ord.
              rewrite ord_lt_unfold in H3.
              destruct H3; auto.
              rewrite bhtower_zero.
              apply bhtower_fixpoint'; auto with ord.
            }
            apply sup_lt in H3. destruct H3 as [r ?].
            rewrite ord_lt_unfold in H3.
            destruct H3; simpl in *.

            transitivity (bhtower n (bhtower (S n) f (sz a)) y' (supOrd
                                                     (fun a1 : b =>
                                                        nextCritical n (bhtower (S n) f (sz a1)) (1 + f0 k)
                                                              (limOrd (fun x : f0 k => bhtower (S n) f b (f0 k x)))))).
            apply bhtower_monotone; auto with ord.
            rewrite nextCritical_inflate_lemma; auto with ord.

            etransitivity; [ apply normal_continuous | ]; auto.
            apply bhtower_n_normal; auto.
            apply bhtower_normal; auto with ord.
            apply sup_least; intro a2.

            destruct (complete_directed b Hcomplete_b a a2) as [a'[??]].
            rewrite (bhtower_unroll n f b (f0 k)).
            rewrite <- lub_le2.
            rewrite <- (sup_le _ _ a').
            rewrite <- (nextCritical_critical (bhtower (S n) f (sz a')) (1 + f0 k) _ y'); auto.
            apply bhtower_monotone; auto with ord.
            apply bhtower_normal; auto with ord.
            rewrite <- H5.
            rewrite H3.
            apply addOrd_increasing; auto with ord.
    Qed.

  End bhtower_normal_inner.

  Lemma bhtower_S_normal :
    forall b f,
      normal_function f ->
      complete b ->
      normal_function (bhtower (S n) f b).
  Proof.
    induction b as [b Hb] using ordinal_induction.
    intros. constructor.
    + intros; apply bhtower_monotone; auto with ord.
    + intros. apply bhtower_inc; auto with ord.
    + apply bhtower_continuous; auto.
    + intros. apply bhtower_complete; auto.
    + intros. apply bhtower_nonzero; auto.
  Qed.

  Lemma bhtower_S_fixpoint :
    forall b f a x,
      normal_function f ->
      complete a ->
      complete b ->
      complete x ->
      a < b ->
      bhtower (S n) f a (bhtower (S n) f b x) ≤ bhtower (S n) f b x.
  Proof.
    intros.
    apply bhtower_fixpoint'; auto.
    intros. apply bhtower_S_normal; auto.
  Qed.

  Lemma bhtower_S_continuous :
    forall f,
      normal_function f ->
      scott_continuous (fun b => bhtower (S n) f b 0).
  Proof.
    intros. hnf; simpl; intros.
    rewrite bhtower_unroll.
    apply lub_least.
    { rewrite <- (sup_le _ _ a0).
      rewrite bhtower_unroll.
      auto with ord. }
    apply sup_least. rewrite sup_unfold. simpl; intros.
    destruct a as [a q]. simpl.
    rewrite <- (sup_le _ _ a).
    rewrite bhtower_unroll.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ q).
    apply nextCritical_monotone; auto with ord.
    rewrite ord_le_unfold. simpl; intros [].
  Qed.

End bhtower_normal.

Lemma bhtower_normal_and_continuous :
  forall n,
    (forall f b, normal_function f -> complete b -> normal_function (bhtower n f b)) /\
    (forall f, normal_function f -> scott_continuous (fun b => bhtower n f b 0)).
Proof.
  induction n; split; intros.
  - constructor.
    * intros; repeat rewrite bhtower_index_zero.
      apply normal_monotone; auto.
    * intros; repeat rewrite bhtower_index_zero.
      apply normal_increasing; auto.
    * hnf; simpl; intros.
      rewrite bhtower_index_zero.
      transitivity (supOrd (fun (i:A) => f (f0 i))).
      apply normal_continuous; auto.
      apply sup_ord_le_morphism.
      intro i.
      rewrite bhtower_index_zero. auto with ord.
    * intros. rewrite bhtower_index_zero.
      apply normal_complete; auto.
    * intros. rewrite bhtower_index_zero.
      apply normal_nonzero; auto.
  - hnf; simpl; intros.
    rewrite bhtower_index_zero.
    rewrite <- (sup_le _ _ a0).
    rewrite bhtower_index_zero.
    auto with ord.
  - apply bhtower_S_normal; auto.
    intros. apply IHn; auto.
  - apply bhtower_S_continuous; auto.
Qed.

Theorem bhtower_normal :
  forall n f b,
    normal_function f ->
    complete b ->
    normal_function (bhtower n f b).
Proof.
  intros. apply bhtower_normal_and_continuous; auto.
Qed.

Theorem bhtower_first_normal :
  forall n f,
    normal_function f ->
    normal_function (fun b => bhtower (S n) f b 0).
Proof.
  intros. constructor.
  - intros. apply bhtower_monotone; auto with ord.
  - intros.
    rewrite (bhtower_unroll n f y).
    rewrite <- lub_le2.
    rewrite ord_lt_unfold in H1.
    destruct H1 as [q H1].
    rewrite <- (sup_le _ _ q).
    apply ord_lt_le_trans with
        (nextCritical n (bhtower (S n) f (sz q)) (1 + 0) 0).
    rewrite <- nextCritical_fix; auto with ord.
    apply ord_le_lt_trans with (bhtower (S n) f q 0).
    apply bhtower_monotone; auto with ord.
    apply normal_increasing; auto with ord.
    apply bhtower_normal; auto.
    apply nextCritical_complete; auto.
    apply bhtower_normal; auto.
    apply bhtower_normal; auto.
    rewrite <- nextCritical_fix; auto with ord.
    apply bhtower_nonzero; auto.
    apply bhtower_normal; auto.
    apply bhtower_normal; auto.
    rewrite <- addOrd_le1; auto with ord.
    apply bhtower_normal; auto.
    apply bhtower_normal; auto.
    rewrite <- addOrd_le1; auto with ord.
    apply nextCritical_monotone; auto with ord.
  - apply bhtower_normal_and_continuous; auto.
  - intros. apply normal_complete; auto.
    apply bhtower_normal; auto.
  - intros. apply bhtower_nonzero; auto.
Qed.

Theorem bhtower_fixpoint :
  forall n f a b x,
    (0 < n)%nat ->
    normal_function f ->
    complete a ->
    complete b ->
    complete x ->
    a < b ->
    bhtower n f a (bhtower n f b x) ≈ bhtower n f b x.
Proof.
  intros.
  destruct n. inversion H.
  split.
  apply bhtower_S_fixpoint; auto.
  apply bhtower_normal; auto.
  apply normal_inflationary; auto.
  apply bhtower_normal; auto.
  apply normal_complete; auto.
  apply bhtower_normal; auto.
Qed.


Theorem bhtower_succ :
  forall n f b x,
    (n > 0)%nat ->
    normal_function f ->
    complete b ->
    complete x ->
    bhtower (S n) f (succOrd b) x ≈ bhtower n (bhtower (S n) f b) (1+x) 0.
Proof.
  intros n f b.
  induction x as [x Hx] using ordinal_induction.
  intros. split.
  - rewrite bhtower_unroll.
    apply lub_least.
    + transitivity (bhtower n (bhtower (S n) f b) 0 (bhtower n (bhtower (S n) f b) (1+x) 0)).
      rewrite bhtower_zero.
      rewrite bhtower_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      transitivity (1+x); auto with ord.
      apply addOrd_le2.
      apply (normal_inflationary (fun i => bhtower n (bhtower (S n) f b) i 0)).
      destruct n. inversion H.
      apply bhtower_first_normal.
      apply bhtower_normal; auto.
      auto with ord.
      apply bhtower_fixpoint; auto with ord.
      apply bhtower_normal; auto.
      rewrite <- addOrd_le1.
      auto with ord.
    + apply sup_least; simpl; intro.

      apply nextCritical_least; auto with ord.
      * intros. apply bhtower_normal; auto.
      * apply bhtower_normal; auto.
      * apply normal_complete; auto with ord.
        apply bhtower_normal; auto with ord.
        apply bhtower_normal; auto with ord.
      * rewrite ord_le_unfold; simpl; intro i.
        rewrite Hx; auto with ord.
        apply (normal_increasing (fun i => bhtower n (bhtower (S n) f b) i 0)).
        destruct n. inversion H.
        apply bhtower_first_normal.
        apply bhtower_normal; auto.
        auto with ord.
        apply addOrd_increasing; auto with ord.
      * intros.
        apply bhtower_fixpoint; auto with ord.
        apply bhtower_normal; auto.

  - destruct n. inversion H.
    rewrite bhtower_unroll.
    apply lub_least.
    apply bhtower_monotone; auto with ord.
    apply sup_least; intro a.
    rewrite (bhtower_unroll (S n) f (succOrd b) x).
    rewrite <- lub_le2.
    simpl.
    rewrite <- (sup_le _ _ tt).
    transitivity (nextCritical n (bhtower (S n) (bhtower (S (S n)) f b) (sz a)) 1 0).
    { apply nextCritical_monotone; auto with ord.
      rewrite addOrd_zero_r; auto with ord.
      rewrite ord_le_unfold; intros []. }
    unfold nextCritical at 1.
    apply sup_least; intro.
    destruct a0. simpl.
    apply normal_fix_least; auto with ord.
    + apply bhtower_normal; auto.
      apply bhtower_normal; auto.
      apply bhtower_normal; auto.
    + apply nextCritical_complete; auto with ord.
      intros; apply bhtower_normal; auto.
      intros; apply bhtower_normal; auto.
      apply lim_complete; auto.
      intros. apply normal_complete; auto.
      apply bhtower_normal; auto.
      apply directed_monotone; auto with ord.
      destruct x; apply H2.
    + rewrite bhtower_zero.
      apply nextCritical_critical; auto with ord.
      intros; apply bhtower_normal; auto.
      intros; apply bhtower_normal; auto.
      apply lim_complete; auto.
      intros. apply normal_complete; auto.
      apply bhtower_normal; auto.
      apply directed_monotone; auto with ord.
      destruct x; apply H2.
Qed.


Theorem bhtower_limit :
  forall n f b x,
    normal_function f ->
    complete b ->
    complete x ->
    limitOrdinal b ->
    bhtower (S n) f b x ≈ supOrd (fun a:b => bhtower (S n) f a (limOrd (fun i => bhtower (S n) f b (x i)))).
Proof.
  induction n; intros f b x Hf Hcb Hcx H.
  - rewrite bhtower_index_one; auto.
    rewrite veblen_unroll.
    split; auto with ord.
    + apply lub_least.
      * rewrite ord_isLimit in H; destruct H as [H0 Hlim].
        rewrite ord_lt_unfold in H0. destruct H0 as [b0 ?].
        destruct b as [B g]. simpl in *.
        rewrite <- (sup_le _ _ b0).
        rewrite bhtower_index_one.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite ord_le_unfold. intro q.
        rewrite ord_lt_unfold. exists q. simpl.
        apply normal_inflationary; auto with ord.
        apply bhtower_normal; auto.
        auto.
      * destruct b as [B g]; simpl.
        apply sup_least; intro i.
        destruct H as [Hz Hlim].
        destruct (Hlim i) as [i' ?].
        rewrite <- (sup_le _ _ i').
        rewrite bhtower_index_one; auto.
        assert (Hlemma : complete (limOrd (fun i0 : x => bhtower 1 f (ord B g) (x i0)))).
        { apply lim_complete.
          - intros; apply normal_complete; auto with ord.
            apply bhtower_normal; auto.
          - apply directed_monotone; auto.
            intros; apply bhtower_monotone; auto with ord.
          - destruct x; hnf in Hcx; intuition.
        }
        apply normal_fix_least; auto with ord.
        ** apply veblen_normal; auto with ord.
           hnf in Hcb; intuition.
        ** apply veblen_complete; auto.
           hnf in Hcb; intuition.
        ** rewrite ord_le_unfold; simpl; intro q.
           apply ord_lt_le_trans with (limOrd (fun i0 : x => bhtower 1 f (ord B g) (x i0))).
           { rewrite ord_lt_unfold. simpl. exists q.
             rewrite bhtower_index_one. auto with ord. auto. }
           apply normal_inflationary; auto with ord.
           apply veblen_normal; auto with ord.
           hnf in Hcb; intuition.
        ** apply veblen_fixpoints; auto with ord.
           hnf in Hcb; intuition.
           hnf in Hcb; intuition.

    + apply sup_least; intro a.
      rewrite bhtower_index_one; auto.
      rewrite <- lub_le2.
      destruct b as [B g]; simpl in *.
      rewrite <- (sup_le _ _ a).
      rewrite normal_fixpoint; auto with ord.
      apply veblen_monotone; auto.
      rewrite <- fixOrd_above.
      rewrite ord_le_unfold; simpl; intro i.
      rewrite ord_lt_unfold; simpl; exists i.
      rewrite bhtower_index_one; auto with ord.
      apply veblen_normal; auto. intuition.
      { apply lim_complete.
        - intros; apply normal_complete; auto with ord.
          apply veblen_normal; auto.
        - apply directed_monotone; auto.
          intros; apply veblen_monotone; auto with ord.
        - destruct x; hnf in Hcx; intuition.
      }

  - split.
    + rewrite bhtower_unroll.
      apply lub_least.
      * rewrite ord_isLimit in H. destruct H as [Hz Hlim].
        rewrite ord_lt_unfold in Hz. destruct Hz as [b0 _].
        rewrite <- (sup_le _ _ b0).
        rewrite bhtower_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite ord_le_unfold; intro i.
        rewrite ord_lt_unfold; exists i. simpl.
        apply normal_inflationary; auto with ord.
        apply bhtower_normal; auto with ord.
      * apply sup_least; intro a.
        destruct b as [B g]; simpl in *.
        destruct H as [Hz Hlim].
        destruct (Hlim a) as [a' Ha']; auto.
        rewrite <- (sup_le _ _ a').
        rewrite bhtower_unroll.
        rewrite <- lub_le2.
        rewrite ord_lt_unfold in Ha'.
        destruct Ha' as [q Hq].
        rewrite <- (sup_le _ _ q).
        simpl.
        apply nextCritical_monotone; auto with ord.
        ** apply addOrd_monotone; auto with ord.
           rewrite ord_le_unfold; intro i.
           rewrite ord_lt_unfold; exists i; simpl.
           apply normal_inflationary; auto with ord.
           apply bhtower_normal; auto.
        ** rewrite ord_le_unfold; intro i.
           rewrite ord_lt_unfold; exists i; simpl.
           apply bhtower_fixpoint; auto with ord arith.
           intuition.
    + apply sup_least; intro a.
      rewrite (bhtower_unroll (S n) f b x).
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ a).
      rewrite <- (nextCritical_fix); auto with ord.
      * apply normal_monotone; auto with ord.
        apply bhtower_normal; auto.
        apply nextCritical_above.
        rewrite <- addOrd_le1.
        auto with ord.
      * intros; apply bhtower_normal; auto.
      * apply bhtower_normal; auto.
      * apply lim_complete; auto with ord.
        ** intros; apply normal_complete; auto with ord.
           apply bhtower_normal; auto.
        ** apply directed_monotone; auto.
           intros; apply bhtower_monotone; auto with ord.
        ** destruct x; hnf in Hcx; intuition.
      * rewrite <- addOrd_le1.
        auto with ord.
Qed.


Lemma bhtower_one :
  forall n f x,
    (n > 0)%nat ->
    normal_function f ->
    complete x ->
    bhtower (S n) f 1 x ≈ bhtower n f (1+x) 0.
Proof.
  intros.
  rewrite bhtower_succ; auto.
  split; apply bhtower_monotone; auto with ord.
  intros. rewrite bhtower_zero. auto with ord.
  intros. rewrite bhtower_zero. auto with ord.
Qed.


Lemma bhtower_one_zero_step :
  forall n f,
    (n > 0)%nat ->
    normal_function f ->
    bhtower (S n) f 1 0 ≈ bhtower n f 1 0.
Proof.
  intros.
  rewrite bhtower_one; auto.
  split; apply bhtower_monotone; auto with ord.
  rewrite addOrd_zero_r; auto with ord.
  rewrite addOrd_zero_r; auto with ord.
Qed.

Lemma bhtower_one_zero :
  forall n f,
    normal_function f ->
    bhtower (S n) f 1 0 ≈ fixOrd f 0.
Proof.
  intros. transitivity (veblen f 1 0).
  induction n.
  apply bhtower_index_one; auto.
  rewrite bhtower_one_zero_step; auto.
  lia.
  rewrite veblen_succ; auto with ord.
  rewrite enum_fixpoints_zero.
  split; apply fixOrd_monotone_func; auto with ord.
  intros. rewrite veblen_zero; auto with ord.
  intros. rewrite veblen_zero; auto with ord.
  intros; apply veblen_monotone; auto with ord.
  apply veblen_normal; auto with ord.
Qed.


Theorem bhtower_succ_zero :
  forall n f b,
    (n > 0)%nat ->
    normal_function f ->
    complete b ->
    bhtower (S n) f (succOrd b) 0 ≈ fixOrd (bhtower (S n) f b) 0.
Proof.
  intros.
  rewrite bhtower_succ; auto.
  transitivity (bhtower n (bhtower (S n) f b) 1 0).
  { split; apply bhtower_monotone; auto with ord;
      rewrite addOrd_zero_r; auto with ord. }
  destruct n. inversion H.
  apply bhtower_one_zero.
  apply bhtower_normal; auto.
Qed.

Lemma bhtower_index_two :
  forall f b x,
    normal_function f ->
    complete b ->
    complete x ->
    bhtower 2 f b x ≈ vtower f b x.
Proof.
  intro f.
  induction b using ordinal_induction.
  induction x using ordinal_induction.
  intros.

  rewrite bhtower_unroll.
  rewrite vtower_unroll.
  apply ord_lub_eq_mor; auto with ord.
  apply sup_ord_eq_morphism.
  hnf; intro i.
  unfold VTower.nextCritical.
  unfold nextCritical.
  apply sup_ord_eq_morphism.
  hnf; intro z.
  transitivity
    (fixOrd (bhtower 1 (bhtower 2 f (sz i)) (sz z))
      (limOrd (fun x0 : x => vtower f b (sz x0)))).
  split; apply fixOrd_monotone; auto with ord.
  apply lim_ord_le_morphism. intro j.
  apply H0; auto with ord.
  apply lim_ord_le_morphism. intro j.
  apply H0; auto with ord.

  unfold fixOrd.
  apply sup_ord_eq_morphism.
  intro m.
  induction m; simpl iter_f; auto with ord.
  rewrite bhtower_index_one; auto.
  transitivity
    (veblen (vtower f (sz i)) (sz z)
            (iter_f (bhtower 1 (bhtower 2 f (sz i)) (sz z))
                    (limOrd (fun x0 : x => vtower f b (sz x0))) m)).
  split; apply veblen_monotone_func; auto with ord.
  apply bhtower_normal; auto.
  apply vtower_normal; auto.
  intros. apply H; auto with ord.
  apply iter_f_complete; auto with ord.
  { apply lim_complete; auto.
    intro. apply normal_complete; auto.
    apply vtower_normal; auto.
    apply directed_monotone; auto with ord.
    intros; apply vtower_monotone; auto with ord.
    destruct x; apply H3. }
  intros. apply normal_complete; auto with ord.
  apply bhtower_normal; auto.
  apply bhtower_normal; auto.
  apply vtower_normal; auto.
  apply bhtower_normal; auto.
  intros.
  apply H; auto with ord.
  apply iter_f_complete; auto with ord.
  { apply lim_complete; auto.
    intro. apply normal_complete; auto.
    apply vtower_normal; auto.
    apply directed_monotone; auto with ord.
    intros; apply vtower_monotone; auto with ord.
    destruct x; apply H3. }
  intros. apply normal_complete; auto with ord.
  apply bhtower_normal; auto.
  apply bhtower_normal; auto.

  apply veblen_eq_mor; auto with ord.
  intros. apply vtower_monotone; auto with ord.
  apply bhtower_normal; auto.
Qed.

