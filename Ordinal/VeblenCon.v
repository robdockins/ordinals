Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.

(** We say that a function is Scott continuous if it
    preserves all nonempty directed suprema of complete ordinals. *)
Definition scott_continuous (s:Ord -> Ord) :=
  forall A (f:A -> Ord) (a0:A),
    directed A f ->
    (forall a, complete (f a)) ->
    s (supOrd f) ≤ supOrd (fun i:A => s (f i)).

Record normal_function (f:Ord -> Ord) :=
  NormalFunction
  { normal_monotone   : forall x y, x ≤ y -> f x ≤ f y
  ; normal_increasing : forall x y, complete y -> x < y -> f x < f y
  ; normal_continuous : scott_continuous f
  ; normal_complete   : forall x, complete x -> complete (f x)
  ; normal_nonzero    : forall x, 0 < f x
  }.

Lemma normal_inflationary (f:Ord -> Ord) :
  normal_function f ->
  forall x, complete x -> x <= f x.
Proof.
  intro H.
  induction x as [X g Hx]. intro Hc.
  rewrite ord_le_unfold; intro x; simpl.
  rewrite (Hx x).
  * apply normal_increasing; auto.
    apply (limit_lt (ord X g)).
  * apply Hc.
Qed.

(* We say a function f enumerates a class of ordinals P if
   f x is the least element of P that is strictly above
   all f y for y < x. *)
Record enumerates (f:Ord -> Ord) (P:Ord -> Prop) : Prop :=
  Enumerates
    { enumerates_included   : forall x, complete x -> P (f x);
      enumerates_monotone   : forall x y, x ≤ y -> f x ≤ f y;
      enumerates_increasing : forall x y, complete y -> x < y -> f x < f y;
      enumerates_least      : forall x z, complete x -> complete z ->
                                          P z -> (forall y, y < x -> f y < z) -> f x ≤ z
    }.

(* We say x is a critical ordinal for β when
   x is a fixpoint for (veblen α) whenever α < β.
 *)
Definition critical_ordinal f (β:Ord) (x:Ord) : Prop :=
  forall α, complete α -> α < β -> x ≈ veblen f α x.

Definition strongly_critical_ordinal f (β:Ord) : Prop :=
  β > 0 /\ complete β /\ critical_ordinal f β β.

(** * Fixpoints of normal functions *)
Section normal_fixpoints.
  Variable f : Ord -> Ord.

  Lemma fixOrd_continuous :
    (forall x y, x <= y -> f x <= f y) ->
    (forall x, complete x -> complete (f x)) ->
    scott_continuous f ->
    scott_continuous (fixOrd f).
  Proof.
    red; simpl; intros Hf1 Hf2 Hf3 A g a0 Hd Hg.
    unfold fixOrd at 1.
    apply sup_least. intro i.
    apply ord_le_trans with (supOrd (fun a => iter_f f (g a) i)).
    - induction i.
      + simpl. reflexivity.
      + simpl.
        eapply ord_le_trans.
        * apply Hf1. apply IHi.
        * apply Hf3; auto.
          intros a1 a2.
          destruct (Hd a1 a2) as [a' [Ha1 Ha2]].
          exists a'. split; apply iter_f_monotone; auto.
          intros. apply iter_f_complete; auto.
    - apply sup_least. intro a.
      rewrite <- (sup_le _ _ a).
      unfold fixOrd.
      apply sup_le.
  Qed.

  Lemma directed_iter_f base :
    (forall x, complete x -> x <= f x) ->
    (forall x y, x <= y -> f x <= f y) ->
    (forall x, complete x -> complete (f x)) ->
    complete base ->
    directed nat (iter_f f base).
  Proof.
    intros. intros i j. exists (Nat.max i j).
    split; apply iter_f_index_monotone; auto.
    + apply PeanoNat.Nat.le_max_l.
    + apply PeanoNat.Nat.le_max_r.
  Qed.

  Lemma normal_fix_complete base :
    complete base ->
    (forall x, complete x -> x <= f x) ->
    (forall x y, x <= y -> f x <= f y) ->
    (forall x, complete x -> complete (f x)) ->
    complete (fixOrd f base).
  Proof.
    intros Hbase Hf1 Hf2 Hf3.
    unfold fixOrd.
    apply sup_complete; auto.
    - intros; apply iter_f_complete; auto.
    - apply directed_iter_f; auto.
    - assert (Hc' : complete (f base)).
      { apply Hf3; auto. }
      destruct (complete_zeroDec base Hbase).
      + destruct (complete_zeroDec (f base) Hc').
        * right. intro i.
          revert H H0. clear -Hf1 Hf2 Hbase. revert base Hbase.
          induction i; simpl; intros; auto.
          transitivity (f base); auto.
          apply Hf2; auto.
          rewrite IHi; auto.
          apply zero_least.
        * left.
          exists 1%nat. simpl.
          auto.
      + left.
        exists 0%nat. simpl. auto.
  Qed.

  Hypothesis Hnormal : normal_function f.

  Lemma normal_prefixpoint : forall base, complete base -> f (fixOrd f base) ≤ fixOrd f base.
  Proof.
    intros.
    apply ord_le_trans with (supOrd (fun i => f (iter_f f base i))).
    - apply (normal_continuous _ Hnormal nat (iter_f f base) 0%nat).
      apply directed_iter_f; auto.
      apply normal_inflationary; auto.
      apply normal_monotone; auto.
      apply normal_complete; auto.
      intro i; apply iter_f_complete; auto.
      apply normal_complete; auto.
    - apply sup_least. intro i.
      unfold fixOrd.
      apply (sup_le _ (iter_f f base) (S i)).
  Qed.

  Lemma normal_fixpoint : forall base, complete base -> fixOrd f base ≈ f (fixOrd f base).
  Proof.
    intros; split.
    - apply normal_inflationary; auto.
      apply normal_fix_complete; auto.
      + apply normal_inflationary; auto.
      + apply normal_monotone; auto.
      + apply normal_complete; auto.
    - apply normal_prefixpoint; auto.
  Qed.

  Lemma normal_fix_least : forall base z, complete z -> base ≤ z -> f z ≤ z -> fixOrd f base ≤ z.
  Proof.
    intros.
    unfold fixOrd.
    apply sup_least.
    intro i; induction i; simpl; auto.
    apply ord_le_trans with (f z); auto.
    apply normal_monotone; auto.
  Qed.

End normal_fixpoints.

Add Parametric Morphism f (Hf:normal_function f) : (fixOrd f)
  with signature ord_le ++> ord_le as normal_fix_le_mor.
Proof.
  apply fixOrd_monotone; auto.
  apply normal_monotone; auto.
Qed.

Add Parametric Morphism f (Hf:normal_function f) : (fixOrd f)
  with signature ord_eq ==> ord_eq as normal_fix_eq_mor.
Proof.
  unfold ord_eq; intuition; apply fixOrd_monotone; auto;
      apply normal_monotone; auto.
Qed.

Lemma powOmega_normal : normal_function powOmega.
Proof.
  apply NormalFunction.
  + apply expOrd_monotone.
  + intros; apply powOmega_increasing; auto.
  + red; intros A f a0 Hd Hc; apply (expOrd_continuous ω A f a0).
  + unfold powOmega. intros; apply expOrd_complete; auto.
    * apply (index_lt ω 0%nat).
    * apply omega_complete.
  + unfold powOmega. intros.
    apply expOrd_nonzero.
Qed.

Lemma enum_are_fixpoints f :
  normal_function f ->
  forall x, complete x -> enum_fixpoints f x ≈ f (enum_fixpoints f x).
Proof.
  intros Hf x Hc.
  destruct x as [X g]; simpl.
  apply normal_fixpoint; auto.
  apply lim_complete.
  - intros. apply enum_fixpoints_complete; auto.
    + apply normal_inflationary; auto.
    + apply normal_monotone; auto.
    + apply normal_complete; auto.
    + apply Hc.
  - intros b1 b2. destruct (complete_directed _ Hc b1 b2) as [b' [Hb1 HB2]].
    exists b'. split; apply enum_fixpoints_monotone; auto.
    apply normal_monotone; auto.
    apply normal_monotone; auto.
  - apply Hc.
Qed.

Lemma enum_fixpoints_zero f :
  normal_function f ->
  enum_fixpoints f zeroOrd ≈ fixOrd f zeroOrd.
Proof.
  simpl.
  split; apply fixOrd_monotone; auto.
  - apply normal_monotone; auto.
  - rewrite ord_le_unfold; simpl; intuition.
  - apply normal_monotone; auto.
  - rewrite ord_le_unfold; simpl; intuition.
Qed.

Lemma enum_fixpoints_succ f x :
  enum_fixpoints f (succOrd x) ≈ fixOrd f (succOrd (enum_fixpoints f x)).
Proof.
  simpl; intros. reflexivity.
Qed.

Lemma enum_fixpoints_cont f :
  normal_function f ->
  scott_continuous (enum_fixpoints f).
Proof.
  intros Hf A g a0 Hd Hc.
  simpl.
  apply normal_fix_least; auto.
  - apply sup_complete.
    + intros; apply enum_fixpoints_complete; auto.
      * apply normal_inflationary; auto.
      * apply normal_monotone; auto.
      * apply normal_complete; auto.
    + intros a1 a2. destruct (Hd a1 a2) as [a' [Ha1 Ha2]].
      exists a'.
      split; apply enum_fixpoints_monotone; auto.
      apply normal_monotone; auto.
      apply normal_monotone; auto.
    + left. exists a0.
      rewrite enum_are_fixpoints; auto.
      apply normal_nonzero; auto.
  - rewrite ord_le_unfold.
    simpl.
    intros [a i]. simpl.
    rewrite <- (sup_le _ _ a).
    apply enum_fixpoints_increasing; auto with ord.
    apply normal_monotone; auto.
  - rewrite (normal_continuous f Hf A (fun i => enum_fixpoints f (g i)) a0).
    + apply sup_least. simpl; intros.
      rewrite <- enum_are_fixpoints; auto.
      rewrite <- (sup_le _ _ a).
      auto with ord.
    + intros a1 a2. destruct (Hd a1 a2) as [a' [??]].
      exists a'. split; apply enum_fixpoints_monotone; auto.
      apply normal_monotone; auto.
      apply normal_monotone; auto.
    + intro; apply enum_fixpoints_complete; auto.
      * apply normal_inflationary; auto.
      * apply normal_monotone; auto.
      * apply normal_complete; auto.
Qed.

Lemma enum_fixpoints_normal f :
  normal_function f ->
  normal_function (enum_fixpoints f).
Proof.
  intros; constructor.
  - apply enum_fixpoints_monotone; auto.
    apply normal_monotone; auto.
  - intros; apply enum_fixpoints_increasing; auto.
    apply normal_monotone; auto.
  - apply enum_fixpoints_cont; auto.
  - apply enum_fixpoints_complete; auto.
    + apply normal_inflationary; auto.
    + apply normal_monotone; auto.
    + apply normal_complete; auto.
  - intros.
    destruct x as [X g].
    simpl.
    unfold fixOrd.
    rewrite <- (sup_le _ _ 1%nat).
    simpl.
    apply normal_nonzero; auto.
Qed.

Lemma enum_least f :
  normal_function f ->
  forall (x z:Ord),
    complete z ->
    f z ≤ z ->
    (forall x', x' < x -> enum_fixpoints f x' < z) ->
    enum_fixpoints f x ≤ z.
Proof.
  intro Hf.
  induction x as [B g Hx]. simpl; intros.
  apply normal_fix_least; auto.
  rewrite ord_le_unfold; simpl; intros.
  apply H1.
  apply limit_lt.
Qed.

Lemma enum_fixpoints_func_mono f g
      (Hf: normal_function f)
      (Hg: normal_function g) :
  (forall x, f x ≤ g x) ->
  (forall x, enum_fixpoints f x ≤ enum_fixpoints g x).
Proof.
  intros.
  induction x as [A q Hx]; simpl.
  unfold fixOrd.
  apply sup_ord_le_morphism. intro i.
  transitivity (iter_f f (ord A (fun b : A => enum_fixpoints g (q b))) i).
  - apply iter_f_monotone; auto.
    apply normal_monotone; auto.
    rewrite ord_le_unfold; simpl; intro a.
    rewrite ord_lt_unfold; simpl; exists a.
    auto.
  - apply iter_f_monotone_func; auto.
    apply normal_monotone; auto.
Qed.

Add Parametric Morphism f (Hf:normal_function f) : (enum_fixpoints f)
  with signature ord_le ++> ord_le  as enum_fixpoint_le_mor.
Proof.
  apply enum_fixpoints_monotone; auto.
  apply normal_monotone. auto.
Qed.

Add Parametric Morphism f (Hf:normal_function f) : (enum_fixpoints f)
  with signature ord_eq ==> ord_eq  as enum_fixpoint_eq_mor.
Proof.
  unfold ord_eq; intuition; apply enum_fixpoints_monotone; auto.
  apply normal_monotone. auto.
  apply normal_monotone. auto.
Qed.



Section veblen.
  Variable f : Ord -> Ord.
  Hypothesis f_normal : normal_function f.

  Lemma veblen_nonzero (β:Ord) (y:Ord) :
    0 < veblen f β y.
  Proof.
    rewrite veblen_unroll.
    rewrite <- lub_le1.
    apply normal_nonzero; auto.
  Qed.

  Lemma veblen_unroll_nonzero (β:Ord) (y:Ord) : complete y ->
    zeroOrd < β -> veblen f β y ≈ boundedSup β (fun α => fixOrd (veblen f α) (limOrd (fun x => veblen f β (y x)))).
  Proof.
    destruct β as [B g].
    intros Hc H; split.
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb]. simpl in *.
    - rewrite veblen_unroll.
      apply lub_least.
      + simpl.
        rewrite <- (sup_le _ _ b).
        unfold fixOrd.
        rewrite <- (sup_le _ _ 1%nat).
        simpl.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        destruct y as [Y h]. simpl.
        rewrite ord_le_unfold.
        simpl; intro q.
        rewrite ord_lt_unfold. simpl.
        exists q.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_inflationary; auto.
        apply Hc.
      + reflexivity.
    - rewrite veblen_unroll.
      apply lub_le2.
  Qed.

  Lemma veblen_inflationary (β:Ord) : forall x, complete x -> x ≤ veblen f β x.
  Proof.
    intro x.
    rewrite veblen_unroll.
    rewrite <- lub_le1.
    apply normal_inflationary. auto.
  Qed.

  Lemma veblen_complete :
    (forall x, complete x -> complete (f x)) ->
    forall β, complete β -> forall x, complete x -> complete (veblen f β x).
  Proof.
    intro Hf.
    induction β as [B g Hβ]; intro Hc1.
    induction x as [X h Hx]; intro Hc2.
    rewrite veblen_unroll.
    unfold boundedSup.
    assert (Hsup : complete (supOrd
         (fun i : B =>
          fixOrd (veblen f (g i))
            (limOrd (fun x : ord X h => veblen f (ord B g) (ord X h x)))))).
    { destruct Hc2 as [H1 [H2 H3]].
      apply sup_complete.
      - intro b. apply normal_fix_complete.
        + simpl. repeat split; auto.
          intros x1 x2. destruct (H1 x1 x2) as [x' [Hx'1 Hx'2]].
          exists x'. split; apply veblen_monotone; auto.
          apply normal_monotone; auto.
          apply normal_monotone; auto.
        + intros; apply veblen_inflationary; auto.
        + apply veblen_monotone.
          apply normal_monotone; auto.
        + simpl; intros.
          apply Hβ; auto.
          apply Hc1.
      - intros b1 b2.
        destruct Hc1 as [Hc1 [Hc2 Hc3]].
        destruct (Hc1 b1 b2) as [b' [Hb1 Hb2]].
        exists b'; simpl.
        split; unfold fixOrd; apply sup_ord_le_morphism; intro i;
          apply iter_f_monotone_func; auto.
        + intros; apply veblen_monotone_first; auto.
          apply normal_monotone; auto.
        + intros; apply veblen_monotone; auto.
          apply normal_monotone; auto.
        + intros; apply veblen_monotone_first; auto.
          apply normal_monotone; auto.
        + intros; apply veblen_monotone; auto.
          apply normal_monotone; auto.
      - destruct Hc1 as [Hc1 [Hc2 Hc3]].
        destruct Hc2 as [[b]|Hc2].
        + left. exists b.
          unfold fixOrd.
          rewrite <- (sup_le _ _ 1%nat); simpl.
          rewrite veblen_unroll.
          rewrite <- lub_le1.
          apply ord_lt_le_trans with (f 0); auto.
          apply normal_nonzero; auto.
          apply normal_monotone; auto.
          apply zero_least.
        + right. intro b. elim Hc2. exact (inhabits b).
    }
    destruct (complete_zeroDec _ Hc1).
    - apply lub_complete1; auto.
      apply sup_least; intro b.
      destruct (ord_le_subord _ _ H b) as [[] _].
    - apply lub_complete2; auto.
      rewrite ord_lt_unfold in H.
      destruct H as [b _].
      rewrite <- (sup_le _ _ b).
      unfold fixOrd.
      rewrite <- (sup_le _ _ 1%nat); simpl.
      rewrite veblen_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      rewrite ord_le_unfold; intro x; simpl.
      rewrite ord_lt_unfold; exists x. simpl.
      apply veblen_inflationary.
      apply Hc2.
  Qed.

  Lemma veblen_increasing0 : forall x y, complete y -> x < y -> veblen f 0 x < veblen f 0 y.
  Proof.
    intros.
    apply ord_le_lt_trans with (f x).
    { rewrite veblen_unroll.
      apply lub_least; auto with ord.
      apply boundedSup_least. simpl; intros.
      elim (ord_lt_irreflexive zeroOrd).
      apply ord_le_lt_trans with x0; auto.
      apply zero_least. }
    apply ord_lt_le_trans with (f y).
    apply normal_increasing; auto.
    rewrite veblen_unroll.
    apply lub_le1.
  Qed.

  Lemma veblen_increasing_nonzero (β:Ord) : 0 < β -> forall x y, x < y -> veblen f β x < veblen f β y.
  Proof.
    intros.
    rewrite (veblen_unroll f β y).
    rewrite <- lub_le2.
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb].
    destruct β as [B g]. simpl.
    rewrite <- (sup_le _ _ b).
    unfold fixOrd.
    rewrite <- (sup_le _ _ 0%nat).
    simpl.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [q Hq].
    rewrite ord_lt_unfold. simpl.
    exists q.
    apply veblen_monotone; auto.
    apply normal_monotone; auto.
  Qed.

  Lemma veblen_increasing (β:Ord) :
    complete β ->
    forall x y, complete y -> x < y -> veblen f β x < veblen f β y.
  Proof.
    intro Hβ.
    destruct (complete_zeroDec β); auto.
    - intros.
      apply ord_le_lt_trans with (veblen f 0 x).
      apply veblen_monotone_first; auto.
      apply normal_monotone; auto.
      apply ord_lt_le_trans with (veblen f 0 y).
      apply veblen_increasing0; auto.
      apply veblen_monotone_first; auto.
      apply normal_monotone; auto.
      apply zero_least.
    - intros. apply veblen_increasing_nonzero; auto.
  Qed.

  Lemma veblen_lt_lemma β : zeroOrd < β -> forall x q,
     complete x ->
     q < veblen f β x ->
     exists a, a < β /\ exists n,
         q < iter_f (veblen f a) (limOrd (fun i => veblen f β (x i))) n.
  Proof.
    intros Hb x q Hc H.
    rewrite veblen_unroll_nonzero in H; auto.
    destruct β as [B g]. simpl in H.
    rewrite ord_lt_unfold in H.
    simpl in H.
    destruct H as [[b [n z]] Hq].
    simpl in *.
    exists (g b). split; [ apply (index_lt (ord B g)) | ].
    exists n.
    rewrite ord_lt_unfold. simpl. exists z. auto.
  Qed.

  Lemma veblen_fixpoints_aux (β:Ord) (Hcomplete : complete β) :
      (forall y, y < β -> complete y -> scott_continuous (veblen f y)) ->
      forall α x, α < β -> complete α -> complete x -> veblen f α (veblen f β x) ≤ veblen f β x.
  Proof.
    intros Hcont a x H Hac Hxc.
    rewrite (veblen_unroll f a).
    apply lub_least.
    - transitivity (f (boundedSup β (fun α => fixOrd (veblen f α) (limOrd (fun i => veblen f β (x i)))))).
      + apply normal_monotone; auto.
        rewrite (veblen_unroll_nonzero); auto. reflexivity.
        apply ord_le_lt_trans with a; auto. apply zero_least.
      + rewrite (veblen_unroll_nonzero); auto.
        2: { apply ord_le_lt_trans with a; auto. apply zero_least. }
        destruct β as [B g]. simpl.
        rewrite ord_lt_unfold in H.
        destruct H as [b Hb].
        rewrite (normal_continuous f f_normal B _ b).
        * apply sup_least; intro i.
          rewrite <- (sup_le _ _ i).
          transitivity (veblen f (g i)
                               (fixOrd (veblen f (g i))
                                           (limOrd (fun i0 : x => veblen f (ord B g) (x i0))))).
          rewrite (veblen_unroll f (g i)).
          apply lub_le1.
          apply normal_prefixpoint.
          { constructor.
            + apply veblen_monotone.
              apply normal_monotone; auto.
            + apply veblen_increasing. apply Hcomplete.
            + apply Hcont. apply (index_lt (ord B g)).
              destruct Hcomplete as [?[??]]; auto.
            + intros; apply veblen_complete; auto.
              apply normal_complete; auto.
              apply Hcomplete.
            + intro; apply veblen_nonzero.
          }
          apply lim_complete.
          ** intro; apply veblen_complete; auto.
             apply normal_complete; auto.
             apply complete_subord; auto.
          ** intros x1 x2. destruct (complete_directed _ Hxc x1 x2) as [x' [Hx1 Hx2]].
             exists x'.
             split; apply veblen_monotone; auto.
             apply normal_monotone; auto.
             apply normal_monotone; auto.
          ** destruct x; apply Hxc.

        * intros b1 b2. destruct (complete_directed _ Hcomplete b1 b2) as [b' [Hb1 Hb2]].
          exists b'. split.
          ** unfold fixOrd. apply sup_ord_le_morphism.
             intro i. apply iter_f_monotone_func.
             *** intros; apply veblen_monotone_first; auto.
                 apply normal_monotone; auto.
             *** intros; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
          ** unfold fixOrd. apply sup_ord_le_morphism.
             intro i. apply iter_f_monotone_func.
             *** intros; apply veblen_monotone_first; auto.
                 apply normal_monotone; auto.
             *** intros; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
        * intro. apply normal_fix_complete; auto.
          ** apply lim_complete.
             *** intros; apply veblen_complete; auto.
                 apply normal_complete; auto.
                 apply complete_subord; auto.
             *** intros x1 x2. destruct (complete_directed _ Hxc x1 x2) as [x' [Hx1 Hx2]].
                 exists x'.
                 split; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
                 apply normal_monotone; auto.
             *** destruct x; apply Hxc.
          ** apply veblen_inflationary.
          ** apply veblen_monotone; auto.
             apply normal_monotone; auto.
          ** intros; apply veblen_complete; auto.
             apply normal_complete; auto.
             apply Hcomplete.

    - destruct a as [A g]. simpl.
      apply sup_least. intro y.
      rewrite (veblen_unroll f β) at 2.
      rewrite <- lub_le2.
      unfold fixOrd.
      apply sup_least.
      intro i.
      simpl.
      induction i; simpl.
      + apply limit_least. intro q.
        destruct (veblen_lt_lemma β) with x q as [a' [Ha' [n Hn]]]; auto.
        * apply ord_le_lt_trans with (ord A g); auto. apply zero_least.
        * apply index_lt.
        * assert (exists a2, a2 < β /\ ord A g <= a2 /\ a' <= a2).
          { destruct β as [B h].
            rewrite ord_lt_unfold in H.
            destruct H as [b1 Hb1].
            rewrite ord_lt_unfold in Ha'.
            destruct Ha' as [b2 Hb2].
            destruct (complete_directed _ Hcomplete b1 b2) as [b' [??]].
            exists (h b').
            split.
            apply (index_lt (ord B h)).
            split.
            simpl in *.
            transitivity (h b1); auto.
            transitivity (h b2); auto.
          }
          destruct H0 as [a2 [?[??]]].
          apply ord_lt_le_trans with (iter_f (veblen f a2) (limOrd (fun i => veblen f β (x i))) (S n)).
          ** simpl.
             apply ord_lt_le_trans with (veblen f (ord A g) (iter_f (veblen f a2) (limOrd (fun i => veblen f β (x i))) n)).
             *** apply veblen_increasing_nonzero; auto.
                 **** apply ord_le_lt_trans with (g y); [ apply zero_least | apply (index_lt (ord A g)) ].
                 **** eapply ord_lt_le_trans; [ apply Hn | ].
                      apply iter_f_monotone_func; intros;
                        [ apply veblen_monotone_first; auto
                        | apply veblen_monotone; auto ].
                 apply normal_monotone; auto.
                 apply normal_monotone; auto.
             *** apply veblen_monotone_first; auto.
                 apply normal_monotone; auto.
          ** transitivity (supOrd (iter_f (veblen f a2) (limOrd (fun x0 : x => veblen f β (x x0))))).
             *** apply sup_le.
             *** rewrite <- boundedSup_le.
                 **** reflexivity.
                 **** intros.
                      apply sup_ord_le_morphism.
                      hnf; simpl; intros.
                      { apply iter_f_monotone_func; intros.
                        - apply veblen_monotone_first; auto.
                          apply normal_monotone; auto.
                        - apply veblen_monotone; auto.
                          apply normal_monotone; auto.
                      }
                 **** auto.
      + transitivity
          (veblen f (g y) (boundedSup β
            (fun α : Ord =>
             supOrd
               (iter_f (veblen f α) (limOrd (fun x0 : x => veblen f β (x x0))))))).
        { apply veblen_monotone; auto. apply normal_monotone; auto. }
        destruct β as [B h].
        simpl.
        rewrite ord_lt_unfold in H.
        destruct H as [b Hb].
        simpl in *.
        assert (Hy' : g y < ord B h).
        { transitivity (ord A g) ; auto.
          apply (index_lt (ord A g)).
          rewrite ord_lt_unfold. exists b. auto.
        }
        assert (Hcy: complete (g y)).
        { destruct Hac as [?[??]]; auto. }
        rewrite (Hcont (g y) Hy' Hcy B _ b).
        * apply sup_least.
          intro b'.
          assert (exists b2, h b <= h b2 /\ h b' <= h b2).
          { destruct Hcomplete as [Hc ?].
            destruct (Hc b b'); auto.
          }
          destruct H as [b2 [??]].
          rewrite <- (sup_le _ _ b2).
          rewrite (Hcont (g y) Hy' Hcy nat _ 0%nat).
          ** apply sup_least.
             simpl; intro j.
             rewrite <- (sup_le _ _ (S j)).
             simpl.
             transitivity (veblen f (g y) (iter_f (veblen f (h b2)) (limOrd (fun x0 : x => veblen f (ord B h) (x x0))) j)).
             *** apply veblen_monotone.
                 apply normal_monotone; auto.
                 apply iter_f_monotone_func; intros.
                 **** apply veblen_monotone_first; auto.
                      apply normal_monotone; auto.
                 **** apply veblen_monotone; auto.
                      apply normal_monotone; auto.
             *** apply veblen_monotone_first.
                 apply normal_monotone; auto.
                 transitivity (ord A g); auto with ord.
                 transitivity (h b); auto.
          ** apply directed_iter_f.
             *** intros; apply veblen_inflationary; auto.
             *** intros; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
             *** intros; apply veblen_complete; auto.
                 apply normal_complete; auto.
                 apply Hcomplete.
             *** apply lim_complete.
                 **** intros; apply veblen_complete; auto.
                      apply normal_complete; auto.
                      apply complete_subord; auto.
                 **** intros x1 x2. destruct (complete_directed _ Hxc x1 x2) as [x' [Hx1 Hx2]].
                      exists x'.
                      split; apply veblen_monotone; auto.
                      apply normal_monotone; auto.
                      apply normal_monotone; auto.
                 **** destruct x; apply Hxc.
          ** intro j. apply iter_f_complete; auto.
             *** apply lim_complete.
                 **** intros; apply veblen_complete; auto.
                      apply normal_complete; auto.
                      apply complete_subord; auto.
                 **** intros x1 x2. destruct (complete_directed _ Hxc x1 x2) as [x' [Hx1 Hx2]].
                      exists x'.
                      split; apply veblen_monotone; auto.
                      apply normal_monotone; auto.
                      apply normal_monotone; auto.
                 **** destruct x; apply Hxc.
             *** intros; apply veblen_complete; auto.
                 apply normal_complete; auto.
                 apply Hcomplete.

        * intros b1 b2. destruct (complete_directed (ord B h) Hcomplete b1 b2) as [b' [Hb1 Hb2]].
          simpl in *.
          exists b'. split.
          ** apply sup_ord_le_morphism. intro j.
             apply iter_f_monotone_func.
             *** intros; apply veblen_monotone_first; auto.
                 apply normal_monotone; auto.
             *** intros; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
          ** apply sup_ord_le_morphism. intro j.
             apply iter_f_monotone_func.
             *** intros; apply veblen_monotone_first; auto.
                 apply normal_monotone; auto.
             *** intros; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
        * intro b'.
          apply sup_complete.
          ** intro j.
             apply iter_f_complete; auto.
             *** apply lim_complete.
                 **** intro; apply veblen_complete; auto.
                      apply normal_complete; auto.
                      apply complete_subord; auto.
                 **** intros x1 x2. destruct (complete_directed _ Hxc x1 x2) as [x' [Hx1 Hx2]].
                      exists x'.
                      split; apply veblen_monotone; auto.
                      apply normal_monotone; auto.
                      apply normal_monotone; auto.
                 **** destruct x; apply Hxc.
             *** intros; apply veblen_complete; auto.
                 apply normal_complete; auto.
                 apply Hcomplete.
          ** apply directed_iter_f.
             *** intros; apply veblen_inflationary; auto.
             *** apply veblen_monotone; auto.
                 apply normal_monotone; auto.
             *** apply veblen_complete; auto.
                 apply normal_complete; auto.
                 apply Hcomplete.
             *** apply lim_complete.
                 **** intro; apply veblen_complete; auto.
                      apply normal_complete; auto.
                      apply complete_subord; auto.
                 **** intros x1 x2. destruct (complete_directed _ Hxc x1 x2) as [x' [Hx1 Hx2]].
                      exists x'.
                      split; apply veblen_monotone; auto.
                      apply normal_monotone; auto.
                      apply normal_monotone; auto.
                 **** destruct x; apply Hxc.
          ** left. exists 1%nat. simpl.
             apply veblen_nonzero.
  Qed.

  Lemma veblen_continuous (β:Ord) : complete β -> scott_continuous (veblen f β).
  Proof.
    induction β as [β Hind] using ordinal_induction.
    intro Hc.
    destruct β as [A g]; simpl.
    hnf; intros X h x Hd Hh.
    rewrite veblen_unroll.
    apply lub_least.
    - rewrite (normal_continuous f f_normal X h x); auto.
      apply sup_ord_le_morphism.
      hnf; simpl; intros.
      rewrite veblen_unroll.
      rewrite <- lub_le1.
      reflexivity.
    - apply sup_least. intro a.
      apply normal_fix_least.
      + constructor.
        * apply veblen_monotone.
          apply normal_monotone; auto.
        * apply veblen_increasing. apply Hc.
        * apply Hind. apply (index_lt (ord A g)).
          apply Hc.
        * apply veblen_complete; auto.
          apply normal_complete; auto.
          apply Hc.
        * apply veblen_nonzero.
      + apply sup_complete.
        * intros; apply veblen_complete; auto.
          apply normal_complete; auto.
        * intros x1 x2. destruct (Hd x1 x2) as [x' [Hx1 Hx2]].
          exists x'. split; apply veblen_monotone; auto.
          apply normal_monotone; auto.
          apply normal_monotone; auto.
        * left. exists x.
          apply veblen_nonzero.
      + rewrite ord_le_unfold.
        rewrite sup_unfold. simpl.
        intros [x' y]. simpl.
        rewrite <- (sup_le _ _ x').
        apply veblen_increasing_nonzero.
        * rewrite ord_lt_unfold. exists a. apply zero_least.
        * apply index_lt.
      + assert (Hc' : complete (g a)).
        { apply Hc. }
        rewrite (Hind (g a) (index_lt (ord A g) a) Hc' X (fun i => veblen f (ord A g) (h i)) x).
        * apply sup_ord_le_morphism. hnf; simpl. intro x'.
          apply veblen_fixpoints_aux; auto.
          apply (index_lt (ord A g)).
        * intros x1 x2.
          destruct (Hd x1 x2) as [x' [??]].
          exists x'.
          split; apply veblen_monotone; auto.
          apply normal_monotone; auto.
          apply normal_monotone; auto.
        * intros; apply veblen_complete; auto.
          apply normal_complete; auto.
  Qed.

  Lemma veblen_fixpoints :
    forall α β x,
      complete α ->
      complete β ->
      complete x ->
      α < β ->
      veblen f α (veblen f β x) ≈ veblen f β x.
  Proof.
    intros; split.
    - apply veblen_fixpoints_aux; auto.
      intros. apply veblen_continuous; auto.
    - apply veblen_inflationary.
      apply veblen_complete; auto.
      apply normal_complete; auto.
  Qed.

  Lemma veblen_continuous_first : strongly_continuous (fun β => veblen f β 0).
  Proof.
    hnf; intros A g a.
    rewrite veblen_unroll.
    apply lub_least.
    - rewrite <- (sup_le _ _ a).
      rewrite veblen_unroll.
      apply lub_le1.
    - simpl.
      apply sup_least. intros [a' z]. simpl.
      rewrite <- (sup_le A (fun i => veblen f (g i) 0) a').
      rewrite veblen_unroll.
      rewrite <- lub_le2.
      destruct (g a') as [Q q]. simpl in *.
      rewrite <- (sup_le Q _ z).
      apply fixOrd_monotone; auto.
      apply veblen_monotone.
      apply normal_monotone; auto.
      rewrite ord_le_unfold.
      simpl; intros. elim a0.
  Qed.

  Lemma veblen_normal (β:Ord) : complete β -> normal_function (veblen f β).
  Proof.
    constructor.
    - apply veblen_monotone.
      apply normal_monotone; auto.
    - apply veblen_increasing; auto.
    - apply veblen_continuous; auto.
    - intros; apply veblen_complete; auto.
      apply normal_complete; auto.
    - apply veblen_nonzero.
  Qed.

  Lemma veblen_increasing_first :
    forall a β, complete β -> a < β -> veblen f a 0 < veblen f β 0.
  Proof.
    intros a β Hβ H.
    rewrite (veblen_unroll f β).
    rewrite <- lub_le2.
    destruct β as [B g].
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb].
    simpl.
    rewrite <- (sup_le _ _ b).
    apply ord_le_lt_trans with (veblen f (g b) zeroOrd).
    apply veblen_monotone_first; auto.
    apply normal_monotone; auto.
    unfold fixOrd.
    rewrite <- (sup_le _ _ 2%nat). simpl.
    apply veblen_increasing.
    - apply Hβ.
    - apply veblen_complete; auto.
      + apply normal_complete; auto.
      + apply Hβ.
      + apply lim_complete.
        * intros [].
        * intros [].
        * right; intros [[]].
    - apply veblen_nonzero.
  Qed.

  Lemma veblen_first_normal :
    normal_function (fun β => veblen f β 0).
  Proof.
    constructor.
    - intros; apply veblen_monotone_first; auto.
      apply normal_monotone; auto.
    - intros; apply veblen_increasing_first; auto.
    - hnf; intros.
      apply veblen_continuous_first; auto.
    - intros; apply veblen_complete; auto.
      apply normal_complete; auto.
      apply zero_complete.
    - intro; apply veblen_nonzero; auto.
  Qed.

  Lemma veblen_zero : forall x,
    veblen f 0 x ≈ f x.
  Proof.
    intro x.
    rewrite veblen_unroll. simpl.
    split.
    - apply lub_least; auto with ord.
      apply sup_least; simpl; intros.
      exfalso; auto.
    - apply lub_le1.
  Qed.

  Lemma veblen_succ : forall a x, complete a ->
    veblen f (succOrd a) x ≈ enum_fixpoints (veblen f a) x.
  Proof.
    intros a x Ha; induction x as [X g Hind].
    simpl.
    rewrite veblen_unroll.
    split.
    - simpl.
      apply lub_least.
      + unfold  fixOrd.
        rewrite <- (sup_le _ _ 1%nat). simpl.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite ord_le_unfold; simpl; intro x.
        rewrite ord_lt_unfold; simpl; exists x.
        apply increasing_inflationary.
        apply enum_fixpoints_increasing.
        apply veblen_normal; auto.
      + apply sup_least. intro.
        apply fixOrd_monotone.
        intros; apply veblen_monotone; auto.
        apply normal_monotone; auto.
        unfold limOrd.
        rewrite ord_le_unfold; simpl; intro x.
        rewrite ord_lt_unfold; simpl; exists x.
        apply Hind.
    - rewrite <- lub_le2.
      simpl.
      rewrite <- (sup_le _ _ tt).
      apply fixOrd_monotone.
      apply veblen_monotone.
      apply normal_monotone; auto.
      rewrite ord_le_unfold; simpl; intro x.
      rewrite ord_lt_unfold; simpl; exists x.
      apply Hind.
  Qed.

  Lemma veblen_limit_zero :
    forall β, limitOrdinal β -> complete β ->
      veblen f β 0 ≈ boundedSup β (fun a => veblen f a 0).
  Proof.
    intros.
    rewrite (veblen_unroll f β).
    split.
    - apply lub_least.
      + transitivity (veblen f zeroOrd zeroOrd).
        rewrite veblen_zero.
        reflexivity.
        destruct β as [B g]; simpl in *.
        destruct H as [[b] _].
        rewrite <- (sup_le _ _ b).
        apply veblen_monotone_first.
        apply normal_monotone; auto.
        apply zero_least.
      + destruct β as [B g]; simpl in *.
        apply sup_least; simpl; intro b.
        destruct H as [_ H].
        destruct (H b) as [b' Hb'].
        rewrite <- (sup_le _ _ b').
        unfold fixOrd.
        apply sup_least.
        intro i; induction i; simpl.
        * rewrite ord_le_unfold; simpl; intuition.
        * rewrite <- (veblen_fixpoints (g b) (g b')); auto.
          apply veblen_monotone; auto.
          apply normal_monotone; auto.
          destruct H0 as [?[??]]; auto.
          destruct H0 as [?[??]]; auto.
          apply zero_complete.
    - rewrite <- lub_le2.
      destruct β as [B g]; simpl in *.
      apply sup_least; simpl; intro i.
      rewrite <- (sup_le _ _ i).
      unfold fixOrd.
      rewrite <- (sup_le _ _ 1%nat).
      simpl.
      apply veblen_monotone.
      apply normal_monotone; auto.
      apply zero_least.
  Qed.

  Lemma veblen_limit_succ :
    forall β x, limitOrdinal β -> complete β -> complete x ->
      veblen f β (succOrd x) ≈ boundedSup β (fun a => veblen f a (succOrd (veblen f β x))).
  Proof.
    intros β x Hlim Hβ Hx.
    rewrite veblen_unroll.
    split.
    - apply lub_least.
      + destruct β as [B g]; simpl.
        destruct Hlim as [[b] _].
        rewrite <- (sup_le _ _ b).
        rewrite (veblen_unroll f (g b)).
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        apply succ_monotone.
        apply veblen_inflationary; auto.
      + destruct β as [B g]; simpl.
        apply sup_least; simpl; intro b.
        destruct Hlim as [_ H].
        destruct (H b) as [b' Hb'].
        rewrite <- (sup_le _ _ b').
        unfold fixOrd. apply sup_least.
        intro i; simpl.
        induction i; simpl.
        * rewrite ord_le_unfold; simpl; intro.
          apply ord_lt_le_trans with (succOrd (veblen f (ord B g) x)).
          rewrite ord_lt_unfold. exists tt; simpl.
          reflexivity.
          apply veblen_inflationary; auto.
          apply succ_complete.
          apply veblen_complete; auto.
          apply normal_complete; auto.

        * rewrite <- (veblen_fixpoints (g b) (g b')); auto.
          ** apply veblen_monotone; auto.
             apply normal_monotone; auto.
          ** apply Hβ.
          ** apply Hβ.
          ** apply succ_complete.
             apply veblen_complete; auto.
             apply normal_complete; auto.

    - destruct β as [B g]; simpl.
      apply sup_least; intro b.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ b).
      unfold fixOrd.
      rewrite <- (sup_le _ _ 1%nat).
      simpl.
      apply veblen_monotone.
      apply normal_monotone; auto.
      apply succ_least.
      rewrite ord_lt_unfold; exists tt. simpl.
      reflexivity.
  Qed.

  Lemma veblen_limit_limit :
    forall β x, limitOrdinal β -> limitOrdinal x -> complete β -> complete x ->
      veblen f β x ≈ boundedSup β (fun a => veblen f a (boundedSup x (fun y => veblen f β y))).
  Proof.
    intros β x Hlimβ Hlimx Hβ Hx.
    destruct β as [B g].
    destruct x as [X h]. simpl.
    rewrite veblen_unroll. simpl.
    split.
    - apply lub_least.
      + destruct Hlimβ as [[b] H].
        rewrite <- (sup_le _ _ b).
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite ord_le_unfold; simpl; intro x.
        destruct Hlimx as [_ H0].
        destruct (H0 x) as [x' Hx'].
        rewrite <- (sup_le _ _ x').
        apply ord_lt_le_trans with (h x'); auto.
        apply veblen_inflationary.
        apply Hx.
      + apply sup_least; intro b.
        destruct Hlimβ as [_ H].
        destruct (H b) as [b' Hb'].
        rewrite <- (sup_le _ _ b').
        unfold fixOrd.
        apply sup_least.
        simpl; intro i.
        induction i; simpl.
        * rewrite ord_le_unfold; simpl; intro x.
          rewrite <- (veblen_inflationary (g b')).
          ** destruct Hlimx as [_ H0].
             destruct (H0 x) as [x' Hx'].
             rewrite <- (sup_le _ _ x').
             apply veblen_increasing_nonzero; auto.
             apply ord_le_lt_trans with (g b'); auto.
             apply zero_least.
             apply (index_lt (ord B g)).
          ** apply sup_complete.
             *** intros; apply veblen_complete; auto.
                 apply normal_complete; auto.
                 apply Hx.
             *** intros x1 x2. destruct (complete_directed (ord X h) Hx x1 x2) as [x' [Hx1 Hx2]].
                 exists x'; split; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
                 apply normal_monotone; auto.
             *** left. exists x. apply veblen_nonzero.
        * rewrite <- (veblen_fixpoints (g b) (g b')); auto.
          ** apply veblen_monotone; auto.
             apply normal_monotone; auto.
          ** apply Hβ.
          ** apply Hβ.
          ** apply sup_complete.
             *** intros; apply veblen_complete; auto.
                 apply normal_complete; auto.
                 apply Hx.
             *** intros x1 x2. destruct (complete_directed (ord X h) Hx x1 x2) as [x' [Hx1 Hx2]].
                 exists x'; split; apply veblen_monotone; auto.
                 apply normal_monotone; auto.
                 apply normal_monotone; auto.
             *** destruct Hx as [Hx1 [Hx2 Hx3]].
                 destruct Hx2 as [[x]|Hx2].
                 **** left. exists x. apply veblen_nonzero.
                 **** right. intro x. elim Hx2. exact (inhabits x).
    - rewrite <- lub_le2.
      apply sup_least; intro b.
      rewrite <- (sup_le _ _ b).
      unfold fixOrd.
      rewrite <- (sup_le _ _ 1%nat); simpl.
      apply veblen_monotone.
      apply normal_monotone; auto.
      apply sup_least. intro x.
      apply ord_lt_le.
      rewrite ord_lt_unfold. simpl. exists x.
      reflexivity.
  Qed.

  Theorem veblen_enumerates_critical β :
    β > 0 -> complete β ->
    enumerates (veblen f β) (critical_ordinal f β).
  Proof.
    intros Hβ Hc.
    constructor.
    - intros x Hx. unfold critical_ordinal.
      intros. symmetry. apply veblen_fixpoints; auto.
    - intros; apply veblen_monotone; auto.
      apply normal_monotone; auto.
    - intros; apply veblen_increasing; auto.
    - intros x z Hx Hz Hz1 Hz2.
      rewrite veblen_unroll.
      apply lub_least.
      + generalize (Hz1 0 zero_complete Hβ).
        rewrite veblen_zero.
        intro.
        rewrite H.
        apply normal_monotone; auto.
        rewrite ord_le_unfold. intro a.
        apply ord_le_lt_trans with (veblen f β (x a)); auto.
        apply veblen_inflationary.
        apply complete_subord. auto.
        apply Hz2. apply index_lt.
      + destruct β as [B g]. simpl.
        apply sup_least; intro i.
        apply fixOrd_least.
        * apply veblen_monotone; auto.
          apply normal_monotone; auto.
        * rewrite ord_le_unfold; simpl.
          intro a.
          apply Hz2.
          apply index_lt.
        * apply Hz1. apply Hc.
          apply (index_lt (ord B g)); auto.
  Qed.

  Theorem strongly_critical_fixpoint β (Hc:complete β) :
    strongly_critical_ordinal f β <-> veblen f β 0 ≈ β.
  Proof.
    split; intro H.
    - destruct H as [Hβ [_ H]].
      split.
      + rewrite veblen_unroll.
        apply lub_least.
        * generalize (H 0 zero_complete Hβ).
          rewrite veblen_zero. intro.
          rewrite H0.
          apply normal_monotone; auto with ord.
        * destruct β as [B g]; simpl.
          apply sup_least. simpl; intro.
          apply fixOrd_least; auto.
          ** apply veblen_monotone; auto.
             apply normal_monotone; auto.
          ** rewrite ord_le_unfold. simpl; intro.
             elim a0.
          ** apply H.
             apply Hc.
             apply (index_lt (ord B g) a).
      + apply (normal_inflationary (fun x => veblen f x 0)); auto.
        apply veblen_first_normal; auto.
    - hnf. split; [ | split]; auto.
      + rewrite <- H. apply veblen_nonzero.
      + intros α Hca Hα.
        rewrite <- H at 1.
        transitivity (veblen f α (veblen f β 0)).
        symmetry. apply veblen_fixpoints; auto.
        apply zero_complete.
        split; apply veblen_monotone.
        apply normal_monotone; auto.
        apply H.
        apply normal_monotone; auto.
        apply H.
  Qed.

End veblen.


Lemma veblen_monotone_func f g :
  normal_function f ->
  normal_function g ->
  (forall i, complete i -> f i <= g i) ->
  forall a x, complete a -> complete x ->
    veblen f a x <= veblen g a x.
Proof.
  intros Hf Hg H.
  induction a as [A h Ha].
  induction x as [X k Hx].
  intros.
  do 2 rewrite veblen_unroll.
  apply lub_least.
  - rewrite <- lub_le1. apply H; auto.
  - simpl.
    apply sup_least; intro i.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    unfold fixOrd.
    apply sup_least; intro n.
    rewrite <- (sup_le _ _ n).
    transitivity (iter_f (veblen g (h i)) (limOrd (fun x0 : X => veblen f (ord A h) (k x0))) n).
    { induction n; simpl iter_f.
      reflexivity.
      transitivity
        (veblen g (h i)
                (iter_f (veblen f (h i)) (limOrd (fun x : X => veblen f (ord A h) (k x))) n)).
      apply (Ha i). apply H0.
      apply iter_f_complete.
      apply lim_complete; auto.
      intros; apply veblen_complete; auto.
      apply normal_complete; auto.
      apply H1.
      { red; intros. destruct (complete_directed (ord X k) H1 a1 a2) as [a' [??]].
        exists a'; split.
        apply veblen_monotone; auto.
        apply normal_monotone; auto.
        apply veblen_monotone; auto.
        apply normal_monotone; auto. }
      apply H1.
      intros; apply veblen_complete; auto.
      apply normal_complete; auto.
      apply H0.
      apply veblen_monotone; auto.
      apply normal_monotone; auto. }

    apply iter_f_monotone.
    intros; apply veblen_monotone; auto.
    apply normal_monotone; auto.
    rewrite ord_le_unfold; intro q. simpl.
    rewrite ord_lt_unfold; exists q; simpl.
    apply Hx; auto.
    apply H1.
Qed.




Lemma enumerates_equiv_pred f P P' :
  normal_function f ->
  (forall x, complete x -> P x <-> P' x) ->
  enumerates f P ->
  enumerates f P'.
Proof.
  intros Hn Hp Hf.
  constructor.
  - intros. apply Hp.
    apply normal_complete; auto.
    apply enumerates_included; auto.
  - eapply enumerates_monotone; eauto.
  - eapply enumerates_increasing; eauto.
  - intros x z Hx Hz1 Hz2.
    apply (enumerates_least f P Hf); auto.
    apply Hp; auto.
Qed.


Theorem enum_fixpoints_enumerates f:
  (forall x, complete x -> x ≤ f x) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  normal_function f ->
  enumerates (enum_fixpoints f) (fun x => x ≈ f x).
Proof.
  intros Hinf Hmono Hcont.
  hnf; intros.
  constructor; auto.
  - apply enum_are_fixpoints; auto.
  - intros; apply enum_fixpoints_monotone; auto.
  - intros; apply enum_fixpoints_increasing; auto.
  - intros x z Hx Hz Hz1 Hz2.
    destruct x as [A g]. simpl.
    apply fixOrd_least; auto.
    + rewrite ord_le_unfold. simpl; intros.
      apply Hz2. apply (index_lt (ord A g) a).
    + apply Hz1.
Qed.

Definition Γ a := enum_fixpoints (fun b => veblen powOmega b 0) a.

Theorem Γ_fixpoints : forall a, complete a -> Γ a ≈ veblen powOmega (Γ a) 0.
Proof.
  intros a Ha. unfold Γ.
  apply enum_are_fixpoints; auto.
  apply veblen_first_normal.
  apply powOmega_normal.
Qed.

Theorem Γ_normal : normal_function Γ.
Proof.
  unfold Γ.
  apply enum_fixpoints_normal.
  apply veblen_first_normal.
  apply powOmega_normal.
Qed.

Theorem Γ₀_least : forall x, veblen powOmega x 0 ≈ x -> Γ 0 ≤ x.
Proof.
  intros.
  unfold Γ.
  rewrite enum_fixpoints_zero.
  apply fixOrd_least.
  intros; apply veblen_monotone_first; auto.
  apply powOmega_monotone; auto.
  apply zero_least.
  apply H.
  apply veblen_first_normal.
  apply powOmega_normal; auto.
Qed.

Theorem Γ_enumerates : enumerates Γ (strongly_critical_ordinal powOmega).
Proof.
  cut (enumerates Γ (fun x => x ≈ veblen powOmega x 0)).
  { apply enumerates_equiv_pred.
    apply Γ_normal.
    intros. rewrite strongly_critical_fixpoint; auto.
    split; apply ord_eq_sym.
    apply powOmega_normal. }

  apply enum_fixpoints_enumerates.
  - intros.
    apply (normal_inflationary (fun x => veblen powOmega x 0)); auto.
    apply veblen_first_normal.
    apply powOmega_normal.
  - intros; apply veblen_monotone_first; auto.
    apply powOmega_monotone.
  - apply veblen_first_normal.
    apply powOmega_normal.
Qed.

Definition Ξ a := enum_fixpoints (fun b => veblen Γ b 0) a.

Theorem Ξ_fixpoints : forall a, complete a -> Ξ a ≈ veblen Γ (Ξ a) 0.
Proof.
  intros a Ha. unfold Ξ.
  apply enum_are_fixpoints; auto.
  apply veblen_first_normal.
  apply Γ_normal.
Qed.

Theorem Ξ_normal : normal_function Ξ.
Proof.
  unfold Ξ.
  apply enum_fixpoints_normal.
  apply veblen_first_normal.
  apply Γ_normal.
Qed.

Theorem Ξ_enumerates : enumerates Ξ (strongly_critical_ordinal Γ).
Proof.
  cut (enumerates Ξ (fun x => x ≈ veblen Γ x 0)).
  { apply enumerates_equiv_pred.
    apply Ξ_normal.
    intros. rewrite strongly_critical_fixpoint; auto.
    split; apply ord_eq_sym.
    apply Γ_normal. }

  apply enum_fixpoints_enumerates.
  - intros.
    apply (normal_inflationary (fun x => veblen Γ x 0)); auto.
    apply veblen_first_normal.
    apply Γ_normal.
  - intros; apply veblen_monotone_first; auto.
    apply normal_monotone.
    apply Γ_normal.
  - apply veblen_first_normal.
    apply Γ_normal.
Qed.

