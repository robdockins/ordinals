Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import ClassicalFacts.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import Classical.
From Ordinal Require Import Enumerate.

Record normal_function (f:Ord -> Ord) :=
  NormalFunction
  { normal_monotone   : forall x y, x ≤ y -> f x ≤ f y
  ; normal_increasing : forall x y, x < y -> f x < f y
  ; normal_continuous : strongly_continuous f
  ; normal_nonzero    : forall x, 0 < f x
  }.

(* We say x is a critical ordinal for β when
   x is a fixpoint for (veblen α) whenever α < β.
 *)
Definition critical_ordinal f (β:Ord) (x:Ord) : Prop :=
  forall α, α < β -> x ≈ veblen f α x.

Definition strongly_critical_ordinal f (β:Ord) : Prop :=
  β > 0 /\ critical_ordinal f β β.

Lemma normal_inflationary f :
  normal_function f ->
  forall x, x ≤ f x.
Proof.
  intro Hf.
  apply increasing_inflationary.
  apply normal_increasing.
  auto.
Qed.

Section veblen.
  Variable f : Ord -> Ord.
  Hypothesis f_normal : normal_function f.
  Hypothesis ord_zeroDec : forall x, x ≤ 0 \/ 0 < x.
  Hypothesis ord_directed : forall (x:Ord), directed x x.

  Lemma veblen_nonzero (β:Ord) (y:Ord) :
    0 < veblen f β y.
  Proof.
    rewrite veblen_unroll.
    rewrite <- lub_le1.
    apply normal_nonzero; auto.
  Qed.

  Lemma veblen_inflationary (β:Ord) : forall x, x ≤ veblen f β x.
  Proof.
    intro x.
    rewrite veblen_unroll.
    rewrite <- lub_le1.
    apply normal_inflationary. auto.
  Qed.

  Lemma veblen_unroll_nonzero (β:Ord) (y:Ord) :
    0 < β -> veblen f β y ≈ supOrd (fun α:β => fixOrd (veblen f α) (limOrd (fun x => veblen f β (y x)))).
  Proof.
    destruct β as [B g].
    intros H; split.
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb]. simpl in *.
    - rewrite veblen_unroll.
      apply lub_least.
      + simpl.
        rewrite <- (sup_le _ _ b).
        transitivity (fixOrd f (limOrd (fun x : y => veblen f (ord B g) (y x)))).
        rewrite fixOrd_fixpoint; auto.
        apply normal_monotone; auto.
        rewrite <- fixOrd_above.
        destruct y as [Y h]. simpl.
        rewrite ord_le_unfold.
        simpl; intro q.
        rewrite ord_lt_unfold. simpl.
        exists q.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_inflationary; auto.
        apply normal_continuous; auto.
        apply normal_inflationary; auto.
        apply fixOrd_monotone_func; auto.
        intros. rewrite veblen_unroll.
        apply lub_le1.
        apply veblen_monotone; auto.
        apply normal_monotone; auto.
      + reflexivity.
    - rewrite veblen_unroll.
      apply lub_le2.
  Qed.

  Lemma veblen_increasing0 : forall x y, x < y -> veblen f 0 x < veblen f 0 y.
  Proof.
    intros.
    apply ord_le_lt_trans with (f x).
    { rewrite veblen_unroll.
      apply lub_least; auto with ord.
      apply sup_least. simpl; intros.
      elim a. }
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
    rewrite <- fixOrd_above.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [q Hq].
    rewrite ord_lt_unfold. simpl.
    exists q.
    apply veblen_monotone; auto.
    apply normal_monotone; auto.
  Qed.

  Lemma veblen_increasing (β:Ord) :
    forall x y, x < y -> veblen f β x < veblen f β y.
  Proof.
    destruct (ord_zeroDec β); auto.
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

  Lemma veblen_lt_lemma β : 0 < β -> forall x q,
     q < veblen f β x ->
     exists a, a < β /\
         q < fixOrd (veblen f a) (limOrd (fun i => veblen f β (x i))).
  Proof.
    intros Hb x q H.
    rewrite veblen_unroll_nonzero in H; auto.
    destruct β as [B g]. simpl in H.
    apply sup_lt in H.
    destruct H as [a H].
    exists (g a). split; auto with ord.
  Qed.

  Lemma veblen_fixpoints_aux (β:Ord) :
      (forall y, y < β -> strongly_continuous (veblen f y)) ->
      forall α x, α < β -> veblen f α (veblen f β x) ≤ veblen f β x.
  Proof.
    intros Hcont a x H.
    rewrite (veblen_unroll f a).
    apply lub_least.
    - transitivity (f (supOrd (fun α:β => fixOrd (veblen f α) (limOrd (fun i => veblen f β (x i)))))).
      + apply normal_monotone; auto.
        rewrite (veblen_unroll_nonzero); auto. reflexivity.
        apply ord_le_lt_trans with a; auto. apply zero_least.
      + rewrite (veblen_unroll_nonzero); auto.
        2: { apply ord_le_lt_trans with a; auto. apply zero_least. }
        destruct β as [B g]. simpl.
        rewrite ord_lt_unfold in H.
        destruct H as [b Hb].
        rewrite (normal_continuous f f_normal B _ b).
        apply sup_least; intro i.
        rewrite <- (sup_le _ _ i).
        transitivity (veblen f (g i)
                             (fixOrd (veblen f (g i))
                                     (limOrd (fun i0 : x => veblen f (ord B g) (x i0))))).
        * rewrite (veblen_unroll f (g i)).
          apply lub_le1.
        * apply fixOrd_prefixpoint.
          apply Hcont.
          apply (index_lt (ord B g) i).

    - destruct a as [A g]. simpl.
      apply sup_least. intro y.
      rewrite (veblen_unroll f β) at 2.
      rewrite <- lub_le2.

      apply fixOrd_least.
      + intros; apply veblen_monotone; auto.
        apply normal_monotone; auto.
      + apply limit_least. intro q.
        destruct (veblen_lt_lemma β) with x q as [a' [Ha' Hq]]; auto with ord.
        apply ord_le_lt_trans with (ord A g); auto with ord.
        destruct β as [B h].
        simpl.
        rewrite ord_lt_unfold in Ha'.
        destruct Ha' as [b1 Hb1].
        rewrite ord_lt_unfold in H.
        destruct H as [b2 Hb2].
        simpl in *.
        destruct (ord_directed (ord B h) b1 b2) as [b' [??]].
        rewrite <- (sup_le _ _ b').
        rewrite fixOrd_fixpoint; auto.
        apply ord_le_lt_trans with (veblen f (h b') (veblen f (ord B h) x q)).
        apply veblen_monotone_first; auto.
        apply normal_monotone; auto.
        rewrite Hb2; auto.
        apply veblen_increasing.
        eapply ord_lt_le_trans; [ apply Hq | ].
        apply fixOrd_monotone_func.
        intros; apply veblen_monotone_first; auto.
        apply normal_monotone; auto.
        rewrite Hb1; auto.
        apply veblen_monotone; auto.
        apply normal_monotone; auto.
        apply Hcont; auto with ord.
        apply veblen_inflationary.
      + destruct β as [B h].
        simpl.
        rewrite ord_lt_unfold in H.
        destruct H as [b1 Hb].
        etransitivity.
        { apply (Hcont (g y)); auto.
          apply ord_lt_le_trans with (ord A g); auto with ord.
          rewrite Hb. auto with ord. }
        apply sup_least; intro b2.
        destruct (ord_directed (ord B h) b1 b2) as [b' [??]].
        rewrite <- (sup_le _ _ b').
        rewrite (fixOrd_fixpoint (veblen f (h b'))); auto.
        transitivity (veblen f (h b')
                             (fixOrd (veblen f (h b2))
                                     (limOrd (fun x0 : x => veblen f (ord B h) (x x0))))).
        apply veblen_monotone_first; auto.
        apply normal_monotone; auto.
        transitivity (ord A g); auto with ord.
        rewrite Hb; auto.
        apply veblen_monotone; auto.
        apply normal_monotone; auto.
        apply fixOrd_monotone_func; auto.
        intros; apply veblen_monotone_first; auto.
        apply normal_monotone; auto.
        intros; apply veblen_monotone; auto.
        apply normal_monotone; auto.
        apply Hcont; auto with ord.
        intros; apply veblen_inflationary; auto.
  Qed.

  Lemma veblen_continuous (β:Ord) : strongly_continuous (veblen f β).
  Proof.
    induction β as [β Hind] using ordinal_induction.
    destruct β as [A g]; simpl.
    hnf; intros X h x.
    rewrite veblen_unroll.
    apply lub_least.
    - rewrite (normal_continuous f f_normal X h x); auto.
      apply sup_ord_le_morphism.
      hnf; simpl; intros.
      rewrite veblen_unroll.
      apply lub_le1.
    - apply sup_least. intro a.
      apply fixOrd_least.
      + apply veblen_monotone. apply normal_monotone; auto.
      + rewrite ord_le_unfold.
        simpl. rewrite sup_unfold.
        simpl. intros [x' y]. simpl.
        rewrite <- (sup_le _ _ x').
        apply veblen_increasing_nonzero.
        * rewrite ord_lt_unfold. exists a. apply zero_least.
        * apply index_lt.
      + rewrite (Hind (g a) (index_lt (ord A g) a) X (fun i => veblen f (ord A g) (h i)) x).
        apply sup_ord_le_morphism. hnf; simpl. intro x'.
        apply veblen_fixpoints_aux; auto.
        apply (index_lt (ord A g)).
  Qed.

  Lemma veblen_fixpoints :
    forall α β x,
      α < β ->
      veblen f α (veblen f β x) ≈ veblen f β x.
  Proof.
    intros. split.
    - apply veblen_fixpoints_aux; auto.
      intros. apply veblen_continuous; auto.
    - apply veblen_inflationary.
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
      rewrite <- (sup_le _ _ z).
      apply fixOrd_monotone; auto.
      apply veblen_monotone.
      apply normal_monotone; auto.
      rewrite ord_le_unfold.
      simpl; intros [].
  Qed.

  Lemma veblen_normal (β:Ord) : normal_function (veblen f β).
  Proof.
    constructor.
    - apply veblen_monotone. apply normal_monotone; auto.
    - apply veblen_increasing; auto.
    - apply veblen_continuous; auto.
    - apply veblen_nonzero.
  Qed.

  Lemma veblen_increasing_first :
    forall a β, a < β -> veblen f a 0 < veblen f β 0.
  Proof.
    intros a β H.
    rewrite (veblen_unroll f β).
    rewrite <- lub_le2.
    destruct β as [B g].
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb].
    simpl.
    rewrite <- (sup_le _ _ b).
    apply ord_le_lt_trans with (veblen f (g b) 0).
    apply veblen_monotone_first; auto. apply normal_monotone; auto.
    rewrite fixOrd_fixpoint; auto.
    apply veblen_increasing.
    rewrite fixOrd_fixpoint; auto.
    apply veblen_nonzero.
    apply veblen_continuous.
    apply veblen_inflationary.
    apply veblen_continuous.
    apply veblen_inflationary.
  Qed.

  Lemma veblen_first_unroll β :
    veblen f β 0 ≈ f 0 ⊔ boundedSup β (fun α => fixOrd (veblen f α) 0).
  Proof.
    destruct β as [B g].
    split; simpl.
    - rewrite veblen_unroll. unfold boundedSup.
      apply lub_least; auto with ord.
      simpl; apply sup_least; intro a.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ a).
      apply fixOrd_monotone; auto.
      apply veblen_monotone; auto.
      apply normal_monotone; auto.
      rewrite ord_le_unfold. intros [].
    - rewrite veblen_unroll.
      apply lub_least; auto with ord.
      apply sup_least; intro a.
      rewrite <- lub_le2.
      simpl.
      rewrite <- (sup_le _ _ a).
      apply fixOrd_monotone; auto with ord.
      apply veblen_monotone; auto.
      apply normal_monotone; auto.
  Qed.

  Lemma veblen_first_unroll_nonzero β :
    β > 0 ->
    veblen f β 0 ≈ boundedSup β (fun α => fixOrd (veblen f α) 0).
  Proof.
    intros.
    rewrite veblen_unroll_nonzero; auto.
    destruct β as [B g].
    split; simpl.
    - simpl; apply sup_least; intro a.
      unfold boundedSup.
      rewrite <- (sup_le _ _ a).
      apply fixOrd_monotone; auto.
      apply veblen_monotone; auto.
      apply normal_monotone; auto.
      rewrite ord_le_unfold. intros [].
    - apply sup_least; intro a.
      rewrite <- (sup_le _ _ a).
      apply fixOrd_monotone; auto with ord.
      apply veblen_monotone; auto.
      apply normal_monotone; auto.
  Qed.

  Lemma veblen_first_normal :
    normal_function (fun β => veblen f β 0).
  Proof.
    constructor.
    - intros; apply veblen_monotone_first; auto. apply normal_monotone; auto.
    - intros; apply veblen_increasing_first; auto.
    - hnf; intros.
      apply veblen_continuous_first; auto.
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
      + rewrite fixOrd_fixpoint.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite <- fixOrd_above.
        rewrite ord_le_unfold; simpl; intro x.
        rewrite ord_lt_unfold; simpl; exists x.
        apply increasing_inflationary.
        apply enum_fixpoints_increasing.
        apply veblen_normal; auto.
        apply veblen_continuous; auto.
        apply veblen_inflationary; auto.
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
    forall β, limitOrdinal β ->
      veblen f β 0 ≈ boundedSup β (fun a => veblen f a 0).
  Proof.
    intros.
    rewrite (veblen_unroll f β).
    split.
    - apply lub_least.
      + transitivity (veblen f 0 0).
        rewrite veblen_zero.
        reflexivity.
        destruct β as [B g]; simpl in *.
        destruct H as [[b] _].
        unfold boundedSup.
        rewrite <- (sup_le _ _ b).
        apply veblen_monotone_first.
        apply normal_monotone; auto.
        apply zero_least.
      + destruct β as [B g]; simpl in *.
        apply sup_least; simpl; intro b.
        destruct H as [_ H].
        destruct (H b) as [b' Hb'].
        unfold boundedSup.
        rewrite <- (sup_le _ _ b').
        apply fixOrd_least.
        * intros; apply veblen_monotone; auto.
          apply normal_monotone; auto.
        * rewrite ord_le_unfold; intros [].
        * apply veblen_fixpoints; auto.
    - rewrite <- lub_le2.
      destruct β as [B g]; simpl in *.
      apply sup_least; simpl; intro i.
      rewrite <- (sup_le _ _ i).
      rewrite fixOrd_fixpoint.
      apply veblen_monotone; auto with ord.
      apply normal_monotone; auto.
      apply veblen_continuous; auto.
      apply veblen_inflationary; auto.
  Qed.

  Lemma veblen_limit_succ :
    forall β x, limitOrdinal β ->
      veblen f β (succOrd x) ≈ boundedSup β (fun a => veblen f a (succOrd (veblen f β x))).
  Proof.
    intros β x Hlim.
    rewrite veblen_unroll.
    split.
    - apply lub_least.
      + destruct β as [B g]; simpl.
        destruct Hlim as [[b] _].
        unfold boundedSup.
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
        unfold boundedSup.
        rewrite <- (sup_le _ _ b').
        apply fixOrd_least.
        * apply veblen_monotone; auto.
          apply normal_monotone; auto.
        * rewrite ord_le_unfold; simpl; intro.
          apply ord_lt_le_trans with (succOrd (veblen f (ord B g) x)).
          rewrite ord_lt_unfold. exists tt; simpl.
          reflexivity.
          apply veblen_inflationary; auto.
        * apply veblen_fixpoints; auto.

    - destruct β as [B g]; simpl.
      apply sup_least; intro b.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ b).
      rewrite fixOrd_fixpoint; auto.
      apply veblen_monotone.
      apply normal_monotone; auto.
      rewrite <- fixOrd_above; auto.
      apply succ_least.
      rewrite ord_lt_unfold; exists tt. simpl.
      reflexivity.
      apply veblen_continuous; auto.
      apply veblen_inflationary; auto.
  Qed.

  Lemma veblen_limit_limit :
    forall β x, limitOrdinal β -> limitOrdinal x ->
      veblen f β x ≈ boundedSup β (fun a => veblen f a (boundedSup x (fun y => veblen f β y))).
  Proof.
    intros β x Hlimβ Hlimx.
    destruct β as [B g].
    destruct x as [X h]. simpl.
    rewrite veblen_unroll. simpl.
    split.
    - apply lub_least.
      + destruct Hlimβ as [[b] H].
        unfold boundedSup.
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
      + apply sup_least; intro b.
        destruct Hlimβ as [_ H].
        destruct (H b) as [b' Hb'].
        unfold boundedSup.
        rewrite <- (sup_le _ _ b').
        apply fixOrd_least.
        * apply veblen_monotone.
          apply normal_monotone; auto.
        * rewrite ord_le_unfold; simpl; intro x.
          rewrite <- (veblen_inflationary (g b')).
          destruct Hlimx as [_ H0].
          destruct (H0 x) as [x' Hx'].
          rewrite <- (sup_le _ _ x').
          apply veblen_increasing_nonzero; auto.
          apply ord_le_lt_trans with (g b'); auto.
          apply zero_least.
          apply (index_lt (ord B g)).
        * apply veblen_fixpoints; auto.
    - rewrite <- lub_le2.
      apply sup_least; intro b.
      rewrite <- (sup_le _ _ b).
      rewrite fixOrd_fixpoint.
      apply veblen_monotone.
      apply normal_monotone. auto.
      apply sup_least. intro x.
      rewrite <- fixOrd_above.
      apply ord_lt_le.
      rewrite ord_lt_unfold. simpl. exists x.
      reflexivity.
      apply veblen_continuous; auto.
      apply veblen_inflationary; auto.
  Qed.

  Theorem veblen_enumerates_critical β :
    β > 0 ->
    enumerates (veblen f β) (critical_ordinal f β).
  Proof.
    intros Hβ.
    constructor.
    - intro x. unfold critical_ordinal.
      intros. symmetry. apply veblen_fixpoints; auto.
    - intros; apply veblen_monotone; auto.
      apply normal_monotone; auto.
    - intros; apply veblen_increasing; auto.
    - intros x z Hz1 Hz2.
      rewrite veblen_unroll.
      apply lub_least.
      + generalize (Hz1 0 Hβ).
        rewrite veblen_zero.
        intro.
        rewrite H.
        apply normal_monotone; auto.
        apply ord_le_intro. intros y Hy.
        apply Hz2 in Hy.
        apply ord_le_lt_trans with (veblen f β y); auto.
        apply veblen_inflationary.
      + destruct β as [B g]. simpl.
        apply sup_least; intro i.
        apply fixOrd_least.
        * apply veblen_monotone; auto.
          apply normal_monotone; auto.
        * rewrite ord_le_unfold; simpl.
          intro a.
          apply Hz2.
          apply index_lt.
        * apply Hz1. apply (index_lt (ord B g)); auto.
  Qed.

  Theorem strongly_critical_fixpoint β :
    strongly_critical_ordinal f β <-> veblen f β 0 ≈ β.
  Proof.
    split; intro H.
    - destruct H as [Hβ H].
      split.
      + rewrite veblen_unroll.
        apply lub_least.
        * generalize (H 0 Hβ).
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
             apply (index_lt (ord B g) a).
      + apply (increasing_inflationary (fun x => veblen f x 0)).
        apply veblen_increasing_first; auto.
    - hnf. split.
      + rewrite <- H.
        apply veblen_nonzero.
      + intros α Hα.
        rewrite <- H at 1.
        transitivity (veblen f α (veblen f β 0)).
        symmetry. apply veblen_fixpoints; auto.
        split; apply veblen_monotone.
        apply normal_monotone; auto.
        apply H.
        apply normal_monotone; auto.
        apply H.
  Qed.

End veblen.


Lemma powOmega_normal : normal_function powOmega.
Proof.
  constructor.
  - apply powOmega_monotone.
  - apply powOmega_increasing.
  - unfold powOmega.
    apply expOrd_continuous.
  - intros. apply expOrd_nonzero.
Qed.

Lemma enum_fixpoints_normal f : normal_function f -> normal_function (enum_fixpoints f).
Proof.
  intros.
  constructor.
  - apply enum_fixpoints_monotone; auto.
    apply normal_monotone; auto.
  - apply enum_fixpoints_increasing; auto.
    apply normal_monotone; auto.
  - apply enum_fixpoints_cont.
    apply normal_monotone; auto.
    apply increasing_inflationary.
    apply normal_increasing; auto.
    apply normal_continuous; auto.
  - intro x. rewrite enum_are_fixpoints.
    apply normal_nonzero; auto.
    apply normal_continuous; auto.
    apply normal_inflationary; auto.
Qed.

Theorem Γ_fixpoints (EM:excluded_middle) : forall a, Γ a ≈ veblen powOmega (Γ a) 0.
Proof.
  intro a. unfold Γ.
  apply enum_are_fixpoints; auto.
  apply veblen_continuous_first.
  apply powOmega_normal.
  apply increasing_inflationary.
  apply veblen_increasing_first.
  apply powOmega_normal.
  intro x. apply classical.order_total; auto.
  intro x. apply classical.ord_directed; auto.
Qed.

Theorem Γ_normal (EM:excluded_middle) : normal_function Γ.
Proof.
  unfold Γ.
  apply enum_fixpoints_normal.
  apply veblen_first_normal.
  apply powOmega_normal.
  intro x. apply classical.order_total; auto.
  intro x. apply classical.ord_directed; auto.
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
  intros; apply veblen_monotone_first; auto.
  apply powOmega_monotone; auto.
Qed.

Theorem Γ_enumerates (EM:excluded_middle) : enumerates Γ (strongly_critical_ordinal powOmega).
Proof.
  apply enumerates_equiv_pred with (fun x => x ≈ veblen powOmega x 0).
  { intro; symmetry. rewrite strongly_critical_fixpoint; auto.
    split; apply ord_eq_sym.
    apply powOmega_normal.
    intro; apply classical.order_total; auto.
    intro; apply classical.ord_directed; auto. }
  apply enum_fixpoints_enumerates.
  - intros. apply (increasing_inflationary (fun x => veblen powOmega x 0)).
    apply veblen_increasing_first.
    apply powOmega_normal.
    intro; apply classical.order_total; auto.
    intro; apply classical.ord_directed; auto.
  - intros; apply veblen_monotone_first; auto.
    apply powOmega_monotone.
  - apply veblen_continuous_first.
    apply powOmega_normal.
Qed.

Definition Ξ a := enum_fixpoints (fun b => veblen Γ b 0) a.

Theorem Ξ_fixpoints (EM:excluded_middle) : forall a, Ξ a ≈ veblen Γ (Ξ a) 0.
Proof.
  intros a. unfold Ξ.
  apply enum_are_fixpoints; auto.
  apply veblen_continuous_first.
  apply Γ_normal. auto.
  apply increasing_inflationary.
  apply veblen_increasing_first.
  apply Γ_normal. auto.
  intro x. apply classical.order_total; auto.
  intro x. apply classical.ord_directed; auto.
Qed.

Theorem Ξ_normal (EM:excluded_middle) : normal_function Ξ.
Proof.
  unfold Ξ.
  apply enum_fixpoints_normal.
  apply veblen_first_normal.
  apply Γ_normal. auto.
  intro x. apply classical.order_total; auto.
  intro x. apply classical.ord_directed; auto.
Qed.

Theorem Ξ_enumerates (EM:excluded_middle) : enumerates Ξ (strongly_critical_ordinal Γ).
Proof.
  apply enumerates_equiv_pred with (fun x => x ≈ veblen Γ x 0).
  { intro; symmetry. rewrite strongly_critical_fixpoint; auto.
    split; apply ord_eq_sym.
    apply Γ_normal; auto.
    intro; apply classical.order_total; auto.
    intro; apply classical.ord_directed; auto. }

  apply enum_fixpoints_enumerates.
  - intros. apply (increasing_inflationary (fun x => veblen Γ x 0)).
    apply veblen_increasing_first.
    apply Γ_normal; auto.
    intro o. apply classical.order_total; auto.
    intro o. apply classical.ord_directed; auto.
  - intros; apply veblen_monotone_first; auto.
    apply normal_monotone. apply Γ_normal; auto.
  - apply veblen_continuous_first.
    apply Γ_normal; auto.
Qed.
