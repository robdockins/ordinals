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


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Open Scope ord_scope.

Section vtower.
Hypothesis EM : excluded_middle.

(* Parameter vtower : Ord -> Ord -> Ord. *)

(*
Section vtower_def.
  Parameter MAGIC : (Ord -> Ord) -> Ord -> Ord.

      (* veblen (vtower a) (1 + x) 0 ≈
           MAGIC (vtower a) (limOrd (fun x0 : x => vtower (succOrd a) (x x0))) *)

      (* MAGIC (vtower (g i)) (limOrd (fun x0 : x => vtower (ord B g) (x x0)))
           ≤ veblen (vtower (g i)) (1 + x) 0 *)

      (* vtower (g i) (limOrd (fun i0 : x => vtower (ord B g) (x i0)))
            ≤ MAGIC (vtower (g i)) (limOrd (fun x0 : x => vtower (ord B g) (x x0))) *)

  Hypothesis vtower_unroll : forall b y,
      vtower b y = 1+y ⊔ boundedSup b (fun a => MAGIC (vtower a) (limOrd (fun x => vtower b (y x)))).


  Hypothesis vtower_monotone :
    forall a x b y,
      a <= b -> x <= y -> vtower a x <= vtower b y.

  Hypothesis vtower_normal : forall a, normal_function (vtower a).

  Hypothesis vtower_fixpoint : forall a b x, a < b -> vtower a (vtower b x) ≈ vtower b x.

  Lemma vtower_succ :
    forall a x, vtower (succOrd a) x ≈ veblen (vtower a) (1+x) 0.
  Proof.
    intros.
    rewrite vtower_unroll.
    split.
    - apply lub_least.
      apply (normal_inflationary (fun i => veblen (vtower a) i 0)).
      apply veblen_first_normal; auto.
      apply classical.ord_complete; auto.
      simpl. apply sup_least; intros [].
      admit. (* MAGIC (vtower a) (limOrd (fun x0 : x => vtower (succOrd a) (x x0)))
                   ≤ veblen (vtower a) (1 + x) 0 *)
    - rewrite <- lub_le2.
      simpl. rewrite <- (sup_le _ _ tt).
      admit. (* veblen (vtower a) (1 + x) 0
                ≤ MAGIC (vtower a) (limOrd (fun x0 : x => vtower (succOrd a) (x x0))) *)
  Admitted.

  Lemma vtower_limit :
    forall b x,
      limitOrdinal b ->
      vtower b x ≈ boundedSup b (fun a => vtower a (limOrd (fun i => vtower b (x i)))).
  Proof.
    intros.
    rewrite vtower_unroll.
    split.
    apply lub_least.
    - destruct b as [B g].
      destruct H as [[b0] H].
      simpl.
      rewrite <- (sup_le _ _ b0).
      rewrite vtower_unroll.
      rewrite <- lub_le1.
      apply addOrd_monotone; auto with ord.
      rewrite ord_le_unfold; intro j.
      rewrite ord_lt_unfold; exists j. simpl.
      apply normal_inflationary; auto.
      apply classical.ord_complete; auto.
    - destruct b as [B g].
      destruct H as [[b0] H].
      simpl. apply sup_least; intro i.
      destruct (H i) as [i' Hb'].
      rewrite <- (sup_le _ _ i').




      transitivity (veblen (vtower (g i)) (1+x) 0).
      admit. (* MAGIC (vtower (g i)) (limOrd (fun x0 : x => vtower (ord B g) (x x0)))
                  ≤ veblen (vtower (g i)) (1 + x) 0 *)
      destruct (H i) as [i' Hi].
      rewrite <- (sup_le _ _ i').
      transitivity (vtower (succOrd (g i)) (limOrd (fun i0 : x => vtower (ord B g) (x i0)))).
      rewrite vtower_succ.
      apply veblen_monotone_first; auto.
      intros; apply normal_monotone; auto.
      apply addOrd_monotone; auto with ord.
      rewrite ord_le_unfold. intros j.
      rewrite ord_lt_unfold. exists j.
      simpl.
      apply normal_inflationary; auto.
      apply classical.ord_complete; auto.
      apply vtower_monotone; auto with ord.
      apply succ_least. auto.
    - destruct b as [B g].
      destruct H as [[b0] H].
      simpl. apply sup_least; intro i.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ i).
      admit. (* vtower (g i) (limOrd (fun i0 : x => vtower (ord B g) (x i0)))
                   ≤ MAGIC (vtower (g i)) (limOrd (fun x0 : x => vtower (ord B g) (x x0))) *)
  Admitted.

End vtower_def.

************)

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
