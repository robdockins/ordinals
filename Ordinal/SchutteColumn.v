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
From Ordinal Require Import BHTower.
From Ordinal Require Import BHTowerFacts.

Open Scope ord_scope.


Fixpoint schutte_column (f: Ord -> Ord) (β: Ord) {struct β} : Ord -> Ord -> Ord :=
  fix inner_α (α: Ord) : Ord -> Ord :=
  fix inner_x (x: Ord) : Ord :=
    f (α + x) ⊔
       match β, α, x with
       | ord B fb, ord A fa, ord X fx =>
           supOrd (fun b:B =>
             supOrd (fun a:A =>
             fixOrd (fun δ => schutte_column (inner_α (fa a)) (fb b) δ 0)
                    (limOrd (fun i:X => inner_x (fx i)))
           ))
       end.

Lemma schutte_column_unroll f β α x:
  schutte_column f β α x =
    f (α + x) ⊔
    supOrd (fun b:β =>
      supOrd (fun a:α =>
      fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0)
             (limOrd (fun i:x => schutte_column f β α i))
    )).
Proof.
  destruct β as [B fb]. destruct α as [A fa]. destruct x as [X fx].
  reflexivity.
Qed.

Global Opaque schutte_column.

Lemma schutte_column0 f α x :
  schutte_column f 0 α x ≈ f (α + x).
Proof.
  rewrite schutte_column_unroll. split.
  - apply lub_least. auto with ord.
    apply sup_least; intros [].
  - rewrite <- lub_le1. auto with ord.
Qed.

Lemma proper_le_eq f:
  Proper (ord_le ==> ord_le) f ->
  Proper (ord_eq ==> ord_eq) f.
Proof.
  unfold Proper, respectful; simpl.
  intros H x y Hxy.
  destruct Hxy; split; auto.
Qed.

Lemma schutte_column00 f α :
  Proper (ord_eq ==> ord_eq) f ->
  schutte_column f 0 α 0 ≈ f α.
Proof.
  intro H.
  rewrite schutte_column0.
  apply H. apply addOrd_zero_r.
Qed.

Lemma iter_f_monotone_func' f g n :
  (forall x, f x ≤ g x) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x, iter_f f x n ≤ iter_f g x n.
Proof.
  intros Hfg Hg.
  induction n; intros; simpl.
  - reflexivity.
  - etransitivity; [ apply Hg; auto | apply Hfg ].
Qed.

Lemma fixOrd_monotone_func' f g :
  (forall x, f x ≤ g x) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x, fixOrd f x ≤ fixOrd g x.
Proof.
  intros.
  unfold fixOrd. apply sup_ord_le_morphism.
  intro n. apply iter_f_monotone_func'; auto.
Qed.

Lemma fixOrd_monotone_full f g :
  (forall x, f x ≤ g x) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x y, x ≤ y -> fixOrd f x ≤ fixOrd g y.
Proof.
  intros.
  transitivity (fixOrd f y).
  apply fixOrd_monotone; auto.
  apply fixOrd_monotone_func'; auto.
Qed.

Lemma iter_f_monotone_func'' f g n :
  (forall x, complete x -> f x ≤ g x) ->
  (forall x, complete x -> complete (g x)) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x, complete x -> iter_f f x n ≤ iter_f g x n.
Proof.
  intros Hfg Hg1 Hg2.
  induction n; intros; simpl.
  - reflexivity.
  - etransitivity; [ apply Hg2; auto | apply Hfg ].
    apply iter_f_complete; auto.
Qed.

Lemma fixOrd_monotone_func'' f g :
  (forall x, complete x -> f x ≤ g x) ->
  (forall x, complete x -> complete (g x)) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x, complete x -> fixOrd f x ≤ fixOrd g x.
Proof.
  intros.
  unfold fixOrd. apply sup_ord_le_morphism.
  intro n. apply iter_f_monotone_func''; auto.
Qed.

Lemma fixOrd_monotone_full' f g :
  (forall x, complete x -> f x ≤ g x) ->
  (forall x, complete x -> complete (g x)) ->
  (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x y, complete y -> x ≤ y -> fixOrd f x ≤ fixOrd g y.
Proof.
  intros.
  transitivity (fixOrd f y).
  apply fixOrd_monotone; auto.
  apply fixOrd_monotone_func''; auto.
Qed.

Lemma schutte_column_monotone_αx:
   forall β α f g,
     (forall a b, a ≤ b -> f a ≤ f b) ->
     (forall a b, a ≤ b -> g a ≤ g b) ->
     (forall a, f a ≤ g a) ->
     (forall α' x, α' ≤ α -> schutte_column f β α' x ≤ schutte_column g β α x) /\
     (forall x x', x ≤ x' -> schutte_column f β α x ≤ schutte_column f β α x').
Proof.
  induction β as [β Hindβ] using ordinal_induction.
  induction α as [α Hindα] using ordinal_induction.
  intros f g Hf Hg Hfg.
  split.
  - intros α'.
    induction x as [x Hindx] using ordinal_induction.
    intros Hα.
    rewrite schutte_column_unroll.
    apply lub_least.
    + rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      transitivity (g (α' + x)); auto.
      apply Hg.
      apply addOrd_monotone; auto with ord.
    + apply sup_least; intro b.
      apply sup_least; intro a.
      rewrite schutte_column_unroll.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ b).
      rewrite ord_le_unfold in Hα.
      generalize (Hα a).
      rewrite ord_lt_unfold.
      intros [a' Ha'].
      rewrite <- (sup_le _ _ a').
      apply fixOrd_monotone_full.
      ** intro p.
         apply Hindβ; auto with ord.
         *** intros. destruct Hindα with a f f; auto with ord.
         *** intros. destruct Hindα with a' g g; auto with ord.
         *** intros. destruct Hindα with a' f g; auto with ord.
      ** intros. destruct Hindβ with b α (schutte_column f β (sz a)) (schutte_column f β (sz a)); auto with ord.
         *** intros. destruct Hindα with a f f; auto with ord.
         *** intros. destruct Hindα with a f f; auto with ord.
         *** apply Hindβ; auto with ord.
             **** intros. destruct Hindα with a f f; auto with ord.
             **** intros. destruct Hindα with a f f; auto with ord.
      ** apply lim_ord_le_morphism. intro i.
         apply Hindx; auto with ord.
         rewrite ord_le_unfold. auto.
  - induction x as [x Hindx] using ordinal_induction.
    intros x' Hx.
    rewrite schutte_column_unroll.
    apply lub_least.
    + rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      apply Hf.
      apply addOrd_monotone; auto with ord.
    + apply sup_least. intros b.
      apply sup_least; intro a.
      rewrite schutte_column_unroll.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ b).
      rewrite <- (sup_le _ _ a).
      apply fixOrd_monotone; auto with ord.
      ** intros. apply Hindβ; auto with ord.
         *** intros. destruct Hindα with a f f; auto with ord.
         *** intros. destruct Hindα with a f f; auto with ord.
      ** rewrite ord_le_unfold. simpl.
         intro i. rewrite ord_lt_unfold; simpl.
         rewrite ord_le_unfold in Hx.
         generalize (Hx i). rewrite ord_lt_unfold.
         intros [i' Hi'].
         exists i'.
         apply Hindx; auto with ord.
Qed.

Lemma schutte_column_monotone f β α x α' x':
     (forall a b, a ≤ b -> f a ≤ f b) ->
     α ≤ α' ->
     x ≤ x' ->
     schutte_column f β α x ≤ schutte_column f β α' x'.
Proof.
  intros Hf Hα Hx.
  destruct (schutte_column_monotone_αx β α' f f); auto with ord.
  transitivity (schutte_column f β α x'); auto with ord.
  destruct (schutte_column_monotone_αx β α f f); auto with ord.
Qed.

Lemma schutte_column_monotone_func f g β α x α' x':
     (forall a b, a ≤ b -> f a ≤ f b) ->
     (forall a b, a ≤ b -> g a ≤ g b) ->
     (forall a, f a ≤ g a) ->
     α ≤ α' ->
     x ≤ x' ->
     schutte_column f β α x ≤ schutte_column g β α' x'.
Proof.
  intros Hf Hα Hx.
  destruct (schutte_column_monotone_αx β α' f g); auto with ord.
  transitivity (schutte_column f β α x'); auto with ord.
  destruct (schutte_column_monotone_αx β α f f); auto with ord.
Qed.

Lemma schutte_column_monotoneβ: forall β1 β2 α x f,
  (forall a b, a ≤ b -> f a ≤ f b) ->
  β1 ≤ β2 ->
  schutte_column f β1 α x ≤ schutte_column f β2 α x.
Proof.
  induction β1 as [β1 Hind] using ordinal_induction.
  intros β2.
  induction α as [α Hindα] using ordinal_induction.
  induction x as [x Hindx] using ordinal_induction.
  intros f Hf Hβ.
  rewrite schutte_column_unroll.
  apply lub_least.
  { rewrite schutte_column_unroll.
    apply lub_le1. }
  apply sup_least; intro b1.
  apply sup_least; intro a.
  rewrite schutte_column_unroll.
  rewrite <- lub_le2.
  rewrite ord_le_unfold in Hβ.
  generalize (Hβ b1).
  rewrite ord_lt_unfold.
  intros [b2 Hb2].
  rewrite <- (sup_le _ _ b2).
  rewrite <- (sup_le _ _ a).
  apply fixOrd_monotone_full.
  - intros.
    transitivity (schutte_column (schutte_column f β2 (sz a)) (sz b1) x0 0).
    apply schutte_column_monotone_func; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    intros; apply Hindα; auto with ord.
    rewrite ord_le_unfold; auto.
    apply Hind; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
  - intros; apply schutte_column_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
  - apply lim_ord_le_morphism. intro i.
    apply Hindx; auto with ord.
    rewrite ord_le_unfold; auto.
Qed.

Lemma schutte_column_monotone_full f g β α x β' α' x':
     (forall a b, a ≤ b -> f a ≤ f b) ->
     (forall a b, a ≤ b -> g a ≤ g b) ->
     (forall a, f a ≤ g a) ->
     β ≤ β' ->
     α ≤ α' ->
     x ≤ x' ->
     schutte_column f β α x ≤ schutte_column g β' α' x'.
Proof.
  intros.
  transitivity (schutte_column f β' α x).
  apply schutte_column_monotoneβ; auto.
  apply schutte_column_monotone_func; auto.
Qed.

Lemma schutte_column_le_f:
  forall β α x f,
    (forall a b, a ≤ b -> f a ≤ f b) ->
    f (α + x) ≤ schutte_column f β α x.
Proof.
  intros β α x f Hf.
  rewrite schutte_column_unroll.
  rewrite <- lub_le1.
  reflexivity.
Qed.

Lemma schutte_column_arg0:
  forall β x f,
    (forall a b, a ≤ b -> f a ≤ f b) ->
    schutte_column f β 0 x ≈ f x.
Proof.
  intros β x f Hf.
  rewrite schutte_column_unroll.
  split.
  - apply lub_least.
    + apply Hf.
      rewrite addOrd_zero_l. auto with ord.
    + apply sup_least; intro b.
      apply sup_least; intros [].
  - rewrite <- lub_le1.
    apply Hf. rewrite addOrd_zero_l. auto with ord.
Qed.

Lemma supOrd_succ f α:
  supOrd (fun x:succOrd α => f x) ≈ f tt.
Proof.
  split; auto with ord.
  apply sup_least; intros []; auto with ord.
Qed.

Lemma schutte_column0_complete: forall β α x f,
  (forall x, complete x -> complete (f x)) ->
  β ≤ 0 ->
  complete α ->
  complete x ->
  complete (schutte_column f β α x).
Proof.
  intros. rewrite schutte_column_unroll.
  assert (Hb: forall b:β, False).
  { intros b.
    elim (zero_lt b). apply ord_lt_le_trans with β; auto with ord. }
  apply lub_complete1.
  * apply sup_least; intros; intuition.
  * apply H.
    apply addOrd_complete; auto.
  * apply sup_complete; intuition.
    hnf; intro. intuition.
Qed.

Lemma schutte_column_nonzero: forall f β α x,
    normal_function f ->
    0 < schutte_column f β α x.
Proof.
  intros. rewrite schutte_column_unroll.
  rewrite <- lub_le1.
  apply normal_nonzero; auto.
Qed.

Lemma normal_addOrd: forall x,
    complete x ->
    0 < x ->
    normal_function (addOrd x).
Proof.
  intros. constructor.
  - intros; apply addOrd_monotone; auto with ord.
  - intros; apply addOrd_increasing; auto with ord.
  - hnf; simpl; intros.
    rewrite addOrd_unfold.
    apply lub_least.
    + rewrite <- (sup_le _ _ a0).
      apply addOrd_le1.
    + rewrite (sup_unfold _ f); simpl.
      apply sup_least; intros [i j]; simpl.
      rewrite <- (sup_le _ _ i).
      apply succ_least.
      apply addOrd_increasing; auto with ord.
  - intros; apply addOrd_complete; auto.
  - intros. rewrite <- addOrd_le1. auto.
Qed.

Lemma normal_ord_decompose: forall x f,
    complete x ->
    0 < x ->
    normal_function f ->
    f x ≈ supOrd (fun i:x => f (succOrd i)).
Proof.
  intros x f Hx Hx0 Hf.
  rewrite ord_lt_unfold in Hx0.
  destruct Hx0 as [x' Hx'].
  split.
  - transitivity (f (supOrd (fun i:x => succOrd i))).
    apply normal_monotone; auto.
    destruct x; simpl.
    apply sup_succ_lim.
    apply (normal_continuous f Hf _ (fun i:x => succOrd (sz i)) x').
    apply directed_monotone; auto with ord.
    intro a. apply succ_complete.
    apply complete_subord; auto.
  - apply sup_least; intro i.
    apply normal_monotone; auto.
    apply succ_least; auto with ord.
Qed.

Lemma schutte_column_ltE: forall [z f β α x],
    z < schutte_column f β α x ->
    forall (R:Prop),
      (z < f (α + x) -> R) ->
      (forall (b:β) (a:α),
        z < fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0) (limOrd (fun i:x => schutte_column f β α i)) -> R) ->
      R.
Proof.
  intros z f β α x H R H1 H2.
  rewrite schutte_column_unroll in H.
  apply lub_lt in H.
  destruct H; auto.
  apply sup_lt in H.
  destruct H as [b H].
  apply sup_lt in H.
  destruct H as [a H].
  apply (H2 b a); auto.
Qed.

Lemma schutte_column_increasing: forall β α y x f,
    normal_function f ->
    complete β ->
    complete α ->
    complete y ->
    x < y ->
    schutte_column f β α x < schutte_column f β α y.
Proof.
  intros β α y x f Hf Hβ Hα Hy Hxy.
  destruct (complete_zeroDec β); auto.
  - rewrite (schutte_column_unroll f β α y).
    rewrite <- lub_le1.
    apply ord_le_lt_trans with (f (α + x)).
    rewrite schutte_column_unroll.
    apply lub_least; auto with ord.
    apply sup_least; intros i.
    rewrite ord_le_unfold in H.
    generalize (H i).
    rewrite ord_lt_unfold; intros [[] _].
    apply normal_increasing; auto.
    apply addOrd_complete; auto.
    apply addOrd_increasing; auto.
  - destruct (complete_zeroDec α); auto.
    + rewrite (schutte_column_unroll f β α y).
      rewrite <- lub_le1.
      apply ord_le_lt_trans with (f (α + x)).
      rewrite schutte_column_unroll.
      apply lub_least; auto with ord.
      apply sup_least; intros i.
      apply sup_least; intros j.
      rewrite ord_le_unfold in H0.
      generalize (H0 j).
      rewrite ord_lt_unfold; intros [[] _].
      apply normal_increasing; auto.
      apply addOrd_complete; auto.
      apply addOrd_increasing; auto.
    + rewrite ord_lt_unfold in Hxy.
      destruct Hxy as [y' Hxy].
      apply ord_le_lt_trans with (schutte_column f β α y').
      apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      rewrite (schutte_column_unroll f β α y).
      rewrite <- lub_le2.
      rewrite ord_lt_unfold in H. destruct H as [b0 _].
      rewrite ord_lt_unfold in H0. destruct H0 as [a0 _].
      rewrite <- (sup_le _ _ b0).
      rewrite <- (sup_le _ _ a0).
      unfold fixOrd.
      rewrite <- (sup_le _ _ 0%nat). simpl.
      rewrite ord_lt_unfold. exists y'. simpl.
      reflexivity.
Qed.

Lemma schutte_column_inflationary1: forall β α x f,
  (forall x, complete x -> x ≤ f x) ->
  complete α ->
  complete x ->
  α ≤ schutte_column f β α x.
Proof.
  intros.
  rewrite schutte_column_unroll.
  rewrite <- lub_le1.
  rewrite <- H.
  apply addOrd_le1.
  apply addOrd_complete; auto.
Qed.

Lemma schutte_column_inflationary2: forall β α x f,
  (forall x, complete x -> x ≤ f x) ->
  complete α ->
  complete x ->
  x ≤ schutte_column f β α x.
Proof.
  intros.
  rewrite schutte_column_unroll.
  rewrite <- lub_le1.
  rewrite <- H.
  apply addOrd_le2.
  apply addOrd_complete; auto.
Qed.

Section schutte_column_normal.
  Variable β: Ord.
  Hypotheses Hβ: complete β.

  Hypothesis Hindβ1: forall f β' α,
      normal_function f ->
      complete β' ->
      complete α ->
      β' < β ->
      normal_function (schutte_column f β' α).

  Hypothesis Hindβ2: forall f β',
      normal_function f ->
      complete β' ->
      β' < β ->
      normal_function (fun α => schutte_column f β' α 0).

  Hypothesis Hindβ3:
    forall β' α b a x f,
      β' < β ->
      normal_function f ->
      b < β' ->
      a < α ->
      complete β' ->
      complete α ->
      complete b ->
      complete a ->
      complete x ->
      schutte_column (schutte_column f β' a) b (schutte_column f β' α x) 0 ≤ schutte_column f β' α x.

  Variable α: Ord.
  Hypothesis Hα: complete α.
  Hypothesis Hindα1: forall f α',
      normal_function f ->
      complete α' ->
      α' < α ->
      normal_function (schutte_column f β α').

  Lemma veblen_gt0_column_complete: forall x f,
      normal_function f ->
      complete x ->
      0 < β ->
      (0 < α -> f (α + x) ≤
          supOrd (fun b:β =>
                    supOrd (fun a:α =>
                              fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0)
                                (limOrd (fun i:x => schutte_column f β α i))
          ))) /\
      complete (schutte_column f β α x).
  Proof.
    induction α as [α' Hindα] using ordinal_induction.
    induction x as [x Hindx] using ordinal_induction; intros f Hf Hx Hβ0.

    assert (Hcompete_aux:
             complete
               (supOrd
                  (fun b : β =>
                     supOrd
                       (fun a : α' =>
                          fixOrd (fun δ : Ord => schutte_column (schutte_column f β (sz a)) (sz b) δ 0)
                            (limOrd (fun i : x => schutte_column f β α' (sz i))))))).
    { apply sup_complete; auto with ord.
      - intros b.
        apply sup_complete; auto with ord.
        intros a.
        apply normal_fix_complete; auto with ord.
        + apply lim_complete.
          * intros. apply Hindx; auto with ord.
            apply complete_subord; auto.
          * apply directed_monotone; auto.
            intros; apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
          * destruct x; apply Hx.
        + intros. apply normal_inflationary with (f := fun x => schutte_column (schutte_column f β (sz a)) (sz b) x 0); auto with ord.
          apply Hindβ2; auto with ord.
          apply Hindα1; auto with ord.
          apply complete_subord; auto.
          apply complete_subord; auto.
        + intros. apply schutte_column_monotone; auto with ord.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
        + intros. apply normal_complete with (f := fun x => schutte_column (schutte_column f β (sz a)) (sz b) x 0); auto with ord.
          apply Hindβ2; auto with ord.
          apply Hindα1; auto with ord.
          apply complete_subord; auto.
          apply complete_subord; auto.
        + apply directed_monotone; auto with ord.
          intros. apply fixOrd_monotone_full'; auto with ord.
          intros. apply schutte_column_monotone_func; auto with ord.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
          intros. apply normal_complete with (f := fun x => schutte_column (schutte_column f β (sz y)) (sz b) x 0); auto with ord.
          apply Hindβ2; auto with ord.
          apply Hindα1; auto with ord.
          apply complete_subord; auto.
          apply complete_subord; auto.
          intros. apply schutte_column_monotone; auto with ord.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.

          apply lim_complete; auto.
          intros. apply Hindx; auto with ord.
          apply complete_subord; auto.
          apply directed_monotone; auto with ord.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
          destruct x; apply Hx.
        + destruct (complete_zeroDec α'); auto with ord.
          * right. intros a.
            assert (Ha: a < 0).
            { apply ord_lt_le_trans with α'; auto with ord. }
            rewrite ord_lt_unfold in Ha. destruct Ha as [[] _].
          * left.
            rewrite ord_lt_unfold in H.
            destruct H as [a _].
            exists a.
            unfold fixOrd.
            rewrite <- (sup_le _ _ 1%nat); simpl.
            apply normal_nonzero.
            apply Hindβ1; auto with ord.
            apply Hindα1; auto with ord.
            apply complete_subord; auto.
            apply complete_subord; auto.

            apply lim_complete; auto.
            intros. apply Hindx; auto with ord.
            apply complete_subord; auto.
            apply directed_monotone; auto with ord.
            intros. apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
            destruct x; apply Hx.
      - apply directed_monotone; auto with ord.
        intros.
        apply sup_ord_le_morphism; intro a.
        apply fixOrd_monotone_func''; auto with ord.
        + intros. apply schutte_column_monotoneβ; auto.
          apply Hindα1; auto with ord.
          apply complete_subord; auto.
        + intro x'. apply normal_complete with (f := fun x => schutte_column (schutte_column f β (sz a)) (sz y) x 0); auto with ord.
          apply Hindβ2; auto with ord.
          apply Hindα1; auto with ord.
          apply complete_subord; auto.
          apply complete_subord; auto.
        + intros. apply schutte_column_monotone; auto with ord.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
        + apply lim_complete; auto.
          intros. apply Hindx; auto with ord.
          apply complete_subord; auto.
          apply directed_monotone; auto with ord.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
          destruct x; apply Hx.
      - destruct (complete_zeroDec α'); auto with ord.
        + right; intro b.
          apply sup_least; intro a.
          assert (Ha: a < 0).
          { apply ord_lt_le_trans with α'; auto with ord. }
          rewrite ord_lt_unfold in Ha. destruct Ha as [[] _].
        + left.
          rewrite ord_lt_unfold in Hβ0.
          destruct Hβ0 as [b _].
          exists b.
          rewrite ord_lt_unfold in H.
          destruct H as [a _].
          rewrite <- (sup_le _ _ a).
          unfold fixOrd.
          rewrite <- (sup_le  _ _ 1%nat); simpl.
          apply schutte_column_nonzero.
          apply Hindα1; auto with ord.
          apply complete_subord; auto. }

    assert (Hle2: 0 < α' -> f (α' + x) ≤ supOrd
      (fun b : β =>
       supOrd
         (fun a : α' =>
          fixOrd
            (fun δ : Ord => schutte_column (schutte_column f β (sz a)) (sz b) δ 0)
            (limOrd (fun i : x => schutte_column f β α' (sz i)))))).
    { intros.
      destruct (complete_zeroDec x); auto.
      - transitivity (f α').
        { apply normal_monotone; auto.
          rewrite H0. rewrite addOrd_zero_r. reflexivity. }
        rewrite (normal_ord_decompose α' f); auto with ord.
        apply sup_least; intro a.
        rewrite ord_lt_unfold in Hβ0. destruct Hβ0 as [b Hb].
        rewrite <- (sup_le _ _ b).
        rewrite <- (sup_le _ _ a).
        transitivity (f (a + 1)).
        { apply normal_monotone; auto.
          rewrite addOrd_succ.
          apply succ_monotone.
          rewrite addOrd_zero_r. reflexivity. }
        unfold fixOrd. rewrite <- (sup_le _ _ 2%nat); simpl.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        apply addOrd_monotone; auto with ord.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        rewrite addOrd_zero_r.
        transitivity (1+0).
        { rewrite addOrd_zero_r; auto with ord. }
        transitivity (f 0).
        apply onePlus_least_normal; auto with ord.
        apply normal_monotone; auto with ord.
      - rewrite (normal_ord_decompose x  (fun x => f (α' + x))); auto with ord.
        apply sup_least; intro i.
        rewrite ord_lt_unfold in Hβ0. destruct Hβ0 as [b Hb].
        rewrite <- (sup_le _ _ b).
        rewrite ord_lt_unfold in H. destruct H as [a Ha].
        rewrite <- (sup_le _ _ a).
        unfold fixOrd. rewrite <- (sup_le _ _ 1%nat); simpl.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite <- (addOrd_le2 a).
        rewrite addOrd_succ.
        apply succ_least.
        rewrite addOrd_zero_r.
        rewrite ord_lt_unfold. simpl. exists i.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        apply normal_inflationary; auto.
        apply addOrd_complete; auto.
        apply complete_subord; auto.
        apply compose_normal; auto.
        apply normal_addOrd; auto with ord. }
    split; auto.

    rewrite schutte_column_unroll.
    destruct (complete_zeroDec α'); auto with ord.
    { apply lub_complete1.
      * apply sup_least; intros b.
        apply sup_least; intros a.
        assert (Ha: a < 0).
        { apply ord_lt_le_trans with α'; auto with ord. }
        rewrite ord_lt_unfold in Ha. destruct Ha as [[] _].
      * apply normal_complete; auto with ord.
        apply addOrd_complete; auto with ord.
      * auto.
    }
    apply lub_complete2; auto.
    apply normal_complete; auto with ord.
    apply addOrd_complete; auto with ord.
  Qed.

  Lemma complete_lemma0:
    forall x f, normal_function f -> complete x -> complete (schutte_column f β α x).
  Proof.
    intros.
    destruct (complete_zeroDec β); auto.
    + apply schutte_column0_complete; auto.
      intros; apply normal_complete; auto.
    + intros; apply veblen_gt0_column_complete; auto.
  Qed.

  Lemma complete_lemma1:
    forall x f, normal_function f -> complete x -> complete (limOrd (fun i : x => schutte_column f β α (sz i))).
  Proof.
    intros. apply lim_complete.
    - intros. apply complete_lemma0; auto.
      apply complete_subord; auto.
    - apply directed_monotone; auto.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
    - destruct x; apply H0.
  Qed.

  Lemma complete_lemma2:
    forall (b:β) (a:α) x f,
      normal_function f -> complete x ->
      complete (fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0) (limOrd (fun i:x => schutte_column f β α i))).
  Proof.
    intros. apply normal_fix_complete; auto with ord.
    - apply complete_lemma1; auto.
    - intros; apply schutte_column_inflationary1; auto.
      intros; apply schutte_column_inflationary2; auto.
      intros; apply normal_inflationary; auto.
      apply complete_subord; auto.
      apply zero_complete.
    - intros; apply schutte_column_monotone; auto with ord.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
    - intros. apply normal_complete; auto.
      apply Hindβ1; auto with ord.
      apply Hindα1; auto with ord.
      apply complete_subord; auto.
      apply complete_subord; auto.
      apply zero_complete.
  Qed.

  Lemma complete_lemma3:
    forall (b:β) x f,
      normal_function f -> complete x ->
      complete (supOrd (fun a:α =>
          fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0) (limOrd (fun i:x => schutte_column f β α i)))).
  Proof.
    intros.
    apply sup_complete; auto.
    - intros. apply complete_lemma2; auto.
    - apply directed_monotone; auto with ord.
      intros. apply fixOrd_monotone_func; auto with ord.
      intros; apply schutte_column_monotone_func; auto with ord.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros; apply schutte_column_monotone; auto with ord.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
    - destruct (complete_zeroDec α); auto.
      + right. intro a.
        elim (zero_lt a).
        apply ord_lt_le_trans with α; auto with ord.
      + rewrite ord_lt_unfold in H1. destruct H1 as [a Ha].
        left. exists a.
        unfold fixOrd. rewrite <- (sup_le _ _ 1%nat). simpl.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        apply normal_nonzero; auto with ord.
  Qed.

  Lemma complete_lemma4:
    forall x f,
      normal_function f -> complete x ->
      complete (supOrd (fun b:β => (supOrd (fun a:α =>
          fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0) (limOrd (fun i:x => schutte_column f β α i)))))).
  Proof.
    intros.
    apply sup_complete; auto.
    - intros. apply complete_lemma3; auto.
    - apply directed_monotone; auto with ord.
      intros. apply sup_ord_le_morphism; intro.
      apply fixOrd_monotone_func; auto with ord.
      intros; apply schutte_column_monotone_full; auto with ord.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros; apply schutte_column_monotone; auto with ord.
      intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
    - destruct (complete_zeroDec β); auto.
      + right. intro b.
        elim (zero_lt b).
        apply ord_lt_le_trans with β; auto with ord.
      + destruct (complete_zeroDec α); auto.
        * right. intro b.
          apply sup_least; intro a.
          elim (zero_lt a).
          apply ord_lt_le_trans with α; auto with ord.
        * rewrite ord_lt_unfold in H1. destruct H1 as [b Hb].
          rewrite ord_lt_unfold in H2. destruct H2 as [a Ha].
          left. exists b.
          rewrite <- (sup_le _ _ a).
          unfold fixOrd. rewrite <- (sup_le _ _ 1%nat). simpl.
          rewrite schutte_column_unroll.
          rewrite <- lub_le1.
          rewrite schutte_column_unroll.
          rewrite <- lub_le1.
          apply normal_nonzero; auto with ord.
  Qed.

  Lemma schutte_column_fixpoint1:
    forall a x f,
      normal_function f ->
      0 < β ->
      a < α ->
      complete a ->
      complete x ->
      f (a + schutte_column f β α x) ≤ schutte_column f β α x.
  Proof.
    induction x as [x Hindx] using ordinal_induction.
    intros f Hf Hβ0 Ha Hx.
    assert (Hnorm: scott_continuous (fun x => f (a + x))).
    { hnf; intros.
      transitivity (f (supOrd (fun i:A => a + f0 i))).
      apply normal_monotone; auto.
      apply addOrd_continuous; auto.
      apply normal_continuous; auto.
      hnf; intros.
      destruct (H a1 a2) as [a3 [Ha1 Ha2]].
      exists a3.
      split; apply addOrd_monotone; auto with ord.
      intros.
      apply addOrd_complete; auto. }

    transitivity (f (a + supOrd (fun b:β =>
                    supOrd (fun a:α =>
                              fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0)
                                (limOrd (fun i:x => schutte_column f β α i)))))).
    { apply normal_monotone; auto.
      apply addOrd_monotone; auto with ord.
      rewrite schutte_column_unroll.
      apply lub_least; auto with ord.
      apply (veblen_gt0_column_complete x f); auto.
      apply ord_le_lt_trans with a; auto with ord. }
    transitivity (supOrd (fun b:β => f (a + supOrd (fun a:α =>
                              fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0)
                                (limOrd (fun i:x => schutte_column f β α i)))))).
    rewrite ord_lt_unfold in Hβ0.
    destruct Hβ0 as [b Hb].
    apply Hnorm; auto.
    apply directed_monotone; auto.
    { intros; apply sup_ord_le_morphism.
      intro a'.
      apply fixOrd_monotone_func; auto with ord.
      intros. apply schutte_column_monotoneβ; auto with ord.
      intros. apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros. apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      apply Hindα1; auto with ord.
      apply complete_subord; auto. }

    { intros b'. apply complete_lemma3; auto. }
    apply sup_least; intro b'.
    transitivity (supOrd (fun a':α => f (a +
                              fixOrd (fun δ => schutte_column (schutte_column f β a') b' δ 0)
                                (limOrd (fun i:x => schutte_column f β α i))))).
    rewrite ord_lt_unfold in Ha.
    destruct Ha as [a2 Ha2].
    apply Hnorm; auto.
    apply directed_monotone; auto.
    { intros.
      apply fixOrd_monotone_func; auto with ord.
      intros. apply schutte_column_monotone_func; auto with ord.
      intros. apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros. apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros. apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      intros. apply schutte_column_monotone; auto with ord.
      intros. apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto. }
    { intros a'. apply complete_lemma2; auto. }
    apply sup_least; intro a'.
    rewrite ord_lt_unfold in Ha.
    destruct Ha as [a2 Ha2].
    destruct (complete_directed α Hα a' a2) as [a3 [Ha31 Ha32]].
    rewrite schutte_column_unroll.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ b').
    rewrite <- (sup_le _ _ a3).
    rewrite normal_fixpoint with (f:=(fun δ : Ord => schutte_column (schutte_column f β (sz a3)) (sz b') δ 0)).
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    apply normal_monotone; auto.
    apply addOrd_monotone; auto with ord.
    transitivity a2; auto.
    rewrite addOrd_zero_r.
    apply fixOrd_monotone_func; auto with ord.
    intros; apply schutte_column_monotone_func; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto with ord.
    apply Hindα1; auto with ord.
    apply complete_subord; auto.
    apply Hindβ2; auto with ord.
    apply Hindα1; auto with ord.
    apply complete_subord; auto.
    apply complete_subord; auto.
    apply complete_lemma1; auto.
  Qed.

  Lemma schutte_column_fixpoint':
    forall a b x f,
      normal_function f ->
      b < β ->
      a < α ->
      complete b ->
      complete a ->
      complete x ->
      schutte_column (schutte_column f β a) b (schutte_column f β α x) 0 ≤ schutte_column f β α x.
  Proof.
    induction a as [a Hinda] using ordinal_induction.
    intros.
    rewrite schutte_column_unroll.
    apply lub_least.
    - transitivity (schutte_column f β a (schutte_column f β α x)).
      apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      rewrite addOrd_zero_r. auto with ord.

      rewrite schutte_column_unroll.
      apply lub_least.
      + apply schutte_column_fixpoint1; auto.
        apply ord_le_lt_trans with b; auto with ord.
      + apply sup_least; intro b2.
        apply sup_least; intro a2.
        unfold fixOrd. simpl.
        apply sup_least; intro j.
        induction j; simpl.
        * clear b2 a2.
          apply limit_least; intro i.
          eapply (@schutte_column_ltE i); auto with ord.
          ** intro Hi'.
             apply ord_lt_le_trans with (schutte_column f β a (f (α + x))).
             { apply normal_increasing; auto with ord.
               apply normal_complete; auto with ord.
               apply addOrd_complete; auto with ord. }
             destruct (complete_zeroDec x); auto.
             *** transitivity (schutte_column f β a (f α)).
                 { apply schutte_column_monotone; auto with ord.
                   apply normal_monotone; auto.
                   apply normal_monotone; auto.
                   rewrite H5. rewrite addOrd_zero_r. auto with ord. }
                 rewrite (normal_ord_decompose α (fun x => schutte_column f β a (f x))); auto with ord.
                 apply sup_least; intro a2.
                 rewrite ord_lt_unfold in H1.
                 destruct H1 as [a1 Ha1].
                 rewrite (schutte_column_unroll f β α x).
                 rewrite <- lub_le2.
                 rewrite ord_lt_unfold in H0.
                 destruct H0 as [b1 Hb1].
                 rewrite <- (sup_le _ _ b1).
                 destruct (complete_directed α Hα a1 a2) as [a3 [Ha31 Ha32]].
                 rewrite <- (sup_le _ _ a3).
                 rewrite <- normal_prefixpoint; auto.
                 rewrite (schutte_column_unroll _ b1).
                 rewrite <- lub_le1.
                 apply schutte_column_monotone; auto with ord.
                 apply normal_monotone; auto.
                 transitivity a1; auto.
                 rewrite <- normal_prefixpoint; auto.
                 rewrite (schutte_column_unroll _ b1).
                 rewrite <- lub_le1.
                 rewrite (schutte_column_unroll _ β).
                 rewrite <- lub_le1.
                 transitivity (f (a2 + 1)).
                 apply normal_monotone; auto with ord.
                 rewrite addOrd_succ.
                 apply succ_monotone.
                 rewrite addOrd_zero_r; auto with ord.
                 rewrite addOrd_zero_r; auto with ord.
                 apply normal_monotone; auto.
                 apply addOrd_monotone; auto.
                 rewrite addOrd_zero_r; auto with ord.
                 rewrite <- normal_prefixpoint; auto.
                 transitivity (1 + 0).
                 apply addOrd_zero_r.
                 apply onePlus_least_normal.
                 apply Hindβ1; auto with ord.
                 apply Hindα1; auto with ord.
                 apply complete_subord; auto.
                 apply complete_subord; auto.
                 apply complete_lemma2; auto.
                 apply zero_complete.
                 apply Hindβ2; auto with ord.
                 apply Hindα1; auto with ord.
                 apply complete_subord; auto.
                 apply complete_subord; auto.
                 apply complete_lemma1; auto.
                 apply Hindβ2; auto with ord.
                 apply Hindα1; auto with ord.
                 apply complete_subord; auto.
                 apply complete_subord; auto.
                 apply complete_lemma1; auto.
                 apply Hindβ2; auto with ord.
                 apply Hindα1; auto with ord.
                 apply complete_subord; auto.
                 apply complete_subord; auto.
                 apply complete_lemma1; auto.
                 apply ord_le_lt_trans with a; auto with ord.
                 apply compose_normal; auto.
             *** rewrite (schutte_column_unroll f β α).
                 rewrite <- lub_le2.
                 rewrite ord_lt_unfold in H0.
                 destruct H0 as [b1 Hb1].
                 rewrite <- (sup_le _ _ b1).
                 rewrite ord_lt_unfold in H1.
                 destruct H1 as [a1 Ha1].
                 rewrite <- (sup_le _ _ a1).
                 rewrite <- normal_prefixpoint.
                 rewrite (schutte_column_unroll _ b1).
                 rewrite <- lub_le1.
                 apply schutte_column_monotone; auto with ord.
                 apply normal_monotone; auto.
                 rewrite addOrd_zero_r.
                 rewrite <- normal_prefixpoint.
                 rewrite (schutte_column_unroll _ b1).
                 rewrite <- lub_le1.
                 rewrite (schutte_column_unroll _ _ a1).
                 rewrite <- lub_le1.
                 apply normal_monotone; auto.
                 rewrite <- (addOrd_le2 a1).
                 rewrite addOrd_zero_r.
                 rewrite <- fixOrd_above.
                 rewrite (normal_ord_decompose x (fun x => α + x)); auto with ord.
                 apply sup_least; intro j.
                 rewrite addOrd_succ.
                 apply succ_least.
                 rewrite ord_lt_unfold.
                 simpl. exists j.
                 rewrite schutte_column_unroll.
                 rewrite <- lub_le1.
                 apply normal_inflationary; auto.
                 apply addOrd_complete; auto.
                 apply complete_subord; auto.
                 apply normal_addOrd; auto with ord.
                 apply ord_le_lt_trans with a1; auto with ord.
                 apply Hindβ2; auto with ord.
                 apply Hindα1; auto with ord.
                 apply complete_subord; auto.
                 apply complete_subord; auto.
                 apply lim_complete.
                 intros. apply veblen_gt0_column_complete; auto with ord.
                 apply complete_subord; auto.
                 apply ord_le_lt_trans with b1; auto with ord.
                 apply directed_monotone; auto with ord.
                 intros; apply schutte_column_monotone; auto with ord.
                 apply normal_monotone; auto.
                 destruct x; apply H4.
                 apply Hindβ2; auto with ord.
                 apply Hindα1; auto with ord.
                 apply complete_subord; auto.
                 apply complete_subord; auto.
                 apply lim_complete.
                 intros. apply veblen_gt0_column_complete; auto with ord.
                 apply complete_subord; auto.
                 apply ord_le_lt_trans with b1; auto with ord.
                 apply directed_monotone; auto with ord.
                 intros; apply schutte_column_monotone; auto with ord.
                 apply normal_monotone; auto.
                 destruct x; apply H4.

          ** intros b3 a3 Hi'.
             eapply ord_lt_le_trans; [ apply normal_increasing; [ | | apply Hi' ]| ]; auto with ord.
             apply complete_lemma2; auto.

             rewrite ord_lt_unfold in H1. destruct H1 as [a1 Ha1].
             destruct (complete_directed α) with a1 a3 as [a4 [Ha14 Ha34]]; auto with ord.
             rewrite (schutte_column_unroll _ _ α).
             rewrite <- lub_le2.
             rewrite <- (sup_le _ _ b3).
             rewrite <- (sup_le _ _ a4).
             rewrite <- normal_prefixpoint with (f:=(fun δ : Ord => schutte_column (schutte_column f β (sz a4)) (sz b3) δ 0)); auto with ord.
             rewrite (schutte_column_unroll _ b3).
             rewrite <- lub_le1.
             apply schutte_column_monotone; auto with ord.
             apply normal_monotone; auto.
             transitivity a1; auto.
             rewrite addOrd_zero_r.
             apply fixOrd_monotone_func.
             intros. apply schutte_column_monotone_func; auto with ord.
             intros. apply schutte_column_monotone_func; auto with ord.
             apply normal_monotone; auto.
             apply normal_monotone; auto.
             intros. apply schutte_column_monotone_func; auto with ord.
             apply normal_monotone; auto.
             apply normal_monotone; auto.
             intros. apply schutte_column_monotone_func; auto with ord.
             apply normal_monotone; auto.
             apply normal_monotone; auto.
             intros. apply schutte_column_monotone_func; auto with ord.
             intros. apply schutte_column_monotone_func; auto with ord.
             apply normal_monotone; auto.
             apply normal_monotone; auto.
             intros. apply schutte_column_monotone_func; auto with ord.
             apply normal_monotone; auto.
             apply normal_monotone; auto.
             apply Hindβ2; auto with ord.
             apply Hindα1; auto with ord.
             apply complete_subord; auto.
             apply complete_subord; auto.
             apply complete_lemma1; auto.

        * simpl.
          rewrite <- (Hinda a2) with (b:=b2) (x:=x) at 2; auto with ord.
          apply schutte_column_monotone; auto with ord.
          intros. apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
          transitivity a; auto with ord.
          apply complete_subord; auto.
          apply complete_subord; auto.

    - apply sup_least; intro b2.
      apply sup_least; intro q.
      rewrite schutte_column_unroll.
      rewrite <- lub_le2.

      apply normal_fix_least.
      * apply Hindβ2; auto with ord.
        apply Hindβ1; auto with ord.
        apply complete_subord.
        apply veblen_gt0_column_complete; auto with ord.
        apply ord_le_lt_trans with b; auto with ord.
        apply complete_subord; auto.
        apply ord_lt_trans with b; auto with ord.
      * apply complete_lemma4; auto.
      * simpl. rewrite ord_le_unfold.
        intros [].
      * transitivity (supOrd (fun b0:β => (supOrd (fun a0:α =>
                                                       schutte_column (schutte_column (schutte_column f β a) b (sz q)) (sz b2)
                                                         (fixOrd
                                                            (fun δ : Ord => schutte_column (schutte_column f β (sz a0)) (sz b0) δ 0)
                                                            (limOrd (fun i : x => schutte_column f β α (sz i))))
                                                         0
                       )))).
          { transitivity (supOrd (fun b0:β =>  schutte_column (schutte_column (schutte_column f β a) b (sz q)) (sz b2)
                                                 (supOrd (fun a0:α =>
                                                         (fixOrd
                                                            (fun δ : Ord => schutte_column (schutte_column f β (sz a0)) (sz b0) δ 0)
                                                            (limOrd (fun i : x => schutte_column f β α (sz i))))
                                                         )) 0
                       )).
            rewrite ord_lt_unfold in H0. destruct H0 as [b1 Hb1].
            apply normal_continuous with (f:=fun z => schutte_column (schutte_column (schutte_column f β a) b (sz q)) (sz b2) z 0); auto with ord.
            apply Hindβ2; auto with ord.
            apply Hindβ1; auto with ord.
            apply complete_subord; auto.
            apply complete_lemma0; auto.
            apply ord_le_lt_trans with b1; auto with ord.
            apply complete_subord; auto.
            apply ord_lt_le_trans with b; auto with ord.
            transitivity b1; auto with ord.
            apply directed_monotone; auto with ord.
            intros.
            apply sup_ord_le_morphism; intro z.
            apply fixOrd_monotone_func; auto with ord.
            intros; apply schutte_column_monotoneβ; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
            intros. apply complete_lemma3; auto.
            apply sup_least; intro b1.
            rewrite <- (sup_le _ _ b1).
            rewrite ord_lt_unfold in H1.
            destruct H1 as [a1 Ha1].
            apply normal_continuous with (f:=fun z => schutte_column (schutte_column (schutte_column f β a) b (sz q)) (sz b2) z 0); auto with ord.
            apply Hindβ2; auto with ord.
            apply Hindβ1; auto with ord.
            apply Hindα1; auto with ord.
            apply ord_le_lt_trans with a1; auto with ord.
            apply complete_subord; auto.
            apply complete_lemma0; auto.
            apply complete_subord; auto.
            transitivity b; auto with ord.
            apply directed_monotone; auto with ord.
            intros.
            apply fixOrd_monotone_func; auto with ord.
            intros; apply schutte_column_monotone_func; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
            intros; apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
            intros; apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            apply normal_monotone; auto.
            intros. apply complete_lemma2; auto. }
          apply sup_least; intro b''.
          apply sup_least; intro a''.
          eapply (@schutte_column_ltE q); auto with ord.
          { intros Hq.
            rewrite ord_lt_unfold in H0. destruct H0 as [b1 Hb1].
            rewrite ord_lt_unfold in H1. destruct H1 as [a1 Ha1].
            destruct (complete_directed β) with b1 b'' as [b3 [Hb13 Hb''3]]; auto with ord.
            destruct (complete_directed α) with a1 a'' as [a3 [Ha13 Ha''3]]; auto with ord.

            destruct (complete_zeroDec x); auto with ord.
            - assert (Hq': sz q < f α).
              { apply ord_lt_le_trans with (f (α + x)); auto.
                apply normal_monotone; auto with ord.
                rewrite H0.
                rewrite addOrd_zero_r. auto with ord. }
              rewrite (normal_ord_decompose α f) in Hq'; auto with ord.
              apply sup_lt in Hq'.
              destruct Hq' as [a4 Ha4].
              destruct (complete_directed α) with a3 a4 as [a5 [Ha35 Ha45]]; auto with ord.
              rewrite <- (sup_le _ _ b3).
              rewrite <- (sup_le _ _ a5).
              etransitivity; [ | apply normal_prefixpoint ]; auto with ord.

              rewrite <- (Hindβ3 b3 _ b2 q); auto with ord.
              apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone_full; auto with ord.
              apply normal_monotone; auto.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone_full; auto with ord.
              apply normal_monotone; auto.
              apply normal_monotone; auto.
              transitivity a1; auto with ord.
              transitivity a3; auto with ord.
              transitivity b1; auto with ord.
              rewrite <- normal_inflationary with (f:=fun z => schutte_column (schutte_column f β (sz a5)) (sz b3) z 0); auto with ord.
              apply fixOrd_monotone_func; auto with ord.
              intros. apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              transitivity a3; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              apply Hindβ2; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma2; auto.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply ord_lt_le_trans with b; auto with ord.
              transitivity b1; auto.
              apply ord_lt_le_trans with (f (succOrd a4)); auto with ord.
              etransitivity; [ | apply normal_prefixpoint ]; auto with ord.
              transitivity (f (a4 + 1)).
              { apply normal_monotone; auto.
                rewrite addOrd_succ.
                apply succ_monotone.
                rewrite addOrd_zero_r.
                reflexivity. }
              rewrite schutte_column_unroll.
              rewrite <- lub_le1.
              rewrite schutte_column_unroll.
              rewrite <- lub_le1.
              apply normal_monotone; auto with ord.
              apply addOrd_monotone; auto with ord.
              rewrite addOrd_zero_r.
              etransitivity; [ | apply normal_prefixpoint ]; auto with ord.
              transitivity (1+0); [ rewrite addOrd_zero_r; auto with ord |].
              apply onePlus_least_normal.
              apply Hindβ1; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma2; auto.
              apply zero_complete.
              apply Hindβ2; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma1; auto.
              apply Hindβ2; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma1; auto.
              apply complete_subord; auto.
              apply complete_lemma2; auto.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma0; auto.
              apply Hindβ2; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma1; auto.
              apply ord_le_lt_trans with a''; auto with ord.
            - rewrite <- (sup_le _ _ b3).
              rewrite <- (sup_le _ _ a3).
              etransitivity; [ | apply normal_prefixpoint ]; auto with ord.
              rewrite <- (Hindβ3 b3 _ b2 q); auto with ord.
              apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone_full; auto with ord.
              apply normal_monotone; auto.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone_full; auto with ord.
              apply normal_monotone; auto.
              apply normal_monotone; auto.
              transitivity a1; auto with ord.
              transitivity b1; auto with ord.
              rewrite <- normal_inflationary with (f:=fun z => schutte_column (schutte_column f β (sz a3)) (sz b3) z 0); auto with ord.
              apply fixOrd_monotone_func; auto with ord.
              intros; apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              intros; apply schutte_column_monotone; auto with ord.
              intros; apply schutte_column_monotone; auto with ord.
              apply normal_monotone; auto.
              apply Hindβ2; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma2; auto.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply ord_lt_le_trans with b; auto with ord.
              transitivity b1; auto with ord.
              apply ord_lt_le_trans with (f (α + x)); auto.
              rewrite <- normal_prefixpoint; auto with ord.
              rewrite schutte_column_unroll.
              rewrite <- lub_le1.
              rewrite schutte_column_unroll.
              rewrite <- lub_le1.
              apply normal_monotone; auto with ord.
              rewrite <- (addOrd_le2 a3).
              rewrite <- fixOrd_above.
              rewrite (normal_ord_decompose x (fun x => α + x)); auto with ord.
              apply sup_least; intro i.
              rewrite addOrd_succ.
              apply succ_least.
              rewrite addOrd_zero_r.
              rewrite ord_lt_unfold; exists i.
              simpl.
              rewrite schutte_column_unroll.
              rewrite <- lub_le1.
              apply normal_inflationary; auto with ord.
              apply addOrd_complete; auto with ord.
              apply complete_subord; auto.
              apply normal_addOrd; auto with ord.
              apply ord_le_lt_trans with a1; auto with ord.
              apply Hindβ2; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma1; auto.
              apply complete_subord; auto.
              apply complete_lemma2; auto.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma0; auto.
              apply Hindβ2; auto with ord.
              apply Hindα1; auto with ord.
              apply complete_subord; auto.
              apply complete_subord; auto.
              apply complete_lemma1; auto. }

          intros b' a' Hq.
          assert (Hb_final: exists bf:β, b <= bf /\ b' <= bf /\ b'' <= bf).
          { rewrite ord_lt_unfold in H0. destruct H0 as [b1 Hb1].
            destruct (complete_directed β) with b1 b' as [b3 [??]]; auto.
            destruct (complete_directed β) with b3 b'' as [b4 [??]]; auto.
            exists b4. intuition.
            transitivity b3; auto.
            transitivity b1; auto.
            transitivity b3; auto. }
          assert (Ha_final: exists af:α, a <= af /\ a' <= af /\ a'' <= af).
          { rewrite ord_lt_unfold in H1. destruct H1 as [a1 Hba].
            destruct (complete_directed α) with a1 a' as [a3 [??]]; auto.
            destruct (complete_directed α) with a3 a'' as [a4 [??]]; auto.
            exists a4. intuition.
            transitivity a3; auto.
            transitivity a1; auto.
            transitivity a3; auto. }
          destruct Hb_final as [bf [Hbf1 [Hbf2 Hbf3]]].
          destruct Ha_final as [af [Haf1 [Haf2 Haf3]]].
          rewrite <- (sup_le _ _ bf).
          rewrite <- (sup_le _ _ af).
          etransitivity; [ | apply normal_prefixpoint ].
          rewrite ord_lt_unfold in Hq.
          destruct Hq as [q' Hq].
          rewrite <- (Hindβ3 bf _ b2 q'); auto with ord.
          etransitivity.
          { eapply schutte_column_monotone_func with (g := (schutte_column (schutte_column f β (sz af)) (sz bf) (sz q'))).
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.
            intros.
            etransitivity.
            eapply schutte_column_monotone_func with (g := (schutte_column f β (sz af))).
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.
            reflexivity.
            reflexivity.
            etransitivity.
            eapply schutte_column_monotoneβ.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.
            apply Hbf1.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply schutte_column_monotone; auto with ord.
            intros; apply normal_monotone; auto with ord.
            reflexivity.
            reflexivity. }
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.

          transitivity ((fixOrd
                           (fun δ : Ord =>
                              schutte_column (schutte_column f β (sz af)) (sz bf) δ 0)
                           (limOrd (fun i : x => schutte_column f β α (sz i))))).
          apply fixOrd_monotone_func.

          etransitivity.
          intros; apply schutte_column_monotone_func with (g := (schutte_column f β (sz af))).
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          reflexivity.
          reflexivity.
          intros; apply schutte_column_monotoneβ; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          apply normal_inflationary with (f := fun x => schutte_column (schutte_column f β (sz af)) (sz bf) x 0).
          apply Hindβ2.
          apply Hindα1; auto.
          apply complete_subord; auto with ord.
          auto with ord.
          apply complete_subord; auto with ord.
          auto with ord.
          apply complete_lemma2; auto.
          apply Hindα1; auto with ord.
          apply complete_subord; auto with ord.
          apply ord_lt_le_trans with b; auto with ord.
          apply ord_lt_le_trans with (fixOrd
                                        (fun δ : Ord =>
                                           schutte_column (schutte_column f β (sz a')) (sz b') δ 0)
                                        (limOrd (fun i : x => schutte_column f β α (sz i)))); auto with ord.
          apply fixOrd_monotone_func.
          etransitivity.
          intros; apply schutte_column_monotone_func with (g := (schutte_column f β (sz af))).
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          reflexivity.
          reflexivity.
          intros; apply schutte_column_monotoneβ; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply schutte_column_monotone; auto with ord.
          intros; apply normal_monotone; auto with ord.
          apply complete_subord; auto.
          apply complete_lemma2; auto.
          apply complete_subord; auto.
          apply complete_subord; auto.
          apply complete_lemma2; auto.
          apply Hindβ2.
          apply Hindα1.
          auto.
          apply complete_subord; auto.
          auto with ord.
          apply complete_subord; auto.
          auto with ord.
          apply complete_lemma1; auto.
  Qed.

  Lemma schutte_column_continuous: forall f,
      normal_function f ->
      scott_continuous (schutte_column f β α).
  Proof.
    intros f Hf A h a0 Hdir Hcomp.
    rewrite schutte_column_unroll.
    apply lub_least.
    - destruct (complete_zeroDec α); auto.
      { transitivity (supOrd (fun i => f (h i))).
        transitivity (f (supOrd h)).
        apply normal_monotone; auto.
        rewrite H. rewrite addOrd_zero_l. auto with ord.
        apply normal_continuous; auto with ord.
        apply sup_ord_le_morphism; intro i.
        rewrite schutte_column_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        apply addOrd_le2.
      }
      transitivity (supOrd (fun i => f (α + h i))).
      apply normal_continuous with (f := fun x => f (α + x)); auto.
      apply compose_normal; auto.
      apply normal_addOrd; auto with ord.
      apply sup_ord_le_morphism. intro i.
      rewrite schutte_column_unroll.
      apply lub_le1.
    - apply sup_least; intro b.
      apply sup_least; intro a.
      apply normal_fix_least; auto with ord.
      + apply Hindβ2; auto with ord.
        apply Hindα1; auto with ord.
        apply complete_subord; auto.
        apply complete_subord; auto.
      + apply sup_complete; auto.
        * intros. apply veblen_gt0_column_complete; auto with ord.
          rewrite ord_lt_unfold. exists b. auto with ord.
        * hnf; intros i j.
          destruct (Hdir i j) as [z [Hz1 Hz2]].
          exists z; split.
          apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
          apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto.
        * left. exists a0.
          apply schutte_column_nonzero; auto.
      + rewrite sup_unfold.
        apply limit_least; intros [i j]; simpl.
        rewrite <- (sup_le _ _ i).
        apply schutte_column_increasing; auto with ord.
      + transitivity (supOrd (fun i => schutte_column (schutte_column f β (sz a)) (sz b) (schutte_column f β α (h i)) 0)).
        apply (normal_continuous (fun x => schutte_column (schutte_column f β (sz a)) (sz b) x 0)); auto.
        apply Hindβ2; auto with ord.
        apply Hindα1; auto with ord.
        apply complete_subord; auto.
        apply complete_subord; auto.
        hnf; simpl; intros i j.
        destruct (Hdir i j) as [z [Hz1 Hz2]].
        exists z. split.
        apply schutte_column_monotone; auto with ord.
        apply normal_monotone; auto.
        apply schutte_column_monotone; auto with ord.
        apply normal_monotone; auto.
        intro.
        apply veblen_gt0_column_complete; auto with ord.
        rewrite ord_lt_unfold. exists b. auto with ord.
        apply sup_least; intro i.
        rewrite <- (sup_le _ _ i).
        apply schutte_column_fixpoint'; auto with ord.
        apply complete_subord; auto.
        apply complete_subord; auto.
   Qed.
End schutte_column_normal.

Lemma schutte_column_normal_and_fixpoint:
  forall β, complete β ->
    (forall α, complete α ->
      (forall f, normal_function f -> normal_function (schutte_column f β α)) /\
      (forall f b a x, normal_function f -> b < β -> a < α -> complete b -> complete a -> complete x ->
        schutte_column (schutte_column f β a) b (schutte_column f β α x) 0 ≤ schutte_column f β α x)) /\
    (forall f, normal_function f -> normal_function (fun δ => schutte_column f β δ 0)).
Proof.
  induction β as [β Hindβ] using ordinal_induction. intros Hβ.
  assert (main_lemma: (forall α : Ord,
   complete α ->
     (forall f : Ord -> Ord, normal_function f -> normal_function (schutte_column f β α)) /\
     (forall (f : Ord -> Ord) (b a x : Ord),
         normal_function f ->
         b < β ->
         a < α ->
         complete b ->
         complete a ->
         complete x ->
         schutte_column (schutte_column f β a) b (schutte_column f β α x) 0 ≤ schutte_column f β α x))).

  { induction α as [α Hindα] using ordinal_induction. intros Hα.
    split.

    - intros f Hf; constructor.
      + intros; apply schutte_column_monotone; auto with ord.
        intros; apply normal_monotone; auto.
      + intros. apply schutte_column_increasing; auto with ord.
      + intros. apply schutte_column_continuous; auto with ord.
        intros. apply Hindβ; auto.
        intros. apply (Hindβ β'); auto.
        intros. apply (Hindβ β'); auto.
        intros. apply Hindα; auto.
      + intros.
        destruct (complete_zeroDec β); auto.
        * rewrite schutte_column_unroll.
          apply lub_complete1.
          apply sup_least; intros.
          rewrite ord_le_unfold in H0.
          generalize (H0 a); simpl.
          rewrite ord_lt_unfold.
          intros [[] _].
          apply normal_complete; auto.
          apply addOrd_complete; auto.
          apply sup_complete.
          intros.
          rewrite ord_le_unfold in H0.
          generalize (H0 a); simpl.
          rewrite ord_lt_unfold.
          intros [[] _].
          hnf; intros.
          rewrite ord_le_unfold in H0.
          generalize (H0 a1); simpl.
          rewrite ord_lt_unfold.
          intros [[] _].
          right. intros.
          rewrite ord_le_unfold in H0.
          generalize (H0 a); simpl.
          rewrite ord_lt_unfold.
          intros [[] _].
        * intros; apply veblen_gt0_column_complete; auto.
          intros; apply Hindβ; auto.
          intros; apply Hindβ; auto.
          intros. apply Hindα; auto.
      + intros; apply schutte_column_nonzero; auto.

    - intros. apply schutte_column_fixpoint'; auto.
      intros. apply Hindβ; auto.
      intros. apply Hindβ; auto.
      intros. apply Hindβ; auto.
      intros. apply Hindα; auto.
  }

  split; auto.
  intros. constructor.
  + intros; apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
    + intros x y. revert x.
      induction y as [y Hindy] using ordinal_induction.
      intros x Hy Hxy.
      destruct (complete_zeroDec β); auto.
      * apply ord_le_lt_trans with (f x).
        rewrite (schutte_column_unroll _ _ x).
        apply lub_least.
        ** apply normal_monotone; auto.
           rewrite addOrd_zero_r; auto with ord.
        ** apply sup_least; intro b.
           rewrite ord_le_unfold in H0.
           generalize (H0 b).
           rewrite ord_lt_unfold; intros [[] _].
        ** rewrite schutte_column_unroll.
           rewrite <- lub_le1.
           apply ord_lt_le_trans with (f y).
           apply normal_increasing; auto with ord.
           apply normal_monotone; auto with ord.
           rewrite addOrd_zero_r; auto with ord.
      * rewrite ord_lt_unfold in H0.
        destruct H0 as [b1 Hb1].
        rewrite ord_lt_unfold in Hxy. destruct Hxy as [y1 Hy1].
        rewrite (schutte_column_unroll _ _ y).
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ b1).
        rewrite <- (sup_le _ _ y1).
        unfold fixOrd; simpl.
        rewrite <- (sup_le _ _ 2%nat); simpl.
        rewrite (schutte_column_unroll _ (sz b1)).
        rewrite <- lub_le1.
        apply ord_le_lt_trans with (schutte_column f β y1 0).
        { apply schutte_column_monotone; auto with ord.
          apply normal_monotone; auto. }
        apply normal_increasing; auto with ord.
        ** apply main_lemma; auto.
           apply complete_subord; auto.
        ** apply addOrd_complete.
           apply normal_complete.
           apply Hindβ; auto with ord.
           *** apply complete_subord; auto.
           *** apply lim_complete.
               intros [].
               intros [].
               right; intros [[]].
           *** apply main_lemma; auto.
               apply complete_subord; auto.
           *** apply zero_complete.
           *** apply zero_complete.
        ** rewrite addOrd_zero_r.
           rewrite schutte_column_unroll.
           rewrite <- lub_le1.
           rewrite schutte_column_unroll.
           rewrite <- lub_le1.
           apply normal_nonzero; auto.
    + hnf; simpl; intros A g g0 Hg1 Hg2.
      rewrite schutte_column_unroll.
      apply lub_least.
      * transitivity (f (supOrd g)).
        { apply normal_monotone; auto.
          rewrite addOrd_zero_r. reflexivity. }
        transitivity (supOrd (fun i:A => f (g i))).
        apply normal_continuous; auto with ord.
        apply sup_least; intro i.
        rewrite <- (sup_le _ _ i).
        rewrite schutte_column_unroll. rewrite <- lub_le1.
        apply normal_monotone; auto with ord.
        rewrite addOrd_zero_r. reflexivity.
      * apply sup_least; intro b1.
        rewrite (sup_unfold _ g); simpl.
        apply sup_least; intros [i j]; simpl.
        rewrite <- (sup_le _ _ i).
        rewrite schutte_column_unroll.
        rewrite <- lub_le2.
        rewrite <- (sup_le _ _ b1).
        rewrite <- (sup_le _ _ j).
        apply fixOrd_monotone; auto with ord.
        intros; apply schutte_column_monotone; auto with ord.
        intros; apply schutte_column_monotone; auto with ord.
        apply normal_monotone; auto.
        apply limit_least; intros [].

    + intros. apply normal_complete; auto.
      apply main_lemma; auto.
      apply zero_complete.
    + intros; apply schutte_column_nonzero; auto.
Qed.

Lemma schutte_column_normal:
  forall β α f,
    complete β ->
    complete α ->
    normal_function f ->
    normal_function (schutte_column f β α).
Proof.
  intros; apply schutte_column_normal_and_fixpoint; auto.
Qed.

Lemma schutte_column_normal_arg:
  forall β f,
    complete β ->
    normal_function f ->
    normal_function (fun α => schutte_column f β α 0).
Proof.
  intros; apply schutte_column_normal_and_fixpoint; auto.
Qed.

Lemma schutte_column_fixpoint:
  forall β α x f b a,
    complete β -> complete α -> normal_function f ->
    b < β -> a < α ->
    complete b -> complete a -> complete x ->
    schutte_column (schutte_column f β a) b (schutte_column f β α x) 0 ≤ schutte_column f β α x.
Proof.
  intros. apply schutte_column_normal_and_fixpoint; auto.
Qed.

Lemma schutte_column_normalβ f:
  normal_function f ->
  normal_function (fun β => schutte_column f β 1 0).
Proof.
  intros. constructor.
  + intros. apply schutte_column_monotoneβ; auto.
    apply normal_monotone; auto.
  + intros.
    rewrite (schutte_column_unroll f y).
    rewrite ord_lt_unfold in H1.
    destruct H1 as [i Hi].
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    rewrite <- (sup_le _ _ tt).
    unfold fixOrd.
    rewrite <- (sup_le _ _ 3%nat); simpl.
    apply ord_le_lt_trans with (schutte_column (schutte_column f y 0) (sz i) 1 0).
    apply transitivity with (schutte_column f (sz i) 1 0).
    apply schutte_column_monotoneβ; auto.
    apply normal_monotone; auto.
    apply schutte_column_monotone_func; auto with ord.
    apply normal_monotone; auto.
    apply normal_monotone; auto.
    apply schutte_column_normal_and_fixpoint; auto with ord.
    intros. rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    apply normal_monotone; auto.
    rewrite addOrd_zero_l; auto with ord.
    apply normal_increasing with (f := fun x => schutte_column (schutte_column f y 0) i x 0).
    apply (schutte_column_normal_and_fixpoint); auto with ord.
    apply complete_subord; auto.
    apply schutte_column_normal_and_fixpoint; auto with ord.
    apply normal_complete; auto with ord.
    apply (schutte_column_normal_and_fixpoint); auto with ord.
    apply complete_subord; auto.
    apply (schutte_column_normal_and_fixpoint); auto with ord.
    apply complete_subord; auto.
    apply (schutte_column_normal_and_fixpoint); auto with ord.
    { simpl; intuition.
      hnf; intros [].
      right. intros [[]]. }
    apply (schutte_column_normal_and_fixpoint); auto with ord.
    rewrite <- onePlus_least_normal with (f := fun x => schutte_column (schutte_column f y 0) (sz i) x 0).
    apply ord_le_lt_trans with (1 + 0).
    rewrite addOrd_zero_r. reflexivity.
    apply addOrd_increasing.
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    apply normal_nonzero; auto.
    apply schutte_column_normal_and_fixpoint; auto with ord.
    apply complete_subord; auto.
    apply schutte_column_normal_and_fixpoint; auto with ord.
    apply normal_complete.
    apply schutte_column_normal_and_fixpoint; auto with ord.
    apply complete_subord; auto.
    { simpl; intuition.
      hnf; intros [].
      right. intros [[]]. }
    apply schutte_column_normal_and_fixpoint; auto with ord.
    apply zero_complete.

  + hnf; simpl; intros.
    rewrite schutte_column_unroll.
    apply lub_least.
    * rewrite <- (sup_le _ _ a0).
      rewrite schutte_column_unroll.
      apply lub_le1.
    * rewrite (sup_unfold _ f0).
      apply sup_least; intros [i j].
      simpl.
      apply sup_least; intros [].
      rewrite <- (sup_le _ _ i).
      rewrite schutte_column_unroll.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ j).
      rewrite <- (sup_le _ _ tt).
      simpl.
      apply fixOrd_monotone_full.
      ** simpl; intros.
         apply schutte_column_monotone_func; auto with ord.
         intros. apply schutte_column_monotone; auto with ord.
         apply normal_monotone; auto.
         intros. apply schutte_column_monotone; auto with ord.
         apply normal_monotone; auto.
         simpl; intros.
         rewrite schutte_column_unroll.
         apply lub_least.
         rewrite schutte_column_unroll.
         apply lub_le1.
         simpl.
         apply sup_least; intro k.
         apply sup_least; intros [].
      ** intros. apply schutte_column_monotone; auto with ord.
         intros. apply schutte_column_monotone; auto with ord.
         apply normal_monotone; auto.
      ** rewrite ord_le_unfold. intros [].

  + intros. apply normal_complete; auto with ord.
    apply schutte_column_normal_and_fixpoint; auto with ord.
  + intros. apply schutte_column_nonzero; auto.
Qed.

Lemma schutte_column_gt0:
  forall β α f x,
    complete β ->
    complete α ->
    complete x ->
    normal_function f ->
    β > 0 ->
    α > 0 ->
    schutte_column f β α x ≈
    supOrd (fun b:β => supOrd (fun a:α =>
      fixOrd (fun δ => schutte_column (schutte_column f β a) b δ 0)
         (limOrd (fun i:x => schutte_column f β α i)))).
Proof.
  intros. split.
  - rewrite schutte_column_unroll.
    apply lub_least; auto with ord.
    apply veblen_gt0_column_complete; auto with ord.
    intros; apply schutte_column_normal; auto.
    intros; apply schutte_column_normal_arg; auto.
    intros; apply schutte_column_normal; auto.
  - rewrite schutte_column_unroll.
    apply lub_le2.
Qed.

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
      apply schutte_column_normal_arg; auto with ord.
      apply schutte_column_normal; auto with ord.
      apply complete_subord; auto.
      apply normal_complete; auto.
      apply veblen_normal; auto.
      apply limit_least; intro i.
      rewrite Hindx; auto with ord.
      apply veblen_increasing; auto with ord.
      apply complete_subord; auto.
      rewrite schutte_column0.
      rewrite Hindα; auto with ord.
      rewrite <- (veblen_fixpoints f Hf a α) at 2; auto with ord.
      apply veblen_monotone; auto with ord.
      apply normal_monotone; auto.
      rewrite addOrd_zero_r. reflexivity.
      apply complete_subord; auto.
      apply complete_subord; auto.
      apply addOrd_complete; auto with ord.
      apply veblen_complete; auto.
      apply normal_complete; auto.
  - rewrite veblen_unroll.
    apply lub_least.
    + rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
      apply addOrd_le2.
    + apply sup_least; intro a.
      apply normal_fix_least; auto with ord.
      apply veblen_normal; auto with ord.
      apply complete_subord; auto.
      apply normal_complete; auto.
      apply schutte_column_normal; auto.
      apply succ_complete. apply zero_complete.
      apply limit_least. intro i.
      rewrite <- Hindx; auto with ord.
      apply normal_increasing; auto with ord.
      apply schutte_column_normal; auto.
      apply succ_complete. apply zero_complete.
      apply complete_subord; auto.
      rewrite <- (schutte_column_fixpoint 1 α x f 0 a) at 2; auto with ord.
      rewrite schutte_column0.
      rewrite <- Hindα; auto with ord.
      apply schutte_column_monotone; auto with ord.
      apply normal_monotone; auto.
      rewrite addOrd_zero_r. reflexivity.
      apply complete_subord; auto.
      apply normal_complete; auto.
      apply schutte_column_normal; auto.
      apply succ_complete. apply zero_complete.
      apply complete_subord; auto.
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

Definition E_number f n := enum_fixpoints (fun β => schutte_column f β 1 0) n.

Lemma E_number_normal f:
  normal_function f ->
  normal_function (E_number f).
Proof.
  intro Hf.
  unfold E_number.
  apply enum_fixpoints_normal.
  apply schutte_column_normalβ; auto.
Qed.

Require Import Cantor.

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
  - split.
    2: { apply normal_inflationary with (f := fun x => schutte_column _ _ x 0); auto with ord.
         apply schutte_column_normal_arg; auto. }
    rewrite schutte_column_gt0; auto with ord.
    apply sup_least; intro b.
    apply sup_least; intro a.
    apply normal_fix_least; auto with ord.
    apply schutte_column_normal_arg; auto with ord.
    apply complete_subord; auto.
    apply schutte_column_normal; auto with ord.
    apply complete_subord; auto.
    apply limit_least; intros [].
    apply H; auto with ord.
    apply complete_subord; auto.
    apply complete_subord; auto.
    intuition.
  - intros.
    split; auto.
    { rewrite <- H.
      apply normal_nonzero.
      apply schutte_column_normal; auto. }
    intros.
    split.
    2: { apply normal_inflationary with (f := fun x => schutte_column _ _ x 0); auto with ord.
         apply schutte_column_normal_arg; auto.
         apply schutte_column_normal; auto with ord. }
    rewrite <- H at 2.
    rewrite <- (schutte_column_fixpoint β α 0 f b a); auto with ord.
    apply schutte_column_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto.
    apply H.
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
    2: { apply normal_inflationary with (f := fun x => schutte_column f x 1 0); auto.
         apply schutte_column_normalβ; auto. }
    rewrite schutte_column_gt0; auto with ord.
    apply sup_least; intro b.
    apply sup_least; intro a.
    apply normal_fix_least; auto with ord.
    apply schutte_column_normal_arg; auto with ord.
    apply complete_subord; auto.
    apply schutte_column_normal; auto with ord.
    apply limit_least; intros [].
    apply H; auto with ord.
    apply complete_subord; auto.
  - split.
    { rewrite <- H.
      apply normal_nonzero.
      apply schutte_column_normal; auto with ord. }
    hnf. intros; split.
    2: { apply normal_inflationary with (f := fun x => schutte_column _ _ x 0); auto.
         apply schutte_column_normal_arg; auto.
         apply schutte_column_normal; auto. }
    rewrite <- H at 3.
    rewrite <- (schutte_column_fixpoint β 1 0 f b a); auto with ord.
    apply schutte_column_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto.
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
  intros. unfold schutte_critical. constructor.
  + intros. split.
    apply schutte_column_normal_and_fixpoint; auto with ord.
    apply normal_inflationary with (f := fun x => schutte_column _ b x 0).
    apply (schutte_column_normal_and_fixpoint b); auto with ord.
    apply (schutte_column_normal_and_fixpoint); auto with ord.
    apply normal_complete; auto.
    apply (schutte_column_normal_and_fixpoint); auto with ord.
  + intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto.
  + apply normal_increasing. apply schutte_column_normal_and_fixpoint; auto.
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
      apply lub_least.
      ** rewrite ord_le_unfold; intro a'.
         rewrite <- (Hfix b a').
         rewrite schutte_column_unroll.
         rewrite <- lub_le1.
         apply ord_le_lt_trans with (schutte_column f β a' 0).
         { apply normal_inflationary with (f := fun x => schutte_column f β x 0).
           apply (schutte_column_normal_and_fixpoint β); auto with ord.
           apply complete_subord; auto. }
         apply normal_increasing.
         apply schutte_column_normal_and_fixpoint; auto.
         apply complete_subord; auto.
         apply addOrd_complete; auto with ord.
         rewrite addOrd_zero_r.
         rewrite <- (Hfix b a').
         apply schutte_column_nonzero.
         apply schutte_column_normal_and_fixpoint; auto.
         apply complete_subord; auto.
         apply complete_subord; auto.
         apply complete_subord; auto.
         auto with ord.
         auto with ord.
         apply complete_subord; auto.
         apply complete_subord; auto.
         auto with ord.
         auto with ord.
      ** apply sup_least; intro i.
         apply succ_least.
         eapply ord_le_lt_trans; [ | apply (Hlt i); auto with ord ].
         rewrite schutte_column_unroll.
         rewrite <- lub_le1.
         apply normal_inflationary; auto.
         apply addOrd_complete; auto with ord.
         apply complete_subord; auto.
      ** apply complete_subord; auto.
      ** apply complete_subord; auto.
    * apply sup_least; intro b.
      apply sup_least; intro a.
      apply normal_fix_least; intros; auto.
      ** apply (schutte_column_normal_and_fixpoint b); auto with ord.
         apply complete_subord; auto.
         apply (schutte_column_normal_and_fixpoint); auto with ord.
         apply complete_subord; auto.
      ** apply limit_least. intro i.
         apply Hlt; auto with ord.
      ** apply Hfix; auto with ord.
         apply complete_subord; auto.
         apply complete_subord; auto.
Qed.

Lemma enum_supercritical f β :
  normal_function f ->
  complete β ->
  0 < β ->
  enumerates (enum_fixpoints (fun α => schutte_column f β α 0)) (schutte_supercritical f β).
Proof.
  intros Hf Hcβ Hβ.
  constructor.
  - intros. rewrite schutte_supercritical_alt; auto with ord.
    rewrite enum_are_fixpoints at 2; auto with ord.
    apply schutte_column_normal_arg; auto with ord.
    apply normal_complete; auto.
    apply enum_fixpoints_normal; auto.
    apply schutte_column_normal_arg; auto with ord.
  - intros; apply normal_monotone; auto.
    apply enum_fixpoints_normal; auto.
    apply schutte_column_normal_arg; auto with ord.
  - intros; apply normal_increasing; auto.
    apply enum_fixpoints_normal; auto.
    apply schutte_column_normal_arg; auto with ord.
  - intros. apply enum_least; auto with ord.
    apply schutte_column_normal_arg; auto with ord.
    rewrite schutte_supercritical_alt in H1; auto with ord.
    apply H1.
Qed.

Lemma enum_hypercritical f:
  normal_function f ->
  enumerates (E_number f) (schutte_hypercritical f).
Proof.
  intro Hf.
  unfold E_number.
  constructor.
  - intros. rewrite schutte_hypercritical_alt; auto with ord.
    rewrite enum_are_fixpoints at 2; auto with ord.
    apply schutte_column_normalβ; auto with ord.
    apply normal_complete; auto.
    apply enum_fixpoints_normal; auto.
    apply schutte_column_normalβ; auto with ord.
  - intros; apply normal_monotone; auto with ord.
    apply enum_fixpoints_normal; auto.
    apply schutte_column_normalβ; auto with ord.
  - intros; apply normal_increasing; auto with ord.
    apply enum_fixpoints_normal; auto.
    apply schutte_column_normalβ; auto with ord.
  - intros. apply enum_least; auto with ord.
    apply schutte_column_normalβ; auto with ord.
    rewrite schutte_hypercritical_alt in H1; auto with ord.
    apply H1.
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
  rewrite <- (schutte_column_fixpoint β α x f 1 0); auto.
  rewrite schutte_column_veblen.
  apply ord_lt_le_trans with (veblen (addOrd 1) (schutte_column f β α x) 0).
  2: { apply veblen_monotone_func; auto with ord.
       apply onePlus_normal.
       apply schutte_column_normal; auto with ord.
       intros; apply onePlus_least_normal; auto.
       apply schutte_column_normal; auto with ord.
       apply schutte_column_normal; auto with ord. }
    rewrite veblen_onePlus; auto with ord.
    rewrite addOrd_zero_r.
    apply expOmega_additively_closed.
    apply normal_complete; auto with ord.
    apply schutte_column_normal; auto with ord.
    rewrite <- normal_inflationary; auto with ord.
    apply powOmega_normal.
    apply schutte_column_normal; auto with ord.
    rewrite <- normal_inflationary; auto with ord.
    apply powOmega_normal.
    apply schutte_column_normal; auto with ord.
    apply schutte_column_normal; auto with ord.
    apply schutte_column_normal; auto with ord.
    apply schutte_column_normal; auto with ord.
    auto with ord.
    apply succ_complete; auto with ord.
    auto with ord.
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
    rewrite schutte_column_arg0.
    apply normal_increasing; auto.
    apply addOrd_complete; auto with ord.
    apply normal_complete; auto.
    apply schutte_column_normal; auto.
    rewrite addOrd_zero_r.
    apply schutte_column_add_closed; auto.
    apply normal_monotone; auto.
    transitivity 1; auto with ord. }

  rewrite <- (schutte_column_fixpoint β α y f b 0); auto with ord.
  apply ord_lt_le_trans with (schutte_column f b (schutte_column f β α y) 0).
  2: { apply schutte_column_monotone_func; auto with ord.
       apply normal_monotone; auto.
       intros; apply schutte_column_monotone; auto with ord.
       apply normal_monotone; auto.
       intro. rewrite schutte_column_arg0; auto with ord.
       apply normal_monotone; auto. }
  rewrite <- (schutte_column_fixpoint b _ 0 f 0 a); auto with ord.
  rewrite schutte_column0.
  apply schutte_column_increasing; auto with ord.
  apply addOrd_complete; auto with ord.
  apply normal_complete; auto with ord.
  apply schutte_column_normal; auto with ord.
  apply schutte_column_normal; auto with ord.
  rewrite addOrd_zero_r.
  apply ord_lt_le_trans with (schutte_column f β α y); auto.
  apply normal_inflationary with (f:=fun x => schutte_column f b x 0); auto with ord.
  apply schutte_column_normal_arg; auto.
  apply normal_complete; auto.
  apply schutte_column_normal; auto.
  apply normal_complete; auto.
  apply schutte_column_normal; auto.
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

Lemma E_number_unreachable:
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
  rewrite <- Hfix.
  apply ord_le_lt_trans with (1+0).
  { rewrite addOrd_zero_r; auto with ord. }
  rewrite <- onePlus_least_normal with (f:=fun x => schutte_column f x 1 0); auto with ord.
  apply addOrd_increasing.
  rewrite <- Hfix.
  apply normal_nonzero.
  apply schutte_column_normal; auto with ord.
  apply schutte_column_normalβ; auto.
  apply ord_lt_le_trans with E; auto.
  apply normal_inflationary  with (f:=fun x => schutte_column f x 1 0); auto with ord.
  apply schutte_column_normalβ; auto.
  apply ord_lt_le_trans with E; auto.
  apply normal_inflationary with (f:=fun x => schutte_column f x 1 0); auto with ord.
  apply schutte_column_normalβ; auto.
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
    apply schutte_column_normal_arg; auto with ord.
    apply complete_subord; auto.
    apply schutte_column_normal; auto with ord.
    apply limit_least; intros [].
    transitivity (schutte_column f b E 0).
    apply schutte_column_monotone_func; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    apply normal_monotone; auto.
    apply normal_monotone; auto.
    intros. rewrite schutte_column_arg0; auto with ord.
    apply normal_monotone; auto.
    rewrite normal_ord_decompose with (f := fun x => schutte_column f b x 0); auto with ord.
    apply sup_least; intro i.
    apply ord_lt_le.
    apply H; auto with ord.
    apply complete_subord; auto.
    apply succ_complete.
    apply complete_subord; auto.
    apply ord_le_lt_trans with (i+1).
    { rewrite addOrd_succ.
      apply succ_monotone.
      rewrite addOrd_zero_r. auto with ord. }
    apply ord_le_lt_trans with (schutte_column f 1 i 1).
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    apply normal_inflationary; auto with ord.
    apply addOrd_complete; auto with ord.
    apply complete_subord; auto.
    apply H; auto with ord.
    apply complete_subord; auto.
    apply schutte_column_normal_arg; auto with ord.
    apply complete_subord; auto.
Qed.

Lemma E_number_iff_unreachable:
  forall E f,
    normal_function f ->
    complete E ->
    schutte_column f E 1 0 ≈ E <-> schutte_unreachable f E.
Proof.
  intros E f Hf He.
  split; intro H.
  - split.
    + rewrite <- H.
      apply schutte_column_nonzero; auto.
    + intros.
      apply E_number_unreachable; auto with ord.
      apply H.
  - split.
    2: { apply normal_inflationary with (f := fun x => schutte_column f x 1 0); auto with ord.
         apply schutte_column_normalβ; auto. }
    apply unreachable_E_number; intuition.
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

Lemma enum_unreachable f:
  normal_function f ->
  enumerates (E_number f) (schutte_unreachable f).
Proof.
  intros. apply enumerates_equiv_pred with (schutte_hypercritical f).
  - apply E_number_normal; auto.
  - intros. apply hypercritical_iff_unreachable; auto.
  - apply enum_hypercritical; auto.
Qed.

Definition SmallVeblenOrdinal := schutte_column (expOrd ω) ω 1 0.
Definition LargeVeblenOrdinal := fixOrd (fun β => schutte_column (expOrd ω) β 1 0) 0.

Lemma SVO_complete: complete SmallVeblenOrdinal.
Proof.
  unfold SmallVeblenOrdinal.
  apply normal_complete; auto with ord.
  apply schutte_column_normal; auto with ord.
  apply omega_complete.
  apply powOmega_normal.
Qed.

Lemma LVO_complete: complete LargeVeblenOrdinal.
Proof.
  unfold LargeVeblenOrdinal.
  apply normal_fix_complete; auto with ord.
  - intros. apply normal_inflationary with (f:= fun x => schutte_column _ x 1 0); auto.
    apply schutte_column_normalβ.
    apply powOmega_normal.
  - intros; apply schutte_column_monotoneβ; auto.
    intros; apply expOrd_monotone; auto.
  - intros. apply normal_complete; auto with ord.
    apply schutte_column_normal; auto with ord.
    apply powOmega_normal.
Qed.

Lemma LVO_unreachable: schutte_unreachable (expOrd ω) LargeVeblenOrdinal.
Proof.
  intros. hnf. split.
  - unfold LargeVeblenOrdinal.
    unfold fixOrd.
    rewrite <- (sup_le _ _ 1%nat); simpl.
    apply normal_nonzero; auto with ord.
    apply schutte_column_normal; auto with ord.
    apply powOmega_normal.

  - intros.
    apply E_number_unreachable; auto.
    apply powOmega_normal.
    apply LVO_complete.

    unfold LargeVeblenOrdinal.
    apply normal_prefixpoint with (f:= fun x => schutte_column _ x 1 0); auto with ord.
    apply schutte_column_normalβ.
    apply powOmega_normal.
Qed.

Lemma LVO_least_unreachable:
  forall E,
    complete E ->
    schutte_unreachable (expOrd ω) E ->
    LargeVeblenOrdinal <= E.
Proof.
  intros E HcE [HE0 HE].
  unfold LargeVeblenOrdinal.
  apply normal_fix_least; auto with ord.
  apply schutte_column_normalβ.
  apply powOmega_normal.
  apply unreachable_E_number; auto with ord.
  apply powOmega_normal.
  split; auto.
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
  apply IHm'; intuition.
  apply schutte_column_normal; auto with ord.
Qed.

Goal forall f α x y,
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

Goal forall f x y,
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

Goal forall m1 m2 β f x,
  (forall a b, a ≤ b -> f a ≤ f b) ->
  complete β ->
  schutte_matrix f (m1++[(β,0)]++m2) x ≈ schutte_matrix f (m1++m2) x.
Proof.
  induction m1 as [|[p q]]; simpl; intros; auto.
  - split; apply schutte_matrix_monotone_func; intros; auto with ord.
    + apply schutte_column_monotone; auto with ord.
    + rewrite schutte_column_arg0; auto with ord.
    + apply schutte_column_monotone; auto with ord.
    + rewrite schutte_column_arg0; auto with ord.
  - apply IHm1; auto.
    intros; apply schutte_column_monotone; auto with ord.
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

Goal forall f m β α,
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
  apply enumerates_func_equiv with (fun x => schutte_column (schutte_matrix f m) β α x).
  - intros.
    rewrite schutte_matrix_app; simpl.
    rewrite schutte_column0.
    split; apply schutte_column_monotone; auto with ord.
    intros; apply normal_monotone; auto.
    apply schutte_matrix_normal; auto.
    rewrite addOrd_zero_r; auto with ord.
    intros; apply normal_monotone; auto.
    apply schutte_matrix_normal; auto.
    rewrite addOrd_zero_r; auto with ord.
  - intros.
    rewrite schutte_matrix_app; simpl.
    rewrite <- H at 2; auto.
    rewrite <- (H0 b a); auto.
    rewrite schutte_matrix_app; simpl.
    split; apply schutte_column_monotone; auto with ord.
    intros; apply schutte_column_monotone; auto with ord.
    intros; apply normal_monotone; auto.
    apply schutte_matrix_normal; auto.
    apply H.
    intros; apply schutte_column_monotone; auto with ord.
    intros; apply normal_monotone; auto.
    apply schutte_matrix_normal; auto.
    apply H.
  - apply enumerates_equiv_pred with (schutte_critical (schutte_matrix f m) β α).
    + apply schutte_column_normal; auto with ord.
      apply schutte_matrix_normal; auto.
    + intros.
      unfold schutte_critical.
      split; intros.
      rewrite schutte_matrix_app; simpl.
      apply H0; auto with ord.
      rewrite <- (H0 b a) at 2; auto.
      rewrite schutte_matrix_app; simpl; auto with ord.
    + apply schutte_column_enumerates; auto.
      apply schutte_matrix_normal; auto.
Qed.
