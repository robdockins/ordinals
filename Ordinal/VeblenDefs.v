Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.

Section veblen.
  Variable f : Ord -> Ord.

  Fixpoint veblen (β:Ord) : Ord -> Ord :=
    fix inner (y:Ord) : Ord :=
      match β, y with
      | ord A g, ord X h =>
        f (ord X h) ⊔ supOrd (fun a => fixOrd (veblen (g a)) (ord X (fun x => inner (h x))))
      end.

  Lemma veblen_unroll (β:Ord) (y:Ord) :
    veblen β y = f y ⊔ boundedSup β (fun α => fixOrd (veblen α) (limOrd (fun x => veblen β (y x)))).
  Proof.
    destruct β; destruct y; reflexivity.
  Qed.

  Global Opaque veblen.

  Hypothesis Hmonotone : forall x y, x ≤ y -> f x ≤ f y.

  Lemma veblen_monotone (β:Ord) : forall x y, x ≤ y -> veblen β x ≤ veblen β y.
  Proof.
    induction β as [A g Hind]; simpl.
    intros x y; revert x.
    induction y as [X h Hind2]; simpl.
    intros.
    rewrite veblen_unroll.
    apply lub_least.
    - rewrite veblen_unroll.
      rewrite <- lub_le1.
      auto.
    - rewrite veblen_unroll.
      rewrite <- lub_le2.
      simpl.
      apply sup_ord_le_morphism.
      red; simpl; intros.
      apply fixOrd_monotone; auto.
      apply limit_least.
      intro i.
      rewrite ord_le_unfold in H.
      generalize (H i).
      intro Hj.
      rewrite ord_lt_unfold in Hj.
      destruct Hj as [j Hj].
      apply ord_le_lt_trans with (veblen (ord A g) (h j)).
      + apply Hind2; auto.
      + rewrite ord_lt_unfold.
        exists j. simpl.
        reflexivity.
  Qed.

  Lemma veblen_monotone_first β : forall α x, α ≤ β -> veblen α x ≤ veblen β x.
  Proof.
    induction β as [β Hβ] using ordinal_induction.
    intros a x.
    revert a.
    induction x as [x Hx] using ordinal_induction.
    intros.
    rewrite (veblen_unroll a).
    rewrite (veblen_unroll β).
    apply lub_least; [ apply lub_le1 | rewrite <- lub_le2 ].
    apply boundedSup_least. intros c Hc.
    destruct β as [B g].
    simpl.
    assert (Hc2 : c < ord B g).
    apply ord_lt_le_trans with a; auto.
    rewrite ord_lt_unfold in Hc2.
    destruct  Hc2 as [i Hi].
    rewrite <- (sup_le _ _ i).
    simpl in *.
    transitivity (fixOrd (veblen c) (limOrd (fun i => veblen (ord B g) (x i)))).
    - apply fixOrd_monotone.
      + apply veblen_monotone.
      + rewrite ord_le_unfold. simpl; intros.
        rewrite ord_lt_unfold. simpl. exists a0.
        apply Hx; auto.
        apply index_lt.
    - unfold fixOrd.
      apply sup_ord_le_morphism.
      hnf; simpl; intro n.
      apply iter_f_monotone_func; intros; auto.
      + apply Hβ.
        apply (index_lt (ord B g)). auto.
      + apply veblen_monotone; auto.
  Qed.

End veblen.

(* We say x is a critical ordinal for β when
   x is in the range of f and also x is a fixpoint
   for (veblen α) whenever α < β.
 *)
Definition critical_ordinal f (β:Ord) (x:Ord) : Prop :=
  (exists y, x ≈ f y) /\ (forall α, α < β -> x ≈ veblen f α x).

Definition strongly_critical_ordinal f (β:Ord) : Prop :=
  critical_ordinal f β β.

Definition Γ a := enum_fixpoints (fun b => veblen powOmega b 0) a.

Lemma Γ_monotone : forall x y, x ≤ y -> Γ x ≤ Γ y.
Proof.
  unfold Γ. intros x y H.
  apply enum_fixpoints_monotone; auto.
  intros. apply veblen_monotone_first; auto.
  intros. apply powOmega_monotone; auto.
Qed.

Lemma Γ_increasing : forall x y, x < y -> Γ x < Γ y.
Proof.
  unfold Γ. intros x y H.
  apply enum_fixpoints_increasing; auto.
  intros. apply veblen_monotone_first; auto.
  intros. apply powOmega_monotone; auto.
Qed.
