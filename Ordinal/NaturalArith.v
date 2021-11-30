Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.


(** The "natural" ordinal addition function as defined by Hessenberg.
  * This ordinal operation is commutative, associative and absorbs zero.
  * It is also strictly monotone in both of its arguments.
  *
  * Morover, it is the smallest binary operation on ordinals which is strictly monotone
  * in both of its arguments.
  *)
Fixpoint naddOrd (x:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match x, y with
    | ord A f, ord B g =>
      ord (A+B) (fun ab =>
                 match ab with
                 | inl a => naddOrd (f a) y
                 | inr b => inner (g b)
                 end
                )
    end.

Notation "a ⊕ b" := (naddOrd a b) (at level 45, right associativity) : ord_scope.

Lemma naddOrd_unfold (x y:Ord) :
  x ⊕ y =
    (limOrd (fun a:x => x a ⊕ y))
    ⊔
    (limOrd (fun b:y => x ⊕ y b)).
Proof.
  destruct x; destruct y; auto.
Qed.

Global Opaque naddOrd.

Lemma naddOrd_le1 x y : x ≤ x ⊕ y.
Proof.
  induction x as [A f Hx].
  destruct y as [B g].
  rewrite naddOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite ord_lt_unfold.
  simpl.
  exists (inl a).
  auto.
Qed.

Lemma naddOrd_le2 x y : y ≤ x ⊕ y.
Proof.
  induction y as [A f Hx].
  destruct x as [B g].
  rewrite naddOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite ord_lt_unfold.
  exists (inr a).
  apply Hx.
Qed.

Lemma naddOrd_zero x : x ≈ x ⊕ 0.
Proof.
  split.
  - induction x as [A f].
    rewrite naddOrd_unfold.
    simpl.
    rewrite ord_le_unfold; simpl; intros.
    rewrite ord_lt_unfold.
    exists (inl a).
    apply H.
  - induction x as [A f].
    rewrite naddOrd_unfold.
    rewrite ord_le_unfold; simpl; intros.
    destruct a; intuition.
    rewrite ord_lt_unfold.
    exists a.
    auto.
Qed.

Lemma naddOrd_comm_le x y : x ⊕ y ≤ y ⊕ x.
Proof.
  revert y.
  induction x as [A f Hx].
  intro y. revert A f Hx.
  induction y as [B g Hy]; intros.
  rewrite ord_le_unfold. rewrite naddOrd_unfold.
  simpl; intros.
  destruct a.
  - rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    simpl.
    exists (inr a); auto.
  - rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    exists (inl b).
    apply Hy. auto.
Qed.

Lemma naddOrd_comm x y : x ⊕ y ≈ y ⊕ x.
Proof.
  split; apply naddOrd_comm_le; auto.
Qed.

Lemma naddOrd_assoc1 : forall x y z,  x ⊕ (y ⊕ z) ≤ (x ⊕ y) ⊕ z.
Proof.
  induction x as [A f]. induction y as [B g]. induction z as [C h].
  rewrite ord_le_unfold.
  rewrite naddOrd_unfold.
  rewrite naddOrd_unfold.
  simpl.
  intros.
  rewrite ord_lt_unfold.
  rewrite naddOrd_unfold.
  rewrite naddOrd_unfold.
  simpl in *.
  destruct a as [a|[b|c]].
  - exists (inl (inl a)).
    generalize (H a (ord B g) (ord C h)).
    rewrite (naddOrd_unfold (ord B g) (ord C h)); simpl; auto.
  - exists (inl (inr b)).
    apply H0.
  - exists (inr c).
    apply H1.
Qed.

Lemma naddOrd_assoc2 : forall x y z, (x ⊕ y) ⊕ z ≤ x ⊕ (y ⊕ z).
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  rewrite ord_le_unfold.
  rewrite naddOrd_unfold.
  rewrite naddOrd_unfold.
  simpl; intros.
  rewrite ord_lt_unfold.
  rewrite naddOrd_unfold.
  rewrite naddOrd_unfold.
  simpl.
  destruct a as [[a|b]|c].
  - exists (inl a).
    apply H.
  - exists (inr (inl b)).
    apply H0.
  - exists (inr (inr c)).
    apply H1.
Qed.

Lemma naddOrd_assoc : forall x y z,  x ⊕ (y ⊕ z) ≈ (x ⊕ y) ⊕ z.
Proof.
  intros; split.
  apply naddOrd_assoc1.
  apply naddOrd_assoc2.
Qed.

Lemma naddOrd_cancel :
  forall x y z, naddOrd x z < naddOrd y z -> x < y.
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  rewrite ord_lt_unfold.
  rewrite naddOrd_unfold.
  rewrite ord_lt_unfold.
  simpl.
  intros [[b|c] ?].
  - exists b.
    rewrite ord_le_unfold. intros.
    rewrite ord_le_unfold in H2.
    rewrite naddOrd_unfold in H2.
    specialize (H2 (inl a)).
    simpl in H2.
    eapply H. apply H2.
  - rewrite ord_le_unfold in H2.
    rewrite naddOrd_unfold in H2.
    specialize (H2 (inr c)).
    simpl in H2.
    apply H1 in H2.
    rewrite ord_lt_unfold in H2.
    auto.
Qed.

Lemma naddOrd_monotone :
  forall x y z1 z2, x ≤ y -> z1 ≤ z2 -> x ⊕ z1 ≤ y ⊕ z2.
Proof.
  induction x as [A f]. destruct y as [B g]. induction z1 as [C h]. destruct z2.
  intros.
  rewrite ord_le_unfold.
  rewrite naddOrd_unfold.
  simpl.
  intros [a|c].
  - rewrite ord_le_unfold in H1.
    specialize (H1 a).
    rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    simpl.
    rewrite ord_lt_unfold in H1.
    destruct H1 as [b Hb].
    exists (inl b).
    apply H; auto.
  - rewrite ord_le_unfold in H2.
    specialize (H2 c).
    rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    rewrite ord_lt_unfold in H2.
    simpl.
    destruct H2 as [a Ha].
    exists (inr a).
    apply H0; auto.
Qed.

Lemma naddOrd_increasing_both :
  forall x y z1 z2, (x < y -> z1 ≤ z2 -> x ⊕ z1 < y ⊕ z2) /\
                    (x ≤ y -> z1 < z2 -> x ⊕ z1 < y ⊕ z2).
Proof.
  induction x as [A f Hx].
  induction y as [B g Hy].
  induction z1 as [C h Hz1].
  destruct z2 as [D i].
  split; intros.
  - rewrite ord_lt_unfold in H.
    destruct H as [a Ha].
    rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    simpl.
    exists (inl a).
    rewrite ord_le_unfold.
    rewrite naddOrd_unfold.
    simpl.
    intros.
    destruct a0.
    + rewrite ord_le_unfold in Ha; auto.
      destruct (Hx a0 (g a) (ord C h) (ord D i)); auto.
    + rewrite ord_le_unfold in H0.
      specialize (H0 c).
      apply Hy; auto.
  - rewrite ord_lt_unfold in H0.
    destruct H0 as [q Hq].
    rewrite ord_lt_unfold.
    rewrite naddOrd_unfold.
    simpl.
    exists (inr q).
    rewrite ord_le_unfold.
    rewrite naddOrd_unfold.
    simpl.
    intros.
    destruct a as [a|c].
    + rewrite ord_le_unfold in H.
      specialize (H a).
      destruct (Hx a (ord B g) (ord C h) (i q)).
      auto.
    + rewrite ord_le_unfold in Hq.
      specialize (Hq c).
      destruct (Hz1 c (i q)).
      auto.
Qed.

Lemma naddOrd_increasing1 :
  forall x y z, x < y -> x ⊕ z < y ⊕ z.
Proof.
  intros.
  destruct (naddOrd_increasing_both x y z z).
  apply H0; auto.
  apply ord_le_refl.
Qed.

Lemma naddOrd_increasing2 :
  forall x y z, x < y -> z ⊕ x < z ⊕ y.
Proof.
  intros.
  destruct (naddOrd_increasing_both z z x y).
  apply H1; auto.
  apply ord_le_refl.
Qed.

Lemma naddOrd_least (f:Ord -> Ord -> Ord)
  (Hmono1 : forall a b c, a < b -> f a c < f b c)
  (Hmono2 : forall a b c, a < b -> f c a < f c b)
  :
  (forall x y, x ⊕ y ≤ f x y).
Proof.
  induction x as [A fa].
  induction y as [B g].
  rewrite ord_le_unfold.
  rewrite naddOrd_unfold.
  simpl.
  intros [a|b].
  - eapply ord_le_lt_trans; [ apply H | auto with ord ].
  - eapply ord_le_lt_trans; [ apply H0 | auto with ord ].
Qed.

Lemma naddOrd_succ x y : succOrd x ⊕ y ≈ succOrd (x ⊕ y).
Proof.
  split.
  - induction y as [B g Hy].
    rewrite ord_le_unfold.
    rewrite naddOrd_unfold.
    simpl.
    intro ua.
    rewrite ord_lt_unfold. simpl.
    exists tt.
    destruct ua as [u|a].
    + apply ord_le_refl.
    + rewrite Hy.
      apply succ_least.
      apply naddOrd_increasing2; auto with ord.
  - apply succ_least.
    apply naddOrd_increasing1.
    apply succ_lt.
Qed.

Lemma naddOrd_succ2 x y : x ⊕ succOrd y ≈ succOrd (x ⊕ y).
Proof.
  rewrite naddOrd_comm.
  rewrite naddOrd_succ.
  rewrite naddOrd_comm.
  reflexivity.
Qed.

Add Parametric Morphism : naddOrd with signature
    ord_le ++> ord_le ++> ord_le as naddOrd_le_mor.
Proof.
  intros. apply naddOrd_monotone; auto.
Qed.

Add Parametric Morphism : naddOrd with signature
    ord_lt ++> ord_le ++> ord_lt as naddOrd_lt_mor1.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply naddOrd_increasing1; eauto.
  apply naddOrd_monotone; auto.
  reflexivity.
Qed.

Add Parametric Morphism : naddOrd with signature
    ord_le ++> ord_lt ++> ord_lt as naddOrd_lt_mor2.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply naddOrd_increasing2; eauto.
  apply naddOrd_monotone; auto.
  reflexivity.
Qed.

Add Parametric Morphism : naddOrd with signature
   ord_eq ==> ord_eq ==> ord_eq as naddOrd_eq_mor.
Proof.
  intros; split; apply naddOrd_le_mor; solve [apply H|apply H0].
Qed.
