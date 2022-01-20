Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.

Open Scope ord_scope.

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


(** * Natural multiplication *)

Fixpoint nmulOrd (x:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match x, y with
    | ord A f, ord B g =>
      (supOrd (fun a:A => nmulOrd (f a) y ⊕ y))
      ⊔
      (supOrd (fun b:B => inner (g b) ⊕ x))
    end.

Notation "a ⊗ b" := (nmulOrd a b) (at level 35, right associativity) : ord_scope.

Lemma nmulOrd_unfold (x y:Ord) :
  x ⊗ y =
    (supOrd (fun a:x => x a ⊗ y ⊕ y))
    ⊔
    (supOrd (fun b:y => x ⊗ y b ⊕ x)).
Proof.
  destruct x; destruct y; auto.
Qed.

Global Opaque nmulOrd.

Lemma nmulOrd_comm_le : forall x y,
  x ⊗ y ≤ y ⊗ x.
Proof.
  induction x as [A f]. induction y as [B g].
  rewrite nmulOrd_unfold.
  apply lub_least.
  - apply sup_least; intro a. simpl.
    rewrite H.
    rewrite (nmulOrd_unfold (ord B g) (ord A f)).
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ a).
    auto with ord.
  - apply sup_least; intro b. simpl.
    rewrite H0.
    rewrite (nmulOrd_unfold (ord B g) (ord A f)).
    rewrite <- lub_le1.
    rewrite <- (sup_le _ _ b).
    auto with ord.
Qed.

Lemma nmulOrd_comm x y :
  x ⊗ y ≈ y ⊗ x.
Proof.
  split; apply nmulOrd_comm_le; auto.
Qed.

Lemma nmulOrd_monotone : forall x y a b,
    a ≤ x -> b ≤ y -> a ⊗ b ≤ x ⊗ y.
Proof.
  induction x as [X f].
  induction y as [Y g].
  intros.
  rewrite (nmulOrd_unfold a b).
  apply lub_least.
  - apply sup_least; intro ai.
    rewrite (nmulOrd_unfold (ord X f) (ord Y g)).
    rewrite <- lub_le1.
    generalize (ord_le_subord _ _ H1 ai); intros [x Hx].
    rewrite <- (sup_le _ _ x).
    simpl.
    apply naddOrd_monotone; auto with ord.
  - apply sup_least; intro bi.
    rewrite (nmulOrd_unfold (ord X f) (ord Y g)).
    rewrite <- lub_le2.
    generalize (ord_le_subord _ _ H2 bi); intros [y Hy].
    rewrite <- (sup_le _ _ y).
    simpl.
    apply naddOrd_monotone; auto with ord.
Qed.

Lemma nmulOrd_increasing2 :
  forall x y z1 z2, x < y -> 0 < z1 -> z1 ≤ z2 -> x ⊗ z1 < y ⊗ z2.
Proof.
  intros x y z1 z2 Hxy Hz1 Hzs.
  rewrite ord_lt_unfold in Hxy.
  destruct Hxy as [b Hb].
  rewrite (nmulOrd_unfold y z2).
  rewrite <- lub_le1.
  rewrite <- (sup_le _ _ b).
  apply ord_lt_le_trans with (y b ⊗ z2 ⊕ 1).
  rewrite naddOrd_comm.
  rewrite naddOrd_succ.
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
  rewrite ord_lt_unfold; exists tt. simpl.
  apply nmulOrd_monotone; auto.
  apply naddOrd_monotone; auto with ord.
  rewrite <- Hzs.
  apply succ_least; auto.
Qed.

Lemma nmulOrd_increasing1 :
  forall x y z1 z2, x < y -> 0 < z1 -> z1 ≤ z2 -> z1 ⊗ x < z2 ⊗ y.
Proof.
  intros.
  rewrite (nmulOrd_comm z1 x).
  rewrite (nmulOrd_comm z2 y).
  apply nmulOrd_increasing2; auto.
Qed.

Add Parametric Morphism : nmulOrd with signature
    ord_le ++> ord_le ++> ord_le as nmulOrd_le_mor.
Proof.
  intros. apply nmulOrd_monotone; auto.
Qed.

Add Parametric Morphism : naddOrd with signature
   ord_eq ==> ord_eq ==> ord_eq as nmulOrd_eq_mor.
Proof.
  intros; split; apply naddOrd_le_mor; solve [apply H|apply H0].
Qed.

Lemma nmulOrd_stepl (x y:Ord) (i:x) :
  x i ⊗ y ⊕ y ≤ x ⊗ y.
Proof.
  rewrite (nmulOrd_unfold x y).
  rewrite <- lub_le1.
  rewrite <- (sup_le _ _ i).
  reflexivity.
Qed.

Lemma nmulOrd_stepr (x y:Ord) (i:y) :
  x ⊗ y i ⊕ x ≤ x ⊗ y.
Proof.
  rewrite (nmulOrd_unfold x y).
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ i).
  reflexivity.
Qed.

Lemma nmulOrd_zero x : x ⊗ 0 ≈ 0.
Proof.
  split; auto with ord.
  induction x as [X f].
  rewrite nmulOrd_unfold.
  apply lub_least.
  - apply sup_least; intro a.
    rewrite <- naddOrd_zero.
    apply H.
  - apply sup_least. intros [].
Qed.

Lemma nmulOrd_one x : x ⊗ 1 ≈ x.
Proof.
  induction x as [A f].
  rewrite nmulOrd_unfold.
  split.
  apply lub_least.
  apply sup_least. intro a.
  simpl.
  rewrite (H a).
  rewrite naddOrd_comm.
  rewrite naddOrd_succ.
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
  apply succ_least.
  apply (index_lt _ a).
  apply sup_least. simpl; intro.
  rewrite nmulOrd_zero.
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
  auto with ord.

  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ tt).
  simpl.
  rewrite nmulOrd_zero.
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
  auto with ord.
Qed.

Lemma nmulDistrib1 : forall x y z,
  x ⊗ (y ⊕ z) ≤ (x ⊗ y) ⊕ (x ⊗ z).
Proof.
  induction x as [x Hindx] using ordinal_induction.
  induction y as [y Hindy] using ordinal_induction.
  induction z as [z Hindz] using ordinal_induction.
  rewrite (nmulOrd_unfold x (y⊕z)).
  apply lub_least.
  + apply sup_least; intro i.
    rewrite (Hindx (x i)); auto with ord.
    transitivity ((x i ⊗ y ⊕ y) ⊕ (x i ⊗ z ⊕ z)).
    rewrite naddOrd_assoc.
    rewrite (naddOrd_comm _ y).
    rewrite naddOrd_assoc.
    rewrite (naddOrd_comm y _).
    repeat rewrite naddOrd_assoc.
    reflexivity.
    apply naddOrd_monotone; apply nmulOrd_stepl.
  + apply sup_least.
    rewrite (naddOrd_unfold y z). simpl.
    intros [i|i].
    * rewrite (Hindy (y i)); auto with ord.
      rewrite (naddOrd_comm _ x).
      rewrite naddOrd_assoc.
      apply naddOrd_monotone; auto with ord.
      rewrite naddOrd_comm.
      apply nmulOrd_stepr.
    * rewrite (Hindz (z i)); auto with ord.
      rewrite <- naddOrd_assoc.
      apply naddOrd_monotone; auto with ord.
      apply nmulOrd_stepr.
Qed.

Lemma nmulDistrib2 : forall a b y z x,
  a ≤ x -> b ≤ x ->
  (a ⊗ y) ⊕ (b ⊗ z) ≤ x ⊗ (y ⊕ z).
Proof.
  induction a as [a Hinda] using ordinal_induction.
  induction b as [b Hindb] using ordinal_induction.
  induction y as [y Hindy] using ordinal_induction.
  induction z as [z Hindz] using ordinal_induction.
  intros x Ha Hb.
  rewrite naddOrd_unfold.
  apply lub_least.
  - apply limit_least.
    rewrite (nmulOrd_unfold a y). simpl.
    intros [[i q]|[i q]]; simpl.
    + apply ord_lt_le_trans with ((a i ⊗ y ⊕ y) ⊕ b ⊗ z).
      apply naddOrd_increasing1. apply index_lt.
      clear q.



      rewrite (naddOrd_comm (a i ⊗ y) y).
      rewrite <- naddOrd_assoc.
      rewrite (Hinda (a i) (index_lt a i) b y z x).






Abort.
(* Not sure how to prove this... or if it is actually true.
   I haven't yet found an induction hypothesis that seems to work.
 *)


(** * Jacobsthal multiplication.
      This is the transfinite iteration of natural addition.
  *)

Fixpoint jmulOrd (a:Ord) (b:Ord) : Ord :=
    match b with
    | ord B g => supOrd (fun i:B => (jmulOrd a (g i)) ⊕ a)
    end.

Notation "a × b" := (jmulOrd a b) (at level 35, right associativity) : ord_scope.

Lemma jmulOrd_unfold (a:Ord) (b:Ord) :
  a × b =
  supOrd (fun i:b => a × (b i) ⊕ a).
Proof.
  destruct b as [B g]; simpl; auto.
Qed.

Lemma jmulOrd_monotone1 : forall z a b , a ≤ b -> a × z ≤ b × z.
Proof.
  induction z as [C h Hz].
  simpl; intros.
  apply sup_least. intro c. simpl.
  rewrite <- (sup_le _ _ c).
  apply naddOrd_monotone; auto.
Qed.

Lemma jmulOrd_monotone2 : forall b a z, b ≤ z -> a × b ≤ a × z.
Proof.
  induction b as [B g Hb].
  intros.
  destruct a as [A f]; simpl in *.
  apply sup_least. intro i.
  rewrite ord_le_unfold in H.
  specialize (H i).
  simpl in H.
  rewrite ord_lt_unfold in H.
  destruct H as [q ?].
  specialize (Hb i).
  generalize (Hb (ord A f) (z q) H).
  intros.
  rewrite (jmulOrd_unfold (ord A f) z).
  rewrite <- (sup_le _ _ q).
  rewrite H0. reflexivity.
Qed.

Lemma jmulOrd_increasing2 : forall a b c,
    0 < a ->
    b < c ->
    a × b < a × c.
Proof.
  intros a b [C h] Ha H.
  rewrite (jmulOrd_unfold a (ord C h)).
  simpl.
  rewrite ord_lt_unfold in H.
  destruct H as [c Hc]. simpl in Hc.
  rewrite <- (sup_le _ _ c).
  apply ord_le_lt_trans with (jmulOrd a (h c)); [ apply jmulOrd_monotone2 ; assumption | ].
  apply ord_le_lt_trans with (naddOrd (jmulOrd a (h c)) zeroOrd).
  - rewrite <- naddOrd_zero. reflexivity.
  - apply naddOrd_increasing2. auto.
Qed.

Add Parametric Morphism : jmulOrd with signature
    ord_le ++> ord_le ++> ord_le as jmulOrd_le_mor.
Proof.
  intros.
  apply ord_le_trans with (x × y0).
  apply jmulOrd_monotone2; auto.
  apply jmulOrd_monotone1; auto.
Qed.

Add Parametric Morphism : jmulOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as jmulOrd_eq_mor.
Proof.
  unfold ord_eq; intuition; apply jmulOrd_le_mor; auto.
Qed.


Lemma jmulOrd_zero_r : forall a, a × 0 ≈ 0.
Proof.
  intros; split.
  - destruct a as [A f]. simpl.
    apply sup_least. intuition.
  - apply zero_least.
Qed.

Lemma jmulOrd_zero_l : forall a, 0 × a ≈ 0.
Proof.
  induction a as [A f Ha].
  split; simpl.
  - apply sup_least; intro x.
    rewrite <- naddOrd_zero.
    apply Ha.
  - apply zero_least.
Qed.

Lemma jmulOrd_succ : forall a b, a × (succOrd b) ≈ (a × b) ⊕ a.
Proof.
  intros; split; simpl.
  - apply sup_least; auto with ord.
  - rewrite <- (sup_le _ _ tt); auto with ord.
Qed.

Lemma jmulOrd_one : forall a, a × 1 ≈ a.
Proof.
  intro.
  rewrite jmulOrd_succ.
  rewrite jmulOrd_zero_r.
  rewrite naddOrd_comm.
  rewrite <- naddOrd_zero.
  reflexivity.
Qed.

Lemma jmulOrd_positive : forall a b,
    zeroOrd < a ->
    zeroOrd < b ->
    zeroOrd < a × b.
Proof.
  intros.
  destruct a as [A f].
  destruct b as [B g].
  simpl.
  rewrite ord_lt_unfold in H.
  rewrite ord_lt_unfold in H0.
  destruct H as [a _].
  destruct H0 as [b _].
  simpl in *.
  rewrite <- (sup_le _ _ b).
  rewrite (naddOrd_zero 0).
  apply ord_le_lt_trans with (ord A f × g b ⊕ 0).
  apply naddOrd_le_mor; apply zero_least.
  apply naddOrd_increasing2.
  rewrite ord_lt_unfold. simpl.
  exists a.
  apply zero_least.
Qed.

Lemma jmulOrd_limit : forall a b,
    limitOrdinal b ->
    a × b ≈ supOrd (fun i:b => a × (b i)).
Proof.
  destruct b as [B g]; simpl; intros.
  split.
  - apply sup_least. intro b.
    destruct H as [_ H].
    destruct (H b) as [b' Hb'].
    rewrite <- (sup_le _ _ b').
    apply ord_le_trans with (jmulOrd a (succOrd (g b))).
    apply (jmulOrd_succ a (g b)).
    apply jmulOrd_monotone2.
    apply succ_least; auto.
  - apply sup_least. intro b.
    rewrite <- (sup_le _ _ b).
    apply naddOrd_le1.
Qed.

Lemma jmulOrd_continuous a : strongly_continuous (jmulOrd a).
Proof.
  red; simpl; intros.
  apply sup_least.
  intros [i q]. simpl.
  rewrite <- (sup_le _ _ i).
  rewrite (jmulOrd_unfold a (f i)).
  rewrite <- (sup_le _ _ q).
  reflexivity.
Qed.
