Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.

Unset Printing Records.

From Ordinal Require Import Defs.

(** * Ordinal operators *)

(** The zero ordinal, which is indexed by the empty type False *)
Definition zeroOrd : Ord := ord False (False_rect _).

(** The successor ordinal, which is indexed by the unit type *)
Definition succOrd (x:Ord) : Ord := ord unit (fun _ => x).

(* Set up numeric notation for ordinals *)
Number Notation Ord Nat.of_num_uint Nat.to_num_uint
         (via nat mapping [zeroOrd => O, succOrd => S]) : ord_scope.

Definition oneOrd := succOrd zeroOrd.

Definition limOrd {A:Type} (f:A -> Ord) := ord A f.

(** The binary upper bound of two ordinals is constructed using a sum type
   over the indices of the two incomming ordinals *)
Definition lubOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A+B) (fun ab => match ab with inl a => f a | inr b => g b end)
  end.
Notation "x ⊔ y" := (lubOrd x y) (at level 55, right associativity) : ord_scope.

(** The supremum of a collection of ordinals is indexed by a sigma type. *)
Definition supOrd {A:Type} (f:A -> Ord) :=
  ord (sigT (fun a => ordCarrier (f a)))
      (fun ai => ordSize (f (projT1 ai)) (projT2 ai)).

(** The binary greatest lower bound of two ordinals is indexed by a pair, and
   we essentially simultaneously play the game represented by the two ordinals.
  *)
Fixpoint glbOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A*B) (fun ab => glbOrd (f (fst ab)) (g (snd ab)))
  end.
Notation "x ⊓ y" := (glbOrd x y) (at level 55, right associativity) : ord_scope.

(** It does not appear to be possible to construct the infimum of an infinite
    collection of ordinals. This would essentially compute the least ordinal
    among a collection.  One is tempted to make the index type of this ordinal
    a dependent function (representing an element of each of the index sets of
    the collection; but I have not been able to figure out how to make it work.
 *)

(* Natural numbers have an ordinal size.
 *)
Fixpoint natOrdSize (x:nat) :=
  match x with
  | O => zeroOrd
  | S n => succOrd (natOrdSize n)
  end.

Canonical Structure ω : Ord :=
  ord nat natOrdSize.

(** We can constructed the supremum of the image of a function on ordinals,
    when applied to all the ordinals strictly below β.
  *)
Definition boundedSup (β:Ord) (f:Ord -> Ord) : Ord :=
  match β with
  | ord B g => supOrd (fun i => f (g i))
  end.

(** The predecessor of an ordinal is the supremum of all the ordinals
    strictly below it.  This function is stationary on limit ordinals
    (and zero) but undoes the action of a successor.
  *)
Definition predOrd (x:Ord) : Ord :=
  match x with
  | ord A f => supOrd f
  end.

(** A "complete" ordinal is one which is directed, in an order-theoretic
    sense, and for which all its subordinals are also complete.

    This is a technical property that appears necessary in some later proofs.
    In a classical seetting all ordinals would have this property.
  *)
Fixpoint complete (x:Ord) : Prop :=
  match x with
  | ord A f =>
    (forall a1 a2, exists a', f a1 <= f a' /\ f a2 <= f a') /\
    (inhabited A \/ ~inhabited A) /\
    (forall a, complete (f a))
  end.


Lemma complete_subord o :
  complete o -> forall i, complete (o i).
Proof.
  destruct o as [A f]; simpl; intuition.
Qed.

Lemma complete_zeroDec o :
  complete o -> o <= zeroOrd \/ zeroOrd < o.
Proof.
  destruct o as [A f]; simpl; intuition.
  - right.
    destruct H1 as [a].
    rewrite ord_lt_unfold. exists a.
    rewrite ord_le_unfold; simpl; intuition.
  - left.
    rewrite ord_le_unfold. intro a.
    elim H1. exact (inhabits a).
Qed.

Lemma complete_directed o :
  complete o ->
  forall a1 a2, exists a',
      o a1 <= o a' /\
      o a2 <= o a'.
Proof.
  destruct o as [A f]; simpl; intuition.
Qed.

Definition strongly_continuous (s:Ord -> Ord) :=
  forall A (f:A -> Ord) (a0:A), s (supOrd f) ≤ supOrd (fun i:A => s (f i)).

(** Zero is the least ordinal. *)
Lemma zero_least : forall o, 0 ≤ o.
Proof.
  intros. rewrite ord_le_unfold.
  simpl. intros [].
Qed.

Lemma zero_complete : complete 0.
Proof.
  hnf; simpl; intuition.
  right. intros [H]; auto.
Qed.

(** Succ is a monotone operator with respetct to both lt and le, and
  * is strictly above its argument.
  *
  * Moreover, it is the smallest ordinal which is strictly above its
  * argument.
  *)
Lemma succ_lt : forall o, o < succOrd o.
Proof.
  intros.
  rewrite ord_lt_unfold. simpl. exists tt. apply ord_le_refl.
Qed.

Lemma succ_least : forall x y, x < y -> succOrd x ≤ y.
Proof.
  intros.
  rewrite ord_le_unfold. simpl; auto.
Qed.

Lemma succ_monotone_lt : forall a b, a < b -> succOrd a < succOrd b.
Proof.
  intros.
  apply ord_le_lt_trans with b.
  apply succ_least; auto.
  apply succ_lt.
Qed.

Lemma succ_monotone_le : forall a b, a ≤ b -> succOrd a ≤ succOrd b.
Proof.
  intros.
  apply succ_least.
  apply ord_le_lt_trans with b; auto.
  apply succ_lt.
Qed.

Lemma succ_congruence : forall a b, a ≈ b -> succOrd a ≈ succOrd b.
Proof.
  unfold ord_eq; intuition; apply succ_monotone_le; auto.
Qed.

Add Parametric Morphism : succOrd with signature
    ord_le ++> ord_le as succOrd_le_mor.
Proof.
  intros; apply succ_monotone_le; auto.
Qed.

Add Parametric Morphism : succOrd with signature
    ord_lt ++> ord_lt as succOrd_lt_mor.
Proof.
  intros; apply succ_monotone_lt; auto.
Qed.

Add Parametric Morphism : succOrd with signature
    ord_eq ==> ord_eq as succOrd_eq_mor.
Proof.
  intros; apply succ_congruence; auto.
Qed.

Lemma succ_complete :forall o, complete o -> complete (succOrd o).
Proof.
  intros; hnf; simpl; intuition.
  - exists tt; split; reflexivity.
  - left; exact (inhabits tt).
Qed.

(** The supremum is nonstrictly above all the ordinals in the
  * collection defined by "f".  Morover it is it the smallest such.
  *)
Lemma sup_le : forall A (f:A -> Ord) a, f a ≤ supOrd f.
Proof.
  intros.
  rewrite ord_le_unfold.
  intro b.
  rewrite ord_lt_unfold.
  exists (@existT A (fun a => ordCarrier (f a)) a b).
  simpl.
  apply ord_le_refl.
Qed.

Lemma sup_least : forall A (f:A -> Ord) z,
    (forall a, f a ≤ z) -> supOrd f ≤ z.
Proof.
  intros.
  rewrite ord_le_unfold.
  simpl; intros.
  destruct a as [a b]. simpl.
  specialize (H a).
  rewrite ord_le_unfold in H.
  apply H.
Qed.

Instance sup_ord_le_morphism (A:Type) :
  Proper (pointwise_relation _ ord_le ==> ord_le) (@supOrd A).
Proof.
  repeat intro.
  red in H.
  apply sup_least. intro.
  rewrite H.
  apply sup_le.
Qed.

Instance sup_ord_eq_morphism (A:Type) :
  Proper (pointwise_relation _ ord_eq ==> ord_eq) (@supOrd A).
Proof.
  repeat intro.
  split.
  red in H.
  apply sup_ord_le_morphism; red; intros; apply H.
  apply sup_ord_le_morphism; red; intros; apply H.
Qed.


(** The limit ordinal is strictly above all the ordinals in
  * the collection defined by "f".  Moreover it is the smallest
  * such.
  *)
Lemma limit_lt : forall A (f:A -> Ord) i, f i < limOrd f.
Proof.
  intros. rewrite ord_lt_unfold. simpl.
  exists i. apply ord_le_refl.
Qed.

Lemma limit_least : forall A (f:A -> Ord) z,
  (forall i, f i < z) -> limOrd f ≤ z.
Proof.
  intros. rewrite ord_le_unfold.
  simpl. auto.
Qed.

Global Hint Resolve limit_lt sup_le : ord.

(** Supremum and limit are closely related operations.
  We always have: sup f <= lim f <= succ (sup f).
  Moreover: lim f = sup (succ . f)
  When f is an ascending set, lim f = sup f
  When f has a maximal element, lim f = succ (sup f)
*)
Lemma sup_lim : forall A (f:A -> Ord),
  supOrd f ≤ limOrd f.
Proof.
  intros.
  apply sup_least.
  intros.
  apply ord_lt_le.
  apply limit_lt.
Qed.

Lemma lim_sup : forall A (f:A -> Ord),
  limOrd f ≤ succOrd (supOrd f).
Proof.
  intros.
  apply limit_least. intro a.
  apply ord_le_lt_trans with (supOrd f).
  apply sup_le.
  apply succ_lt.
Qed.

Lemma sup_succ_lim : forall A (f:A -> Ord),
  limOrd f ≈ supOrd (fun a:A => succOrd (f a)).
Proof.
  intros.
  split.
  - apply limit_least. intros.
    rewrite ord_lt_unfold.
    simpl.
    exists (existT _ i tt).
    simpl.
    apply ord_le_refl.
  - apply sup_least.
    intros.
    apply succ_least.
    apply limit_lt.
Qed.

Lemma ascending_sup_lim : forall A (f:A -> Ord),
  ascendingSet A f ->
  limOrd f ≈ supOrd f.
Proof.
  intros.
  split; [ | apply sup_lim ].
  apply limit_least. intro a.
  destruct (H a) as [a' ?].
  apply ord_lt_le_trans with (f a'); auto with ord.
Qed.

Lemma succ_sup_lim : forall A (f:A -> Ord),
  hasMaxElement A f ->
  limOrd f ≈ succOrd (supOrd f).
Proof.
  intros.
  split; [ apply lim_sup |].
  apply succ_least.
  destruct H as [amax Hamax].
  rewrite ord_lt_unfold. simpl. exists amax.
  apply sup_least. auto.
Qed.

Instance lim_ord_le_morphism (A:Type) :
  Proper (pointwise_relation _ ord_le ==> ord_le) (@limOrd A).
Proof.
  repeat intro.
  apply limit_least. intros.
  red in H. rewrite H.
  apply limit_lt.
Qed.

Instance lim_ord_eq_morphism (A:Type) :
  Proper (pointwise_relation _ ord_eq ==> ord_eq) (@limOrd A).
Proof.
  repeat intro.
  split; apply lim_ord_le_morphism;
    red; intros; apply H.
Qed.

(** Provided f is a monotone function, boundedSup β f
    is an upper bound of f α whenever a < β.  Moreover, it
    is the smallest ordinal with this property.
  *)
Lemma boundedSup_le β (f:Ord -> Ord) :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x, x < β -> f x ≤ boundedSup β f.
Proof.
  intro Hmono.
  destruct β as [B g].
  simpl; intros.
  rewrite ord_lt_unfold in H.
  destruct H as [b Hb].
  rewrite <- (sup_le _ _ b).
  apply Hmono. apply Hb.
Qed.

Lemma boundedSup_least β (f:Ord -> Ord) z :
  (forall x, x < β -> f x ≤ z) ->
  boundedSup β f ≤ z.
Proof.
  destruct β as [B g]. simpl. intros.
  apply sup_least.
  intros. apply H.
  apply (index_lt (ord B g)).
Qed.

(** ω is the smallest limit ordinal *)
Lemma omega_limit : limitOrdinal ω.
Proof.
  simpl. split.
  - exact (inhabits 0%nat).
  - hnf; intros.
    exists (S a).
    simpl.
    apply succ_lt.
Qed.

Lemma omega_least : forall x, limitOrdinal x -> ω <= x.
Proof.
  intros.
  destruct x as [A f]; simpl in *.
  rewrite ord_le_unfold.
  simpl; intro.
  destruct H as [[q] H].
  rewrite ord_lt_unfold; simpl.
  induction a; simpl.
  - exists q. apply zero_least.
  - destruct IHa as [r Hr].
    destruct (H r) as [s Hs].
    exists s.
    apply succ_least.
    apply ord_le_lt_trans with (f r); auto.
Qed.

Lemma natOrdSize_monotone : forall i j, (i<=j)%nat -> natOrdSize i <= natOrdSize j.
Proof.
 intros i j H; induction H; simpl.
  - reflexivity.
  - rewrite IHle. apply ord_lt_le. apply succ_lt.
Qed.

Lemma omega_complete : complete ω.
Proof.
  hnf; simpl; repeat split.
  - intros.
    exists (Nat.max a1 a2); split; apply natOrdSize_monotone.
    + apply PeanoNat.Nat.le_max_l.
    + apply PeanoNat.Nat.le_max_r.
  - left. exact (inhabits 0%nat).
  - induction a.
    + apply zero_complete.
    + apply succ_complete; auto.
Qed.

(** Any zero ordinal is equal to the distinguished zeroOrd *)
Lemma ord_isZero z : zeroOrdinal z <-> z ≈ 0.
Proof.
  split.
  - intro. split.
    + destruct z as [Z f].
      rewrite ord_le_unfold. intro a; elim (H a).
    + apply zero_least.
  - repeat intro.
    destruct z as [Z f].
    simpl. intro a.
    destruct H as [H1 H2].
    rewrite ord_le_unfold in H1.
    generalize (H1 a).
    rewrite ord_lt_unfold.
    simpl; intros [[] _].
Qed.

(** Any successor ordinal is equal to some application of succOrd. *)
Lemma ord_isSucc x : successorOrdinal x <-> exists o, x ≈ succOrd o.
Proof.
  split.
  - intros.
    destruct x as [A f].
    destruct H as [a Ha].
    exists (f a).
    split.
    + rewrite ord_le_unfold. simpl; intro a'.
      apply ord_le_lt_trans with (f a); auto.
      apply succ_lt.
    + apply succ_least.
      apply (index_lt (ord A f)).
  - intros [o Ho].
    destruct Ho as [Ho1 Ho2].
    destruct x as [A f].
    simpl. hnf.
    rewrite ord_le_unfold in Ho2.
    specialize (Ho2 tt).
    rewrite ord_lt_unfold in Ho2.
    destruct Ho2 as [a Ha].
    exists a. simpl in Ha.
    intros.
    rewrite ord_le_unfold in Ho1.
    specialize (Ho1 a'). rewrite ord_lt_unfold in Ho1.
    destruct Ho1 as [z Hz]. simpl in *.
    transitivity o; auto.
Qed.

Lemma ord_isLimit β : limitOrdinal β -> β ≈ boundedSup β (fun a => a).
Proof.
  destruct β as [B g]; simpl.
  intros [_ Hb].
  rewrite <- ascending_sup_lim; auto.
  reflexivity.
Qed.


Lemma ord_isLimit' β : zeroOrd < β -> β ≈ boundedSup β (fun a => a) -> limitOrdinal β.
Proof.
  destruct β as [B g]; simpl.
  intros H Heq ; split.
  - rewrite ord_lt_unfold in H.
    destruct H as [b ?].
    exact (inhabits b).
  - red. intro a.
    destruct Heq as [Hle1 Hle2].
    rewrite ord_le_unfold in Hle1.
    generalize (Hle1 a).
    simpl; intros.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [a' ?]. simpl in *.
    destruct a'. simpl in *.
    exists x.
    rewrite ord_lt_unfold. exists o. auto.
Qed.

(** pred(y) is the smallest ordinal that is (nonstrictly) above
  * all the ordinals (strictly) below y.
  *)
Lemma pred_le y :
  forall x, x < y -> x ≤ predOrd y.
Proof.
  intros.
  destruct y as [B g]; simpl in *.
  rewrite ord_lt_unfold in H.
  destruct H as [b Hb]. simpl in *.
  rewrite Hb.
  apply sup_le.
Qed.

Lemma pred_least y z :
  (forall x, x < y -> x ≤ z) ->
  predOrd y ≤ z.
Proof.
  intros.
  destruct y as [B g]. simpl.
  apply sup_least. intros.
  apply H; auto with ord.
Qed.

Lemma pred_zero : zeroOrd ≈ predOrd zeroOrd.
Proof.
  split.
  - apply zero_least.
  - apply pred_least.
    intros.
    rewrite ord_lt_unfold in H.
    destruct H. destruct x0.
Qed.

Lemma pred_successor x : successorOrdinal x -> predOrd x < x.
Proof.
  destruct x as [A f]; simpl; intros.
  rewrite ord_lt_unfold.
  red in H. simpl in *.
  destruct H as [a Ha].
  exists a. apply sup_least. auto.
Qed.

Lemma pred_limit x : limitOrdinal x -> x ≈ predOrd x.
Proof.
  intros.
  split.
  - destruct x as [A f].
    rewrite ord_le_unfold. simpl; intro a.
    destruct H as [_ H].
    destruct (H a) as [a' ?].
    rewrite <- (sup_le _ _ a'). auto.
  - apply pred_least.
    apply ord_lt_le.
Qed.

Lemma pred_succ x : x ≈ predOrd (succOrd x).
Proof.
  split.
  - apply pred_le. apply succ_lt.
  - apply pred_least. intros.
    rewrite ord_lt_unfold in H. simpl in *.
    destruct H. auto.
Qed.

Lemma succ_pred x : x ≤ succOrd (predOrd x).
Proof.
  rewrite ord_le_unfold. intros.
  rewrite ord_lt_unfold. simpl. exists tt.
  apply pred_le; auto with ord.
Qed.

Lemma succ_pred' x : successorOrdinal x -> x ≈ succOrd (predOrd x).
Proof.
  intros.
  split.
  - apply succ_pred.
  - apply succ_least; apply pred_successor; auto.
Qed.

Add Parametric Morphism : predOrd with signature
    ord_le ++> ord_le as pred_le_mor.
Proof.
  intros.
  apply pred_least. intros.
  apply pred_le.
  rewrite <- H.
  auto.
Qed.

Add Parametric Morphism : predOrd with signature
    ord_eq ==> ord_eq as pred_eq_mor.
Proof.
  intros; split; apply pred_le_mor; apply H.
Qed.


(** glb is the greatest lower bound of its arguments.
 *)
Lemma glb_le1 : forall x y, x ⊓ y ≤ x.
Proof.
  induction x as [A f Hx]. destruct y as [B g]. simpl.
  rewrite ord_le_unfold; simpl.
  intros [a b]; simpl.
  rewrite ord_lt_unfold; simpl.
  exists a. apply Hx.
Qed.

Lemma glb_le2 : forall y x, x ⊓ y ≤ y.
Proof.
  induction y as [B g Hy]. destruct x as [A f]. simpl.
  rewrite ord_le_unfold; simpl.
  intros [a b]; simpl.
  rewrite ord_lt_unfold; simpl.
  exists b. apply Hy.
Qed.

Lemma glb_greatest : forall z x y, z ≤ x -> z ≤ y -> z ≤ x ⊓ y.
Proof.
  induction z as [C h Hz]; simpl; intros.
  rewrite ord_le_unfold; simpl; intro c.
  rewrite ord_le_unfold in H.
  rewrite ord_le_unfold in H0.
  destruct x as [A f].
  destruct y as [B g].
  specialize (H c).
  specialize (H0 c).
  simpl.
  rewrite ord_lt_unfold in H.
  rewrite ord_lt_unfold in H0.
  destruct H as [a Ha].
  destruct H0 as [b Hb].
  simpl in *.
  rewrite ord_lt_unfold.
  simpl.
  exists (a,b). simpl.
  apply Hz; auto.
Qed.

Lemma glb_complete : forall x y, complete x -> complete y -> complete (x ⊓ y).
Proof.
  induction x as [X f Hx].
  destruct y as [Y g].
  simpl. intros [Hx1 [Hx2 Hx3]] [Hy1 [Hy2 Hy3]]; repeat split.
  - intros [x1 y1] [x2 y2].
    destruct (Hx1 x1 x2) as [x' [Hx'1 Hx'2]].
    destruct (Hy1 y1 y2) as [y' [Hy'1 Hy'2]].
    exists (x',y'). split; simpl.
    + apply glb_greatest.
      * rewrite glb_le1. auto.
      * rewrite glb_le2. auto.
    + apply glb_greatest.
      * rewrite glb_le1. auto.
      * rewrite glb_le2. auto.
  - destruct Hx2 as [[x]|Hx2].
    + destruct Hy2 as [[y]|Hy2].
      * left. exact (inhabits (x,y)).
      * right; intros [[x' y']]; auto.
    + right; intros [[x' y']]; auto.
  - intros [x y]. simpl.
    apply Hx; auto.
Qed.


Add Parametric Morphism : glbOrd with signature
    ord_le ++> ord_le ++> ord_le as ord_glb_le_mor.
Proof.
  intros.
  apply glb_greatest.
  - rewrite <- H.
    apply glb_le1.
  - rewrite <- H0.
    apply glb_le2.
Qed.

Add Parametric Morphism : glbOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as ord_glb_eq_mor.
Proof.
  unfold ord_eq.
  intros; split; apply ord_glb_le_mor; intuition.
Qed.

(** lub is the least upper bound of its arguments.
  *)
Lemma lub_le1 : forall x y, x ≤ x ⊔ y.
Proof.
  intros. rewrite ord_le_unfold.
  intros.
  destruct x; destruct y; simpl.
  rewrite ord_lt_unfold.
  simpl.
  exists (inl a).
  apply ord_le_refl.
Qed.

Lemma lub_le2 : forall x y, y ≤ x ⊔ y.
Proof.
  intros. rewrite ord_le_unfold.
  destruct x; destruct y; simpl.
  intros.
  rewrite ord_lt_unfold.
  exists (inr a).
  apply ord_le_refl.
Qed.

Lemma lub_least x y z :
  x ≤ z -> y ≤ z -> x ⊔ y ≤ z.
Proof.
  repeat rewrite ord_le_unfold.
  destruct x as [A f]; destruct y as [B g]; simpl; intros.
  rewrite ord_lt_unfold.
  destruct z as [C h]; simpl.
  destruct a as [a|b].
  - specialize (H a).
    rewrite ord_lt_unfold in H.
    destruct H as [c ?]. exists c.
    simpl. auto.
  - specialize (H0 b).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [c ?].
    exists c. simpl. auto.
Qed.

(** lubOrd is a commutative, associative operator
  *)
Lemma lub_le_comm : forall x y, x ⊔ y ≤ y ⊔ x.
Proof.
  intros.
  apply lub_least.
  apply lub_le2.
  apply lub_le1.
Qed.

Lemma lub_le_assoc1 : forall x y z,
    x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z.
Proof.
  intros.
  apply lub_least.
  apply ord_le_trans with (lubOrd x y).
  apply lub_le1.
  apply lub_le1.
  apply lub_least.
  apply ord_le_trans with (lubOrd x y).
  apply lub_le2.
  apply lub_le1.
  apply lub_le2.
Qed.

Lemma lub_le_assoc2 : forall x y z,
    (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z).
Proof.
  intros.
  apply lub_least.
  apply lub_least.
  apply lub_le1.
  apply ord_le_trans with (lubOrd y z).
  apply lub_le1.
  apply lub_le2.
  apply ord_le_trans with (lubOrd y z).
  apply lub_le2.
  apply lub_le2.
Qed.

Lemma lubOrd_monotone a b c d :
  a ≤ c -> b ≤ d -> a ⊔ b ≤ c ⊔ d.
Proof.
  intros.
  apply lub_least.
  apply ord_le_trans with c; auto.
  apply lub_le1.
  apply ord_le_trans with d; auto.
  apply lub_le2.
Qed.


Add Parametric Morphism : lubOrd with signature
    ord_le ++> ord_le ++> ord_le as ord_lub_le_mor.
Proof.
  intros.
  apply lub_least.
  - rewrite H.
    apply lub_le1.
  - rewrite H0.
    apply lub_le2.
Qed.


Add Parametric Morphism : lubOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as ord_lub_eq_mor.
Proof.
  unfold ord_eq.
  intros; split; apply ord_lub_le_mor; intuition.
Qed.


(**  The lub of successors is <= the successor of the lub.
  *)
Lemma succ_lub x y :
 succOrd x ⊔ succOrd y ≤ succOrd (x ⊔ y).
Proof.
  apply lub_least.
  - apply succ_monotone_le.
    apply lub_le1.
  - apply succ_monotone_le.
    apply lub_le2.
Qed.