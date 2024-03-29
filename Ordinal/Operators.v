Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import ChoiceFacts.

Unset Printing Records.

From Ordinal Require Import Defs.

(** * Basic ordinal operators *)

(** The zero ordinal, which is indexed by the empty type False.
    This is the least ordinal. *)
Definition zeroOrd : Ord := ord False (False_rect _).

(** The successor ordinal, which is indexed by the unit type.
    It is the smallest ordinal strictly larger than its argument. *)
Definition succOrd (x:Ord) : Ord := ord unit (fun _ => x).

(* Set up numeric notation for ordinals. This allows us to use standard
   notations like @0@, @1@, @2@, etc. for finite ordinals. *)
Number Notation Ord Nat.of_num_uint Nat.to_num_uint
         (via nat mapping [zeroOrd => O, succOrd => S]) : ord_scope.

Definition limOrd {A:Type} (f:A -> Ord) := ord A f.

(** The binary upper bound of two ordinals is constructed using a sum type
   over the indices of the two argument ordinals. *)
Definition lubOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A+B) (fun ab => match ab with inl a => f a | inr b => g b end)
  end.
Notation "x ⊔ y" := (lubOrd x y) (at level 55, right associativity) : ord_scope.

(** The supremum of a collection of ordinals is indexed by a sigma type.
    This is the least ordinal that is (nonstrictly) above all the ordinals
    in the range of @f@. *)
Definition supOrd {A:Type} (f:A -> Ord) :=
  ord (sigT (fun a => ordCarrier (f a)))
      (fun ai => ordSize (f (projT1 ai)) (projT2 ai)).

(** We say that a function on ordinals is strongly continuous
    if it preserves all nonempty suprema. *)
Definition strongly_continuous (s:Ord -> Ord) :=
  forall A (f:A -> Ord) (a0:A), s (supOrd f) ≤ supOrd (fun i:A => s (f i)).

(** The binary greatest lower bound of two ordinals is indexed by a pair, and
    we essentially simultaneously play the game represented by the two ordinals.
  *)
Fixpoint glbOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A*B) (fun ab => glbOrd (f (fst ab)) (g (snd ab)))
  end.
Notation "x ⊓ y" := (glbOrd x y) (at level 55, right associativity) : ord_scope.

(**  We can even construct the greatest lower bound of a nonempty, infinite
     collection of ordinals. Here we demand the collection be nonempty by
     distinguishing a particular one separately; this element is ultimately
     what we do induction on.

     The index set of the recursively-defined ordinal is essentially a
     dependent function that choses a subelement of each element of
     the range of f.

     To show that this ordinal is the greatest lower bound, we require
     a choice principle to reify a proof of the form
     @forall x, exists y, ...@ into a function. If we stated the ordinal
     ordering realations to be informative (rather than in Prop), this
     choice principle would not be necessary.
 *)
Fixpoint infOrd_loop (x:Ord) : forall (A:Type) (f:A -> Ord), Ord :=
  fun A f =>
  match x with
  | ord B g =>
      ord (B * (forall i:A, ordCarrier (f i)))
          (fun jk => infOrd_loop (g (fst jk)) A (fun i:A => f i (snd jk i)))
  end.

Definition infOrd (A:Type) (i:A) (f:A -> Ord) := infOrd_loop (f i) A f.


(* The natural numbers inject into the ordinals in the obvious way. *)
Fixpoint natOrdSize (x:nat) :=
  match x with
  | O => zeroOrd
  | S n => succOrd (natOrdSize n)
  end.

(* The limit of all the finite ordinals gives the smallest limit ordinal, ω. *)
Canonical Structure ω : Ord := ord nat natOrdSize.

(** We can constructed the supremum of the image of a function on ordinals,
    when applied to all the ordinals indexed by β.
  *)
Definition boundedSup (β:Ord) (f:Ord -> Ord) : Ord := supOrd (fun i:β => f (β i)).

(** The predecessor of an ordinal is the supremum of all the ordinals
    strictly below it. This function is stationary on limit ordinals
    (and zero) but undoes the action of a successor.
  *)
Definition predOrd (x:Ord) : Ord :=
  match x with
  | ord A f => supOrd f
  end.

(** A "complete" ordinal is one which is directed, in an
    order-theoretic sense; for which it decidable if it is inhabited;
    and for which all its subordinals are also complete.

    This is an important technical property that appears frequently in
    some later proofs. In a classical setting, all ordinals have this
    property, as it follows easily from the totality of order.
*)
Definition directed A (f:A -> Ord) :=
  forall a1 a2, exists a', f a1 <= f a' /\ f a2 <= f a'.

Fixpoint complete (x:Ord) : Prop :=
  match x with
  | ord A f =>
    (directed A f) /\
    (inhabited A \/ ~inhabited A) /\
    (forall a, complete (f a))
  end.

Lemma complete_subord o :
  complete o -> forall i, complete (o i).
Proof.
  destruct o as [A f]; simpl; intuition.
Qed.

Lemma complete_zeroDec o :
  complete o -> o <= 0 \/ 0 < o.
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

Lemma directed_monotone :
  forall (a:Ord) f,
    (forall (x y:a), sz x <= sz y -> f x <= f y) ->
    complete a ->
    directed a f.
Proof.
  intros.
  hnf; simpl; intros.
  destruct (complete_directed a H0 a1 a2) as [a' [??]].
  exists a'.
  split; apply H; auto.
Qed.

Lemma zero_unfold : 0 = ord False (False_rect Ord).
Proof.
  reflexivity.
Qed.

(** Zero is the least ordinal. *)
Lemma zero_least : forall o, 0 ≤ o.
Proof.
  intros. rewrite ord_le_unfold.
  simpl. intros [].
Qed.

(** No ordinal is strictly below zero. *)
Lemma zero_lt : forall o, o < 0 -> False.
Proof.
  intros.
  rewrite ord_lt_unfold in H.
  destruct H as [[] _].
Qed.

Lemma zero_complete : complete 0.
Proof.
  simpl; repeat (hnf; intuition).
  right. intros [[]].
Qed.

Global Hint Resolve zero_least zero_lt zero_complete : ord.

Lemma succ_unfold x : succOrd x = ord unit (fun _ => x).
Proof.
  reflexivity.
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

Lemma succ_monotone : forall a b, a ≤ b -> succOrd a ≤ succOrd b.
Proof.
  intros.
  apply succ_least.
  apply ord_le_lt_trans with b; auto with ord.
  apply succ_lt.
Qed.

Lemma succ_increasing : forall a b, a < b -> succOrd a < succOrd b.
Proof.
  intros.
  apply ord_le_lt_trans with b; auto with ord.
  apply succ_least; auto.
  apply succ_lt.
Qed.

Lemma succ_trans x y : x ≤ y -> x < succOrd y.
Proof.
  intros.
  rewrite ord_lt_unfold.
  simpl. exists tt. auto.
Qed.

Lemma succ_trans' x y : x ≤ y -> x ≤ succOrd y.
Proof.
  intros.
  apply ord_lt_le.
  apply succ_trans; auto.
Qed.

Lemma succ_congruence : forall a b, a ≈ b -> succOrd a ≈ succOrd b.
Proof.
  unfold ord_eq; intuition; apply succ_monotone; auto.
Qed.

Global Hint Resolve
  succ_lt succ_least succ_monotone succ_increasing succ_trans succ_congruence : ord.

Add Parametric Morphism : succOrd with signature
    ord_le ++> ord_le as succOrd_le_mor.
Proof.
  intros; apply succ_monotone; auto.
Qed.

Add Parametric Morphism : succOrd with signature
    ord_lt ++> ord_lt as succOrd_lt_mor.
Proof.
  intros; apply succ_increasing; auto.
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

Lemma natOrdSize_complete n : complete (natOrdSize n).
Proof.
  induction n; simpl natOrdSize.
  apply zero_complete.
  apply succ_complete; auto.
Qed.

Global Hint Resolve succ_complete natOrdSize_complete: ord.



Lemma sup_unfold A (f:A->Ord) :
  supOrd f =
  ord (sigT (fun a => ordCarrier (f a)))
      (fun ai => ordSize (f (projT1 ai)) (projT2 ai)).
Proof.
  reflexivity.
Qed.

(** The supremum is nonstrictly above all the ordinals in the
  * collection defined by "f".  Morover it is it the smallest such.
  *)
Lemma sup_le : forall A (f:A -> Ord) a, f a ≤ supOrd f.
Proof.
  intros A f a.
  rewrite ord_le_unfold.
  intro b.
  rewrite ord_lt_unfold.
  exists (@existT A (fun a => ordCarrier (f a)) a b).
  simpl. auto with ord.
Qed.

Lemma sup_least : forall A (f:A -> Ord) z,
    (forall a, f a ≤ z) -> supOrd f ≤ z.
Proof.
  intros A f z H.
  rewrite ord_le_unfold.
  intros [a b]; simpl.
  specialize (H a).
  rewrite ord_le_unfold in H.
  apply H.
Qed.

Lemma sup_lt x A (f:A -> Ord) :
  x < supOrd f -> exists a:A, x < f a.
Proof.
  rewrite ord_lt_unfold. simpl.
  intros [[a q] H]; simpl in *.
  exists a.
  rewrite ord_lt_unfold.
  exists q. auto.
Qed.

Global Instance sup_ord_le_morphism (A:Type) :
  Proper (pointwise_relation _ ord_le ==> ord_le) (@supOrd A).
Proof.
  repeat intro.
  red in H.
  apply sup_least. intro a.
  rewrite H.
  apply sup_le.
Qed.

Global Instance sup_ord_eq_morphism (A:Type) :
  Proper (pointwise_relation _ ord_eq ==> ord_eq) (@supOrd A).
Proof.
  repeat intro.
  split.
  red in H.
  apply sup_ord_le_morphism; red; intros; apply H.
  apply sup_ord_le_morphism; red; intros; apply H.
Qed.


Lemma limit_unfold A (f:A -> Ord) : limOrd f = ord A f.
Proof.
  reflexivity.
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
  When f is an ascending set: lim f = sup f
  When f has a maximal element: lim f = succ (sup f)
*)
Lemma sup_lim : forall A (f:A -> Ord),
  supOrd f ≤ limOrd f.
Proof.
  intros A f.
  apply sup_least.
  auto with ord.
Qed.

Lemma lim_sup : forall A (f:A -> Ord),
  limOrd f ≤ succOrd (supOrd f).
Proof.
  intros A f.
  apply limit_least. intro a.
  apply ord_le_lt_trans with (supOrd f); auto with ord.
Qed.

Lemma sup_succ_lim : forall A (f:A -> Ord),
  limOrd f ≈ supOrd (fun a:A => succOrd (f a)).
Proof.
  intros.
  split.
  - apply limit_least.
    intro i.
    rewrite <- (sup_le _ _ i).
    auto with ord.
  - apply sup_least; auto with ord.
Qed.

Lemma ascending_sup_lim : forall A (f:A -> Ord),
  ascendingSet A f ->
  limOrd f ≈ supOrd f.
Proof.
  intros A f Hasc.
  split; [ | apply sup_lim ].
  apply limit_least. intro a.
  destruct (Hasc a) as [a' ?].
  apply ord_lt_le_trans with (f a'); auto with ord.
Qed.

Lemma succ_sup_lim : forall A (f:A -> Ord),
  hasMaxElement A f ->
  limOrd f ≈ succOrd (supOrd f).
Proof.
  intros A f Hmax.
  split; [ apply lim_sup |].
  apply succ_least.
  destruct Hmax as [i Hmax].
  rewrite ord_lt_unfold. simpl. exists i.
  apply sup_least. auto.
Qed.

Global Instance lim_ord_le_morphism (A:Type) :
  Proper (pointwise_relation _ ord_le ==> ord_le) (@limOrd A).
Proof.
  repeat intro.
  apply limit_least. intros.
  red in H. rewrite H.
  apply limit_lt.
Qed.

Global Instance lim_ord_eq_morphism (A:Type) :
  Proper (pointwise_relation _ ord_eq ==> ord_eq) (@limOrd A).
Proof.
  repeat intro.
  split; apply lim_ord_le_morphism;
    red; intros; apply H.
Qed.


(** Here we show that @infOrd@ computes the greatest lower bound of a nonempty
    collection. Note, this proof requires the @DependentFunctionalChoice@ principle.

    Classicaly, the infimum of a set of ordinals is always a member of the set, as there
    can be no infinte decending chains of ordinals. *)
Lemma inf_loop_lower_bound:
  forall x A f, infOrd_loop x A f <= x /\ (forall i, infOrd_loop x A f <= f i).
Proof.
  induction x as [B g Hx].
  simpl; intuition.
  - rewrite ord_le_unfold; simpl.
    intros [j k]; simpl.
    rewrite ord_lt_unfold; simpl.
    exists j.
    apply Hx.
  - rewrite ord_le_unfold; simpl.
    intros [j k]; simpl.
    rewrite ord_lt_unfold; simpl.
    exists (k i); simpl.
    destruct (Hx j A (fun i => f i (k i))); auto.
Qed.

Lemma inf_loop_greatest (HC:DependentFunctionalChoice) :
  forall x A f z,
    z <= x ->
    (forall i, z <= f i) ->
    z <= infOrd_loop x A f.
Proof.
  induction x as [B g Hx].
  simpl; intuition.
  rewrite ord_le_unfold; simpl.
  intro q.
  rewrite ord_lt_unfold; simpl.
  rewrite ord_le_unfold in H. specialize (H q).
  rewrite ord_lt_unfold in H. destruct H as [b Hb].
  red in HC.
  destruct (HC A (fun i => ordCarrier (f i)) (fun i j => z q <= f i j)) as [k Hk].
  { intro i. specialize (H0 i).
    rewrite ord_le_unfold in H0.
    specialize (H0 q).
    rewrite ord_lt_unfold in H0.
    auto. }
  exists (b, k).
  simpl.
  apply Hx; auto.
Qed.

Lemma inf_lower_bound : forall A i0 f i,
  infOrd A i0 f <= f i.
Proof.
  intros. unfold infOrd. apply inf_loop_lower_bound.
Qed.

Lemma inf_greatest (HC:DependentFunctionalChoice) :
  forall A i0 f z,
    (forall i, z <= f i) ->
    z <= infOrd A i0 f.
Proof.
  intros. unfold infOrd.
  apply inf_loop_greatest; auto.
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
  unfold boundedSup.
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
  unfold boundedSup. simpl. intros.
  apply sup_least; auto with ord.
Qed.

(** ω is the smallest limit ordinal *)
Lemma omega_limit : limitOrdinal ω.
Proof.
  simpl. split.
  - exact (inhabits 0%nat).
  - hnf; intros n.
    exists (S n); simpl; auto with ord.
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
  - exists q; auto with ord.
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

Lemma natOrdSize_increasing m n :
  (m < n)%nat -> natOrdSize m < natOrdSize n.
Proof.
  intro H. induction H; simpl.
  apply succ_lt.
  transitivity (natOrdSize m0); auto with ord.
Qed.

Lemma succ_cancel_le x y :
  succOrd x <= succOrd y -> x <= y.
Proof.
  intros.
  do 2 rewrite succ_unfold in H.
  destruct (ord_le_subord _ _ H tt) as [??].
  auto.
Qed.

Lemma succ_cancel_eq x y :
  succOrd x ≈ succOrd y -> x ≈ y.
Proof.
  intros; split; apply succ_cancel_le; apply H.
Qed.

Lemma natOrdSize_unique : forall m n,
  natOrdSize m ≈ natOrdSize n -> m = n.
Proof.
  induction m; destruct n; simpl; intros; auto.
  - elim (ord_lt_irreflexive 0).
    rewrite H at 2.
    apply succ_trans; auto with ord.
  - elim (ord_lt_irreflexive 0).
    rewrite <- H at 2.
    apply succ_trans; auto with ord.
  - f_equal. apply IHm.
    apply succ_cancel_eq; auto.
Qed.

Lemma omega_complete : complete ω.
Proof.
  hnf; simpl; repeat split.
  - intros a1 a2.
    exists (Nat.max a1 a2); split; apply natOrdSize_monotone.
    + apply PeanoNat.Nat.le_max_l.
    + apply PeanoNat.Nat.le_max_r.
  - left. exact (inhabits 0%nat).
  - induction a.
    + apply zero_complete.
    + apply succ_complete; auto.
Qed.

Lemma omega_gt0 : 0 < ω.
Proof. apply (index_lt _ 0%nat). Qed.

Lemma omega_gt1 : 1 < ω.
Proof. apply (index_lt ω 1%nat). Qed.

(** Any zero ordinal is equal to the distinguished zeroOrd *)
Lemma ord_isZero z : zeroOrdinal z <-> z ≈ 0.
Proof.
  split.
  - intro. split; auto with ord.
    destruct z as [Z f].
    rewrite ord_le_unfold. intro a; elim H. exact (inhabits a).
  - repeat intro.
    destruct z as [Z f].
    simpl. intros [a].
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

Lemma ord_isLimit : forall x,
    limitOrdinal x <->
    (x > 0 /\ (forall i, i < x -> exists j, i < j /\ j < x)).
Proof.
  intros [X f].
  split; simpl; intuition.
  - rewrite ord_lt_unfold.
    destruct H0 as [x]. exists x. auto with ord.
  - rewrite ord_lt_unfold in H.
    destruct H as [x ?].
    destruct (H1 x) as [x' ?].
    exists (f x').
    split.
    rewrite H; auto.
    apply (index_lt (ord X f) x').
  - rewrite ord_lt_unfold in H0.
    destruct H0 as [x _].
    exact (inhabits x).
  - red; intros.
    destruct (H1 (f a)) as [j [??]].
    apply (index_lt (ord X f) a).
    rewrite ord_lt_unfold in H2.
    destruct H2 as [k ?].
    exists k.
    apply ord_lt_le_trans with j; auto.
Qed.

Lemma limit_boundedSup β : limitOrdinal β -> β ≈ boundedSup β (fun a => a).
Proof.
  destruct β as [B g]; simpl.
  unfold boundedSup.
  intros [_ Hb].
  rewrite <- ascending_sup_lim; auto.
  reflexivity.
Qed.

Lemma limit_boundedSup' β :
  0 < β ->
  β ≈ boundedSup β (fun a => a) ->
  limitOrdinal β.
Proof.
  destruct β as [B g]; simpl.
  unfold boundedSup.
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

Add Parametric Morphism : zeroOrdinal with signature
    ord_eq ==> impl as zeroOrdinal_mor.
Proof.
  repeat intro.
  rewrite ord_isZero in H0.
  rewrite ord_isZero.
  rewrite <- H; auto.
Qed.

Add Parametric Morphism : successorOrdinal with signature
    ord_eq ==> impl as succOrdinal_mor.
Proof.
  repeat intro.
  rewrite ord_isSucc  in H0.
  rewrite ord_isSucc.
  destruct H0 as [o ?].
  exists o.
  rewrite <- H; auto.
Qed.

Add Parametric Morphism : limitOrdinal with signature
    ord_eq ==> impl as limitOrdinal_mor.
Proof.
  repeat intro.
  rewrite ord_isLimit in H0.
  rewrite ord_isLimit.
  intuition.
  rewrite <- H; auto.
  destruct (H2 i) as [j [??]].
  rewrite H; auto.
  exists j; split; auto.
  rewrite <- H; auto.
Qed.

Lemma pred_unfold x : predOrd x = supOrd (ordSize x).
Proof.
  destruct x; reflexivity.
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

Lemma pred_zero : 0 ≈ predOrd 0.
Proof.
  split; auto with ord.
  apply pred_least.
  intros x H.
  rewrite ord_lt_unfold in H.
  destruct H as [[] _].
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

Lemma glb_unfold x y :
  x ⊓ y = ord (ordCarrier x * ordCarrier y)
              (fun i => x (fst i) ⊓ y (snd i)).
Proof.
  destruct x; destruct y; reflexivity.
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

Lemma lub_unfold x y :
  x ⊔ y = ord (ordCarrier x + ordCarrier y)
              (fun xy => match xy with
                         | inl i => x i
                         | inr i => y i
                         end).
Proof.
  destruct x; destruct y; reflexivity.
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

Lemma lub_lt a b c :
  a < b ⊔ c -> a < b \/ a < c.
Proof.
  rewrite ord_lt_unfold. unfold lubOrd. simpl.
  intros [q ?].
  destruct b as [B h].
  destruct c as [C g]. simpl in *.
  destruct q.
  - left. rewrite ord_lt_unfold. eauto.
  - right. rewrite ord_lt_unfold. eauto.
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

Lemma lub_binary_sup a b :
  a ⊔ b ≈ supOrd (fun i:bool => if i then a else b).
Proof.
  split.
  - apply lub_least.
    + rewrite <- (sup_le _ _ true).
      reflexivity.
    + rewrite <- (sup_le _ _ false).
      reflexivity.
  - apply sup_least. intros [|].
    + apply lub_le1.
    + apply lub_le2.
Qed.

Lemma lub_continuous f a b :
  (forall a b, a ≤ b -> f a ≤ f b) ->
  strongly_continuous f ->
  f (a ⊔ b) ≈ f a ⊔ f b.
Proof.
  intros Hmono Hcont.
  transitivity (f (supOrd (fun i:bool => if i then a else b))).
  { split; apply Hmono; apply lub_binary_sup. }
  split.
  - rewrite (Hcont bool (fun i => if i then a else b) false).
    apply sup_least. intros [|].
    + apply lub_le1.
    + apply lub_le2.
  - apply lub_least; apply Hmono.
    + rewrite <- (sup_le _ _ true); reflexivity.
    + rewrite <- (sup_le _ _ false); reflexivity.
Qed.

(**  The lub of successors is <= the successor of the lub.
  *)
Lemma succ_lub x y :
 succOrd x ⊔ succOrd y ≤ succOrd (x ⊔ y).
Proof.
  apply lub_least.
  - apply succ_monotone.
    apply lub_le1.
  - apply succ_monotone.
    apply lub_le2.
Qed.


Global Hint Unfold ordSize : ord.
Global Hint Resolve
     limit_lt lub_le1 lub_le2
     ord_lt_trans ord_le_trans ord_eq_trans
     succ_trans
     succ_trans'
     lub_le1 lub_le2
     ord_lt_le ord_le_refl ord_eq_refl : ord.

Lemma lub_complete1 : forall x y,
    x >= y ->
    complete x ->
    complete y ->
    complete (x ⊔ y).
Proof.
 intros x y Hxy Hx Hy.
 destruct x as [X f].
 destruct y as [Y g].
 simpl in *.
 destruct Hx as [Hx1 [Hx2 Hx3]].
 repeat split.
 - intros [x1|y1].
   + intros [x2|y2].
     * destruct (Hx1 x1 x2) as [x' [Hx'1 Hx'2]].
       exists (inl x'); split; auto.
     * destruct (ord_le_subord _ _ Hxy y2) as [x2 Hy2]. simpl in *.
       destruct (Hx1 x1 x2) as [x' [Hx'1 Hx'2]].
       exists (inl x'); split; auto.
       transitivity (f x2); auto.
   + destruct (ord_le_subord _ _ Hxy y1) as [x1 Hy1]. simpl in *.
     intros [x2|y2].
     * destruct (Hx1 x1 x2) as [x' [Hx'1 Hx'2]].
       exists (inl x'); split; auto.
       transitivity (f x1); auto.
     * destruct (ord_le_subord _ _ Hxy y2) as [x2 Hy2]. simpl in *.
       destruct (Hx1 x1 x2) as [x' [Hx'1 Hx'2]].
       exists (inl x'); split; auto.
       transitivity (f x1); auto.
       transitivity (f x2); auto.
 - destruct Hx2 as [[x]|Hx2].
   + left. exact (inhabits (inl x)).
   + right. intros [[x|y]].
     * apply Hx2. exact (inhabits x).
     * apply Hx2.
       destruct (ord_le_subord _ _ Hxy y) as [x _]. simpl in *.
       exact (inhabits x).
 - intros [x|y]; auto.
   destruct Hy as [_ [_ Hy]].
   apply Hy.
Qed.


Lemma lub_complete2 : forall x y,
    x <= y ->
    complete x ->
    complete y ->
    complete (x ⊔ y).
Proof.
 intros x y Hxy Hx Hy.
 destruct x as [X f].
 destruct y as [Y g].
 simpl in *.
 destruct Hy as [Hy1 [Hy2 Hy3]].
 repeat split.
 - intros [x1|y1].
   + destruct (ord_le_subord _ _ Hxy x1) as [y1 Hx1]. simpl in *.
     intros [x2|y2].
     * destruct (ord_le_subord _ _ Hxy x2) as [y2 Hx2]. simpl in *.
       destruct (Hy1 y1 y2) as [y' [Hy'1 Hy'2]].
       exists (inr y'); split; auto.
       transitivity (g y1); auto.
       transitivity (g y2); auto.
     * destruct (Hy1 y1 y2) as [y' [Hy'1 Hy'2]].
       exists (inr y'); split; auto.
       transitivity (g y1); auto.
   + intros [x2|y2].
     * destruct (ord_le_subord _ _ Hxy x2) as [y2 Hx2]. simpl in *.
       destruct (Hy1 y1 y2) as [y' [Hy'1 Hy'2]].
       exists (inr y'); split; auto.
       transitivity (g y2); auto.
     * destruct (Hy1 y1 y2) as [y' [Hy'1 Hy'2]].
       exists (inr y'); split; auto.
 - destruct Hy2 as [[y]|Hy2].
   + left. exact (inhabits (inr y)).
   + right. intros [[x|y]].
     * apply Hy2.
       destruct (ord_le_subord _ _ Hxy x) as [y _]. simpl in *.
       exact (inhabits y).
     * apply Hy2.
       exact (inhabits y).
 - intros [x|y]; auto.
   destruct Hx as [_ [_ Hx]]; apply Hx.
Qed.

Lemma lim_complete : forall A (f:A -> Ord),
    (forall a, complete (f a)) ->
    directed A f ->
    (inhabited A \/ ~inhabited A) ->
    complete (limOrd f).
Proof.
  intros A f H1 H2 H3.
  simpl. repeat split; auto.
Qed.

Lemma sup_complete : forall A (f:A -> Ord),
    (forall a, complete (f a)) ->
    directed A f ->
    ((exists a, 0 < f a) \/ (forall a, f a <= 0)) ->
    complete (supOrd f).
Proof.
  intros A f H1 H2 H3.
  simpl. repeat split.
  - intros [a1 q1] [a2 q2]. simpl.
    destruct (H2 a1 a2) as [a' [Ha1 Ha2]].
    destruct (ord_le_subord _ _ Ha1 q1) as [q1' Hq1].
    destruct (ord_le_subord _ _ Ha2 q2) as [q2' Hq2].
    destruct (complete_directed (f a') (H1 a') q1' q2') as [q' [Hq'1 Hq'2]].
    exists (existT _ a' q'). simpl. split.
    transitivity (f a' q1'); auto.
    transitivity (f a' q2'); auto.
  - destruct H3.
    + left. destruct H as [a Ha].
      rewrite ord_lt_unfold in Ha.
      destruct Ha as [q Hq].
      exact (inhabits (existT _ a q)).
    + right. intros [[a q]].
      destruct (ord_le_subord _ _ (H a) q) as [[] _].
  - intros [a q]; simpl.
    apply complete_subord; auto.
Qed.


Global Opaque lubOrd glbOrd supOrd.



Definition succ_unreachable (x:Ord) :=
  forall a, a < x -> succOrd a < x.

Add Parametric Morphism : succ_unreachable with signature
    ord_eq ==> impl as succ_unreachable_eq_mor.
Proof.
  intros. hnf; intros.
  unfold succ_unreachable.
  intro i.
  rewrite <- H.
  apply H0.
Qed.

Lemma zero_succ_unreachable: succ_unreachable 0.
Proof.
  hnf; intros.
  elim (ord_lt_irreflexive a).
  apply ord_lt_le_trans with 0; auto with ord.
Qed.

Lemma limit_unreachable y :
    limitOrdinal y ->
    succ_unreachable y.
Proof.
  intros Hlim x Hxy.
  rewrite ord_isLimit in Hlim.
  destruct Hlim as [Hz Hlim].
  destruct (Hlim x) as [q [??]]; auto.
  apply ord_le_lt_trans with q; auto.
  apply succ_least; auto.
Qed.

Lemma unreachable_limit y :
  y > 0 -> succ_unreachable y -> limitOrdinal y.
Proof.
  intros. rewrite ord_isLimit; split; auto.
  intros.
  exists (succOrd i). split; auto with ord.
Qed.
