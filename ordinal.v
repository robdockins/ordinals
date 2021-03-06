Require Import List.
Require Import Relations.
Require Import Wf.
Require Import Wellfounded.Transitive_Closure.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Import ListNotations.
Open Scope list.

Unset Printing Records.

Delimit Scope ord_scope with ord.
Open Scope ord_scope.

(** Ordinals, represented as Type-indexed trees
  * of potentially infinite width, but finite depth.
  *)
Inductive Ord : Type :=
  ord { ordCarrier :> Type
      ; ordSize :> ordCarrier -> Ord
      }.

Definition sz {A:Ord} (x:A) : Ord := ordSize A x.
Coercion sz : ordCarrier >-> Ord.
Add Printing Coercion sz.


(** We define less-than and less-equal essentially by mutual
  * recursion on the structure of ordinals.
  *)
Fixpoint ord_lt (x y:Ord) {struct x}: Prop :=
  match x, y with
  | ord A f, ord B g =>
    exists b:B, forall a:A, ord_lt (f a) (g b)
  end.

Definition ord_le (x y:Ord) : Prop :=
  match x with
  | ord A f => forall a:A, ord_lt (f a) y
  end.

Definition ord_eq (x y:Ord) : Prop :=
  ord_le x y /\ ord_le y x.

Notation "x > y" := (ord_lt y x) : ord_scope.
Notation "x < y" := (ord_lt x y) : ord_scope.
Notation "x >= y" := (ord_le y x) : ord_scope.
Notation "x <= y" := (ord_le x y) : ord_scope.
Notation "x ≥ y" := (ord_le y x) (at level 70, no associativity) : ord_scope.
Notation "x ≤ y" := (ord_le x y) (at level 70, no associativity) : ord_scope.
Notation "x ≈ y" := (ord_eq x y) (at level 70, no associativity) : ord_scope.

(*  The notation "x ◃ y" indicates that "x" has a strictly smaller ordinal measure
    than "y".  Note that "x" and "y" do not need to have the same type.

    Likewise "x ⊴ y" indicates that "x" has an ordinal measure no larger than "y".
 *)
Notation "x ◃ y" := (sz x < sz y)%ord (at level 80, no associativity).
Notation "x ⊴ y" := (sz x ≤ sz y)%ord (at level 80, no associativity).

(** Characteristic equation for less-than *)
Lemma ord_lt_unfold x y :
  x < y = exists b:y, x ≤ y b.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

(** Characteristic equation for less-equal *)
Lemma ord_le_unfold x y :
  x ≤ y = forall a:x, x a < y.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

Global Opaque ord_le ord_lt.

(** Less-than implies less-equal
  *)
Lemma ord_lt_le : forall b a,
  a < b -> a ≤ b.
Proof.
  induction b as [B g]. intros.
  rewrite ord_lt_unfold in H0. simpl in *.
  destruct H0 as [b ?].
  destruct a as [A f].
  rewrite ord_le_unfold in *.
  intros.
  specialize (H0 a).
  rewrite ord_lt_unfold.
  exists b. apply H. auto.
Qed.

(** Less-equal is a reflexive relation
  *)
Lemma ord_le_refl x : x ≤ x.
Proof.
  induction x as [A f].
  rewrite ord_le_unfold.
  intros.
  rewrite ord_lt_unfold.
  exists a. apply H.
Qed.


Lemma index_lt : forall (a:Ord) (i:a), a i < a.
Proof.
  intros.
  rewrite ord_lt_unfold.
  exists i. apply ord_le_refl.
Qed.

Lemma index_le : forall (a:Ord) (i:a), a i ≤ a.
Proof.
  intros.
  apply ord_lt_le.
  apply index_lt.
Qed.

Hint Resolve ord_lt_le ord_le_refl index_lt index_le : ord.


(** These various transitivity-releated facts need to
    be proved simultaneuously.
  *)
Lemma ord_trans :
  forall b a c,
    (a ≤ b -> b ≤ c -> a ≤ c) /\
    (a ≤ b -> b < c -> a < c) /\
    (a < b -> b ≤ c -> a < c).
Proof.
  induction b as [B g].
  intros.
  repeat split; intros.
  - rewrite ord_le_unfold.
    rewrite ord_le_unfold in H0.
    intro ai.
    specialize (H0 ai).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [bi ?].
    rewrite ord_le_unfold in H1.
    specialize (H1 bi).
    specialize (H bi (a ai) c); intuition.
  - rewrite ord_lt_unfold.
    rewrite ord_lt_unfold in H1.
    destruct H1 as [ci ?].
    exists ci.
    rewrite ord_le_unfold in H1.
    rewrite ord_le_unfold.
    rewrite ord_le_unfold in H0.
    intros ai.
    specialize (H0 ai).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [bi ?].
    specialize (H1 bi).
    specialize (H bi (a ai) (c ci)); intuition.
  - rewrite ord_lt_unfold in H0.
    destruct H0 as [bi ?].
    rewrite ord_le_unfold in H1.
    specialize (H1 bi).
    destruct (H bi a c); intuition.
Qed.

(** Less-equal is transitive.
  *)
Lemma ord_le_trans a b c :
    a ≤ b -> b ≤ c -> a ≤ c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** Less-than is transitive *)
Lemma ord_lt_trans a b c :
    a < b -> b < c -> a < c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** Less-equal preserves less-than *)
Lemma ord_lt_le_trans a b c :
  a < b -> b ≤ c -> a < c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

Lemma ord_le_lt_trans a b c :
  a ≤ b -> b < c -> a < c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** The less-than ordering on ordinals is well-founded.
  *)
Lemma ord_lt_acc : forall x y,  y ≤ x -> Acc ord_lt y.
Proof.
  induction x as [A f]; intros z Hz.
  constructor. intros y Hy.
  assert (Hyx : (ord_lt y (ord A f))).
  { apply ord_lt_le_trans with z; auto. }

  rewrite ord_lt_unfold in Hyx.
  destruct Hyx as [b ?].
  apply (H b).
  auto.
Defined.

Lemma ord_lt_wf : well_founded ord_lt.
Proof.
  red; intros.
  apply ord_lt_acc with a.
  apply ord_le_refl.
Defined.

(** The less-than order is irreflexive, a simple corollary of well-foundedness.
  *)
Corollary ord_lt_irreflexive : forall x, x < x -> False.
Proof.
  induction x using (well_founded_induction ord_lt_wf).
  firstorder.
Qed.


(** * Ordinal equality is an equality relation *)

Lemma ord_eq_refl : forall x, x ≈ x.
Proof.
  intros; split; apply ord_le_refl.
Qed.

Lemma ord_eq_trans : forall x y z, x ≈ y -> y ≈ z -> x ≈ z.
Proof.
  unfold ord_eq; intuition; eapply ord_le_trans; eauto.
Qed.

Lemma ord_eq_sym : forall x y, x ≈ y -> y ≈ x.
Proof.
  unfold ord_eq; intuition.
Qed.


Add Parametric Relation : Ord ord_le
    reflexivity proved by ord_le_refl
    transitivity proved by ord_le_trans
    as ord_le_rel.

Add Parametric Relation : Ord ord_lt
    transitivity proved by ord_lt_trans
    as ord_lt_rel.

Add Parametric Relation : Ord ord_eq
    reflexivity proved by ord_eq_refl
    symmetry proved by ord_eq_sym
    transitivity proved by ord_eq_trans
    as ord_eq_rel.

Instance ord_lt_le_subreleation : subrelation ord_lt ord_le.
Proof.
  red. intros; apply ord_lt_le; auto.
Qed.

Instance ord_eq_le_subrelation : subrelation ord_eq ord_le.
Proof.
  red. unfold ord_eq. intuition.
Qed.

Instance ord_eq_flip_le_subrelation : subrelation ord_eq (flip ord_le).
Proof.
  red. unfold ord_eq. intuition.
Qed.

Add Parametric Morphism : ord_lt with signature
    ord_le --> ord_le ++> impl as ord_lt_mor.
Proof.
  repeat intro.
  apply ord_le_lt_trans with x; auto.
  apply ord_lt_le_trans with x0; auto.
Qed.

Add Parametric Morphism : ord_lt with signature
    ord_le ++> ord_le --> flip impl as ord_lt_mor'.
Proof.
  repeat intro.
  apply ord_le_lt_trans with y; auto.
  apply ord_lt_le_trans with y0; auto.
Qed.


(** Ordinal operators *)
Definition zeroOrd : Ord := ord False (False_rect _).
Definition succOrd (x:Ord) : Ord := ord unit (fun _ => x).
Definition oneOrd := succOrd zeroOrd.
Definition limOrd {A:Type} (f:A -> Ord) := ord A f.
Definition lubOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A+B) (fun ab => match ab with inl a => f a | inr b => g b end)
  end.
Notation "x ⊔ y" := (lubOrd x y) (at level 55, right associativity) : ord_scope.

Definition supOrd {A:Type} (f:A -> Ord) :=
  ord (sigT (fun a => ordCarrier (f a)))
      (fun ai => ordSize (f (projT1 ai)) (projT2 ai)).

Fixpoint glbOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A*B) (fun ab => glbOrd (f (fst ab)) (g (snd ab)))
  end.
Notation "x ⊓ y" := (glbOrd x y) (at level 55, right associativity) : ord_scope.



Definition predOrd (x:Ord) : Ord :=
  match x with
  | ord A f => supOrd f
  end.

Definition hasMaxElement A (f:A -> Ord) :=
  exists a, forall a', f a ≥ f a'.

Definition ascendingSet A (f:A -> Ord) :=
  forall a, exists a', f a < f a'.

Definition successorOrdinal (x:Ord) :=
  match x with
  | ord A f => hasMaxElement A f
  end.

Definition limitOrdinal (x:Ord) :=
  match x with
  | ord A f => (exists a:A, True) /\ ascendingSet A f
  end.

(** Zero is the least ordinal.
  *)
Lemma zero_least : forall o, ord_le zeroOrd o.
Proof.
  intros. rewrite ord_le_unfold.
  simpl. intros. elim a.
Qed.

(** Succ is a monotone operator with respetct to both lt and le, and
  * which is strictly above its argument.
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

(** The supremum ordinal is nonstrictly above all the ordinals in the
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

Hint Resolve limit_lt sup_le : ord.

(** Supremum and limit are closely related operations.
  * We always have: sup f <= lim f <= succ (sup f).
  * Moreover: lim f = sup (succ . f)
  * When f is an ascending set, lim f = sup f
  * When f has a maximal element, lim f = succ (sup f)
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


(** Functions into sized types have sizes defined by nontrivial
    limit ordinals.
*)
Definition funOrd {A B:Type} (sz:B -> Ord) (f:A -> B) : Ord :=
  limOrd (fun x => sz (f x)).
Canonical Structure FunOrd (A:Type) (B:Ord) :=
  ord (A -> B) (@funOrd A B (ordSize B)).

Definition depOrd {A:Type} {B:A -> Type} (sz : forall a:A, B a -> Ord) (f:forall a:A, B a) : Ord :=
  limOrd (fun x => sz x (f x)).
Canonical Structure DepOrd (A:Type) (B:A -> Ord) :=
  ord (forall a:A, B a) (@depOrd A B (fun x => ordSize (B x))).

(** Functions have larger ordinal size than each of their points.
 *)
Lemma fun_lt : forall A (B:Ord) (f:A -> B) i, f i ◃ f.
Proof.
  simpl; intros.
  unfold funOrd.
  apply (limit_lt _ (fun x => ordSize B (f x))).
Qed.

Lemma dep_lt : forall (A:Type) (B:A->Ord) (f:DepOrd A B) i, f i ◃ f.
Proof.
  simpl; intros.
  unfold depOrd.
  apply (limit_lt _ (fun x => ordSize (B x) (f x))).
Qed.

Hint Resolve fun_lt dep_lt : ord.


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


(** * Definitions by transfinite recursion.
  *)
Definition foldOrd (z:Ord) (s:Ord -> Ord) : Ord -> Ord :=
  fix foldOrd (x:Ord) : Ord :=
    match x with
    | ord A f => lubOrd z (supOrd (fun i:A => s (foldOrd (f i))))
    end.

Lemma foldOrd_least z s (q:Ord -> Ord)
      (Hz : forall x, z ≤ q x)
      (Hmono : forall x y, x ≤ y -> s x ≤ s y)
      (Hsq : forall (x:Ord) (i:x), s (q (x i)) ≤ (q x)) :
      (forall x, foldOrd z s x ≤ q x).
Proof.
  induction x as [A f Hx].
  simpl.
  apply lub_least.
  - apply Hz.
  - apply sup_least. intros a.
    apply ord_le_trans with (s (q (f a))).
    apply Hmono. auto.
    apply (Hsq (ord A f)).
Qed.

Lemma foldOrd_unfold z s (x:Ord) i :
  s (foldOrd z s (x i)) ≤ foldOrd z s x.
Proof.
  destruct x as [A f]. simpl.
  eapply ord_le_trans; [ | apply lub_le2 ].
  eapply ord_le_trans; [ | apply (sup_le _ _ i)]. simpl.
  apply ord_le_refl.
Qed.

Lemma foldOrd_above_z z s x : z ≤ foldOrd z s x.
Proof.
  destruct x as [A f]; simpl.
  apply lub_le1.
Qed.

Lemma foldOrd_monotone_le z s : forall x y,
    (forall a b, a ≤ b -> s a ≤ s b) ->
    x ≤ y -> foldOrd z s x ≤ foldOrd z s y.
Proof.
  induction x as [A f Hx]. simpl; intros.
  apply lub_least.
  - apply foldOrd_above_z.
  - apply sup_least. intros a; simpl.
    rewrite ord_le_unfold in H0.
    specialize (H0 a). simpl in H0.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [b ?].
    rewrite <- (foldOrd_unfold z s y b).
    apply H.
    apply Hx; auto.
Qed.

Lemma mono_lt_increasing f :
  (forall x y, x < y -> f x < f y) ->
  forall a, a ≤ f a.
Proof.
  intro Hmono.
  induction a as [B g Ha].
  rewrite ord_le_unfold. intro b. simpl.
  apply ord_le_lt_trans with (f (g b)).
  apply Ha.
  apply Hmono.
  apply limit_lt.
Qed.

Lemma foldOrd_zero z s : foldOrd z s zeroOrd ≈ z.
Proof.
  split.
  - simpl.
    apply lub_least.
    + apply ord_le_refl.
    + apply sup_least. intros. elim a.
  - apply foldOrd_above_z.
Qed.

Lemma foldOrd_monotone_lt z s : forall x y,
    (forall a, z ≤ a -> a < s a) ->
    (forall a b, a ≤ b -> s a ≤ s b) ->
    x < y -> foldOrd z s x < foldOrd z s y.
Proof.
  intros x y. revert x.
  destruct y as [B g]; simpl; intros.
  rewrite ord_lt_unfold in H1.
  destruct H1 as [b ?].
  simpl in *.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ b).
  eapply ord_le_lt_trans; [ | apply H; apply foldOrd_above_z ].
  apply foldOrd_monotone_le; auto.
Qed.

Lemma foldOrd_succ z s x :
  (forall q, z ≤ q -> z ≤ s q) ->
  foldOrd z s (succOrd x) ≈ s (foldOrd z s x).
Proof.
  split.
  - simpl.
    apply lub_least.
    + apply H.
      destruct x; simpl.
      apply lub_le1.
    + apply sup_least. intro.
      apply ord_le_refl.
  - simpl.
    + rewrite <- lub_le2.
      rewrite <- (sup_le _ _ tt).
      reflexivity.
Qed.

Lemma foldOrd_limit z s x :
  limitOrdinal x ->
  (forall a b, a ≤ b -> s a ≤ s b) ->
  foldOrd z s x ≈ supOrd (fun i:x => foldOrd z s (x i)).
Proof.
  intros.
  split.
  - destruct x as [A f]. destruct H. simpl.
    apply lub_least.
    + destruct H as [a0 _].
      eapply ord_le_trans; [ | apply (sup_le _ _ a0) ]. simpl.
      destruct (f a0); simpl.
      apply lub_le1.
    + apply sup_least. intro a.
      destruct (H1 a) as [a' ?].
      eapply ord_le_trans; [ | apply (sup_le _ _ a') ]. simpl.
      apply ord_le_trans with (foldOrd z s (succOrd (f a))).
      simpl.
      eapply ord_le_trans; [ | apply lub_le2 ].
      eapply ord_le_trans; [ | apply (sup_le _ _ tt) ]. simpl.
      apply ord_le_refl.
      apply foldOrd_monotone_le; auto.
      apply succ_least. auto.
  - apply sup_least. intro a.
    apply foldOrd_monotone_le; auto with ord.
Qed.

Definition strongly_continuous (s:Ord -> Ord) :=
  forall A (f:A -> Ord) (a0:A), s (supOrd f) ≤ supOrd (fun i:A => s (f i)).

Lemma foldOrd_strongly_continuous z s :
  strongly_continuous (foldOrd z s).
Proof.
  red; simpl; intros.
  apply lub_least.
  - rewrite <- (sup_le _ _ a0).
    apply foldOrd_above_z.
  - apply sup_least.
    intros [a q]; simpl.
    rewrite <- (sup_le _ _ a).
    apply foldOrd_unfold.
Qed.

(** The "natural" ordinal addition function as defined by Hessenberg.
  * This ordinal operation is commutative, associative and absorbs zero.
  * It is also strictly monotone in both of its arguments.
  *
  * Morover, it is the smallest binary operation on ordinals which is strictly monotone
  * in both of its arguments.
  *)
Fixpoint addOrd (x:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match x, y with
    | ord A f, ord B g =>
      ord (A+B) (fun ab =>
                 match ab with
                 | inl a => addOrd (f a) y
                 | inr b => inner (g b)
                 end
                )
    end.

Notation "a ⊕ b" := (addOrd a b) (at level 45, right associativity) : ord_scope.

Lemma addOrd_unfold (x y:Ord) :
  x ⊕ y =
    (limOrd (fun a:x => x a ⊕ y))
    ⊔
    (limOrd (fun b:y => x ⊕ y b)).
Proof.
  destruct x; destruct y; auto.
Qed.

Global Opaque addOrd.

Lemma addOrd_le1 x y : x ≤ x ⊕ y.
Proof.
  induction x as [A f Hx].
  destruct y as [B g].
  rewrite addOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite ord_lt_unfold.
  simpl.
  exists (inl a).
  auto.
Qed.

Lemma addOrd_le2 x y : y ≤ x ⊕ y.
Proof.
  induction y as [A f Hx].
  destruct x as [B g].
  rewrite addOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite ord_lt_unfold.
  exists (inr a).
  apply Hx.
Qed.

Lemma addOrd_zero x : x ≈ x ⊕ zeroOrd.
Proof.
  split.
  - induction x as [A f].
    rewrite addOrd_unfold.
    simpl.
    rewrite ord_le_unfold; simpl; intros.
    rewrite ord_lt_unfold.
    exists (inl a).
    apply H.
  - induction x as [A f].
    rewrite addOrd_unfold.
    rewrite ord_le_unfold; simpl; intros.
    destruct a; intuition.
    rewrite ord_lt_unfold.
    exists a.
    auto.
Qed.

Lemma addOrd_comm_le x y : x ⊕ y ≤ y ⊕ x.
Proof.
  revert y.
  induction x as [A f Hx].
  intro y. revert A f Hx.
  induction y as [B g Hy]; intros.
  rewrite ord_le_unfold. rewrite addOrd_unfold.
  simpl; intros.
  destruct a.
  - rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    simpl.
    exists (inr a); auto.
  - rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    exists (inl b).
    apply Hy. auto.
Qed.

Lemma addOrd_comm x y : x ⊕ y ≈ y ⊕ x.
Proof.
  split; apply addOrd_comm_le; auto.
Qed.

Lemma addOrd_assoc1 : forall x y z,  x ⊕ (y ⊕ z) ≤ (x ⊕ y) ⊕ z.
Proof.
  induction x as [A f]. induction y as [B g]. induction z as [C h].
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl.
  intros.
  rewrite ord_lt_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl in *.
  destruct a as [a|[b|c]].
  - exists (inl (inl a)).
    generalize (H a (ord B g) (ord C h)).
    rewrite (addOrd_unfold (ord B g) (ord C h)); simpl; auto.
  - exists (inl (inr b)).
    apply H0.
  - exists (inr c).
    apply H1.
Qed.

Lemma addOrd_assoc2 : forall x y z, (x ⊕ y) ⊕ z ≤ x ⊕ (y ⊕ z).
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl; intros.
  rewrite ord_lt_unfold.
  rewrite addOrd_unfold.
  rewrite addOrd_unfold.
  simpl.
  destruct a as [[a|b]|c].
  - exists (inl a).
    apply H.
  - exists (inr (inl b)).
    apply H0.
  - exists (inr (inr c)).
    apply H1.
Qed.

Lemma addOrd_assoc : forall x y z,  x ⊕ (y ⊕ z) ≈ (x ⊕ y) ⊕ z.
Proof.
  intros; split.
  apply addOrd_assoc1.
  apply addOrd_assoc2.
Qed.

Lemma addOrd_cancel :
  forall x y z, addOrd x z < addOrd y z -> x < y.
Proof.
  induction x as [A f].
  induction y as [B g].
  induction z as [C h].
  rewrite ord_lt_unfold.
  rewrite addOrd_unfold.
  rewrite ord_lt_unfold.
  simpl.
  intros [[b|c] ?].
  - exists b.
    rewrite ord_le_unfold. intros.
    rewrite ord_le_unfold in H2.
    rewrite addOrd_unfold in H2.
    specialize (H2 (inl a)).
    simpl in H2.
    eapply H. apply H2.
  - rewrite ord_le_unfold in H2.
    rewrite addOrd_unfold in H2.
    specialize (H2 (inr c)).
    simpl in H2.
    apply H1 in H2.
    rewrite ord_lt_unfold in H2.
    auto.
Qed.

Lemma addOrd_monotone_le :
  forall x y z1 z2, x ≤ y -> z1 ≤ z2 -> x ⊕ z1 ≤ y ⊕ z2.
Proof.
  induction x as [A f]. destruct y as [B g]. induction z1 as [C h]. destruct z2.
  intros.
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  simpl.
  intros [a|c].
  - rewrite ord_le_unfold in H1.
    specialize (H1 a).
    rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    simpl.
    rewrite ord_lt_unfold in H1.
    destruct H1 as [b Hb].
    exists (inl b).
    apply H; auto.
  - rewrite ord_le_unfold in H2.
    specialize (H2 c).
    rewrite ord_lt_unfold.
    rewrite addOrd_unfold.
    rewrite ord_lt_unfold in H2.
    simpl.
    destruct H2 as [a Ha].
    exists (inr a).
    apply H0; auto.
Qed.

Lemma addOrd_monotone_lt :
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
    rewrite addOrd_unfold.
    simpl.
    exists (inl a).
    rewrite ord_le_unfold.
    rewrite addOrd_unfold.
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
    rewrite addOrd_unfold.
    simpl.
    exists (inr q).
    rewrite ord_le_unfold.
    rewrite addOrd_unfold.
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

Lemma addOrd_monotone_lt1 :
  forall x y z, x < y -> x ⊕ z < y ⊕ z.
Proof.
  intros.
  destruct (addOrd_monotone_lt x y z z).
  apply H0; auto.
  apply ord_le_refl.
Qed.

Lemma addOrd_monotone_lt2 :
  forall x y z, x < y -> z ⊕ x < z ⊕ y.
Proof.
  intros.
  destruct (addOrd_monotone_lt z z x y).
  apply H1; auto.
  apply ord_le_refl.
Qed.

Lemma addOrd_least (f:Ord -> Ord -> Ord)
  (Hmono1 : forall a b c, a < b -> f a c < f b c)
  (Hmono2 : forall a b c, a < b -> f c a < f c b)
  :
  (forall x y, x ⊕ y ≤ f x y).
Proof.
  induction x as [A fa].
  induction y as [B g].
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  simpl.
  intros [a|b].
  - eapply ord_le_lt_trans; [ apply H | auto with ord ].
  - eapply ord_le_lt_trans; [ apply H0 | auto with ord ].
Qed.

Lemma addOrd_succ x y : addOrd (succOrd x) y ≈ succOrd (addOrd x y).
Proof.
  split.
  - induction y as [B g Hy].
    rewrite ord_le_unfold.
    rewrite addOrd_unfold.
    simpl.
    intro ua.
    rewrite ord_lt_unfold. simpl.
    exists tt.
    destruct ua as [u|a].
    + apply ord_le_refl.
    + rewrite Hy.
      apply succ_least.
      apply addOrd_monotone_lt2; auto with ord.
  - apply succ_least.
    apply addOrd_monotone_lt1.
    apply succ_lt.
Qed.

Lemma addOrd_succ2 x y : addOrd x (succOrd y) ≈ succOrd (addOrd x y).
Proof.
  rewrite addOrd_comm.
  rewrite addOrd_succ.
  rewrite addOrd_comm.
  reflexivity.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_le ++> ord_le ++> ord_le as addOrd_le_mor.
Proof.
  intros. apply addOrd_monotone_le; auto.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_lt ++> ord_le ++> ord_lt as addOrd_lt_mor1.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply addOrd_monotone_lt1; eauto.
  apply addOrd_monotone_le; auto.
  reflexivity.
Qed.

Add Parametric Morphism : addOrd with signature
    ord_le ++> ord_lt ++> ord_lt as addOrd_lt_mor2.
Proof.
  intros.
  eapply ord_lt_le_trans.
  apply addOrd_monotone_lt2; eauto.
  apply addOrd_monotone_le; auto.
  reflexivity.
Qed.

Add Parametric Morphism : addOrd with signature
   ord_eq ==> ord_eq ==> ord_eq as addOrd_eq_mor.
Proof.
  intros; split; apply addOrd_le_mor; solve [apply H|apply H0].
Qed.



(** * An ordinal multiplication *)

Fixpoint mulOrd (x:Ord) (y:Ord) : Ord :=
    match y with
    | ord B g => supOrd (fun b:B => mulOrd x (g b) ⊕ x)
    end.

Notation "x ⊗ y" := (mulOrd x y) (at level 43, right associativity) : ord_scope.

Lemma mulOrd_unfold (x:Ord) (y:Ord) :
  x ⊗ y =
  supOrd (fun i:y => x ⊗ (y i) ⊕ x).
Proof.
  destruct y; auto.
Qed.

Lemma mulOrd_monotone_le1 : forall z x y, x ≤ y -> x ⊗ z ≤ y ⊗ z.
Proof.
  induction z as [C h Hz].
  simpl; intros.
  apply sup_least. intro c. simpl.
  rewrite <- (sup_le _ _ c).
  apply addOrd_monotone_le; auto.
Qed.

Lemma mulOrd_monotone_le2 : forall y x z, y ≤ z -> x ⊗ y ≤ x ⊗ z.
Proof.
  induction y as [B g Hy].
  intros.
  destruct x as [A f]; simpl in *.
  apply sup_least. intro b.
  rewrite ord_le_unfold in H.
  specialize (H b).
  simpl in H.
  rewrite ord_lt_unfold in H.
  destruct H as [q ?].
  specialize (Hy b).
  generalize (Hy (ord A f) (z q) H).
  intros.
  rewrite (mulOrd_unfold (ord A f) z).
  rewrite <- (sup_le _ _ q).
  apply addOrd_monotone_le; auto.
  apply ord_le_refl.
Qed.

Lemma mulOrd_monotone_lt2 : forall x y z,
    zeroOrd < x ->
    y < z ->
    x ⊗ y < x ⊗ z.
Proof.
  intros x y [C h] Hx H.
  rewrite (mulOrd_unfold x (ord C h)).
  simpl.
  rewrite ord_lt_unfold in H.
  destruct H as [c Hc]. simpl in Hc.
  rewrite <- (sup_le _ _ c).
  apply ord_le_lt_trans with (mulOrd x (h c)); [ apply mulOrd_monotone_le2; assumption | ].
  apply ord_le_lt_trans with (addOrd (mulOrd x (h c)) zeroOrd).
  - apply addOrd_zero.
  - apply addOrd_monotone_lt2. auto.
Qed.

Lemma mulOrd_zero : forall x, x ⊗ zeroOrd ≈ zeroOrd.
Proof.
  intros; split.
  - destruct x as [A f]. simpl.
    apply sup_least. intuition.
  - apply zero_least.
Qed.

Lemma mulOrd_succ : forall x y, x ⊗ (succOrd y) ≈ (x ⊗ y) ⊕ x.
Proof.
  intros; split; simpl.
  - apply sup_least; auto with ord.
  - rewrite <- (sup_le _ _ tt); auto with ord.
Qed.

Lemma mulOrd_one : forall x, mulOrd x oneOrd ≈ x.
Proof.
  intro.
  unfold oneOrd.
  rewrite mulOrd_succ.
  rewrite mulOrd_zero.
  rewrite addOrd_comm.
  rewrite <- addOrd_zero.
  reflexivity.
Qed.

Lemma mulOrd_positive : forall x y,
    zeroOrd < x ->
    zeroOrd < y ->
    zeroOrd < x ⊗ y.
Proof.
  intros.
  destruct x as [A f].
  destruct y as [B g].
  simpl.
  rewrite ord_lt_unfold in H.
  rewrite ord_lt_unfold in H0.
  destruct H as [a _].
  destruct H0 as [b _].
  simpl in *.
  rewrite <- (sup_le _ _ b).
  rewrite addOrd_unfold.
  rewrite <- lub_le2.
  rewrite ord_lt_unfold. exists a.
  apply zero_least.
Qed.

Lemma mulOrd_limit : forall x y,
    limitOrdinal y ->
    x ⊗ y ≈ supOrd (fun b:y => x ⊗ (y b)).
Proof.
  destruct y as [B g]; simpl; intros.
  split.
  - apply sup_least. intro b.
    destruct H as [_ H].
    destruct (H b) as [b' Hb'].
    rewrite <- (sup_le _ _ b').
    apply ord_le_trans with (mulOrd x (succOrd (g b))).
    apply (mulOrd_succ x (g b)).
    apply mulOrd_monotone_le2.
    apply succ_least; auto.
  - apply sup_least. intro b.
    rewrite <- (sup_le _ _ b).
    apply addOrd_le1.
Qed.

Lemma mulOrd_continuous x : strongly_continuous (mulOrd x).
Proof.
  red; simpl; intros.
  apply sup_least.
  intros [a q]. simpl.
  rewrite <- (sup_le _ _ a).
  rewrite (mulOrd_unfold x (f a)).
  rewrite <- (sup_le _ _ q).
  apply ord_le_refl.
Qed.

Add Parametric Morphism : mulOrd with signature
    ord_le ++> ord_le ++> ord_le as mulOrd_le_mor.
Proof.
  intros.
  apply ord_le_trans with (x ⊗ y0).
  apply mulOrd_monotone_le2; auto.
  apply mulOrd_monotone_le1; auto.
Qed.

Add Parametric Morphism : mulOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as mulOrd_eq_mor.
Proof.
  unfold ord_eq; intuition; apply mulOrd_le_mor; auto.
Qed.


(** * An ordinal exponentiation *)

Definition expOrd (x y:Ord) : Ord :=
  foldOrd oneOrd (fun a => a ⊗ x) y.

Lemma expOrd_nonzero x y : zeroOrd < expOrd x y.
Proof.
  apply ord_lt_le_trans with oneOrd.
  apply succ_lt.
  apply foldOrd_above_z.
Qed.

Lemma expOrd_zero x : expOrd x zeroOrd ≈ oneOrd.
Proof.
  apply foldOrd_zero.
Qed.

Lemma expOrd_succ x y :
  zeroOrd < x ->
  expOrd x (succOrd y) ≈ (expOrd x y) ⊗ x.
Proof.
  intros.
  apply foldOrd_succ.
  intros.
  apply succ_least.
  apply mulOrd_positive.
  rewrite ord_le_unfold in H0. apply (H0 tt). auto.
Qed.

Lemma expOrd_monotone_le a : forall x y,
    x ≤ y ->
    expOrd a x ≤ expOrd a y.
Proof.
  intros. apply foldOrd_monotone_le; auto.
  intros; apply mulOrd_monotone_le1; auto.
Qed.

Lemma expOrd_monotone_lt a (Ha : oneOrd < a) :
  forall y x,
    x < y ->
    expOrd a x < expOrd a y.
Proof.
  intros.
  apply foldOrd_monotone_lt; auto.
  - intros.
    rewrite mulOrd_unfold.
    rewrite ord_lt_unfold in Ha.
    destruct Ha as [q ?].
    rewrite ord_le_unfold in H1. specialize (H1 tt).
    rewrite ord_le_unfold in H0. specialize (H0 tt).
    simpl in *.

    eapply ord_lt_le_trans; [ | apply (sup_le _ _ q)]. simpl.
    apply ord_le_lt_trans with (addOrd zeroOrd a0).
    + eapply ord_le_trans; [ | apply addOrd_comm ].
      apply addOrd_zero.
    + apply addOrd_monotone_lt1.
      apply mulOrd_positive; auto.
  - apply mulOrd_monotone_le1.
Qed.

Lemma expOrd_limit x y (Hx:oneOrd < x) :
  limitOrdinal y ->
  expOrd x y ≈ (supOrd (fun b:y => expOrd x (y b))).
Proof.
  intros.
  apply foldOrd_limit; auto.
  apply mulOrd_monotone_le1.
Qed.

Lemma expOrd_continuous x (Hx:ord_lt oneOrd x) :
  strongly_continuous (expOrd x).
Proof.
  apply foldOrd_strongly_continuous; auto.
Qed.

Record normal_function (f:Ord -> Ord) :=
  NormalFunction
  { normal_monotone   : forall x y, x ≤ y -> f x ≤ f y
  ; normal_increasing : forall x, x ≤ f x
  ; normal_continuous : strongly_continuous f
  }.

(** * Fixpoints of normal functions *)
Section normal_fixpoints.
  Variable f : Ord -> Ord.
  Hypothesis Hnormal : normal_function f.

  Definition iter_f (base:Ord) : nat -> Ord :=
    fix iter_f (n:nat) : Ord :=
      match n with
      | 0 => base
      | S n' => f (iter_f n')
      end.

  Definition normal_fix (base:Ord) : Ord := supOrd (iter_f base).

  Lemma normal_prefixpoint : forall base, f (normal_fix base) ≤ normal_fix base.
  Proof.
    intros.
    apply ord_le_trans with (supOrd (fun i => f (iter_f base i))).
    - apply (normal_continuous _ Hnormal nat (iter_f base) 0).
    - apply sup_least. intro i.
      unfold normal_fix.
      apply (sup_le _ (iter_f base) (S i)).
  Qed.

  Lemma normal_fixpoint : forall base, normal_fix base ≈ f (normal_fix base).
  Proof.
    intros; split.
    - apply normal_increasing; auto.
    - apply normal_prefixpoint.
  Qed.

  Lemma normal_fix_above : forall base, base ≤ normal_fix base.
  Proof.
    intros.
    unfold normal_fix.
    apply (sup_le _ (iter_f base) 0).
  Qed.

  Lemma normal_fix_least : forall base z, base ≤ z -> f z ≤ z -> normal_fix base ≤ z.
  Proof.
    intros.
    unfold normal_fix.
    apply sup_least.
    intro i; induction i; simpl; auto.
    apply ord_le_trans with (f z); auto.
    apply normal_monotone; auto.
  Qed.

  Lemma normal_fix_monotone_le : forall b1 b2, ord_le b1 b2 -> ord_le (normal_fix b1) (normal_fix b2).
  Proof.
    unfold normal_fix; intros.
    apply sup_least. intro n.
    eapply ord_le_trans with (iter_f b2 n); [ | apply sup_le ].
    induction n; simpl; auto.
    apply normal_monotone; auto.
  Qed.

  Lemma normal_fix_continuous : strongly_continuous normal_fix.
  Proof.
    red; simpl; intros A g a0.
    unfold normal_fix at 1.
    apply sup_least. intro i.
    apply ord_le_trans with (supOrd (fun a => iter_f (g a) i)).
    - induction i.
      + simpl.
        reflexivity.
      + simpl.
        eapply ord_le_trans.
        * apply normal_monotone; [ apply Hnormal | apply IHi ].
        * apply normal_continuous; auto.
    - apply sup_least. intro a.
      rewrite <- (sup_le _ _ a).
      unfold normal_fix.
      apply sup_le.
  Qed.

  Lemma normal_lub x y :
    f (x ⊔ y) ≤ f x ⊔ f y.
  Proof.
    apply ord_le_trans with (f (supOrd (fun b:bool => if b then x else y))).
    - apply normal_monotone; auto.
      apply lub_least.
      + apply (sup_le bool (fun b => if b then x else y) true).
      + apply (sup_le bool (fun b => if b then x else y) false).
    - eapply ord_le_trans; [ apply normal_continuous; auto; exact false |].
      apply sup_least.
      intros [|]; [ apply lub_le1 | apply lub_le2 ].
  Qed.
End normal_fixpoints.

Add Parametric Morphism f (Hf:normal_function f) : (normal_fix f)
  with signature ord_le ++> ord_le as normal_fix_le_mor.
Proof.
  apply normal_fix_monotone_le; auto.
Qed.


Add Parametric Morphism f (Hf:normal_function f) : (normal_fix f)
  with signature ord_eq ==> ord_eq as normal_fix_eq_mor.
Proof.
  unfold ord_eq; intuition; apply normal_fix_monotone_le; auto.
Qed.

(* Natural numbers have an ordinal size.
 *)
Fixpoint natOrdSize (x:nat) :=
  match x with
  | O => zeroOrd
  | S n => succOrd (natOrdSize n)
  end.

Canonical Structure ω : Ord :=
  ord nat natOrdSize.

Definition powOmega (x:Ord) : Ord := expOrd ω x.

Lemma omega_gt1 : ord_lt oneOrd ω.
Proof.
  rewrite ord_lt_unfold.
  exists 1. simpl.
  apply ord_le_refl.
Qed.

Lemma powOmega_normal : normal_function powOmega.
Proof.
  apply NormalFunction.
  + apply expOrd_monotone_le.
  + apply mono_lt_increasing.
    intros; apply (expOrd_monotone_lt ω omega_gt1 y x); auto.
  + red; intros A f a0; apply (expOrd_continuous ω omega_gt1 A f a0).
Qed.

Definition enum_fixpoints (f:Ord -> Ord) : Ord -> Ord :=
  fix rec (x:Ord) : Ord :=
  match x with
  | ord B g => normal_fix f (ord B (fun b => rec (g b)))
  end.

Lemma enum_are_fixpoints f :
  normal_function f ->
  forall x, enum_fixpoints f x ≈ f (enum_fixpoints f x).
Proof.
  intros.
  destruct x; simpl.
  apply normal_fixpoint; auto.
Qed.

Lemma enum_fixpoints_zero f :
  normal_function f ->
  enum_fixpoints f zeroOrd ≈ normal_fix f zeroOrd.
Proof.
  simpl.
  split; apply normal_fix_monotone_le; auto.
  - rewrite ord_le_unfold; simpl; intuition.
  - rewrite ord_le_unfold; simpl; intuition.
Qed.

Lemma enum_fixpoints_succ f x :
  enum_fixpoints f (succOrd x) ≈ normal_fix f (succOrd (enum_fixpoints f x)).
Proof.
  simpl; intros. reflexivity.
Qed.

Lemma enum_fixpoints_monotone f :
  normal_function f ->
  (forall x y,
      (x ≤ y -> enum_fixpoints f x ≤ enum_fixpoints f y) /\
      (x < y -> enum_fixpoints f x < enum_fixpoints f y)).
Proof.
  intros Hf x.
  induction x as [B g Hx].
  induction y as [C h Hy].
  simpl; intuition.
  - apply normal_fix_least; auto.
    rewrite ord_le_unfold; simpl; intros.
    rewrite ord_le_unfold in H.
    specialize (H a). simpl in H.
    apply (Hx a (ord C h)); auto.
    apply normal_prefixpoint; auto.
  - rewrite ord_lt_unfold in H.
    destruct H as [i ?].
    simpl in H.
    apply Hy in H.
    simpl in H.
    eapply ord_lt_le_trans; [| apply normal_fix_above ].
    rewrite ord_lt_unfold. exists i. simpl.
    auto.
Qed.

Lemma enum_fixpoints_monotone_lt f :
  normal_function f ->
  (forall x y, x < y -> enum_fixpoints f x < enum_fixpoints f y).
Proof.
  intros; apply enum_fixpoints_monotone; auto.
Qed.

Lemma enum_fixpoints_monotone_le f :
  normal_function f ->
  (forall x y, x ≤ y -> enum_fixpoints f x ≤ enum_fixpoints f y).
Proof.
  intros; apply enum_fixpoints_monotone; auto.
Qed.

Lemma enum_fixpoints_cont f :
  normal_function f ->
  strongly_continuous (enum_fixpoints f).
Proof.
  repeat intro.
  simpl.
  apply normal_fix_least; auto.
  rewrite ord_le_unfold.
  simpl.
  intros [a i]. simpl.
  rewrite <- (sup_le _ _ a).
  apply enum_fixpoints_monotone_lt; auto with ord.
  rewrite (normal_continuous f H A (fun i => enum_fixpoints f (f0 i)) a0).
  apply sup_least. simpl; intros.
  rewrite <- enum_are_fixpoints; auto.
  rewrite <- (sup_le _ _ a).
  auto with ord.
Qed.

Lemma enum_fixpoints_normal f :
  normal_function f ->
  normal_function (enum_fixpoints f).
Proof.
  intros; constructor.
  - apply enum_fixpoints_monotone_le; auto.
  - apply mono_lt_increasing.
    apply enum_fixpoints_monotone_lt; auto.
  - apply enum_fixpoints_cont; auto.
Qed.

Lemma enum_least f :
  normal_function f ->
  forall (x z:Ord),
    f z ≤ z ->
    (forall x', x' < x -> enum_fixpoints f x' < z) ->
    enum_fixpoints f x ≤ z.
Proof.
  intro Hf.
  induction x as [B g Hx]. simpl; intros.
  apply normal_fix_least; auto.
  rewrite ord_le_unfold; simpl; intros.
  apply H0.
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
  apply normal_fix_least; auto.
  - rewrite ord_le_unfold. simpl; intro a.
    rewrite <- (normal_fix_above).
    rewrite ord_lt_unfold. simpl. exists a.
    auto.
  - rewrite H.
    apply normal_prefixpoint; auto.
Qed.

Add Parametric Morphism f (Hf:normal_function f) : (enum_fixpoints f)
  with signature ord_le ++> ord_le  as enum_fixpoint_le_mor.
Proof.
  apply enum_fixpoints_monotone_le; auto.
Qed.

Add Parametric Morphism f (Hf:normal_function f) : (enum_fixpoints f)
  with signature ord_eq ==> ord_eq  as enum_fixpoint_eq_mor.
Proof.
  unfold ord_eq; intuition; apply enum_fixpoints_monotone_le; auto.
Qed.

Definition ε (x:Ord) := enum_fixpoints powOmega x.

Lemma epsilon_fixpoint x : ε x ≈ expOrd ω (ε x).
Proof.
  intros. unfold ε. apply enum_are_fixpoints.
  apply powOmega_normal.
Qed.

Fixpoint veblen (x:Ord) : Ord -> Ord :=
  match x with
  | ord A f => fun y => expOrd ω y ⊔ supOrd (fun a => enum_fixpoints (veblen (f a)) y)
  end.

Lemma veblen_unroll (x:Ord) (y:Ord) :
  veblen x y =
  expOrd ω y ⊔ supOrd (fun a:x => enum_fixpoints (veblen (x a)) y).
Proof.
  destruct x; auto.
Qed.


Lemma veblen_normal (x:Ord) : normal_function (veblen x).
Proof.
  induction x as [A f Hx]; simpl.
  constructor; simpl.
  - simpl; intros.
    apply lub_least.
    + rewrite <- lub_le1.
      apply expOrd_monotone_le. auto.
    + rewrite <- lub_le2.
      apply sup_ord_le_morphism.
      red; simpl; intros.
      apply enum_fixpoints_monotone_le; auto.
  - simpl; intros.
    rewrite <- lub_le1.
    apply normal_increasing.
    apply powOmega_normal.
  - red; intros.
    apply lub_least.
    + rewrite (normal_continuous (expOrd ω) powOmega_normal _ f0 a0).
      apply sup_least; intro i.
      rewrite <- (sup_le _ _ i).
      apply lub_le1.
    + apply sup_least; intro i.
      rewrite (enum_fixpoints_cont (veblen (f i)) (Hx i) _ f0 a0).
      apply sup_least. intros.
      rewrite <- (sup_le _ _ a).
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ i).
      auto with ord.
Qed.

Lemma veblen_unroll_nonzero (x:Ord) (y:Ord) :
  zeroOrd < x ->
  veblen x y ≈ supOrd (fun a:x => enum_fixpoints (veblen (x a)) y).
Proof.
  intros.
  rewrite veblen_unroll.
  split.
  - apply lub_least; auto with ord.
    rewrite ord_lt_unfold in H.
    destruct H as [b0 ?].
    rewrite <- (sup_le _ _ b0).
    rewrite enum_are_fixpoints; [ | apply veblen_normal ].
    rewrite veblen_unroll at 1.
    rewrite <- lub_le1.
    apply expOrd_monotone_le.
    apply mono_lt_increasing.
    apply enum_fixpoints_monotone_lt.
    apply veblen_normal.
  - apply lub_le2.
Qed.

Lemma veblen_zero x :
  veblen zeroOrd x ≈ expOrd ω x.
Proof.
  split; simpl.
  - apply lub_least; auto with ord.
    apply sup_least; intuition.
  - apply lub_le1.
Qed.

Lemma veblen_succ x y :
  veblen (succOrd x) y ≈ enum_fixpoints (veblen x) y.
Proof.
  split; simpl.
  - apply lub_least.
    + destruct x as [A f]; simpl.
      rewrite (enum_are_fixpoints); simpl.
      rewrite <- lub_le1.
      apply expOrd_monotone_le.
      apply mono_lt_increasing.
      apply enum_fixpoints_monotone_lt.
      apply (veblen_normal (ord A f)).
      apply (veblen_normal (ord A f)).
    + apply sup_least. simpl; intros; auto with ord.
  - rewrite <- lub_le2.
    rewrite <- (sup_le _ _ tt).
    auto with ord.
Qed.

Lemma veblen_one x :
  veblen oneOrd x ≈ ε x.
Proof.
  unfold oneOrd.
  rewrite veblen_succ.
  unfold ε.
  split; apply enum_fixpoints_func_mono; auto.
  - apply veblen_normal.
  - apply powOmega_normal.
  - intro. apply veblen_zero.
  - apply powOmega_normal.
  - apply veblen_normal.
  - intro. apply veblen_zero.
Qed.

Lemma veblen_monotone_first (x y z:Ord) :
  x ≤ y -> veblen x z ≤ veblen y z.
Proof.
  revert y z. induction x as [A f Hx]; simpl; intros.
  apply lub_least.
  - destruct y; simpl.
    apply lub_le1.
  - apply sup_least. intro a.
    destruct y as [B g]; simpl.
    rewrite <- lub_le2.
    rewrite ord_le_unfold in H.
    specialize (H a).
    rewrite ord_lt_unfold in H.
    simpl in H.
    destruct H as [b ?].
    rewrite <- (sup_le _ _ b).
    apply enum_fixpoints_func_mono.
    + apply veblen_normal.
    + apply veblen_normal.
    + intros. apply Hx. auto.
Qed.

Lemma veblen_continuous_first y :
  strongly_continuous (fun x => veblen x y).
Proof.
  red; simpl; intros.
  apply lub_least; simpl.
  rewrite <- (sup_le _ _ a0).
  rewrite <- veblen_zero.
  apply veblen_monotone_first.
  apply zero_least.
  apply sup_least.
  intros [a q]; simpl.
  rewrite <- (sup_le _ _ a).
  destruct (f a) as [Q r]. simpl in *.
  rewrite <- lub_le2.
  rewrite <- (sup_le _ _ q).
  auto with ord.
Qed.

Add Parametric Morphism : veblen
  with signature ord_le ++> ord_le ++> ord_le as veblen_le_mor.
Proof.
  intros.
  apply ord_le_trans with (veblen x y0).
  apply normal_monotone; auto. apply veblen_normal.
  apply veblen_monotone_first; auto.
Qed.

Add Parametric Morphism : veblen
  with signature ord_eq ==> ord_eq ==> ord_eq as veblen_eq_mor.
Proof.
  unfold ord_eq; intuition; apply veblen_le_mor; auto.
Qed.

Lemma veblen_exp_prefixpoint b x :
  zeroOrd < b ->
  expOrd ω (veblen b x) ≤ veblen b x.
Proof.
  intros.
  revert x.
  intros.
  destruct b as [B g].
  simpl.
  rewrite <- lub_le2 at 2.
  rewrite normal_lub; [ | apply powOmega_normal ].
  apply lub_least.
  - rewrite ord_lt_unfold in H.
    destruct H as [b ?]. simpl in *.
    rewrite  <- (sup_le _ _ b).
    rewrite enum_are_fixpoints; [ | apply veblen_normal ].
    rewrite (veblen_unroll (g b)) at 1.
    rewrite <- lub_le1.
    apply expOrd_monotone_le.
    rewrite enum_are_fixpoints; [ | apply veblen_normal ].
    rewrite (veblen_unroll (g b)) at 1.
    rewrite <- lub_le1.
    apply expOrd_monotone_le.
    apply normal_increasing.
    apply enum_fixpoints_normal.
    apply veblen_normal.
  - rewrite ord_lt_unfold in H.
    destruct H as [b0 _].
    rewrite (normal_continuous powOmega powOmega_normal _ (fun a => enum_fixpoints (veblen (g a)) x) b0).
    apply sup_least; simpl; intros b.
    unfold powOmega.
    rewrite <- (sup_le _ _ b).
    rewrite enum_are_fixpoints at 2; [ | apply veblen_normal ].
    rewrite (veblen_unroll (g b)).
    rewrite <- lub_le1.
    auto with ord.
Qed.

Lemma normal_veblen_sup : forall (b:Ord),
  zeroOrd < b ->
  normal_function (fun z : Ord => supOrd (fun a0 : b => veblen (b a0) z)).
Proof.
  intros. constructor.
  - intros.
    apply sup_least; intro i.
    rewrite <- (sup_le _ _ i).
    apply normal_monotone; auto.
    apply veblen_normal.
  - intros.
    rewrite ord_lt_unfold in H.
    destruct H as [b0 ?].
    rewrite <- (sup_le _ _ b0).
    apply normal_increasing.
    apply veblen_normal.
  - red; simpl; intros.
    apply sup_least; intros i.
    rewrite (normal_continuous (veblen (b i)) (veblen_normal _) A f a0).
    apply sup_least; intro a.
    rewrite <- (sup_le _ _ a).
    rewrite <- (sup_le _ _ i).
    auto with ord.
Qed.


Lemma veblen_lt_prefixpoint (a b x:Ord) :
  a < b -> veblen a (veblen b x) ≤ veblen b x.
Proof.
  intros.
  rewrite (veblen_unroll a).
  apply lub_least.
  - apply veblen_exp_prefixpoint.
    eapply ord_le_lt_trans with a; auto.
    apply zero_least.
  - apply sup_least.
    intros q.
    assert (zeroOrd < b).
    { apply ord_le_lt_trans with a; auto.
      apply zero_least.
    }

    rewrite (veblen_unroll_nonzero b x) at 2; auto.
    apply ord_le_trans with
        (enum_fixpoints (fun z => supOrd (fun a0 => veblen (b a0) z)) x).
    + rewrite (enum_are_fixpoints (fun z => supOrd (fun a0 => veblen (b a0) z))).
      * rewrite ord_lt_unfold in H.
        destruct H as [b0 ?].
        apply enum_least.
        ** apply veblen_normal.
        ** rewrite <- (sup_le _ _ b0) at 2.
           apply veblen_le_mor.
           *** rewrite <- H.
               apply ord_lt_le.
               apply index_lt.
           *** apply sup_least. intros b'.
               eapply ord_le_trans; [|   apply (enum_are_fixpoints (fun z => supOrd (fun a0 => veblen (b a0) z)))].
               **** rewrite <- (sup_le _ _ b').
                    auto with ord.
               **** apply normal_veblen_sup; auto.
        ** intros.
           rewrite <- (sup_le _ _ b0).
           rewrite (veblen_unroll).
           rewrite <- lub_le2.
           rewrite ord_le_unfold in H.
           generalize (H q). intros.
           rewrite ord_lt_unfold in H2.
           destruct H2 as [z ?].
           rewrite <- (sup_le _ _ z).
           eapply ord_le_lt_trans.
           *** eapply (enum_fixpoints_func_mono _ (veblen ((b b0) z))).
               **** apply veblen_normal.
               **** apply veblen_normal.
               **** intros. apply veblen_monotone_first. auto.
           *** apply enum_fixpoints_monotone_lt.
               **** apply veblen_normal.
               **** eapply ord_lt_le_trans.
                    ***** apply H1.
                    ***** rewrite veblen_unroll_nonzero; auto.
                          apply sup_least. intros.
                          apply enum_fixpoints_func_mono.
                          ****** apply veblen_normal.
                          ****** apply normal_veblen_sup; auto.
                          ****** intros. rewrite <- (sup_le _ _ a0). auto with ord.
      * apply normal_veblen_sup; auto.
    + admit. (* !!! plausible, but not at all obvious *)
Admitted.

Lemma veblen_increasing_first x y :
  x ≤ veblen x y.
Abort. (* ???? *)


(** * Lexicographic orders, encoded as ordinals *)

Definition lex {α β:Ord} (x:α) (y:β) :=
  β ⊗ sz x ⊕ sz y.

Lemma lex1 (α β:Ord) (x x':α) (y y':β) :
  x ◃ x' ->
  lex x y < lex x' y'.
Proof.
  unfold lex; intros.
  apply ord_lt_le_trans with (β ⊗ succOrd x ⊕ y').
  - rewrite <- (addOrd_le1 _ (sz y')).
    rewrite mulOrd_succ.
    apply addOrd_monotone_lt2; auto with ord.
  - apply addOrd_monotone_le; auto with ord.
    apply mulOrd_monotone_le2.
    apply succ_least. auto.
Qed.

Lemma lex2 (α β:Ord) (x x':α) (y y':β) :
  x ⊴ x' ->
  y ◃ y' ->
  lex x y < lex x' y'.
Proof.
  unfold lex; intros.
  rewrite H.
  apply addOrd_monotone_lt2; auto.
Qed.

(** * Well-founded relations generate ordinals *)

Section wf_ord.
  Variable A:Type.
  Variable R:A -> A -> Prop.
  Hypothesis Hwf : well_founded R.

  Fixpoint mk_wf_ord (a:A) (X:Acc R a) : Ord :=
    match X with
    | Acc_intro _ H => ord { a':A | R a' a } (fun x => mk_wf_ord (proj1_sig x) (H _ (proj2_sig x)))
    end.
  Definition wf_ord (a:A) : Ord := mk_wf_ord a (Hwf a).

  Lemma wf_ord_lt : forall a a', R a' a -> wf_ord a' < wf_ord a.
  Proof.
    unfold wf_ord. intros a a'.
    generalize (Hwf a'). revert a'.
    generalize (Hwf a).
    induction a using (well_founded_induction Hwf); intros.
    destruct a0; simpl.
    rewrite ord_lt_unfold.
    exists (exist _ a' H0); simpl.
    rewrite ord_le_unfold.
    destruct a1. simpl; intros.
    destruct a2. simpl.
    apply H; auto.
  Qed.

  Lemma wf_ord_lt_trans : forall a a', clos_trans _ R a' a -> wf_ord a' < wf_ord a.
  Proof.
    intros; induction H.
    - apply wf_ord_lt; auto.
    - eapply ord_lt_trans; eauto.
  Qed.

  Lemma wf_ord_le_trans : forall a a', clos_refl_trans _ R a' a -> wf_ord a' ≤ wf_ord a.
  Proof.
    intros; induction H.
    - apply ord_lt_le; apply wf_ord_lt; auto.
    - apply ord_le_refl.
    - eapply ord_le_trans; eauto.
  Qed.

End wf_ord.


Definition ord_measure (o:Ord) := Acc ord_lt o.

Definition Ack_measure (m:nat) (n:nat) := ord_measure (@lex ω ω m n).

Program Fixpoint Ackdef (m:nat) (n:nat) {HM : Ack_measure m n} {struct HM}: nat :=
  match m, n with
  | O   , _    => n+1
  | S m', 0    => Ackdef m' 1
  | S m', S n' => Ackdef m' (Ackdef m n')
  end.
Next Obligation.
  intros; subst.
  destruct HM as [HM]; apply HM; simpl.
  apply lex1.
  apply succ_lt.
Defined.
Next Obligation.
  intros; subst.
  destruct HM as [HM]; apply HM; simpl.
  apply lex2.
  apply ord_le_refl.
  apply succ_lt.
Defined.
Next Obligation.
  destruct HM as [HM]; apply HM; simpl.
  apply lex1.
  apply succ_lt.

  destruct HM as [HM]; apply HM; simpl.
  apply lex1.
  apply succ_lt.
Defined.

Definition Ack m n := @Ackdef m n (ord_lt_wf _).

Lemma subterm_trans : forall {A B C:Ord} (x:A) (y:B) (z:C),
  x ◃ y -> y ◃ z -> x ◃ z.
Proof.
  simpl; intros. eapply ord_lt_trans; eauto.
Qed.

Lemma size_discriminate : forall (A:Ord) (x y:A), x ◃ y -> x <> y.
Proof.
  repeat intro; subst y.
  apply (ord_lt_irreflexive _ H).
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

Lemma lub_trans1 x y z : x ≤ y -> x ≤ y ⊔ z.
Proof.
  intros.
  apply ord_le_trans with y; auto.
  apply lub_le1.
Qed.

Lemma lub_trans2 x y z : x ≤ z -> x ≤ y ⊔ z.
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply lub_le2.
Qed.

Lemma add_trans1 x y z : x ≤ y -> x ≤ y ⊕ z.
Proof.
  intros.
  apply ord_le_trans with y; auto.
  apply addOrd_le1.
Qed.

Lemma add_trans1' x y z : x < y -> x < y ⊕ z.
Proof.
  intros.
  apply ord_lt_le_trans with y; auto.
  apply addOrd_le1.
Qed.

Lemma add_trans2 x y z : x ≤ z -> x ≤ y ⊕ z.
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply addOrd_le2.
Qed.

Lemma add_trans2' x y z : x < z -> x < y ⊕ z.
Proof.
  intros.
  apply ord_lt_le_trans with z; auto.
  apply addOrd_le2.
Qed.

Hint Unfold ordSize : ord.
Hint Resolve
     limit_lt lub_le1 lub_le2
     ord_lt_trans ord_le_trans ord_eq_trans
     succ_trans
     succ_trans'
     lub_trans1 lub_trans2
     add_trans1 add_trans2
     add_trans1' add_trans2'
     ord_lt_le ord_le_refl ord_eq_refl : ord.


(* Lists of ordinal-sized types have an ordinal size.
 *)
Definition listOrd {A} (f:A -> Ord) : list A -> Ord :=
  fix listOrd (l:list A) : Ord :=
    match l with
    | [] => zeroOrd
    | x::xs => succOrd (addOrd (f x) (listOrd xs))
    end.

Canonical Structure ListOrd (A:Ord) : Ord :=
  ord (list A) (listOrd (ordSize A)).

Lemma listAdd (A:Ord) (xs ys:list A) :
  sz (xs ++ ys) ≈ sz xs ⊕ sz ys.
Proof.
  induction xs; simpl.
  - rewrite addOrd_comm.
    apply addOrd_zero.
  - rewrite addOrd_succ.
    rewrite IHxs.
    rewrite addOrd_assoc.
    reflexivity.
Qed.


(** Basic lemmas about constructors for nat and list *)
Lemma S_lt : forall x:ω, x ◃ S x.
Proof.
  simpl; auto with ord.
Qed.

Lemma head_lt : forall (A:Ord) (h:A) (t:list A), h ◃ (h::t).
Proof.
  simpl; eauto with ord.
Qed.

Lemma tail_lt : forall (A:Ord) (h:A) (t:list A), t ◃ (h::t).
Proof.
  simpl; eauto with ord.
Qed.

Hint Resolve head_lt tail_lt : ord.

Lemma app_lt1 : forall (A:Ord) (xs ys:list A), ys <> [] ->  xs ◃ xs ++ ys.
Proof.
  intros. rewrite listAdd. simpl.
  rewrite addOrd_zero at 1.
  apply addOrd_monotone_lt2.
  destruct ys.
  + elim H; auto.
  + simpl.
    apply succ_trans.
    apply zero_least.
Qed.

Lemma app_lt2 : forall (A:Ord) (xs ys:list A), xs <> [] -> ys ◃ xs ++ ys.
Proof.
  intros. rewrite listAdd. simpl.
  rewrite addOrd_zero at 1.
  rewrite addOrd_comm.
  apply addOrd_monotone_lt1.
  destruct xs.
  + elim H; auto.
  + simpl.
    apply succ_trans.
    apply zero_least.
Qed.

Require Import Permutation.

Lemma Permutation_size (A:Ord) (r s:list A) : Permutation r s -> sz r ≈ sz s.
Proof.
  intro H; induction H; simpl; eauto with ord.
  - rewrite IHPermutation; auto with ord.
  - repeat rewrite addOrd_succ2.
    do 2 rewrite addOrd_assoc.
    rewrite (addOrd_comm (A y)).
    auto with ord.
Qed.

Lemma In_lt : forall (A:Ord) (x:A) l, In x l -> x ◃ l.
Proof.
  induction l; simpl; intuition; subst; eauto with ord.
Qed.
Hint Resolve In_lt : ord.


(** Let's play around with some Ltac support.

    This Ltac code is currently super first-pass, and could probably
    be improved a lot.
  *)
Ltac try_ord := try solve [ auto with ord | simpl; auto 100 with ord | simpl; eauto with ord ].

Ltac subterm_trans x :=
  apply subterm_trans with x; try_ord.

Ltac esubterm_trans :=
  eapply subterm_trans; try_ord.

Ltac ord_crush :=
  intros; apply size_discriminate;
  try_ord;
  repeat (progress esubterm_trans).

(** Some simple examples based on nats and lists *)

Goal forall x:nat, x <> S (S (S (S x))).
Proof.
  ord_crush.
Qed.


Goal forall (a b c:nat) x, x <> a::b::c::x.
Proof.
  ord_crush.
Qed.


(** An example based on even/odd numbers *)

Inductive even :=
| even0 : even
| evenS : odd -> even
with odd :=
| oddS : even -> odd.

(* Some fairly boilerplate code defining the ordinal size function,
   and registering associated canconical structures.
 *)
Fixpoint even_size (x:even) : Ord :=
  match x with
  | even0 => zeroOrd
  | evenS y => succOrd (odd_size y)
  end
with
odd_size (x:odd) : Ord :=
  match x with
  | oddS y => succOrd (even_size y)
  end.

Canonical Structure evenOrdSize :=
  ord even even_size.
Canonical Structure oddOrdSize :=
  ord odd odd_size.

(* Now we can crush that proof *)
Lemma even_odd_neq : forall x, x <> oddS (evenS (oddS (evenS x))).
Proof.
  ord_crush.
Qed.


(** Countably-wide rose trees *)

Inductive tree :=
| leaf : tree
| node : (nat -> tree) -> tree.

Fixpoint tree_size (t:tree) : Ord :=
  match t with
  | leaf => zeroOrd
  | node f => funOrd tree_size f
  end.

Canonical Structure treeOrdSize :=
  ord tree tree_size.

(* Not entirely sure how to automate this proof better... *)
Goal forall x f g n m ,
    g m = x ->
    f n = node g ->
    x <> node f.
Proof.
  intros. apply size_discriminate.
  apply subterm_trans with (f n).
  rewrite H0.
  rewrite <- H.
  apply fun_lt.
  apply fun_lt.
Qed.

(** A more complicated example using mutual recursion,
    nested lists and dependent types.
 *)
Inductive asdf : nat -> Set :=
| mkAsdf : forall n, list (qwerty n) -> asdf n
with
qwerty : nat -> Set :=
| emptyQwerty : qwerty 0
| someQwerty  : forall n, qwerty n -> (forall m, asdf m) -> qwerty (S n).

Fixpoint asdf_size n (x:asdf n) : Ord :=
  match x with
  | mkAsdf n xs => succOrd (listOrd (qwerty_size n) xs)
  end
with qwerty_size n (x:qwerty n) : Ord :=
  match x with
  | emptyQwerty => zeroOrd
  | someQwerty n x y => succOrd (addOrd (qwerty_size n x) (depOrd asdf_size y))
  end.

Canonical Structure AsdfOrdSize n :=
  ord (asdf n) (asdf_size n).
Canonical Structure QwertyOrdSize n :=
  ord (qwerty n) (qwerty_size n).

Goal forall n a b c f,
  f (S n) <> mkAsdf _ [a; b; someQwerty _ c f].
Proof.
  ord_crush.
Qed.
