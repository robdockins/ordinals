Require Import List.
Require Import Relations.
Require Import Wf.
Require Import Wellfounded.Transitive_Closure.

Import ListNotations.
Open Scope list.

Unset Printing Records.

(** Ordinals, represented as Type-indexed trees
  * of potentially infinite width, but finite depth.
  *)
Inductive Ord : Type :=
  ord { ordCarrier :> Type
      ; ordSize :> ordCarrier -> Ord
      }.

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

(** Characteristic equation for less-than *)
Lemma ord_lt_unfold x y :
  ord_lt x y = exists b:y, ord_le x (y b).
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

(** Characteristic equation for less-equal *)
Lemma ord_le_unfold x y :
  ord_le x y = forall a:x, ord_lt (x a) y.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

Global Opaque ord_le ord_lt.

(** Less-than implies less-equal
  *)
Lemma ord_lt_le : forall b a,
  ord_lt a b -> ord_le a b.
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
Lemma ord_le_refl x : ord_le x x.
Proof.
  induction x as [A f].
  rewrite ord_le_unfold.
  intros.
  rewrite ord_lt_unfold.
  exists a. apply H.
Qed.

(** These various transitivity-releated facts need to
    be proved simultaneuously.
  *)
Lemma ord_trans :
  forall b a c,
    (ord_le a b -> ord_le b c -> ord_le a c) /\
    (ord_le a b -> ord_lt b c -> ord_lt a c) /\
    (ord_lt a b -> ord_le b c -> ord_lt a c).
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
    ord_le a b -> ord_le b c -> ord_le a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** Less-than is transitive *)
Lemma ord_lt_trans a b c :
    ord_lt a b -> ord_lt b c -> ord_lt a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
  apply H2.
  apply ord_lt_le; auto.
Qed.

(** Less-equal preserves less-than *)
Lemma ord_lt_le_trans a b c :
  ord_lt a b -> ord_le b c -> ord_lt a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

Lemma ord_le_lt_trans a b c :
  ord_le a b -> ord_lt b c -> ord_lt a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** The less-than ordering on ordinals is well-founded.
  *)
Lemma ord_lt_acc : forall x y,  ord_le y x -> Acc ord_lt y.
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
Corollary ord_lt_irreflexive : forall x, ord_lt x x -> False.
Proof.
  induction x using (well_founded_induction ord_lt_wf).
  firstorder.
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
Definition supOrd {A:Type} (f:A -> Ord) :=
  ord (sigT (fun a => ordCarrier (f a)))
      (fun ai => ordSize (f (projT1 ai)) (projT2 ai)).

Fixpoint glbOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A*B) (fun ab => glbOrd (f (fst ab)) (g (snd ab)))
  end.

Definition predOrd (x:Ord) : Ord :=
  match x with
  | ord A f => supOrd f
  end.

Definition hasMaxElement A (f:A -> Ord) :=
  exists a, forall a', ord_le (f a') (f a).

Definition ascendingSet A (f:A -> Ord) :=
  forall a, exists a', ord_lt (f a) (f a').

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
Lemma succ_monotone_lt : forall a b, ord_lt a b -> ord_lt (succOrd a) (succOrd b).
Proof.
  intros.
  rewrite ord_lt_unfold. simpl. exists tt.
  rewrite ord_le_unfold. simpl. auto.
Qed.

Lemma succ_monotone_le : forall a b, ord_le a b -> ord_le (succOrd a) (succOrd b).
Proof.
  intros.
  rewrite ord_le_unfold. simpl; intros _.
  rewrite ord_lt_unfold. simpl. exists tt.
  auto.
Qed.

Lemma succ_lt : forall o, ord_lt o (succOrd o).
Proof.
  intros.
  rewrite ord_lt_unfold. simpl. exists tt. apply ord_le_refl.
Qed.

Lemma succ_least : forall x y, ord_lt x y -> ord_le (succOrd x) y.
Proof.
  intros.
  rewrite ord_le_unfold. simpl; auto.
Qed.

(** The supremum ordinal is nonstrictly above all the ordinals in the
  * collection defined by "f".  Morover it is it the smallest such.
  *)
Lemma sup_le : forall A (f:A -> Ord) a, ord_le (f a) (supOrd f).
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
    (forall a, ord_le (f a) z) -> ord_le (supOrd f) z.
Proof.
  intros.
  rewrite ord_le_unfold.
  simpl; intros.
  destruct a as [a b]. simpl.
  specialize (H a).
  rewrite ord_le_unfold in H.
  specialize (H b).
  auto.
Qed.

(** The limit ordinal is strictly above all the ordinals in
  * the collection defined by "f".  Moreover it is the smallest
  * such.
  *)
Lemma limit_lt : forall A (f:A -> Ord) i, ord_lt (f i) (limOrd f).
Proof.
  intros. rewrite ord_lt_unfold. simpl.
  exists i. apply ord_le_refl.
Qed.

Lemma limit_least : forall A (f:A -> Ord) z,
  (forall i, ord_lt (f i) z) -> ord_le (limOrd f) z.
Proof.
  intros. rewrite ord_le_unfold.
  simpl. auto.
Qed.

(** Supremum and limit are closely related operations.
  * We always have: sup f <= lim f <= succ (sup f).
  * Moreover: lim f = sup (succ . f)
  * When f is an ascending set, lim f = sup f
  * When f has a maximal element, lim f = succ (sup f)
  *)
Lemma sup_lim : forall A (f:A -> Ord),
  ord_le (supOrd f) (limOrd f).
Proof.
  intros.
  apply sup_least.
  intros.
  apply ord_lt_le.
  apply limit_lt.
Qed.

Lemma lim_sup : forall A (f:A -> Ord),
  ord_le (limOrd f) (succOrd (supOrd f)).
Proof.
  intros.
  apply limit_least. intro a.
  apply ord_le_lt_trans with (supOrd f).
  apply sup_le.
  apply succ_lt.
Qed.

Lemma sup_succ_lim : forall A (f:A -> Ord),
  ord_eq (limOrd f) (supOrd (fun a:A => succOrd (f a))).
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
  ord_eq (limOrd f) (supOrd f).
Proof.
  intros.
  split; [ | apply sup_lim ].
  apply limit_least. intro a.
  destruct (H a) as [a' ?].
  apply ord_lt_le_trans with (f a'); auto.
  apply sup_le.
Qed.

Lemma succ_sup_lim : forall A (f:A -> Ord),
  hasMaxElement A f ->
  ord_eq (limOrd f) (succOrd (supOrd f)).
Proof.
  intros.
  split; [ apply lim_sup |].
  apply succ_least.
  destruct H as [amax Hamax].
  rewrite ord_lt_unfold. simpl. exists amax.
  apply sup_least. auto.
Qed.

(** pred(y) is the smallest ordinal that is (nonstrictly) above
  * all the ordinals (strictly) below y.
  *)
Lemma pred_le y :
  forall x, ord_lt x y -> ord_le x (predOrd y).
Proof.
  intros.
  rewrite ord_lt_unfold in H.
  destruct H as [b Hb].
  rewrite ord_le_unfold.
  intro a.
  rewrite ord_lt_unfold.
  destruct y as [B g]; simpl in *.
  rewrite ord_le_unfold in Hb.
  specialize (Hb a).
  rewrite ord_lt_unfold in Hb.
  destruct Hb as [c ?].
  exists (existT _ b c); simpl.
  auto.
Qed.

Lemma pred_least y z :
  (forall x, ord_lt x y -> ord_le x z) ->
  ord_le (predOrd y) z.
Proof.
  intros.
  rewrite ord_le_unfold.
  destruct y as [B g]. simpl.
  intros [b c]. simpl.
  assert (ord_le (g b) z).
  { apply H. rewrite ord_lt_unfold. simpl. exists b. apply ord_le_refl. }
  rewrite ord_le_unfold in H0.
  apply H0.
Qed.

Lemma pred_zero : ord_eq zeroOrd (predOrd zeroOrd).
Proof.
  split.
  - apply zero_least.
  - apply pred_least.
    intros.
    rewrite ord_lt_unfold in H.
    destruct H. destruct x0.
Qed.

Lemma pred_successor x : successorOrdinal x -> ord_lt (predOrd x) x.
Proof.
  destruct x as [A f]; simpl; intros.
  rewrite ord_lt_unfold.
  red in H. simpl in *.
  destruct H as [a Ha].
  exists a. apply sup_least. auto.
Qed.

Lemma pred_limit x : limitOrdinal x -> ord_eq x (predOrd x).
Proof.
  intros.
  split.
  - destruct x as [A f]; simpl in *; intros.
    destruct H as [_ H].
    rewrite ord_le_unfold. simpl.
    intros.
    rewrite ord_lt_unfold. simpl.
    destruct (H a) as [a' ?].
    rewrite ord_lt_unfold in H0.
    destruct H0 as [q ?].
    exists (existT _ a' q). simpl. auto.
  - apply pred_least.
    apply ord_lt_le.
Qed.

Lemma pred_succ x : ord_eq x (predOrd (succOrd x)).
Proof.
  split.
  - apply pred_le. apply succ_lt.
  - apply pred_least. intros.
    rewrite ord_lt_unfold in H. simpl in *.
    destruct H. auto.
Qed.

Lemma succ_pred x : ord_le x (succOrd (predOrd x)).
Proof.
  rewrite ord_le_unfold. intros.
  rewrite ord_lt_unfold. simpl. exists tt.
  apply pred_le.
  rewrite ord_lt_unfold. exists a.
  apply ord_le_refl.
Qed.

Lemma succ_pred' x : successorOrdinal x -> ord_eq x (succOrd (predOrd x)).
Proof.
  intros.
  split.
  - apply succ_pred.
  - apply succ_least; apply pred_successor; auto.
Qed.

(** glb is the greatest lower bound of its arguments.
 *)
Lemma glb_le1 : forall x y, ord_le (glbOrd x y) x.
Proof.
  induction x as [A f Hx]. destruct y as [B g]. simpl.
  rewrite ord_le_unfold; simpl.
  intros [a b]; simpl.
  rewrite ord_lt_unfold; simpl.
  exists a. apply Hx.
Qed.

Lemma glb_le2 : forall y x, ord_le (glbOrd x y) y.
Proof.
  induction y as [B g Hy]. destruct x as [A f]. simpl.
  rewrite ord_le_unfold; simpl.
  intros [a b]; simpl.
  rewrite ord_lt_unfold; simpl.
  exists b. apply Hy.
Qed.

Lemma glb_greatest : forall z x y, ord_le z x -> ord_le z y -> ord_le z (glbOrd x y).
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

(** lub is the least upper bound of its arguments.
  *)
Lemma lub_le1 : forall x y, ord_le x (lubOrd x y).
Proof.
  intros. rewrite ord_le_unfold.
  intros.
  destruct x; destruct y; simpl.
  rewrite ord_lt_unfold.
  simpl.
  exists (inl a).
  apply ord_le_refl.
Qed.

Lemma lub_le2 : forall x y, ord_le y (lubOrd x y).
Proof.
  intros. rewrite ord_le_unfold.
  destruct x; destruct y; simpl.
  intros.
  rewrite ord_lt_unfold.
  exists (inr a).
  apply ord_le_refl.
Qed.

Lemma lub_least x y z :
  ord_le x z -> ord_le y z -> ord_le (lubOrd x y) z.
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
Lemma lub_le_comm : forall x y, ord_le (lubOrd x y) (lubOrd y x).
Proof.
  intros.
  apply lub_least.
  apply lub_le2.
  apply lub_le1.
Qed.

Lemma lub_le_assoc1 : forall x y z,
    ord_le (lubOrd x (lubOrd y z)) (lubOrd (lubOrd x y) z).
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
    ord_le (lubOrd (lubOrd x y) z) (lubOrd x (lubOrd y z)).
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
  ord_le a c -> ord_le b d -> ord_le (lubOrd a b) (lubOrd c d).
Proof.
  intros.
  apply lub_least.
  apply ord_le_trans with c; auto.
  apply lub_le1.
  apply ord_le_trans with d; auto.
  apply lub_le2.
Qed.


(**  The lub of successors is le the successor of the lub.
  *)
Lemma succ_lub x y :
 ord_le (lubOrd (succOrd x) (succOrd y)) (succOrd (lubOrd x y)).
Proof.
  apply lub_least.
  apply succ_monotone_le.
  apply lub_le1.
  apply succ_monotone_le.
  apply lub_le2.
Qed.


Definition foldOrd (z:Ord) (s:Ord -> Ord) : Ord -> Ord :=
  fix foldOrd (x:Ord) : Ord :=
    match x with
    | ord A f => lubOrd z (supOrd (fun i:A => s (foldOrd (f i))))
    end.


Lemma foldOrd_least z s (q:Ord -> Ord)
      (Hz : forall x, ord_le z (q x))
      (Hmono : forall x y, ord_le x y -> ord_le (s x) (s y))
      (Hsq : forall (x:Ord) (i:x), ord_le (s (q (x i))) (q x)) :
      (forall x, ord_le (foldOrd z s x) (q x)).
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
  ord_le (s (foldOrd z s (x i))) (foldOrd z s x).
Proof.
  destruct x as [A f]. simpl.
  eapply ord_le_trans; [ | apply lub_le2 ].
  eapply ord_le_trans; [ | apply (sup_le _ _ i)]. simpl.
  apply ord_le_refl.
Qed.

Lemma foldOrd_above_z z s x : ord_le z (foldOrd z s x).
Proof.
  destruct x as [A f]; simpl.
  apply lub_le1.
Qed.

Lemma foldOrd_monotone_le z s : forall x y,
    (forall a b, ord_le a b -> ord_le (s a) (s b)) ->
    ord_le x y -> ord_le (foldOrd z s x) (foldOrd z s y).
Proof.
  induction x as [A f Hx]. simpl; intros.
  apply lub_least.
  - destruct y; simpl.
    apply lub_le1.
  - apply sup_least. intros a; simpl.
    destruct y as [B g]. simpl.
    eapply ord_le_trans; [ | apply lub_le2 ].
    rewrite ord_le_unfold in H0.
    specialize (H0 a). simpl in H0.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [b ?]. simpl in H0.
    eapply ord_le_trans; [ | apply (sup_le _ _ b) ]. simpl.
    apply H.
    apply Hx; auto.
Qed.

Lemma mono_lt_increasing f :
  (forall x y, ord_lt x y -> ord_lt (f x) (f y)) ->
  forall a, ord_le a (f a).
Proof.
  intro Hmono.
  induction a as [B g Ha].
  rewrite ord_le_unfold. intro b. simpl.
  apply ord_le_lt_trans with (f (g b)).
  apply Ha.
  apply Hmono.
  apply limit_lt.
Qed.

Lemma foldOrd_zero z s : ord_eq (foldOrd z s zeroOrd) z.
Proof.
  split.
  - simpl.
    apply lub_least.
    + apply ord_le_refl.
    + apply sup_least. intros. elim a.
  - apply foldOrd_above_z.
Qed.

Lemma foldOrd_monotone_lt z s : forall x y,
    (forall a, ord_le z a -> ord_lt a (s a)) ->
    (forall a b, ord_le a b -> ord_le (s a) (s b)) ->
    ord_lt x y -> ord_lt (foldOrd z s x) (foldOrd z s y).
Proof.
  intros x y. revert x.
  destruct y as [B g]; simpl; intros.
  rewrite ord_lt_unfold in H1.
  destruct H1 as [b ?].
  simpl in *.
  eapply ord_lt_le_trans; [ | apply lub_le2 ].
  eapply ord_lt_le_trans; [ | apply (sup_le _ _ b) ]. simpl.
  eapply ord_le_lt_trans; [ | apply H; apply foldOrd_above_z ].
  apply foldOrd_monotone_le; auto.
Qed.

Lemma foldOrd_succ z s x :
  (forall q, ord_le z q -> ord_le z (s q)) ->
  ord_eq (foldOrd z s (succOrd x)) (s (foldOrd z s x)).
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
    + eapply ord_le_trans; [ | apply lub_le2 ].
      eapply ord_le_trans; [ | apply (sup_le _ _ tt) ]. simpl.
      apply ord_le_refl.
Qed.

Lemma foldOrd_limit z s x :
  limitOrdinal x ->
  (forall a b, ord_le a b -> ord_le (s a) (s b)) ->
  ord_eq (foldOrd z s x) (supOrd (fun i:x => foldOrd z s (x i))).
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
    apply foldOrd_monotone_le; auto.
    apply ord_lt_le.
    destruct x.
    apply limit_lt.
Qed.

Definition strongly_continuous (s:Ord -> Ord) :=
  forall A (f:A -> Ord) (a0:A), ord_le (s (supOrd f)) (supOrd (fun i:A => s (f i))).

Lemma foldOrd_strongly_continuous z s :
  strongly_continuous (foldOrd z s).
Proof.
  red; simpl; intros.
  apply lub_least.
  - eapply ord_le_trans; [ | apply (sup_le _ _ a0) ]. simpl.
    destruct (f a0) as [Q r]; simpl.
    apply lub_le1.
  - apply sup_least.
    intros [a q]; simpl.
    eapply ord_le_trans; [ | apply (sup_le _ _ a) ]. simpl.
    destruct (f a) as [Q r]. simpl.
    eapply ord_le_trans; [ | apply lub_le2 ].
    eapply ord_le_trans; [ | apply (sup_le _ _ q) ]. simpl.
    apply ord_le_refl.
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

Lemma addOrd_unfold (x y:Ord) :
  addOrd x y =
    lubOrd (limOrd (fun a:x => addOrd (x a) y))
           (limOrd (fun b:y => addOrd x (y b))).
Proof.
  destruct x; destruct y; auto.
Qed.

Global Opaque addOrd.


Lemma addOrd_le1 x y : ord_le x (addOrd x y).
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

Lemma addOrd_le2 x y : ord_le y (addOrd x y).
Proof.
  induction y as [A f Hx].
  destruct x as [B g].
  rewrite addOrd_unfold.
  rewrite ord_le_unfold; intros.
  rewrite ord_lt_unfold.
  exists (inr a).
  apply Hx.
Qed.


Lemma addOrd_zero x : ord_eq x (addOrd x zeroOrd).
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

Lemma addOrd_comm_le x y : ord_le (addOrd x y) (addOrd y x).
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

Lemma addOrd_comm x y : ord_eq (addOrd x y) (addOrd y x).
Proof.
  split; apply addOrd_comm_le; auto.
Qed.

Lemma addOrd_assoc1 : forall x y z,  ord_le (addOrd x (addOrd y z)) (addOrd (addOrd x y) z).
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

Lemma addOrd_assoc2 : forall x y z, ord_le (addOrd (addOrd x y) z) (addOrd x (addOrd y z)).
Proof.
  induction x. induction y. induction z.
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

Lemma addOrd_assoc : forall x y z,  ord_eq (addOrd x (addOrd y z)) (addOrd (addOrd x y) z).
Proof.
  intros; split.
  apply addOrd_assoc1.
  apply addOrd_assoc2.
Qed.

Lemma addOrd_cancel :
  forall x y z, ord_lt (addOrd x z) (addOrd y z) -> ord_lt x y.
Proof.
  induction x as [A f]. induction y as [B g]. induction z as [C h].
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
  forall x y z1 z2, ord_le x y -> ord_le z1 z2 -> ord_le (addOrd x z1) (addOrd y z2).
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
  forall x y z1 z2, (ord_lt x y -> ord_le z1 z2 -> ord_lt (addOrd x z1) (addOrd y z2)) /\
                    (ord_le x y -> ord_lt z1 z2 -> ord_lt (addOrd x z1) (addOrd y z2)).
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
  forall x y z, ord_lt x y -> ord_lt (addOrd x z) (addOrd y z).
Proof.
  intros.
  destruct (addOrd_monotone_lt x y z z).
  apply H0; auto.
  apply ord_le_refl.
Qed.

Lemma addOrd_monotone_lt2 :
  forall x y z, ord_lt x y -> ord_lt (addOrd z x) (addOrd z y).
Proof.
  intros.
  destruct (addOrd_monotone_lt z z x y).
  apply H1; auto.
  apply ord_le_refl.
Qed.

Lemma addOrd_least (f:Ord -> Ord -> Ord)
  (Hmono1 : forall a b c, ord_lt a b -> ord_lt (f a c) (f b c))
  (Hmono2 : forall a b c, ord_lt a b -> ord_lt (f c a) (f c b))
  :
  (forall x y, ord_le (addOrd x y) (f x y)).
Proof.
  induction x as [A fa].
  induction y as [B g].
  rewrite ord_le_unfold.
  rewrite addOrd_unfold.
  simpl.
  intros [a|b].
  - eapply ord_le_lt_trans.
    apply H.
    apply Hmono1.
    apply limit_lt.
  - eapply ord_le_lt_trans.
    apply H0.
    apply Hmono2.
    apply limit_lt.
Qed.

Lemma addOrd_succ x y : ord_eq (addOrd (succOrd x) y) (succOrd (addOrd x y)).
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
    + eapply ord_le_trans.
      apply Hy.
      apply succ_least.
      apply addOrd_monotone_lt2.
      apply limit_lt.
  - apply succ_least.
    apply addOrd_monotone_lt1.
    apply succ_lt.
Qed.


(** * An ordinal multiplication *)

Fixpoint mulOrd (x:Ord) (y:Ord) : Ord :=
    match y with
    | ord B g => supOrd (fun b:B => addOrd (mulOrd x (g b)) x)
    end.

Lemma mulOrd_unfold (x:Ord) (y:Ord) :
  mulOrd x y =
  supOrd (fun i:y => addOrd (mulOrd x (y i)) x).
Proof.
  destruct y; auto.
Qed.


Lemma mulOrd_monotone_le1 : forall z x y, ord_le x y -> ord_le (mulOrd x z) (mulOrd y z).
Proof.
  induction z as [C h Hz].
  simpl; intros.
  apply sup_least. intro c. simpl.
  eapply ord_le_trans; [ | apply (sup_le _ _ c) ].
  apply addOrd_monotone_le; auto.
Qed.


Lemma mulOrd_monotone_le2 : forall y x z, ord_le y z -> ord_le (mulOrd x y) (mulOrd x z).
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
  eapply ord_le_trans; [ | apply (sup_le _ _ q) ]. simpl.
  apply addOrd_monotone_le; auto.
  apply ord_le_refl.
Qed.

Lemma mulOrd_monotone_lt2 : forall x y z, ord_lt zeroOrd x ->
                                   ord_lt y z ->
                                   ord_lt (mulOrd x y) (mulOrd x z).
Proof.
  intros x y [C h] Hx H.
  rewrite (mulOrd_unfold x (ord C h)).
  simpl.
  rewrite ord_lt_unfold in H.
  destruct H as [c Hc]. simpl in Hc.
  eapply ord_lt_le_trans; [ | apply (sup_le _ _ c) ]. simpl.
  apply ord_le_lt_trans with (mulOrd x (h c)); [ apply mulOrd_monotone_le2; assumption | ].
  apply ord_le_lt_trans with (addOrd (mulOrd x (h c)) zeroOrd).
  - apply addOrd_zero.
  - apply addOrd_monotone_lt2. auto.
Qed.


Lemma mulOrd_zero : forall x, ord_le (mulOrd x zeroOrd) zeroOrd.
Proof.
  destruct x as [A f]. simpl.
  rewrite ord_le_unfold. simpl. intros [[] _].
Qed.

Lemma mulOrd_succ : forall x y, ord_eq (mulOrd x (succOrd y)) (addOrd (mulOrd x y) x).
Proof.
  intros.
  split.
  - simpl.
    apply sup_least. intro.
    apply ord_le_refl.
  - simpl.
    rewrite ord_le_unfold.
    simpl; intros.
    rewrite ord_lt_unfold.
    simpl.
    exists (existT _ tt a). simpl.
    apply ord_le_refl.
Qed.

Lemma mulOrd_one : forall x, ord_eq (mulOrd x oneOrd) x.
Proof.
  split.
  - eapply ord_le_trans; [ apply mulOrd_succ |].
    apply ord_le_trans with (addOrd zeroOrd x).
    apply addOrd_monotone_le; [ apply mulOrd_zero | apply ord_le_refl ].
    eapply ord_le_trans; [ apply addOrd_comm | apply addOrd_zero ].
  - eapply ord_le_trans; [| apply mulOrd_succ ].
    apply ord_le_trans with (addOrd zeroOrd x).
    eapply ord_le_trans; [ apply addOrd_zero | apply addOrd_comm ].
    eapply addOrd_monotone_le; [ apply zero_least | apply ord_le_refl ].
Qed.

Lemma mulOrd_positive : forall x y, ord_lt zeroOrd x -> ord_lt zeroOrd y -> ord_lt zeroOrd (mulOrd x y).
Proof.
  intros.
  rewrite ord_lt_unfold.
  destruct x as [A f].
  destruct y as [B g].
  simpl.
  rewrite ord_lt_unfold in H.
  rewrite ord_lt_unfold in H0.
  destruct H as [a _].
  destruct H0 as [b _].
  simpl in *.
  assert (exists q : addOrd (mulOrd (ord A f) (g b)) (ord A f) , True).
  { rewrite addOrd_unfold. simpl.
    destruct (mulOrd (ord A f) (g b)). simpl.
    exists (inr a). auto. }
  destruct H as [q _].
  exists (existT _ b q).
  apply zero_least.
Qed.

Lemma mulOrd_limit : forall x y,
    limitOrdinal y ->
    ord_eq (mulOrd x y) (supOrd (fun b:y => mulOrd x (y b))).
Proof.
  destruct y as [B g]; simpl; intros.
  split.
  - apply sup_least. intro b.
    destruct H as [_ H].
    destruct (H b) as [b' Hb'].
    eapply ord_le_trans.
    2: apply (sup_le _ _ b'). simpl.
    apply ord_le_trans with (mulOrd x (succOrd (g b))).
    destruct (mulOrd_succ x (g b)); auto.
    apply mulOrd_monotone_le2.
    apply succ_least.
    auto.
  - apply sup_least. intro b.
    eapply ord_le_trans; [ | apply (sup_le _ _ b) ]; simpl.
    apply addOrd_le1.
Qed.

Lemma mulOrd_continuous x : strongly_continuous (mulOrd x).
Proof.
  red; simpl; intros.
  apply sup_least.
  intros [a q]. simpl.
  eapply ord_le_trans; [| apply (sup_le _ _ a) ]. simpl.
  rewrite (mulOrd_unfold x (f a)).
  eapply ord_le_trans; [| apply (sup_le _ _ q) ]. simpl.
  apply ord_le_refl.
Qed.

(** * An ordinal exponentiation *)

Definition expOrd (x y:Ord) : Ord :=
  foldOrd oneOrd (fun a => mulOrd a x) y.

Lemma expOrd_unfold x y :
  expOrd x y =
  lubOrd oneOrd (supOrd (fun b:y => mulOrd (expOrd x (y b)) x)).
Proof.
  destruct y; simpl; auto.
Qed.

Lemma expOrd_nonzero x y : ord_lt zeroOrd (expOrd x y).
Proof.
  destruct y as [B g]. simpl.
  rewrite ord_lt_unfold. simpl.
  exists (inl tt).
  apply zero_least.
Qed.

Lemma expOrd_zero x : ord_eq (expOrd x zeroOrd) oneOrd.
Proof.
  apply foldOrd_zero.
Qed.

Lemma expOrd_succ x y : ord_lt zeroOrd x -> ord_eq (expOrd x (succOrd y)) (mulOrd (expOrd x y) x).
Proof.
  intros.
  apply foldOrd_succ.
  intros.
  apply succ_least.
  apply mulOrd_positive.
  rewrite ord_le_unfold in H0. apply (H0 tt). auto.
Qed.

Lemma expOrd_monotone_le a : forall x y, ord_le x y -> ord_le (expOrd a x) (expOrd a y).
Proof.
  intros. apply foldOrd_monotone_le; auto.
  intros; apply mulOrd_monotone_le1; auto.
Qed.

Lemma expOrd_monotone_lt a (Ha : ord_lt oneOrd a) : forall y x, ord_lt x y -> ord_lt (expOrd a x) (expOrd a y).
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

Lemma expOrd_limit x y (Hx:ord_lt oneOrd x) : limitOrdinal y -> ord_eq (expOrd x y) (supOrd (fun b:y => expOrd x (y b))).
Proof.
  intros.
  apply foldOrd_limit; auto.
  apply mulOrd_monotone_le1.
Qed.

Lemma expOrd_continuous x (Hx:ord_lt oneOrd x) A (f:A -> Ord) (a0:A) : ord_le (expOrd x (supOrd f)) (supOrd (fun a => expOrd x (f a))).
Proof.
  apply foldOrd_strongly_continuous; auto.
Qed.

Record normal_function (f:Ord -> Ord) :=
  NormalFunction
  { normal_monotone_le : forall x y, ord_le x y -> ord_le (f x) (f y)
  ; normal_monotone_lt : forall x y, ord_lt x y -> ord_lt (f x) (f y)
  ; normal_continuous  : strongly_continuous f
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

  Lemma normal_prefixpoint : forall base, ord_le (f (normal_fix base)) (normal_fix base).
  Proof.
    intros.
    apply ord_le_trans with (supOrd (fun i => f (iter_f base i))).
    - apply (normal_continuous _ Hnormal nat (iter_f base) 0).
    - apply sup_least. intro i.
      unfold normal_fix.
      apply (sup_le _ (iter_f base) (S i)).
  Qed.

  Lemma normal_fixpoint : forall base, ord_eq (normal_fix base) (f (normal_fix base)).
  Proof.
    intros; split.
    - unfold normal_fix.
      apply mono_lt_increasing.
      apply normal_monotone_lt; auto.
    - apply normal_prefixpoint.
  Qed.

  Lemma normal_fix_above : forall base, ord_le base (normal_fix base).
  Proof.
    intros.
    unfold normal_fix.
    apply (sup_le _ (iter_f base) 0).
  Qed.

  Lemma normal_fix_least : forall base z, ord_le base z -> ord_le (f z) z -> ord_le (normal_fix base) z.
  Proof.
    intros.
    unfold normal_fix.
    apply sup_least.
    intro i; induction i; simpl; auto.
    apply ord_le_trans with (f z); auto.
    apply normal_monotone_le; auto.
  Qed.

  Lemma normal_fix_monotone_le : forall b1 b2, ord_le b1 b2 -> ord_le (normal_fix b1) (normal_fix b2).
  Proof.
    unfold normal_fix; intros.
    apply sup_least. intro n.
    eapply ord_le_trans with (iter_f b2 n); [ | apply sup_le ].
    induction n; simpl; auto.
    apply normal_monotone_le; auto.
  Qed.

  Lemma normal_fix_continuous : strongly_continuous normal_fix .
  Proof.
    red; simpl; intros A g a0.
    unfold normal_fix at 1.
    apply sup_least. intro i.
    apply ord_le_trans with (supOrd (fun a => iter_f (g a) i)).
    - induction i.
      + simpl.
        apply sup_least. intros a.
        apply sup_le.
      + simpl.
        eapply ord_le_trans.
        * apply normal_monotone_le; [ apply Hnormal | apply IHi ].
        * apply normal_continuous; auto.
    - apply sup_least. intro a.
      eapply ord_le_trans; [ | apply (sup_le _ _ a) ]. simpl.
      unfold normal_fix.
      eapply ord_le_trans; [ | apply (sup_le _ _ i) ]. simpl.
      apply ord_le_refl.
  Qed.

End normal_fixpoints.

(* Natural numbers have an ordinal size.
 *)
Fixpoint natOrdSize (x:nat) :=
  match x with
  | O => zeroOrd
  | S n => succOrd (natOrdSize n)
  end.

Canonical Structure Omega : Ord :=
  ord nat natOrdSize.

Definition powOmega (x:Ord) : Ord := expOrd Omega x.

Lemma omega_gt1 : ord_lt oneOrd Omega.
Proof.
  rewrite ord_lt_unfold.
  exists 1. simpl.
  apply ord_le_refl.
Qed.

Lemma powOmega_normal : normal_function powOmega.
Proof.
  apply NormalFunction.
  + apply expOrd_monotone_le.
  + intros; apply (expOrd_monotone_lt Omega omega_gt1 y x); auto.
  + red; intros A f a0; apply (expOrd_continuous Omega omega_gt1 A f a0).
Qed.

Lemma normal_lub f x y  (Hf:normal_function f) :
  ord_le (f (lubOrd x y)) (lubOrd (f x) (f y)).
Proof.
  apply ord_le_trans with (f (supOrd (fun b:bool => if b then x else y))).
  - apply normal_monotone_le; auto.
    apply lub_least.
    + apply (sup_le bool (fun b => if b then x else y) true).
    + apply (sup_le bool (fun b => if b then x else y) false).
  - eapply ord_le_trans; [ apply normal_continuous; auto; exact false |].
    apply sup_least.
    intros [|]; [ apply lub_le1 | apply lub_le2 ].
Qed.

Definition epsilon0 := normal_fix powOmega zeroOrd.

Lemma epsilon_fixpoint : ord_le (expOrd Omega epsilon0) epsilon0.
Proof.
  intros. unfold epsilon0.
  apply (normal_fixpoint _ powOmega_normal).
Qed.

(** * Lexicographic orders, encoded as ordinals *)

Definition lex (alpha:Ord) (x y:Ord) :=
  addOrd (mulOrd alpha x) y.

Lemma lex1 alpha x x' y y' :
  ord_lt x x' ->
  ord_lt y alpha ->
  ord_lt (lex alpha x y) (lex alpha x' y').
Proof.
  unfold lex; intros.
  apply ord_lt_le_trans with (addOrd (mulOrd alpha (succOrd x)) y').
  - apply ord_lt_le_trans with (mulOrd alpha (succOrd x)); [ | apply addOrd_le1 ].
    eapply ord_lt_le_trans; [ | apply mulOrd_succ ].
    apply addOrd_monotone_lt2; auto.
  - apply addOrd_monotone_le. apply mulOrd_monotone_le2.
    apply succ_least. auto.
    apply ord_le_refl.
Qed.

Lemma lex2 alpha x x' y y' :
  ord_le x x' ->
  ord_lt y y' ->
  ord_lt (lex alpha x y) (lex alpha x' y').
Proof.
  unfold lex; intros.
  eapply ord_le_lt_trans with (addOrd (mulOrd alpha x') y).
  apply addOrd_monotone_le.
  apply mulOrd_monotone_le2; auto.
  apply ord_le_refl.
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

  Lemma wf_ord_lt : forall a a', R a' a -> ord_lt (wf_ord a') (wf_ord a).
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

  Lemma wf_ord_lt_trans : forall a a', clos_trans _ R a' a -> ord_lt (wf_ord a') (wf_ord a).
  Proof.
    intros; induction H.
    - apply wf_ord_lt; auto.
    - eapply ord_lt_trans; eauto.
  Qed.

  Lemma wf_ord_le_trans : forall a a', clos_refl_trans _ R a' a -> ord_le (wf_ord a') (wf_ord a).
  Proof.
    intros; induction H.
    - apply ord_lt_le; apply wf_ord_lt; auto.
    - apply ord_le_refl.
    - eapply ord_le_trans; eauto.
  Qed.

End wf_ord.


Definition ord_measure (o:Ord) := Acc ord_lt o.



Definition Ack_measure (m:nat) (n:nat) := ord_measure (lex Omega (natOrdSize m) (natOrdSize n)).

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
  apply (limit_lt _ natOrdSize 1).
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
  apply (limit_lt _ natOrdSize 0).

  destruct HM as [HM]; apply HM; simpl.
  apply lex1.
  apply succ_lt.
  apply (limit_lt _ natOrdSize (S n0)).
Defined.

Definition Ack m n := @Ackdef m n (ord_lt_wf _).




(*  The notation "x ◃ y" indicates that "x" has a strictly smaller ordinal measure
    than "y".  Note that "x" and "y" do not need to have the same type.
 *)
Notation "x ◃ y" := (ord_lt (ordSize _ x) (ordSize _ y)) (at level 80, no associativity).
Notation "x ⊴ y" := (ord_le (ordSize _ x) (ordSize _ y)) (at level 80, no associativity).


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

Lemma succ_trans x y : ord_le x y -> ord_lt x (succOrd y).
Proof.
  intros.
  rewrite ord_lt_unfold.
  simpl. exists tt. auto.
Qed.

Lemma succ_trans' x y : ord_le x y -> ord_le x (succOrd y).
Proof.
  intros.
  apply ord_lt_le.
  apply succ_trans; auto.
Qed.

Lemma lub_trans1 x y z : ord_le x y -> ord_le x (lubOrd y z).
Proof.
  intros.
  apply ord_le_trans with y; auto.
  apply lub_le1.
Qed.

Lemma lub_trans2 x y z : ord_le x z -> ord_le x (lubOrd y z).
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply lub_le2.
Qed.

Lemma add_trans1 x y z : ord_le x y -> ord_le x (addOrd y z).
Proof.
  intros.
  apply ord_le_trans with y; auto.
  apply addOrd_le1.
Qed.

Lemma add_trans1' x y z : ord_lt x y -> ord_lt x (addOrd y z).
Proof.
  intros.
  apply ord_lt_le_trans with y; auto.
  apply addOrd_le1.
Qed.

Lemma add_trans2 x y z : ord_le x z -> ord_le x (addOrd y z).
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply addOrd_le2.
Qed.

Lemma add_trans2' x y z : ord_lt x z -> ord_lt x (addOrd y z).
Proof.
  intros.
  apply ord_lt_le_trans with z; auto.
  apply addOrd_le2.
Qed.

Hint Unfold ordSize : ord.
Hint Resolve
     limit_lt lub_le1 lub_le2
     ord_lt_trans ord_le_trans
     succ_trans
     succ_trans'
     lub_trans1 lub_trans2
     add_trans1 add_trans2
     add_trans1' add_trans2'
     ord_lt_le ord_le_refl : ord.


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
  ord_eq (ordSize _ (xs ++ ys)) (addOrd (ordSize _ xs) (ordSize _ ys)).
Proof.
  induction xs; simpl.
  - destruct (addOrd_zero (listOrd (ordSize A) ys)).
    split.
    eapply ord_le_trans. apply H.
    apply addOrd_comm.
    eapply ord_le_trans. apply addOrd_comm.
    apply H0.
  - split.
    + apply ord_le_trans with (succOrd (addOrd (ordSize A a)
                                (addOrd (ordSize (ListOrd A) xs) (ordSize (ListOrd A) ys)))).
      * apply succ_monotone_le.
        apply addOrd_monotone_le.
        auto with ord.
        destruct IHxs; auto.
      * eapply ord_le_trans.
        apply addOrd_succ.
        eapply ord_le_trans.
        apply addOrd_assoc1.
        apply addOrd_monotone_le; auto with ord.
        apply addOrd_succ.
    + apply ord_le_trans with (succOrd (addOrd (ordSize A a)
                                (addOrd (ordSize (ListOrd A) xs) (ordSize (ListOrd A) ys)))).
      * eapply ord_le_trans.
        apply addOrd_succ.
        apply succ_monotone_le.
        apply addOrd_assoc2.
      * apply succ_monotone_le.
        apply addOrd_monotone_le.
        auto with ord.
        destruct IHxs; auto.
Qed.


(** Basic lemmas about constructors for nat and list *)
Lemma S_lt : forall x:nat, x ◃ S x.
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
  intros. simpl.
  apply ord_le_lt_trans with (addOrd (listOrd (ordSize A) xs) zeroOrd).
  apply addOrd_zero.
  apply ord_lt_le_trans with (addOrd (listOrd (ordSize A) xs) (listOrd (ordSize A) ys)).
  - apply addOrd_monotone_lt2.
    destruct ys.
    + elim H; auto.
    + simpl.
      eapply ord_le_lt_trans.
      apply zero_least.
      apply succ_lt.
  - apply (listAdd A xs ys).
Qed.

Lemma app_lt2 : forall (A:Ord) (xs ys:list A), xs <> [] -> ys ◃ xs ++ ys.
Proof.
  intros. simpl.
  apply ord_le_lt_trans with (addOrd zeroOrd (listOrd (ordSize A) ys)).
  eapply ord_le_trans.
  apply addOrd_zero.
  apply addOrd_comm.

  apply ord_lt_le_trans with (addOrd (listOrd (ordSize A) xs) (listOrd (ordSize A) ys)).
  - apply addOrd_monotone_lt1.
    destruct xs.
    + elim H; auto.
    + simpl.
      eapply ord_le_lt_trans.
      apply zero_least.
      apply succ_lt.
  - apply (listAdd A xs ys).
Qed.


Lemma In_lt : forall (A:Ord) (x:A) l, In x l -> x ◃ l.
Proof.
  induction l; simpl; intuition; subst; eauto with ord.
Qed.
Hint Resolve In_lt.


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

Hint Resolve fun_lt dep_lt.

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
