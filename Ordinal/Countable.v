Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.


Inductive countableOrd : Set :=
| czero  : countableOrd
| climit : (nat -> countableOrd) -> countableOrd.

Fixpoint countableToOrd (x:countableOrd) : Ord :=
  match x with
  | czero => zeroOrd
  | climit f => ord nat (fun i => countableToOrd (f i))
  end.

Canonical Structure Ω := ord countableOrd countableToOrd.

Definition Ωc := ord { o:countableOrd | complete (sz o) } (fun o => countableToOrd (proj1_sig o)).

Lemma countable_zero_dec (x:Ω) : x <= zeroOrd \/ zeroOrd < x.
Proof.
  destruct x; simpl; auto with ord.
  right.
  rewrite ord_lt_unfold. simpl. exists 0%nat.
  apply zero_least.
Qed.

Parameter nat_sum : nat -> nat + nat.
Parameter nat_unsum : nat + nat -> nat.

Hypothesis nat_sum_inv : forall n, nat_unsum (nat_sum n) = n.
Hypothesis nat_unsum_inv : forall xy, nat_sum (nat_unsum xy) = xy.

Parameter nat_prod : nat -> nat * nat.
Parameter nat_unprod : nat * nat -> nat.

Hypothesis nat_prodinv : forall n, nat_unprod (nat_prod n) = n.
Hypothesis nat_unprod_inv : forall xy, nat_prod (nat_unprod xy) = xy.

Definition club (x y : Ω) :=
  match x, y with
  | czero, _ => y
  | _, czero => x
  | climit fx, climit fy =>
    climit (fun i => match nat_sum i with
                     | inl a => fx a
                     | inr b => fy b
                     end)
  end.

Lemma club_eq : forall x y:Ω, club x y ≈ x ⊔ y.
Proof.
  split.
  - destruct x; destruct y; simpl.
    + apply zero_least.
    + rewrite ord_le_unfold; simpl; intro i.
      rewrite ord_lt_unfold; simpl. exists (inr i).
      reflexivity.
    + rewrite ord_le_unfold; simpl; intro i.
      rewrite ord_lt_unfold; simpl. exists (inl i).
      reflexivity.
    + rewrite ord_le_unfold; simpl; intro i.
      rewrite ord_lt_unfold; simpl.
      exists (nat_sum i).
      destruct (nat_sum i); simpl; reflexivity.
  - destruct x; destruct y; simpl.
    + rewrite ord_le_unfold; simpl; intro.
      destruct a; exfalso; auto.
    + rewrite ord_le_unfold; simpl; intro.
      destruct a. exfalso; auto.
      rewrite ord_lt_unfold; exists n; reflexivity.
    + rewrite ord_le_unfold; simpl; intro.
      destruct a. 
      rewrite ord_lt_unfold; exists n; reflexivity.
      exfalso; auto.
    + rewrite ord_le_unfold; simpl; intro.
      rewrite ord_lt_unfold; simpl.
      exists (nat_unsum a).
      rewrite nat_unsum_inv.
      destruct a; simpl; reflexivity.
Qed.


Fixpoint club' (x y:countableOrd) : countableOrd :=
  match x, y with
  | czero, _ => y
  | _, czero => x
  | climit fx, climit fy =>
    climit (fun i => let (j,k) := nat_prod i in
                      club' (fx j) (fy k))
  end.


Lemma club'_le1 : forall (x y:countableOrd), countableToOrd x <= countableToOrd (club' x y).
Proof.
  simpl in *.
  induction x as [|f Hx].
  - intros. simpl. apply zero_least.
  - intros [|g].
    + simpl. reflexivity.
    + simpl. rewrite ord_le_unfold.
      intro i. simpl.
      rewrite ord_lt_unfold; simpl.
      exists (nat_unprod (i, 0%nat)).
      rewrite nat_unprod_inv.
      apply Hx.
Qed.

Lemma club'_le2 : forall (x y:countableOrd), countableToOrd y <= countableToOrd (club' x y).
Proof.
  simpl in *.
  intros x y; revert x.
  induction y as [|g Hy].
  - intros. simpl. apply zero_least.
  - intros [|f].
    + simpl. reflexivity.
    + simpl. rewrite ord_le_unfold.
      intro i. simpl.
      rewrite ord_lt_unfold; simpl.
      exists (nat_unprod (0%nat, i)).
      rewrite nat_unprod_inv.
      apply Hy.
Qed.

Lemma club'_least : forall (x y z:countableOrd),
  complete (sz z) ->
  sz x <= sz z ->
  sz y <= sz z ->
  sz (club' x y) <= sz z.
Proof.
  induction x as [|f Hx].
  { simpl; intros; auto. }
  intros [|g].
  { simpl; intros; auto. }
  simpl; intros.
  destruct z as [|h].
  { simpl in H0. destruct (ord_le_subord _ _ H0 0%nat) as [[] _]. }

  rewrite ord_le_unfold; simpl; intro i.
  set (j := fst (nat_prod i)).
  set (k := snd (nat_prod i)).
  destruct (ord_le_subord _ _ H0 j) as [j' Hj]. simpl in Hj.
  destruct (ord_le_subord _ _ H1 k) as [k' Hk]. simpl in Hk.
  destruct (complete_directed _ H j' k') as [l [Hj' Hk']].
  rewrite ord_lt_unfold. simpl. exists l.
  destruct (nat_prod i).
  apply Hx; auto.
  apply H.
  apply ord_le_trans with (sz (h j')); auto.
  apply ord_le_trans with (sz (h k')); auto.
Qed.

Lemma club'_complete : forall (x y:countableOrd),
  complete (sz x) -> complete (sz y) -> complete (sz (club' x y)).
Proof.
  induction x as [|f Hx].
  { simpl; intros; auto. }
  destruct y as [|g].
  { simpl; intros; auto. }
  intros. simpl.
  repeat split.
  - intros a b. 
    set (xa := fst (nat_prod a)).
    set (ya := snd (nat_prod a)).
    set (xb := fst (nat_prod b)).
    set (yb := snd (nat_prod b)).
    destruct (complete_directed _ H xa xb) as [x' [??]].
    destruct (complete_directed _ H0 ya yb) as [y' [??]].
    exists (nat_unprod (x', y')).
    rewrite nat_unprod_inv.
    destruct (nat_prod a).
    destruct (nat_prod b).
    split.
    + apply club'_least. apply Hx.
      apply H. apply H0.
      unfold xa, ya, xb, yb in *. simpl in *.
      rewrite H1. apply club'_le1.
      unfold xa, ya, xb, yb in *. simpl in *.
      rewrite H3. apply club'_le2.
    + apply club'_least. apply Hx.
      apply H. apply H0.
      unfold xa, ya, xb, yb in *. simpl in *.
      rewrite H2. apply club'_le1.
      unfold xa, ya, xb, yb in *. simpl in *.
      rewrite H4. apply club'_le2.
  - left. exact (inhabits 0%nat).
  - intro i.
    destruct (nat_prod i).
    apply Hx. apply H. apply H0.
Qed.

Lemma Ωc_complete : complete Ωc.
Proof.
  simpl. repeat split.
  - intros [o1 Ho1] [o2 Ho2]. simpl.
    exists (exist _ (club' o1 o2) (club'_complete o1 o2 Ho1 Ho2)).
    simpl. split; [ apply club'_le1 | apply club'_le2 ].
  - left. exact (inhabits (exist _ czero zero_complete)).
  - intros [o H]. simpl. auto.
Qed.
