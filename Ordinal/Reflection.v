Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import List.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.

Open Scope ord_scope.

Inductive Shape : Set :=
| PROP : Shape
| ORD : Shape
| PROD : Shape -> Shape -> Shape
| ARROW : Shape -> Shape -> Shape
.

Notation "S ==> T" := (ARROW S T) : ord_scope.

Fixpoint ordShape (S:Shape) : Type :=
  match S with
  | PROP        => Prop
  | ORD         => Ord
  | PROD S1 S2  => ordShape S1 * ordShape S2
  | ARROW S1 S2 => ordShape S1 -> ordShape S2
  end.

Fixpoint reflShape (S:Shape) (X:Type) : Type :=
  match S with
  | PROP        => Prop
  | ORD         => X
  | PROD S1 S2  => reflShape S1 X * reflShape S2 X
  | ARROW S1 S2 => reflShape S1 X -> reflShape S2 X
  end.

Fixpoint reflects (A:Type) (f:A -> Ord) (P:A -> Prop) (S:Shape) : ordShape S -> reflShape S A -> Prop :=
  match S as S' return ordShape S' -> reflShape S' A -> Prop with
  | PROP => fun p q => p <-> q
  | ORD  => fun x a => x ≈ f a /\ P a
  | PROD S1 S2 => fun x a => reflects A f P S1 (fst x) (fst a) /\ reflects A f P S2 (snd x) (snd a)
  | ARROW S1 S2 => fun g h => forall x a, reflects A f P S1 x a -> reflects A f P S2 (g x) (h a)
  end.


Remark ε0_least_exp_closed :
  forall X denote P zeroX succX expOmegaX,
    (forall x:X, exists x', denote x ≈ denote x' /\ P x') ->
    reflects X denote P ORD 0 zeroX ->
    reflects X denote P (ORD ==> ORD) succOrd succX ->
    reflects X denote P (ORD ==> ORD) (expOrd ω) expOmegaX ->

    ε 0 ≤ ord X denote.
Proof.
  intros X denote P zeroX succX expOmegaX Hnorm Hzero Hsucc HexpOmega.

  assert (Hlimit : limitOrdinal (ord X denote)).
  { simpl; split.
    - exact (inhabits zeroX).
    - hnf; simpl; intros.
      destruct (Hnorm a) as [a' [Ha1 Ha2]].
      exists (succX a').
      apply ord_lt_le_trans with (succOrd (denote a)).
      apply succ_lt.
      apply Hsucc.
      simpl; split; auto. }

  apply ε0_least_expOmega_closed; auto.
  transitivity (expOrd ω (supOrd denote)).
  - apply expOrd_monotone.
    apply limit_boundedSup; auto.
  - etransitivity; [ apply expOrd_continuous |].
    exact zeroX.
    apply sup_least; intro x.
    destruct (Hnorm x) as [x' [Hx1 Hx2]].
    transitivity (denote (expOmegaX x')).
    apply HexpOmega. simpl; split; auto.
    apply (index_le (ord X denote)).
Qed.



(** TODO, this ordering stuff doesn't really go here *)
Inductive ordering := LT | EQ | GT.

Definition ordering_swap (o:ordering) : ordering :=
  match o with
  | LT => GT
  | EQ => EQ
  | GT => LT
  end.

(* Compute the lexicographic ordering given two sub-orderings. *)
Definition lexCompare (o1:ordering) (o2:ordering) : ordering :=
  match o1 with
  | LT => LT
  | EQ => o2
  | GT => GT
  end.

Definition ordering_correct o a b :=
  match o with
  | LT => a < b
  | EQ => a ≈ b
  | GT => a > b
  end.

Fixpoint nat_compare (x y:nat) : ordering :=
  match x, y with
  | O, O       => EQ
  | S _, O     => GT
  | O , S _    => LT
  | S x', S y' => nat_compare x' y'
  end.

Lemma nat_compare_correct :
  forall x y,
    match nat_compare x y with
    | LT => (x < y)%nat
    | EQ => x = y
    | GT => (x > y)%nat
    end.
Proof.
  induction x; destruct y; simpl; auto with arith.
  generalize (IHx y).
  destruct (nat_compare x y); intuition.
Qed.

Add Parametric Morphism o : (ordering_correct o)
  with signature ord_eq ==> ord_eq ==> impl as ordering_correct_eq_mor.
Proof.
  repeat intro.
  destruct o; simpl in *.
  rewrite <- H. rewrite <- H0. auto.
  rewrite <- H. rewrite <- H0. auto.
  rewrite <- H. rewrite <- H0. auto.
Qed.  
