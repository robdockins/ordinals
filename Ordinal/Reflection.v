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

Fixpoint reflects (A:Type) (f:A -> Ord) (S:Shape) : ordShape S -> reflShape S A -> Prop :=
  match S as S' return ordShape S' -> reflShape S' A -> Prop with
  | PROP => fun p q => p <-> q
  | ORD  => fun x a => x ≈ f a
  | PROD S1 S2 => fun x a => reflects A f S1 (fst x) (fst a) /\ reflects A f S2 (snd x) (snd a)
  | ARROW S1 S2 => fun g h => forall x a, reflects A f S1 x a -> reflects A f S2 (g x) (h a)
  end.


Remark ε0_least_exp_closed :
  forall X denote zeroX succX expOmegaX,
    reflects X denote ORD 0 zeroX ->
    reflects X denote (ORD ==> ORD) succOrd succX ->
    reflects X denote (ORD ==> ORD) (expOrd ω) expOmegaX ->

    ε 0 ≤ ord X denote.
Proof.
  intros X denote zeroX succX expOmegaX Hzero Hsucc HexpOmega.

  assert (Hlimit : limitOrdinal (ord X denote)).
  { simpl; split.
    - exact (inhabits zeroX).
    - hnf; simpl; intros.
      exists (succX a).
      apply ord_lt_le_trans with (succOrd (denote a)).
      apply succ_lt.
      apply Hsucc.
      simpl; reflexivity. }

  apply ε0_least_expOmega_closed; auto.
  transitivity (expOrd ω (supOrd denote)).
  - apply expOrd_monotone.
    apply ord_isLimit; auto.
  - etransitivity; [ apply expOrd_continuous |].
    exact zeroX.
    apply sup_least; intro x.
    transitivity (denote (expOmegaX x)).
    apply HexpOmega. simpl; reflexivity.
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

