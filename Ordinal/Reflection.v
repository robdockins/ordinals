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
| Arrow : Shape -> Shape -> Shape
.

Fixpoint ordShape (S:Shape) : Type :=
  match S with
  | PROP        => Prop
  | ORD         => Ord
  | Arrow S1 S2 => ordShape S1 -> ordShape S2
  end.

Fixpoint reflShape (S:Shape) (X:Type) : Type :=
  match S with
  | PROP        => Prop
  | ORD         => X
  | Arrow S1 S2 => reflShape S1 X -> reflShape S2 X
  end.

Fixpoint reflects (A:Type) (f:A -> Ord) (S:Shape) : ordShape S -> reflShape S A -> Prop :=
  match S as S' return ordShape S' -> reflShape S' A -> Prop with
  | PROP => fun p q => p <-> q
  | ORD  => fun x a => x ≈ f a
  | Arrow S1 S2 => fun g h => forall x a, reflects A f S1 x a -> reflects A f S2 (g x) (h a)
  end.


