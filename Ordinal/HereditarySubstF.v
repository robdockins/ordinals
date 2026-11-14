From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import NaturalArith.

Open Scope ord_scope.

(** * An ordinal measure for hereditary substitution in Leivant's
      predicative System F

    In predicative System F, quantifiers carry a level (a kind [k]):
    [∀X:k. U] quantifies over types of kind [k], and has kind
    [max (k+1) k'] if [U] has kind [k'] (Leivant; the presentation of
    Mangin and Sozeau, "Equations for hereditary substitution in Leivant's
    predicative System F", 2015).  Unlike the simply-typed case,
    hereditary substitution terminates only on well-typed input: the
    type [V] instantiating [∀X:k. U] may be larger than [U].  Mangin and
    Sozeau order types lexicographically by the multiset of the kinds
    they quantify over, and then by depth.

    Here the multiset becomes an ordinal: [κ U] is the natural sum of
    [ω^k] over the quantifiers [∀X:k] in [U], and the type measure is
    [ω · κ U + depth U].  The two facts the termination proof needs are:

    - the components of an arrow type are smaller ([tord_arrow_l],
      [tord_arrow_r]);
    - instantiating a quantifier by a well-kinded type is smaller
      ([tord_inst]).

    The second is the heart of the matter.  Substitution adds one copy of
    [κ V] per occurrence of [X] ([kord_tsubst]); a type of kind [k] has
    [κ V < ω^k] ([kinded_bound]); and [ω^k] is closed under natural sums
    ([nadd_closed_con]).  So
    [κ (U[V/X]) ≈ κ U ⊕ n·κ V < κ U ⊕ ω^k ≈ κ (∀X:k. U)] ([kord_inst]).
    A type of kind [k] has measure below [ω · ω^k = ω^(k+1)]
    ([tord_bound]), so all measures are below [ω^ω]. *)

(** ** Types and kinding *)

Definition kind := nat.

Inductive typ : Set :=
| tvar : nat -> typ
| arrow : typ -> typ -> typ
| all : kind -> typ -> typ.

Fixpoint tshift (c:nat) (T:typ) : typ :=
  match T with
  | tvar Y => tvar (if Y <? c then Y else S Y)
  | arrow A B => arrow (tshift c A) (tshift c B)
  | all k U => all k (tshift (S c) U)
  end.

(** [tsubst U X T] substitutes [T] for the variable [X] in [U]. *)
Fixpoint tsubst (U:typ) (X:nat) (T:typ) : typ :=
  match U with
  | tvar Y => if Y =? X then T else tvar (if Y <? X then Y else pred Y)
  | arrow A B => arrow (tsubst A X T) (tsubst B X T)
  | all k V => all k (tsubst V (S X) (tshift 0 T))
  end.

(** The number of occurrences of [X] in [U]. *)
Fixpoint occ (X:nat) (U:typ) : nat :=
  match U with
  | tvar Y => if Y =? X then 1 else 0
  | arrow A B => occ X A + occ X B
  | all _ V => occ (S X) V
  end.

(** Kinding, with cumulativity at variables (Mangin and Sozeau's rules). *)
Inductive kinding : list kind -> typ -> kind -> Prop :=
| K_var (Γ:list kind) (X:nat) (k k':kind) :
    nth_error Γ X = Some k -> (k <= k')%nat -> kinding Γ (tvar X) k'
| K_arrow (Γ:list kind) A B (k k':kind) : kinding Γ A k -> kinding Γ B k' -> kinding Γ (arrow A B) (Nat.max k k')
| K_all (Γ:list kind) (k:kind) U (k':kind) : kinding (k :: Γ) U k' -> kinding Γ (all k U) (Nat.max (S k) k').

(** ** The ordinal of the kinds of a type *)

Fixpoint kord (T:typ) : Ord :=
  match T with
  | tvar _ => 0
  | arrow A B => kord A ⊕ kord B
  | all k U => expOrd ω (natOrdSize k) ⊕ kord U
  end.

Fixpoint depth (T:typ) : nat :=
  match T with
  | tvar _ => 1
  | arrow A B => depth A + depth B
  | all _ U => S (depth U)
  end.

Lemma depth_pos T : (0 < depth T)%nat.
Proof. induction T; simpl; lia. Qed.

(** [n] copies of [x], added naturally. *)
Fixpoint nrep (n:nat) (x:Ord) : Ord :=
  match n with
  | O => 0
  | S n => x ⊕ nrep n x
  end.

Lemma nrep_add m n x : nrep (m + n) x ≈ nrep m x ⊕ nrep n x.
Proof.
  induction m; simpl.
  - symmetry. apply naddOrd_zero_l.
  - rewrite IHm. apply naddOrd_assoc.
Qed.

Lemma nadd_swap a b c d : (a ⊕ b) ⊕ (c ⊕ d) ≈ (a ⊕ c) ⊕ (b ⊕ d).
Proof.
  rewrite <- naddOrd_assoc, (naddOrd_assoc b c d), (naddOrd_comm b c).
  rewrite <- (naddOrd_assoc c b d), naddOrd_assoc. reflexivity.
Qed.

Lemma kord_tshift : forall T c, kord (tshift c T) = kord T.
Proof.
  induction T as [Y | A IHA B IHB | k U IHU]; intro c; simpl; auto.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHU. reflexivity.
Qed.

(** Substitution adds one copy of the kinds of [T] per occurrence. *)
Theorem kord_tsubst : forall U X T, kord (tsubst U X T) ≈ kord U ⊕ nrep (occ X U) (kord T).
Proof.
  induction U as [Y | A IHA B IHB | k V IHV]; intros X T; simpl.
  - destruct (Y =? X); simpl.
    + rewrite naddOrd_zero_l, naddOrd_zero_r. reflexivity.
    + rewrite naddOrd_zero_l. reflexivity.
  - rewrite IHA, IHB, nrep_add. apply nadd_swap.
  - rewrite IHV, kord_tshift. apply naddOrd_assoc.
Qed.

(** A type of kind [k] quantifies only over kinds below [k]. *)
Theorem kinded_bound : forall Γ T k, kinding Γ T k -> kord T < expOrd ω (natOrdSize k).
Proof.
  intros Γ T k H. induction H; cbn [kord].
  - apply expOrd_nonzero.
  - apply nadd_closed_con; [apply natOrdSize_complete| |].
    + apply ord_lt_le_trans with (expOrd ω (natOrdSize k)); auto.
      apply expOrd_monotone. apply natOrdSize_monotone. lia.
    + apply ord_lt_le_trans with (expOrd ω (natOrdSize k')); auto.
      apply expOrd_monotone. apply natOrdSize_monotone. lia.
  - apply nadd_closed_con; [apply natOrdSize_complete| |].
    + apply ord_lt_le_trans with (expOrd ω (natOrdSize (S k))).
      * apply expOrd_increasing; [apply omega_gt1|].
        apply natOrdSize_increasing. lia.
      * apply expOrd_monotone. apply natOrdSize_monotone. apply Nat.le_max_l.
    + apply ord_lt_le_trans with (expOrd ω (natOrdSize k')); auto.
      apply expOrd_monotone. apply natOrdSize_monotone. lia.
Qed.

Lemma nrep_below n x k : x < expOrd ω (natOrdSize k) -> nrep n x < expOrd ω (natOrdSize k).
Proof.
  intro Hx. induction n; simpl.
  - apply expOrd_nonzero.
  - apply nadd_closed_con; auto. apply natOrdSize_complete.
Qed.

(** Instantiating a quantifier by a well-kinded type decreases the
    ordinal of the kinds: [ω^k] absorbs any number of copies of the
    instance. *)
Theorem kord_inst Γ T k U : kinding Γ T k -> kord (tsubst U 0 T) < kord (all k U).
Proof.
  intro HT. simpl. rewrite kord_tsubst, (naddOrd_comm (expOrd ω (natOrdSize k))).
  apply naddOrd_increasing2. apply nrep_below. eapply kinded_bound; eauto.
Qed.

(** ** The type measure [ω · κ + depth] *)

Definition tord (T:typ) : Ord := ω * kord T + natOrdSize (depth T).

(** Lexicographic comparison, as ordinal comparison. *)
Lemma lex_lt_major a a' d d' : a' < a -> ω * a' + natOrdSize d' < ω * a + natOrdSize d.
Proof.
  intro H. apply ord_lt_le_trans with (ω * a' + ω).
  - apply addOrd_increasing. apply (index_lt ω d').
  - rewrite <- mulOrd_succ. rewrite <- addOrd_le1.
    apply mulOrd_monotone2. apply succ_least. exact H.
Qed.

Lemma lex_lt_minor a a' d d' : a' ≤ a -> (d' < d)%nat -> ω * a' + natOrdSize d' < ω * a + natOrdSize d.
Proof.
  intros Ha Hd. apply ord_le_lt_trans with (ω * a + natOrdSize d').
  - apply addOrd_monotone; [apply mulOrd_monotone2; exact Ha | reflexivity].
  - apply addOrd_increasing. apply natOrdSize_increasing. exact Hd.
Qed.

Theorem tord_arrow_l A B : tord A < tord (arrow A B).
Proof.
  apply lex_lt_minor; [apply naddOrd_le1 | simpl; pose proof (depth_pos B); lia].
Qed.

Theorem tord_arrow_r A B : tord B < tord (arrow A B).
Proof.
  apply lex_lt_minor; [apply naddOrd_le2 | simpl; pose proof (depth_pos A); lia].
Qed.

(** The key decrease: a well-kinded instance of [∀X:k. U] is smaller,
    whatever its depth. *)
Theorem tord_inst Γ T k U : kinding Γ T k -> tord (tsubst U 0 T) < tord (all k U).
Proof. intro HT. apply lex_lt_major. eapply kord_inst; eauto. Qed.

(** Shifting does not change the measure (the shifted type is the one
    used under a type binder). *)
Lemma depth_tshift : forall T c, depth (tshift c T) = depth T.
Proof. induction T; intro c; simpl; auto. Qed.

Theorem tord_tshift T c : tord (tshift c T) ≈ tord T.
Proof. unfold tord. rewrite kord_tshift, depth_tshift. reflexivity. Qed.

(** A type of kind [k] has measure below [ω · ω^k], that is [ω^(k+1)];
    so all measures lie below [ω^ω]. *)
Theorem tord_bound Γ T k : kinding Γ T k -> tord T < ω * expOrd ω (natOrdSize k).
Proof.
  intro HT. unfold tord.
  apply ord_lt_le_trans with (ω * kord T + ω).
  - apply addOrd_increasing. apply (index_lt ω (depth T)).
  - rewrite <- mulOrd_succ. apply mulOrd_monotone2. apply succ_least.
    eapply kinded_bound; eauto.
Qed.

(** For example, [∀X:1. X → X] instantiated with [∀Y:0. Y] (of kind 1):
    the instance is deeper, but its kinds are smaller. *)
Example tord_inst_example :
  tord (tsubst (arrow (tvar 0) (tvar 0)) 0 (all 0%nat (tvar 0)))
    < tord (all 1%nat (arrow (tvar 0) (tvar 0))).
Proof.
  apply tord_inst with (Γ := nil).
  replace 1%nat with (Nat.max (S 0) 0) by reflexivity.
  constructor. econstructor; [reflexivity | lia].
Qed.
