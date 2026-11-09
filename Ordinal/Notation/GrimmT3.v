From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Btauto.
Import ListNotations.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import AckermannTower.
From Ordinal Require Import Notation.ATowerNotation.

(** * Grimm's syntactic presentation of Ackermann's system

    J. Grimm, "Implementation of three types of ordinals in Coq" (INRIA
    RR-8407, 2013; GAIA [theories/schutte/ssete9.v], [Module Ackermann])
    formalizes Ackermann's 1951 notation system syntactically, shifted to
    start from [0].  A term [T3cons a b c n d] stands for
    [ψ(a,b,c)·(n+1) + d]; the comparison is Ackermann's rule G6 (cases a-i)
    for brackets, and lexicographic on sums.  Grimm proves well-foundedness
    of normal forms syntactically.

    This file ports Grimm's syntax, comparison and normal forms (his file
    depends on MathComp), and defines a translation [T3_to_VF] into the
    semantic notation system of [ATowerNotation], whose order type is
    [LargeAckermannOrdinal] ([VF_LAO]).

    Ackermann's brackets skip fixed points, whereas [VForm] uses Veblen's
    functions and forbids fixed-point arguments in normal forms.  The
    translation therefore shifts indices in two places:
    - β-absorption: when [φ(a,b,0) = b], index [0] would denote [b] itself,
      which already has a name; the γ index then starts at [1];
    - γ-skipping: when the (shifted) γ is [λ + m] with [λ] a fixed point of
      [φ(a,b,·)] and [m] finite, it is incremented once more.

    Main results:
    - [T3lt_total]: Grimm's comparison is total (on all terms);
    - [T3_to_VF_normal]: normal forms translate to [VForm] normal forms;
    - [T3lt_correct]: on normal forms, Grimm's comparison agrees with the
      semantic order, in both directions, so it is in particular
      well-founded (independently of Grimm's syntactic proof);
    - [T3_denote_inj]: normal forms are determined by their denotation;
    - [T3_LAO]: the normal forms have order type [LargeAckermannOrdinal].

    The proof of [T3lt_correct] is by induction on the combined size of the
    terms ([GrimmT3_main]), carrying normality of the translation along.
    Six of Grimm's nine bracket cases reduce to the subterm properties
    [psi_gt_b] and [psi_gt_c]; the others are [psi_mono_c] (same level and
    β, which needs [normal_forms_unique] at one boundary), [psi_lt_same_a]
    and [psi_lt_cross]. *)

(** ** Syntax, comparison, normal forms (after Grimm) *)

Inductive T3 : Set :=
| T3zero : T3
| T3cons : T3 -> T3 -> T3 -> nat -> T3 -> T3.

Fixpoint T3eqb (x y:T3) : bool :=
  match x, y with
  | T3zero, T3zero => true
  | T3cons a b c n d, T3cons a' b' c' n' d' =>
      T3eqb a a' && T3eqb b b' && T3eqb c c' && Nat.eqb n n' && T3eqb d d'
  | _, _ => false
  end.

Fixpoint T3size (x:T3) : nat :=
  match x with
  | T3zero => 0
  | T3cons a b c _ d => S (T3size a + T3size b + T3size c + T3size d)
  end.

(** The bracket [ψ(a,b,c)], Grimm's [[a,b,c]]. *)
Definition T3psi (a b c:T3) : T3 := T3cons a b c 0 T3zero.

Definition lt_psi_rec (f:T3 -> T3 -> bool) (a b c a' b' c':T3) : bool :=
  let x := T3psi a b c in
  let x' := T3psi a' b' c' in
  (T3eqb a a' && T3eqb b b' && f c c') ||
  (T3eqb a a' && f b b' && f c x') ||
  (T3eqb a a' && f b' b && f x c') ||
  (T3eqb a a' && f b' b && T3eqb x c') ||
  (f a a' && f b x' && f c x') ||
  (f a' a && f x b') ||
  (f a' a && T3eqb x b') ||
  (f a' a && f x c') ||
  (f a' a && T3eqb x c').

Definition lt_rec (f:T3 -> T3 -> bool) (x y:T3) : bool :=
  match x, y with
  | T3cons a b c n d, T3cons a' b' c' n' d' =>
      if lt_psi_rec f a b c a' b' c' then true
      else if T3eqb a a' && T3eqb b b' && T3eqb c c' then
             if Nat.ltb n n' then true
             else if Nat.eqb n n' then f d d' else false
           else false
  | T3zero, T3cons _ _ _ _ _ => true
  | _, _ => false
  end.

Fixpoint T3lta (k:nat) : T3 -> T3 -> bool :=
  match k with
  | O => fun _ _ => false
  | S k => lt_rec (T3lta k)
  end.

Definition T3lt (x y:T3) : bool := T3lta (S (T3size x + T3size y)) x y.

Lemma lt_rec_ext f g x y :
  (forall u v, (T3size u + T3size v < T3size x + T3size y)%nat -> f u v = g u v) ->
  lt_rec f x y = lt_rec g x y.
Proof.
  intro H.
  destruct x as [|a b c n d]; destruct y as [|a' b' c' n' d']; simpl; auto.
  unfold lt_psi_rec, T3psi.
  rewrite (H c c'), (H b b'), (H c (T3cons a' b' c' 0 T3zero)), (H b' b),
    (H (T3cons a b c 0 T3zero) c'), (H a a'), (H b (T3cons a' b' c' 0 T3zero)),
    (H a' a), (H (T3cons a b c 0 T3zero) b'), (H d d') by (simpl; lia).
  reflexivity.
Qed.

Lemma T3lta_fuel : forall k k' x y,
  (T3size x + T3size y < k)%nat -> (k <= k')%nat -> T3lta k x y = T3lta k' x y.
Proof.
  induction k as [|k IH]; intros k' x y Hk Hk'; [lia|].
  destruct k' as [|k']; [lia|]. simpl.
  apply lt_rec_ext. intros u v Huv. apply IH; lia.
Qed.

(** Fuel independence: [T3lt] satisfies its defining recursion. *)
Lemma T3lt_unfold x y : T3lt x y = lt_rec T3lt x y.
Proof.
  unfold T3lt at 1. simpl. apply lt_rec_ext.
  intros u v Huv. unfold T3lt. symmetry. apply T3lta_fuel; lia.
Qed.

Lemma T3eqb_eq : forall x y, T3eqb x y = true <-> x = y.
Proof.
  induction x as [|a IHa b IHb c IHc n d IHd]; destruct y as [|a' b' c' n' d'];
    simpl; split; intro H; try discriminate; auto.
  - repeat (apply andb_prop in H as [H ?]).
    apply IHa in H. subst.
    match goal with
    | H1 : T3eqb b _ = true, H2 : T3eqb c _ = true,
      H3 : Nat.eqb n _ = true, H4 : T3eqb d _ = true |- _ =>
        apply IHb in H1; apply IHc in H2; apply Nat.eqb_eq in H3; apply IHd in H4
    end.
    subst. reflexivity.
  - injection H as <- <- <- <- <-.
    rewrite (proj2 (IHa a) eq_refl), (proj2 (IHb b) eq_refl), (proj2 (IHc c) eq_refl),
      Nat.eqb_refl, (proj2 (IHd d) eq_refl).
    reflexivity.
Qed.

Lemma T3eqb_refl x : T3eqb x x = true.
Proof. apply T3eqb_eq. reflexivity. Qed.

Lemma T3lt_cons a b c n d a' b' c' n' d' :
  T3lt (T3cons a b c n d) (T3cons a' b' c' n' d') =
  if lt_psi_rec T3lt a b c a' b' c' then true
  else if T3eqb a a' && T3eqb b b' && T3eqb c c' then
         if Nat.ltb n n' then true
         else if Nat.eqb n n' then T3lt d d' else false
       else false.
Proof. rewrite T3lt_unfold. reflexivity. Qed.

Lemma T3lt_zero_cons a b c n d : T3lt T3zero (T3cons a b c n d) = true.
Proof. rewrite T3lt_unfold. reflexivity. Qed.

(** *** The nine cases of rule G6, as introduction rules *)

Section lt_psi_intro.
  Variable f : T3 -> T3 -> bool.
  Variables a b c a' b' c' : T3.
  Let x := T3psi a b c.
  Let x' := T3psi a' b' c'.

  Lemma lt_psi_a : a = a' -> b = b' -> f c c' = true -> lt_psi_rec f a b c a' b' c' = true.
  Proof. intros <- <- H. unfold lt_psi_rec. rewrite !T3eqb_refl, H. btauto. Qed.

  Lemma lt_psi_b : a = a' -> f b b' = true -> f c x' = true -> lt_psi_rec f a b c a' b' c' = true.
  Proof. intros <- H1 H2. unfold lt_psi_rec. rewrite T3eqb_refl, H1. fold x'. rewrite H2. btauto. Qed.

  Lemma lt_psi_c : a = a' -> f b' b = true -> f x c' = true -> lt_psi_rec f a b c a' b' c' = true.
  Proof. intros <- H1 H2. unfold lt_psi_rec. rewrite T3eqb_refl, H1. fold x. rewrite H2. btauto. Qed.

  Lemma lt_psi_d : a = a' -> f b' b = true -> x = c' -> lt_psi_rec f a b c a' b' c' = true.
  Proof.
    intros <- H1 H2. unfold lt_psi_rec. rewrite T3eqb_refl, H1. fold x.
    rewrite (proj2 (T3eqb_eq x c') H2). btauto.
  Qed.

  Lemma lt_psi_e : f a a' = true -> f b x' = true -> f c x' = true -> lt_psi_rec f a b c a' b' c' = true.
  Proof. intros H1 H2 H3. unfold lt_psi_rec. fold x'. rewrite H1, H2, H3. btauto. Qed.

  Lemma lt_psi_f : f a' a = true -> f x b' = true -> lt_psi_rec f a b c a' b' c' = true.
  Proof. intros H1 H2. unfold lt_psi_rec. fold x. rewrite H1, H2. btauto. Qed.

  Lemma lt_psi_g : f a' a = true -> x = b' -> lt_psi_rec f a b c a' b' c' = true.
  Proof.
    intros H1 H2. unfold lt_psi_rec. fold x. rewrite H1, (proj2 (T3eqb_eq x b') H2). btauto.
  Qed.

  Lemma lt_psi_h : f a' a = true -> f x c' = true -> lt_psi_rec f a b c a' b' c' = true.
  Proof. intros H1 H2. unfold lt_psi_rec. fold x. rewrite H1, H2. btauto. Qed.

  Lemma lt_psi_i : f a' a = true -> x = c' -> lt_psi_rec f a b c a' b' c' = true.
  Proof.
    intros H1 H2. unfold lt_psi_rec. fold x. rewrite H1, (proj2 (T3eqb_eq x c') H2). btauto.
  Qed.
End lt_psi_intro.

(** *** Totality of Grimm's comparison (on all terms) *)

Definition T3trich (x y:T3) : Prop := T3lt x y = true \/ x = y \/ T3lt y x = true.

Lemma lt_psi_total a b c a' b' c' :
  T3trich a a' -> T3trich b b' -> T3trich c c' ->
  T3trich b (T3psi a' b' c') -> T3trich c (T3psi a' b' c') ->
  T3trich b' (T3psi a b c) -> T3trich c' (T3psi a b c) ->
  lt_psi_rec T3lt a b c a' b' c' = true \/ (a = a' /\ b = b' /\ c = c') \/
  lt_psi_rec T3lt a' b' c' a b c = true.
Proof.
  intros Ha Hb Hc Hby Hcy Hbx Hcx.
  destruct Ha as [Ha|[Ha|Ha]].
  - (* a < a' *)
    destruct Hby as [Hby|[Hby|Hby]].
    + destruct Hcy as [Hcy|[Hcy|Hcy]].
      * left. apply lt_psi_e; auto.
      * right; right. apply lt_psi_i; auto.
      * right; right. apply lt_psi_h; auto.
    + right; right. apply lt_psi_g; auto.
    + right; right. apply lt_psi_f; auto.
  - (* a = a' *)
    subst a'.
    destruct Hb as [Hb|[Hb|Hb]].
    + destruct Hcy as [Hcy|[Hcy|Hcy]].
      * left. apply lt_psi_b; auto.
      * right; right. apply lt_psi_d; auto.
      * right; right. apply lt_psi_c; auto.
    + subst b'.
      destruct Hc as [Hc|[Hc|Hc]].
      * left. apply lt_psi_a; auto.
      * right; left. auto.
      * right; right. apply lt_psi_a; auto.
    + destruct Hcx as [Hcx|[Hcx|Hcx]].
      * right; right. apply lt_psi_b; auto.
      * left. apply lt_psi_d; auto.
      * left. apply lt_psi_c; auto.
  - (* a' < a *)
    destruct Hbx as [Hbx|[Hbx|Hbx]].
    + destruct Hcx as [Hcx|[Hcx|Hcx]].
      * right; right. apply lt_psi_e; auto.
      * left. apply lt_psi_i; auto.
      * left. apply lt_psi_h; auto.
    + left. apply lt_psi_g; auto.
    + left. apply lt_psi_f; auto.
Qed.

Theorem T3lt_total : forall x y, T3trich x y.
Proof.
  intros x y. remember (T3size x + T3size y)%nat as k eqn:Hk.
  revert x y Hk.
  induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
  intros [|a b c n d] [|a' b' c' n' d'] Hk.
  - right; left; reflexivity.
  - left. apply T3lt_zero_cons.
  - right; right. apply T3lt_zero_cons.
  - assert (H : forall u v, (T3size u + T3size v < k)%nat -> T3trich u v).
    { intros u v Huv. apply (IH _ Huv). reflexivity. }
    simpl in Hk.
    destruct (lt_psi_total a b c a' b' c') as [Hl|[[-> [-> ->]]|Hr]];
      try (apply H; simpl; lia).
    + left. rewrite T3lt_cons, Hl. reflexivity.
    + destruct (Nat.lt_trichotomy n n') as [Hn|[<-|Hn]].
      * left. rewrite T3lt_cons, (proj2 (Nat.ltb_lt _ _) Hn).
        destruct (lt_psi_rec T3lt a' b' c' a' b' c'); auto.
        rewrite !T3eqb_refl. reflexivity.
      * destruct (H d d') as [Hd|[->|Hd]]; [lia| | |].
        -- left. rewrite T3lt_cons, Nat.ltb_irrefl, Nat.eqb_refl, !T3eqb_refl, Hd.
           destruct (lt_psi_rec T3lt a' b' c' a' b' c'); reflexivity.
        -- right; left; reflexivity.
        -- right; right. rewrite T3lt_cons, Nat.ltb_irrefl, Nat.eqb_refl, !T3eqb_refl, Hd.
           destruct (lt_psi_rec T3lt a' b' c' a' b' c'); reflexivity.
      * right; right. rewrite T3lt_cons, (proj2 (Nat.ltb_lt _ _) Hn).
        destruct (lt_psi_rec T3lt a' b' c' a' b' c'); auto.
        rewrite !T3eqb_refl. reflexivity.
    + right; right. rewrite T3lt_cons, Hr. reflexivity.
Qed.

Fixpoint T3nf (x:T3) : bool :=
  match x with
  | T3zero => true
  | T3cons a b c _ d => T3nf a && T3nf b && T3nf c && T3nf d && T3lt d (T3psi a b c)
  end.

(** ** Comparison on [VForm] as booleans *)

Definition vf_ltb (x y:VForm) : bool := match VF_compare x y with LT => true | _ => false end.
Definition vf_leb (x y:VForm) : bool := match VF_compare x y with GT => false | _ => true end.

Lemma vf_ltb_correct x y : vf_ltb x y = true <-> VF_denote x < VF_denote y.
Proof.
  unfold vf_ltb.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y); intro H; split; intro H'; auto; try discriminate.
  - elim (ord_lt_irreflexive (VF_denote x)). rewrite H at 2. exact H'.
  - elim (ord_lt_irreflexive (VF_denote x)). transitivity (VF_denote y); auto.
Qed.

Lemma vf_leb_sound x y : vf_leb x y = true -> VF_denote x ≤ VF_denote y.
Proof.
  unfold vf_leb.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y); intros H H'; try discriminate.
  - apply ord_lt_le; exact H.
  - apply H.
Qed.

(** A boolean version of [VF_isNormal]. *)
Fixpoint vf_normalb (x:VForm) : bool :=
  match x with
  | Z => true
  | V m a b =>
      vf_normalb m && vf_normalb a && vf_normalb b &&
      match b with
      | Z => match a with Z => true | V n _ _ => vf_leb n m end
      | V n x' _ =>
          match VF_compare m n with
          | LT => vf_leb b a
          | EQ => vf_leb x' a
          | GT => true
          end
      end
  end.

Lemma vf_normalb_sound : forall x, vf_normalb x = true -> VF_isNormal x.
Proof.
  induction x as [|m IHm a IHa b IHb]; simpl; auto.
  intro H. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  repeat split; auto.
  destruct b as [|n x' y'].
  - destruct a as [|n' ? ?]; auto. apply vf_leb_sound; auto.
  - destruct (VF_compare m n); auto; apply vf_leb_sound; auto.
Qed.

(** ** The translation *)

Definition vf_one : VForm := V Z Z Z.

Fixpoint vf_finiteb (x:VForm) : bool :=
  match x with
  | Z => true
  | V Z Z r => vf_finiteb r
  | _ => false
  end.

(** [x + 1], for [x] in normal form. *)
Fixpoint vf_plus_one (x:VForm) : VForm :=
  match x with
  | Z => vf_one
  | V Z e r => V Z e (vf_plus_one r)
  | V _ _ _ => V Z x vf_one
  end.

(** [-1 + x]: removes one from a finite [x]; fixes infinite [x]. *)
Definition vf_minus_one (x:VForm) : VForm :=
  match x with
  | V Z Z r => r
  | _ => x
  end.

(** If [x = λ + m] with [λ] a strongly critical term ([V n _ _], [n ≠ Z])
    and [m] finite, return [λ]. *)
Definition vf_split_fin (x:VForm) : option VForm :=
  match x with
  | V Z (V (V _ _ _) _ _ as lam) r => if vf_finiteb r then Some lam else None
  | V (V _ _ _) _ _ => Some x
  | _ => None
  end.

(** Whether [V L B ξ] satisfies the top-level normality condition, i.e.
    [ξ] is not a fixed point of [φ_{L,B}] (and, for [ξ = Z], [B] is not
    absorbed). *)
Definition vf_top_ok (L B xi:VForm) : bool :=
  match xi with
  | Z => match B with Z => true | V n _ _ => vf_leb n L end
  | V n x _ =>
      match VF_compare L n with
      | LT => vf_leb xi B
      | EQ => vf_leb x B
      | GT => true
      end
  end.

(** The γ index of the [ω^·] family: skip the ε-numbers. *)
Definition shift_omega (C:VForm) : VForm :=
  match vf_split_fin C with
  | Some _ => vf_plus_one C
  | None => C
  end.

(** The γ index of the family [φ_{L,B}]: β-absorption, then γ-skipping. *)
Definition shift_gen (L B C:VForm) : VForm :=
  let C1 := if vf_top_ok L B Z then C else VF_onePlus C in
  match vf_split_fin C1 with
  | Some lam => if vf_top_ok L B lam then C1 else vf_plus_one C1
  | None => C1
  end.

(** The bracket [ψ(a,b,c)], from the translations of its components. *)
Definition vf_psi (A B C:VForm) : VForm :=
  match A, B with
  | Z, Z => V Z (shift_omega C) Z
  | Z, _ => let B' := vf_minus_one B in V vf_one B' (shift_gen vf_one B' C)
  | _, _ => let L := VF_onePlus A in V L B (shift_gen L B C)
  end.

(** The [ω]-exponent of an additive principal term. *)
Definition vf_exponent (P:VForm) : VForm :=
  match P with
  | V Z e Z => e
  | _ => P
  end.

Fixpoint vf_rep (n:nat) (E tail:VForm) : VForm :=
  match n with
  | O => tail
  | S n => V Z E (vf_rep n E tail)
  end.

Fixpoint T3_to_VF (x:T3) : VForm :=
  match x with
  | T3zero => Z
  | T3cons a b c n d =>
      let P := vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c) in
      let E := vf_exponent P in
      match T3_to_VF d with
      | Z => vf_rep n E P
      | t => vf_rep (S n) E t
      end
  end.

Definition T3_denote (x:T3) : Ord := VF_denote (T3_to_VF x).

(** ** Semantics of sums *)

(** [rep_ord n e t] is [ω^e + (ω^e + ... (ω^e + t))] with [n] copies. *)
Fixpoint rep_ord (n:nat) (e t:Ord) : Ord :=
  match n with
  | O => t
  | S n => expOrd ω e + rep_ord n e t
  end.

Lemma vf_rep_denote n E t :
  VF_denote (vf_rep n E t) ≈ rep_ord n (VF_denote E) (VF_denote t).
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite veblen_ack0 by (first [apply VF_complete | auto with ord]).
    rewrite IHn. reflexivity.
Qed.

Lemma rep_ord_monotone n e : forall t t', t ≤ t' -> rep_ord n e t ≤ rep_ord n e t'.
Proof.
  induction n; simpl; intros; auto.
  apply addOrd_monotone; auto with ord.
Qed.

Lemma rep_ord_increasing n e : forall t t', t < t' -> rep_ord n e t < rep_ord n e t'.
Proof.
  induction n; simpl; intros; auto.
  apply addOrd_increasing; auto.
Qed.

Lemma rep_ord_ge n e t : t ≤ rep_ord n e t.
Proof.
  induction n; simpl; auto with ord.
  rewrite IHn at 1. apply addOrd_le2.
Qed.

Lemma rep_ord_head n e t : expOrd ω e ≤ rep_ord (S n) e t.
Proof. simpl. apply addOrd_le1. Qed.

(** Below an additively closed bound. *)
Lemma rep_ord_bounded n e t z :
  additively_closed z -> expOrd ω e < z -> t < z -> rep_ord n e t < z.
Proof.
  intros Hz He Ht. induction n; simpl; auto.
Qed.

(** The shape of a translated bracket: either [ω^e] or a bracket of
    nonzero level, which is an ε-number. *)
Definition vf_principal_shape (P:VForm) : Prop :=
  match P with
  | V Z _ Z => True
  | V (V _ _ _) _ _ => True
  | _ => False
  end.

Lemma VF_onePlus_V x : x <> Z -> exists m a b, VF_onePlus x = V m a b.
Proof.
  destruct x as [|m a b]; [congruence|]. intros _.
  destruct m as [|m1 m2 m3]; [destruct a as [|a1 a2 a3]|]; simpl; eauto.
Qed.

Lemma vf_psi_shape A B C : vf_principal_shape (vf_psi A B C).
Proof.
  destruct A as [|m a b].
  - destruct B; simpl; auto.
  - destruct (VF_onePlus_V (V m a b)) as [m' [a' [b' Heq]]]; [discriminate|].
    change (vf_principal_shape
              (V (VF_onePlus (V m a b)) B (shift_gen (VF_onePlus (V m a b)) B C))).
    rewrite Heq. exact I.
Qed.

Lemma vf_exponent_correct P :
  vf_principal_shape P ->
  expOrd ω (VF_denote (vf_exponent P)) ≈ VF_denote P.
Proof.
  destruct P as [|L B xi]; simpl; [tauto|].
  destruct L as [|m a b].
  - destruct xi; [|tauto]. intros _. simpl.
    rewrite veblen_ack0 by (first [apply VF_complete | auto with ord]).
    rewrite addOrd_zero_r. reflexivity.
  - intros _. simpl.
    apply veblen_tower_epsilon.
    + exact (VF_complete (V m a b)).
    + exact (VF_complete B).
    + exact (VF_complete xi).
    + destruct (VF_isZero (V m a b)) as [H|H]; [discriminate H|exact H].
Qed.

(** The denotation of a sum: [ψ(a,b,c)·(n+1) + d]. *)
Lemma T3_denote_cons a b c n d :
  let P := vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c) in
  T3_denote (T3cons a b c n d) ≈
    rep_ord (S n) (VF_denote (vf_exponent P)) (T3_denote d).
Proof.
  intro P. unfold T3_denote. simpl. fold P.
  assert (HP : expOrd ω (VF_denote (vf_exponent P)) ≈ VF_denote P).
  { apply vf_exponent_correct. apply vf_psi_shape. }
  destruct (T3_to_VF d) as [|m x y] eqn:Hd.
  - rewrite vf_rep_denote.
    transitivity (rep_ord n (VF_denote (vf_exponent P)) (expOrd ω (VF_denote (vf_exponent P)) + 0)).
    + split; apply rep_ord_monotone; rewrite addOrd_zero_r; apply HP.
    + clear. induction n; simpl.
      * reflexivity.
      * split; apply addOrd_monotone; auto with ord; apply IHn.
  - exact (vf_rep_denote (S n) (vf_exponent P) (V m x y)).
Qed.

Definition T3_exp (a b c:T3) : Ord :=
  VF_denote (vf_exponent (vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c))).

Lemma T3_denote_psi a b c :
  T3_denote (T3psi a b c) ≈ expOrd ω (T3_exp a b c).
Proof.
  unfold T3psi. rewrite T3_denote_cons. simpl.
  rewrite addOrd_zero_r. reflexivity.
Qed.

(** The three ways one sum can lie below another. *)
Lemma sum_lt_head e e' n n' t t' :
  complete e' -> expOrd ω e < expOrd ω e' -> t < expOrd ω e ->
  rep_ord (S n) e t < rep_ord (S n') e' t'.
Proof.
  intros He' Hee Ht.
  apply ord_lt_le_trans with (expOrd ω e'); [|apply rep_ord_head].
  apply rep_ord_bounded; auto.
  - apply expOmega_additively_closed; auto.
  - transitivity (expOrd ω e); auto.
Qed.

Lemma sum_lt_count e n n' t t' :
  (n < n')%nat -> t < expOrd ω e ->
  rep_ord (S n) e t < rep_ord (S n') e t'.
Proof.
  intros Hn Ht.
  apply ord_lt_le_trans with (rep_ord (S n) e (expOrd ω e)).
  - apply rep_ord_increasing; auto.
  - assert (H : forall k u, rep_ord k e (expOrd ω e + u) ≈ rep_ord (S k) e u).
    { induction k; simpl; intros; [reflexivity|].
      split; apply addOrd_monotone; auto with ord; apply IHk. }
    transitivity (rep_ord (S n) e (expOrd ω e + rep_ord (n' - S n) e t')).
    + apply rep_ord_monotone. rewrite <- addOrd_le1. reflexivity.
    + rewrite H.
      replace (S n') with (S (S n) + (n' - S n))%nat by lia.
      clear. generalize (S (S n)). intro k. revert k.
      induction k; simpl; [reflexivity|].
      apply addOrd_monotone; auto with ord.
Qed.

Lemma sum_lt_tail e n t t' :
  t < t' -> rep_ord n e t < rep_ord n e t'.
Proof. apply rep_ord_increasing. Qed.

(** ** Semantic toolkit for brackets *)

Local Hint Resolve
      ackermann_tower_fin_normal veblen_complete veblen_normal veblen_first_normal
      veblen_first_onePlus_normal normal_monotone normal_complete onePlus_normal
      powOmega_normal addOrd_complete addOrd_increasing succ_complete zero_complete
      natOrdSize_complete ackermann_tower_normal ackermann_tower_monotone VF_complete
  : core.

Lemma VF_V_increasing m a x y :
  VF_denote x < VF_denote y -> VF_denote (V m a x) < VF_denote (V m a y).
Proof. intro H. simpl. apply veblen_increasing; auto with ord. Qed.

Lemma VF_V_inflationary m a x : VF_denote x ≤ VF_denote (V m a x).
Proof. simpl. apply veblen_inflationary; auto with ord. Qed.

Lemma VF_V_pos m a x : 0 < VF_denote (V m a x).
Proof. simpl. apply veblen_nonzero; auto with ord. Qed.

(** Comparison across levels: the target is a fixed point of the lower level. *)
Lemma vf_lt_cross L b x n b' x' :
  VF_denote L < VF_denote n ->
  VF_denote b < VF_denote (V n b' x') ->
  VF_denote x < VF_denote (V n b' x') ->
  VF_denote (V L b x) < VF_denote (V n b' x').
Proof.
  intros HL Hb Hx.
  apply ord_lt_le_trans with (VF_denote (V L b (V n b' x'))).
  - apply VF_V_increasing; auto.
  - destruct (Vmn_collapse n L b b' x' HL Hb); auto.
Qed.

(** Comparison within a level. *)
Lemma vf_lt_same L b x b' x' :
  VF_denote b < VF_denote b' ->
  VF_denote x < VF_denote (V L b' x') ->
  VF_denote (V L b x) < VF_denote (V L b' x').
Proof.
  intros Hb Hx.
  apply ord_lt_le_trans with (VF_denote (V L b (V L b' x'))).
  - apply VF_V_increasing; auto.
  - destruct (V_collapse L b b' x' Hb); auto.
Qed.

Lemma VF_one_denote : VF_denote vf_one ≈ 1.
Proof.
  unfold vf_one. simpl.
  rewrite veblen_ack0 by auto with ord.
  rewrite addOrd_zero_r. apply expOrd_zero.
Qed.

Lemma VF_sum_denote e r : VF_denote (V Z e r) ≈ expOrd ω (VF_denote e) + VF_denote r.
Proof. simpl. apply veblen_ack0; auto. Qed.

(** Terms of nonzero level are ε-numbers. *)
Lemma VF_high_epsilon m a b x y :
  expOrd ω (VF_denote (V (V m a b) x y)) ≈ VF_denote (V (V m a b) x y).
Proof.
  apply veblen_tower_epsilon; auto.
  apply VF_V_pos.
Qed.

Lemma vf_plus_one_succ : forall x, VF_denote (vf_plus_one x) ≈ succOrd (VF_denote x).
Proof.
  induction x as [|m Hm a Ha r Hr].
  - simpl vf_plus_one. rewrite VF_one_denote. reflexivity.
  - destruct m as [|m1 m2 m3].
    + simpl vf_plus_one. rewrite !VF_sum_denote, Hr.
      rewrite addOrd_succ. reflexivity.
    + simpl vf_plus_one. rewrite VF_sum_denote, VF_one_denote.
      rewrite VF_high_epsilon.
      rewrite addOrd_succ, addOrd_zero_r. reflexivity.
Qed.

Lemma vf_minus_one_le x : VF_denote (vf_minus_one x) ≤ VF_denote x.
Proof.
  destruct x as [|[|m1 m2 m3] a r]; simpl vf_minus_one; try reflexivity.
  destruct a; try reflexivity.
  rewrite VF_sum_denote. apply addOrd_le2.
Qed.

Lemma additively_closed_eq x y : x ≈ y -> additively_closed x -> additively_closed y.
Proof.
  intros Hxy Hx a b Ha Hb. rewrite <- Hxy in *. apply Hx; auto.
Qed.

(** One plus an infinite additively closed ordinal. *)
Lemma onePlus_closed z : additively_closed z -> 1 < z -> 1 + z ≈ z.
Proof.
  intros Hz H1. split.
  - apply additively_closed_collapse; auto.
  - apply addOrd_le2.
Qed.

Lemma omega_pow_gt1 e : 0 < e -> complete e -> 1 < expOrd ω e.
Proof.
  intros He Hc.
  apply ord_lt_le_trans with ω; [apply omega_gt1|].
  rewrite <- (expOrd_one' ω omega_gt0) at 1.
  apply expOrd_monotone. apply succ_least. auto.
Qed.

Lemma onePlus_minus_one x : x <> Z -> VF_denote x ≈ 1 + VF_denote (vf_minus_one x).
Proof.
  destruct x as [|[|m1 m2 m3] a r]; [congruence| |]; intros _.
  - destruct a as [|a1 a2 a3]; simpl vf_minus_one.
    + rewrite VF_sum_denote. simpl. rewrite expOrd_zero. reflexivity.
    + rewrite VF_sum_denote. rewrite addOrd_assoc.
      rewrite (onePlus_closed (expOrd ω (VF_denote (V a1 a2 a3)))); [reflexivity| |].
      * apply expOmega_additively_closed; auto.
      * apply omega_pow_gt1; auto. apply VF_V_pos.
  - simpl vf_minus_one. symmetry. apply onePlus_closed.
    + apply additively_closed_eq with (expOrd ω (VF_denote (V (V m1 m2 m3) a r))).
      * apply VF_high_epsilon.
      * apply expOmega_additively_closed; auto.
    + rewrite <- VF_high_epsilon. apply omega_pow_gt1; auto. apply VF_V_pos.
Qed.

(** Bounds on the shifted index. *)
Lemma shift_omega_bounds C :
  VF_denote C ≤ VF_denote (shift_omega C) /\
  VF_denote (shift_omega C) ≤ succOrd (VF_denote C).
Proof.
  unfold shift_omega. destruct (vf_split_fin C).
  - rewrite vf_plus_one_succ. split; auto with ord.
  - split; auto with ord.
Qed.

Lemma shift_gen_bounds L B C :
  VF_denote C ≤ VF_denote (shift_gen L B C) /\
  VF_denote (shift_gen L B C) ≤ succOrd (1 + VF_denote C).
Proof.
  unfold shift_gen.
  assert (H1 : VF_denote C ≤ VF_denote (if vf_top_ok L B Z then C else VF_onePlus C) /\
               VF_denote (if vf_top_ok L B Z then C else VF_onePlus C) ≤ 1 + VF_denote C).
  { destruct (vf_top_ok L B Z).
    - split; [reflexivity | apply addOrd_le2].
    - rewrite VF_onePlus_equal. split; [apply addOrd_le2 | reflexivity]. }
  destruct H1 as [H1 H2].
  destruct (vf_split_fin _); [destruct (vf_top_ok L B v)|]; split; auto with ord.
  - rewrite H1. rewrite vf_plus_one_succ. auto with ord.
  - rewrite vf_plus_one_succ. apply succ_monotone. auto.
Qed.

Lemma below_closed_succ_onePlus z c :
  additively_closed z -> 1 < z -> c < z -> succOrd (1 + c) < z.
Proof.
  intros Hz H1 Hc.
  apply ord_le_lt_trans with ((1 + c) + 1).
  - rewrite addOrd_succ, addOrd_zero_r. reflexivity.
  - apply Hz; auto.
Qed.

(** ** Normality of the translation *)

Lemma VF_one_normal : VF_isNormal vf_one.
Proof. simpl. auto. Qed.

Lemma vf_plus_one_normal : forall x, VF_isNormal x -> VF_isNormal (vf_plus_one x).
Proof.
  induction x as [|m Hm a Ha r Hr]; intro Hx.
  - apply VF_one_normal.
  - destruct m as [|m1 m2 m3].
    + simpl in Hx. destruct Hx as [_ [Hna [Hnr Htop]]].
      destruct r as [|[|n1 n2 n3] x y].
      * simpl. repeat split; auto. apply zero_least.
      * change (VF_isNormal (V Z a (V Z x (vf_plus_one y)))).
        specialize (Hr Hnr). simpl in Hr |- *. intuition.
      * change (VF_isNormal (V Z a (V Z (V (V n1 n2 n3) x y) vf_one))).
        specialize (Hr Hnr). simpl in Hr |- *. intuition.
    + change (VF_isNormal (V Z (V (V m1 m2 m3) a r) vf_one)).
      simpl. simpl in Hx. intuition. apply zero_least.
Qed.

Lemma vf_minus_one_normal x : VF_isNormal x -> VF_isNormal (vf_minus_one x).
Proof.
  destruct x as [|[|m1 m2 m3] [|a1 a2 a3] r]; simpl; tauto.
Qed.

(** The top-level condition of [VF_isNormal]. *)
Definition top_cond (L B xi:VForm) : Prop :=
  match xi with
  | Z => match B with Z => True | V n _ _ => VF_denote L >= VF_denote n end
  | V n x _ =>
      match VF_compare L n with
      | LT => VF_denote B >= VF_denote xi
      | EQ => VF_denote B >= VF_denote x
      | GT => True
      end
  end.

Lemma VF_isNormal_V L B xi :
  VF_isNormal (V L B xi) <->
  VF_isNormal L /\ VF_isNormal B /\ VF_isNormal xi /\ top_cond L B xi.
Proof. destruct xi; simpl; tauto. Qed.

Lemma vf_top_ok_sound L B xi : vf_top_ok L B xi = true -> top_cond L B xi.
Proof.
  unfold vf_top_ok, top_cond. destruct xi as [|n x y].
  - destruct B; auto. apply vf_leb_sound.
  - destruct (VF_compare L n); auto; apply vf_leb_sound.
Qed.

Lemma VF_compare_V_Z m a b : VF_compare (V m a b) Z = GT.
Proof. reflexivity. Qed.

(** After the shift, the index is never a fixed point. *)
Lemma skip_top m1 m2 m3 B C1 :
  (C1 = Z -> vf_top_ok (V m1 m2 m3) B Z = true) ->
  vf_top_ok (V m1 m2 m3) B
    (match vf_split_fin C1 with
     | Some lam => if vf_top_ok (V m1 m2 m3) B lam then C1 else vf_plus_one C1
     | None => C1
     end) = true.
Proof.
  intro HC1.
  destruct C1 as [|[|n1 n2 n3] x y]; cbn [vf_split_fin].
  - apply HC1. reflexivity.
  - destruct x as [|[|p1 p2 p3] x1 x2]; try reflexivity.
    destruct (vf_finiteb y); try reflexivity.
    destruct (vf_top_ok (V m1 m2 m3) B (V (V p1 p2 p3) x1 x2)); reflexivity.
  - destruct (vf_top_ok (V m1 m2 m3) B (V (V n1 n2 n3) x y)) eqn:Htop.
    + exact Htop.
    + reflexivity.
Qed.

Lemma shift_gen_top m1 m2 m3 B C :
  vf_top_ok (V m1 m2 m3) B (shift_gen (V m1 m2 m3) B C) = true.
Proof.
  unfold shift_gen. cbv zeta. apply skip_top.
  destruct (vf_top_ok (V m1 m2 m3) B Z) eqn:H0; auto.
  destruct C as [|[|? ? ?] [|? ? ?] ?]; simpl; discriminate.
Qed.

Lemma shift_omega_top C :
  match shift_omega C with Z => True | V n _ _ => n = Z end.
Proof.
  unfold shift_omega.
  destruct C as [|[|n1 n2 n3] x y]; simpl; auto.
  destruct x as [|[|? ? ?] ? ?]; simpl; auto.
  destruct (vf_finiteb y); simpl; auto.
Qed.

Lemma shift_omega_normal C : VF_isNormal C -> VF_isNormal (shift_omega C).
Proof.
  unfold shift_omega. destruct (vf_split_fin C); auto using vf_plus_one_normal.
Qed.

Lemma shift_gen_normal L B C : VF_isNormal C -> VF_isNormal (shift_gen L B C).
Proof.
  intro HC. unfold shift_gen.
  assert (H1 : VF_isNormal (if vf_top_ok L B Z then C else VF_onePlus C)).
  { destruct (vf_top_ok L B Z); auto using VF_onePlus_normal. }
  destruct (vf_split_fin _); [destruct (vf_top_ok L B v)|]; auto using vf_plus_one_normal.
Qed.

Lemma VF_onePlus_nonzero A : A <> Z -> exists m1 m2 m3, VF_onePlus A = V m1 m2 m3 /\ m1 = m1.
Proof.
  intro H. destruct (VF_onePlus_V A H) as [m [a [b E]]]. exists m, a, b. auto.
Qed.

Theorem vf_psi_normal A B C :
  VF_isNormal A -> VF_isNormal B -> VF_isNormal C -> VF_isNormal (vf_psi A B C).
Proof.
  intros HA HB HC.
  destruct A as [|ma aa ba].
  - destruct B as [|mb ab bb].
    + simpl vf_psi. apply VF_isNormal_V. split; [exact I|]. split.
      * apply shift_omega_normal; auto.
      * split; [exact I|]. simpl.
        generalize (shift_omega_top C). destruct (shift_omega C); auto.
        intros ->. apply zero_least.
    + change (VF_isNormal (V vf_one (vf_minus_one (V mb ab bb))
                (shift_gen vf_one (vf_minus_one (V mb ab bb)) C))).
      apply VF_isNormal_V. split; [apply VF_one_normal|].
      split; [apply vf_minus_one_normal; auto|].
      split; [apply shift_gen_normal; auto|].
      apply vf_top_ok_sound. apply shift_gen_top.
  - destruct (VF_onePlus_V (V ma aa ba)) as [m1 [m2 [m3 Heq]]]; [discriminate|].
    change (VF_isNormal (V (VF_onePlus (V ma aa ba)) B
                          (shift_gen (VF_onePlus (V ma aa ba)) B C))).
    apply VF_isNormal_V. split; [apply VF_onePlus_normal; auto|].
    split; auto. split; [apply shift_gen_normal; auto|].
    rewrite Heq. apply vf_top_ok_sound. apply shift_gen_top.
Qed.

Lemma expOmega_reflect x y :
  expOrd ω (VF_denote x) < expOrd ω (VF_denote y) -> VF_denote x < VF_denote y.
Proof.
  intro H. generalize (VF_compare_correct x y).
  destruct (VF_compare x y); intro Hc; auto.
  - elim (ord_lt_irreflexive (expOrd ω (VF_denote y))).
    apply ord_le_lt_trans with (expOrd ω (VF_denote x)); auto.
    apply expOrd_monotone. apply Hc.
  - elim (ord_lt_irreflexive (expOrd ω (VF_denote y))).
    transitivity (expOrd ω (VF_denote x)); auto.
    apply expOrd_increasing; auto. apply omega_gt1.
Qed.

Lemma VF_rep_normal E T :
  VF_isNormal (V Z E T) -> forall k, VF_isNormal (vf_rep (S k) E T).
Proof.
  intros H k. induction k; auto.
  change (VF_isNormal (V Z E (V Z E (vf_rep k E T)))).
  apply VF_isNormal_V. apply VF_isNormal_V in H.
  destruct H as [_ [HE _]].
  split; [exact I|]. split; [exact HE|]. split; [exact IHk|].
  unfold top_cond; apply ord_le_refl.
Qed.

Lemma vf_exponent_normal P :
  vf_principal_shape P -> VF_isNormal P -> VF_isNormal (vf_exponent P).
Proof.
  destruct P as [|[|? ? ?] ? [|? ? ?]]; simpl; try tauto.
Qed.

Lemma T3_to_VF_cons_normal a b c n d :
  let P := vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c) in
  VF_isNormal P -> VF_isNormal (T3_to_VF d) -> T3_denote d < VF_denote P ->
  VF_isNormal (T3_to_VF (T3cons a b c n d)).
Proof.
  intros P HP Hd Hlt.
  assert (Hshape := vf_psi_shape (T3_to_VF a) (T3_to_VF b) (T3_to_VF c)). fold P in Hshape.
  assert (HE : expOrd ω (VF_denote (vf_exponent P)) ≈ VF_denote P) by (apply vf_exponent_correct; auto).
  assert (HEn : VF_isNormal (vf_exponent P)) by (apply vf_exponent_normal; auto).
  simpl T3_to_VF. fold P. unfold T3_denote in Hlt.
  destruct (T3_to_VF d) as [|m x y] eqn:Ed.
  - destruct n as [|k]; [exact HP|].
    apply VF_rep_normal.
    destruct P as [|[|p1 p2 p3] pb pc]; simpl in Hshape; try contradiction.
    + destruct pc; [|contradiction]. simpl vf_exponent.
      apply VF_isNormal_V. pose proof HP as HP'. apply VF_isNormal_V in HP'.
      destruct HP' as [_ [Hpb _]].
      split; [exact I|]. split; [exact Hpb|]. split; [exact HP|].
      unfold top_cond; apply ord_le_refl.
    + simpl vf_exponent.
      apply VF_isNormal_V.
      split; [exact I|]. split; [exact HP|]. split; [exact HP|].
      unfold top_cond; apply ord_le_refl.
  - apply VF_rep_normal.
    apply VF_isNormal_V.
    split; [exact I|]. split; [exact HEn|]. split; [exact Hd|].
    destruct m as [|m1 m2 m3].
    + change (VF_denote (vf_exponent P) >= VF_denote x).
      apply ord_lt_le. apply expOmega_reflect. rewrite HE.
      apply ord_le_lt_trans with (VF_denote (V Z x y)); auto.
      rewrite VF_sum_denote. apply addOrd_le1.
    + change (VF_denote (vf_exponent P) >= VF_denote (V (V m1 m2 m3) x y)).
      apply ord_lt_le. apply expOmega_reflect. rewrite HE.
      rewrite VF_high_epsilon. auto.
Qed.

(** Every bracket lies strictly above its [b] and [c] arguments. *)
Lemma psi_gt_c A B C :
  VF_isNormal (vf_psi A B C) -> VF_denote C < VF_denote (vf_psi A B C).
Proof.
  intro HP. generalize (normal_subterm_shrink _ HP).
  destruct A as [|ma aa ba].
  - destruct B as [|mb ab bb].
    + simpl vf_psi. simpl subterm_shrink. intros [_ [H _]].
      apply ord_le_lt_trans with (VF_denote (shift_omega C)); auto.
      apply shift_omega_bounds.
    + change (subterm_shrink (V vf_one (vf_minus_one (V mb ab bb))
                (shift_gen vf_one (vf_minus_one (V mb ab bb)) C)) ->
              VF_denote C < VF_denote (V vf_one (vf_minus_one (V mb ab bb))
                (shift_gen vf_one (vf_minus_one (V mb ab bb)) C))).
      simpl subterm_shrink. intros [_ [_ H]].
      eapply ord_le_lt_trans; [apply shift_gen_bounds | exact H].
  - change (subterm_shrink (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C)) ->
            VF_denote C < VF_denote (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C))).
    simpl subterm_shrink. intros [_ [_ H]].
    eapply ord_le_lt_trans; [apply shift_gen_bounds | exact H].
Qed.

Lemma psi_gt_b A B C :
  VF_isNormal (vf_psi A B C) -> VF_denote B < VF_denote (vf_psi A B C).
Proof.
  intro HP. generalize (normal_subterm_shrink _ HP).
  destruct A as [|ma aa ba].
  - destruct B as [|mb ab bb].
    + intros _. simpl vf_psi. apply VF_V_pos.
    + set (B := V mb ab bb).
      change (subterm_shrink (V vf_one (vf_minus_one B) (shift_gen vf_one (vf_minus_one B) C)) ->
              VF_denote B < VF_denote (V vf_one (vf_minus_one B) (shift_gen vf_one (vf_minus_one B) C))).
      simpl subterm_shrink. intros [_ [H _]].
      rewrite (onePlus_minus_one B) by discriminate.
      unfold vf_one in *.
      set (Q := V (V Z Z Z) (vf_minus_one B) (shift_gen (V Z Z Z) (vf_minus_one B) C)) in *.
      assert (Hcl : additively_closed (VF_denote Q)).
      { apply additively_closed_eq with (expOrd ω (VF_denote Q)).
        - apply VF_high_epsilon.
        - apply expOmega_additively_closed; auto. }
      assert (H1 : 1 < VF_denote Q).
      { unfold Q. rewrite <- VF_high_epsilon. apply omega_pow_gt1; auto. apply VF_V_pos. }
      apply Hcl; auto.
  - change (subterm_shrink (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C)) ->
            VF_denote B < VF_denote (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C))).
    simpl subterm_shrink. intros [_ [H _]]. exact H.
Qed.

(** ** Strict monotonicity of the shifted index *)

Lemma vf_plus_one_finite r : vf_finiteb r = true -> vf_finiteb (vf_plus_one r) = true.
Proof.
  induction r as [|[|m1 m2 m3] _ [|a1 a2 a3] _ r IH]; simpl; try discriminate; auto.
Qed.

Lemma split_plus_one C lam :
  vf_split_fin C = Some lam -> vf_split_fin (vf_plus_one C) = Some lam.
Proof.
  destruct C as [|[|n1 n2 n3] x y]; simpl; try discriminate.
  - destruct x as [|[|p1 p2 p3] x1 x2]; try discriminate.
    destruct (vf_finiteb y) eqn:Hy; try discriminate.
    intro H. injection H as <-. simpl. rewrite (vf_plus_one_finite y Hy). reflexivity.
  - intro H. injection H as <-. reflexivity.
Qed.

Lemma lt_succ_le x y : x < succOrd y -> x ≤ y.
Proof.
  intro H. rewrite ord_lt_unfold in H. destruct H as [[] H]. exact H.
Qed.

(** The common shape of both shifts: [skip C1] adds one exactly when
    [C1 = λ + m] with [λ] a fixed point (decided by [test]). *)
Definition skip (test:VForm -> bool) (C1:VForm) : VForm :=
  match vf_split_fin C1 with
  | Some lam => if test lam then C1 else vf_plus_one C1
  | None => C1
  end.

Lemma skip_ge test C1 : VF_denote C1 ≤ VF_denote (skip test C1).
Proof.
  unfold skip. destruct (vf_split_fin C1); [destruct (test v)|]; try reflexivity.
  rewrite vf_plus_one_succ. auto with ord.
Qed.

Lemma skip_normal test C1 : VF_isNormal C1 -> VF_isNormal (skip test C1).
Proof.
  unfold skip. destruct (vf_split_fin C1); [destruct (test v)|]; auto using vf_plus_one_normal.
Qed.

Lemma skip_mono test C1 C1' :
  VF_isNormal C1 -> VF_isNormal C1' ->
  VF_denote C1 < VF_denote C1' ->
  VF_denote (skip test C1) < VF_denote (skip test C1').
Proof.
  intros Hn Hn' Hlt.
  unfold skip at 1.
  destruct (vf_split_fin C1) as [lam|] eqn:Hs; [destruct (test lam) eqn:Ht|].
  - eapply ord_lt_le_trans; [exact Hlt | apply skip_ge].
  - (* C1 is skipped: compare C1 + 1 with C1' *)
    generalize (VF_compare_correct (vf_plus_one C1) C1').
    destruct (VF_compare (vf_plus_one C1) C1'); intro Hc.
    + eapply ord_lt_le_trans; [exact Hc | apply skip_ge].
    + assert (HE : vf_plus_one C1 = C1').
      { apply normal_forms_unique; auto using vf_plus_one_normal. }
      subst C1'. unfold skip.
      rewrite (split_plus_one _ _ Hs), Ht.
      rewrite (vf_plus_one_succ (vf_plus_one C1)). apply succ_lt.
    + elim (ord_lt_irreflexive (VF_denote C1)).
      apply ord_lt_le_trans with (VF_denote C1'); auto.
      apply lt_succ_le. rewrite <- vf_plus_one_succ. exact Hc.
  - eapply ord_lt_le_trans; [exact Hlt | apply skip_ge].
Qed.

Lemma shift_omega_skip C : shift_omega C = skip (fun _ => false) C.
Proof. unfold shift_omega, skip. destruct (vf_split_fin C); reflexivity. Qed.

Lemma shift_gen_skip L B C :
  shift_gen L B C = skip (vf_top_ok L B) (if vf_top_ok L B Z then C else VF_onePlus C).
Proof. reflexivity. Qed.

Lemma shift_omega_mono C C' :
  VF_isNormal C -> VF_isNormal C' -> VF_denote C < VF_denote C' ->
  VF_denote (shift_omega C) < VF_denote (shift_omega C').
Proof. rewrite !shift_omega_skip. apply skip_mono. Qed.

Lemma shift_gen_mono L B C C' :
  VF_isNormal C -> VF_isNormal C' -> VF_denote C < VF_denote C' ->
  VF_denote (shift_gen L B C) < VF_denote (shift_gen L B C').
Proof.
  intros Hn Hn' Hlt. rewrite !shift_gen_skip.
  destruct (vf_top_ok L B Z); apply skip_mono; auto using VF_onePlus_normal.
  rewrite !VF_onePlus_equal. apply addOrd_increasing. exact Hlt.
Qed.

(** ** Comparing brackets *)

Lemma vf_psi_nonzero A B C : vf_psi A B C <> Z.
Proof. generalize (vf_psi_shape A B C). destruct (vf_psi A B C); simpl; [tauto | discriminate]. Qed.

Lemma vf_psi_high A B C :
  (A <> Z \/ B <> Z) -> exists m1 m2 m3 x y, vf_psi A B C = V (V m1 m2 m3) x y.
Proof.
  intros H. destruct A as [|ma aa ba].
  - destruct B as [|mb ab bb]; [destruct H; congruence|].
    exists Z, Z, Z, (vf_minus_one (V mb ab bb)), (shift_gen vf_one (vf_minus_one (V mb ab bb)) C).
    reflexivity.
  - destruct (VF_onePlus_V (V ma aa ba)) as [m1 [m2 [m3 Heq]]]; [discriminate|].
    exists m1, m2, m3, B, (shift_gen (VF_onePlus (V ma aa ba)) B C).
    change (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C) =
            V (V m1 m2 m3) B (shift_gen (VF_onePlus (V ma aa ba)) B C)).
    rewrite Heq at 1. reflexivity.
Qed.

Lemma high_facts P :
  (exists m1 m2 m3 x y, P = V (V m1 m2 m3) x y) ->
  additively_closed (VF_denote P) /\ 1 < VF_denote P.
Proof.
  intros [m1 [m2 [m3 [x [y ->]]]]]. split.
  - apply additively_closed_eq with (expOrd ω (VF_denote (V (V m1 m2 m3) x y))).
    + apply VF_high_epsilon.
    + apply expOmega_additively_closed; auto.
  - rewrite <- VF_high_epsilon. apply omega_pow_gt1; auto. apply VF_V_pos.
Qed.

Lemma below_high_shift P L B C :
  (exists m1 m2 m3 x y, P = V (V m1 m2 m3) x y) ->
  VF_denote C < VF_denote P ->
  VF_denote (shift_gen L B C) < VF_denote P /\ VF_denote (shift_omega C) < VF_denote P.
Proof.
  intros HP HC. destruct (high_facts P HP) as [Hcl H1].
  assert (Hs : succOrd (1 + VF_denote C) < VF_denote P) by (apply below_closed_succ_onePlus; auto).
  split.
  - eapply ord_le_lt_trans; [apply shift_gen_bounds | exact Hs].
  - eapply ord_le_lt_trans; [apply shift_omega_bounds|].
    eapply ord_le_lt_trans; [|exact Hs]. apply succ_monotone. apply addOrd_le2.
Qed.

Lemma VF_onePlus_pos A : A <> Z -> 1 < VF_denote (VF_onePlus A).
Proof.
  intro HA. rewrite VF_onePlus_equal.
  apply ord_le_lt_trans with (1 + 0); [rewrite addOrd_zero_r; reflexivity|].
  apply addOrd_increasing.
  destruct A; [congruence|]. apply VF_V_pos.
Qed.

(** Case a: same [a] and [b], larger [c]. *)
Lemma psi_mono_c A B C C' :
  VF_isNormal C -> VF_isNormal C' -> VF_denote C < VF_denote C' ->
  VF_denote (vf_psi A B C) < VF_denote (vf_psi A B C').
Proof.
  intros Hn Hn' Hlt.
  destruct A as [|ma aa ba].
  - destruct B as [|mb ab bb].
    + simpl vf_psi. rewrite !VF_sum_denote, !addOrd_zero_r.
      apply expOrd_increasing; [apply omega_gt1|].
      apply shift_omega_mono; auto.
    + change (VF_denote (V vf_one (vf_minus_one (V mb ab bb)) (shift_gen vf_one (vf_minus_one (V mb ab bb)) C)) <
              VF_denote (V vf_one (vf_minus_one (V mb ab bb)) (shift_gen vf_one (vf_minus_one (V mb ab bb)) C'))).
      apply VF_V_increasing. apply shift_gen_mono; auto.
  - change (VF_denote (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C)) <
            VF_denote (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C'))).
    apply VF_V_increasing. apply shift_gen_mono; auto.
Qed.

(** Case b: same [a], larger [b], and [c] below the larger bracket. *)
Lemma psi_lt_same_a A B B' C C' :
  VF_denote B < VF_denote B' ->
  VF_denote C < VF_denote (vf_psi A B' C') ->
  VF_denote (vf_psi A B C) < VF_denote (vf_psi A B' C').
Proof.
  intros HB HC.
  assert (HB' : B' <> Z) by (intros ->; elim (ord_lt_irreflexive 0);
                            apply ord_le_lt_trans with (VF_denote B); auto with ord).
  assert (Hhigh := vf_psi_high A B' C' (or_intror HB')).
  destruct (below_high_shift _ (match A with Z => vf_one | _ => VF_onePlus A end)
             (match A with Z => vf_minus_one B | _ => B end) C Hhigh HC) as [Hg Ho].
  destruct A as [|ma aa ba].
  - destruct B' as [|mb' ab' bb']; [congruence|].
    destruct B as [|mb ab bb].
    + simpl vf_psi at 1.
      change (VF_denote (V Z (shift_omega C) Z) <
              VF_denote (V vf_one (vf_minus_one (V mb' ab' bb')) (shift_gen vf_one (vf_minus_one (V mb' ab' bb')) C'))).
      apply vf_lt_cross.
      * rewrite VF_one_denote. apply succ_lt.
      * apply Ho.
      * apply VF_V_pos.
    + change (VF_denote (V vf_one (vf_minus_one (V mb ab bb)) (shift_gen vf_one (vf_minus_one (V mb ab bb)) C)) <
              VF_denote (V vf_one (vf_minus_one (V mb' ab' bb')) (shift_gen vf_one (vf_minus_one (V mb' ab' bb')) C'))).
      apply vf_lt_same.
      * apply onePlus_lt_cancel.
        rewrite <- !onePlus_minus_one by discriminate. exact HB.
      * exact Hg.
  - change (VF_denote (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C)) <
            VF_denote (V (VF_onePlus (V ma aa ba)) B' (shift_gen (VF_onePlus (V ma aa ba)) B' C'))).
    apply vf_lt_same; auto.
Qed.

(** Case e: larger [a], with [b] and [c] below the larger bracket. *)
Lemma psi_lt_cross A A' B B' C C' :
  VF_denote A < VF_denote A' ->
  VF_denote B < VF_denote (vf_psi A' B' C') ->
  VF_denote C < VF_denote (vf_psi A' B' C') ->
  VF_denote (vf_psi A B C) < VF_denote (vf_psi A' B' C').
Proof.
  intros HA HB HC.
  assert (HA' : A' <> Z) by (intros ->; elim (ord_lt_irreflexive 0);
                            apply ord_le_lt_trans with (VF_denote A); auto with ord).
  assert (Hhigh := vf_psi_high A' B' C' (or_introl HA')).
  destruct A' as [|ma' aa' ba']; [congruence|].
  change (VF_denote (vf_psi A B C) <
          VF_denote (V (VF_onePlus (V ma' aa' ba')) B' (shift_gen (VF_onePlus (V ma' aa' ba')) B' C'))).
  change (VF_denote C < VF_denote (V (VF_onePlus (V ma' aa' ba')) B' (shift_gen (VF_onePlus (V ma' aa' ba')) B' C'))) in HC.
  change (VF_denote B < VF_denote (V (VF_onePlus (V ma' aa' ba')) B' (shift_gen (VF_onePlus (V ma' aa' ba')) B' C'))) in HB.
  set (P' := V (VF_onePlus (V ma' aa' ba')) B' (shift_gen (VF_onePlus (V ma' aa' ba')) B' C')) in *.
  assert (Hhigh' : exists m1 m2 m3 x y, P' = V (V m1 m2 m3) x y) by exact Hhigh.
  destruct A as [|ma aa ba].
  - destruct B as [|mb ab bb].
    + simpl vf_psi. apply vf_lt_cross.
      * simpl VF_denote at 1. apply ord_lt_trans with 1; [apply succ_lt|].
        apply VF_onePlus_pos. discriminate.
      * apply (below_high_shift P' Z Z C Hhigh' HC).
      * apply VF_V_pos.
    + change (VF_denote (V vf_one (vf_minus_one (V mb ab bb)) (shift_gen vf_one (vf_minus_one (V mb ab bb)) C)) <
              VF_denote P').
      apply vf_lt_cross.
      * rewrite VF_one_denote. apply VF_onePlus_pos. discriminate.
      * eapply ord_le_lt_trans; [apply vf_minus_one_le | exact HB].
      * apply (below_high_shift P' vf_one (vf_minus_one (V mb ab bb)) C Hhigh' HC).
  - change (VF_denote (V (VF_onePlus (V ma aa ba)) B (shift_gen (VF_onePlus (V ma aa ba)) B C)) <
            VF_denote P').
    apply vf_lt_cross.
    + rewrite !VF_onePlus_equal. apply addOrd_increasing. exact HA.
    + exact HB.
    + apply (below_high_shift P' (VF_onePlus (V ma aa ba)) B C Hhigh' HC).
Qed.

Lemma T3_denote_psi_vf a b c :
  T3_denote (T3psi a b c) ≈ VF_denote (vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c)).
Proof.
  rewrite T3_denote_psi. unfold T3_exp. apply vf_exponent_correct. apply vf_psi_shape.
Qed.

Lemma lt_psi_cases f a b c a' b' c' :
  let x := T3psi a b c in
  let x' := T3psi a' b' c' in
  lt_psi_rec f a b c a' b' c' = true ->
  (a = a' /\ b = b' /\ f c c' = true) \/
  (a = a' /\ f b b' = true /\ f c x' = true) \/
  (a = a' /\ f b' b = true /\ f x c' = true) \/
  (a = a' /\ f b' b = true /\ x = c') \/
  (f a a' = true /\ f b x' = true /\ f c x' = true) \/
  (f a' a = true /\ f x b' = true) \/
  (f a' a = true /\ x = b') \/
  (f a' a = true /\ f x c' = true) \/
  (f a' a = true /\ x = c').
Proof.
  intros x x' H. unfold lt_psi_rec in H. fold x x' in H.
  repeat rewrite Bool.orb_true_iff in H.
  repeat rewrite Bool.andb_true_iff in H.
  repeat rewrite T3eqb_eq in H.
  tauto.
Qed.

Lemma T3nf_psi_inv a b c :
  T3nf (T3psi a b c) = true -> T3nf a = true /\ T3nf b = true /\ T3nf c = true.
Proof.
  intro H.
  change (T3nf a && T3nf b && T3nf c && T3nf T3zero && T3lt T3zero (T3cons a b c 0 T3zero) = true) in H.
  repeat (apply andb_prop in H as [H ?]). auto.
Qed.

Lemma T3nf_psi a b c :
  T3nf a = true -> T3nf b = true -> T3nf c = true -> T3nf (T3psi a b c) = true.
Proof.
  intros Ha Hb Hc.
  change (T3nf a && T3nf b && T3nf c && T3nf T3zero && T3lt T3zero (T3cons a b c 0 T3zero) = true).
  rewrite Ha, Hb, Hc, T3lt_zero_cons. reflexivity.
Qed.

Lemma T3lt_zero_r x : T3lt x T3zero = false.
Proof. rewrite T3lt_unfold. destruct x; reflexivity. Qed.

Lemma T3_to_VF_cons_nonzero a b c n d : T3_to_VF (T3cons a b c n d) <> Z.
Proof.
  cbn [T3_to_VF]. destruct (T3_to_VF d); destruct n; cbn [vf_rep]; try discriminate.
  apply vf_psi_nonzero.
Qed.

Lemma T3_denote_cons_pos a b c n d : 0 < T3_denote (T3cons a b c n d).
Proof.
  unfold T3_denote. generalize (T3_to_VF_cons_nonzero a b c n d).
  destruct (T3_to_VF (T3cons a b c n d)); [congruence|]. intros _. apply VF_V_pos.
Qed.

Theorem bracket_sound a b c a' b' c' :
  let x := T3psi a b c in
  let y := T3psi a' b' c' in
  T3nf x = true -> T3nf y = true ->
  VF_isNormal (T3_to_VF a) -> VF_isNormal (T3_to_VF b) -> VF_isNormal (T3_to_VF c) ->
  VF_isNormal (T3_to_VF a') -> VF_isNormal (T3_to_VF b') -> VF_isNormal (T3_to_VF c') ->
  (forall u v, (T3size u + T3size v < T3size x + T3size y)%nat ->
     T3nf u = true -> T3nf v = true -> T3lt u v = true -> T3_denote u < T3_denote v) ->
  lt_psi_rec T3lt a b c a' b' c' = true ->
  T3_denote x < T3_denote y.
Proof.
  intros x y Hx Hy Na Nb Nc Na' Nb' Nc' IH H.
  destruct (T3nf_psi_inv a b c Hx) as [Fa [Fb Fc]].
  destruct (T3nf_psi_inv a' b' c' Hy) as [Fa' [Fb' Fc']].
  assert (HP : VF_isNormal (vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c))) by (apply vf_psi_normal; auto).
  assert (HP' : VF_isNormal (vf_psi (T3_to_VF a') (T3_to_VF b') (T3_to_VF c'))) by (apply vf_psi_normal; auto).
  assert (Ex : T3_denote x ≈ VF_denote (vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c))) by apply T3_denote_psi_vf.
  assert (Ey : T3_denote y ≈ VF_denote (vf_psi (T3_to_VF a') (T3_to_VF b') (T3_to_VF c'))) by apply T3_denote_psi_vf.
  assert (Sx : T3size x = S (T3size a + T3size b + T3size c + 0)) by reflexivity.
  assert (Sy : T3size y = S (T3size a' + T3size b' + T3size c' + 0)) by reflexivity.
  rewrite Ex, Ey.
  destruct (lt_psi_cases _ _ _ _ _ _ _ H) as
      [[Ea [Eb Hc]]|[[Ea [Hb Hc]]|[[Ea [Hb Hc]]|[[Ea [Hb Hc]]|[[Ha [Hb Hc]]|
       [[Ha Hb]|[[Ha Hb]|[[Ha Hc]|[Ha Hc]]]]]]]]].
  - (* a *) subst a' b'. apply psi_mono_c; auto.
    apply (IH c c'); auto. unfold x, y; simpl; lia.
  - (* b *) subst a'. apply psi_lt_same_a.
    + apply (IH b b'); auto. unfold x, y; simpl; lia.
    + rewrite <- Ey. apply (IH c y); auto. unfold x, y; simpl; lia.
  - (* c *) rewrite <- Ex.
    apply ord_lt_trans with (VF_denote (T3_to_VF c')).
    + apply (IH x c'); auto. unfold x, y; simpl; lia.
    + apply psi_gt_c; auto.
  - (* d *) rewrite <- Ex. unfold x. rewrite Hc. apply psi_gt_c; auto.
  - (* e *) apply psi_lt_cross.
    + apply (IH a a'); auto. unfold x, y; simpl; lia.
    + rewrite <- Ey. apply (IH b y); auto. unfold x, y; simpl; lia.
    + rewrite <- Ey. apply (IH c y); auto. unfold x, y; simpl; lia.
  - (* f *) rewrite <- Ex.
    apply ord_lt_trans with (VF_denote (T3_to_VF b')).
    + apply (IH x b'); auto. unfold x, y; simpl; lia.
    + apply psi_gt_b; auto.
  - (* g *) rewrite <- Ex. unfold x. rewrite Hb. apply psi_gt_b; auto.
  - (* h *) rewrite <- Ex.
    apply ord_lt_trans with (VF_denote (T3_to_VF c')).
    + apply (IH x c'); auto. unfold x, y; simpl; lia.
    + apply psi_gt_c; auto.
  - (* i *) rewrite <- Ex. unfold x. rewrite Hc. apply psi_gt_c; auto.
Qed.

(** ** The main theorem *)

Lemma T3nf_cons_inv a b c n d :
  T3nf (T3cons a b c n d) = true ->
  T3nf a = true /\ T3nf b = true /\ T3nf c = true /\ T3nf d = true /\
  T3lt d (T3psi a b c) = true.
Proof.
  intro H. simpl in H.
  repeat (apply andb_prop in H as [H ?]). auto.
Qed.

Lemma T3_denote_head_bound a b c d :
  T3_denote d < T3_denote (T3psi a b c) ->
  T3_denote d <
    expOrd ω (VF_denote (vf_exponent (vf_psi (T3_to_VF a) (T3_to_VF b) (T3_to_VF c)))).
Proof.
  intro H. rewrite vf_exponent_correct by apply vf_psi_shape.
  rewrite <- T3_denote_psi_vf. exact H.
Qed.

Theorem GrimmT3_main : forall m,
  (forall t, (T3size t <= m)%nat -> T3nf t = true -> VF_isNormal (T3_to_VF t)) /\
  (forall u v, (T3size u + T3size v <= m)%nat ->
     T3nf u = true -> T3nf v = true -> T3lt u v = true -> T3_denote u < T3_denote v).
Proof.
  induction m as [m IH] using (well_founded_induction Wf_nat.lt_wf).
  assert (Hnorm : forall t, (T3size t < m)%nat -> T3nf t = true -> VF_isNormal (T3_to_VF t)).
  { intros t Ht Hnf. apply (proj1 (IH (T3size t) Ht)); auto. }
  assert (Hsound : forall u v, (T3size u + T3size v <= m)%nat ->
            T3nf u = true -> T3nf v = true -> T3lt u v = true -> T3_denote u < T3_denote v).
  { intros u v Hm Hu Hv Huv.
    destruct u as [|a b c n d]; destruct v as [|a' b' c' n' d'].
    - rewrite T3lt_zero_r in Huv. discriminate.
    - apply T3_denote_cons_pos.
    - rewrite T3lt_zero_r in Huv. discriminate.
    - assert (Hsmall : forall u' v', (T3size u' + T3size v' < T3size (T3cons a b c n d) + T3size (T3cons a' b' c' n' d'))%nat ->
                T3nf u' = true -> T3nf v' = true -> T3lt u' v' = true -> T3_denote u' < T3_denote v').
      { intros u' v' Hs. apply (proj2 (IH (T3size u' + T3size v')%nat ltac:(lia))). lia. }
      destruct (T3nf_cons_inv _ _ _ _ _ Hu) as [Fa [Fb [Fc [Fd Hd]]]].
      destruct (T3nf_cons_inv _ _ _ _ _ Hv) as [Fa' [Fb' [Fc' [Fd' Hd']]]].
      simpl T3size in Hm, Hsmall.
      assert (Hdb : T3_denote d < T3_denote (T3psi a b c)).
      { apply Hsmall; auto. simpl; lia. apply T3nf_psi; auto. }
      rewrite T3lt_cons in Huv.
      rewrite !T3_denote_cons.
      destruct (lt_psi_rec T3lt a b c a' b' c') eqn:Hpsi.
      + apply sum_lt_head.
        * apply VF_complete.
        * rewrite !vf_exponent_correct by apply vf_psi_shape.
          rewrite <- !T3_denote_psi_vf.
          apply bracket_sound; auto using T3nf_psi.
          -- apply Hnorm; auto. lia.
          -- apply Hnorm; auto. lia.
          -- apply Hnorm; auto. lia.
          -- apply Hnorm; auto. lia.
          -- apply Hnorm; auto. lia.
          -- apply Hnorm; auto. lia.
          -- intros u' v' Hs. apply Hsmall. simpl in Hs |- *. lia.
        * apply T3_denote_head_bound. exact Hdb.
      + destruct (T3eqb a a' && T3eqb b b' && T3eqb c c') eqn:Heq; [|discriminate].
        apply andb_prop in Heq as [Heq Hc]. apply andb_prop in Heq as [Ha Hb].
        apply T3eqb_eq in Ha, Hb, Hc. subst a' b' c'.
        destruct (Nat.ltb n n') eqn:Hn.
        * apply sum_lt_count.
          -- apply Nat.ltb_lt. exact Hn.
          -- apply T3_denote_head_bound. exact Hdb.
        * destruct (Nat.eqb n n') eqn:Hn2; [|discriminate].
          apply Nat.eqb_eq in Hn2. subst n'.
          apply sum_lt_tail. apply Hsmall; auto. simpl; lia. }
  split; auto.
  intros t Ht Hnf.
  destruct t as [|a b c n d]; [exact I|].
  destruct (T3nf_cons_inv _ _ _ _ _ Hnf) as [Fa [Fb [Fc [Fd Hd]]]].
  simpl T3size in Ht.
  apply T3_to_VF_cons_normal.
  - apply vf_psi_normal; apply Hnorm; auto; lia.
  - apply Hnorm; auto. lia.
  - rewrite <- T3_denote_psi_vf. apply Hsound; auto.
    + simpl. lia.
    + apply T3nf_psi; auto.
Qed.

(** Grimm's normal forms translate to normal forms of [ATowerNotation]. *)
Theorem T3_to_VF_normal t : T3nf t = true -> VF_isNormal (T3_to_VF t).
Proof. apply (proj1 (GrimmT3_main (T3size t))). auto. Qed.

(** Grimm's comparison is sound and complete for the semantic order. *)
Theorem T3lt_correct t u :
  T3nf t = true -> T3nf u = true ->
  (T3lt t u = true <-> T3_denote t < T3_denote u).
Proof.
  intros Ht Hu. split.
  - apply (proj2 (GrimmT3_main (T3size t + T3size u))); auto.
  - intro Hlt.
    destruct (T3lt_total t u) as [H|[->|H]]; auto.
    + elim (ord_lt_irreflexive (T3_denote u)); auto.
    + elim (ord_lt_irreflexive (T3_denote t)).
      transitivity (T3_denote u); auto.
      apply (proj2 (GrimmT3_main (T3size u + T3size t))); auto.
Qed.

(** Normal forms are unique: equal denotations mean equal terms. *)
Theorem T3_denote_inj t u :
  T3nf t = true -> T3nf u = true -> T3_denote t ≈ T3_denote u -> t = u.
Proof.
  intros Ht Hu Heq.
  destruct (T3lt_total t u) as [H|[->|H]]; auto.
  - apply (T3lt_correct t u Ht Hu) in H.
    elim (ord_lt_irreflexive (T3_denote u)). rewrite <- Heq at 1. exact H.
  - apply (T3lt_correct u t Hu Ht) in H.
    elim (ord_lt_irreflexive (T3_denote u)). rewrite <- Heq at 2. exact H.
Qed.

(** ** Sanity checks *)

Definition t_one   := T3psi T3zero T3zero T3zero.
Definition t_two   := T3cons T3zero T3zero T3zero 1 T3zero.
Definition t_omega := T3psi T3zero T3zero t_one.
Definition t_eps0  := T3psi T3zero t_one T3zero.
Definition t_Gamma0 := T3psi t_one T3zero T3zero.

Example T3_to_VF_one : T3_to_VF t_one = V Z Z Z.          Proof. reflexivity. Qed.
Example T3_to_VF_omega : T3_to_VF t_omega = V Z vf_one Z. Proof. reflexivity. Qed.
Example T3_to_VF_eps0 : T3_to_VF t_eps0 = V vf_one Z Z.   Proof. reflexivity. Qed.
Example T3_to_VF_Gamma0 :
  T3_to_VF t_Gamma0 = V (V Z Z vf_one) Z Z.              Proof. reflexivity. Qed.

(** Ackermann's (1,1,ε₀) is ω^(ε₀+1), not ω^ε₀ = ε₀. *)
Example T3_to_VF_skip :
  T3_to_VF (T3psi T3zero T3zero t_eps0) = V Z (V Z (V vf_one Z Z) vf_one) Z.
Proof. reflexivity. Qed.

(** Grimm's [ψ(0,Γ₀,0)] lies above [Γ₀]: β-absorption. *)
Example T3_to_VF_absorb :
  T3_to_VF (T3psi T3zero t_Gamma0 T3zero) =
  V vf_one (V (V Z Z vf_one) Z Z) vf_one.
Proof. reflexivity. Qed.

(** ** Order type: [LargeAckermannOrdinal] *)

Lemma VF_V_monotone m a b m' a' b' :
  VF_denote m ≤ VF_denote m' -> VF_denote a ≤ VF_denote a' -> VF_denote b ≤ VF_denote b' ->
  VF_denote (V m a b) ≤ VF_denote (V m' a' b').
Proof.
  intros Hm Ha Hb. simpl.
  transitivity (veblen (ackermann_tower (addOrd 1) (VF_denote m')) (VF_denote a) (VF_denote b)).
  { apply veblen_monotone_func; auto with ord;
      intros; apply ackermann_tower_monotone; auto with ord. }
  transitivity (veblen (ackermann_tower (addOrd 1) (VF_denote m')) (VF_denote a') (VF_denote b)).
  { apply veblen_monotone_first; auto with ord. }
  apply veblen_monotone; auto with ord.
Qed.

(** An upper translation: every [VForm] lies below the denotation of a
    Grimm bracket. *)
Fixpoint vf_up (x:VForm) : T3 :=
  match x with
  | Z => T3zero
  | V m a b =>
      T3psi (match vf_up m with T3zero => t_one | t => t end) (vf_up a) (vf_up b)
  end.

Lemma vf_up_nf : forall x, T3nf (vf_up x) = true.
Proof.
  induction x as [|m Hm a Ha b Hb]; [reflexivity|].
  simpl vf_up. apply T3nf_psi; auto.
  destruct (vf_up m); auto; reflexivity.
Qed.

Lemma vf_up_ge : forall x, VF_denote x ≤ T3_denote (vf_up x).
Proof.
  induction x as [|m Hm a Ha b Hb]; [apply zero_least|].
  simpl vf_up.
  set (am := match vf_up m with T3zero => t_one | t => t end).
  assert (Ham : T3_to_VF am <> Z /\ VF_denote m ≤ 1 + VF_denote (T3_to_VF am)).
  { unfold am. destruct (vf_up m) as [|a1 a2 a3 n1 d1] eqn:Eu.
    - split; [discriminate|].
      transitivity (T3_denote T3zero); [exact Hm | apply zero_least].
    - split; [apply T3_to_VF_cons_nonzero|].
      transitivity (T3_denote (T3cons a1 a2 a3 n1 d1)); [exact Hm | apply addOrd_le2]. }
  destruct Ham as [Hnz Hle].
  rewrite T3_denote_psi_vf.
  destruct (T3_to_VF am) as [|ma aa ba] eqn:Eam; [congruence|].
  change (VF_denote (V m a b) ≤
          VF_denote (V (VF_onePlus (V ma aa ba)) (T3_to_VF (vf_up a))
                       (shift_gen (VF_onePlus (V ma aa ba)) (T3_to_VF (vf_up a)) (T3_to_VF (vf_up b))))).
  apply VF_V_monotone.
  - rewrite VF_onePlus_equal. exact Hle.
  - exact Ha.
  - rewrite Hb. apply shift_gen_bounds.
Qed.

(** The ordinal of Grimm's normal forms. *)
Definition T3ord : Ord := ord { t:T3 | T3nf t = true } (fun t => T3_denote (proj1_sig t)).

(** Grimm's (that is, Ackermann's) normal forms, ordered by [T3lt]
    ([T3lt_correct]), have order type [LargeAckermannOrdinal]. *)
Theorem T3_LAO : T3ord ≈ LargeAckermannOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. intros [t Ht]. simpl.
    apply (VF_below_LAO (T3_to_VF t)).
  - rewrite <- VF_LAO. rewrite ord_le_unfold. intro x. simpl.
    apply ord_le_lt_trans with (T3_denote (vf_up x)); [apply vf_up_ge|].
    apply (index_lt T3ord (exist _ (vf_up x) (vf_up_nf x))).
Qed.
