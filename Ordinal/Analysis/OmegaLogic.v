From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From Ordinal Require Import Notation.VNotation.
From Ordinal Require Import Analysis.PeanoArith.
From Ordinal Require Import Analysis.Hardy.

Local Open Scope nat_scope.

(** * An ω-logic for arithmetic, with bounding by the Hardy functions

    Sequents are lists of signed formulas of [PeanoArith]: [(true, A)]
    asserts [A] and [(false, A)] its negation.  The rules are those of
    Tait's one-sided calculus with the ω-rule, but every derivation
    carries a _control_ [n], and heights are V forms related by
    [β ≺_n α] ([olt], [Hardy]):

    - the ω-rule has its [i]-th premise at control [max n (i+1)];
    - an existential witness must be below the control;
    - the control may be raised, from [n] to [m ≤ H_γ(n)], at the cost
      of adding [γ] to the height ([od_up]).

    Bounded formulas (the class [DP]: equations, the connectives, and
    the bounded quantifiers [∀z ≤ v] and [∃d. u + d = v]) are decided by
    evaluation; a true one is an axiom, and the ω-rule never applies to
    one.  An atom [X t] has no truth value; the identity axiom
    [X t, ¬X t'] with [t] and [t'] of equal value ([od_xax]) is its only
    rule, and a cut on an [X]-atom has rank one.  With these conventions
    the cut elimination of Schütte and Tait goes through, each level of
    cuts costing an exponential [α ↦ ω^α] of the height ([od_elim]).  A
    derivation without cuts of rank
    above zero of a Σ₁ sequent at height [α] and control [n] has
    witnesses below [H_α(n)] ([od_bounding]). *)

(** ** Semantics *)

Fixpoint teval (ρ:nat -> nat) (t:aterm) : nat :=
  match t with
  | tv i => ρ i
  | tz => 0
  | ts t => S (teval ρ t)
  | tplus s t => teval ρ s + teval ρ t
  | tmult s t => teval ρ s * teval ρ t
  end.

Definition scons (x:nat) (ρ:nat -> nat) : nat -> nat :=
  fun i => match i with O => x | S i => ρ i end.

Fixpoint sat (ρ:nat -> nat) (A:form) : Prop :=
  match A with
  | Eq s t => teval ρ s = teval ρ t
  | Bot => False
  | And A B => sat ρ A /\ sat ρ B
  | Or A B => sat ρ A \/ sat ρ B
  | Imp A B => sat ρ A -> sat ρ B
  | All A => forall x, sat (scons x ρ) A
  | Ex A => exists x, sat (scons x ρ) A
  | PX _ => False
  end.

Fixpoint num (n:nat) : aterm :=
  match n with O => tz | S n => ts (num n) end.

Lemma teval_num ρ n : teval ρ (num n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma teval_ext ρ ρ' t : (forall i, ρ i = ρ' i) -> teval ρ t = teval ρ' t.
Proof. intro H. induction t; simpl; auto. Qed.

Lemma sat_ext A : forall ρ ρ', (forall i, ρ i = ρ' i) -> (sat ρ A <-> sat ρ' A).
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u];
    intros ρ ρ' H; simpl.
  - rewrite (teval_ext ρ ρ' s H), (teval_ext ρ ρ' t H). reflexivity.
  - reflexivity.
  - rewrite (IHA ρ ρ' H), (IHB ρ ρ' H). reflexivity.
  - rewrite (IHA ρ ρ' H), (IHB ρ ρ' H). reflexivity.
  - rewrite (IHA ρ ρ' H), (IHB ρ ρ' H). reflexivity.
  - split; intros Hx x; specialize (Hx x); revert Hx; apply IHA; intros [|i]; simpl; auto.
  - split; intros [x Hx]; exists x; revert Hx; apply IHA; intros [|i]; simpl; auto.
  - reflexivity.
Qed.

Lemma teval_asubst ρ σ t : teval ρ (asubst σ t) = teval (fun i => teval ρ (σ i)) t.
Proof. induction t; simpl; auto. Qed.

Lemma teval_shift x ρ t : teval (scons x ρ) (asubst shift_sub t) = teval ρ t.
Proof. rewrite teval_asubst. apply teval_ext. intro i. reflexivity. Qed.

Lemma sat_fsubst A : forall ρ σ, sat ρ (fsubst σ A) <-> sat (fun i => teval ρ (σ i)) A.
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u];
    intros ρ σ; simpl.
  - rewrite !teval_asubst. reflexivity.
  - reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - split; intros Hx x; specialize (Hx x); revert Hx.
    + rewrite IHA. apply sat_ext. intros [|i]; simpl; [reflexivity | first [apply teval_shift | symmetry; apply teval_shift]].
    + rewrite IHA. apply sat_ext. intros [|i]; simpl; [reflexivity | first [apply teval_shift | symmetry; apply teval_shift]].
  - split; intros [x Hx]; exists x; revert Hx.
    + rewrite IHA. apply sat_ext. intros [|i]; simpl; [reflexivity | first [apply teval_shift | symmetry; apply teval_shift]].
    + rewrite IHA. apply sat_ext. intros [|i]; simpl; [reflexivity | first [apply teval_shift | symmetry; apply teval_shift]].
  - reflexivity.
Qed.

Lemma sat_sub1 ρ A t : sat ρ (sub1 A t) <-> sat (scons (teval ρ t) ρ) A.
Proof.
  unfold sub1. rewrite sat_fsubst. apply sat_ext. intros [|i]; reflexivity.
Qed.

Lemma sat_sub1_num ρ A i : sat ρ (sub1 A (num i)) <-> sat (scons i ρ) A.
Proof. rewrite sat_sub1, teval_num. reflexivity. Qed.

(** Closed formulas are evaluated with all variables [0]. *)
Definition ρ0 : nat -> nat := fun _ => 0.

(** ** Bounded formulas *)

Fixpoint occ (k:nat) (t:aterm) : bool :=
  match t with
  | tv i => Nat.eqb i k
  | tz => false
  | ts t => occ k t
  | tplus s t | tmult s t => occ k s || occ k t
  end.

(** [∀z ≤ v. B] is [∀z. (∃d. z + d = v) → B], and [∃d. u + d = v]
    states [u ≤ v]. *)
Inductive DP : form -> Prop :=
| DP_eq s t : DP (Eq s t)
| DP_bot : DP Bot
| DP_and A B : DP A -> DP B -> DP (And A B)
| DP_or A B : DP A -> DP B -> DP (Or A B)
| DP_imp A B : DP A -> DP B -> DP (Imp A B)
| DP_ball v B : occ 0 v = false -> occ 1 v = false -> DP B ->
    DP (All (Imp (Ex (Eq (tplus (tv 1) (tv 0)) v)) B))
| DP_bex u v : occ 0 u = false -> occ 0 v = false -> DP (Ex (Eq (tplus u (tv 0)) v)).

Fixpoint isD (A:form) : bool :=
  match A with
  | Eq _ _ => true
  | Bot => true
  | And A B | Or A B | Imp A B => isD A && isD B
  | All (Imp (Ex (Eq (tplus (tv 1) (tv 0)) v)) B) => negb (occ 0 v) && negb (occ 1 v) && isD B
  | Ex (Eq (tplus u (tv 0)) v) => negb (occ 0 u) && negb (occ 0 v)
  | _ => false
  end.

Lemma DP_isD A : DP A -> isD A = true.
Proof.
  induction 1; simpl; auto.
  - rewrite IHDP1, IHDP2. reflexivity.
  - rewrite IHDP1, IHDP2. reflexivity.
  - rewrite IHDP1, IHDP2. reflexivity.
  - rewrite H, H0, IHDP. reflexivity.
  - rewrite H, H0. reflexivity.
Qed.

Lemma isD_DP : forall A, isD A = true -> DP A.
Proof.
  fix IH 1. intros A H.
  destruct A as [s t| |A B|A B|A B|A|A|u].
  - constructor.
  - constructor.
  - simpl in H. apply andb_prop in H as [H1 H2]. constructor; [apply IH; exact H1 | apply IH; exact H2].
  - simpl in H. apply andb_prop in H as [H1 H2]. constructor; [apply IH; exact H1 | apply IH; exact H2].
  - simpl in H. apply andb_prop in H as [H1 H2]. constructor; [apply IH; exact H1 | apply IH; exact H2].
  - destruct A as [| | | |G B| | |]; try discriminate.
    destruct G as [| | | | | |E|]; try discriminate.
    destruct E as [w v| | | | | | |]; try discriminate.
    destruct w as [| | |a b|]; try discriminate.
    destruct a as [[|[|i]]| | | |]; try discriminate.
    destruct b as [[|i]| | | |]; try discriminate.
    simpl in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply negb_true_iff in H1. apply negb_true_iff in H2.
    constructor; [exact H1 | exact H2 | apply IH; exact H3].
  - destruct A as [w v| | | | | | |]; try discriminate.
    destruct w as [| | |u b|]; try discriminate.
    destruct b as [[|i]| | | |]; try discriminate.
    simpl in H. apply andb_prop in H as [H1 H2].
    apply negb_true_iff in H1. apply negb_true_iff in H2.
    constructor; assumption.
  - discriminate.
Qed.

Lemma occ_asubst k τ t : occ k (asubst τ t) = true -> exists i, occ i t = true /\ occ k (τ i) = true.
Proof.
  induction t as [i| |t IH|s IHs t IHt|s IHs t IHt]; simpl; intro H.
  - exists i. rewrite Nat.eqb_refl. split; [reflexivity | exact H].
  - discriminate.
  - apply IH. exact H.
  - apply orb_prop in H as [H|H].
    + destruct (IHs H) as [i [H1 H2]]. exists i. rewrite H1. split; [reflexivity | exact H2].
    + destruct (IHt H) as [i [H1 H2]]. exists i. rewrite H1, orb_true_r. split; [reflexivity | exact H2].
  - apply orb_prop in H as [H|H].
    + destruct (IHs H) as [i [H1 H2]]. exists i. rewrite H1. split; [reflexivity | exact H2].
    + destruct (IHt H) as [i [H1 H2]]. exists i. rewrite H1, orb_true_r. split; [reflexivity | exact H2].
Qed.

Lemma occ_shift k t : occ k (asubst shift_sub t) = match k with O => false | S k => occ k t end.
Proof.
  induction t as [i| |t IH|s IHs t IHt|s IHs t IHt]; simpl.
  - destruct k; [reflexivity|]. reflexivity.
  - destruct k; reflexivity.
  - exact IH.
  - rewrite IHs, IHt. destruct k; reflexivity.
  - rewrite IHs, IHt. destruct k; reflexivity.
Qed.

Lemma occ_up0 σ t : occ 0 t = false -> occ 0 (asubst (up σ) t) = false.
Proof.
  intro H. destruct (occ 0 (asubst (up σ) t)) eqn:E; [|reflexivity].
  destruct (occ_asubst _ _ _ E) as [[|i] [H1 H2]].
  - rewrite H in H1. discriminate.
  - simpl in H2. rewrite occ_shift in H2. discriminate.
Qed.

Lemma occ_up1 σ t : occ 0 t = false -> occ 1 t = false -> occ 1 (asubst (up (up σ)) t) = false.
Proof.
  intros H0 H1. destruct (occ 1 (asubst (up (up σ)) t)) eqn:E; [|reflexivity].
  destruct (occ_asubst _ _ _ E) as [[|[|i]] [H2 H3]].
  - rewrite H0 in H2. discriminate.
  - rewrite H1 in H2. discriminate.
  - simpl in H3. rewrite occ_shift, occ_shift in H3. discriminate.
Qed.

Lemma DP_fsubst A : DP A -> forall σ, DP (fsubst σ A).
Proof.
  induction 1 as [s t| |A B _ IHA _ IHB|A B _ IHA _ IHB|A B _ IHA _ IHB|v B Hv0 Hv1 _ IHB|u v Hu Hv];
    intro σ; simpl.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; [apply occ_up0; exact Hv0 | apply occ_up1; assumption | apply IHB].
  - constructor; apply occ_up0; assumption.
Qed.

Lemma isD_fsubst A σ : isD A = true -> isD (fsubst σ A) = true.
Proof. intro H. apply DP_isD. apply DP_fsubst. apply isD_DP. exact H. Qed.

(** ** Deciding bounded formulas *)

Fixpoint fall (b:nat) (f:nat -> bool) : bool :=
  match b with O => f 0 | S b => fall b f && f (S b) end.

Lemma fall_spec b f : fall b f = true <-> forall z, z <= b -> f z = true.
Proof.
  induction b as [|b IH]; simpl.
  - split; [intros H z Hz; replace z with 0 by lia; exact H | intro H; apply H; lia].
  - rewrite andb_true_iff, IH. split.
    + intros [H1 H2] z Hz. destruct (Nat.eq_dec z (S b)) as [->|Hne]; [exact H2 | apply H1; lia].
    + intro H. split; [intros z Hz; apply H; lia | apply H; lia].
Qed.

Fixpoint deval (ρ:nat -> nat) (A:form) : bool :=
  match A with
  | Eq s t => Nat.eqb (teval ρ s) (teval ρ t)
  | Bot => false
  | And A B => deval ρ A && deval ρ B
  | Or A B => deval ρ A || deval ρ B
  | Imp A B => implb (deval ρ A) (deval ρ B)
  | All (Imp (Ex (Eq (tplus (tv 1) (tv 0)) v)) B) =>
      fall (teval (scons 0 (scons 0 ρ)) v) (fun z => deval (scons z ρ) B)
  | Ex (Eq (tplus u (tv 0)) v) => Nat.leb (teval (scons 0 ρ) u) (teval (scons 0 ρ) v)
  | _ => false
  end.

Lemma teval_occ ρ ρ' t : (forall i, occ i t = true -> ρ i = ρ' i) -> teval ρ t = teval ρ' t.
Proof.
  induction t as [i| |t IH|s IHs t IHt|s IHs t IHt]; simpl; intro H.
  - apply H. simpl. apply Nat.eqb_refl.
  - reflexivity.
  - f_equal. apply IH. exact H.
  - f_equal; [apply IHs | apply IHt]; intros i Hi; apply H; simpl; rewrite Hi; [reflexivity | apply orb_true_r].
  - f_equal; [apply IHs | apply IHt]; intros i Hi; apply H; simpl; rewrite Hi; [reflexivity | apply orb_true_r].
Qed.

Lemma deval_correct A : DP A -> forall ρ, deval ρ A = true <-> sat ρ A.
Proof.
  induction 1 as [s t| |A B _ IHA _ IHB|A B _ IHA _ IHB|A B _ IHA _ IHB|v B Hv0 Hv1 _ IHB|u v Hu Hv];
    intro ρ; simpl.
  - apply Nat.eqb_eq.
  - split; [discriminate | contradiction].
  - rewrite andb_true_iff, IHA, IHB. reflexivity.
  - rewrite orb_true_iff, IHA, IHB. reflexivity.
  - rewrite <- IHA, <- IHB. destruct (deval ρ A), (deval ρ B); simpl; intuition discriminate.
  - rewrite fall_spec.
    assert (Ev : forall x d, teval (scons d (scons x ρ)) v = teval (scons 0 (scons 0 ρ)) v).
    { intros x d. apply teval_occ. intros [|[|i]] Hi; simpl; auto.
      - rewrite Hv0 in Hi. discriminate.
      - rewrite Hv1 in Hi. discriminate. }
    split.
    + intros H x [d Hd]. apply IHB. apply H. simpl in Hd. rewrite (Ev x d) in Hd. lia.
    + intros H z Hz. apply IHB. apply H. exists (teval (scons 0 (scons 0 ρ)) v - z).
      simpl. rewrite (Ev z). lia.
  - assert (Eu : forall d, teval (scons d ρ) u = teval (scons 0 ρ) u).
    { intro d. apply teval_occ. intros [|i] Hi; simpl; auto. rewrite Hu in Hi. discriminate. }
    assert (Ev : forall d, teval (scons d ρ) v = teval (scons 0 ρ) v).
    { intro d. apply teval_occ. intros [|i] Hi; simpl; auto. rewrite Hv in Hi. discriminate. }
    rewrite Nat.leb_le. split.
    + intro H. exists (teval (scons 0 ρ) v - teval (scons 0 ρ) u).
      simpl. rewrite (Eu (teval (scons 0 ρ) v - teval (scons 0 ρ) u)).
      rewrite (Ev (teval (scons 0 ρ) v - teval (scons 0 ρ) u)). lia.
    + intros [d Hd]. simpl in Hd. rewrite (Eu d), (Ev d) in Hd. lia.
Qed.

Lemma deval_sat A : isD A = true -> forall ρ, deval ρ A = true <-> sat ρ A.
Proof. intro H. apply deval_correct. apply isD_DP. exact H. Qed.

Lemma deval_false A ρ : isD A = true -> deval ρ A = false <-> ~ sat ρ A.
Proof.
  intro H. rewrite <- (deval_sat A H ρ). destruct (deval ρ A); split; intro; try discriminate; auto.
  exfalso; auto.
Qed.

(** ** Signed formulas *)

Definition sform : Type := (bool * form)%type.

Definition sneg (s:sform) : sform := (negb (fst s), snd s).

Lemma sneg_sneg s : sneg (sneg s) = s.
Proof. destruct s as [b A]. unfold sneg. simpl. rewrite negb_involutive. reflexivity. Qed.

(** A true bounded formula, and a false one. *)
Definition dax (s:sform) : Prop := isD (snd s) = true /\ deval ρ0 (snd s) = fst s.
Definition dfalse (s:sform) : Prop := isD (snd s) = true /\ deval ρ0 (snd s) = negb (fst s).

Lemma dfalse_sneg s : dfalse s <-> dax (sneg s).
Proof.
  destruct s as [b A]. unfold dfalse, dax, sneg. simpl. reflexivity.
Qed.

Lemma dax_dec s : isD (snd s) = true -> dax s \/ dfalse s.
Proof.
  destruct s as [b A]. unfold dax, dfalse. simpl. intro H.
  destruct b, (deval ρ0 A); auto.
Qed.

Definition inst (b:bool) (A:form) (i:nat) : sform := (b, sub1 A (num i)).

Inductive kind : Type :=
| KAtom : kind
| KConj : sform -> sform -> kind
| KDisj : sform -> sform -> kind
| KUniv : bool -> form -> kind
| KExis : bool -> form -> kind.

Definition kindof (s:sform) : kind :=
  match s with
  | (true, And A B) => KConj (true, A) (true, B)
  | (false, Or A B) => KConj (false, A) (false, B)
  | (false, Imp A B) => KConj (true, A) (false, B)
  | (true, Or A B) => KDisj (true, A) (true, B)
  | (false, And A B) => KDisj (false, A) (false, B)
  | (true, Imp A B) => KDisj (false, A) (true, B)
  | (true, All A) => KUniv true A
  | (false, Ex A) => KUniv false A
  | (true, Ex A) => KExis true A
  | (false, All A) => KExis false A
  | _ => KAtom
  end.

Lemma kind_conj_neg s s1 s2 : kindof s = KConj s1 s2 -> kindof (sneg s) = KDisj (sneg s1) (sneg s2).
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intro H; try discriminate;
    injection H; intros; subst; reflexivity.
Qed.

Lemma kind_disj_neg s s1 s2 : kindof s = KDisj s1 s2 -> kindof (sneg s) = KConj (sneg s1) (sneg s2).
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intro H; try discriminate;
    injection H; intros; subst; reflexivity.
Qed.

Lemma kind_univ_neg s b A : kindof s = KUniv b A -> kindof (sneg s) = KExis (negb b) A.
Proof.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intro H; try discriminate;
    injection H; intros; subst; reflexivity.
Qed.

Lemma kind_exis_neg s b A : kindof s = KExis b A -> kindof (sneg s) = KUniv (negb b) A.
Proof.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intro H; try discriminate;
    injection H; intros; subst; reflexivity.
Qed.

Lemma inst_sneg b A i : sneg (inst b A i) = inst (negb b) A i.
Proof. reflexivity. Qed.

(** Bounded formulas are closed under their components. *)
Lemma isD_conj s s1 s2 : kindof s = KConj s1 s2 -> isD (snd s) = true ->
  isD (snd s1) = true /\ isD (snd s2) = true.
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intros H HD; try discriminate;
    injection H; intros; subst; simpl; apply andb_prop; exact HD.
Qed.

Lemma isD_disj s s1 s2 : kindof s = KDisj s1 s2 -> isD (snd s) = true ->
  isD (snd s1) = true /\ isD (snd s2) = true.
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intros H HD; try discriminate;
    injection H; intros; subst; simpl; apply andb_prop; exact HD.
Qed.

Lemma isD_quant_inst A t : (isD (All A) = true \/ isD (Ex A) = true) -> isD (sub1 A t) = true.
Proof.
  intros [H|H]; apply isD_DP in H; inversion H; subst; apply DP_isD.
  - unfold sub1. simpl. constructor.
    + apply DP_bex; [|apply occ_up0; assumption].
      rewrite occ_shift. reflexivity.
    + apply DP_fsubst. assumption.
  - unfold sub1. simpl. constructor.
Qed.

Lemma occ_asubst_back k τ t i : occ i t = true -> occ k (τ i) = true -> occ k (asubst τ t) = true.
Proof.
  induction t as [j| |t IH|s IHs t IHt|s IHs t IHt]; simpl; intros H1 H2.
  - apply Nat.eqb_eq in H1. subst. exact H2.
  - discriminate.
  - apply IH; assumption.
  - apply orb_prop in H1 as [H1|H1]; [rewrite (IHs H1 H2) | rewrite (IHt H1 H2), orb_true_r]; reflexivity.
  - apply orb_prop in H1 as [H1|H1]; [rewrite (IHs H1 H2) | rewrite (IHt H1 H2), orb_true_r]; reflexivity.
Qed.

Lemma shift_not_tv0 t : asubst shift_sub t <> tv 0.
Proof. destruct t; simpl; discriminate. Qed.

Lemma up_tv0 σ w : asubst (up σ) w = tv 0 -> w = tv 0.
Proof.
  destruct w as [[|i]| | | |]; simpl; intro H; try discriminate; auto.
  exfalso. exact (shift_not_tv0 _ H).
Qed.

Lemma upup_tv1 σ w : asubst (up (up σ)) w = tv 1 -> w = tv 1.
Proof.
  destruct w as [[|[|i]]| | | |]; simpl; intro H; try discriminate; auto.
  exfalso. destruct (σ i) as [[|j]| | | |]; simpl in H; discriminate.
Qed.

Lemma occ_up0_back σ t : occ 0 (asubst (up σ) t) = false -> occ 0 t = false.
Proof.
  intro H. destruct (occ 0 t) eqn:E; [|reflexivity].
  rewrite (occ_asubst_back 0 (up σ) t 0 E eq_refl) in H. discriminate.
Qed.

Lemma occ_up1_back σ t : occ 1 (asubst (up (up σ)) t) = false -> occ 1 t = false.
Proof.
  intro H. destruct (occ 1 t) eqn:E; [|reflexivity].
  rewrite (occ_asubst_back 1 (up (up σ)) t 1 E eq_refl) in H. discriminate.
Qed.

Lemma upup_pat σ w : asubst (up (up σ)) w = tplus (tv 1) (tv 0) -> w = tplus (tv 1) (tv 0).
Proof.
  destruct w as [[|[|i]]| | |a b|]; simpl; intro H; try discriminate.
  - destruct (σ i) as [| | |x y|]; simpl in H; try discriminate.
    injection H as _ H. destruct y as [[|j]| | | |]; simpl in H; discriminate.
  - injection H as Ha Hb. apply upup_tv1 in Ha. apply up_tv0 in Hb. subst. reflexivity.
Qed.

Lemma up_pat σ w u' : asubst (up σ) w = tplus u' (tv 0) -> exists u, w = tplus u (tv 0).
Proof.
  destruct w as [[|i]| | |a b|]; simpl; intro H; try discriminate.
  - destruct (σ i) as [| | |x y|]; simpl in H; try discriminate.
    injection H as _ H. exfalso. exact (shift_not_tv0 _ H).
  - injection H as _ Hb. apply up_tv0 in Hb. subst. exists a. reflexivity.
Qed.

Lemma isD_fsubst_back : forall A σ, isD (fsubst σ A) = true -> isD A = true.
Proof.
  fix IH 1. intros A σ H.
  destruct A as [s t| |A B|A B|A B|A|A|u].
  - reflexivity.
  - reflexivity.
  - simpl in *. apply andb_prop in H as [H1 H2]. rewrite (IH A σ H1), (IH B σ H2). reflexivity.
  - simpl in *. apply andb_prop in H as [H1 H2]. rewrite (IH A σ H1), (IH B σ H2). reflexivity.
  - simpl in *. apply andb_prop in H as [H1 H2]. rewrite (IH A σ H1), (IH B σ H2). reflexivity.
  - destruct A as [| | | |G B| | |]; try discriminate.
    destruct G as [| | | | | |E|]; try discriminate.
    destruct E as [w v| | | | | | |]; try discriminate.
    simpl in H.
    destruct (asubst (up (up σ)) w) as [| | |a b|] eqn:Ew; try discriminate.
    destruct a as [[|[|i]]| | | |]; try discriminate.
    destruct b as [[|i]| | | |]; try discriminate.
    apply upup_pat in Ew. subst w.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply negb_true_iff in H1. apply negb_true_iff in H2.
    simpl. rewrite (occ_up0_back _ _ H1), (occ_up1_back _ _ H2), (IH B (up σ) H3). reflexivity.
  - destruct A as [w v| | | | | | |]; try discriminate.
    simpl in H.
    destruct (asubst (up σ) w) as [| | |a b|] eqn:Ew; try discriminate.
    destruct b as [[|i]| | | |]; try discriminate.
    destruct (up_pat σ w a Ew) as [u ->].
    simpl in Ew. injection Ew as Ea. subst a.
    apply andb_prop in H as [H1 H2].
    apply negb_true_iff in H1. apply negb_true_iff in H2.
    simpl. rewrite (occ_up0_back _ _ H1), (occ_up0_back _ _ H2). reflexivity.
  - discriminate.
Qed.

Lemma isD_fsubst_eq A σ : isD (fsubst σ A) = isD A.
Proof.
  destruct (isD A) eqn:E.
  - apply isD_fsubst. exact E.
  - destruct (isD (fsubst σ A)) eqn:E'; [|reflexivity].
    rewrite (isD_fsubst_back A σ E') in E. discriminate.
Qed.

Lemma deval_fsubst A σ ρ : isD A = true ->
  deval ρ (fsubst σ A) = deval (fun i => teval ρ (σ i)) A.
Proof.
  intro H. assert (H' := isD_fsubst A σ H).
  destruct (deval (fun i => teval ρ (σ i)) A) eqn:E.
  - apply deval_sat; [exact H'|]. apply sat_fsubst. apply deval_sat; assumption.
  - apply deval_false; [exact H'|]. rewrite sat_fsubst. apply deval_false; assumption.
Qed.

Lemma deval_ext A ρ ρ' : isD A = true -> (forall i, ρ i = ρ' i) -> deval ρ A = deval ρ' A.
Proof.
  intros H E. destruct (deval ρ' A) eqn:E'.
  - apply deval_sat; [exact H|]. rewrite (sat_ext A ρ ρ' E). apply deval_sat; assumption.
  - apply deval_false; [exact H|]. rewrite (sat_ext A ρ ρ' E). apply deval_false; assumption.
Qed.

Lemma deval_sub1 A ρ i : isD A = true -> deval ρ (sub1 A (num i)) = deval (scons i ρ) A.
Proof.
  intro H. unfold sub1. rewrite deval_fsubst by exact H. apply deval_ext; [exact H|].
  intros [|j]; simpl; [apply teval_num | reflexivity].
Qed.

(** ** Ranks *)

Fixpoint rank (A:form) : nat :=
  if isD A then 0 else
  match A with
  | And A B | Or A B | Imp A B => S (Nat.max (rank A) (rank B))
  | All A | Ex A => S (rank A)
  | PX _ => 1
  | _ => 0
  end.

Lemma rank_D A : isD A = true -> rank A = 0.
Proof. intro H. destruct A; cbn [rank]; try rewrite H; try reflexivity; discriminate. Qed.

Lemma rank_0_D A : rank A = 0 -> isD A = true.
Proof.
  intro H. destruct (isD A) eqn:E; [reflexivity|].
  destruct A; cbn [rank] in H; rewrite E in H; try discriminate; simpl in E; discriminate.
Qed.

Lemma rank_fsubst A : forall σ, rank (fsubst σ A) = rank A.
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u]; intro σ.
  - assert (E := isD_fsubst_eq (Eq s t) σ). cbn [fsubst] in E |- *. cbn [rank]. try rewrite E. reflexivity.
  - assert (E := isD_fsubst_eq (Bot) σ). cbn [fsubst] in E |- *. cbn [rank]. try rewrite E. reflexivity.
  - assert (E := isD_fsubst_eq (And A B) σ). cbn [fsubst] in E |- *. cbn [rank]. try rewrite E. rewrite IHA, IHB. reflexivity.
  - assert (E := isD_fsubst_eq (Or A B) σ). cbn [fsubst] in E |- *. cbn [rank]. try rewrite E. rewrite IHA, IHB. reflexivity.
  - assert (E := isD_fsubst_eq (Imp A B) σ). cbn [fsubst] in E |- *. cbn [rank]. try rewrite E. rewrite IHA, IHB. reflexivity.
  - assert (E := isD_fsubst_eq (All A) σ). cbn [fsubst] in E |- *. cbn [rank]. try rewrite E. rewrite IHA. reflexivity.
  - assert (E := isD_fsubst_eq (Ex A) σ). cbn [fsubst] in E |- *. cbn [rank]. try rewrite E. rewrite IHA. reflexivity.
  - reflexivity.
Qed.

Lemma rank_conj s s1 s2 : kindof s = KConj s1 s2 -> isD (snd s) = false ->
  rank (snd s1) < rank (snd s) /\ rank (snd s2) < rank (snd s).
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intros H HD; try discriminate;
    injection H; intros; subst; simpl; rewrite HD; lia.
Qed.

Lemma rank_disj s s1 s2 : kindof s = KDisj s1 s2 -> isD (snd s) = false ->
  rank (snd s1) < rank (snd s) /\ rank (snd s2) < rank (snd s).
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intros H HD; try discriminate;
    injection H; intros; subst; simpl; rewrite HD; lia.
Qed.

Lemma rank_univ s b A i : kindof s = KUniv b A -> isD (snd s) = false ->
  rank (snd (inst b A i)) < rank (snd s).
Proof.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intros H HD; try discriminate;
    injection H; intros; subst; unfold sub1; rewrite rank_fsubst; simpl; rewrite HD; lia.
Qed.

Lemma rank_exis s b A i : kindof s = KExis b A -> isD (snd s) = false ->
  rank (snd (inst b A i)) < rank (snd s).
Proof.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intros H HD; try discriminate;
    injection H; intros; subst; unfold sub1; rewrite rank_fsubst; simpl; rewrite HD; lia.
Qed.

(** An atom is a bounded formula or an [X]-atom. *)
Lemma kind_atom_D s : kindof s = KAtom -> isD (snd s) = true \/ exists u, snd s = PX u.
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intro H; try discriminate; eauto.
Qed.

Lemma kind_PX b u : kindof (b, PX u) = KAtom.
Proof. destruct b; reflexivity. Qed.

(** ** False bounded formulas have false components *)

Lemma dfalse_conj s s1 s2 : kindof s = KConj s1 s2 -> dfalse s -> dfalse s1 \/ dfalse s2.
Proof.
  intros Hk [HD Hv]. destruct (isD_conj s s1 s2 Hk HD) as [H1 H2].
  revert Hk HD Hv H1 H2. unfold dfalse.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intros Hk HD Hv H1 H2; try discriminate;
    injection Hk; intros; subst; simpl in *.
  - destruct (deval ρ0 A); simpl in Hv; auto.
  - destruct (deval ρ0 A); simpl in Hv; auto.
  - destruct (deval ρ0 A); simpl in Hv; auto.
Qed.

Lemma dfalse_disj s s1 s2 : kindof s = KDisj s1 s2 -> dfalse s -> dfalse s1 /\ dfalse s2.
Proof.
  intros Hk [HD Hv]. destruct (isD_disj s s1 s2 Hk HD) as [H1 H2].
  revert Hk HD Hv H1 H2. unfold dfalse.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intros Hk HD Hv H1 H2; try discriminate;
    injection Hk; intros; subst; simpl in *.
  - destruct (deval ρ0 A), (deval ρ0 B); simpl in Hv; try discriminate; auto.
  - destruct (deval ρ0 A), (deval ρ0 B); simpl in Hv; try discriminate; auto.
  - destruct (deval ρ0 A), (deval ρ0 B); simpl in Hv; try discriminate; auto.
Qed.

Lemma dfalse_exis s b A i : kindof s = KExis b A -> dfalse s -> dfalse (inst b A i).
Proof.
  unfold dfalse, inst.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intros Hk [HD Hv]; try discriminate;
    injection Hk; intros; subst; simpl.
  - assert (Hi : isD (sub1 A (num i)) = true) by (apply isD_quant_inst; right; exact HD).
    split; [exact Hi|]. apply deval_false; [exact Hi|].
    intro Hs. apply (deval_false (Ex A) ρ0 HD) in Hv. apply Hv.
    exists i. apply sat_sub1_num. exact Hs.
  - assert (Hi : isD (sub1 A (num i)) = true) by (apply isD_quant_inst; left; exact HD).
    split; [exact Hi|]. apply deval_sat; [exact Hi|].
    apply (deval_sat (All A) HD ρ0) in Hv. apply sat_sub1_num. apply Hv.
Qed.

Lemma dax_not_dfalse s : dax s -> dfalse s -> False.
Proof.
  intros [_ H1] [_ H2]. rewrite H1 in H2. destruct (fst s); discriminate.
Qed.

(** ** Derivations

    [OD n ρ α Γ]: the sequent [Γ] is derivable at control [n] with height
    [α], using cuts on formulas of rank below [ρ] only.  Principal
    formulas stay in the premises, so contraction is built in. *)

Inductive OD : nat -> nat -> VForm -> list sform -> Prop :=
| od_ax n ρ α Γ s :
    In s Γ -> dax s -> OD n ρ α Γ
| od_xax n ρ α Γ u v :
    In (true, PX u) Γ -> In (false, PX v) Γ -> teval ρ0 u = teval ρ0 v -> OD n ρ α Γ
| od_conj n ρ α β Γ s s1 s2 :
    In s Γ -> kindof s = KConj s1 s2 ->
    OD n ρ β (s1 :: Γ) -> OD n ρ β (s2 :: Γ) -> olt n β α -> OD n ρ α Γ
| od_disj n ρ α β Γ s s1 s2 s' :
    In s Γ -> kindof s = KDisj s1 s2 -> (s' = s1 \/ s' = s2) ->
    OD n ρ β (s' :: Γ) -> olt n β α -> OD n ρ α Γ
| od_univ n ρ α (β:nat -> VForm) Γ s b A :
    In s Γ -> kindof s = KUniv b A -> isD (snd s) = false ->
    (forall i, OD (Nat.max n (S i)) ρ (β i) (inst b A i :: Γ)) ->
    (forall i, olt (Nat.max n (S i)) (β i) α) -> OD n ρ α Γ
| od_exis n ρ α β Γ s b A m :
    In s Γ -> kindof s = KExis b A -> m < n ->
    OD n ρ β (inst b A m :: Γ) -> olt n β α -> OD n ρ α Γ
| od_cut n ρ α β Γ s :
    rank (snd s) < ρ -> OD n ρ β (s :: Γ) -> OD n ρ β (sneg s :: Γ) -> olt n β α -> OD n ρ α Γ
| od_up n m ρ α β γ h Γ :
    n <= m -> OD m ρ β Γ -> hardy γ n h -> m <= h -> olt n (vcat β γ) α -> OD n ρ α Γ.

(** [Γ ⊑ Γ']: every formula of [Γ] is in [Γ'] or is a false bounded
    formula. *)
Definition sub_mod (Γ Γ':list sform) : Prop := forall s, In s Γ -> In s Γ' \/ dfalse s.

Lemma sub_mod_cons s Γ Γ' : sub_mod Γ Γ' -> sub_mod (s :: Γ) (s :: Γ').
Proof. intros H x [<-|Hx]; [left; left; reflexivity | destruct (H x Hx); [left; right|right]; auto]. Qed.

Lemma sub_mod_drop s Γ Γ' : dfalse s -> sub_mod Γ Γ' -> sub_mod (s :: Γ) Γ'.
Proof. intros Hs H x [<-|Hx]; [right; exact Hs | apply H; exact Hx]. Qed.

Lemma sub_mod_incl Γ Γ' : incl Γ Γ' -> sub_mod Γ Γ'.
Proof. intros H x Hx. left. apply H. exact Hx. Qed.

(** Weakening, raising the control, the cut rank and the height, and
    deleting false bounded formulas. *)
Theorem od_struct n ρ α Γ : OD n ρ α Γ ->
  forall n' ρ' α' Γ', n <= n' -> ρ <= ρ' -> reach n α α' -> sub_mod Γ Γ' -> OD n' ρ' α' Γ'.
Proof.
  induction 1 as [n ρ α Γ s Hs Hax
                 |n ρ α Γ u v Hu Hv Huv
                 |n ρ α β Γ s s1 s2 Hs Hk _ IH1 _ IH2 Hlt
                 |n ρ α β Γ s s1 s2 s' Hs Hk Hs' _ IH Hlt
                 |n ρ α β Γ s b A Hs Hk HD _ IH Hlt
                 |n ρ α β Γ s b A m Hs Hk Hm _ IH Hlt
                 |n ρ α β Γ s Hr _ IH1 _ IH2 Hlt
                 |n m ρ α β γ h Γ Hnm _ IH Hh Hmh Hlt];
    intros n' ρ' α' Γ' Hn Hρ Hα HΓ.
  - destruct (HΓ s Hs) as [Hs'|Hf]; [|exfalso; exact (dax_not_dfalse s Hax Hf)].
    apply od_ax with s; assumption.
  - apply od_xax with u v; [| |exact Huv].
    + destruct (HΓ _ Hu) as [H|[H _]]; [exact H | discriminate].
    + destruct (HΓ _ Hv) as [H|[H _]]; [exact H | discriminate].
  - assert (Hβ : reach n β α') by (eapply reach_trans; [apply olt_reach; exact Hlt | exact Hα]).
    destruct (HΓ s Hs) as [Hs'|Hf].
    + apply od_conj with β s s1 s2; auto.
      * apply IH1; auto using reach_refl, sub_mod_cons.
      * apply IH2; auto using reach_refl, sub_mod_cons.
      * apply olt_mono with n; [exact Hn|]. apply olt_reach_trans with α; assumption.
    + destruct (dfalse_conj s s1 s2 Hk Hf) as [H|H].
      * apply IH1; auto. apply sub_mod_drop; assumption.
      * apply IH2; auto. apply sub_mod_drop; assumption.
  - assert (Hβ : reach n β α') by (eapply reach_trans; [apply olt_reach; exact Hlt | exact Hα]).
    destruct (HΓ s Hs) as [Hs''|Hf].
    + apply od_disj with β s s1 s2 s'; auto.
      * apply IH; auto using reach_refl, sub_mod_cons.
      * apply olt_mono with n; [exact Hn|]. apply olt_reach_trans with α; assumption.
    + destruct (dfalse_disj s s1 s2 Hk Hf) as [H1 H2].
      apply IH; auto. apply sub_mod_drop; [destruct Hs' as [->| ->]; assumption | exact HΓ].
  - destruct (HΓ s Hs) as [Hs'|Hf]; [|exfalso; destruct Hf as [Hf _]; rewrite Hf in HD; discriminate].
    apply od_univ with β s b A; auto.
    + intro i. apply (IH i); auto using reach_refl, sub_mod_cons. lia.
    + intro i. apply olt_mono with (Nat.max n (S i)); [lia|].
      apply olt_reach_trans with α; [apply Hlt|]. apply reach_mono with n; [lia | exact Hα].
  - assert (Hβ : reach n β α') by (eapply reach_trans; [apply olt_reach; exact Hlt | exact Hα]).
    destruct (HΓ s Hs) as [Hs'|Hf].
    + apply od_exis with β s b A m; auto; [lia| |].
      * apply IH; auto using reach_refl, sub_mod_cons.
      * apply olt_mono with n; [exact Hn|]. apply olt_reach_trans with α; assumption.
    + apply IH; auto. apply sub_mod_drop; [apply dfalse_exis with s; assumption | exact HΓ].
  - apply od_cut with β s; [lia| | |].
    + apply IH1; auto using reach_refl, sub_mod_cons.
    + apply IH2; auto using reach_refl, sub_mod_cons.
    + apply olt_mono with n; [exact Hn|]. apply olt_reach_trans with α; assumption.
  - destruct (hardy_exists γ n') as [h' Hh'].
    assert (Hhh : h <= h') by (apply (hardy_mono_arg γ n n'); assumption).
    apply od_up with (Nat.max m n') β γ h'; [lia| |exact Hh'| |].
    + apply IH; auto using reach_refl. lia.
    + apply Nat.max_lub; [lia|]. eapply hardy_ge. exact Hh'.
    + apply olt_mono with n; [exact Hn|]. apply olt_reach_trans with α; assumption.
Qed.

Lemma od_weaken n ρ α Γ Γ' : OD n ρ α Γ -> incl Γ Γ' -> OD n ρ α Γ'.
Proof. intros H Hi. eapply od_struct; eauto using reach_refl, sub_mod_incl. Qed.

Lemma od_height n ρ α α' Γ : OD n ρ α Γ -> reach n α α' -> OD n ρ α' Γ.
Proof. intros H Hr. eapply od_struct; eauto. intros x Hx. left. exact Hx. Qed.

Lemma od_control n n' ρ α Γ : OD n ρ α Γ -> n <= n' -> OD n' ρ α Γ.
Proof. intros H Hn. eapply od_struct; eauto using reach_refl. intros x Hx. left. exact Hx. Qed.

Lemma od_rank n ρ ρ' α Γ : OD n ρ α Γ -> ρ <= ρ' -> OD n ρ' α Γ.
Proof. intros H Hρ. eapply od_struct; eauto using reach_refl. intros x Hx. left. exact Hx. Qed.

(** ** Inversion *)

Lemma sub_rem_cons (x s:sform) (Γ Δ:list sform) : (forall y, In y Δ -> y = s \/ In y Γ) ->
  forall y, In y (x :: Δ) -> y = s \/ In y (x :: Γ).
Proof. intros H y [<-|Hy]; [right; left; reflexivity | destruct (H y Hy); [left|right; right]; auto]. Qed.

Lemma xax_keep (s:sform) (Γ Δ:list sform) b u : (forall y, In y Δ -> y = s \/ In y Γ) ->
  kindof s <> KAtom -> In (b, PX u) Δ -> In (b, PX u) Γ.
Proof.
  intros H Hk Hin. destruct (H _ Hin) as [E|E]; [|exact E].
  exfalso. apply Hk. rewrite <- E. apply kind_PX.
Qed.

Lemma od_inv_conj n ρ α Δ : OD n ρ α Δ ->
  forall s s1 s2 sj Γ, kindof s = KConj s1 s2 -> isD (snd s) = false -> (sj = s1 \/ sj = s2) ->
  (forall y, In y Δ -> y = s \/ In y Γ) -> OD n ρ α (sj :: Γ).
Proof.
  induction 1 as [n ρ α Δ x Hx Hax
                 |n ρ α Δ u v Hu Hv Huv
                 |n ρ α β Δ x x1 x2 Hx Hk _ IH1 _ IH2 Hlt
                 |n ρ α β Δ x x1 x2 x' Hx Hk Hsel _ IH Hlt
                 |n ρ α β Δ x b A Hx Hk HD _ IH Hlt
                 |n ρ α β Δ x b A m Hx Hk Hm _ IH Hlt
                 |n ρ α β Δ x Hr _ IH1 _ IH2 Hlt
                 |n m ρ α β γ h Δ Hnm _ IH Hh Hmh Hlt];
    intros s s1 s2 sj Γ Hks HDs Hsj HΔ.
  - destruct (HΔ x Hx) as [->|Hx'].
    + exfalso. destruct Hax as [Hax _]. rewrite Hax in HDs. discriminate.
    + apply od_ax with x; [right; exact Hx' | exact Hax].
  - apply od_xax with u v; [right | right | exact Huv];
      (eapply xax_keep; [exact HΔ | rewrite Hks; discriminate | eassumption]).
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. injection Hk as <- <-.
      assert (H1 := IH1 s s1 s2 sj (s1 :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ)).
      assert (H2 := IH2 s s1 s2 sj (s2 :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ)).
      destruct Hsj as [->| ->].
      * eapply od_struct; [exact H1| | |apply olt_reach; exact Hlt|]; auto.
        intros y [<-|[<-|Hy]]; left; [left|left|right]; auto.
      * eapply od_struct; [exact H2| | |apply olt_reach; exact Hlt|]; auto.
        intros y [<-|[<-|Hy]]; left; [left|left|right]; auto.
    + apply od_conj with β x x1 x2; [right; exact Hx' | exact Hk | | | exact Hlt].
      * eapply od_weaken; [apply (IH1 s s1 s2 sj (x1 :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ))|].
        intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
      * eapply od_weaken; [apply (IH2 s s1 s2 sj (x2 :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ))|].
        intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. discriminate.
    + apply od_disj with β x x1 x2 x'; [right; exact Hx' | exact Hk | exact Hsel | | exact Hlt].
      eapply od_weaken; [apply (IH s s1 s2 sj (x' :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ))|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. discriminate.
    + apply od_univ with β x b A; [right; exact Hx' | exact Hk | exact HD | | exact Hlt].
      intro i. eapply od_weaken; [apply (IH i s s1 s2 sj (inst b A i :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ))|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. discriminate.
    + apply od_exis with β x b A m; [right; exact Hx' | exact Hk | exact Hm | | exact Hlt].
      eapply od_weaken; [apply (IH s s1 s2 sj (inst b A m :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ))|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - apply od_cut with β x; [exact Hr | | | exact Hlt].
    + eapply od_weaken; [apply (IH1 s s1 s2 sj (x :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ))|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
    + eapply od_weaken; [apply (IH2 s s1 s2 sj (sneg x :: Γ) Hks HDs Hsj (sub_rem_cons _ _ _ _ HΔ))|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - apply od_up with m β γ h; auto. apply (IH s s1 s2 sj Γ Hks HDs Hsj HΔ).
Qed.

Lemma max_swap n i j : Nat.max (Nat.max n (S j)) (S i) = Nat.max (Nat.max n (S i)) (S j).
Proof. lia. Qed.

Lemma od_inv_univ n ρ α Δ : OD n ρ α Δ ->
  forall s b A Γ, kindof s = KUniv b A -> isD (snd s) = false ->
  (forall y, In y Δ -> y = s \/ In y Γ) -> forall i, OD (Nat.max n (S i)) ρ α (inst b A i :: Γ).
Proof.
  induction 1 as [n ρ α Δ x Hx Hax
                 |n ρ α Δ u v Hu Hv Huv
                 |n ρ α β Δ x x1 x2 Hx Hk _ IH1 _ IH2 Hlt
                 |n ρ α β Δ x x1 x2 x' Hx Hk Hsel _ IH Hlt
                 |n ρ α β Δ x b' A' Hx Hk HD _ IH Hlt
                 |n ρ α β Δ x b' A' m Hx Hk Hm _ IH Hlt
                 |n ρ α β Δ x Hr _ IH1 _ IH2 Hlt
                 |n m ρ α β γ h Δ Hnm _ IH Hh Hmh Hlt];
    intros s b A Γ Hks HDs HΔ i.
  - destruct (HΔ x Hx) as [->|Hx'].
    + exfalso. destruct Hax as [Hax _]. rewrite Hax in HDs. discriminate.
    + apply od_ax with x; [right; exact Hx' | exact Hax].
  - apply od_xax with u v; [right | right | exact Huv];
      (eapply xax_keep; [exact HΔ | rewrite Hks; discriminate | eassumption]).
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. discriminate.
    + apply od_conj with β x x1 x2; [right; exact Hx' | exact Hk | | | apply olt_mono with n; [lia | exact Hlt]].
      * eapply od_weaken; [apply (IH1 s b A (x1 :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i)|].
        intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
      * eapply od_weaken; [apply (IH2 s b A (x2 :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i)|].
        intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. discriminate.
    + apply od_disj with β x x1 x2 x'; [right; exact Hx' | exact Hk | exact Hsel | | apply olt_mono with n; [lia | exact Hlt]].
      eapply od_weaken; [apply (IH s b A (x' :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i)|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. injection Hk as <- <-.
      assert (H := IH i s b A (inst b A i :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i).
      replace (Nat.max (Nat.max n (S i)) (S i)) with (Nat.max n (S i)) in H by lia.
      eapply od_struct; [exact H| | |apply olt_reach; apply Hlt|]; auto.
      intros y [<-|[<-|Hy]]; left; [left|left|right]; auto.
    + apply od_univ with β x b' A'; [right; exact Hx' | exact Hk | exact HD | |].
      * intro j. rewrite <- max_swap.
        eapply od_weaken; [apply (IH j s b A (inst b' A' j :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i)|].
        intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
      * intro j. apply olt_mono with (Nat.max n (S j)); [lia | apply Hlt].
  - destruct (HΔ x Hx) as [->|Hx'].
    + rewrite Hks in Hk. discriminate.
    + apply od_exis with β x b' A' m; [right; exact Hx' | exact Hk | lia | | apply olt_mono with n; [lia | exact Hlt]].
      eapply od_weaken; [apply (IH s b A (inst b' A' m :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i)|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - apply od_cut with β x; [exact Hr | | | apply olt_mono with n; [lia | exact Hlt]].
    + eapply od_weaken; [apply (IH1 s b A (x :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i)|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
    + eapply od_weaken; [apply (IH2 s b A (sneg x :: Γ) Hks HDs (sub_rem_cons _ _ _ _ HΔ) i)|].
      intros y [<-|[<-|Hy]]; [right; left|left|right; right]; auto.
  - destruct (hardy_exists γ (Nat.max n (S i))) as [h' Hh'].
    assert (Hhh : h <= h') by (apply (hardy_mono_arg γ n (Nat.max n (S i))); [lia | assumption | assumption]).
    apply od_up with (Nat.max m (S i)) β γ h'; [lia | | exact Hh' | |].
    + apply (IH s b A Γ Hks HDs HΔ i).
    + apply Nat.max_lub; [lia|]. apply hardy_ge in Hh'. lia.
    + apply olt_mono with n; [lia | exact Hlt].
Qed.

(** Contraction of an [X]-atom into another with the same value. *)
Lemma od_xcontr n ρ α Δ : OD n ρ α Δ ->
  forall b w w' Γ, (forall y, In y Δ -> y = (b, PX w) \/ In y Γ) -> In (b, PX w') Γ ->
  teval ρ0 w = teval ρ0 w' -> OD n ρ α Γ.
Proof.
  induction 1 as [n ρ α Δ x Hx Hax
                 |n ρ α Δ u v Hu Hv Huv
                 |n ρ α β Δ x x1 x2 Hx Hk _ IH1 _ IH2 Hlt
                 |n ρ α β Δ x x1 x2 x' Hx Hk Hsel _ IH Hlt
                 |n ρ α β Δ x b' A' Hx Hk HD _ IH Hlt
                 |n ρ α β Δ x b' A' m Hx Hk Hm _ IH Hlt
                 |n ρ α β Δ x Hr _ IH1 _ IH2 Hlt
                 |n m ρ α β γ h Δ Hnm _ IH Hh Hmh Hlt];
    intros b w w' Γ HΔ Hw' Ew.
  - destruct (HΔ x Hx) as [->|Hx'].
    + exfalso. destruct Hax as [Hax _]. discriminate.
    + apply od_ax with x; assumption.
  - destruct (HΔ _ Hu) as [E|Hu']; destruct (HΔ _ Hv) as [E'|Hv'].
    + rewrite <- E' in E. discriminate.
    + injection E as <- <-. apply od_xax with w' v; [exact Hw' | exact Hv' | lia].
    + injection E' as <- <-. apply od_xax with u w'; [exact Hu' | exact Hw' | lia].
    + apply od_xax with u v; assumption.
  - assert (Hk' : kindof x <> KAtom) by (rewrite Hk; discriminate).
    destruct (HΔ x Hx) as [->|Hx']; [exfalso; apply Hk'; apply kind_PX|].
    apply od_conj with β x x1 x2; [exact Hx' | exact Hk | | | exact Hlt].
    + apply (IH1 b w w' (x1 :: Γ)); [apply sub_rem_cons; exact HΔ | right; exact Hw' | exact Ew].
    + apply (IH2 b w w' (x2 :: Γ)); [apply sub_rem_cons; exact HΔ | right; exact Hw' | exact Ew].
  - assert (Hk' : kindof x <> KAtom) by (rewrite Hk; discriminate).
    destruct (HΔ x Hx) as [->|Hx']; [exfalso; apply Hk'; apply kind_PX|].
    apply od_disj with β x x1 x2 x'; [exact Hx' | exact Hk | exact Hsel | | exact Hlt].
    apply (IH b w w' (x' :: Γ)); [apply sub_rem_cons; exact HΔ | right; exact Hw' | exact Ew].
  - assert (Hk' : kindof x <> KAtom) by (rewrite Hk; discriminate).
    destruct (HΔ x Hx) as [->|Hx']; [exfalso; apply Hk'; apply kind_PX|].
    apply od_univ with β x b' A'; [exact Hx' | exact Hk | exact HD | | exact Hlt].
    intro i. apply (IH i b w w' (inst b' A' i :: Γ)); [apply sub_rem_cons; exact HΔ | right; exact Hw' | exact Ew].
  - assert (Hk' : kindof x <> KAtom) by (rewrite Hk; discriminate).
    destruct (HΔ x Hx) as [->|Hx']; [exfalso; apply Hk'; apply kind_PX|].
    apply od_exis with β x b' A' m; [exact Hx' | exact Hk | exact Hm | | exact Hlt].
    apply (IH b w w' (inst b' A' m :: Γ)); [apply sub_rem_cons; exact HΔ | right; exact Hw' | exact Ew].
  - apply od_cut with β x; [exact Hr | | | exact Hlt].
    + apply (IH1 b w w' (x :: Γ)); [apply sub_rem_cons; exact HΔ | right; exact Hw' | exact Ew].
    + apply (IH2 b w w' (sneg x :: Γ)); [apply sub_rem_cons; exact HΔ | right; exact Hw' | exact Ew].
  - apply od_up with m β γ h; auto. apply (IH b w w' Γ HΔ Hw' Ew).
Qed.

(** ** Cut elimination *)

Lemma rem_head (C:sform) (Γ:list sform) : forall y, In y (C :: Γ) -> y = C \/ In y Γ.
Proof. intros y [<-|Hy]; [left; reflexivity | right; exact Hy]. Qed.

Lemma kind_sneg_PX C w : snd C = PX w -> kindof (sneg C) = KAtom.
Proof. destruct C as [[|] A]; simpl; intros ->; reflexivity. Qed.

Lemma kind_conj_univ_neg C :
  (exists c1 c2, kindof C = KConj c1 c2) \/ (exists b A, kindof C = KUniv b A) \/ (exists w, snd C = PX w) ->
  (forall x1 x2, kindof (sneg C) <> KConj x1 x2) /\ (forall b A, kindof (sneg C) <> KUniv b A).
Proof.
  intros [[c1 [c2 H]]|[[b [A H]]|[w H]]].
  - apply kind_conj_neg in H. rewrite H. split; intros; discriminate.
  - apply kind_univ_neg in H. rewrite H. split; intros; discriminate.
  - rewrite (kind_sneg_PX C w H). split; intros; discriminate.
Qed.

(** The reduction lemma: a cut on [C] of maximal rank [ρ], where [C] is
    invertible (a conjunction or a universal) or an [X]-atom, is removed
    at the cost of adding the heights. *)
Theorem od_reduce ρ C : rank (snd C) = ρ -> isD (snd C) = false ->
  (exists c1 c2, kindof C = KConj c1 c2) \/ (exists b A, kindof C = KUniv b A) \/ (exists w, snd C = PX w) ->
  forall n β Δ, OD n ρ β Δ ->
  forall n0 α Γ, n0 <= n -> OD n0 ρ α (C :: Γ) ->
  (forall y, In y Δ -> y = sneg C \/ In y Γ) -> OD n ρ (vcat α β) Γ.
Proof.
  intros HrC HDC Hkind. destruct (kind_conj_univ_neg C Hkind) as [HnC HnU].
  subst ρ. intros n β Δ HD. remember (rank (snd C)) as ρ' eqn:Eρ. revert Eρ.
  induction HD as [n ρ' β Δ x Hx Hax
                  |n ρ' β Δ u v Hu Hv Huv
                 |n ρ' β βp Δ x x1 x2 Hx Hk _ IH1 _ IH2 Hlt
                 |n ρ' β βp Δ x x1 x2 x' Hx Hk Hsel _ IH Hlt
                 |n ρ' β βp Δ x b A Hx Hk HD _ IH Hlt
                 |n ρ' β βp Δ x b A m Hx Hk Hm _ IH Hlt
                 |n ρ' β βp Δ x Hr _ IH1 _ IH2 Hlt
                 |n m ρ' β βp γ h Δ Hnm _ IH Hh Hmh Hlt];
    intros Eρ n0 α Γ Hn0 HC HΔ; subst ρ'.
  - destruct (HΔ x Hx) as [->|Hin].
    + exfalso. destruct Hax as [Hax _]. simpl in Hax. rewrite Hax in HDC. discriminate.
    + apply od_ax with x; assumption.
  - destruct (HΔ _ Hu) as [E|Hu']; destruct (HΔ _ Hv) as [E'|Hv'].
    + rewrite <- E' in E. discriminate.
    + assert (EC : C = (false, PX u)) by (rewrite <- (sneg_sneg C), <- E; reflexivity). subst C.
      eapply od_struct; [apply (od_xcontr _ _ _ _ HC false u v Γ (rem_head _ Γ) Hv' Huv) | exact Hn0 | lia
                         | apply reach_prefix | apply sub_mod_incl, incl_refl].
    + assert (EC : C = (true, PX v)) by (rewrite <- (sneg_sneg C), <- E'; reflexivity). subst C.
      eapply od_struct; [apply (od_xcontr _ _ _ _ HC true v u Γ (rem_head _ Γ) Hu' (eq_sym Huv)) | exact Hn0 | lia
                         | apply reach_prefix | apply sub_mod_incl, incl_refl].
    + apply od_xax with u v; assumption.
  - destruct (HΔ x Hx) as [->|Hin]; [exfalso; exact (HnC x1 x2 Hk)|].
    apply od_conj with (vcat α βp) x x1 x2; [exact Hin | exact Hk | | | apply olt_vcat; exact Hlt].
    + apply (IH1 eq_refl n0 α (x1 :: Γ) Hn0); [|apply sub_rem_cons; exact HΔ].
      eapply od_weaken; [exact HC|]. intros y [<-|Hy]; [left|right; right]; auto.
    + apply (IH2 eq_refl n0 α (x2 :: Γ) Hn0); [|apply sub_rem_cons; exact HΔ].
      eapply od_weaken; [exact HC|]. intros y [<-|Hy]; [left|right; right]; auto.
  - assert (IH' : OD n (rank (snd C)) (vcat α βp) (x' :: Γ)).
    { apply (IH eq_refl n0 α (x' :: Γ) Hn0); [|apply sub_rem_cons; exact HΔ].
      eapply od_weaken; [exact HC|]. intros y [<-|Hy]; [left|right; right]; auto. }
    destruct (HΔ x Hx) as [->|Hin].
    + destruct Hkind as [[c1 [c2 HkC]]|[[b [A HkC]]|[w HkC]]].
      2:{ apply kind_univ_neg in HkC. rewrite HkC in Hk. discriminate. }
      2:{ rewrite (kind_sneg_PX C w HkC) in Hk. discriminate. }
      assert (HkC' := kind_conj_neg C c1 c2 HkC). rewrite HkC' in Hk.
      injection Hk as <- <-.
      assert (Hcj : exists cj, (cj = c1 \/ cj = c2) /\ x' = sneg cj).
      { destruct Hsel as [->| ->]; [exists c1|exists c2]; auto. }
      destruct Hcj as [cj [Hcj ->]].
      apply od_cut with (vcat α βp) cj; [| | exact IH' | apply olt_vcat; exact Hlt].
      * destruct (rank_conj C c1 c2 HkC HDC) as [H1 H2]. destruct Hcj as [->| ->]; lia.
      * eapply od_struct; [apply (od_inv_conj _ _ _ _ HC C c1 c2 cj Γ HkC HDC Hcj (rem_head C Γ))| | |apply reach_prefix|];
          auto using reach_refl.
        intros y Hy. left. exact Hy.
    + apply od_disj with (vcat α βp) x x1 x2 x'; [exact Hin | exact Hk | exact Hsel | exact IH' | apply olt_vcat; exact Hlt].
  - destruct (HΔ x Hx) as [->|Hin]; [exfalso; exact (HnU b A Hk)|].
    apply od_univ with (fun i => vcat α (βp i)) x b A; [exact Hin | exact Hk | exact HD | |].
    + intro i. apply (IH i eq_refl n0 α (inst b A i :: Γ)); [lia| |apply sub_rem_cons; exact HΔ].
      eapply od_weaken; [exact HC|]. intros y [<-|Hy]; [left|right; right]; auto.
    + intro i. apply olt_vcat. apply Hlt.
  - assert (IH' : OD n (rank (snd C)) (vcat α βp) (inst b A m :: Γ)).
    { apply (IH eq_refl n0 α (inst b A m :: Γ) Hn0); [|apply sub_rem_cons; exact HΔ].
      eapply od_weaken; [exact HC|]. intros y [<-|Hy]; [left|right; right]; auto. }
    destruct (HΔ x Hx) as [->|Hin].
    + destruct Hkind as [[c1 [c2 HkC]]|[[b' [A' HkC]]|[w HkC]]].
      { apply kind_conj_neg in HkC. rewrite HkC in Hk. discriminate. }
      2:{ rewrite (kind_sneg_PX C w HkC) in Hk. discriminate. }
      assert (HkC' := kind_univ_neg C b' A' HkC). rewrite HkC' in Hk.
      injection Hk as <- <-.
      apply od_cut with (vcat α βp) (inst b' A' m); [| | | apply olt_vcat; exact Hlt].
      * exact (rank_univ C b' A' m HkC HDC).
      * eapply od_struct; [apply (od_inv_univ _ _ _ _ HC C b' A' Γ HkC HDC (rem_head C Γ) m) | | |apply reach_prefix|];
          auto using reach_refl; [lia|].
        intros y Hy. left. exact Hy.
      * rewrite inst_sneg. exact IH'.
    + apply od_exis with (vcat α βp) x b A m; [exact Hin | exact Hk | exact Hm | exact IH' | apply olt_vcat; exact Hlt].
  - apply od_cut with (vcat α βp) x; [exact Hr | | | apply olt_vcat; exact Hlt].
    + apply (IH1 eq_refl n0 α (x :: Γ) Hn0); [|apply sub_rem_cons; exact HΔ].
      eapply od_weaken; [exact HC|]. intros y [<-|Hy]; [left|right; right]; auto.
    + apply (IH2 eq_refl n0 α (sneg x :: Γ) Hn0); [|apply sub_rem_cons; exact HΔ].
      eapply od_weaken; [exact HC|]. intros y [<-|Hy]; [left|right; right]; auto.
  - apply od_up with m (vcat α βp) γ h; [exact Hnm | | exact Hh | exact Hmh |].
    + apply (IH eq_refl n0 α Γ); [lia | exact HC | exact HΔ].
    + rewrite vcat_assoc. apply olt_vcat. exact Hlt.
Qed.

(** The elimination lemma: removing the cuts of the top rank costs one
    exponential. *)
Theorem od_elim n ρ α Γ : OD n (S ρ) α Γ -> 1 <= ρ -> 3 <= n -> OD n ρ (V α Z) Γ.
Proof.
  intros H Hρ. remember (S ρ) as ρ' eqn:E. revert E.
  induction H as [n ρ' α Γ x Hx Hax
                 |n ρ' α Γ u v Hu Hv Huv
                 |n ρ' α β Γ x x1 x2 Hx Hk _ IH1 _ IH2 Hlt
                 |n ρ' α β Γ x x1 x2 x' Hx Hk Hsel _ IH Hlt
                 |n ρ' α β Γ x b A Hx Hk HD _ IH Hlt
                 |n ρ' α β Γ x b A m Hx Hk Hm _ IH Hlt
                 |n ρ' α β Γ x Hr _ IH1 _ IH2 Hlt
                 |n m ρ' α β γ h Γ Hnm _ IH Hh Hmh Hlt];
    intros E Hn; subst ρ'.
  - apply od_ax with x; assumption.
  - apply od_xax with u v; assumption.
  - apply od_conj with (V β Z) x x1 x2; auto. apply olt_exp; [lia | exact Hlt].
  - apply od_disj with (V β Z) x x1 x2 x'; auto. apply olt_exp; [lia | exact Hlt].
  - apply od_univ with (fun i => V (β i) Z) x b A; auto.
    + intro i. apply IH; [reflexivity | lia].
    + intro i. apply olt_exp; [lia | apply Hlt].
  - apply od_exis with (V β Z) x b A m; auto. apply olt_exp; [lia | exact Hlt].
  - assert (H1 := IH1 eq_refl Hn). assert (H2 := IH2 eq_refl Hn).
    destruct (Nat.lt_ge_cases (rank (snd x)) ρ) as [Hlo|Hhi].
    + apply od_cut with (V β Z) x; auto. apply olt_exp; [lia | exact Hlt].
    + assert (Hrx : rank (snd x) = ρ) by lia.
      assert (HDx : isD (snd x) = false).
      { destruct (isD (snd x)) eqn:ED; [|reflexivity]. rewrite rank_D in Hrx by exact ED. lia. }
      destruct Hlt as [α1 [Hα1 Hβ]].
      assert (Hexp : reach n (V β Z) (V α1 Z)) by (apply reach_exp_mono; [lia | exact Hβ]).
      apply od_height with (vcat (V α1 Z) (V α1 Z)); [|apply olt_reach; apply olt_two; assumption].
      destruct (kindof x) as [|x1 x2|x1 x2|b A|b A] eqn:Hk.
      * destruct (kind_atom_D x Hk) as [HD'|[w Hw]]; [rewrite HD' in HDx; discriminate|].
        refine (od_reduce ρ x Hrx HDx (or_intror (or_intror (ex_intro _ w Hw))) n (V α1 Z) (sneg x :: Γ) _
          n (V α1 Z) Γ (le_n n) _ _); [apply od_height with (V β Z); assumption | apply od_height with (V β Z); assumption|].
        intros y [<-|Hy]; [left|right]; auto.
      * refine (od_reduce ρ x Hrx HDx (or_introl (ex_intro _ x1 (ex_intro _ x2 Hk))) n (V α1 Z) (sneg x :: Γ) _
          n (V α1 Z) Γ (le_n n) _ _); [apply od_height with (V β Z); assumption | apply od_height with (V β Z); assumption|].
        intros y [<-|Hy]; [left|right]; auto.
      * assert (Hk' := kind_disj_neg x x1 x2 Hk).
        refine (od_reduce ρ (sneg x) Hrx HDx (or_introl (ex_intro _ _ (ex_intro _ _ Hk'))) n (V α1 Z) (x :: Γ) _
          n (V α1 Z) Γ (le_n n) _ _); [apply od_height with (V β Z); assumption | apply od_height with (V β Z); assumption|].
        intros y [<-|Hy]; [left; rewrite sneg_sneg; reflexivity|right; exact Hy].
      * refine (od_reduce ρ x Hrx HDx (or_intror (or_introl (ex_intro _ b (ex_intro _ A Hk)))) n (V α1 Z) (sneg x :: Γ) _
          n (V α1 Z) Γ (le_n n) _ _); [apply od_height with (V β Z); assumption | apply od_height with (V β Z); assumption|].
        intros y [<-|Hy]; [left|right]; auto.
      * assert (Hk' := kind_exis_neg x b A Hk).
        refine (od_reduce ρ (sneg x) Hrx HDx (or_intror (or_introl (ex_intro _ _ (ex_intro _ _ Hk')))) n (V α1 Z) (x :: Γ) _
          n (V α1 Z) Γ (le_n n) _ _); [apply od_height with (V β Z); assumption | apply od_height with (V β Z); assumption|].
        intros y [<-|Hy]; [left; rewrite sneg_sneg; reflexivity|right; exact Hy].
  - assert (Hm3 : 3 <= m) by lia.
    assert (H1 := IH eq_refl Hm3).
    destruct Hlt as [α1 [Hα1 Hβγ]].
    assert (Hβ : reach n β α1) by (eapply reach_trans; [apply reach_prefix | exact Hβγ]).
    destruct (hardy_exists (V α1 Z) n) as [h' Hh'].
    apply od_up with m (V α1 Z) (V α1 Z) h'; [exact Hnm | | exact Hh' | | apply olt_two; [lia | exact Hα1]].
    + apply od_height with (V β Z); [exact H1|]. apply reach_exp_mono; [lia|].
      apply reach_mono with n; assumption.
    + destruct (hardy_exists (vcat β γ) n) as [k Hk].
      destruct (hardy_exists α1 n) as [k1 Hk1].
      apply Nat.le_trans with h; [exact Hmh|].
      apply Nat.le_trans with k; [apply (hardy_vcat_ge β γ n k h Hk Hh)|].
      apply Nat.le_trans with k1; [apply (hardy_mono_reach n (vcat β γ) α1 k k1 Hβγ Hk Hk1)|].
      apply (hardy_exp_ge α1 n k1 h'); [lia | exact Hk1 | exact Hh'].
Qed.

Fixpoint otower (k:nat) (a:VForm) : VForm :=
  match k with O => a | S k => otower k (V a Z) end.

Theorem od_elim_all k : forall n α Γ, OD n (S k) α Γ -> 3 <= n -> OD n 1 (otower k α) Γ.
Proof.
  induction k as [|k IH]; intros n α Γ H Hn; [exact H|].
  simpl. apply IH; [|exact Hn]. apply od_elim; [exact H | lia | exact Hn].
Qed.

(** ** Bounding

    In a derivation of a Σ₁ sequent whose cuts are on bounded formulas
    only, the existential witnesses can be bounded: some formula of the
    sequent is true with all its witnesses below [H_α(n)]. *)

Fixpoint isS (A:form) : bool :=
  isD A || match A with Ex B => isS B | _ => false end.

Lemma isS_iff A : isS A = true <-> isD A = true \/ exists B, A = Ex B /\ isS B = true.
Proof.
  split.
  - destruct A as [s t| |A B|A B|A B|A|A|u]; cbn [isS]; rewrite orb_true_iff;
      intros [H|H]; auto; try discriminate.
    right. exists A. auto.
  - intros [H|[B [-> H]]]; [destruct A; cbn [isS]; rewrite H; reflexivity|].
    cbn [isS]. rewrite H. apply orb_true_r.
Qed.

Lemma isS_fsubst A : forall σ, isS A = true -> isS (fsubst σ A) = true.
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u]; intros σ H;
    apply isS_iff in H as [H|[B' [E H]]]; apply isS_iff;
    try (left; apply isD_fsubst; exact H); try discriminate.
  injection E as <-. right. exists (fsubst (up σ) A). split; [reflexivity | apply IHA; exact H].
Qed.

Definition sigf (s:sform) : Prop := (fst s = true /\ isS (snd s) = true) \/ isD (snd s) = true.

Fixpoint tb (B:nat) (ρ:nat -> nat) (A:form) : Prop :=
  if isD A then deval ρ A = true else
  match A with Ex A' => exists m, m < B /\ tb B (scons m ρ) A' | _ => False end.

Definition Tbs (B:nat) (s:sform) : Prop :=
  if fst s then tb B ρ0 (snd s) else isD (snd s) = true /\ deval ρ0 (snd s) = false.

Lemma tb_mono B B' A : forall ρ, B <= B' -> tb B ρ A -> tb B' ρ A.
Proof.
  induction A as [s t| |A IHA C IHC|A IHA C IHC|A IHA C IHC|A IHA|A IHA|u]; intros ρ HB H;
    cbn [tb] in *; destruct (isD _); auto.
  destruct H as [m [Hm H]]. exists m. split; [lia | apply IHA; assumption].
Qed.

Lemma tb_ext B A : forall ρ ρ', (forall i, ρ i = ρ' i) -> tb B ρ A -> tb B ρ' A.
Proof.
  induction A as [s t| |A IHA C IHC|A IHA C IHC|A IHA C IHC|A IHA|A IHA|u]; intros ρ ρ' E H;
    cbn [tb] in *; destruct (isD _) eqn:ED;
    try (rewrite <- (deval_ext _ ρ ρ' ED E); exact H); auto.
  destruct H as [m [Hm H]]. exists m. split; [exact Hm|].
  apply (IHA (scons m ρ)); [|exact H]. intros [|i]; simpl; auto.
Qed.

Lemma tb_eq B ρ A : tb B ρ A =
  if isD A then deval ρ A = true else
  match A with Ex A' => exists m, m < B /\ tb B (scons m ρ) A' | _ => False end.
Proof. destruct A; reflexivity. Qed.

Lemma tb_fsubst B A : forall ρ σ, tb B ρ (fsubst σ A) -> tb B (fun i => teval ρ (σ i)) A.
Proof.
  induction A as [s t| |A IHA C IHC|A IHA C IHC|A IHA C IHC|A IHA|A IHA|u]; intros ρ σ H;
    rewrite tb_eq in H |- *; rewrite isD_fsubst_eq in H;
    destruct (isD _) eqn:ED; try (rewrite <- deval_fsubst by exact ED; exact H);
    cbn [fsubst] in H; auto.
  destruct H as [m [Hm H]]. exists m. split; [exact Hm|].
  apply IHA in H. revert H. apply tb_ext. intros [|i]; simpl; [reflexivity | apply teval_shift].
Qed.

Lemma Tbs_mono B B' s : B <= B' -> Tbs B s -> Tbs B' s.
Proof. destruct s as [[|] A]; unfold Tbs; simpl; [apply tb_mono | auto]. Qed.

Lemma Tbs_dax B s : dax s -> Tbs B s.
Proof.
  destruct s as [[|] A]; unfold Tbs, dax; simpl; intros [HD Hv].
  - destruct A; cbn [tb]; rewrite HD; exact Hv.
  - auto.
Qed.

Lemma Tbs_dfalse B s : dfalse s -> Tbs B s -> False.
Proof.
  destruct s as [[|] A]; unfold Tbs, dfalse; simpl; intros [HD Hv] H.
  - destruct A; cbn [tb] in H; rewrite HD in H; rewrite Hv in H; discriminate.
  - destruct H as [_ H]. rewrite Hv in H. discriminate.
Qed.

Lemma sigf_D s : isD (snd s) = false -> sigf s -> exists A, s = (true, Ex A) /\ isS A = true.
Proof.
  intros HD [[Hb HS]|H]; [|rewrite H in HD; discriminate].
  destruct s as [b A]; simpl in *; subst b.
  destruct A; cbn [isS] in HS; rewrite HD in HS; try discriminate.
  eexists; split; [reflexivity | exact HS].
Qed.

Theorem od_bounding n ρ α Γ : OD n ρ α Γ -> ρ <= 1 ->
  (forall s, In s Γ -> sigf s) -> forall h, hardy α n h -> exists s, In s Γ /\ Tbs h s.
Proof.
  induction 1 as [n ρ α Γ s Hs Hax
                 |n ρ α Γ u v Hu Hv Huv
                 |n ρ α β Γ s s1 s2 Hs Hk _ IH1 _ IH2 Hlt
                 |n ρ α β Γ s s1 s2 s' Hs Hk Hsel _ IH Hlt
                 |n ρ α β Γ s b A Hs Hk HD _ IH Hlt
                 |n ρ α β Γ s b A m Hs Hk Hm _ IH Hlt
                 |n ρ α β Γ s Hr _ IH1 _ IH2 Hlt
                 |n m ρ α β γ h Γ Hnm _ IH Hh Hmh Hlt];
    intros Hρ HΓ hα Hα.
  - exists s. split; [exact Hs | apply Tbs_dax; exact Hax].
  - exfalso. destruct (HΓ _ Hu) as [[_ H]|H]; discriminate.
  - destruct (isD (snd s)) eqn:HD.
    + destruct (dax_dec s HD) as [Hax|Hf]; [exists s; split; [exact Hs | apply Tbs_dax; exact Hax]|].
      destruct (hardy_exists β n) as [hβ Hβ].
      assert (Hle : hβ <= hα) by (apply (olt_hardy n β α); assumption).
      destruct (isD_conj s s1 s2 Hk HD) as [HD1 HD2].
      destruct (dfalse_conj s s1 s2 Hk Hf) as [H|H].
      * destruct (IH1 Hρ ltac:(intros x [<-|Hx]; [right; exact HD1 | apply HΓ; exact Hx]) hβ Hβ)
          as [x [[<-|Hx] Hx']]; [exfalso; exact (Tbs_dfalse _ _ H Hx')|].
        exists x. split; [exact Hx | apply Tbs_mono with hβ; assumption].
      * destruct (IH2 Hρ ltac:(intros x [<-|Hx]; [right; exact HD2 | apply HΓ; exact Hx]) hβ Hβ)
          as [x [[<-|Hx] Hx']]; [exfalso; exact (Tbs_dfalse _ _ H Hx')|].
        exists x. split; [exact Hx | apply Tbs_mono with hβ; assumption].
    + destruct (sigf_D s HD (HΓ s Hs)) as [A [-> _]]. discriminate.
  - destruct (isD (snd s)) eqn:HD.
    + destruct (dax_dec s HD) as [Hax|Hf]; [exists s; split; [exact Hs | apply Tbs_dax; exact Hax]|].
      destruct (hardy_exists β n) as [hβ Hβ].
      assert (Hle : hβ <= hα) by (apply (olt_hardy n β α); assumption).
      destruct (isD_disj s s1 s2 Hk HD) as [HD1 HD2].
      destruct (dfalse_disj s s1 s2 Hk Hf) as [H1 H2].
      assert (HDs' : isD (snd s') = true) by (destruct Hsel as [-> | ->]; assumption).
      assert (Hfs' : dfalse s') by (destruct Hsel as [-> | ->]; assumption).
      destruct (IH Hρ ltac:(intros x [<-|Hx]; [right; exact HDs' | apply HΓ; exact Hx]) hβ Hβ)
        as [x [[<-|Hx] Hx']]; [exfalso; exact (Tbs_dfalse _ _ Hfs' Hx')|].
      exists x. split; [exact Hx | apply Tbs_mono with hβ; assumption].
    + destruct (sigf_D s HD (HΓ s Hs)) as [A' [-> _]]. discriminate.
  - destruct (sigf_D s HD (HΓ s Hs)) as [A' [-> _]]. discriminate.
  - destruct (hardy_exists β n) as [hβ Hβ].
    assert (Hle : hβ <= hα) by (apply (olt_hardy n β α); assumption).
    assert (Hmα : m < hα).
    { apply Nat.lt_le_trans with n; [exact Hm|]. eapply hardy_ge. exact Hα. }
    destruct (isD (snd s)) eqn:HD.
    + destruct (dax_dec s HD) as [Hax|Hf]; [exists s; split; [exact Hs | apply Tbs_dax; exact Hax]|].
      assert (Hfi := dfalse_exis s b A m Hk Hf).
      destruct (IH Hρ ltac:(intros x [<-|Hx]; [right; exact (proj1 Hfi) | apply HΓ; exact Hx]) hβ Hβ)
        as [x [[<-|Hx] Hx']]; [exfalso; exact (Tbs_dfalse _ _ Hfi Hx')|].
      exists x. split; [exact Hx | apply Tbs_mono with hβ; assumption].
    + destruct (sigf_D s HD (HΓ s Hs)) as [A' [-> HS]].
      simpl in Hk. injection Hk as <- <-.
      assert (Hsi : sigf (inst true A' m)).
      { left. split; [reflexivity|]. apply isS_fsubst. exact HS. }
      destruct (IH Hρ ltac:(intros x [<-|Hx]; [exact Hsi | apply HΓ; exact Hx]) hβ Hβ)
        as [x [[<-|Hx] Hx']].
      * exists (true, Ex A'). split; [exact Hs|].
        unfold Tbs. simpl. cbn [tb]. simpl in HD. rewrite HD.
        exists m. split; [exact Hmα|].
        unfold Tbs, inst in Hx'. simpl in Hx'. unfold sub1 in Hx'.
        apply tb_fsubst in Hx'. apply tb_mono with hβ; [exact Hle|].
        revert Hx'. apply tb_ext. intros [|i]; simpl; [apply teval_num | reflexivity].
      * exists x. split; [exact Hx | apply Tbs_mono with hβ; assumption].
  - destruct (hardy_exists β n) as [hβ Hβ].
    assert (Hle : hβ <= hα) by (apply (olt_hardy n β α); assumption).
    assert (HDs : isD (snd s) = true) by (apply rank_0_D; lia).
    destruct (dax_dec s HDs) as [Hax|Hf].
    + assert (Hf : dfalse (sneg s)) by (apply dfalse_sneg; rewrite sneg_sneg; exact Hax).
      destruct (IH2 Hρ ltac:(intros x [<-|Hx]; [right; exact HDs | apply HΓ; exact Hx]) hβ Hβ)
        as [x [[<-|Hx] Hx']]; [exfalso; exact (Tbs_dfalse _ _ Hf Hx')|].
      exists x. split; [exact Hx | apply Tbs_mono with hβ; assumption].
    + destruct (IH1 Hρ ltac:(intros x [<-|Hx]; [right; exact HDs | apply HΓ; exact Hx]) hβ Hβ)
        as [x [[<-|Hx] Hx']]; [exfalso; exact (Tbs_dfalse _ _ Hf Hx')|].
      exists x. split; [exact Hx | apply Tbs_mono with hβ; assumption].
  - destruct (hardy_exists β m) as [hm Hm].
    destruct (hardy_exists β h) as [hβh Hβh].
    destruct (IH Hρ HΓ hm Hm) as [x [Hx Hx']].
    exists x. split; [exact Hx|]. apply Tbs_mono with hm; [|exact Hx'].
    apply Nat.le_trans with hβh; [apply (hardy_mono_arg β m h); assumption|].
    apply (olt_hardy n (vcat β γ) α); [exact Hlt | | exact Hα].
    apply hardy_vcat with h; assumption.
Qed.

(** A Σ₁ sentence [∃y. θ] with [θ] bounded, derived without unbounded
    cuts at height [α] and control [n], has a witness below [H_α(n)]. *)
Corollary od_witness n α A h : OD n 1 α [(true, Ex A)] -> isD A = true -> isD (Ex A) = false ->
  hardy α n h -> exists m, m < h /\ sat ρ0 (sub1 A (num m)).
Proof.
  intros H HA HE Hh.
  destruct (od_bounding n 1 α _ H (le_n 1)) with h as [s [[<-|[]] Hs]]; [|exact Hh|].
  - intros s [<-|[]]. left. split; [reflexivity|].
    apply isS_iff. right. exists A. split; [reflexivity|]. apply isS_iff. left. exact HA.
  - unfold Tbs in Hs. cbn [fst snd] in Hs. rewrite tb_eq, HE in Hs.
    destruct Hs as [m [Hm Hs]]. exists m. split; [exact Hm|].
    rewrite tb_eq, HA in Hs. apply deval_sat in Hs; [|exact HA].
    apply sat_sub1_num. exact Hs.
Qed.
