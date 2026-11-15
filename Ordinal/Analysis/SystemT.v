From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Wellfounded.
Import ListNotations.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import Notation.VNotation.

Local Open Scope nat_scope.

(** * An ordinal analysis of Gödel's System T below ε₀

    Following Tait ("Infinitely long terms of transfinite type", 1965),
    the recursor of System T is replaced by an ω-branching term:
    [rec C z s t] becomes [Ω_C(f) t], where [Ω_C(f) : nat → C] has one
    branch [f n = s (n-1) (... (s 0 z))] per numeral.  The resulting
    infinitary simply-typed terms are normalized by cut elimination,
    one type level at a time.

    Derivations carry a _height_ and a _cut rank_.  The heights are
    V forms ([VNotation]), so every ordinal in this file is a notation,
    and lies below ε₀ ([VNotation_below_ε₀]).  The analysis is:

    - the translation of a term [t] has height [h t] and cut rank
      [tlev t], the largest level of a type at which [t] eliminates
      ([tr_typed]); [h t] is below [ω^ω] ([h_below_ω_ω]);
    - one pass of cut elimination ([elim]) lowers the cut rank by one,
      sending height [α] to [ω^α] ([elim_typed]);
    - hence the normal form of [t] has height at most the tower
      [ω^ω^...^(h t)] of height [tlev t] ([T_normalization]); this is the
      ordinal [ord_of t] of the term, an explicit V form, below the
      tower [ω_{tlev t + 2}] ([ord_of_bound]);
    - a closed normal term of type [nat] is a numeral, so every closed
      term of type [nat] reduces to a numeral ([T_total]).

    All the recursion is structural, on infinitary terms; the heights
    are bounds on those terms, in the manner of Tait and Schwichtenberg.
    Each pass is the familiar reduction lemma for cuts of maximal level:
    a β-redex at that level becomes a substitution at a lower level
    ([subst_typed]), an ω-redex selects a branch, and the commuting
    conversions push eliminations into branches. *)

(** ** Types and levels *)

Inductive ty : Set :=
| TN : ty
| TAr : ty -> ty -> ty.

(** Levels start at 1: an ω-redex has level 1, and substituting at any
    type may create one. *)
Fixpoint lev (τ:ty) : nat :=
  match τ with
  | TN => 1
  | TAr A B => Nat.max (S (lev A)) (lev B)
  end.

Lemma lev_pos τ : 1 <= lev τ.
Proof.
  destruct τ as [|A B]; cbn [lev]; [lia|].
  apply Nat.le_trans with (S (lev A)); [lia | apply Nat.le_max_l].
Qed.

(** ** Infinitary terms

    Applications are annotated with the type [A → B] of the function, so
    that the level of a potential cut can be read off the term. *)

Inductive iterm : Set :=
| ivar : nat -> iterm
| ilam : ty -> iterm -> iterm
| iapp : ty -> ty -> iterm -> iterm -> iterm
| izero : iterm
| isucc : iterm -> iterm
| iomega : ty -> (nat -> iterm) -> iterm.   (* [Ω_C(f) : nat → C] *)

Fixpoint lift (c:nat) (M:iterm) : iterm :=
  match M with
  | ivar y => ivar (if y <? c then y else S y)
  | ilam A K => ilam A (lift (S c) K)
  | iapp A B M N => iapp A B (lift c M) (lift c N)
  | izero => izero
  | isucc K => isucc (lift c K)
  | iomega C f => iomega C (fun n => lift c (f n))
  end.

Definition unshift (k y:nat) : nat := if y <? k then y else pred y.

(** [subst M k N] replaces the variable [k] of [M] by [N]. *)
Fixpoint subst (M:iterm) (k:nat) (N:iterm) : iterm :=
  match M with
  | ivar y => if y =? k then N else ivar (unshift k y)
  | ilam A K => ilam A (subst K (S k) (lift 0 N))
  | iapp A B M1 M2 => iapp A B (subst M1 k N) (subst M2 k N)
  | izero => izero
  | isucc K => isucc (subst K k N)
  | iomega C f => iomega C (fun n => subst (f n) k N)
  end.

Fixpoint inum (n:nat) : iterm :=
  match n with O => izero | S n => isucc (inum n) end.

(** The head variable of an application spine, if any.  Applications
    with a variable head are never cuts. *)
Fixpoint head_var (M:iterm) : option nat :=
  match M with
  | ivar x => Some x
  | iapp _ _ M _ => head_var M
  | _ => None
  end.

Definition isvh (M:iterm) : bool :=
  match head_var M with Some _ => true | None => false end.

Definition is_om (M:iterm) : bool :=
  match M with iomega _ _ => true | _ => false end.

(** An application [M N] at [A → B] is admissible at cut rank [ρ] when
    [M] has a variable head, or it is an ω-term applied to a neutral
    argument (or ω-redexes are allowed, [1 ≤ ρ]), or its level is at
    most [ρ]. *)
Definition cut_ok (ρ:nat) (A B:ty) (M N:iterm) : bool :=
  isvh M || (is_om M && (isvh N || (1 <=? ρ))) || (lev (TAr A B) <=? ρ).

(** ** Ordinal heights as V forms

    Heights are terms of the notation system [VForm] ([VNotation]):
    [V a x] denotes [ω^a + x].  The forms need not be normal: [vplus]
    appends the summands, which denotes ordinal addition without any
    comparison. *)

Fixpoint vplus (a b:VForm) : VForm :=
  match a with Z => b | V e x => V e (vplus x b) end.

Definition vexp (a:VForm) : VForm := V a Z.
Definition vsucc (a:VForm) : VForm := vplus a (vexp Z).

Fixpoint tower (k:nat) (a:VForm) : VForm :=
  match k with O => a | S k => tower k (vexp a) end.

Local Open Scope ord_scope.

Local Hint Resolve VF_complete zero_complete : core.

Lemma V_eq (a x:VForm) : sz (V a x) ≈ expOrd ω (sz a) + sz x.
Proof. apply veblen_onePlus; apply VF_complete. Qed.

Lemma vplus_eq (a b:VForm) : sz (vplus a b) ≈ sz a + sz b.
Proof.
  induction a as [|e _ x IH]; cbn [vplus].
  - symmetry. apply addOrd_zero_l.
  - rewrite !V_eq, IH. apply addOrd_assoc.
Qed.

Lemma vexp_eq (a:VForm) : sz (vexp a) ≈ expOrd ω (sz a).
Proof. unfold vexp. rewrite V_eq. apply addOrd_zero_r. Qed.

Lemma Z_eq : sz Z ≈ 0.
Proof. reflexivity. Qed.

Lemma vsucc_eq (a:VForm) : sz (vsucc a) ≈ succOrd (sz a).
Proof.
  unfold vsucc. rewrite vplus_eq, vexp_eq, Z_eq, expOrd_zero.
  rewrite addOrd_succ, addOrd_zero_r. reflexivity.
Qed.

Lemma vplus_le1 (a b:VForm) : a ⊴ vplus a b.
Proof. rewrite vplus_eq. apply addOrd_le1. Qed.

Lemma vplus_le2 (a b:VForm) : b ⊴ vplus a b.
Proof. rewrite vplus_eq. apply addOrd_le2. Qed.

Lemma vsucc_lt (a:VForm) : a ◃ vsucc a.
Proof. rewrite vsucc_eq. apply succ_lt. Qed.

Lemma vsucc_least (a b:VForm) : a ◃ b -> vsucc a ⊴ b.
Proof. intro H. rewrite vsucc_eq. apply succ_least. exact H. Qed.

(** [ω^c] is closed under addition, for complete [c]; every V form is
    complete. *)
Lemma below_exp_add (c:VForm) (x y:Ord) :
  x < expOrd ω (sz c) -> y < expOrd ω (sz c) -> x + y < expOrd ω (sz c).
Proof. apply expOmega_additively_closed. apply VF_complete. Qed.

Lemma vexp_increasing (a b:VForm) : a ◃ b -> vexp a ◃ vexp b.
Proof.
  intro H. rewrite !vexp_eq. apply expOrd_increasing; [apply omega_gt1 | exact H].
Qed.

(** Every V form is below its own power of [ω] (so below ε₀). *)
Lemma VF_shrink (x:VForm) : sz x < expOrd ω (sz x).
Proof.
  induction x as [|a IHa x IHx].
  - apply expOrd_nonzero.
  - rewrite (V_eq a x) at 1. apply below_exp_add.
    + apply expOrd_increasing; [apply omega_gt1 | apply VF_denote_shrink1].
    + eapply ord_lt_le_trans; [exact IHx|].
      apply expOrd_monotone. apply VF_denote_le2.
Qed.

(** The bound used by the reduction lemmas: [a + b + 1 < ω^c] when
    [a, b < ω^c] and [c > 0]. *)
Lemma below_exp_sum (a b c:VForm) :
  a ◃ vexp c -> b ◃ vexp c -> Z ◃ c -> vsucc (vplus a b) ◃ vexp c.
Proof.
  intros Ha Hb Hc. rewrite vsucc_eq, vplus_eq. rewrite vexp_eq in *.
  apply ord_le_lt_trans with (sz a + sz b + 1).
  { assert (E : sz a + sz b + 1 ≈ succOrd (sz a + sz b + 0)) by apply addOrd_succ.
    rewrite E, addOrd_zero_r. reflexivity. }
  apply below_exp_add; [apply below_exp_add; auto|].
  apply ord_le_lt_trans with (expOrd ω 0).
  - rewrite expOrd_zero. reflexivity.
  - apply expOrd_increasing; [apply omega_gt1 | exact Hc].
Qed.

Local Open Scope nat_scope.

(** ** Derivations with heights and cut ranks

    [D ρ Γ M A α]: [M] has type [A] in [Γ], by a derivation of height [α]
    whose cuts all have level at most [ρ].  Premises have strictly
    smaller heights; leaves may have any height. *)

Inductive D (ρ:nat) : list ty -> iterm -> ty -> VForm -> Prop :=
| D_var Γ x A α : nth_error Γ x = Some A -> D ρ Γ (ivar x) A α
| D_lam Γ A M B β α :
    D ρ (A :: Γ) M B β -> β ◃ α -> D ρ Γ (ilam A M) (TAr A B) α
| D_app Γ A B M N β1 β2 α :
    D ρ Γ M (TAr A B) β1 -> D ρ Γ N A β2 -> β1 ◃ α -> β2 ◃ α ->
    cut_ok ρ A B M N = true -> D ρ Γ (iapp A B M N) B α
| D_zero Γ α : D ρ Γ izero TN α
| D_succ Γ M β α : D ρ Γ M TN β -> β ◃ α -> D ρ Γ (isucc M) TN α
| D_omega Γ C f (β : nat -> VForm) α :
    (forall n, D ρ Γ (f n) C (β n)) -> (forall n, β n ◃ α) ->
    D ρ Γ (iomega C f) (TAr TN C) α.

Lemma cut_ok_cases ρ A B M N : cut_ok ρ A B M N = true ->
  isvh M = true \/ (is_om M = true /\ (isvh N = true \/ 1 <= ρ)) \/ lev (TAr A B) <= ρ.
Proof.
  unfold cut_ok. intro H.
  destruct (isvh M) eqn:E1; [left; reflexivity|].
  destruct (lev (TAr A B) <=? ρ) eqn:E3; [right; right; apply Nat.leb_le; exact E3|].
  rewrite orb_false_r in H. simpl in H. right; left.
  apply andb_true_iff in H as [H1 H2]. split; auto.
  apply orb_true_iff in H2 as [H2|H2]; [left; auto | right; apply Nat.leb_le; auto].
Qed.

Lemma cut_ok_vh ρ A B M N : isvh M = true -> cut_ok ρ A B M N = true.
Proof. unfold cut_ok. intro H. rewrite H. reflexivity. Qed.

Lemma cut_ok_om ρ A B M N :
  is_om M = true -> isvh N = true \/ 1 <= ρ -> cut_ok ρ A B M N = true.
Proof.
  unfold cut_ok. intros H1 [H2|H2]; rewrite H1; [rewrite H2|apply Nat.leb_le in H2; rewrite H2];
    rewrite !orb_true_r; reflexivity.
Qed.

Lemma cut_ok_lev ρ A B M N : lev (TAr A B) <= ρ -> cut_ok ρ A B M N = true.
Proof. unfold cut_ok. intro H. apply Nat.leb_le in H. rewrite H, !orb_true_r. reflexivity. Qed.

Lemma cut_ok_mono ρ ρ' A B M N : ρ <= ρ' -> cut_ok ρ A B M N = true -> cut_ok ρ' A B M N = true.
Proof.
  intros Hr H. destruct (cut_ok_cases _ _ _ _ _ H) as [H1 | [[H1 H2] | H1]].
  - apply cut_ok_vh; auto.
  - apply cut_ok_om; auto. destruct H2; [left; auto | right; lia].
  - apply cut_ok_lev; lia.
Qed.

(** Raising the height or the cut rank preserves derivability. *)
Lemma D_mono ρ Γ M A α : D ρ Γ M A α ->
  forall ρ' α', ρ <= ρ' -> α ⊴ α' -> D ρ' Γ M A α'.
Proof.
  intro H. induction H; intros ρ' α' Hr Ha.
  - constructor; auto.
  - econstructor; [apply IHD; eauto; reflexivity | eapply ord_lt_le_trans; eauto].
  - apply D_app with (β1 := β1) (β2 := β2).
    + apply IHD1; auto. reflexivity.
    + apply IHD2; auto. reflexivity.
    + eapply ord_lt_le_trans; eauto.
    + eapply ord_lt_le_trans; eauto.
    + eapply cut_ok_mono; eauto.
  - constructor.
  - econstructor; [apply IHD; eauto; reflexivity | eapply ord_lt_le_trans; eauto].
  - apply D_omega with (β := β); [intro n; apply H0; auto; reflexivity |].
    intro n; eapply ord_lt_le_trans; eauto.
Qed.

Lemma D_height ρ Γ M A α α' : D ρ Γ M A α -> α ⊴ α' -> D ρ Γ M A α'.
Proof. intros H Ha. eapply D_mono; eauto. Qed.

(** ** Weakening *)

Lemma head_var_lift c M :
  head_var (lift c M) = option_map (fun y => if y <? c then y else S y) (head_var M).
Proof. induction M; simpl; auto. Qed.

Lemma isvh_lift c M : isvh (lift c M) = isvh M.
Proof. unfold isvh. rewrite head_var_lift. destruct (head_var M); reflexivity. Qed.

Lemma is_om_lift c M : is_om (lift c M) = is_om M.
Proof. destruct M; reflexivity. Qed.

Lemma cut_ok_lift ρ A B c M N : cut_ok ρ A B (lift c M) (lift c N) = cut_ok ρ A B M N.
Proof. unfold cut_ok. rewrite !isvh_lift, is_om_lift. reflexivity. Qed.

Lemma nth_error_insert {X} : forall (Γ1 Γ2 : list X) a y,
  nth_error (Γ1 ++ a :: Γ2) (if y <? length Γ1 then y else S y) = nth_error (Γ1 ++ Γ2) y.
Proof.
  induction Γ1 as [|b Γ1 IH]; intros Γ2 a y; simpl.
  - destruct y; reflexivity.
  - destruct y as [|y]; simpl; auto.
    specialize (IH Γ2 a y). destruct (Nat.ltb_spec y (length Γ1));
      destruct (Nat.ltb_spec (S y) (S (length Γ1))); try lia; auto.
Qed.

Lemma nth_error_remove {X} (Γ1 Γ2 : list X) a y :
  y <> length Γ1 -> nth_error (Γ1 ++ Γ2) (unshift (length Γ1) y) = nth_error (Γ1 ++ a :: Γ2) y.
Proof.
  intros Hxy. rewrite <- (nth_error_insert Γ1 Γ2 a (unshift (length Γ1) y)). f_equal.
  unfold unshift.
  destruct (Nat.ltb_spec y (length Γ1)); [destruct (Nat.ltb_spec y (length Γ1)); lia|].
  destruct (Nat.ltb_spec (pred y) (length Γ1)); lia.
Qed.

Lemma nth_error_at {X} (Γ1 Γ2 : list X) a : nth_error (Γ1 ++ a :: Γ2) (length Γ1) = Some a.
Proof. induction Γ1; simpl; auto. Qed.

Lemma D_weaken ρ Γ M A α : D ρ Γ M A α ->
  forall Γ1 Γ2 B, Γ = Γ1 ++ Γ2 -> D ρ (Γ1 ++ B :: Γ2) (lift (length Γ1) M) A α.
Proof.
  intro H. induction H; intros Γ1 Γ2 B0 E; subst; simpl.
  - constructor. rewrite nth_error_insert. auto.
  - econstructor; [apply (IHD (A :: Γ1)); reflexivity | auto].
  - econstructor; eauto. rewrite cut_ok_lift. auto.
  - constructor.
  - econstructor; eauto.
  - apply D_omega with (β := β); [intro n; apply H0; reflexivity | auto].
Qed.

Lemma D_weaken0 ρ Γ M A B α : D ρ Γ M A α -> D ρ (B :: Γ) (lift 0 M) A α.
Proof. intro H. apply (D_weaken _ _ _ _ _ H [] Γ B). reflexivity. Qed.

(** ** Substitution

    The type of a variable-headed spine has level at most that of the
    head; so substituting at [A] creates cuts of level at most [lev A]. *)

Lemma head_lev ρ Γ M T α : D ρ Γ M T α ->
  forall x A, head_var M = Some x -> nth_error Γ x = Some A -> lev T <= lev A.
Proof.
  intro H. induction H; simpl; intros x0 A0 Hh Hx; try discriminate.
  - injection Hh as <-. rewrite H in Hx. injection Hx as <-. lia.
  - specialize (IHD1 x0 A0 Hh Hx). cbn [lev] in IHD1. lia.
Qed.

Lemma head_var_subst M k N y :
  head_var M = Some y -> y <> k -> head_var (subst M k N) = Some (unshift k y).
Proof.
  induction M; simpl; intros Hh Hy; try discriminate; auto.
  injection Hh as <-. destruct (Nat.eqb_spec n k); [contradiction | reflexivity].
Qed.

Lemma is_om_subst M k N : is_om M = true -> is_om (subst M k N) = true.
Proof. destruct M; simpl; auto; discriminate. Qed.

Theorem subst_typed ρ Γ M B α : D ρ Γ M B α ->
  forall Γ1 Γ2 A N β, Γ = Γ1 ++ A :: Γ2 -> D ρ (Γ1 ++ Γ2) N A β -> lev A <= ρ ->
  D ρ (Γ1 ++ Γ2) (subst M (length Γ1) N) B (vplus β α).
Proof.
  intro H. induction H; intros Γ1 Γ2 A0 N0 β0 E HN Hl; subst; simpl.
  - destruct (Nat.eqb_spec x (length Γ1)) as [->|Hne].
    + rewrite nth_error_at in H. injection H as <-.
      eapply D_height; [exact HN | apply vplus_le1].
    + constructor. rewrite (nth_error_remove Γ1 Γ2 A0); auto.
  - econstructor.
    + apply (IHD (A :: Γ1) Γ2 A0 (lift 0 N0) β0); auto. apply D_weaken0. auto.
    + rewrite !vplus_eq. apply addOrd_increasing. auto.
  - econstructor; [eapply IHD1; eauto | eapply IHD2; eauto
                   | rewrite !vplus_eq; apply addOrd_increasing; auto
                   | rewrite !vplus_eq; apply addOrd_increasing; auto |].
    destruct (cut_ok_cases _ _ _ _ _ H3) as [H4 | [[H4 _] | H4]].
    + unfold isvh in H4. destruct (head_var M) as [y|] eqn:Hy; [|discriminate].
      destruct (Nat.eq_dec y (length Γ1)) as [->|Hne].
      * apply cut_ok_lev. eapply Nat.le_trans; [|exact Hl].
        eapply head_lev; [exact H | exact Hy | apply nth_error_at].
      * apply cut_ok_vh. unfold isvh. rewrite (head_var_subst _ _ _ _ Hy Hne). reflexivity.
    + apply cut_ok_om; [apply is_om_subst; auto |]. right. pose proof (lev_pos A0). lia.
    + apply cut_ok_lev. auto.
  - constructor.
  - econstructor; [eapply IHD; eauto | rewrite !vplus_eq; apply addOrd_increasing; auto].
  - apply D_omega with (β := fun n => vplus β0 (β n)).
    + intro n. eapply H0; eauto.
    + intro n. rewrite !vplus_eq. apply addOrd_increasing. auto.
Qed.

(** ** Reduction

    The compatible closure of β-reduction, of the ω-rules (selecting a
    branch, or stripping a successor), and of the commuting conversions
    for an ω-term applied to a neutral argument.  Congruence under an
    ω-term reduces all of its branches at once. *)

Inductive red : iterm -> iterm -> Prop :=
| r_refl M : red M M
| r_trans M N P : red M N -> red N P -> red M P
| r_lam A M M' : red M M' -> red (ilam A M) (ilam A M')
| r_app A B M M' N N' : red M M' -> red N N' -> red (iapp A B M N) (iapp A B M' N')
| r_succ M M' : red M M' -> red (isucc M) (isucc M')
| r_omega C f g : (forall n, red (f n) (g n)) -> red (iomega C f) (iomega C g)
| r_beta A B A' K N : red (iapp A B (ilam A' K) N) (subst K 0 N)
| r_om_zero A B C f : red (iapp A B (iomega C f) izero) (f 0)
| r_om_succ A B C f K :
    red (iapp A B (iomega C f) (isucc K)) (iapp A B (iomega C (fun n => f (S n))) K)
| r_comm A B A0 B0 C f K N :
    red (iapp A B (iapp A0 B0 (iomega C f) K) N)
        (iapp A0 B (iomega B (fun n => iapp A B (f n) N)) K)
| r_case A B A0 B0 C E f g K :
    red (iapp A B (iomega C f) (iapp A0 B0 (iomega E g) K))
        (iapp A0 B (iomega B (fun n => iapp A B (iomega C f) (g n))) K).

(** ** The reduction lemmas

    [app_red A B M N] reduces the application [M N] at [A → B], for [M]
    of cut rank below the level of [A → B]: a λ is substituted into, and
    an ω-term applied to an argument absorbs [N] into its branches. *)

Fixpoint app_red (A B:ty) (M N:iterm) : iterm :=
  match M with
  | ilam _ K => subst K 0 N
  | iapp A0 _ M1 K =>
      match M1 with
      | iomega _ f => iapp A0 B (iomega B (fun n => app_red A B (f n) N)) K
      | _ => iapp A B M N
      end
  | _ => iapp A B M N
  end.

(** [omega_red A B C f N] reduces the ω-redex [Ω_C(f) N], for [N] normal:
    a numeral selects a branch, and an ω-term in [N] is commuted
    outwards. *)
Fixpoint omega_red (A B C:ty) (f:nat -> iterm) (N:iterm) : iterm :=
  match N with
  | izero => f 0
  | isucc K => omega_red A B C (fun n => f (S n)) K
  | iapp A0 _ N1 K =>
      match N1 with
      | iomega _ g => iapp A0 B (iomega B (fun n => omega_red A B C f (g n))) K
      | _ => iapp A B (iomega C f) N
      end
  | _ => iapp A B (iomega C f) N
  end.

(** One pass of cut elimination: cuts of level [ρ+1] are reduced, those
    of lower level are kept. *)
Fixpoint elim (ρ:nat) (M:iterm) : iterm :=
  match M with
  | ivar x => ivar x
  | ilam A K => ilam A (elim ρ K)
  | iapp A B M N =>
      let M' := elim ρ M in
      let N' := elim ρ N in
      if cut_ok ρ A B M' N' then iapp A B M' N'
      else match M' with
           | iomega C f => omega_red A B C f N'
           | _ => app_red A B M' N'
           end
  | izero => izero
  | isucc K => isucc (elim ρ K)
  | iomega C f => iomega C (fun n => elim ρ (f n))
  end.

Fixpoint norm (ρ:nat) (M:iterm) : iterm :=
  match ρ with O => M | S r => norm r (elim r M) end.

Lemma app_red_red : forall M A B N, red (iapp A B M N) (app_red A B M N).
Proof.
  fix IH 1. intros [x | A' K | A0 B0 M1 K | | K | C f] A B N; simpl;
    try apply r_refl; try apply r_beta.
  destruct M1 as [ | | | | | C f]; try apply r_refl.
  eapply r_trans; [apply r_comm|]. apply r_app; [|apply r_refl].
  apply r_omega. intro n. apply IH.
Qed.

Lemma omega_red_red : forall N A B C f, red (iapp A B (iomega C f) N) (omega_red A B C f N).
Proof.
  fix IH 1. intros [x | A' K | A0 B0 N1 K | | K | E g] A B C f; simpl;
    try apply r_refl; try apply r_om_zero.
  - destruct N1 as [ | | | | | E g]; try apply r_refl.
    eapply r_trans; [apply r_case|]. apply r_app; [|apply r_refl].
    apply r_omega. intro n. apply IH.
  - eapply r_trans; [apply r_om_succ | apply IH].
Qed.

Lemma elim_red ρ : forall M, red M (elim ρ M).
Proof.
  induction M as [x | A K IH | A B M IHM N IHN | | K IH | C f IH]; simpl.
  - apply r_refl.
  - apply r_lam. auto.
  - eapply r_trans; [apply r_app; [exact IHM | exact IHN]|].
    destruct (cut_ok ρ A B (elim ρ M) (elim ρ N)); [apply r_refl|].
    destruct (elim ρ M); try apply app_red_red. apply omega_red_red.
  - apply r_refl.
  - apply r_succ. auto.
  - apply r_omega. auto.
Qed.

Lemma norm_red ρ : forall M, red M (norm ρ M).
Proof.
  induction ρ; intro M; simpl; [apply r_refl|].
  eapply r_trans; [apply elim_red | apply IHρ].
Qed.

(** ** Inversion and bookkeeping *)

Lemma inv_var ρ Γ x T α : D ρ Γ (ivar x) T α -> nth_error Γ x = Some T.
Proof. intro H. inversion H; auto. Qed.

Lemma inv_lam ρ Γ A K T α : D ρ Γ (ilam A K) T α ->
  exists B β, T = TAr A B /\ D ρ (A :: Γ) K B β /\ (β ◃ α).
Proof. intro H. inversion H; subst. eauto. Qed.

Lemma inv_app ρ Γ A B M N T α : D ρ Γ (iapp A B M N) T α ->
  T = B /\ exists β1 β2, D ρ Γ M (TAr A B) β1 /\ D ρ Γ N A β2 /\
    (β1 ◃ α) /\ (β2 ◃ α) /\ cut_ok ρ A B M N = true.
Proof. intro H. inversion H; subst. split; eauto 10. Qed.

Lemma inv_succ ρ Γ K T α : D ρ Γ (isucc K) T α -> T = TN /\ exists β, D ρ Γ K TN β /\ (β ◃ α).
Proof. intro H. inversion H; subst. eauto. Qed.

Lemma inv_omega ρ Γ C f T α : D ρ Γ (iomega C f) T α ->
  T = TAr TN C /\ exists β : nat -> VForm, (forall n, D ρ Γ (f n) C (β n)) /\ (forall n, β n ◃ α).
Proof. intro H. inversion H; subst. eauto. Qed.

Lemma inv_zero ρ Γ T α : D ρ Γ izero T α -> T = TN.
Proof. intro H. inversion H; auto. Qed.

Lemma lev_dom A B : S (lev A) <= lev (TAr A B).
Proof. apply Nat.le_max_l. Qed.

Lemma lev_cod A B : lev B <= lev (TAr A B).
Proof. apply Nat.le_max_r. Qed.

Local Open Scope ord_scope.

Lemma VF_ind (P : VForm -> Prop) : (forall a, (forall b, b ◃ a -> P b) -> P a) -> forall a, P a.
Proof.
  intros H a.
  induction a as [a IH] using (well_founded_induction (wf_inverse_image VForm Ord ord_lt sz ord_lt_wf)).
  apply H. exact IH.
Qed.

Lemma vplus_mono (a b c d:VForm) : a ⊴ b -> c ⊴ d -> vplus a c ⊴ vplus b d.
Proof. intros H1 H2. rewrite !vplus_eq. apply addOrd_monotone; auto. Qed.

Lemma vsucc_mono (a b:VForm) : a ⊴ b -> vsucc a ⊴ vsucc b.
Proof. intro H. rewrite !vsucc_eq. apply succ_monotone. exact H. Qed.

Lemma vsucc_plus_le (a b c:VForm) : b ◃ c -> vsucc (vplus a b) ⊴ vplus a c.
Proof.
  intro H. rewrite vsucc_eq, !vplus_eq. rewrite <- addOrd_succ.
  apply addOrd_monotone; [reflexivity | apply succ_least; exact H].
Qed.

Lemma lt_sum_l (a b:VForm) : a ◃ vsucc (vplus a b).
Proof. eapply ord_le_lt_trans; [apply vplus_le1 | apply vsucc_lt]. Qed.

Lemma lt_sum_r (a b:VForm) : b ◃ vsucc (vplus a b).
Proof. eapply ord_le_lt_trans; [apply vplus_le2 | apply vsucc_lt]. Qed.

Lemma lt_sum_r' (a b c:VForm) : c ◃ b -> c ◃ vsucc (vplus a b).
Proof. intro H. eapply ord_lt_le_trans; [exact H | apply ord_lt_le; apply lt_sum_r]. Qed.

(** [a + b + 1] grows strictly in [b]; used in the commuting cases. *)
Lemma sum_step (a b c:VForm) : b ◃ c -> vsucc (vplus a b) ◃ vsucc (vplus a c).
Proof. intro H. eapply ord_le_lt_trans; [apply vsucc_plus_le; exact H | apply vsucc_lt]. Qed.

Local Open Scope nat_scope.

(** ** The reduction lemma for β and the commuting conversion

    For [M : A → B] and [N : A] of cut rank [ρ], with [lev (A → B) ≤ ρ+1],
    [app_red A B M N] has cut rank [ρ] and height [h N + h M + 1].  The
    proof is by transfinite induction on the height of [M]: the commuting
    case recurses into the branches of an ω-term, two levels down. *)

Theorem app_red_typed ρ Γ A B N γ2 : D ρ Γ N A γ2 -> lev (TAr A B) <= S ρ ->
  forall γ1 M, D ρ Γ M (TAr A B) γ1 -> D ρ Γ (app_red A B M N) B (vsucc (vplus γ2 γ1)).
Proof.
  intros HN Hl.
  assert (HlA : lev A <= ρ) by (pose proof (lev_dom A B); lia).
  assert (Hρ : 1 <= ρ) by (pose proof (lev_pos A); lia).
  intro γ1. induction γ1 as [γ1 IH] using VF_ind. intros M HM.
  destruct M as [x | A' K | A0 B0 M1 K | | K | C f]; simpl.
  - apply D_app with (β1 := γ1) (β2 := γ2); [exact HM | exact HN | apply lt_sum_r | apply lt_sum_l |].
    apply cut_ok_vh; reflexivity.
  - destruct (inv_lam _ _ _ _ _ _ HM) as [B' [β [E [HK Hβ]]]]. injection E as E1 E2; subst A' B'.
    eapply D_height; [apply (subst_typed _ _ _ _ _ HK [] Γ A N γ2); auto |].
    apply ord_lt_le. eapply ord_le_lt_trans; [|apply vsucc_lt].
    apply vplus_mono; [reflexivity | apply ord_lt_le; exact Hβ].
  - destruct (inv_app _ _ _ _ _ _ _ _ HM) as [E [β1 [β2 [HM1 [HK [Hb1 [Hb2 Hc]]]]]]]. subst B0.
    assert (Hdef : D ρ Γ (iapp A B (iapp A0 (TAr A B) M1 K) N) B (vsucc (vplus γ2 γ1))
              \/ is_om M1 = true).
    { destruct (cut_ok_cases _ _ _ _ _ Hc) as [Hv | [[Ho _] | Hl']]; [left | right; exact Ho | left].
      - apply D_app with (β1 := γ1) (β2 := γ2); [exact HM | exact HN | apply lt_sum_r | apply lt_sum_l |].
        apply cut_ok_vh; exact Hv.
      - apply D_app with (β1 := γ1) (β2 := γ2); [exact HM | exact HN | apply lt_sum_r | apply lt_sum_l |].
        apply cut_ok_lev. eapply Nat.le_trans; [apply lev_cod | exact Hl']. }
    destruct M1 as [ | | | | | C f];
      try (destruct Hdef as [Hdef | Hdef]; [exact Hdef | discriminate]).
    destruct (inv_omega _ _ _ _ _ _ HM1) as [E [δ [Hf Hδ]]]. injection E as E1 E2; subst A0 C.
    apply D_app with (β1 := vsucc (vplus γ2 β1)) (β2 := β2).
    + apply D_omega with (β := fun n => vsucc (vplus γ2 (δ n))).
      * intro n. apply IH; [eapply ord_lt_trans; eauto | apply Hf].
      * intro n. apply sum_step. auto.
    + exact HK.
    + apply sum_step. exact Hb1.
    + apply lt_sum_r'. exact Hb2.
    + apply cut_ok_om; [reflexivity | right; exact Hρ].
  - apply inv_zero in HM. discriminate.
  - apply inv_succ in HM. destruct HM; discriminate.
  - destruct (inv_omega _ _ _ _ _ _ HM) as [E [δ [Hf Hδ]]]. injection E as E1 E2; subst A C.
    apply D_app with (β1 := γ1) (β2 := γ2); [exact HM | exact HN | apply lt_sum_r | apply lt_sum_l |].
    apply cut_ok_om; [reflexivity | right; exact Hρ].
Qed.

(** ** The reduction lemma for ω-redexes

    At cut rank [0], an ω-term applied to a normal argument of type
    [nat] reduces to cut rank [0], with height [h(Ω f) + h N + 1]; by
    transfinite induction on the height of [N]. *)

Theorem omega_red_typed Γ A B C : forall γ2 N f γ1,
  D 0 Γ (iomega C f) (TAr A B) γ1 -> D 0 Γ N A γ2 ->
  D 0 Γ (omega_red A B C f N) B (vsucc (vplus γ1 γ2)).
Proof.
  intro γ2. induction γ2 as [γ2 IH] using VF_ind. intros N f γ1 Hf HN.
  destruct (inv_omega _ _ _ _ _ _ Hf) as [E [δ [Hδ Hδlt]]]. injection E as E1 E2; subst A C.
  destruct N as [x | A' K | A0 B0 N1 K | | K | E g]; simpl.
  - apply D_app with (β1 := γ1) (β2 := γ2); [exact Hf | exact HN | apply lt_sum_l | apply lt_sum_r |].
    apply cut_ok_om; [reflexivity | left; reflexivity].
  - destruct (inv_lam _ _ _ _ _ _ HN) as [? [? [E _]]]. discriminate.
  - destruct (inv_app _ _ _ _ _ _ _ _ HN) as [E0 [β1 [β2 [HN1 [HK [Hb1 [Hb2 Hc]]]]]]]. subst B0.
    assert (Hdef : D 0 Γ (iapp TN B (iomega B f) (iapp A0 TN N1 K)) B (vsucc (vplus γ1 γ2))
              \/ is_om N1 = true).
    { destruct (cut_ok_cases _ _ _ _ _ Hc) as [Hv | [[Ho _] | Hl']]; [left | right; exact Ho |].
      - apply D_app with (β1 := γ1) (β2 := γ2); [exact Hf | exact HN | apply lt_sum_l | apply lt_sum_r |].
        apply cut_ok_om; [reflexivity | left; exact Hv].
      - pose proof (lev_pos (TAr A0 TN)). lia. }
    destruct N1 as [ | | | | | E g];
      try (destruct Hdef as [Hdef | Hdef]; [exact Hdef | discriminate]).
    destruct (inv_omega _ _ _ _ _ _ HN1) as [E' [δ' [Hg Hδ']]]. injection E' as E1 E2; subst A0 E.
    assert (HvK : isvh K = true).
    { destruct (cut_ok_cases _ _ _ _ _ Hc) as [Hv | [[_ [Hv | Hv]] | Hl']];
        [discriminate | exact Hv | lia | pose proof (lev_pos (TAr TN TN)); lia]. }
    apply D_app with (β1 := vsucc (vplus γ1 β1)) (β2 := β2).
    + apply D_omega with (β := fun n => vsucc (vplus γ1 (δ' n))).
      * intro n. apply IH; [eapply ord_lt_trans; eauto | exact Hf | apply Hg].
      * intro n. apply sum_step. auto.
    + exact HK.
    + apply sum_step. exact Hb1.
    + apply lt_sum_r'. exact Hb2.
    + apply cut_ok_om; [reflexivity | left; exact HvK].
  - eapply D_height; [apply (Hδ 0%nat) |]. apply ord_lt_le.
    eapply ord_lt_le_trans; [apply Hδlt | apply ord_lt_le; apply lt_sum_l].
  - destruct (inv_succ _ _ _ _ _ HN) as [_ [β [HK Hβ]]].
    eapply D_height; [apply (IH β Hβ K (fun n => f (S n)) γ1) |].
    + apply D_omega with (β := fun n => δ (S n)); auto.
    + exact HK.
    + apply vsucc_mono. apply vplus_mono; [reflexivity | apply ord_lt_le; exact Hβ].
  - destruct (inv_omega _ _ _ _ _ _ HN) as [E' _]. discriminate.
Qed.

(** ** One pass of cut elimination

    A derivation of cut rank [ρ+1] and height [α] becomes one of cut rank
    [ρ] and height [ω^α].  At an application, both sides are eliminated
    (heights [ω^β1], [ω^β2] with [β1, β2 < α]); a remaining cut of level
    [ρ+1] is reduced, at height [ω^β1 + ω^β2 + 1 < ω^α]. *)

Theorem elim_typed ρ Γ M T α : D (S ρ) Γ M T α ->
  D ρ Γ (elim ρ M) T (vexp α) /\
  (isvh M = true -> isvh (elim ρ M) = true) /\
  (is_om M = true -> is_om (elim ρ M) = true).
Proof.
  intro H. induction H as [Γ x A α Hx | Γ A M B β α HM IH Hβ
                         | Γ A B M N β1 β2 α HM IHM HN IHN Hb1 Hb2 Hc
                         | Γ α | Γ M β α HM IH Hβ | Γ C f β α Hf IH Hβ]; simpl.
  - split; [constructor; auto | split; auto].
  - destruct IH as [IH _]. split; [econstructor; [exact IH | apply vexp_increasing; exact Hβ] |].
    split; discriminate.
  - destruct IHM as [HM' [HvM HoM]]. destruct IHN as [HN' _].
    assert (Hpos : Z ◃ α) by (eapply ord_le_lt_trans; [apply zero_least | exact Hb1]).
    assert (Hb1' := vexp_increasing _ _ Hb1). assert (Hb2' := vexp_increasing _ _ Hb2).
    destruct (cut_ok ρ A B (elim ρ M) (elim ρ N)) eqn:Hc'.
    { split; [econstructor; eauto | split; [exact HvM | discriminate]]. }
    split; [| split; intro Hv; [rewrite (cut_ok_vh _ _ _ _ _ (HvM Hv)) in Hc'; discriminate
                              | discriminate]].
    destruct (is_om (elim ρ M)) eqn:Hom.
    + (* an ω-redex: only possible at [ρ = 0] *)
      destruct ρ as [|ρ]; [| rewrite (cut_ok_om _ A B _ (elim (S ρ) N) Hom (or_intror (le_n_S _ _ (Nat.le_0_l ρ)))) in Hc'; discriminate].
      destruct (elim 0 M) as [ | | | | | C f] eqn:EM; try discriminate.
      eapply D_height; [apply (omega_red_typed _ _ _ _ _ _ _ _ HM' HN') |].
      apply ord_lt_le. apply below_exp_sum; auto.
    + assert (Hl : lev (TAr A B) <= S ρ).
      { destruct (cut_ok_cases _ _ _ _ _ Hc) as [Hv | [[Ho _] | Hl]]; auto.
        - pose proof (cut_ok_vh ρ A B _ (elim ρ N) (HvM Hv)) as X. congruence.
        - pose proof (HoM Ho) as X. congruence. }
      assert (E : match elim ρ M with
                  | iomega C f => omega_red A B C f (elim ρ N)
                  | _ => app_red A B (elim ρ M) (elim ρ N) end
                  = app_red A B (elim ρ M) (elim ρ N))
        by (destruct (elim ρ M); simpl in Hom; congruence).
      rewrite E.
      eapply D_height; [apply (app_red_typed _ _ _ _ _ _ HN' Hl _ _ HM') |].
      apply ord_lt_le. apply below_exp_sum; auto.
  - split; [constructor | split; discriminate].
  - destruct IH as [IH _]. split; [econstructor; [exact IH | apply vexp_increasing; exact Hβ] |].
    split; discriminate.
  - split; [| split; [discriminate | reflexivity]].
    apply D_omega with (β := fun n => vexp (β n)).
    + intro n. apply IH.
    + intro n. apply vexp_increasing. auto.
Qed.

(** Iterating: cut rank [ρ] and height [α] give a normal derivation of
    height [tower ρ α = ω^ω^...^α]. *)
Theorem norm_typed : forall ρ Γ M T α, D ρ Γ M T α -> D 0 Γ (norm ρ M) T (tower ρ α).
Proof.
  induction ρ as [|ρ IH]; intros Γ M T α H; simpl; auto.
  apply IH. apply elim_typed. exact H.
Qed.

(** ** Closed normal terms of type [nat] are numerals *)

Lemma closed_head ρ M T α : D ρ [] M T α -> head_var M = None.
Proof.
  remember [] as Γ. intro H. induction H; subst; simpl; auto.
  destruct x; discriminate.
Qed.

Theorem canonical_nat M α : D 0 [] M TN α -> exists k, M = inum k.
Proof.
  remember [] as Γ. remember TN as T. intro H.
  induction H as [Γ x A α Hx | | Γ A B M N β1 β2 α HM _ HN _ _ _ Hc | Γ α
                 | Γ M β α HM IH _ |]; subst; try discriminate.
  - destruct x; discriminate.
  - exfalso. assert (HvM : isvh M = false) by (unfold isvh; rewrite (closed_head _ _ _ _ HM); auto).
    assert (HvN : isvh N = false) by (unfold isvh; rewrite (closed_head _ _ _ _ HN); auto).
    destruct (cut_ok_cases _ _ _ _ _ Hc) as [Hv | [[_ [Hv | Hv]] | Hl]]; try congruence; try lia.
    pose proof (lev_pos (TAr A TN)). lia.
  - exists 0. reflexivity.
  - destruct IH as [k ->]; auto. exists (S k). reflexivity.
Qed.

(** ** System T *)

Inductive term : Set :=
| var : nat -> term
| lam : ty -> term -> term
| app : ty -> ty -> term -> term -> term
| zero : term
| succ : term -> term
| rec : ty -> term -> term -> term -> term.   (* [rec C z s t] *)

Inductive typing : list ty -> term -> ty -> Prop :=
| T_var Γ x A : nth_error Γ x = Some A -> typing Γ (var x) A
| T_lam Γ A t B : typing (A :: Γ) t B -> typing Γ (lam A t) (TAr A B)
| T_app Γ A B t u : typing Γ t (TAr A B) -> typing Γ u A -> typing Γ (app A B t u) B
| T_zero Γ : typing Γ zero TN
| T_succ Γ t : typing Γ t TN -> typing Γ (succ t) TN
| T_rec Γ C z s t :
    typing Γ z C -> typing Γ s (TAr TN (TAr C C)) -> typing Γ t TN ->
    typing Γ (rec C z s t) C.

(** The [n]-th unfolding of the recursor: [s (n-1) (... (s 0 z))]. *)
Fixpoint iter (C:ty) (z s:iterm) (n:nat) : iterm :=
  match n with
  | O => z
  | S n => iapp C C (iapp TN (TAr C C) s (inum n)) (iter C z s n)
  end.

Fixpoint tr (t:term) : iterm :=
  match t with
  | var x => ivar x
  | lam A t => ilam A (tr t)
  | app A B t u => iapp A B (tr t) (tr u)
  | zero => izero
  | succ t => isucc (tr t)
  | rec C z s t => iapp TN C (iomega C (iter C (tr z) (tr s))) (tr t)
  end.

Fixpoint vnat (n:nat) : VForm := match n with O => Z | S n => vsucc (vnat n) end.

(** The heights of translations are below [ω^ω]: [hexp t] is a finite
    exponent with [h t < ω^(hexp t)] ([h_below]). *)
Fixpoint hexp (t:term) : nat :=
  match t with
  | var _ | zero => 1
  | lam _ t | succ t => hexp t
  | app _ _ t u => Nat.max (hexp t) (hexp u)
  | rec _ z s t => S (Nat.max (S (Nat.max (hexp z) (hexp s))) (hexp t))
  end.

(** The height of the translation.  The ω-term for [rec C z s t] has
    height [ω^(m+1) = ω^m · ω], where [m = max (hexp z) (hexp s)]: its
    [n]-th branch is a sum of [h z], [n] copies of [h s] and some finite
    parts, all below [ω^m]. *)
Fixpoint h (t:term) : VForm :=
  match t with
  | var _ => Z
  | lam _ t => vsucc (h t)
  | app _ _ t u => vsucc (vplus (h t) (h u))
  | zero => Z
  | succ t => vsucc (h t)
  | rec _ z s t => vsucc (vplus (vexp (vnat (S (Nat.max (hexp z) (hexp s))))) (h t))
  end.

(** The cut rank of the translation: the largest level of a type at
    which [t] eliminates (at least [1], for the ω-redexes). *)
Fixpoint tlev (t:term) : nat :=
  match t with
  | var _ | zero => 1
  | lam _ t | succ t => tlev t
  | app A B t u => Nat.max (lev (TAr A B)) (Nat.max (tlev t) (tlev u))
  | rec C z s t =>
      Nat.max (lev (TAr TN (TAr C C))) (Nat.max (tlev z) (Nat.max (tlev s) (tlev t)))
  end.

(** The ordinal of a term: the height of its normal form. *)
Definition ord_of (t:term) : VForm := tower (tlev t) (h t).

Fixpoint ib (hz hs:VForm) (n:nat) : VForm :=
  match n with
  | O => hz
  | S n => vsucc (vplus (ib hz hs n) (vplus hs (vnat (S n))))
  end.

Lemma inum_typed ρ Γ n : D ρ Γ (inum n) TN (vnat n).
Proof. induction n; simpl; econstructor; eauto. apply vsucc_lt. Qed.

Lemma iter_typed ρ Γ C z s hz hs :
  D ρ Γ z C hz -> D ρ Γ s (TAr TN (TAr C C)) hs -> lev (TAr TN (TAr C C)) <= ρ ->
  forall n, D ρ Γ (iter C z s n) C (ib hz hs n).
Proof.
  intros Hz Hs Hl n. induction n as [|n IH]; cbn [iter ib]; auto.
  apply D_app with (β1 := vplus hs (vnat (S n))) (β2 := ib hz hs n).
  - apply D_app with (β1 := hs) (β2 := vnat n); [exact Hs | apply inum_typed | | |].
    + rewrite vplus_eq. rewrite <- addOrd_zero_r at 1. apply addOrd_increasing.
      cbn [vnat]. rewrite vsucc_eq. apply ord_le_lt_trans with (sz (vnat n)); [apply zero_least | apply succ_lt].
    + eapply ord_lt_le_trans; [apply vsucc_lt | apply vplus_le2].
    + apply cut_ok_lev. auto.
  - exact IH.
  - apply lt_sum_r.
  - apply lt_sum_l.
  - apply cut_ok_lev. eapply Nat.le_trans; [apply lev_cod | exact Hl].
Qed.

Local Open Scope ord_scope.

Lemma vnat_eq n : sz (vnat n) ≈ natOrdSize n.
Proof. induction n as [|n IH]; cbn [vnat natOrdSize]; [reflexivity|]. rewrite vsucc_eq, IH. reflexivity. Qed.

Lemma vnat_lt m n : (m < n)%nat -> vnat m ◃ vnat n.
Proof. intro H. rewrite !vnat_eq. apply natOrdSize_increasing. exact H. Qed.

Lemma vnat_le m n : (m <= n)%nat -> vnat m ⊴ vnat n.
Proof. intro H. rewrite !vnat_eq. apply natOrdSize_monotone. exact H. Qed.

Lemma vexp_mono (a b:VForm) : a ⊴ b -> vexp a ⊴ vexp b.
Proof. intro H. rewrite !vexp_eq. apply expOrd_monotone. exact H. Qed.

Lemma Z_lt_vnat n : (1 <= n)%nat -> Z ◃ vnat n.
Proof. intro H. apply (vnat_lt 0 n). lia. Qed.

Lemma vnat_below (K:VForm) n : Z ◃ K -> vnat n ◃ vexp K.
Proof.
  intro HK. induction n as [|n IH]; cbn [vnat].
  - rewrite vexp_eq. apply expOrd_nonzero.
  - unfold vsucc. rewrite vplus_eq. rewrite (vexp_eq K) in *. apply below_exp_add; auto.
    rewrite vexp_eq. apply expOrd_increasing; [apply omega_gt1 | exact HK].
Qed.

(** The branches of the ω-term for a recursor are below [ω^K], as soon
    as [h z] and [h s] are. *)
Lemma ib_below hz hs K n :
  hz ◃ vexp K -> hs ◃ vexp K -> Z ◃ K -> ib hz hs n ◃ vexp K.
Proof.
  intros Hz Hs Hpos.
  induction n as [|n IH]; cbn [ib]; auto.
  apply below_exp_sum; auto.
  rewrite vplus_eq. rewrite (vexp_eq K) in *. apply below_exp_add; auto.
  rewrite <- vexp_eq. apply vnat_below. exact Hpos.
Qed.

Lemma hexp_pos t : (1 <= hexp t)%nat.
Proof. induction t; simpl; lia. Qed.

Lemma below_vexp_vnat (a:VForm) m n : a ◃ vexp (vnat m) -> (m <= n)%nat -> a ◃ vexp (vnat n).
Proof. intros H Hmn. eapply ord_lt_le_trans; [exact H | apply vexp_mono, vnat_le, Hmn]. Qed.

Theorem h_below t : h t ◃ vexp (vnat (hexp t)).
Proof.
  induction t as [x | A t IH | A B t IHt u IHu | | t IH | C z IHz s IHs t IHt]; cbn [h hexp].
  - rewrite vexp_eq. apply expOrd_nonzero.
  - apply ord_le_lt_trans with (sz (vsucc (vplus (h t) Z))).
    + apply vsucc_mono. apply vplus_le1.
    + apply below_exp_sum; auto. rewrite vexp_eq. apply expOrd_nonzero.
      apply Z_lt_vnat, hexp_pos.
  - apply below_exp_sum.
    + eapply below_vexp_vnat; [exact IHt | apply Nat.le_max_l].
    + eapply below_vexp_vnat; [exact IHu | apply Nat.le_max_r].
    + apply Z_lt_vnat. pose proof (hexp_pos t). lia.
  - rewrite vexp_eq. apply expOrd_nonzero.
  - apply ord_le_lt_trans with (sz (vsucc (vplus (h t) Z))).
    + apply vsucc_mono. apply vplus_le1.
    + apply below_exp_sum; auto. rewrite vexp_eq. apply expOrd_nonzero.
      apply Z_lt_vnat, hexp_pos.
  - apply below_exp_sum.
    + apply vexp_increasing. apply vnat_lt. lia.
    + eapply below_vexp_vnat; [exact IHt | lia].
    + apply Z_lt_vnat. lia.
Qed.

(** [ω] as a V form. *)
Definition vω : VForm := vexp (vnat 1).

Lemma vω_eq : sz vω ≈ ω.
Proof.
  unfold vω. rewrite vexp_eq, vnat_eq. apply expOrd_one'. apply omega_gt0.
Qed.

(** So the heights of translations are below [ω^ω]. *)
Theorem h_below_ω_ω t : h t ◃ vexp vω.
Proof.
  eapply ord_lt_le_trans; [apply h_below|]. apply vexp_mono.
  apply ord_lt_le. rewrite vω_eq, vnat_eq. apply index_lt.
Qed.

Lemma tower_increasing k : forall a b, a ◃ b -> tower k a ◃ tower k b.
Proof.
  induction k as [|k IH]; intros a b H; simpl; auto. apply IH. apply vexp_increasing. exact H.
Qed.

Local Open Scope nat_scope.

Lemma tlev_pos t : 1 <= tlev t.
Proof.
  induction t; simpl; auto.
  - pose proof (lev_pos (TAr t1 t2)). lia.
  - pose proof (lev_pos (TAr TN (TAr t1 t1))). lia.
Qed.

(** The translation of a term [t] has cut rank [tlev t] and height [h t]. *)
Theorem tr_typed Γ t A : typing Γ t A -> D (tlev t) Γ (tr t) A (h t).
Proof.
  intro H. induction H as [Γ x A Hx | Γ A t B Ht IH | Γ A B t u Ht IHt Hu IHu | Γ
                         | Γ t Ht IH | Γ C z s t Hz IHz Hs IHs Ht IHt]; cbn [tr h tlev].
  - constructor. exact Hx.
  - econstructor; [exact IH | apply vsucc_lt].
  - apply D_app with (β1 := h t) (β2 := h u).
    + eapply D_mono; [exact IHt | | reflexivity]. rewrite <- Nat.le_max_r. apply Nat.le_max_l.
    + eapply D_mono; [exact IHu | | reflexivity]. rewrite <- Nat.le_max_r. apply Nat.le_max_r.
    + apply lt_sum_l.
    + apply lt_sum_r.
    + apply cut_ok_lev. apply Nat.le_max_l.
  - constructor.
  - econstructor; [exact IH | apply vsucc_lt].
  - set (ρ := Nat.max (lev (TAr TN (TAr C C))) (Nat.max (tlev z) (Nat.max (tlev s) (tlev t)))).
    set (m := Nat.max (hexp z) (hexp s)).
    assert (Hl : lev (TAr TN (TAr C C)) <= ρ) by apply Nat.le_max_l.
    assert (Hz' : tlev z <= ρ) by (unfold ρ; lia).
    assert (Hs' : tlev s <= ρ) by (unfold ρ; lia).
    assert (Ht' : tlev t <= ρ) by (unfold ρ; lia).
    apply D_app with (β1 := vexp (vnat (S m))) (β2 := h t).
    + apply D_omega with (β := ib (h z) (h s)).
      * apply iter_typed; auto.
        -- eapply D_mono; [exact IHz | exact Hz' | reflexivity].
        -- eapply D_mono; [exact IHs | exact Hs' | reflexivity].
      * intro n. apply ib_below.
        -- eapply below_vexp_vnat; [apply h_below | unfold m; lia].
        -- eapply below_vexp_vnat; [apply h_below | unfold m; lia].
        -- apply Z_lt_vnat. lia.
    + eapply D_mono; [exact IHt | exact Ht' | reflexivity].
    + apply lt_sum_l.
    + apply lt_sum_r.
    + apply cut_ok_om; [reflexivity | right]. pose proof (lev_pos (TAr TN (TAr C C))). lia.
Qed.

(** ** The ordinal analysis

    Every term [t] of System T normalizes, through its infinitary
    translation, to a normal derivation of height [ord_of t], a tower of
    [tlev t] exponentials over [h t < ω^ω].  It is a V form, hence below
    ε₀; more precisely it is below the tower [ω_{tlev t + 2}] of
    [tlev t + 1] exponentials over [ω]. *)

Theorem T_normalization Γ t A : typing Γ t A ->
  D 0 Γ (norm (tlev t) (tr t)) A (ord_of t) /\ red (tr t) (norm (tlev t) (tr t)).
Proof.
  intro H. split; [apply norm_typed; apply tr_typed; exact H | apply norm_red].
Qed.

Theorem ord_of_bound t : (ord_of t ◃ tower (S (tlev t)) vω)%ord.
Proof. unfold ord_of. cbn [tower]. apply tower_increasing. apply h_below_ω_ω. Qed.

Theorem ord_of_below_ε0 t : (sz (ord_of t) < ε 0)%ord.
Proof. apply VNotation_below_ε₀. Qed.

(** Every closed term of type [nat] reduces to a numeral. *)
Theorem T_total t : typing [] t TN ->
  exists k, norm (tlev t) (tr t) = inum k /\ red (tr t) (inum k).
Proof.
  intro H. destruct (T_normalization _ _ _ H) as [Hn Hr].
  destruct (canonical_nat _ _ Hn) as [k Hk]. exists k. rewrite Hk in Hr. auto.
Qed.

(** For example, doubling by recursion: [rec 0 (λ_ y. S (S y)) 3]
    normalizes to [6] in [tlev = 2] passes. *)
Example double_three :
  norm (tlev (rec TN zero (lam TN (lam TN (succ (succ (var 0))))) (succ (succ (succ zero)))))
       (tr (rec TN zero (lam TN (lam TN (succ (succ (var 0))))) (succ (succ (succ zero)))))
  = inum 6.
Proof. reflexivity. Qed.
