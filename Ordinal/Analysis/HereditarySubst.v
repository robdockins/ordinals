From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wellfounded.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.

Open Scope ord_scope.

(** * Termination of hereditary substitution, by an ordinal measure

    Hereditary substitution [[M/x]^τ N] substitutes the canonical term [M]
    of type [τ] for the variable [x] in the canonical term [N], and reduces
    every redex this creates on the spot, so that the result is canonical
    again (Watkins, Cervesato, Pfenning and Walker, CMU-CS-02-101).  Its
    termination is usually argued by a lexicographic induction on the type
    [τ] and then on [N], or obtained from nested structural recursion
    (Keller and Altenkirch, MSFP 2010).  Here the same argument is given as
    a single ordinal measure in [Ord]:

    - the ordinal of a type is [|base| = 0] and
      [|a → b| = (|a| ⊔ |b|) + ω], that is [ω · height] ([tyOrd_eq]);
    - substituting into a term or spine [N] at type [τ] has measure
      [|τ| + size N], and applying a substituted term to a spine at type
      [τ] has measure [|τ|].

    Every recursive call decreases the measure ([measure_*]), and every
    measure at type [τ] lies below [ω · (height τ + 1)], hence below [ω²]
    ([measure_bound]).  Termination is the totality of the graph [HS] of the
    equations ([hsub_total]), by well-founded induction on the measure; the
    equations themselves then hold by determinism of [HS]
    ([hsub_lam], ...).  As the CLF report observes, termination does not
    depend on typing: ill-typed applications simply return their head. *)

(** ** Simple types and canonical terms in spine form *)

Inductive ty : Set :=
| base : ty
| arr : ty -> ty -> ty.

Fixpoint height (τ:ty) : nat :=
  match τ with
  | base => 0
  | arr a b => S (Nat.max (height a) (height b))
  end.

(** Canonical terms, with de Bruijn indices: [lam t], or a variable
    applied to a spine of arguments. *)
Inductive nf : Set :=
| lam : nf -> nf
| ne : nat -> spine -> nf
with spine : Set :=
| snil : spine
| scons : nf -> spine -> spine.

Fixpoint size (t:nf) : nat :=
  match t with
  | lam t => S (size t)
  | ne _ sp => S (size_sp sp)
  end
with size_sp (sp:spine) : nat :=
  match sp with
  | snil => 0
  | scons t sp => S (size t + size_sp sp)
  end.

(** Shifting the free variables [≥ k] up by one. *)
Fixpoint lift (k:nat) (t:nf) : nf :=
  match t with
  | lam t => lam (lift (S k) t)
  | ne y sp => ne (if y <? k then y else S y) (lift_sp k sp)
  end
with lift_sp (k:nat) (sp:spine) : spine :=
  match sp with
  | snil => snil
  | scons t sp => scons (lift k t) (lift_sp k sp)
  end.

(** After substituting for [x], the variables above [x] move down. *)
Definition unshift (x y:nat) : nat := if y <? x then y else pred y.

(** ** The graph of hereditary substitution

    There are three kinds of call: substitution into a term, substitution
    into a spine, and application of a substituted term to a spine. *)

Inductive call : Set :=
| CH : ty -> nf -> nat -> nf -> call       (* [[M/x]^τ N]   *)
| CS : ty -> nf -> nat -> spine -> call    (* [[M/x]^τ sp]  *)
| CA : ty -> nf -> spine -> call.          (* [M · sp] at τ *)

Inductive res : Set :=
| rn : nf -> res
| rs : spine -> res.

Inductive HS : call -> res -> Prop :=
| hs_lam τ M x t r :
    HS (CH τ (lift 0 M) (S x) t) (rn r) ->
    HS (CH τ M x (lam t)) (rn (lam r))
| hs_var τ M x y sp sp' :
    x <> y ->
    HS (CS τ M x sp) (rs sp') ->
    HS (CH τ M x (ne y sp)) (rn (ne (unshift x y) sp'))
| hs_head τ M x sp sp' r :
    HS (CS τ M x sp) (rs sp') ->
    HS (CA τ M sp') (rn r) ->
    HS (CH τ M x (ne x sp)) (rn r)
| hs_snil τ M x :
    HS (CS τ M x snil) (rs snil)
| hs_scons τ M x t sp t' sp' :
    HS (CH τ M x t) (rn t') ->
    HS (CS τ M x sp) (rs sp') ->
    HS (CS τ M x (scons t sp)) (rs (scons t' sp'))
| ha_nil τ M :
    HS (CA τ M snil) (rn M)
| ha_beta a b t N sp r1 r :
    HS (CH a N 0 t) (rn r1) ->
    HS (CA b r1 sp) (rn r) ->
    HS (CA (arr a b) (lam t) (scons N sp)) (rn r)
| ha_base M N sp :
    HS (CA base M (scons N sp)) (rn M)
| ha_ne a b y sp0 N sp :
    HS (CA (arr a b) (ne y sp0) (scons N sp)) (rn (ne y sp0)).

Lemma HS_det : forall c r1, HS c r1 -> forall r2, HS c r2 -> r1 = r2.
Proof.
  intros c r1 H. induction H; intros r2 H2; inversion H2; subst; try congruence;
    repeat match goal with
           | IH : forall r2, HS ?c r2 -> _ = r2, H : HS ?c _ |- _ =>
               apply IH in H; inversion H; subst; clear IH
           end; try reflexivity; try congruence.
Qed.

(** Calls on terms and applications return terms, calls on spines return
    spines. *)
Definition res_ok (c:call) (r:res) : Prop :=
  match c, r with
  | CS _ _ _ _, rs _ => True
  | CS _ _ _ _, rn _ => False
  | _, rn _ => True
  | _, rs _ => False
  end.

Lemma HS_res_ok c r : HS c r -> res_ok c r.
Proof. intro H; destruct H; simpl; auto. Qed.

(** ** The ordinal measure *)

Fixpoint tyOrd (τ:ty) : Ord :=
  match τ with
  | base => 0
  | arr a b => (tyOrd a ⊔ tyOrd b) + ω
  end.

Definition measure (c:call) : Ord :=
  match c with
  | CH τ _ _ N => tyOrd τ + natOrdSize (size N)
  | CS τ _ _ sp => tyOrd τ + natOrdSize (size_sp sp)
  | CA τ _ _ => tyOrd τ
  end.

Lemma tyOrd_dom a b k : tyOrd a + natOrdSize k < tyOrd (arr a b).
Proof.
  simpl. apply ord_lt_le_trans with (tyOrd a + ω).
  - apply addOrd_increasing. apply (index_lt ω k).
  - apply addOrd_monotone; auto with ord.
Qed.

Lemma tyOrd_cod a b : tyOrd b < tyOrd (arr a b).
Proof.
  simpl. apply ord_le_lt_trans with (tyOrd a ⊔ tyOrd b); [apply lub_le2|].
  rewrite <- (addOrd_zero_r (tyOrd a ⊔ tyOrd b)) at 1.
  apply addOrd_increasing. apply omega_gt0.
Qed.

Lemma add_nat_lt α m n : (m < n)%nat -> α + natOrdSize m < α + natOrdSize n.
Proof. intro H. apply addOrd_increasing. apply natOrdSize_increasing; auto. Qed.

(** Every recursive call decreases the measure. *)
Lemma measure_lam τ M x t : measure (CH τ (lift 0 M) (S x) t) < measure (CH τ M x (lam t)).
Proof. apply add_nat_lt. simpl. lia. Qed.

Lemma measure_spine τ M x y sp : measure (CS τ M x sp) < measure (CH τ M x (ne y sp)).
Proof. apply add_nat_lt. simpl. lia. Qed.

Lemma measure_head τ M x sp sp' : measure (CA τ M sp') < measure (CH τ M x (ne x sp)).
Proof.
  unfold measure. apply ord_le_lt_trans with (tyOrd τ + natOrdSize 0).
  - apply addOrd_le1.
  - apply add_nat_lt. simpl. lia.
Qed.

Lemma measure_scons_hd τ M x t sp : measure (CH τ M x t) < measure (CS τ M x (scons t sp)).
Proof. apply add_nat_lt. simpl. lia. Qed.

Lemma measure_scons_tl τ M x t sp : measure (CS τ M x sp) < measure (CS τ M x (scons t sp)).
Proof. apply add_nat_lt. simpl. lia. Qed.

Lemma measure_beta_arg a b N t M sp : measure (CH a N 0 t) < measure (CA (arr a b) M sp).
Proof. apply tyOrd_dom. Qed.

Lemma measure_beta_rest a b r1 M sp sp' : measure (CA b r1 sp) < measure (CA (arr a b) M sp').
Proof. apply tyOrd_cod. Qed.

(** ** Termination: the graph is total *)

Theorem hsub_total : forall c, { r | HS c r }.
Proof.
  apply (well_founded_induction_type
           (wf_inverse_image _ _ ord_lt measure ord_lt_wf)).
  intros c IH.
  destruct c as [τ M x N | τ M x sp | τ M sp].
  - destruct N as [t | y sp].
    + destruct (IH _ (measure_lam τ M x t)) as [[r|s] Hr];
        [| exfalso; exact (HS_res_ok _ _ Hr)].
      exists (rn (lam r)). constructor; auto.
    + destruct (IH _ (measure_spine τ M x y sp)) as [[t|sp'] Hsp];
        [exfalso; exact (HS_res_ok _ _ Hsp) |].
      destruct (Nat.eq_dec x y) as [<-|Hxy].
      * destruct (IH _ (measure_head τ M x sp sp')) as [[r|s] Hr];
          [| exfalso; exact (HS_res_ok _ _ Hr)].
        exists (rn r). econstructor; eauto.
      * exists (rn (ne (unshift x y) sp')). constructor; auto.
  - destruct sp as [| t sp].
    + exists (rs snil). constructor.
    + destruct (IH _ (measure_scons_hd τ M x t sp)) as [[t'|s] Ht];
        [| exfalso; exact (HS_res_ok _ _ Ht)].
      destruct (IH _ (measure_scons_tl τ M x t sp)) as [[u|sp'] Hsp];
        [exfalso; exact (HS_res_ok _ _ Hsp) |].
      exists (rs (scons t' sp')). constructor; auto.
  - destruct sp as [| N sp].
    + exists (rn M). constructor.
    + destruct τ as [| a b].
      * exists (rn M). constructor.
      * destruct M as [t | y sp0].
        -- destruct (IH _ (measure_beta_arg a b N t (lam t) (scons N sp))) as [[r1|s] H1];
             [| exfalso; exact (HS_res_ok _ _ H1)].
           destruct (IH _ (measure_beta_rest a b r1 (lam t) sp (scons N sp))) as [[r|s] H2];
             [| exfalso; exact (HS_res_ok _ _ H2)].
           exists (rn r). econstructor; eauto.
        -- exists (rn (ne y sp0)). constructor.
Defined.

(** ** The functions and their equations *)

Definition hsub (τ:ty) (M:nf) (x:nat) (N:nf) : nf :=
  match proj1_sig (hsub_total (CH τ M x N)) with rn r => r | rs _ => N end.

Definition hsub_sp (τ:ty) (M:nf) (x:nat) (sp:spine) : spine :=
  match proj1_sig (hsub_total (CS τ M x sp)) with rs s => s | rn _ => sp end.

Definition happ (τ:ty) (M:nf) (sp:spine) : nf :=
  match proj1_sig (hsub_total (CA τ M sp)) with rn r => r | rs _ => M end.

Lemma hsub_spec τ M x N r : HS (CH τ M x N) (rn r) -> hsub τ M x N = r.
Proof.
  intro H. unfold hsub. destruct (hsub_total (CH τ M x N)) as [r' H']. simpl.
  rewrite (HS_det _ _ H' _ H). reflexivity.
Qed.

Lemma hsub_sp_spec τ M x sp s : HS (CS τ M x sp) (rs s) -> hsub_sp τ M x sp = s.
Proof.
  intro H. unfold hsub_sp. destruct (hsub_total (CS τ M x sp)) as [r' H']. simpl.
  rewrite (HS_det _ _ H' _ H). reflexivity.
Qed.

Lemma happ_spec τ M sp r : HS (CA τ M sp) (rn r) -> happ τ M sp = r.
Proof.
  intro H. unfold happ. destruct (hsub_total (CA τ M sp)) as [r' H']. simpl.
  rewrite (HS_det _ _ H' _ H). reflexivity.
Qed.

Lemma hsub_HS τ M x N : HS (CH τ M x N) (rn (hsub τ M x N)).
Proof.
  unfold hsub. destruct (hsub_total (CH τ M x N)) as [[r|s] H]; simpl; auto.
  elim (HS_res_ok _ _ H).
Qed.

Lemma hsub_sp_HS τ M x sp : HS (CS τ M x sp) (rs (hsub_sp τ M x sp)).
Proof.
  unfold hsub_sp. destruct (hsub_total (CS τ M x sp)) as [[r|s] H]; simpl; auto.
  elim (HS_res_ok _ _ H).
Qed.

Lemma happ_HS τ M sp : HS (CA τ M sp) (rn (happ τ M sp)).
Proof.
  unfold happ. destruct (hsub_total (CA τ M sp)) as [[r|s] H]; simpl; auto.
  elim (HS_res_ok _ _ H).
Qed.

Lemma hsub_lam τ M x t : hsub τ M x (lam t) = lam (hsub τ (lift 0 M) (S x) t).
Proof. apply hsub_spec. constructor. apply hsub_HS. Qed.

Lemma hsub_var τ M x y sp :
  x <> y -> hsub τ M x (ne y sp) = ne (unshift x y) (hsub_sp τ M x sp).
Proof. intro H. apply hsub_spec. constructor; auto. apply hsub_sp_HS. Qed.

Lemma hsub_head τ M x sp : hsub τ M x (ne x sp) = happ τ M (hsub_sp τ M x sp).
Proof. apply hsub_spec. econstructor; [apply hsub_sp_HS | apply happ_HS]. Qed.

Lemma hsub_sp_nil τ M x : hsub_sp τ M x snil = snil.
Proof. apply hsub_sp_spec. constructor. Qed.

Lemma hsub_sp_cons τ M x t sp :
  hsub_sp τ M x (scons t sp) = scons (hsub τ M x t) (hsub_sp τ M x sp).
Proof. apply hsub_sp_spec. constructor; [apply hsub_HS | apply hsub_sp_HS]. Qed.

Lemma happ_nil τ M : happ τ M snil = M.
Proof. apply happ_spec. constructor. Qed.

Lemma happ_beta a b t N sp :
  happ (arr a b) (lam t) (scons N sp) = happ b (hsub a N 0 t) sp.
Proof. apply happ_spec. econstructor; [apply hsub_HS | apply happ_HS]. Qed.

(** For example, [[λz.z / 0]^(base→base) (0 · (1))] is [0]: the head
    redex [(λz.z) 0] is reduced on the spot. *)
Example hsub_example :
  hsub (arr base base) (lam (ne 0 snil)) 0 (ne 0 (scons (ne 1 snil) snil)) = ne 0 snil.
Proof.
  rewrite hsub_head, hsub_sp_cons, hsub_var, hsub_sp_nil by discriminate.
  rewrite happ_beta, hsub_head, hsub_sp_nil, !happ_nil. reflexivity.
Qed.

(** ** The measure is below [ω · (height + 1)]

    The ordinal of a type is [ω · height], so every measure at type [τ] is
    below [ω · (height τ + 1)], and all measures are below [ω · ω]. *)

Lemma omega_mul_max m n :
  natOrdSize m ≤ natOrdSize n \/ natOrdSize n ≤ natOrdSize m.
Proof.
  destruct (Nat.le_ge_cases m n); [left|right]; apply natOrdSize_monotone; auto.
Qed.

Theorem tyOrd_eq : forall τ, tyOrd τ ≈ ω * natOrdSize (height τ).
Proof.
  induction τ as [|a IHa b IHb]; simpl.
  - symmetry. apply mulOrd_zero_r.
  - rewrite mulOrd_succ. apply addOrd_eq_mor; [|reflexivity].
    rewrite IHa, IHb.
    destruct (Nat.le_ge_cases (height a) (height b)) as [H|H].
    + rewrite (Nat.max_r _ _ H). split.
      * apply lub_least; [|reflexivity].
        apply mulOrd_monotone2. apply natOrdSize_monotone; auto.
      * apply lub_le2.
    + rewrite (Nat.max_l _ _ H). split.
      * apply lub_least; [reflexivity|].
        apply mulOrd_monotone2. apply natOrdSize_monotone; auto.
      * apply lub_le1.
Qed.

Definition call_ty (c:call) : ty :=
  match c with CH τ _ _ _ | CS τ _ _ _ | CA τ _ _ => τ end.

Theorem measure_bound c : measure c < ω * natOrdSize (S (height (call_ty c))).
Proof.
  assert (H : forall τ k, tyOrd τ + natOrdSize k < ω * natOrdSize (S (height τ))).
  { intros τ k. simpl natOrdSize. rewrite mulOrd_succ, <- tyOrd_eq.
    apply addOrd_increasing. apply (index_lt ω k). }
  destruct c as [τ M x N | τ M x sp | τ M sp]; simpl measure; simpl call_ty; auto.
  rewrite <- (addOrd_zero_r (tyOrd τ)). apply (H τ 0%nat).
Qed.

Corollary measure_below_omega2 c : measure c < ω * ω.
Proof.
  apply ord_lt_le_trans with (ω * natOrdSize (S (height (call_ty c)))).
  - apply measure_bound.
  - apply mulOrd_monotone2. apply ord_lt_le. apply (index_lt ω).
Qed.
