From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wellfounded.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import HereditarySubst.

Open Scope ord_scope.

(** * Termination of hereditary substitution for LF

    In LF, types contain terms, so hereditary substitution goes into
    canonical types and kinds as well as objects.  As in the canonical
    presentations of LF (Watkins, Cervesato, Pfenning and Walker; Harper
    and Pfenning), it is indexed by the simple type [τ] obtained by erasing
    the dependent type of the substituted object: substitution does not
    change erasures ([erase_hsub_tp]), so the index stays meaningful, while
    the dependent type itself does not get structurally smaller.

    The ordinal measure of [HereditarySubst] carries over unchanged: a
    call substituting into an object, spine, type or kind at index [τ] has
    measure [|τ| + size], and an application at [τ] has measure [|τ|].
    Types and kinds only add structural recursion at the same index; the
    index decreases only in the application case, exactly as for simple
    types.  So every call at index [τ] is again below
    [ω · (height τ + 1)] ([lmeasure_bound]). *)

(** ** Canonical LF syntax, with de Bruijn indices *)

Inductive head : Set :=
| hvar : nat -> head
| hcst : nat -> head.

(** Objects: [lam M], or a head applied to a spine. *)
Inductive tm : Set :=
| tlam : tm -> tm
| tapp : head -> tspine -> tm
with tspine : Set :=
| tnil : tspine
| tcons : tm -> tspine -> tspine.

(** Types: a family constant applied to a spine, or [Πx:A.B]. *)
Inductive tp : Set :=
| atom : nat -> tspine -> tp
| pi : tp -> tp -> tp.

(** Kinds: [type], or [Πx:A.K]. *)
Inductive kd : Set :=
| ktype : kd
| kpi : tp -> kd -> kd.

Fixpoint tsize (t:tm) : nat :=
  match t with
  | tlam t => S (tsize t)
  | tapp _ sp => S (tsize_sp sp)
  end
with tsize_sp (sp:tspine) : nat :=
  match sp with
  | tnil => 0
  | tcons t sp => S (tsize t + tsize_sp sp)
  end.

Fixpoint psize (A:tp) : nat :=
  match A with
  | atom _ sp => S (tsize_sp sp)
  | pi A B => S (psize A + psize B)
  end.

Fixpoint ksize (K:kd) : nat :=
  match K with
  | ktype => 0
  | kpi A K => S (psize A + ksize K)
  end.

(** The simple-type erasure of a type. *)
Fixpoint erase (A:tp) : ty :=
  match A with
  | atom _ _ => base
  | pi A B => arr (erase A) (erase B)
  end.

Fixpoint tlift (k:nat) (t:tm) : tm :=
  match t with
  | tlam t => tlam (tlift (S k) t)
  | tapp (hvar y) sp => tapp (hvar (if y <? k then y else S y)) (tlift_sp k sp)
  | tapp (hcst c) sp => tapp (hcst c) (tlift_sp k sp)
  end
with tlift_sp (k:nat) (sp:tspine) : tspine :=
  match sp with
  | tnil => tnil
  | tcons t sp => tcons (tlift k t) (tlift_sp k sp)
  end.

(** ** The graph of hereditary substitution *)

Inductive lcall : Set :=
| LH : ty -> tm -> nat -> tm -> lcall          (* into an object *)
| LS : ty -> tm -> nat -> tspine -> lcall      (* into a spine   *)
| LT : ty -> tm -> nat -> tp -> lcall          (* into a type    *)
| LK : ty -> tm -> nat -> kd -> lcall          (* into a kind    *)
| LA : ty -> tm -> tspine -> lcall.            (* application    *)

Inductive lres : Set :=
| ln : tm -> lres
| ls : tspine -> lres
| lt : tp -> lres
| lk : kd -> lres.

Inductive LHS : lcall -> lres -> Prop :=
(* objects *)
| lh_lam τ M x t r :
    LHS (LH τ (tlift 0 M) (S x) t) (ln r) ->
    LHS (LH τ M x (tlam t)) (ln (tlam r))
| lh_cst τ M x c sp sp' :
    LHS (LS τ M x sp) (ls sp') ->
    LHS (LH τ M x (tapp (hcst c) sp)) (ln (tapp (hcst c) sp'))
| lh_var τ M x y sp sp' :
    x <> y ->
    LHS (LS τ M x sp) (ls sp') ->
    LHS (LH τ M x (tapp (hvar y) sp)) (ln (tapp (hvar (unshift x y)) sp'))
| lh_head τ M x sp sp' r :
    LHS (LS τ M x sp) (ls sp') ->
    LHS (LA τ M sp') (ln r) ->
    LHS (LH τ M x (tapp (hvar x) sp)) (ln r)
(* spines *)
| ls_nil τ M x :
    LHS (LS τ M x tnil) (ls tnil)
| ls_cons τ M x t sp t' sp' :
    LHS (LH τ M x t) (ln t') ->
    LHS (LS τ M x sp) (ls sp') ->
    LHS (LS τ M x (tcons t sp)) (ls (tcons t' sp'))
(* types *)
| lt_atom τ M x a sp sp' :
    LHS (LS τ M x sp) (ls sp') ->
    LHS (LT τ M x (atom a sp)) (lt (atom a sp'))
| lt_pi τ M x A B A' B' :
    LHS (LT τ M x A) (lt A') ->
    LHS (LT τ (tlift 0 M) (S x) B) (lt B') ->
    LHS (LT τ M x (pi A B)) (lt (pi A' B'))
(* kinds *)
| lk_type τ M x :
    LHS (LK τ M x ktype) (lk ktype)
| lk_pi τ M x A K A' K' :
    LHS (LT τ M x A) (lt A') ->
    LHS (LK τ (tlift 0 M) (S x) K) (lk K') ->
    LHS (LK τ M x (kpi A K)) (lk (kpi A' K'))
(* application *)
| la_nil τ M :
    LHS (LA τ M tnil) (ln M)
| la_beta a b t N sp r1 r :
    LHS (LH a N 0 t) (ln r1) ->
    LHS (LA b r1 sp) (ln r) ->
    LHS (LA (arr a b) (tlam t) (tcons N sp)) (ln r)
| la_base M N sp :
    LHS (LA base M (tcons N sp)) (ln M)
| la_app a b h sp0 N sp :
    LHS (LA (arr a b) (tapp h sp0) (tcons N sp)) (ln (tapp h sp0)).

Lemma LHS_det : forall c r1, LHS c r1 -> forall r2, LHS c r2 -> r1 = r2.
Proof.
  intros c r1 H. induction H; intros r2 H2; inversion H2; subst; try congruence;
    repeat match goal with
           | IH : forall r2, LHS ?c r2 -> _ = r2, H : LHS ?c _ |- _ =>
               apply IH in H; inversion H; subst; clear IH
           end; try reflexivity; try congruence.
Qed.

Definition lres_ok (c:lcall) (r:lres) : Prop :=
  match c, r with
  | LH _ _ _ _, ln _ | LA _ _ _, ln _ => True
  | LS _ _ _ _, ls _ => True
  | LT _ _ _ _, lt _ => True
  | LK _ _ _ _, lk _ => True
  | _, _ => False
  end.

Lemma LHS_res_ok c r : LHS c r -> lres_ok c r.
Proof. intro H; destruct H; simpl; auto. Qed.

(** ** The ordinal measure, as for simple types *)

Definition lmeasure (c:lcall) : Ord :=
  match c with
  | LH τ _ _ t => tyOrd τ + natOrdSize (tsize t)
  | LS τ _ _ sp => tyOrd τ + natOrdSize (tsize_sp sp)
  | LT τ _ _ A => tyOrd τ + natOrdSize (psize A)
  | LK τ _ _ K => tyOrd τ + natOrdSize (ksize K)
  | LA τ _ _ => tyOrd τ
  end.

Lemma lt_head_measure τ k : (0 < k)%nat -> tyOrd τ < tyOrd τ + natOrdSize k.
Proof.
  intro Hk. apply ord_le_lt_trans with (tyOrd τ + natOrdSize 0).
  - apply addOrd_le1.
  - apply add_nat_lt. exact Hk.
Qed.

(** ** Termination: the graph is total *)

Ltac lsize := apply add_nat_lt; simpl; lia.

Theorem lhsub_total : forall c, { r | LHS c r }.
Proof.
  apply (well_founded_induction_type
           (wf_inverse_image _ _ ord_lt lmeasure ord_lt_wf)).
  intros c IH.
  (* get a result of the expected kind from the induction hypothesis *)
  assert (getn : forall c', lmeasure c' < lmeasure c ->
            (exists t, lres_ok c' (ln t)) -> { t | LHS c' (ln t) }).
  { intros c' Hc' Hk. destruct (IH c' Hc') as [[t|s|A|K] H]; [exists t; exact H| | |];
      exfalso; destruct Hk as [t' Ht']; pose proof (LHS_res_ok _ _ H);
      destruct c'; simpl in *; auto. }
  assert (gets : forall c', lmeasure c' < lmeasure c ->
            (exists s, lres_ok c' (ls s)) -> { s | LHS c' (ls s) }).
  { intros c' Hc' Hk. destruct (IH c' Hc') as [[t|s|A|K] H]; [| exists s; exact H | |];
      exfalso; destruct Hk as [s' Hs']; pose proof (LHS_res_ok _ _ H);
      destruct c'; simpl in *; auto. }
  assert (gett : forall c', lmeasure c' < lmeasure c ->
            (exists A, lres_ok c' (lt A)) -> { A | LHS c' (lt A) }).
  { intros c' Hc' Hk. destruct (IH c' Hc') as [[t|s|A|K] H]; [| | exists A; exact H |];
      exfalso; destruct Hk as [A' HA']; pose proof (LHS_res_ok _ _ H);
      destruct c'; simpl in *; auto. }
  assert (getk : forall c', lmeasure c' < lmeasure c ->
            (exists K, lres_ok c' (lk K)) -> { K | LHS c' (lk K) }).
  { intros c' Hc' Hk. destruct (IH c' Hc') as [[t|s|A|K] H]; [| | | exists K; exact H];
      exfalso; destruct Hk as [K' HK']; pose proof (LHS_res_ok _ _ H);
      destruct c'; simpl in *; auto. }
  destruct c as [τ M x N | τ M x sp | τ M x A | τ M x K | τ M sp].
  - destruct N as [t | [y|c] sp].
    + destruct (getn (LH τ (tlift 0 M) (S x) t)) as [r Hr];
        [lsize | exists (tapp (hcst 0) tnil); exact I |].
      exists (ln (tlam r)). constructor; auto.
    + destruct (gets (LS τ M x sp)) as [sp' Hsp]; [lsize | exists tnil; exact I |].
      destruct (Nat.eq_dec x y) as [<-|Hxy].
      * destruct (getn (LA τ M sp')) as [r Hr];
          [apply lt_head_measure; simpl; lia | exists (tapp (hcst 0) tnil); exact I |].
        exists (ln r). econstructor; eauto.
      * exists (ln (tapp (hvar (unshift x y)) sp')). constructor; auto.
    + destruct (gets (LS τ M x sp)) as [sp' Hsp]; [lsize | exists tnil; exact I |].
      exists (ln (tapp (hcst c) sp')). constructor; auto.
  - destruct sp as [| t sp].
    + exists (ls tnil). constructor.
    + destruct (getn (LH τ M x t)) as [t' Ht]; [lsize | exists (tapp (hcst 0) tnil); exact I |].
      destruct (gets (LS τ M x sp)) as [sp' Hsp]; [lsize | exists tnil; exact I |].
      exists (ls (tcons t' sp')). constructor; auto.
  - destruct A as [a sp | A B].
    + destruct (gets (LS τ M x sp)) as [sp' Hsp]; [lsize | exists tnil; exact I |].
      exists (lt (atom a sp')). constructor; auto.
    + destruct (gett (LT τ M x A)) as [A' HA]; [lsize | exists A; exact I |].
      destruct (gett (LT τ (tlift 0 M) (S x) B)) as [B' HB]; [lsize | exists B; exact I |].
      exists (lt (pi A' B')). constructor; auto.
  - destruct K as [| A K].
    + exists (lk ktype). constructor.
    + destruct (gett (LT τ M x A)) as [A' HA]; [lsize | exists A; exact I |].
      destruct (getk (LK τ (tlift 0 M) (S x) K)) as [K' HK]; [lsize | exists K; exact I |].
      exists (lk (kpi A' K')). constructor; auto.
  - destruct sp as [| N sp].
    + exists (ln M). constructor.
    + destruct τ as [| a b].
      * exists (ln M). constructor.
      * destruct M as [t | h sp0].
        -- destruct (getn (LH a N 0 t)) as [r1 H1];
             [apply tyOrd_dom | exists (tapp (hcst 0) tnil); exact I |].
           destruct (getn (LA b r1 sp)) as [r H2];
             [apply tyOrd_cod | exists (tapp (hcst 0) tnil); exact I |].
           exists (ln r). econstructor; eauto.
        -- exists (ln (tapp h sp0)). constructor.
Defined.

(** ** The functions and their equations *)

Definition lhsub τ M x t : tm :=
  match proj1_sig (lhsub_total (LH τ M x t)) with ln r => r | _ => t end.
Definition lhsub_sp τ M x sp : tspine :=
  match proj1_sig (lhsub_total (LS τ M x sp)) with ls r => r | _ => sp end.
Definition lhsub_tp τ M x A : tp :=
  match proj1_sig (lhsub_total (LT τ M x A)) with lt r => r | _ => A end.
Definition lhsub_kd τ M x K : kd :=
  match proj1_sig (lhsub_total (LK τ M x K)) with lk r => r | _ => K end.
Definition lhapp τ M sp : tm :=
  match proj1_sig (lhsub_total (LA τ M sp)) with ln r => r | _ => M end.

Ltac lspec f c :=
  unfold f; destruct (lhsub_total c) as [r' H']; simpl;
  match goal with H : LHS c _ |- _ => rewrite (LHS_det _ _ H' _ H) end; reflexivity.

Lemma lhsub_spec τ M x t r : LHS (LH τ M x t) (ln r) -> lhsub τ M x t = r.
Proof. intro H. lspec lhsub (LH τ M x t). Qed.
Lemma lhsub_sp_spec τ M x sp r : LHS (LS τ M x sp) (ls r) -> lhsub_sp τ M x sp = r.
Proof. intro H. lspec lhsub_sp (LS τ M x sp). Qed.
Lemma lhsub_tp_spec τ M x A r : LHS (LT τ M x A) (lt r) -> lhsub_tp τ M x A = r.
Proof. intro H. lspec lhsub_tp (LT τ M x A). Qed.
Lemma lhsub_kd_spec τ M x K r : LHS (LK τ M x K) (lk r) -> lhsub_kd τ M x K = r.
Proof. intro H. lspec lhsub_kd (LK τ M x K). Qed.
Lemma lhapp_spec τ M sp r : LHS (LA τ M sp) (ln r) -> lhapp τ M sp = r.
Proof. intro H. lspec lhapp (LA τ M sp). Qed.

Ltac lgraph f c :=
  unfold f; destruct (lhsub_total c) as [[] H]; simpl; auto;
  elim (LHS_res_ok _ _ H).

Lemma lhsub_LHS τ M x t : LHS (LH τ M x t) (ln (lhsub τ M x t)).
Proof. lgraph lhsub (LH τ M x t). Qed.
Lemma lhsub_sp_LHS τ M x sp : LHS (LS τ M x sp) (ls (lhsub_sp τ M x sp)).
Proof. lgraph lhsub_sp (LS τ M x sp). Qed.
Lemma lhsub_tp_LHS τ M x A : LHS (LT τ M x A) (lt (lhsub_tp τ M x A)).
Proof. lgraph lhsub_tp (LT τ M x A). Qed.
Lemma lhsub_kd_LHS τ M x K : LHS (LK τ M x K) (lk (lhsub_kd τ M x K)).
Proof. lgraph lhsub_kd (LK τ M x K). Qed.
Lemma lhapp_LHS τ M sp : LHS (LA τ M sp) (ln (lhapp τ M sp)).
Proof. lgraph lhapp (LA τ M sp). Qed.

Global Hint Resolve lhsub_LHS lhsub_sp_LHS lhsub_tp_LHS lhsub_kd_LHS lhapp_LHS : core.

Lemma lhsub_lam τ M x t : lhsub τ M x (tlam t) = tlam (lhsub τ (tlift 0 M) (S x) t).
Proof. apply lhsub_spec. constructor; auto. Qed.
Lemma lhsub_cst τ M x c sp : lhsub τ M x (tapp (hcst c) sp) = tapp (hcst c) (lhsub_sp τ M x sp).
Proof. apply lhsub_spec. constructor; auto. Qed.
Lemma lhsub_var τ M x y sp :
  x <> y -> lhsub τ M x (tapp (hvar y) sp) = tapp (hvar (unshift x y)) (lhsub_sp τ M x sp).
Proof. intro H. apply lhsub_spec. constructor; auto. Qed.
Lemma lhsub_head τ M x sp : lhsub τ M x (tapp (hvar x) sp) = lhapp τ M (lhsub_sp τ M x sp).
Proof. apply lhsub_spec. econstructor; eauto. Qed.
Lemma lhsub_sp_nil τ M x : lhsub_sp τ M x tnil = tnil.
Proof. apply lhsub_sp_spec. constructor. Qed.
Lemma lhsub_sp_cons τ M x t sp :
  lhsub_sp τ M x (tcons t sp) = tcons (lhsub τ M x t) (lhsub_sp τ M x sp).
Proof. apply lhsub_sp_spec. constructor; auto. Qed.
Lemma lhsub_tp_atom τ M x a sp : lhsub_tp τ M x (atom a sp) = atom a (lhsub_sp τ M x sp).
Proof. apply lhsub_tp_spec. constructor; auto. Qed.
Lemma lhsub_tp_pi τ M x A B :
  lhsub_tp τ M x (pi A B) = pi (lhsub_tp τ M x A) (lhsub_tp τ (tlift 0 M) (S x) B).
Proof. apply lhsub_tp_spec. constructor; auto. Qed.
Lemma lhsub_kd_type τ M x : lhsub_kd τ M x ktype = ktype.
Proof. apply lhsub_kd_spec. constructor. Qed.
Lemma lhsub_kd_pi τ M x A K :
  lhsub_kd τ M x (kpi A K) = kpi (lhsub_tp τ M x A) (lhsub_kd τ (tlift 0 M) (S x) K).
Proof. apply lhsub_kd_spec. constructor; auto. Qed.
Lemma lhapp_nil τ M : lhapp τ M tnil = M.
Proof. apply lhapp_spec. constructor. Qed.
Lemma lhapp_beta a b t N sp :
  lhapp (arr a b) (tlam t) (tcons N sp) = lhapp b (lhsub a N 0 t) sp.
Proof. apply lhapp_spec. econstructor; eauto. Qed.

(** ** Erasure is invariant

    Substitution into a type does not change its simple-type erasure,
    which is why the erasure, and not the dependent type, indexes the
    substitution. *)

Theorem erase_hsub_tp : forall A τ M x, erase (lhsub_tp τ M x A) = erase A.
Proof.
  induction A as [a sp | A IHA B IHB]; intros τ M x.
  - rewrite lhsub_tp_atom. reflexivity.
  - rewrite lhsub_tp_pi. simpl. rewrite IHA, IHB. reflexivity.
Qed.

(** ** The measure is below [ω · (height + 1)] *)

Definition lcall_ty (c:lcall) : ty :=
  match c with
  | LH τ _ _ _ | LS τ _ _ _ | LT τ _ _ _ | LK τ _ _ _ | LA τ _ _ => τ
  end.

Theorem lmeasure_bound c : lmeasure c < ω * natOrdSize (S (height (lcall_ty c))).
Proof.
  assert (H : forall τ k, tyOrd τ + natOrdSize k < ω * natOrdSize (S (height τ))).
  { intros τ k. simpl natOrdSize. rewrite mulOrd_succ, <- tyOrd_eq.
    apply addOrd_increasing. apply (index_lt ω k). }
  destruct c; simpl lmeasure; simpl lcall_ty; auto.
  rewrite <- (addOrd_zero_r (tyOrd t)). apply (H t 0%nat).
Qed.

(** For example, substituting [λz.z] (of erased type [base → base]) for
    [0] in the type [c (0 · (d))] reduces the redex in its index. *)
Example lhsub_tp_example :
  lhsub_tp (arr base base) (tlam (tapp (hvar 0) tnil)) 0
    (atom 7 (tcons (tapp (hvar 0) (tcons (tapp (hcst 3) tnil) tnil)) tnil))
  = atom 7 (tcons (tapp (hcst 3) tnil) tnil).
Proof.
  rewrite lhsub_tp_atom, lhsub_sp_cons, lhsub_sp_nil, lhsub_head.
  rewrite lhsub_sp_cons, lhsub_sp_nil, lhsub_cst, lhsub_sp_nil.
  rewrite lhapp_beta, lhsub_head, lhsub_sp_nil, !lhapp_nil. reflexivity.
Qed.
