From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Wellfounded.
Import ListNotations.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import NaturalArith.
From Ordinal Require Import Analysis.HereditarySubstF.

Local Open Scope nat_scope.

(** * Hereditary substitution and normalization for Leivant's predicative
      System F

    Building on the ordinal type measure of [HereditarySubstF], this file
    defines hereditary substitution on the normal forms of predicative
    System F, proves that it terminates by the ordinal measure
    [ω · tord U + size], and that it preserves typing; normalization and
    consistency follow (Mangin and Sozeau 2015 do the same with a
    multiset ordering).

    Termination is unconditional, as for simple types and LF: when a type
    abstraction meets a type argument, the function checks decidably that
    the argument has the quantifier's kind ([kind_of]), and otherwise
    returns its input.  With the check, every recursive call decreases the
    ordinal measure ([tord_inst] does the work); the typing theorem shows
    that the check always succeeds on well-typed input.

    Contents:
    - type-level de Bruijn lemmas and kinding (cumulativity, inference,
      weakening, substitution);
    - normal forms in spine form, with typing judgments;
    - weakening by term and type variables, and type substitution into
      normal forms;
    - hereditary substitution as a graph, its totality by the ordinal
      measure ([hsub_total]), and typing preservation ([HS_typed]);
    - normalization of all well-typed terms ([normalization]) and
      consistency ([consistency]);
    - β-reduction on raw terms, the correctness of hereditary substitution
      with respect to it ([HS_red]), and normalization in the strong form:
      every well-typed term reduces to a normal form of the same type
      ([normalization_red]). *)

(** ** Type-level de Bruijn lemmas *)

Ltac vcases :=
  repeat (match goal with
          | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
          | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
          end; cbn [tsubst tshift] in *);
  try (exfalso; lia); try reflexivity; try (f_equal; lia).

Lemma tshift_tshift : forall T X Y,
  X <= Y -> tshift X (tshift Y T) = tshift (S Y) (tshift X T).
Proof.
  induction T as [Z | A IHA B IHB | k U IHU]; intros X Y H; cbn [tshift].
  - vcases.
  - rewrite IHA, IHB; auto.
  - rewrite IHU by lia. reflexivity.
Qed.

Lemma tsubst_tshift : forall T X U, tsubst (tshift X T) X U = T.
Proof.
  induction T as [Z | A IHA B IHB | k V IHV]; intros X U; cbn [tsubst tshift].
  - vcases.
  - rewrite IHA, IHB; auto.
  - rewrite IHV. reflexivity.
Qed.

(** Shifting below the substituted variable. *)
Lemma tshift_tsubst_le : forall T X Y U,
  X <= Y -> tshift X (tsubst T Y U) = tsubst (tshift X T) (S Y) (tshift X U).
Proof.
  induction T as [Z | A IHA B IHB | k V IHV]; intros X Y U H; cbn [tsubst tshift].
  - vcases.
  - rewrite IHA, IHB; auto.
  - rewrite (IHV (S X) (S Y)) by lia. rewrite (tshift_tshift U 0 X) by lia. reflexivity.
Qed.

(** Shifting above the substituted variable. *)
Lemma tshift_tsubst_ge : forall T X Y U,
  Y <= X -> tshift X (tsubst T Y U) = tsubst (tshift (S X) T) Y (tshift X U).
Proof.
  induction T as [Z | A IHA B IHB | k V IHV]; intros X Y U H; cbn [tsubst tshift].
  - vcases.
  - rewrite IHA, IHB; auto.
  - rewrite (IHV (S X) (S Y)) by lia. rewrite (tshift_tshift U 0 X) by lia. reflexivity.
Qed.

Lemma tsubst_tsubst : forall T X Y U V,
  X <= Y ->
  tsubst (tsubst T X U) Y V = tsubst (tsubst T (S Y) (tshift X V)) X (tsubst U Y V).
Proof.
  induction T as [Z | A IHA B IHB | k W IHW]; intros X Y U V H; cbn [tsubst tshift].
  - vcases. rewrite tsubst_tshift. reflexivity.
  - rewrite IHA, IHB; auto.
  - rewrite (IHW (S X) (S Y)) by lia. f_equal. f_equal.
    + rewrite (tshift_tshift V 0 X) by lia. reflexivity.
    + rewrite (tshift_tsubst_le U 0 Y) by lia. reflexivity.
Qed.

(** ** Kinding *)

Lemma kinding_cumul : forall Δ T k, kinding Δ T k -> forall k', k <= k' -> kinding Δ T k'.
Proof.
  intros Δ T k H. induction H; intros k'' Hle.
  - econstructor; eauto. lia.
  - pose proof (Nat.le_max_l k k'). pose proof (Nat.le_max_r k k').
    rewrite <- (Nat.max_id k''). constructor; [apply IHkinding1 | apply IHkinding2]; lia.
  - pose proof (Nat.le_max_l (S k) k'). pose proof (Nat.le_max_r (S k) k').
    rewrite <- (Nat.max_r (S k) k'') by lia. constructor. apply IHkinding. lia.
Qed.

(** The least kind of a type, if any. *)
Fixpoint kind_of (Δ:list kind) (T:typ) : option kind :=
  match T with
  | tvar X => nth_error Δ X
  | arrow A B =>
      match kind_of Δ A, kind_of Δ B with
      | Some k, Some k' => Some (Nat.max k k')
      | _, _ => None
      end
  | all k U =>
      match kind_of (k :: Δ) U with
      | Some k' => Some (Nat.max (S k) k')
      | None => None
      end
  end.

Lemma kind_of_sound : forall T Δ k, kind_of Δ T = Some k -> kinding Δ T k.
Proof.
  induction T as [X | A IHA B IHB | k0 U IHU]; intros Δ k H; simpl in H.
  - econstructor; eauto.
  - destruct (kind_of Δ A) eqn:EA; [|discriminate].
    destruct (kind_of Δ B) eqn:EB; [|discriminate].
    injection H as <-. constructor; auto.
  - destruct (kind_of (k0 :: Δ) U) eqn:EU; [|discriminate].
    injection H as <-. constructor; auto.
Qed.

Lemma kind_of_complete : forall Δ T k, kinding Δ T k -> exists k0, kind_of Δ T = Some k0 /\ k0 <= k.
Proof.
  intros Δ T k H. induction H; cbn [kind_of].
  - exists k. auto.
  - destruct IHkinding1 as [k1 [E1 H1]], IHkinding2 as [k2 [E2 H2]].
    rewrite E1, E2. exists (Nat.max k1 k2). split; auto. apply Nat.max_le_compat; auto.
  - destruct IHkinding as [k1 [E1 H1]]. rewrite E1. exists (Nat.max (S k) k1). split; auto.
    apply Nat.max_le_compat; auto.
Qed.

Lemma nth_error_insert {A} : forall (Δ1 Δ2 : list A) a X,
  nth_error (Δ1 ++ a :: Δ2) (if X <? length Δ1 then X else S X) = nth_error (Δ1 ++ Δ2) X.
Proof.
  induction Δ1 as [|b Δ1 IH]; intros Δ2 a X; simpl.
  - destruct X; reflexivity.
  - destruct X as [|X]; simpl; auto.
    specialize (IH Δ2 a X). destruct (Nat.ltb_spec X (length Δ1)) as [H|H];
      destruct (Nat.ltb_spec (S X) (S (length Δ1))) as [H'|H']; try lia; auto.
Qed.

Lemma kinding_weaken : forall Δ T k, kinding Δ T k ->
  forall Δ1 Δ2 k0, Δ = Δ1 ++ Δ2 -> kinding (Δ1 ++ k0 :: Δ2) (tshift (length Δ1) T) k.
Proof.
  intros Δ T k H. induction H; intros Δ1 Δ2 k0 E; subst; simpl.
  - econstructor; [|eauto]. rewrite nth_error_insert. auto.
  - constructor; auto.
  - constructor. apply (IHkinding (k :: Δ1) Δ2 k0). reflexivity.
Qed.

Lemma nth_error_remove {A} : forall (Δ1 Δ2 : list A) a X,
  X <> length Δ1 ->
  nth_error (Δ1 ++ Δ2) (if X <? length Δ1 then X else pred X) = nth_error (Δ1 ++ a :: Δ2) X.
Proof.
  induction Δ1 as [|b Δ1 IH]; intros Δ2 a X H; simpl in *.
  - destruct X; [lia|]. reflexivity.
  - destruct X as [|X]; simpl; auto.
    specialize (IH Δ2 a X ltac:(lia)).
    destruct (Nat.ltb_spec X (length Δ1)) as [H1|H1];
      destruct (Nat.ltb_spec (S X) (S (length Δ1))) as [H2|H2]; try lia; auto.
    destruct X; [lia|]. simpl in *. auto.
Qed.

Lemma nth_error_at {A} : forall (Δ1 Δ2 : list A) a, nth_error (Δ1 ++ a :: Δ2) (length Δ1) = Some a.
Proof. induction Δ1; simpl; auto. Qed.

Lemma kinding_subst : forall Δ T k', kinding Δ T k' ->
  forall Δ1 Δ2 k C, Δ = Δ1 ++ k :: Δ2 -> kinding (Δ1 ++ Δ2) C k ->
  kinding (Δ1 ++ Δ2) (tsubst T (length Δ1) C) k'.
Proof.
  intros Δ T k' H. induction H; intros Δ1 Δ2 k0 C E HC; subst; simpl.
  - destruct (Nat.eqb_spec X (length Δ1)) as [->|Hne].
    + rewrite nth_error_at in H. injection H as <-. eapply kinding_cumul; eauto.
    + econstructor; [|eauto]. rewrite (nth_error_remove Δ1 Δ2 k0 X Hne); eauto.
  - constructor; eauto.
  - constructor. apply (IHkinding (k :: Δ1) Δ2 k0); auto.
    apply (kinding_weaken _ _ _ HC [] (Δ1 ++ Δ2)). reflexivity.
Qed.

(** ** Normal forms and their typing *)

(** Normal forms in spine form; type and term variables have separate de
    Bruijn indices. *)
Inductive nf : Set :=
| nlam : typ -> nf -> nf
| ntlam : kind -> nf -> nf
| nne : nat -> spine -> nf
with spine : Set :=
| snil : spine
| sapp : nf -> spine -> spine
| stapp : typ -> spine -> spine.

Fixpoint nsize (t:nf) : nat :=
  match t with
  | nlam _ t => S (nsize t)
  | ntlam _ t => S (nsize t)
  | nne _ sp => S (ssize sp)
  end
with ssize (sp:spine) : nat :=
  match sp with
  | snil => 0
  | sapp t sp => S (nsize t + ssize sp)
  | stapp _ sp => S (ssize sp)
  end.

Fixpoint sp_app (sp1 sp2:spine) : spine :=
  match sp1 with
  | snil => sp2
  | sapp t sp => sapp t (sp_app sp sp2)
  | stapp C sp => stapp C (sp_app sp sp2)
  end.

(** Contexts interleave kinded type variables and typed term variables. *)
Inductive entry : Set :=
| EK : kind -> entry
| ET : typ -> entry.

Definition env := list entry.

Fixpoint kctx (e:env) : list kind :=
  match e with
  | [] => []
  | EK k :: e => k :: kctx e
  | ET _ :: e => kctx e
  end.

Fixpoint get_var (e:env) (x:nat) : option typ :=
  match e with
  | [] => None
  | EK _ :: e => option_map (tshift 0) (get_var e x)
  | ET A :: e => match x with O => Some A | S x => get_var e x end
  end.

Fixpoint cntT (e:env) : nat :=
  match e with
  | [] => 0
  | EK _ :: e => cntT e
  | ET _ :: e => S (cntT e)
  end.

Lemma kctx_app e1 e2 : kctx (e1 ++ e2) = kctx e1 ++ kctx e2.
Proof. induction e1 as [|[k|A] e1 IH]; simpl; auto. rewrite IH. reflexivity. Qed.

Inductive check : env -> nf -> typ -> Prop :=
| C_lam e A t B : check (ET A :: e) t B -> check e (nlam A t) (arrow A B)
| C_tlam e k t B : check (EK k :: e) t B -> check e (ntlam k t) (all k B)
| C_ne e x sp A T : get_var e x = Some A -> spine_ty e A sp T -> check e (nne x sp) T
with spine_ty : env -> typ -> spine -> typ -> Prop :=
| S_nil e A : spine_ty e A snil A
| S_app e A B t sp T : check e t A -> spine_ty e B sp T -> spine_ty e (arrow A B) (sapp t sp) T
| S_tapp e k B C sp T :
    kinding (kctx e) C k -> spine_ty e (tsubst B 0 C) sp T -> spine_ty e (all k B) (stapp C sp) T.

Scheme check_ind' := Induction for check Sort Prop
  with spine_ind' := Induction for spine_ty Sort Prop.

Lemma spine_app : forall e A sp1 U, spine_ty e A sp1 U ->
  forall sp2 T, spine_ty e U sp2 T -> spine_ty e A (sp_app sp1 sp2) T.
Proof.
  intros e A sp1 U H. induction H; intros sp2 T' H2; simpl; auto; econstructor; eauto.
Qed.

(** ** Weakening by a term variable *)

Fixpoint shift_tm (c:nat) (t:nf) : nf :=
  match t with
  | nlam A t => nlam A (shift_tm (S c) t)
  | ntlam k t => ntlam k (shift_tm c t)
  | nne y sp => nne (if y <? c then y else S y) (shift_sp c sp)
  end
with shift_sp (c:nat) (sp:spine) : spine :=
  match sp with
  | snil => snil
  | sapp t sp => sapp (shift_tm c t) (shift_sp c sp)
  | stapp C sp => stapp C (shift_sp c sp)
  end.

Lemma get_var_insert : forall e1 e2 A y,
  get_var (e1 ++ ET A :: e2) (if y <? cntT e1 then y else S y) = get_var (e1 ++ e2) y.
Proof.
  induction e1 as [|[k|B] e1 IH]; intros e2 A y; simpl.
  - destruct y; reflexivity.
  - rewrite IH. reflexivity.
  - destruct y as [|y]; simpl; auto.
    specialize (IH e2 A y).
    destruct (Nat.ltb_spec y (cntT e1)); destruct (Nat.ltb_spec (S y) (S (cntT e1))); try lia; auto.
Qed.

Lemma weaken_tm : forall e t T, check e t T ->
  forall e1 e2 A, e = e1 ++ e2 -> check (e1 ++ ET A :: e2) (shift_tm (cntT e1) t) T.
Proof.
  intros e t T H.
  induction H using check_ind' with
    (P0 := fun e B sp T _ => forall e1 e2 A, e = e1 ++ e2 ->
             spine_ty (e1 ++ ET A :: e2) B (shift_sp (cntT e1) sp) T);
    intros e1 e2 A0 E; subst; simpl.
  - constructor. apply (IHcheck (ET A :: e1)). reflexivity.
  - constructor. apply (IHcheck (EK k :: e1)). reflexivity.
  - econstructor; [rewrite get_var_insert; eauto | auto].
  - constructor.
  - constructor; auto.
  - econstructor; [rewrite kctx_app in *; simpl; auto | auto].
Qed.

(** ** Weakening by a type variable *)

Fixpoint tshift_tm (X:nat) (t:nf) : nf :=
  match t with
  | nlam A t => nlam (tshift X A) (tshift_tm X t)
  | ntlam k t => ntlam k (tshift_tm (S X) t)
  | nne y sp => nne y (tshift_sp X sp)
  end
with tshift_sp (X:nat) (sp:spine) : spine :=
  match sp with
  | snil => snil
  | sapp t sp => sapp (tshift_tm X t) (tshift_sp X sp)
  | stapp C sp => stapp (tshift X C) (tshift_sp X sp)
  end.

Fixpoint shift_env (X:nat) (e:env) : env :=
  match e with
  | [] => []
  | EK k :: e => EK k :: shift_env (pred X) e
  | ET A :: e => ET (tshift X A) :: shift_env X e
  end.

Lemma kctx_shift_env : forall e X, kctx (shift_env X e) = kctx e.
Proof. induction e as [|[k|A] e IH]; intro X; simpl; auto. rewrite IH. reflexivity. Qed.

Lemma get_var_shift_env : forall e1 e2 k y,
  get_var (shift_env (length (kctx e1)) e1 ++ EK k :: e2) y =
  option_map (tshift (length (kctx e1))) (get_var (e1 ++ e2) y).
Proof.
  induction e1 as [|[k'|B] e1 IH]; intros e2 k y; simpl.
  - destruct (get_var e2 y); reflexivity.
  - rewrite IH. destruct (get_var (e1 ++ e2) y) as [A|]; simpl; auto.
    rewrite (tshift_tshift A 0 (length (kctx e1))) by lia. reflexivity.
  - destruct y as [|y]; simpl; auto.
Qed.

Lemma weaken_ty : forall e t T, check e t T ->
  forall e1 e2 k, e = e1 ++ e2 ->
  check (shift_env (length (kctx e1)) e1 ++ EK k :: e2)
        (tshift_tm (length (kctx e1)) t) (tshift (length (kctx e1)) T).
Proof.
  intros e t T H.
  induction H using check_ind' with
    (P0 := fun e B sp T _ => forall e1 e2 k, e = e1 ++ e2 ->
             spine_ty (shift_env (length (kctx e1)) e1 ++ EK k :: e2)
                      (tshift (length (kctx e1)) B) (tshift_sp (length (kctx e1)) sp)
                      (tshift (length (kctx e1)) T));
    intros e1 e2 kk E; subst; simpl.
  - constructor. apply (IHcheck (ET A :: e1)). reflexivity.
  - constructor. apply (IHcheck (EK k :: e1)). reflexivity.
  - econstructor; [rewrite get_var_shift_env, e0; reflexivity | auto].
  - constructor.
  - constructor; auto.
  - econstructor.
    + rewrite kctx_app, kctx_shift_env. simpl. rewrite kctx_app in k0.
      apply (kinding_weaken _ _ _ k0 (kctx e1) (kctx e2)). reflexivity.
    + rewrite <- tshift_tsubst_ge by lia. auto.
Qed.

(** ** Type substitution into normal forms *)

Fixpoint tsubst_tm (t:nf) (X:nat) (C:typ) : nf :=
  match t with
  | nlam A t => nlam (tsubst A X C) (tsubst_tm t X C)
  | ntlam k t => ntlam k (tsubst_tm t (S X) (tshift 0 C))
  | nne y sp => nne y (tsubst_sp sp X C)
  end
with tsubst_sp (sp:spine) (X:nat) (C:typ) : spine :=
  match sp with
  | snil => snil
  | sapp t sp => sapp (tsubst_tm t X C) (tsubst_sp sp X C)
  | stapp D sp => stapp (tsubst D X C) (tsubst_sp sp X C)
  end.

Inductive env_subst : nat -> typ -> env -> env -> Prop :=
| es_here e k C : kinding (kctx e) C k -> env_subst 0 C (EK k :: e) e
| es_var X C e e' A : env_subst X C e e' -> env_subst X C (ET A :: e) (ET (tsubst A X C) :: e')
| es_kind X C e e' k : env_subst X C e e' -> env_subst (S X) (tshift 0 C) (EK k :: e) (EK k :: e').

Lemma env_subst_get_var : forall X C e e', env_subst X C e e' ->
  forall y, get_var e' y = option_map (fun A => tsubst A X C) (get_var e y).
Proof.
  intros X C e e' H. induction H; intro y; simpl.
  - destruct (get_var e y) as [A|]; simpl; auto. rewrite tsubst_tshift. reflexivity.
  - destruct y; simpl; auto.
  - rewrite IHenv_subst. destruct (get_var e y) as [A|]; simpl; auto.
    rewrite (tshift_tsubst_le A 0 X) by lia. reflexivity.
Qed.

Lemma env_subst_kctx : forall X C e e', env_subst X C e e' ->
  exists Δ1 Δ2 k, kctx e = Δ1 ++ k :: Δ2 /\ kctx e' = Δ1 ++ Δ2 /\ length Δ1 = X /\
                  kinding (kctx e') C k.
Proof.
  intros X C e e' H. induction H; simpl.
  - exists [], (kctx e), k. auto.
  - exact IHenv_subst.
  - destruct IHenv_subst as [Δ1 [Δ2 [k0 [E1 [E2 [L HC]]]]]].
    exists (k :: Δ1), Δ2, k0. rewrite E1, E2. simpl. repeat split; auto.
    rewrite E2 in HC. apply (kinding_weaken _ _ _ HC [] (Δ1 ++ Δ2)). reflexivity.
Qed.

Lemma subst_ty : forall e t T, check e t T ->
  forall X C e', env_subst X C e e' -> check e' (tsubst_tm t X C) (tsubst T X C).
Proof.
  intros e t T H.
  induction H using check_ind' with
    (P0 := fun e B sp T _ => forall X C e', env_subst X C e e' ->
             spine_ty e' (tsubst B X C) (tsubst_sp sp X C) (tsubst T X C));
    intros XX CC ee HS; simpl.
  - constructor. apply IHcheck. constructor. auto.
  - constructor. apply IHcheck. constructor. auto.
  - econstructor; [rewrite (env_subst_get_var _ _ _ _ HS), e0; reflexivity | auto].
  - constructor.
  - constructor; auto.
  - econstructor.
    + destruct (env_subst_kctx _ _ _ _ HS) as [Δ1 [Δ2 [k1 [E1 [E2 [L HC]]]]]].
      rewrite E2, <- L. rewrite E1 in k0. apply (kinding_subst _ _ _ k0 Δ1 Δ2 k1); auto.
      rewrite <- E2. auto.
    + rewrite <- (tsubst_tsubst B 0 XX C CC) by lia. auto.
Qed.

(** ** The graph of hereditary substitution

    [CH Δ U u x t] substitutes [u : U] for the term variable [x] in [t];
    [CS] does the same in a spine; [CA Δ U u sp] applies [u : U] to the
    spine [sp].  [Δ] is the kind context, used to check the kind of a type
    argument before reducing a type-application redex. *)

Inductive call : Set :=
| CH : list kind -> typ -> nf -> nat -> nf -> call
| CS : list kind -> typ -> nf -> nat -> spine -> call
| CA : list kind -> typ -> nf -> spine -> call.

Inductive res : Set :=
| rn : nf -> res
| rs : spine -> res.

Definition unshift (x y:nat) : nat := if y <? x then y else pred y.

(** The applications that are not redexes of the expected shape; on
    well-typed input they never occur. *)
Definition stuck (Δ:list kind) (U:typ) (u:nf) (sp:spine) : Prop :=
  match u, sp with
  | nlam _ _, sapp _ _ => match U with arrow _ _ => False | _ => True end
  | nlam _ _, stapp _ _ => True
  | ntlam _ _, sapp _ _ => True
  | ntlam _ _, stapp C _ =>
      match U with
      | all k _ => kind_of Δ C = None \/ exists k0, kind_of Δ C = Some k0 /\ k < k0
      | _ => True
      end
  | _, _ => False
  end.

Inductive HS : call -> res -> Prop :=
| hs_lam Δ U u x A t r :
    HS (CH Δ U (shift_tm 0 u) (S x) t) (rn r) ->
    HS (CH Δ U u x (nlam A t)) (rn (nlam A r))
| hs_tlam Δ U u x k t r :
    HS (CH (k :: Δ) (tshift 0 U) (tshift_tm 0 u) x t) (rn r) ->
    HS (CH Δ U u x (ntlam k t)) (rn (ntlam k r))
| hs_var Δ U u x y sp sp' :
    x <> y ->
    HS (CS Δ U u x sp) (rs sp') ->
    HS (CH Δ U u x (nne y sp)) (rn (nne (unshift x y) sp'))
| hs_head Δ U u x sp sp' r :
    HS (CS Δ U u x sp) (rs sp') ->
    HS (CA Δ U u sp') (rn r) ->
    HS (CH Δ U u x (nne x sp)) (rn r)
| hs_snil Δ U u x :
    HS (CS Δ U u x snil) (rs snil)
| hs_sapp Δ U u x t sp t' sp' :
    HS (CH Δ U u x t) (rn t') ->
    HS (CS Δ U u x sp) (rs sp') ->
    HS (CS Δ U u x (sapp t sp)) (rs (sapp t' sp'))
| hs_stapp Δ U u x C sp sp' :
    HS (CS Δ U u x sp) (rs sp') ->
    HS (CS Δ U u x (stapp C sp)) (rs (stapp C sp'))
| ha_nil Δ U u :
    HS (CA Δ U u snil) (rn u)
| ha_ne Δ U y sp0 sp :
    sp <> snil ->
    HS (CA Δ U (nne y sp0) sp) (rn (nne y (sp_app sp0 sp)))
| ha_beta Δ A B A' b t sp r1 r :
    HS (CH Δ A t 0 b) (rn r1) ->
    HS (CA Δ B r1 sp) (rn r) ->
    HS (CA Δ (arrow A B) (nlam A' b) (sapp t sp)) (rn r)
| ha_tbeta Δ k B k' b C sp k0 r :
    kind_of Δ C = Some k0 -> k0 <= k ->
    HS (CA Δ (tsubst B 0 C) (tsubst_tm b 0 C) sp) (rn r) ->
    HS (CA Δ (all k B) (ntlam k' b) (stapp C sp)) (rn r)
| ha_stuck Δ U u sp :
    stuck Δ U u sp ->
    HS (CA Δ U u sp) (rn u).

Lemma HS_det : forall c r1, HS c r1 -> forall r2, HS c r2 -> r1 = r2.
Proof.
  intros c r1 H. induction H; intros r2 H2; inversion H2; subst; try congruence;
    try (simpl in *; tauto);
    try (match goal with
         | Hs : stuck _ _ _ _ |- _ => simpl in Hs;
             destruct Hs as [Hs|[? [Hs ?]]]; rewrite Hs in *; try discriminate;
             match goal with E : Some _ = Some _ |- _ => injection E as <- end; lia
         end);
    repeat match goal with
           | IH : forall r2, HS ?c r2 -> _ = r2, H : HS ?c _ |- _ =>
               apply IH in H; inversion H; subst; clear IH
           end; try reflexivity; try congruence.
Qed.

Definition res_ok (c:call) (r:res) : Prop :=
  match c, r with
  | CS _ _ _ _ _, rs _ => True
  | CS _ _ _ _ _, rn _ => False
  | _, rn _ => True
  | _, rs _ => False
  end.

Lemma HS_res_ok c r : HS c r -> res_ok c r.
Proof. intro H; destruct H; simpl; auto. Qed.

(** ** The ordinal measure and termination *)

Definition hmeasure (c:call) : Ord :=
  match c with
  | CH _ U _ _ t => (ω * tord U + natOrdSize (nsize t))%ord
  | CS _ U _ _ sp => (ω * tord U + natOrdSize (ssize sp))%ord
  | CA _ U _ _ => (ω * tord U)%ord
  end.

Lemma add_nat_lt' a m n : m < n -> (a + natOrdSize m < a + natOrdSize n)%ord.
Proof. intro H. apply addOrd_increasing. apply natOrdSize_increasing; auto. Qed.

Lemma below_head a n : (a < a + natOrdSize (S n))%ord.
Proof.
  apply ord_le_lt_trans with (a + natOrdSize 0)%ord; [apply addOrd_le1 | apply add_nat_lt'; lia].
Qed.

Lemma below_major a a' d : (a' < a)%ord -> (ω * a' + natOrdSize d < ω * a)%ord.
Proof.
  intro H. rewrite <- (addOrd_zero_r (ω * a)%ord).
  apply (lex_lt_major a a' 0 d H).
Qed.

Lemma below_major' a a' : (a' < a)%ord -> (ω * a' < ω * a)%ord.
Proof. intro H. apply mulOrd_increasing2; auto. apply omega_gt0. Qed.

Lemma tord_shift_measure U n : (ω * tord (tshift 0 U) + natOrdSize n ≈ ω * tord U + natOrdSize n)%ord.
Proof.
  apply addOrd_eq_mor; [|reflexivity].
  split; apply mulOrd_monotone2; apply (tord_tshift U 0).
Qed.

Theorem hsub_total : forall c, { r | HS c r }.
Proof.
  apply (well_founded_induction_type
           (wf_inverse_image _ _ ord_lt hmeasure ord_lt_wf)).
  intros c IH.
  assert (getn : forall c', (hmeasure c' < hmeasure c)%ord ->
            (forall s, ~ HS c' (rs s)) -> { t | HS c' (rn t) }).
  { intros c' Hc' Hk. destruct (IH c' Hc') as [[t|s] H]; [exists t; exact H|].
    exfalso. exact (Hk s H). }
  assert (gets : forall c', (hmeasure c' < hmeasure c)%ord ->
            (forall t, ~ HS c' (rn t)) -> { s | HS c' (rs s) }).
  { intros c' Hc' Hk. destruct (IH c' Hc') as [[t|s] H]; [|exists s; exact H].
    exfalso. exact (Hk t H). }
  assert (notS : forall Δ U u x t s, ~ HS (CH Δ U u x t) (rs s))
    by (intros * H; exact (HS_res_ok _ _ H)).
  assert (notSA : forall Δ U u sp s, ~ HS (CA Δ U u sp) (rs s))
    by (intros * H; exact (HS_res_ok _ _ H)).
  assert (notN : forall Δ U u x sp t, ~ HS (CS Δ U u x sp) (rn t))
    by (intros * H; exact (HS_res_ok _ _ H)).
  destruct c as [Δ U u x t | Δ U u x sp | Δ U u sp].
  - destruct t as [A t | k t | y sp].
    + destruct (getn (CH Δ U (shift_tm 0 u) (S x) t)) as [r Hr]; [apply add_nat_lt'; simpl; lia | auto |].
      exists (rn (nlam A r)). constructor; auto.
    + destruct (getn (CH (k :: Δ) (tshift 0 U) (tshift_tm 0 u) x t)) as [r Hr]; [| auto |].
      { cbn [hmeasure]. rewrite tord_shift_measure. apply add_nat_lt'. simpl. lia. }
      exists (rn (ntlam k r)). constructor; auto.
    + destruct (gets (CS Δ U u x sp)) as [sp' Hsp]; [apply add_nat_lt'; simpl; lia | auto |].
      destruct (Nat.eq_dec x y) as [<-|Hxy].
      * destruct (getn (CA Δ U u sp')) as [r Hr]; [apply below_head | auto |].
        exists (rn r). econstructor; eauto.
      * exists (rn (nne (unshift x y) sp')). constructor; auto.
  - destruct sp as [| t sp | C sp].
    + exists (rs snil). constructor.
    + destruct (getn (CH Δ U u x t)) as [t' Ht]; [apply add_nat_lt'; simpl; lia | auto |].
      destruct (gets (CS Δ U u x sp)) as [sp' Hsp]; [apply add_nat_lt'; simpl; lia | auto |].
      exists (rs (sapp t' sp')). constructor; auto.
    + destruct (gets (CS Δ U u x sp)) as [sp' Hsp]; [apply add_nat_lt'; simpl; lia | auto |].
      exists (rs (stapp C sp')). constructor; auto.
  - destruct sp as [| t sp1 | C sp1].
    + exists (rn u). constructor.
    + destruct u as [A' b | k' b | y sp0].
      * destruct U as [Z | A B | k B]; try (exists (rn (nlam A' b)); constructor; exact I).
        destruct (getn (CH Δ A t 0 b)) as [r1 H1];
          [apply below_major; apply tord_arrow_l | auto |].
        destruct (getn (CA Δ B r1 sp1)) as [r H2];
          [apply below_major'; apply tord_arrow_r | auto |].
        exists (rn r). econstructor; eauto.
      * exists (rn (ntlam k' b)). constructor. exact I.
      * exists (rn (nne y (sp_app sp0 (sapp t sp1)))). constructor. discriminate.
    + destruct u as [A' b | k' b | y sp0].
      * exists (rn (nlam A' b)). constructor. exact I.
      * destruct U as [Z | A B | k B]; try (exists (rn (ntlam k' b)); constructor; exact I).
        destruct (kind_of Δ C) as [k0|] eqn:EC.
        -- destruct (le_lt_dec k0 k) as [Hle|Hlt].
           ++ destruct (getn (CA Δ (tsubst B 0 C) (tsubst_tm b 0 C) sp1)) as [r H2]; [| auto |].
              { apply below_major'. apply tord_inst with (Γ := Δ).
                apply kinding_cumul with k0; auto. apply kind_of_sound; auto. }
              exists (rn r). econstructor; eauto.
           ++ exists (rn (ntlam k' b)). constructor. simpl. right. eauto.
        -- exists (rn (ntlam k' b)). constructor. simpl. left. auto.
      * exists (rn (nne y (sp_app sp0 (stapp C sp1)))). constructor. discriminate.
Defined.

(** ** Typing preservation *)

(** Removing the substituted variable from a context. *)
Lemma get_var_remove e1 e2 U0 x y :
  cntT e1 = x -> x <> y ->
  get_var (e1 ++ e2) (unshift x y) = get_var (e1 ++ ET U0 :: e2) y.
Proof.
  intros Hx Hxy. rewrite <- (get_var_insert e1 e2 U0 (unshift x y)). f_equal.
  unfold unshift. subst x.
  destruct (Nat.ltb_spec y (cntT e1)); destruct (Nat.ltb_spec y (cntT e1)); try lia;
    vcases.
Qed.

Definition post (c:call) (r:res) : Prop :=
  match c, r with
  | CH Δ U u x t, rn r =>
      forall e1 e2 U0 T, Δ = kctx (e1 ++ ET U0 :: e2) -> cntT e1 = x ->
        get_var (e1 ++ ET U0 :: e2) x = Some U -> check (e1 ++ e2) u U ->
        check (e1 ++ ET U0 :: e2) t T -> check (e1 ++ e2) r T
  | CS Δ U u x sp, rs sp' =>
      forall e1 e2 U0 A T, Δ = kctx (e1 ++ ET U0 :: e2) -> cntT e1 = x ->
        get_var (e1 ++ ET U0 :: e2) x = Some U -> check (e1 ++ e2) u U ->
        spine_ty (e1 ++ ET U0 :: e2) A sp T -> spine_ty (e1 ++ e2) A sp' T
  | CA Δ U u sp, rn r =>
      forall e T, Δ = kctx e -> check e u U -> spine_ty e U sp T -> check e r T
  | _, _ => True
  end.

Lemma kctx_remove e1 e2 U0 : kctx (e1 ++ ET U0 :: e2) = kctx (e1 ++ e2).
Proof. rewrite !kctx_app. reflexivity. Qed.

Theorem HS_typed : forall c r, HS c r -> post c r.
Proof.
  intros c r H. induction H; simpl in *.
  - (* lam *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    constructor. apply (IHHS (ET A :: e1) e2 U0); simpl; auto.
    apply (weaken_tm _ _ _ Hu [] (e1 ++ e2) A). reflexivity.
  - (* tlam *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    constructor. apply (IHHS (EK k :: e1) e2 U0); simpl; auto.
    + rewrite Hg. reflexivity.
    + apply (weaken_ty _ _ _ Hu [] (e1 ++ e2) k). reflexivity.
  - (* other variable *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    econstructor; [| eapply IHHS; eauto].
    rewrite (get_var_remove e1 e2 U0); auto.
  - (* the substituted variable *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    match goal with Hv : get_var _ _ = Some ?A, Hsp : spine_ty _ ?A _ _ |- _ =>
      assert (A = U) by congruence; subst A end.
    apply IHHS2; auto.
    + apply kctx_remove.
    + eapply IHHS1; eauto.
  - intros e1 e2 U0 A T HΔ Hx Hg Hu Hs. inversion Hs; subst. constructor.
  - intros e1 e2 U0 A T HΔ Hx Hg Hu Hs. inversion Hs; subst.
    constructor; [eapply IHHS1 | eapply IHHS2]; eauto.
  - intros e1 e2 U0 A T HΔ Hx Hg Hu Hs. inversion Hs; subst.
    constructor; [rewrite <- kctx_remove with (U0 := U0); auto | eapply IHHS; eauto].
  - intros e T HΔ Hu Hs. inversion Hs; subst. auto.
  - intros e T HΔ Hu Hs. inversion Hu; subst. econstructor; eauto. eapply spine_app; eauto.
  - (* β *)
    intros e T HΔ Hu Hs. inversion Hu; subst. inversion Hs; subst.
    apply IHHS2; auto.
    apply (IHHS1 [] e A); simpl; auto.
  - (* type β *)
    intros e T HΔ Hu Hs. inversion Hu; subst. inversion Hs; subst.
    apply IHHS; auto.
    match goal with Hb : check (EK _ :: e) _ _ |- _ => apply (subst_ty _ _ _ Hb 0 C e) end.
    constructor. auto.
  - (* stuck: impossible on well-typed input *)
    intros e T HΔ Hu Hs. exfalso.
    destruct u as [A' b | k' b | y sp0]; destruct sp as [| t sp | C sp]; simpl in H; try tauto;
      inversion Hu; subst; inversion Hs; subst; try tauto.
    match goal with Hk : kinding _ C _ |- _ => destruct (kind_of_complete _ _ _ Hk) as [k0 [E Hk0]] end.
    destruct H as [H|[k1 [H Hlt]]]; rewrite H in E; try discriminate.
    injection E as ->. lia.
Qed.

(** ** The functions *)

Definition hsub (Δ:list kind) (U:typ) (u:nf) (x:nat) (t:nf) : nf :=
  match proj1_sig (hsub_total (CH Δ U u x t)) with rn r => r | rs _ => t end.

Definition happ (Δ:list kind) (U:typ) (u:nf) (sp:spine) : nf :=
  match proj1_sig (hsub_total (CA Δ U u sp)) with rn r => r | rs _ => u end.

(** Substituting [u : U] for the innermost variable preserves typing. *)
Theorem hsub_typed e U u t T :
  check (ET U :: e) t T -> check e u U -> check e (hsub (kctx e) U u 0 t) T.
Proof.
  intros Ht Hu. unfold hsub. destruct (hsub_total (CH (kctx e) U u 0 t)) as [[r|s] H]; simpl.
  - apply (HS_typed _ _ H [] e U); simpl; auto.
  - elim (HS_res_ok _ _ H).
Qed.

(** Applying [u : U] to a well-typed spine preserves typing. *)
Theorem happ_typed e U u sp T :
  check e u U -> spine_ty e U sp T -> check e (happ (kctx e) U u sp) T.
Proof.
  intros Hu Hs. unfold happ. destruct (hsub_total (CA (kctx e) U u sp)) as [[r|s] H]; simpl.
  - apply (HS_typed _ _ H e T); auto.
  - elim (HS_res_ok _ _ H).
Qed.

(** ** Normalization and consistency *)

Inductive term : Set :=
| var : nat -> term
| abs : typ -> term -> term
| app : term -> term -> term
| tabs : kind -> term -> term
| tapp : term -> typ -> term.

Inductive typing : env -> term -> typ -> Prop :=
| T_Var e x T : get_var e x = Some T -> typing e (var x) T
| T_Abs e A t B : typing (ET A :: e) t B -> typing e (abs A t) (arrow A B)
| T_App e t1 t2 A B : typing e t1 (arrow A B) -> typing e t2 A -> typing e (app t1 t2) B
| T_Tabs e k t B : typing (EK k :: e) t B -> typing e (tabs k t) (all k B)
| T_Tapp e t k B C : typing e t (all k B) -> kinding (kctx e) C k -> typing e (tapp t C) (tsubst B 0 C).

(** Every well-typed term has a normal form of the same type. *)
Theorem normalization : forall e t T, typing e t T -> exists n, check e n T.
Proof.
  intros e t T H. induction H.
  - exists (nne x snil). econstructor; eauto. constructor.
  - destruct IHtyping as [n Hn]. exists (nlam A n). constructor. auto.
  - destruct IHtyping1 as [n1 H1], IHtyping2 as [n2 H2].
    exists (happ (kctx e) (arrow A B) n1 (sapp n2 snil)).
    apply happ_typed; auto. constructor; auto. constructor.
  - destruct IHtyping as [n Hn]. exists (ntlam k n). constructor. auto.
  - destruct IHtyping as [n Hn].
    exists (happ (kctx e) (all k B) n (stapp C snil)).
    apply happ_typed; auto. econstructor; eauto. constructor.
Qed.

(** Consistency: the type [∀X:0. X] has no closed inhabitant. *)
Theorem consistency : forall t, ~ typing [] t (all 0 (tvar 0)).
Proof.
  intros t Ht. destruct (normalization _ _ _ Ht) as [n Hn].
  inversion Hn; subst; simpl in *; try discriminate.
  match goal with H : check (EK 0 :: []) _ (tvar 0) |- _ => inversion H; subst end.
  simpl in *. discriminate.
Qed.

(** ** Reduction, and the correctness of hereditary substitution

    Normal forms embed into raw terms ([emb]); hereditary substitution is
    correct in that ordinary substitution followed by β-reduction reaches
    the same normal form ([HS_red]).  Like typing preservation, this holds
    on well-typed input, where the stuck cases do not occur.  With it,
    every well-typed term reduces to a normal form of the same type
    ([normalization_red]). *)

Fixpoint shift_term (c:nat) (t:term) : term :=
  match t with
  | var y => var (if y <? c then y else S y)
  | abs A t => abs A (shift_term (S c) t)
  | app t1 t2 => app (shift_term c t1) (shift_term c t2)
  | tabs k t => tabs k (shift_term c t)
  | tapp t C => tapp (shift_term c t) C
  end.

Fixpoint tshift_term (X:nat) (t:term) : term :=
  match t with
  | var y => var y
  | abs A t => abs (tshift X A) (tshift_term X t)
  | app t1 t2 => app (tshift_term X t1) (tshift_term X t2)
  | tabs k t => tabs k (tshift_term (S X) t)
  | tapp t C => tapp (tshift_term X t) (tshift X C)
  end.

Fixpoint tsubst_term (t:term) (X:nat) (C:typ) : term :=
  match t with
  | var y => var y
  | abs A t => abs (tsubst A X C) (tsubst_term t X C)
  | app t1 t2 => app (tsubst_term t1 X C) (tsubst_term t2 X C)
  | tabs k t => tabs k (tsubst_term t (S X) (tshift 0 C))
  | tapp t D => tapp (tsubst_term t X C) (tsubst D X C)
  end.

(** [subst t x u] substitutes [u] for the term variable [x] in [t]. *)
Fixpoint subst (t:term) (x:nat) (u:term) : term :=
  match t with
  | var y => if y =? x then u else var (unshift x y)
  | abs A t => abs A (subst t (S x) (shift_term 0 u))
  | app t1 t2 => app (subst t1 x u) (subst t2 x u)
  | tabs k t => tabs k (subst t x (tshift_term 0 u))
  | tapp t C => tapp (subst t x u) C
  end.

Inductive red1 : term -> term -> Prop :=
| r_beta A t u : red1 (app (abs A t) u) (subst t 0 u)
| r_tbeta k t C : red1 (tapp (tabs k t) C) (tsubst_term t 0 C)
| r_abs A t t' : red1 t t' -> red1 (abs A t) (abs A t')
| r_app1 t1 t1' t2 : red1 t1 t1' -> red1 (app t1 t2) (app t1' t2)
| r_app2 t1 t2 t2' : red1 t2 t2' -> red1 (app t1 t2) (app t1 t2')
| r_tabs k t t' : red1 t t' -> red1 (tabs k t) (tabs k t')
| r_tapp t t' C : red1 t t' -> red1 (tapp t C) (tapp t' C).

Inductive reds : term -> term -> Prop :=
| reds_refl t : reds t t
| reds_step t t' t'' : red1 t t' -> reds t' t'' -> reds t t''.

Lemma reds_trans : forall t t' t'', reds t t' -> reds t' t'' -> reds t t''.
Proof. intros t t' t'' H. induction H; intros; auto. econstructor; eauto. Qed.

Lemma reds_one t t' : red1 t t' -> reds t t'.
Proof. intro H. econstructor; eauto. constructor. Qed.

Ltac reds_cong c :=
  let H := fresh in intro H; induction H; [constructor | econstructor; [apply c; eauto | eauto]].

Lemma reds_abs A t t' : reds t t' -> reds (abs A t) (abs A t').
Proof. reds_cong r_abs. Qed.
Lemma reds_tabs k t t' : reds t t' -> reds (tabs k t) (tabs k t').
Proof. reds_cong r_tabs. Qed.
Lemma reds_tapp C t t' : reds t t' -> reds (tapp t C) (tapp t' C).
Proof. reds_cong r_tapp. Qed.
Lemma reds_app1 u t t' : reds t t' -> reds (app t u) (app t' u).
Proof. reds_cong r_app1. Qed.
Lemma reds_app2 u t t' : reds t t' -> reds (app u t) (app u t').
Proof. reds_cong r_app2. Qed.

Lemma reds_app t t' u u' : reds t t' -> reds u u' -> reds (app t u) (app t' u').
Proof.
  intros H1 H2. apply reds_trans with (app t' u); [apply reds_app1 | apply reds_app2]; auto.
Qed.

(** *** Embedding normal forms *)

Fixpoint emb (t:nf) : term :=
  match t with
  | nlam A t => abs A (emb t)
  | ntlam k t => tabs k (emb t)
  | nne y sp => emb_sp (var y) sp
  end
with emb_sp (h:term) (sp:spine) : term :=
  match sp with
  | snil => h
  | sapp t sp => emb_sp (app h (emb t)) sp
  | stapp C sp => emb_sp (tapp h C) sp
  end.

Scheme nf_mut := Induction for nf Sort Prop
  with spine_mut := Induction for spine Sort Prop.

Lemma emb_sp_app : forall sp1 sp2 h, emb_sp h (sp_app sp1 sp2) = emb_sp (emb_sp h sp1) sp2.
Proof. induction sp1; intros sp2 h; simpl; auto. Qed.

Lemma reds_emb_sp : forall sp h h', reds h h' -> reds (emb_sp h sp) (emb_sp h' sp).
Proof.
  induction sp as [| t sp IH | C sp IH]; intros h h' H; simpl; auto.
  - apply IH. apply reds_app1. auto.
  - apply IH. apply reds_tapp. auto.
Qed.

Lemma shift_emb : forall t c, shift_term c (emb t) = emb (shift_tm c t).
Proof.
  apply (nf_mut (fun t => forall c, shift_term c (emb t) = emb (shift_tm c t))
                (fun sp => forall c h, shift_term c (emb_sp h sp) = emb_sp (shift_term c h) (shift_sp c sp)));
    intros; simpl; try (rewrite H0; simpl); try (rewrite H; simpl); try reflexivity.
Qed.

Lemma tshift_emb : forall t X, tshift_term X (emb t) = emb (tshift_tm X t).
Proof.
  apply (nf_mut (fun t => forall X, tshift_term X (emb t) = emb (tshift_tm X t))
                (fun sp => forall X h, tshift_term X (emb_sp h sp) = emb_sp (tshift_term X h) (tshift_sp X sp)));
    intros; simpl; try (rewrite H0; simpl); try (rewrite H; simpl); try reflexivity.
Qed.

Lemma tsubst_emb : forall t X C, tsubst_term (emb t) X C = emb (tsubst_tm t X C).
Proof.
  apply (nf_mut (fun t => forall X C, tsubst_term (emb t) X C = emb (tsubst_tm t X C))
                (fun sp => forall X C h, tsubst_term (emb_sp h sp) X C =
                                          emb_sp (tsubst_term h X C) (tsubst_sp sp X C)));
    intros; simpl; try (rewrite H0; simpl); try (rewrite H; simpl); try reflexivity.
Qed.

(** Substitution into an embedded spine, with the arguments substituted. *)
Fixpoint emb_sps (h:term) (sp:spine) (x:nat) (u:term) : term :=
  match sp with
  | snil => h
  | sapp t sp => emb_sps (app h (subst (emb t) x u)) sp x u
  | stapp C sp => emb_sps (tapp h C) sp x u
  end.

Lemma subst_emb_sp : forall sp h x u, subst (emb_sp h sp) x u = emb_sps (subst h x u) sp x u.
Proof. induction sp; intros h x u; simpl; auto. Qed.

(** *** Correctness *)

Definition rpost (c:call) (r:res) : Prop :=
  match c, r with
  | CH Δ U u x t, rn r =>
      forall e1 e2 U0 T, Δ = kctx (e1 ++ ET U0 :: e2) -> cntT e1 = x ->
        get_var (e1 ++ ET U0 :: e2) x = Some U -> check (e1 ++ e2) u U ->
        check (e1 ++ ET U0 :: e2) t T -> reds (subst (emb t) x (emb u)) (emb r)
  | CS Δ U u x sp, rs sp' =>
      forall e1 e2 U0 A T, Δ = kctx (e1 ++ ET U0 :: e2) -> cntT e1 = x ->
        get_var (e1 ++ ET U0 :: e2) x = Some U -> check (e1 ++ e2) u U ->
        spine_ty (e1 ++ ET U0 :: e2) A sp T ->
        forall h h', reds h h' -> reds (emb_sps h sp x (emb u)) (emb_sp h' sp')
  | CA Δ U u sp, rn r =>
      forall e T, Δ = kctx e -> check e u U -> spine_ty e U sp T -> reds (emb_sp (emb u) sp) (emb r)
  | _, _ => True
  end.

Theorem HS_red : forall c r, HS c r -> rpost c r.
Proof.
  intros c r H. induction H; simpl in *.
  - (* lam *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    apply reds_abs. rewrite shift_emb.
    match goal with Hb : check (ET A :: _) t ?B |- _ => apply (IHHS (ET A :: e1) e2 U0 B) end; simpl; auto.
    apply (weaken_tm _ _ _ Hu [] (e1 ++ e2) A). reflexivity.
  - (* tlam *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    apply reds_tabs. rewrite tshift_emb.
    match goal with Hb : check (EK k :: _) t ?B |- _ => apply (IHHS (EK k :: e1) e2 U0 B) end; simpl; auto.
    + rewrite Hg. reflexivity.
    + apply (weaken_ty _ _ _ Hu [] (e1 ++ e2) k). reflexivity.
  - (* other variable *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    rewrite subst_emb_sp. simpl.
    destruct (Nat.eqb_spec y (cntT e1)) as [E|E]; [congruence|].
    eapply IHHS; eauto. constructor.
  - (* the substituted variable *)
    intros e1 e2 U0 T HΔ Hx Hg Hu Ht. inversion Ht; subst.
    match goal with Hv : get_var _ _ = Some ?A, Hsp : spine_ty _ ?A _ _ |- _ =>
      assert (A = U) by congruence; subst A end.
    rewrite subst_emb_sp. simpl. rewrite Nat.eqb_refl.
    apply reds_trans with (emb_sp (emb u) sp').
    + eapply IHHS1; eauto. constructor.
    + apply IHHS2 with (e := e1 ++ e2) (T := T); auto.
      * apply kctx_remove.
      * apply (HS_typed _ _ H (e1) e2 U0 U T); eauto.
  - intros e1 e2 U0 A T HΔ Hx Hg Hu Hs h h' Hh. auto.
  - intros e1 e2 U0 A T HΔ Hx Hg Hu Hs h h' Hh. inversion Hs; subst.
    eapply IHHS2; eauto. apply reds_app; auto. eapply IHHS1; eauto.
  - intros e1 e2 U0 A T HΔ Hx Hg Hu Hs h h' Hh. inversion Hs; subst.
    eapply IHHS; eauto. apply reds_tapp. auto.
  - intros e T HΔ Hu Hs. constructor.
  - intros e T HΔ Hu Hs. simpl. rewrite emb_sp_app. constructor.
  - (* β *)
    intros e T HΔ Hu Hs. inversion Hu; subst. inversion Hs; subst. simpl.
    apply reds_trans with (emb_sp (subst (emb b) 0 (emb t)) sp).
    { apply reds_emb_sp. apply reds_one. constructor. }
    apply reds_trans with (emb_sp (emb r1) sp).
    { apply reds_emb_sp. apply (IHHS1 [] e A B); simpl; auto. }
    apply IHHS2 with (e := e) (T := T); auto.
    apply (HS_typed _ _ H [] e A); simpl; auto.
  - (* type β *)
    intros e T HΔ Hu Hs. inversion Hu; subst. inversion Hs; subst. simpl.
    apply reds_trans with (emb_sp (tsubst_term (emb b) 0 C) sp).
    { apply reds_emb_sp. apply reds_one. constructor. }
    rewrite tsubst_emb.
    apply IHHS with (e := e) (T := T); auto.
    match goal with Hb : check (EK _ :: e) _ _ |- _ => apply (subst_ty _ _ _ Hb 0 C e) end.
    constructor. auto.
  - (* stuck: impossible on well-typed input *)
    intros e T HΔ Hu Hs. exfalso.
    destruct u as [A' b | k' b | y sp0]; destruct sp as [| t sp | C sp]; simpl in H; try tauto;
      inversion Hu; subst; inversion Hs; subst; try tauto.
    match goal with Hk : kinding _ C _ |- _ => destruct (kind_of_complete _ _ _ Hk) as [k0 [E Hk0]] end.
    destruct H as [H|[k1 [H Hlt]]]; rewrite H in E; try discriminate.
    injection E as ->. lia.
Qed.

Theorem happ_red e U u sp T :
  check e u U -> spine_ty e U sp T -> reds (emb_sp (emb u) sp) (emb (happ (kctx e) U u sp)).
Proof.
  intros Hu Hs. unfold happ. destruct (hsub_total (CA (kctx e) U u sp)) as [[r|s] H]; simpl.
  - apply (HS_red _ _ H e T); auto.
  - elim (HS_res_ok _ _ H).
Qed.

(** Every well-typed term reduces to a normal form of the same type. *)
Theorem normalization_red : forall e t T, typing e t T ->
  exists n, check e n T /\ reds t (emb n).
Proof.
  intros e t T H. induction H.
  - exists (nne x snil). split; [econstructor; eauto; constructor | constructor].
  - destruct IHtyping as [n [Hn Hr]]. exists (nlam A n). split; [constructor; auto | apply reds_abs; auto].
  - destruct IHtyping1 as [n1 [H1 R1]], IHtyping2 as [n2 [H2 R2]].
    assert (Hs : spine_ty e (arrow A B) (sapp n2 snil) B) by (constructor; auto; constructor).
    exists (happ (kctx e) (arrow A B) n1 (sapp n2 snil)). split.
    + apply happ_typed; auto.
    + apply reds_trans with (app (emb n1) (emb n2)); [apply reds_app; auto|].
      change (app (emb n1) (emb n2)) with (emb_sp (emb n1) (sapp n2 snil)).
      apply (happ_red e _ _ _ B); auto.
  - destruct IHtyping as [n [Hn Hr]]. exists (ntlam k n). split; [constructor; auto | apply reds_tabs; auto].
  - destruct IHtyping as [n [Hn Hr]].
    assert (Hs : spine_ty e (all k B) (stapp C snil) (tsubst B 0 C)) by (econstructor; eauto; constructor).
    exists (happ (kctx e) (all k B) n (stapp C snil)). split.
    + apply happ_typed; auto.
    + apply reds_trans with (tapp (emb n) C); [apply reds_tapp; auto|].
      change (tapp (emb n) C) with (emb_sp (emb n) (stapp C snil)).
      apply (happ_red e _ _ _ (tsubst B 0 C)); auto.
Qed.
