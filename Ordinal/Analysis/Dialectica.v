From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From Ordinal Require Import Analysis.SystemTCL.
From Ordinal Require Import Analysis.PeanoArith.

Open Scope nat_scope.

(** * Consistency of Peano arithmetic by Gödel's Dialectica interpretation

    Gödel's functional interpretation carries Heyting arithmetic into
    the quantifier-free theory of the functionals of System T: from a
    proof of [A] it extracts a term [t] such that the quantifier-free
    matrix [A_D(t, y)] holds for every [y].  With the negative
    translation ([PeanoArith]), a proof of [⊥] in Peano arithmetic would
    give a closed term making [⊥_D] true, which is impossible.

    The interpretation targets combinatory T with pairs ([SystemTCL]).
    The quantifier-free matrices are terms of type [N], read as true when
    they reduce to [0], and their variables range over closed terms of
    the right types.  What makes this work is [T_value]: every closed
    term of type [N] has a unique numeral value, which decides the
    matrices (needed for contraction) and drives the recursor in the
    induction rule.  [T_value] rests on strong normalization, which
    [SystemTCL] proves by an ordinal assignment below ε₀.

    The predicate variable [X] of [PeanoArith] is read as the empty set:
    its atoms are interpreted like [⊥]. *)

(** ** Terms with free variables

    Terms of T have no binders, so substitution is a plain map over the
    variables. *)

Fixpoint tsub (ρ:nat -> term) (M:term) : term :=
  match M with
  | var i => ρ i
  | app A M N => app A (tsub ρ M) (tsub ρ N)
  | _ => M
  end.

Lemma tsub_ext ρ ρ' M : (forall i, ρ i = ρ' i) -> tsub ρ M = tsub ρ' M.
Proof. intro H. induction M; simpl; f_equal; auto. Qed.

Lemma tsub_comp σ ρ M : tsub σ (tsub ρ M) = tsub (fun i => tsub σ (ρ i)) M.
Proof. induction M; simpl; f_equal; auto. Qed.

Lemma tsub_num ρ n : tsub ρ (num n) = num n.
Proof. induction n; simpl; f_equal; auto. Qed.

Fixpoint prepend {X:Type} (l:list X) (f:nat -> X) (i:nat) : X :=
  match l, i with
  | [], _ => f i
  | a :: _, O => a
  | _ :: l, S i => prepend l f i
  end.

Lemma prepend_lt {X} (l:list X) f i d : i < length l -> prepend l f i = nth i l d.
Proof.
  revert i. induction l as [|a l IH]; intros i Hi; simpl in *; [lia|].
  destruct i; auto. apply IH. lia.
Qed.

Lemma prepend_ge {X} (l:list X) f j : prepend l f (length l + j) = f j.
Proof. induction l; simpl; auto. Qed.

Lemma prepend_ge' {X} (l:list X) f i : length l <= i -> prepend l f i = f (i - length l).
Proof. intro H. replace i with (length l + (i - length l)) at 1 by lia. apply prepend_ge. Qed.

Lemma prepend_app {X} (l1 l2:list X) f i : prepend (l1 ++ l2) f i = prepend l1 (prepend l2 f) i.
Proof. revert i. induction l1; intro i; simpl; auto. destruct i; auto. Qed.

(** Typing with a context that assigns a type to every variable. *)
Inductive wt (Γ:nat -> ty) : term -> ty -> Prop :=
| wt_var i : wt Γ (var i) (Γ i)
| wt_K A B : wt Γ (Kc A B) (TAr A (TAr B A))
| wt_S A B C : wt Γ (Sc A B C) (TAr (TAr A (TAr B C)) (TAr (TAr A B) (TAr A C)))
| wt_Z : wt Γ Zc TN
| wt_Suc : wt Γ Suc (TAr TN TN)
| wt_R C : wt Γ (Rc C) (TAr TN (TAr C (TAr (TAr TN (TAr C C)) C)))
| wt_P A B : wt Γ (Pc A B) (TAr A (TAr B (TPr A B)))
| wt_P1 A B : wt Γ (P1c A B) (TAr (TPr A B) A)
| wt_P2 A B : wt Γ (P2c A B) (TAr (TPr A B) B)
| wt_app A B M N : wt Γ M (TAr A B) -> wt Γ N A -> wt Γ (app A M N) B.

Lemma wt_var' Γ i A : Γ i = A -> wt Γ (var i) A.
Proof. intros <-. constructor. Qed.

Lemma wt_tsub Γ Δ ρ M A : wt Γ M A -> (forall i, wt Δ (ρ i) (Γ i)) -> wt Δ (tsub ρ M) A.
Proof. intros H Hρ. induction H; simpl; eauto using wt. Qed.

Lemma wt_typing Γ ρ M A : wt Γ M A -> (forall i, typing [] (ρ i) (Γ i)) -> typing [] (tsub ρ M) A.
Proof. intros H Hρ. induction H; simpl; eauto using typing. Qed.

Lemma typing_wt M A : typing [] M A -> forall Γ, wt Γ M A.
Proof.
  intros H Γ. induction H; eauto using wt.
  destruct x; discriminate.
Qed.

Lemma typing_closed M A : typing [] M A -> forall ρ, tsub ρ M = M.
Proof.
  intros H ρ. induction H; simpl; auto.
  - destruct x; discriminate.
  - f_equal; auto.
Qed.

Lemma prepend_typing (xs:list term) (Ts:list ty) (ns:nat -> term) (f:nat -> ty) :
  Forall2 (fun x T => typing [] x T) xs Ts -> (forall j, typing [] (ns j) (f j)) ->
  forall i, typing [] (prepend xs ns i) (prepend Ts f i).
Proof. intros H Hn. induction H; intro i; simpl; auto. destruct i; auto. Qed.

(** ** Bracket abstraction *)

Fixpoint infer (Γ:nat -> ty) (M:term) : option ty :=
  match M with
  | var i => Some (Γ i)
  | Kc A B => Some (TAr A (TAr B A))
  | Sc A B C => Some (TAr (TAr A (TAr B C)) (TAr (TAr A B) (TAr A C)))
  | Zc => Some TN
  | Suc => Some (TAr TN TN)
  | Rc C => Some (TAr TN (TAr C (TAr (TAr TN (TAr C C)) C)))
  | Pc A B => Some (TAr A (TAr B (TPr A B)))
  | P1c A B => Some (TAr (TPr A B) A)
  | P2c A B => Some (TAr (TPr A B) B)
  | app _ M _ => match infer Γ M with Some (TAr _ B) => Some B | _ => None end
  end.

Lemma infer_wt Γ M A : wt Γ M A -> infer Γ M = Some A.
Proof. induction 1; simpl; auto. rewrite IHwt1. reflexivity. Qed.

Definition tyof (Γ:nat -> ty) (M:term) : ty :=
  match infer Γ M with Some A => A | None => TN end.

(** [Kt T A M = λ_:A. M] and the identity [I]. *)
Definition Kt (T A:ty) (M:term) : term := app T (Kc T A) M.

Definition It (A:ty) : term :=
  app (TAr A (TAr A A)) (app (TAr A (TAr (TAr A A) A)) (Sc A (TAr A A) A) (Kc A (TAr A A))) (Kc A A).

Definition rem (j:nat) (Γ:nat -> ty) : nat -> ty :=
  fun i => if i <? j then Γ i else Γ (S i).

Definition ins {X:Type} (j:nat) (a:X) (f:nat -> X) : nat -> X :=
  fun i => if i <? j then f i else if i =? j then a else f (pred i).

(** [lam_at Γ j M] abstracts the variable [j] of [M]. *)
Fixpoint lam_at (Γ:nat -> ty) (j:nat) (M:term) : term :=
  match M with
  | var i => if i =? j then It (Γ j) else Kt (Γ i) (Γ j) (var (if i <? j then i else pred i))
  | app B P Q =>
      app (TAr (Γ j) B) (app (TAr (Γ j) (TAr B (tyof Γ M))) (Sc (Γ j) B (tyof Γ M)) (lam_at Γ j P))
          (lam_at Γ j Q)
  | _ => Kt (tyof Γ M) (Γ j) M
  end.

Lemma wt_It Γ A : wt Γ (It A) (TAr A A).
Proof. unfold It. repeat econstructor. Qed.

Lemma wt_Kt Γ T A M : wt Γ M T -> wt Γ (Kt T A M) (TAr A T).
Proof. intro H. unfold Kt. repeat econstructor. exact H. Qed.

Lemma wt_lam_at Γ j M T : wt Γ M T -> wt (rem j Γ) (lam_at Γ j M) (TAr (Γ j) T).
Proof.
  induction 1 as [i | | | | | | | | | A B M N HM IHM HN IHN]; simpl;
    try (apply wt_Kt; unfold tyof; simpl; constructor).
  - destruct (Nat.eqb_spec i j) as [->|Hij]; [apply wt_It|].
    apply wt_Kt, wt_var'. unfold rem.
    destruct (Nat.ltb_spec i j) as [Hlt|Hge]; cbv beta iota.
    + assert (E : (i <? j) = true) by (apply Nat.ltb_lt; auto). rewrite E. reflexivity.
    + assert (E : (pred i <? j) = false) by (apply Nat.ltb_ge; lia). rewrite E. f_equal. lia.
  - unfold tyof. rewrite (infer_wt _ _ _ (wt_app _ _ _ _ _ HM HN)).
    econstructor; [econstructor; [constructor | exact IHM] | exact IHN].
Qed.

Lemma star_It X A N : star (app X (It A) N) N.
Proof.
  unfold It. eapply star_step; [apply st_S|]. eapply star_step; [apply st_K|]. apply star_refl.
Qed.

Lemma star_lam_at Γ j M : forall ρ X N, star (app X (tsub ρ (lam_at Γ j M)) N) (tsub (ins j N ρ) M).
Proof.
  induction M as [i| | | | | | | | |B P IHP Q IHQ]; intros ρ X N; simpl;
    try (eapply star_step; [apply st_K | apply star_refl]).
  - unfold ins. destruct (Nat.eqb_spec i j) as [->|Hij].
    + rewrite Nat.ltb_irrefl. apply star_It.
    + simpl. eapply star_step; [apply st_K|].
      destruct (Nat.ltb_spec i j).
      * apply star_refl.
      * destruct (Nat.eqb_spec i j); [lia|].
        destruct (Nat.ltb_spec (pred i) j); [lia|]. apply star_refl.
  - eapply star_step; [apply st_S|]. apply star_app; auto.
Qed.

Lemma star_tsub ρ ρ' M : (forall i, star (ρ i) (ρ' i)) -> star (tsub ρ M) (tsub ρ' M).
Proof. intro H. induction M; simpl; auto using star_refl, star_app. Qed.

(** ** Evaluation

    A closed term of type [N] is read as true when it reduces to [0]. *)

Definition holds (M:term) : Prop := star M (num 0).

Lemma num_inj n m : num n = num m -> n = m.
Proof. intro H. apply (f_equal is_num) in H. rewrite !is_num_num in H. congruence. Qed.

Lemma star_from_num n N : star (num n) N -> N = num n.
Proof. apply star_normal. intros N' H. eapply num_normal; eauto. Qed.

Lemma star_num_unique M n m : star M (num n) -> star M (num m) -> n = m.
Proof.
  intros H1 H2. destruct (confluence _ _ _ H1 H2) as [P [HP1 HP2]].
  apply star_from_num in HP1. apply star_from_num in HP2. apply num_inj. congruence.
Qed.

Lemma evals_star M M' n : star M M' -> (star M (num n) <-> star M' (num n)).
Proof.
  intro H. split; intro Hn.
  - destruct (confluence _ _ _ H Hn) as [P [HP1 HP2]].
    apply star_from_num in HP2. subst. exact HP1.
  - eapply star_trans; eauto.
Qed.

Lemma holds_star M M' : star M M' -> (holds M <-> holds M').
Proof. apply evals_star. Qed.

Lemma T_eval M : typing [] M TN -> exists n, star M (num n).
Proof. intro H. destruct (T_value _ H) as [n [Hn _]]. eauto. Qed.

Lemma holds_dec M : typing [] M TN -> holds M \/ (exists m, star M (num (S m))).
Proof. intro H. destruct (T_eval _ H) as [[|m] Hm]; eauto. Qed.

Lemma not_holds M m : star M (num (S m)) -> ~ holds M.
Proof. intros H1 H2. pose proof (star_num_unique _ _ _ H1 H2). discriminate. Qed.

(** ** Pairs, definition by cases and arithmetic *)

Definition tpair (A B:ty) (a b:term) : term := app B (app A (Pc A B) a) b.
Definition pi1 (A B:ty) (M:term) : term := app (TPr A B) (P1c A B) M.
Definition pi2 (A B:ty) (M:term) : term := app (TPr A B) (P2c A B) M.

Lemma star_pi1 A B C D a b : star (pi1 A B (tpair C D a b)) a.
Proof. apply star_one, st_P1. Qed.

Lemma star_pi2 A B C D a b : star (pi2 A B (tpair C D a b)) b.
Proof. apply star_one, st_P2. Qed.

Lemma star_pi1' A B M a b C D : star M (tpair C D a b) -> star (pi1 A B M) a.
Proof. intro H. eapply star_trans; [apply star_app_r, H | apply star_pi1]. Qed.

Lemma star_pi2' A B M a b C D : star M (tpair C D a b) -> star (pi2 A B M) b.
Proof. intro H. eapply star_trans; [apply star_app_r, H | apply star_pi2]. Qed.

Lemma wt_tpair Γ A B a b : wt Γ a A -> wt Γ b B -> wt Γ (tpair A B a b) (TPr A B).
Proof. intros. unfold tpair. repeat econstructor; eauto. Qed.

Lemma wt_pi1 Γ A B M : wt Γ M (TPr A B) -> wt Γ (pi1 A B M) A.
Proof. intros. unfold pi1. repeat econstructor; eauto. Qed.

Lemma wt_pi2 Γ A B M : wt Γ M (TPr A B) -> wt Γ (pi2 A B M) B.
Proof. intros. unfold pi2. repeat econstructor; eauto. Qed.

(** [cond σ z a b] is [a] if [z = 0], and [b] otherwise. *)
Definition cond (σ:ty) (z a b:term) : term :=
  app (TAr TN (TAr σ σ)) (app σ (app TN (Rc σ) z) a) (Kt (TAr σ σ) TN (Kt σ σ b)).

Lemma wt_cond Γ σ z a b : wt Γ z TN -> wt Γ a σ -> wt Γ b σ -> wt Γ (cond σ z a b) σ.
Proof. intros. unfold cond, Kt. repeat econstructor; eauto. Qed.

Lemma cond_0 σ z a b : star z (num 0) -> star (cond σ z a b) a.
Proof.
  intro H. eapply star_trans; [apply star_app_l, star_app_l, star_app_r, H|].
  apply star_one, st_R0. reflexivity.
Qed.

Lemma cond_S σ z a b m : star z (num (S m)) -> star (cond σ z a b) b.
Proof.
  intro H. eapply star_trans; [apply star_app_l, star_app_l, star_app_r, H|].
  eapply star_step; [apply st_RS; apply is_num_num|].
  eapply star_step; [apply st_l, st_K|]. eapply star_step; [apply st_K|]. apply star_refl.
Qed.

Definition recN (y x g:term) : term := app (TAr TN (TAr TN TN)) (app TN (app TN (Rc TN) y) x) g.

Lemma wt_recN Γ y x g : wt Γ y TN -> wt Γ x TN -> wt Γ g (TAr TN (TAr TN TN)) -> wt Γ (recN y x g) TN.
Proof. intros. unfold recN. repeat econstructor; eauto. Qed.

Lemma recN_star y y' x x' g : star y y' -> star x x' -> star (recN y x g) (recN y' x' g).
Proof. intros. unfold recN. apply star_app_l, star_app; auto. apply star_app_r. auto. Qed.

Lemma recN_0 x g : star (recN (num 0) x g) x.
Proof. apply star_one, st_R0. reflexivity. Qed.

Lemma recN_S n x f : star (recN (num (S n)) x (Kt (TAr TN TN) TN f))
                            (app TN f (recN (num n) x (Kt (TAr TN TN) TN f))).
Proof.
  eapply star_step; [apply st_RS; apply is_num_num|].
  eapply star_step; [apply st_l, st_K|]. apply star_refl.
Qed.

Definition addT (x y:term) : term := recN y x (Kt (TAr TN TN) TN Suc).

Definition TN0 : nat -> ty := fun _ => TN.

(** [ADDR x w = w + x], [PREDF n = n - 1]. *)
Definition ADDR : term := lam_at TN0 0 (lam_at TN0 0 (addT (var 0) (var 1))).
Definition predT (n:term) : term := recN n Zc (Kc TN TN).
Definition PREDF : term := lam_at TN0 0 (predT (var 0)).

Definition mulT (x y:term) : term := recN y Zc (Kt (TAr TN TN) TN (app TN ADDR x)).
Definition subT (x y:term) : term := recN y x (Kt (TAr TN TN) TN PREDF).
Definition eqT (x y:term) : term := addT (subT x y) (subT y x).

Lemma wt_addT Γ x y : wt Γ x TN -> wt Γ y TN -> wt Γ (addT x y) TN.
Proof. intros. unfold addT, Kt. apply wt_recN; repeat econstructor; auto. Qed.

Lemma wt_ext Γ Δ M A : (forall i, Γ i = Δ i) -> wt Γ M A -> wt Δ M A.
Proof. intros E H. induction H; try rewrite E; eauto using wt. Qed.

Lemma tsub_id M : tsub var M = M.
Proof. induction M; simpl; f_equal; auto. Qed.

(** Closed terms typed in [TN0] are typed everywhere. *)
Lemma wt_TN0_closed Γ M A : wt TN0 M A -> (forall ρ, tsub ρ M = M) -> wt Γ M A.
Proof.
  intros H Hc. rewrite <- (Hc (fun _ => Zc)). apply typing_wt.
  apply (wt_typing TN0); auto. intro. constructor.
Qed.

Lemma wt_ADDR Γ : wt Γ ADDR (TAr TN (TAr TN TN)).
Proof.
  apply wt_TN0_closed; [|reflexivity].
  apply (wt_ext (rem 0 TN0)); [reflexivity|]. apply wt_lam_at.
  apply (wt_ext (rem 0 TN0)); [reflexivity|]. apply wt_lam_at.
  apply wt_addT; constructor.
Qed.

Lemma wt_predT Γ n : wt Γ n TN -> wt Γ (predT n) TN.
Proof. intros. unfold predT. apply wt_recN; repeat constructor; auto. Qed.

Lemma wt_PREDF Γ : wt Γ PREDF (TAr TN TN).
Proof.
  apply wt_TN0_closed; [|reflexivity].
  apply (wt_ext (rem 0 TN0)); [reflexivity|]. apply wt_lam_at.
  apply wt_predT; constructor.
Qed.

Lemma wt_mulT Γ x y : wt Γ x TN -> wt Γ y TN -> wt Γ (mulT x y) TN.
Proof.
  intros. unfold mulT, Kt. apply wt_recN; [auto | constructor |].
  eapply wt_app; [constructor | eapply wt_app; [apply wt_ADDR | auto]].
Qed.

Lemma wt_subT Γ x y : wt Γ x TN -> wt Γ y TN -> wt Γ (subT x y) TN.
Proof.
  intros. unfold subT, Kt. apply wt_recN; auto.
  eapply wt_app; [constructor | apply wt_PREDF].
Qed.

Lemma wt_eqT Γ x y : wt Γ x TN -> wt Γ y TN -> wt Γ (eqT x y) TN.
Proof. intros. unfold eqT. apply wt_addT; apply wt_subT; auto. Qed.

(** Their values. *)
Lemma addT_num m k : star (addT (num m) (num k)) (num (m + k)).
Proof.
  induction k as [|k IH].
  - rewrite Nat.add_0_r. apply recN_0.
  - eapply star_trans; [apply recN_S|]. rewrite Nat.add_succ_r. apply star_app_r, IH.
Qed.

Lemma addT_eval x y m k : star x (num m) -> star y (num k) -> star (addT x y) (num (m + k)).
Proof. intros. eapply star_trans; [apply recN_star; eauto | apply addT_num]. Qed.

Lemma ADDR_eval X Y x w : star (app X (app Y ADDR x) w) (addT w x).
Proof.
  rewrite <- (tsub_id ADDR). unfold ADDR.
  eapply star_trans; [apply star_app_l, star_lam_at|].
  apply (star_lam_at TN0 0 (addT (var 0) (var 1))).
Qed.

Lemma mulT_num m k : star (mulT (num m) (num k)) (num (m * k)).
Proof.
  induction k as [|k IH].
  - rewrite Nat.mul_0_r. apply recN_0.
  - eapply star_trans; [apply recN_S|]. eapply star_trans; [apply ADDR_eval|].
    rewrite Nat.mul_succ_r. apply addT_eval; [exact IH | apply star_refl].
Qed.

Lemma mulT_eval x y m k : star x (num m) -> star y (num k) -> star (mulT x y) (num (m * k)).
Proof.
  intros Hx Hy. unfold mulT. eapply star_trans; [apply recN_star; [exact Hy | apply star_refl]|].
  eapply star_trans; [|apply mulT_num]. unfold mulT, recN, Kt.
  apply star_app_r, star_app_r, star_app_r, Hx.
Qed.

Lemma predT_num n : star (predT (num n)) (num (pred n)).
Proof.
  destruct n as [|n].
  - apply recN_0.
  - eapply star_step; [apply st_RS; apply is_num_num|].
    eapply star_step; [apply st_K|]. apply star_refl.
Qed.

Lemma PREDF_eval X x n : star x (num n) -> star (app X PREDF x) (num (pred n)).
Proof.
  intro H. rewrite <- (tsub_id PREDF). unfold PREDF.
  eapply star_trans; [apply (star_lam_at TN0 0 (predT (var 0)) var)|].
  simpl. eapply star_trans; [apply recN_star; [exact H | apply star_refl] | apply predT_num].
Qed.

Lemma subT_num m k : star (subT (num m) (num k)) (num (m - k)).
Proof.
  induction k as [|k IH].
  - rewrite Nat.sub_0_r. apply recN_0.
  - eapply star_trans; [apply recN_S|]. eapply star_trans; [apply PREDF_eval, IH|].
    replace (m - S k) with (pred (m - k)) by lia. apply star_refl.
Qed.

Lemma subT_eval x y m k : star x (num m) -> star y (num k) -> star (subT x y) (num (m - k)).
Proof. intros. eapply star_trans; [apply recN_star; eauto | apply subT_num]. Qed.

Lemma eqT_eval x y m k : star x (num m) -> star y (num k) ->
  exists d, star (eqT x y) (num d) /\ (d = 0 <-> m = k).
Proof.
  intros Hx Hy. exists ((m - k) + (k - m)). split; [|lia].
  apply addT_eval; apply subT_eval; auto.
Qed.

(** Arithmetic terms as terms of T. *)
Fixpoint tr (t:aterm) : term :=
  match t with
  | tv i => var i
  | tz => Zc
  | ts t => app TN Suc (tr t)
  | tplus a b => addT (tr a) (tr b)
  | tmult a b => mulT (tr a) (tr b)
  end.

Lemma tsub_addT ρ x y : tsub ρ (addT x y) = addT (tsub ρ x) (tsub ρ y).
Proof. reflexivity. Qed.

Lemma tsub_mulT ρ x y : tsub ρ (mulT x y) = mulT (tsub ρ x) (tsub ρ y).
Proof. reflexivity. Qed.

Lemma tsub_eqT ρ x y : tsub ρ (eqT x y) = eqT (tsub ρ x) (tsub ρ y).
Proof. reflexivity. Qed.

Lemma tsub_cond ρ σ z a b : tsub ρ (cond σ z a b) = cond σ (tsub ρ z) (tsub ρ a) (tsub ρ b).
Proof. reflexivity. Qed.

Lemma tr_asubst σ t : tr (asubst σ t) = tsub (fun i => tr (σ i)) (tr t).
Proof.
  induction t; cbn [tr asubst]; auto.
  - simpl. f_equal. auto.
  - rewrite tsub_addT. f_equal; auto.
  - rewrite tsub_mulT. f_equal; auto.
Qed.

Lemma wt_tr Γ t : (forall i, Γ i = TN) -> wt Γ (tr t) TN.
Proof.
  intro H. induction t; simpl.
  - apply wt_var'. auto.
  - constructor.
  - repeat econstructor. auto.
  - apply wt_addT; auto.
  - apply wt_mulT; auto.
Qed.

Definition Ns (ns:nat -> term) : Prop := forall j, typing [] (ns j) TN.

Lemma typing_tr ns t : Ns ns -> typing [] (tsub ns (tr t)) TN.
Proof. intro H. apply (wt_typing TN0); auto. apply wt_tr. reflexivity. Qed.

(** ** The Dialectica interpretation

    [wty A] is the type of witnesses of [A], [cty A] the type of its
    counterexamples, and [dia A] the quantifier-free matrix [A_D]: a term
    of type [N] whose variable [0] is the counterexample, variable [1]
    the witness, and variables [2 + j] the free number variables of
    [A]. *)

Fixpoint wty (A:form) : ty :=
  match A with
  | Eq _ _ => TN
  | Bot => TN
  | And A B => TPr (wty A) (wty B)
  | Or A B => TPr TN (TPr (wty A) (wty B))
  | Imp A B => TPr (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A)))
  | All A => TAr TN (wty A)
  | Ex A => TPr TN (wty A)
  | PX _ => TN
  end
with cty (A:form) : ty :=
  match A with
  | Eq _ _ => TN
  | Bot => TN
  | And A B => TPr (cty A) (cty B)
  | Or A B => TPr (cty A) (cty B)
  | Imp A B => TPr (wty A) (cty B)
  | All A => TPr TN (cty A)
  | Ex A => cty A
  | PX _ => TN
  end.

Lemma wty_cty_subst A : forall σ, wty (fsubst σ A) = wty A /\ cty (fsubst σ A) = cty A.
Proof.
  induction A; intro σ; simpl; auto;
    try (destruct (IHA1 σ) as [-> ->]; destruct (IHA2 σ) as [-> ->]; auto);
    destruct (IHA (up σ)) as [-> ->]; auto.
Qed.

Lemma wty_subst A σ : wty (fsubst σ A) = wty A.
Proof. apply wty_cty_subst. Qed.

Lemma cty_subst A σ : cty (fsubst σ A) = cty A.
Proof. apply wty_cty_subst. Qed.

Definition dsub {X:Type} (y x:X) (f:nat -> X) : nat -> X :=
  fun i => match i with O => y | 1 => x | S (S j) => f j end.

Definition nvars : nat -> term := fun j => var (S (S j)).

Fixpoint dia (A:form) : term :=
  match A with
  | Eq s t => eqT (tsub nvars (tr s)) (tsub nvars (tr t))
  | Bot => num 1
  | And A B =>
      addT (tsub (dsub (pi1 (cty A) (cty B) (var 0)) (pi1 (wty A) (wty B) (var 1)) nvars) (dia A))
           (tsub (dsub (pi2 (cty A) (cty B) (var 0)) (pi2 (wty A) (wty B) (var 1)) nvars) (dia B))
  | Or A B =>
      cond TN (pi1 TN (TPr (wty A) (wty B)) (var 1))
        (tsub (dsub (pi1 (cty A) (cty B) (var 0))
                    (pi1 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) (var 1))) nvars) (dia A))
        (tsub (dsub (pi2 (cty A) (cty B) (var 0))
                    (pi2 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) (var 1))) nvars) (dia B))
  | Imp A B =>
      let a := pi1 (wty A) (cty B) (var 0) in
      let v := pi2 (wty A) (cty B) (var 0) in
      let f := pi1 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) (var 1) in
      let g := pi2 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) (var 1) in
      cond TN (tsub (dsub (app (cty B) (app (wty A) g a) v) a nvars) (dia A))
              (tsub (dsub v (app (wty A) f a) nvars) (dia B)) Zc
  | All A =>
      tsub (dsub (pi2 TN (cty A) (var 0)) (app TN (var 1) (pi1 TN (cty A) (var 0)))
                 (prepend [pi1 TN (cty A) (var 0)] nvars)) (dia A)
  | Ex A =>
      tsub (dsub (var 0) (pi2 TN (wty A) (var 1)) (prepend [pi1 TN (wty A) (var 1)] nvars)) (dia A)
  | PX _ => num 1
  end.

Definition dctx (A:form) : nat -> ty := dsub (cty A) (wty A) TN0.

Ltac wtac :=
  repeat match goal with
  | |- wt _ (nvars _) _ => unfold nvars; apply wt_var'; reflexivity
  | |- wt _ (var _) _ => apply wt_var'; reflexivity
  | |- wt _ (pi1 _ _ _) _ => eapply wt_pi1
  | |- wt _ (pi2 _ _ _) _ => eapply wt_pi2
  | |- wt _ (tpair _ _ _ _) _ => eapply wt_tpair
  | |- wt _ (app _ _ _) _ => econstructor
  | |- wt _ _ _ => constructor
  end.

Lemma wt_dia A : wt (dctx A) (dia A) TN.
Proof.
  induction A; simpl.
  - apply wt_eqT; apply (wt_tsub TN0); try (apply wt_tr; reflexivity); intro; wtac.
  - repeat constructor.
  - apply wt_addT; (eapply wt_tsub; [eauto|]); intros [|[|j]]; simpl; wtac.
  - apply wt_cond; [wtac| |]; (eapply wt_tsub; [eauto|]); intros [|[|j]]; simpl; wtac.
  - apply wt_cond; [| |constructor]; (eapply wt_tsub; [eauto|]); intros [|[|j]]; simpl; wtac.
  - eapply wt_tsub; [eauto|]. intros [|[|[|j]]]; simpl; wtac.
  - eapply wt_tsub; [eauto|]. intros [|[|[|j]]]; simpl; wtac.
  - repeat constructor.
Qed.

(** ** Truth of the matrix on closed instances *)

Definition Dsem (A:form) (x y:term) (ns:nat -> term) : Prop :=
  holds (tsub (dsub y x ns) (dia A)).

Definition DT (A:form) (x y:term) (ns:nat -> term) : Prop :=
  typing [] x (wty A) /\ typing [] y (cty A) /\ Ns ns.

Lemma dia_typing A x y ns : DT A x y ns -> typing [] (tsub (dsub y x ns) (dia A)) TN.
Proof. intros [Hx [Hy Hn]]. apply (wt_typing (dctx A)); [apply wt_dia|]. intros [|[|j]]; simpl; auto. Qed.

Lemma tsub_dsub σ Y X NF M :
  tsub σ (tsub (dsub Y X NF) M) = tsub (dsub (tsub σ Y) (tsub σ X) (fun j => tsub σ (NF j))) M.
Proof. rewrite tsub_comp. apply tsub_ext. intros [|[|j]]; reflexivity. Qed.

Lemma Dsem_star A x x' y y' ns ns' :
  star x x' -> star y y' -> (forall j, star (ns j) (ns' j)) -> (Dsem A x y ns <-> Dsem A x' y' ns').
Proof. intros. apply holds_star, star_tsub. intros [|[|j]]; simpl; auto. Qed.

Lemma Dsem_ext A x y ns ns' : (forall j, ns j = ns' j) -> (Dsem A x y ns <-> Dsem A x y ns').
Proof. intro E. unfold Dsem. rewrite (tsub_ext _ (dsub y x ns')); [reflexivity|]. intros [|[|j]]; simpl; auto. Qed.

Lemma holds_addT p q : typing [] p TN -> typing [] q TN -> (holds (addT p q) <-> holds p /\ holds q).
Proof.
  intros Hp Hq. destruct (T_eval _ Hp) as [m Hm]. destruct (T_eval _ Hq) as [k Hk].
  pose proof (addT_eval _ _ _ _ Hm Hk) as Ha. unfold holds. split.
  - intro H. pose proof (star_num_unique _ _ _ Ha H).
    assert (m = 0) by lia. assert (k = 0) by lia. subst. auto.
  - intros [H1 H2]. rewrite (star_num_unique _ _ _ Hm H1), (star_num_unique _ _ _ Hk H2) in Ha. exact Ha.
Qed.

Lemma holds_cond z p q : typing [] z TN ->
  (holds (cond TN z p q) <-> (holds z /\ holds p) \/ ((exists m, star z (num (S m))) /\ holds q)).
Proof.
  intro Hz. destruct (holds_dec _ Hz) as [H0|[m Hm]].
  - rewrite (holds_star _ _ (cond_0 _ _ _ _ H0)). split; [auto|].
    intros [[_ H]|[[m Hm] _]]; auto. elim (not_holds _ _ Hm H0).
  - rewrite (holds_star _ _ (cond_S _ _ _ _ _ Hm)). split; [eauto|].
    intros [[H _]|[_ H]]; auto. elim (not_holds _ _ Hm H).
Qed.

Lemma holds_imp p q : typing [] p TN -> (holds (cond TN p q Zc) <-> (holds p -> holds q)).
Proof.
  intro Hp. rewrite holds_cond by auto. split.
  - intros [[_ H]|[[m Hm] _]] H'; auto. elim (not_holds _ _ Hm H').
  - intro H. destruct (holds_dec _ Hp) as [H0|Hm]; auto. right. split; auto. apply star_refl.
Qed.

Lemma typing_pi1 A B M : typing [] M (TPr A B) -> typing [] (pi1 A B M) A.
Proof. intro. unfold pi1. repeat econstructor. auto. Qed.

Lemma typing_pi2 A B M : typing [] M (TPr A B) -> typing [] (pi2 A B M) B.
Proof. intro. unfold pi2. repeat econstructor. auto. Qed.

Lemma Ns_cons z ns : typing [] z TN -> Ns ns -> Ns (prepend [z] ns).
Proof. intros Hz Hn [|j]; simpl; auto. Qed.

(** The clauses of the interpretation. *)

Lemma D_bot x y ns : ~ Dsem Bot x y ns.
Proof. unfold Dsem. cbn [dia]. intro H. apply (not_holds (num 1) 0); [apply star_refl | exact H]. Qed.

Lemma D_eq s t x y ns : Ns ns ->
  (Dsem (Eq s t) x y ns <-> exists m, star (tsub ns (tr s)) (num m) /\ star (tsub ns (tr t)) (num m)).
Proof.
  intro Hn. unfold Dsem. cbn [dia]. rewrite tsub_eqT, !tsub_comp.
  change (fun i => tsub (dsub y x ns) (nvars i)) with ns.
  destruct (T_eval _ (typing_tr _ s Hn)) as [m Hm].
  destruct (T_eval _ (typing_tr _ t Hn)) as [k Hk].
  destruct (eqT_eval _ _ _ _ Hm Hk) as [d [Hd Ed]].
  unfold holds. split.
  - intro H. rewrite (star_num_unique _ _ _ Hd H) in Ed. destruct Ed as [E _].
    specialize (E eq_refl). subst. eauto.
  - intros [m' [H1 H2]]. rewrite (star_num_unique _ _ _ Hm H1), (star_num_unique _ _ _ Hk H2) in Ed.
    destruct Ed as [_ E]. rewrite (E eq_refl) in Hd. exact Hd.
Qed.

Lemma D_and A B x y ns : DT (And A B) x y ns ->
  (Dsem (And A B) x y ns <->
   Dsem A (pi1 (wty A) (wty B) x) (pi1 (cty A) (cty B) y) ns /\
   Dsem B (pi2 (wty A) (wty B) x) (pi2 (cty A) (cty B) y) ns).
Proof.
  intros [Hx [Hy Hn]]. unfold Dsem. cbn [dia]. rewrite tsub_addT, !tsub_dsub.
  apply holds_addT; apply dia_typing; repeat split; auto using typing_pi1, typing_pi2.
Qed.

Lemma D_or A B x y ns : DT (Or A B) x y ns ->
  (Dsem (Or A B) x y ns <->
   (holds (pi1 TN (TPr (wty A) (wty B)) x) /\
    Dsem A (pi1 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) x)) (pi1 (cty A) (cty B) y) ns) \/
   ((exists m, star (pi1 TN (TPr (wty A) (wty B)) x) (num (S m))) /\
    Dsem B (pi2 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) x)) (pi2 (cty A) (cty B) y) ns)).
Proof.
  intros [Hx [Hy Hn]]. unfold Dsem. cbn [dia]. rewrite tsub_cond, !tsub_dsub.
  apply holds_cond. apply typing_pi1. exact Hx.
Qed.

Lemma D_imp A B x y ns : DT (Imp A B) x y ns ->
  let a := pi1 (wty A) (cty B) y in
  let v := pi2 (wty A) (cty B) y in
  let f := pi1 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) x in
  let g := pi2 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) x in
  (Dsem (Imp A B) x y ns <-> (Dsem A a (app (cty B) (app (wty A) g a) v) ns -> Dsem B (app (wty A) f a) v ns)).
Proof.
  intros [Hx [Hy Hn]]. unfold Dsem. cbn [dia]. rewrite tsub_cond, !tsub_dsub.
  apply holds_imp. apply dia_typing. repeat split; auto.
  - apply typing_pi1. exact Hy.
  - repeat econstructor; eauto using typing_pi1, typing_pi2.
Qed.

Lemma D_all A x y ns :
  Dsem (All A) x y ns <->
  Dsem A (app TN x (pi1 TN (cty A) y)) (pi2 TN (cty A) y) (prepend [pi1 TN (cty A) y] ns).
Proof.
  unfold Dsem. cbn [dia]. rewrite tsub_dsub.
  rewrite (tsub_ext _ (dsub (pi2 TN (cty A) y) (app TN x (pi1 TN (cty A) y)) (prepend [pi1 TN (cty A) y] ns)));
    [reflexivity|]. intros [|[|[|j]]]; reflexivity.
Qed.

Lemma D_ex A x y ns :
  Dsem (Ex A) x y ns <-> Dsem A (pi2 TN (wty A) x) y (prepend [pi1 TN (wty A) x] ns).
Proof.
  unfold Dsem. cbn [dia]. rewrite tsub_dsub.
  rewrite (tsub_ext _ (dsub y (pi2 TN (wty A) x) (prepend [pi1 TN (wty A) x] ns)));
    [reflexivity|]. intros [|[|[|j]]]; reflexivity.
Qed.

(** Substituting in the formula is substituting in the number
    variables. *)
Lemma dia_subst A : forall σ y x ns,
  tsub (dsub y x ns) (dia (fsubst σ A)) = tsub (dsub y x (fun j => tsub ns (tr (σ j)))) (dia A).
Proof.
  induction A; intros σ y x ns; cbn [dia fsubst]; rewrite ?wty_subst, ?cty_subst.
  - rewrite !tsub_eqT, !tsub_comp, !tr_asubst, !tsub_comp. reflexivity.
  - reflexivity.
  - rewrite !tsub_addT, !tsub_dsub, IHA1, IHA2. reflexivity.
  - rewrite !tsub_cond, !tsub_dsub, IHA1, IHA2. reflexivity.
  - rewrite !tsub_cond, !tsub_dsub, IHA1, IHA2. reflexivity.
  - rewrite !tsub_dsub, IHA. apply tsub_ext. intros [|[|[|j]]]; auto. simpl.
    rewrite tr_asubst, tsub_comp. reflexivity.
  - rewrite !tsub_dsub, IHA. apply tsub_ext. intros [|[|[|j]]]; auto. simpl.
    rewrite tr_asubst, tsub_comp. reflexivity.
  - reflexivity.
Qed.

Lemma D_subst A σ x y ns :
  Dsem (fsubst σ A) x y ns <-> Dsem A x y (fun j => tsub ns (tr (σ j))).
Proof. unfold Dsem. rewrite dia_subst. reflexivity. Qed.

Lemma D_shift A x y ns : Dsem (fshift A) x y ns <-> Dsem A x y (fun j => ns (S j)).
Proof. apply D_subst. Qed.

Lemma D_sub1 A t x y ns : Dsem (sub1 A t) x y ns <-> Dsem A x y (prepend [tsub ns (tr t)] ns).
Proof. unfold sub1. rewrite D_subst. apply Dsem_ext. intros [|j]; reflexivity. Qed.

(** ** Realizers of derivations

    For a derivation of [Γ ⊢ A], a witness term [t] for [A], whose
    variables are the witnesses [x_i] of the hypotheses followed by the
    number variables, and for each hypothesis a counterexample term
    [s i], which may also use the counterexample [y] of [A] (variable
    [0]).  If the counterexamples [s i] do not refute the hypotheses,
    then [y] does not refute [t]. *)

Definition hctx (Γ:list form) : nat -> ty := prepend (map wty Γ) TN0.
Definition sctx (A:form) (Γ:list form) : nat -> ty := prepend (cty A :: map wty Γ) TN0.

Definition XT (Γ:list form) (xs:list term) : Prop := Forall2 (fun x B => typing [] x (wty B)) xs Γ.

Definition Hyps (Γ:list form) (xs:list term) (ys:nat -> term) (ns:nat -> term) : Prop :=
  forall i B, nth_error Γ i = Some B -> Dsem B (nth i xs Zc) (ys i) ns.

Definition Real (Γ:list form) (A:form) : Prop :=
  exists (t:term) (s:nat -> term),
    wt (hctx Γ) t (wty A) /\
    (forall i B, nth_error Γ i = Some B -> wt (sctx A Γ) (s i) (cty B)) /\
    forall xs y ns, XT Γ xs -> typing [] y (cty A) -> Ns ns ->
      Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (s i)) ns ->
      Dsem A (tsub (prepend xs ns) t) y ns.

Lemma XT_length Γ xs : XT Γ xs -> length xs = length Γ.
Proof. intro H. symmetry. apply Forall2_length in H. auto. Qed.

Lemma XT_nth Γ xs i B : XT Γ xs -> nth_error Γ i = Some B -> typing [] (nth i xs Zc) (wty B).
Proof.
  intro H. revert i. induction H as [|x C xs Γ Hx H IH]; intros [|i] Hi; simpl in *; try discriminate.
  - injection Hi as <-. exact Hx.
  - auto.
Qed.

Lemma XT_map Γ xs : XT Γ xs -> Forall2 (fun x T => typing [] x T) xs (map wty Γ).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma hctx_typed Γ xs ns : XT Γ xs -> Ns ns -> forall i, typing [] (prepend xs ns i) (hctx Γ i).
Proof. intros H Hn. apply prepend_typing; [apply XT_map, H | exact Hn]. Qed.

Lemma sctx_typed A Γ xs y ns : XT Γ xs -> typing [] y (cty A) -> Ns ns ->
  forall i, typing [] (prepend (y :: xs) ns i) (sctx A Γ i).
Proof. intros H Hy Hn [|i]; [exact Hy | exact (hctx_typed Γ xs ns H Hn i)]. Qed.

Lemma hctx_nth Γ i B : nth_error Γ i = Some B -> hctx Γ i = wty B.
Proof.
  unfold hctx. revert i. induction Γ as [|C Γ IH]; intros [|i] H; simpl in *; try discriminate.
  - congruence.
  - apply IH. exact H.
Qed.

Lemma hctx_ge Γ i : length Γ <= i -> hctx Γ i = TN.
Proof.
  intro H. unfold hctx. rewrite prepend_ge'; [reflexivity|]. rewrite length_map. exact H.
Qed.

Lemma inst_t Γ t T xs ns : wt (hctx Γ) t T -> XT Γ xs -> Ns ns -> typing [] (tsub (prepend xs ns) t) T.
Proof. intros H Hx Hn. eapply wt_typing; [exact H | apply hctx_typed; auto]. Qed.

Lemma inst_s A Γ s T xs y ns : wt (sctx A Γ) s T -> XT Γ xs -> typing [] y (cty A) -> Ns ns ->
  typing [] (tsub (prepend (y :: xs) ns) s) T.
Proof. intros H Hx Hy Hn. eapply wt_typing; [exact H | apply sctx_typed; auto]. Qed.

(** Moving terms between the two kinds of context. *)
Definition shs : nat -> term := fun i => var (S i).
Definition ysub (Y:term) : nat -> term := prepend [Y] shs.

Lemma inst_shs y xs ns M : tsub (prepend (y :: xs) ns) (tsub shs M) = tsub (prepend xs ns) M.
Proof. rewrite tsub_comp. reflexivity. Qed.

Lemma inst_ysub y xs ns Y M :
  tsub (prepend (y :: xs) ns) (tsub (ysub Y) M) = tsub (prepend (tsub (prepend (y :: xs) ns) Y :: xs) ns) M.
Proof. rewrite tsub_comp. apply tsub_ext. intros [|i]; reflexivity. Qed.

Lemma wt_shs A Γ M T : wt (hctx Γ) M T -> wt (sctx A Γ) (tsub shs M) T.
Proof. intro H. eapply wt_tsub; [exact H|]. intro i. apply wt_var'. reflexivity. Qed.

Lemma wt_ysub A A' Γ Y M T : wt (sctx A' Γ) M T -> wt (sctx A Γ) Y (cty A') -> wt (sctx A Γ) (tsub (ysub Y) M) T.
Proof. intros H HY. eapply wt_tsub; [exact H|]. intros [|i]; [exact HY | apply wt_var'; reflexivity]. Qed.

Lemma Hyps_star Γ xs ys ys' ns : (forall i, star (ys i) (ys' i)) -> (Hyps Γ xs ys ns <-> Hyps Γ xs ys' ns).
Proof.
  intro H. split; intros Hh i B HB; specialize (Hh i B HB).
  - exact (proj1 (Dsem_star B _ _ _ _ ns ns (star_refl _) (H i) (fun _ => star_refl _)) Hh).
  - exact (proj2 (Dsem_star B _ _ _ _ ns ns (star_refl _) (H i) (fun _ => star_refl _)) Hh).
Qed.

Lemma Hyps_ext Γ xs ys ys' ns : (forall i, ys i = ys' i) -> (Hyps Γ xs ys ns <-> Hyps Γ xs ys' ns).
Proof. intro H. apply Hyps_star. intro i. rewrite H. apply star_refl. Qed.

(** Default terms of every type. *)
Fixpoint zero (T:ty) : term :=
  match T with
  | TN => Zc
  | TAr A B => Kt B A (zero B)
  | TPr A B => tpair A B (zero A) (zero B)
  end.

Lemma wt_zero Γ T : wt Γ (zero T) T.
Proof. induction T; simpl; [constructor | apply wt_Kt; auto | apply wt_tpair; auto]. Qed.

Lemma tsub_zero ρ T : tsub ρ (zero T) = zero T.
Proof. induction T; simpl; auto. unfold Kt. simpl. rewrite IHT2. reflexivity.
  unfold tpair. simpl. rewrite IHT1, IHT2. reflexivity. Qed.

Lemma typing_zero T : typing [] (zero T) T.
Proof. rewrite <- (tsub_zero (fun _ => Zc) T). eapply wt_typing; [apply (wt_zero TN0)|]. intro. constructor. Qed.

Definition zeros (Γ:list form) : nat -> term := fun i => zero (cty (nth i Γ Bot)).

Lemma nth_error_nth' (Γ:list form) i B : nth_error Γ i = Some B -> nth i Γ Bot = B.
Proof. intro H. apply nth_error_nth. exact H. Qed.

Lemma wt_zeros A Γ i B : nth_error Γ i = Some B -> wt (sctx A Γ) (zeros Γ i) (cty B).
Proof. intro H. unfold zeros. rewrite (nth_error_nth' _ _ _ H). apply wt_zero. Qed.

(** Merging two lists of counterexamples: for each hypothesis, keep the
    first candidate if it refutes the hypothesis, and the second
    otherwise.  This is where the matrices must be decidable. *)
Definition merge1 (n:nat) (B:form) (i:nat) (a b:term) : term :=
  cond (cty B) (tsub (dsub a (var (S i)) (fun j => var (S n + j))) (dia B)) b a.

Definition mergeS (Γ:list form) (a b:nat -> term) : nat -> term :=
  fun i => merge1 (length Γ) (nth i Γ Bot) i (a i) (b i).

Lemma nth_error_lt {X} (l:list X) i a : nth_error l i = Some a -> i < length l.
Proof. intro H. apply nth_error_Some. congruence. Qed.

Lemma wt_mergeS A Γ a b i B : nth_error Γ i = Some B ->
  wt (sctx A Γ) (a i) (cty B) -> wt (sctx A Γ) (b i) (cty B) -> wt (sctx A Γ) (mergeS Γ a b i) (cty B).
Proof.
  intros HB Ha Hb. unfold mergeS, merge1. rewrite (nth_error_nth' _ _ _ HB).
  apply wt_cond; auto. eapply wt_tsub; [apply wt_dia|].
  intros [|[|j]]; auto.
  - apply wt_var'. change (hctx Γ i = wty B). apply hctx_nth. exact HB.
  - apply wt_var'. change (hctx Γ (length Γ + j) = TN). apply hctx_ge. lia.
Qed.

Lemma merge_sem Γ a b xs y ns : XT Γ xs -> Ns ns ->
  (forall i B, nth_error Γ i = Some B -> typing [] (tsub (prepend (y :: xs) ns) (a i)) (cty B)) ->
  Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (mergeS Γ a b i)) ns ->
  Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (a i)) ns /\
  Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (b i)) ns.
Proof.
  intros Hx Hn Ha H.
  pose proof (XT_length _ _ Hx) as Hlen.
  assert (Hboth : forall i B, nth_error Γ i = Some B ->
            Dsem B (nth i xs Zc) (tsub (prepend (y :: xs) ns) (a i)) ns /\ Dsem B (nth i xs Zc) (tsub (prepend (y :: xs) ns) (b i)) ns).
  { intros i B HB. specialize (H i B HB). cbv beta in H.
    unfold mergeS, merge1 in H. rewrite (nth_error_nth' _ _ _ HB) in H.
    assert (Ez : tsub (prepend (y :: xs) ns) (tsub (dsub (a i) (var (S i)) (fun j => var (S (length Γ) + j))) (dia B))
                 = tsub (dsub (tsub (prepend (y :: xs) ns) (a i)) (nth i xs Zc) ns) (dia B)).
    { rewrite tsub_dsub. apply tsub_ext. intros [|[|j]]; auto.
      - simpl. simpl. apply prepend_lt. rewrite Hlen. eapply nth_error_lt; eauto.
      - simpl. simpl. rewrite <- Hlen. apply prepend_ge. }
    rewrite tsub_cond, Ez in H.
    assert (Hz : typing [] (tsub (dsub (tsub (prepend (y :: xs) ns) (a i)) (nth i xs Zc) ns) (dia B)) TN).
    { apply dia_typing. repeat split; eauto using XT_nth. }
    destruct (holds_dec _ Hz) as [H0|[m Hm]].
    - split; [exact H0|].
      exact (proj1 (Dsem_star B _ _ _ _ ns ns (star_refl _) (cond_0 _ _ _ _ H0) (fun _ => star_refl _)) H).
    - exfalso. apply (not_holds _ _ Hm).
      exact (proj1 (Dsem_star B _ _ _ _ ns ns (star_refl _) (cond_S _ _ _ _ _ Hm) (fun _ => star_refl _)) H). }
  split; intros i B HB; apply Hboth; auto.
Qed.

Lemma Hyps_ext' Γ xs ys ys' ns : Hyps Γ xs ys ns -> (forall i, ys i = ys' i) -> Hyps Γ xs ys' ns.
Proof. intros H E. apply (Hyps_ext _ _ _ _ _ E). exact H. Qed.

Lemma Hyps_red Γ xs ys ys' ns : Hyps Γ xs ys' ns -> (forall i, star (ys i) (ys' i)) -> Hyps Γ xs ys ns.
Proof. intros H E. apply (Hyps_star _ _ _ _ _ E). exact H. Qed.

Lemma Dsem_red A x x' y y' ns : star x x' -> star y y' -> Dsem A x' y' ns -> Dsem A x y ns.
Proof. intros Hx Hy H. apply (Dsem_star A x x' y y' ns ns Hx Hy (fun _ => star_refl _)). exact H. Qed.

Lemma Dsem_fwd A x x' y y' ns : star x x' -> star y y' -> Dsem A x y ns -> Dsem A x' y' ns.
Proof. intros Hx Hy H. apply (Dsem_star A x x' y y' ns ns Hx Hy (fun _ => star_refl _)). exact H. Qed.

Lemma XT_cons Γ xs A x : typing [] x (wty A) -> XT Γ xs -> XT (A :: Γ) (x :: xs).
Proof. intros. constructor; auto. Qed.

(** ** Soundness, rule by rule *)

Lemma R_hyp Γ A : In A Γ -> Real Γ A.
Proof.
  intro H. apply In_nth_error in H as [p Hp].
  exists (var p), (fun i => if i =? p then var 0 else zeros Γ i).
  split; [|split].
  - apply wt_var'. apply hctx_nth. exact Hp.
  - intros i B HB. destruct (Nat.eqb_spec i p) as [->|].
    + rewrite Hp in HB. injection HB as <-. apply wt_var'. reflexivity.
    + apply wt_zeros. exact HB.
  - intros xs y ns Hx Hy Hn H. specialize (H p A Hp). cbv beta in H. rewrite Nat.eqb_refl in H.
    simpl. rewrite (prepend_lt _ _ _ Zc); [exact H|].
    rewrite (XT_length _ _ Hx). eapply nth_error_lt; eauto.
Qed.

Lemma R_botE Γ A : Real Γ Bot -> Real Γ A.
Proof.
  intros [t [s [Ht [Hs H]]]].
  exists (zero (wty A)), (fun i => tsub (ysub Zc) (s i)). split; [apply wt_zero|split].
  - intros i B HB. apply wt_ysub with Bot; [auto | constructor].
  - intros xs y ns Hx Hy Hn Hh. exfalso.
    apply (D_bot (tsub (prepend xs ns) t) Zc ns). apply H; auto; [constructor|].
    apply (Hyps_ext' _ _ _ _ _ Hh). intro i. rewrite inst_ysub. reflexivity.
Qed.

Lemma R_andI Γ A B : Real Γ A -> Real Γ B -> Real Γ (And A B).
Proof.
  intros [t1 [s1 [Ht1 [Hs1 H1]]]] [t2 [s2 [Ht2 [Hs2 H2]]]].
  pose (a := fun i => tsub (ysub (pi1 (cty A) (cty B) (var 0))) (s1 i)).
  pose (b := fun i => tsub (ysub (pi2 (cty A) (cty B) (var 0))) (s2 i)).
  assert (Ha : forall i C, nth_error Γ i = Some C -> wt (sctx (And A B) Γ) (a i) (cty C)).
  { intros i C HC. eapply wt_ysub; [eauto | wtac]. }
  assert (Hb : forall i C, nth_error Γ i = Some C -> wt (sctx (And A B) Γ) (b i) (cty C)).
  { intros i C HC. eapply wt_ysub; [eauto | wtac]. }
  exists (tpair (wty A) (wty B) t1 t2), (mergeS Γ a b). split; [|split].
  - apply wt_tpair; auto.
  - intros i C HC. apply wt_mergeS; auto.
  - intros xs y ns Hx Hy Hn Hh.
    destruct (merge_sem _ _ _ _ _ _ Hx Hn (fun i C HC => inst_s _ _ _ _ _ _ _ (Ha i C HC) Hx Hy Hn) Hh)
      as [Hha Hhb].
    assert (HtA := inst_t _ _ _ _ _ Ht1 Hx Hn). assert (HtB := inst_t _ _ _ _ _ Ht2 Hx Hn).
    apply D_and; [repeat split; auto; simpl; unfold tpair; repeat econstructor; eauto|]. split.
    + eapply Dsem_red; [apply star_pi1 | apply star_refl|].
      apply H1; auto; [apply typing_pi1; auto|].
      apply (Hyps_ext' _ _ _ _ _ Hha). intro i. unfold a. rewrite inst_ysub. reflexivity.
    + eapply Dsem_red; [apply star_pi2 | apply star_refl|].
      apply H2; auto; [apply typing_pi2; auto|].
      apply (Hyps_ext' _ _ _ _ _ Hhb). intro i. unfold b. rewrite inst_ysub. reflexivity.
Qed.

Lemma R_andE1 Γ A B : Real Γ (And A B) -> Real Γ A.
Proof.
  intros [t [s [Ht [Hs H]]]].
  exists (pi1 (wty A) (wty B) t), (fun i => tsub (ysub (tpair (cty A) (cty B) (var 0) (zero (cty B)))) (s i)).
  split; [apply wt_pi1; auto | split].
  - intros i C HC. eapply wt_ysub; [eauto|]. apply wt_tpair; [wtac | apply wt_zero].
  - intros xs y ns Hx Hy Hn Hh.
    assert (Hy' : typing [] (tpair (cty A) (cty B) y (zero (cty B))) (cty (And A B))).
    { unfold tpair. repeat econstructor; auto using typing_zero. }
    assert (HD := H xs _ ns Hx Hy' Hn).
    specialize (HD ltac:(apply (Hyps_ext' _ _ _ _ _ Hh); intro i; rewrite inst_ysub;
                         unfold tpair; simpl; rewrite tsub_zero; reflexivity)).
    apply D_and in HD; [|repeat split; auto; eapply inst_t; eauto].
    destruct HD as [HD _]. eapply Dsem_fwd; [apply star_refl | apply star_pi1 | exact HD].
Qed.

Lemma R_andE2 Γ A B : Real Γ (And A B) -> Real Γ B.
Proof.
  intros [t [s [Ht [Hs H]]]].
  exists (pi2 (wty A) (wty B) t), (fun i => tsub (ysub (tpair (cty A) (cty B) (zero (cty A)) (var 0))) (s i)).
  split; [apply wt_pi2; auto | split].
  - intros i C HC. eapply wt_ysub; [eauto|]. apply wt_tpair; [apply wt_zero | wtac].
  - intros xs y ns Hx Hy Hn Hh.
    assert (Hy' : typing [] (tpair (cty A) (cty B) (zero (cty A)) y) (cty (And A B))).
    { unfold tpair. repeat econstructor; auto using typing_zero. }
    assert (HD := H xs _ ns Hx Hy' Hn).
    specialize (HD ltac:(apply (Hyps_ext' _ _ _ _ _ Hh); intro i; rewrite inst_ysub;
                         unfold tpair; simpl; rewrite tsub_zero; reflexivity)).
    apply D_and in HD; [|repeat split; auto; eapply inst_t; eauto].
    destruct HD as [_ HD]. eapply Dsem_fwd; [apply star_refl | apply star_pi2 | exact HD].
Qed.

Lemma ins0 {X} (a:X) f i : ins 0 a f i = prepend [a] f i.
Proof. destruct i; reflexivity. Qed.

Lemma inst_ysub_eq y xs ns Y Y' M : tsub (prepend (y :: xs) ns) Y = Y' ->
  tsub (prepend (y :: xs) ns) (tsub (ysub Y) M) = tsub (prepend (Y' :: xs) ns) M.
Proof. intros <-. apply inst_ysub. Qed.

Lemma R_orI1 Γ A B : Real Γ A -> Real Γ (Or A B).
Proof.
  intros [t [s [Ht [Hs H]]]].
  exists (tpair TN (TPr (wty A) (wty B)) Zc (tpair (wty A) (wty B) t (zero (wty B)))),
         (fun i => tsub (ysub (pi1 (cty A) (cty B) (var 0))) (s i)).
  split; [|split].
  - apply wt_tpair; [constructor | apply wt_tpair; auto using wt_zero].
  - intros i C HC. eapply wt_ysub; [eauto | wtac].
  - intros xs y ns Hx Hy Hn Hh.
    assert (Ht' := inst_t _ _ _ _ _ Ht Hx Hn).
    apply D_or; [repeat split; auto; simpl; rewrite tsub_zero; unfold tpair; repeat econstructor;
                 auto using typing_zero|].
    left. split; [apply star_pi1|].
    eapply Dsem_red; [eapply star_pi1'; apply star_pi2 | apply star_refl|].
    apply H; auto; [apply typing_pi1; auto|].
    apply (Hyps_ext' _ _ _ _ _ Hh). intro i. apply inst_ysub_eq. reflexivity.
Qed.

Lemma R_orI2 Γ A B : Real Γ B -> Real Γ (Or A B).
Proof.
  intros [t [s [Ht [Hs H]]]].
  exists (tpair TN (TPr (wty A) (wty B)) (num 1) (tpair (wty A) (wty B) (zero (wty A)) t)),
         (fun i => tsub (ysub (pi2 (cty A) (cty B) (var 0))) (s i)).
  split; [|split].
  - apply wt_tpair; [repeat constructor | apply wt_tpair; auto using wt_zero].
  - intros i C HC. eapply wt_ysub; [eauto | wtac].
  - intros xs y ns Hx Hy Hn Hh.
    assert (Ht' := inst_t _ _ _ _ _ Ht Hx Hn).
    apply D_or; [repeat split; auto; simpl; rewrite tsub_zero; unfold tpair; repeat econstructor;
                 auto using typing_zero|].
    right. split; [exists 0; apply star_pi1|].
    eapply Dsem_red; [eapply star_pi2'; apply star_pi2 | apply star_refl|].
    apply H; auto; [apply typing_pi2; auto|].
    apply (Hyps_ext' _ _ _ _ _ Hh). intro i. apply inst_ysub_eq. reflexivity.
Qed.

Lemma R_impI Γ A B : Real (A :: Γ) B -> Real Γ (Imp A B).
Proof.
  intros [t [s [Ht [Hs H]]]].
  set (FA := TAr (wty A) (wty B)). set (GA := TAr (wty A) (TAr (cty B) (cty A))).
  set (f := lam_at (hctx (A :: Γ)) 0 t).
  set (g := lam_at (hctx (A :: Γ)) 0 (lam_at (sctx B (A :: Γ)) 0 (s 0))).
  set (ρ := dsub (pi2 (wty A) (cty B) (var 0)) (pi1 (wty A) (cty B) (var 0)) shs).
  assert (Hf : wt (hctx Γ) f FA).
  { apply (wt_ext (rem 0 (hctx (A :: Γ)))); [reflexivity|]. apply wt_lam_at. exact Ht. }
  assert (Hg : wt (hctx Γ) g GA).
  { apply (wt_ext (rem 0 (hctx (A :: Γ)))); [reflexivity|]. apply wt_lam_at.
    apply (wt_ext (rem 0 (sctx B (A :: Γ)))); [reflexivity|]. apply wt_lam_at. apply Hs. reflexivity. }
  exists (tpair FA GA f g), (fun i => tsub ρ (s (S i))). split; [|split].
  - apply wt_tpair; auto.
  - intros i C HC. eapply wt_tsub; [apply Hs; exact HC|].
    intros [|[|j]]; unfold ρ; simpl; [wtac | wtac | apply wt_var'; reflexivity].
  - intros xs y ns Hx Hy Hn Hh.
    assert (Ht' : typing [] (tsub (prepend xs ns) (tpair FA GA f g)) (wty (Imp A B))).
    { eapply inst_t; eauto. apply wt_tpair; auto. }
    apply D_imp; [repeat split; auto|]. cbv zeta. intro HA.
    set (a := pi1 (wty A) (cty B) y). set (v := pi2 (wty A) (cty B) y).
    assert (Ef : star (app (wty A) (pi1 FA GA (tsub (prepend xs ns) (tpair FA GA f g))) a)
                      (tsub (prepend (a :: xs) ns) t)).
    { eapply star_trans; [apply star_app_l, star_pi1|]. unfold f.
      eapply star_trans; [apply star_lam_at|]. rewrite (tsub_ext _ _ _ (ins0 _ _)). apply star_refl. }
    assert (Eg : star (app (cty B) (app (wty A) (pi2 FA GA (tsub (prepend xs ns) (tpair FA GA f g))) a) v)
                      (tsub (prepend (v :: a :: xs) ns) (s 0))).
    { eapply star_trans; [apply star_app_l, star_app_l, star_pi2|]. unfold g.
      eapply star_trans; [apply star_app_l, star_lam_at|].
      eapply star_trans; [apply star_lam_at|].
      rewrite (tsub_ext _ (prepend (v :: a :: xs) ns)); [apply star_refl|].
      intros [|[|k]]; reflexivity. }
    eapply Dsem_red; [exact Ef | apply star_refl|].
    apply H.
    + apply XT_cons; auto. apply typing_pi1. exact Hy.
    + apply typing_pi2. exact Hy.
    + exact Hn.
    + intros [|i] C HC.
      * injection HC as <-. eapply Dsem_fwd; [apply star_refl | exact Eg | exact HA].
      * specialize (Hh i C HC). cbv beta in Hh |- *.
        rewrite tsub_comp in Hh. erewrite tsub_ext; [exact Hh|].
        intros [|[|k]]; reflexivity.
Qed.

Lemma R_impE Γ A B : Real Γ (Imp A B) -> Real Γ A -> Real Γ B.
Proof.
  intros [t1 [s1 [Ht1 [Hs1 H1]]]] [t2 [s2 [Ht2 [Hs2 H2]]]].
  set (FA := TAr (wty A) (wty B)). set (GA := TAr (wty A) (TAr (cty B) (cty A))).
  pose (a := fun i => tsub (ysub (tpair (wty A) (cty B) (tsub shs t2) (var 0))) (s1 i)).
  pose (b := fun i => tsub (ysub (app (cty B) (app (wty A) (pi2 FA GA (tsub shs t1)) (tsub shs t2)) (var 0))) (s2 i)).
  assert (Ha : forall i C, nth_error Γ i = Some C -> wt (sctx B Γ) (a i) (cty C)).
  { intros i C HC. eapply wt_ysub; [eauto|]. apply wt_tpair; [apply wt_shs; auto | wtac]. }
  assert (Hb : forall i C, nth_error Γ i = Some C -> wt (sctx B Γ) (b i) (cty C)).
  { intros i C HC. eapply wt_ysub; [eauto|].
    econstructor; [econstructor; [apply wt_pi2; apply wt_shs; exact Ht1 | apply wt_shs; auto] | wtac]. }
  exists (app (wty A) (pi1 FA GA t1) t2), (mergeS Γ a b). split; [|split].
  - econstructor; [apply wt_pi1; exact Ht1 | auto].
  - intros i C HC. apply wt_mergeS; auto.
  - intros xs y ns Hx Hy Hn Hh.
    destruct (merge_sem _ _ _ _ _ _ Hx Hn (fun i C HC => inst_s _ _ _ _ _ _ _ (Ha i C HC) Hx Hy Hn) Hh)
      as [Hha Hhb].
    set (t1i := tsub (prepend xs ns) t1). set (t2i := tsub (prepend xs ns) t2).
    assert (Ht1i : typing [] t1i (wty (Imp A B))) by (eapply inst_t; eauto).
    assert (Ht2i : typing [] t2i (wty A)) by (eapply inst_t; eauto).
    assert (HI : Dsem (Imp A B) t1i (tpair (wty A) (cty B) t2i y) ns).
    { apply H1; auto; [unfold tpair; repeat econstructor; auto|].
      apply (Hyps_ext' _ _ _ _ _ Hha). intro i. apply inst_ysub_eq.
      unfold tpair. cbn [tsub]. rewrite inst_shs. reflexivity. }
    assert (HA : Dsem A t2i (app (cty B) (app (wty A) (pi2 FA GA t1i) t2i) y) ns).
    { apply H2; auto.
      - repeat econstructor; eauto.
      - apply (Hyps_ext' _ _ _ _ _ Hhb). intro i. apply inst_ysub_eq.
        unfold pi2. cbn [tsub]. rewrite !inst_shs. reflexivity. }
    assert (HDT : DT (Imp A B) t1i (tpair (wty A) (cty B) t2i y) ns).
    { repeat split; auto. simpl. unfold tpair. repeat econstructor; auto. }
    pose proof (proj1 (D_imp A B _ _ ns HDT) HI) as HI'. cbv zeta in HI'.
    eapply Dsem_fwd; [apply star_app_r, star_pi1 | apply star_pi2 |]. apply HI'.
    eapply Dsem_red; [apply star_pi1 | apply star_app; [apply star_app_r, star_pi1 | apply star_pi2] | exact HA].
Qed.

(** Context maps for a hypothesis added at the front. *)
Definition xsub (X:term) : nat -> term := prepend [var 0; tsub shs X] shs.

Lemma inst_xsub y xs ns X M :
  tsub (prepend (y :: xs) ns) (tsub (xsub X) M) = tsub (prepend (y :: tsub (prepend xs ns) X :: xs) ns) M.
Proof. rewrite tsub_comp. apply tsub_ext. intros [|[|k]]; simpl; auto. apply inst_shs. Qed.

Lemma wt_xsub C D Γ X M T : wt (sctx C (D :: Γ)) M T -> wt (hctx Γ) X (wty D) ->
  wt (sctx C Γ) (tsub (xsub X) M) T.
Proof.
  intros H HX. eapply wt_tsub; [exact H|].
  intros [|[|k]]; simpl; [apply wt_var'; reflexivity | apply wt_shs; exact HX | apply wt_var'; reflexivity].
Qed.

Lemma inst_hsub xs ns X M : tsub (prepend xs ns) (tsub (prepend [X] var) M) =
                            tsub (prepend (tsub (prepend xs ns) X :: xs) ns) M.
Proof. rewrite tsub_comp. apply tsub_ext. intros [|k]; reflexivity. Qed.

Lemma wt_hsub D Γ X M T : wt (hctx (D :: Γ)) M T -> wt (hctx Γ) X (wty D) ->
  wt (hctx Γ) (tsub (prepend [X] var) M) T.
Proof.
  intros H HX. eapply wt_tsub; [exact H|]. intros [|k]; simpl; [exact HX | apply wt_var'; reflexivity].
Qed.

Lemma Hyps_cons A Γ x xs ys ns : Dsem A x (ys 0) ns -> Hyps Γ xs (fun i => ys (S i)) ns ->
  Hyps (A :: Γ) (x :: xs) ys ns.
Proof. intros H0 H [|i] B HB; simpl in HB; [injection HB as <-; exact H0 | apply H; exact HB]. Qed.

Lemma R_orE Γ A B C : Real Γ (Or A B) -> Real (A :: Γ) C -> Real (B :: Γ) C -> Real Γ C.
Proof.
  intros [t0 [s0 [Ht0 [Hs0 H0]]]] [t1 [s1 [Ht1 [Hs1 H1]]]] [t2 [s2 [Ht2 [Hs2 H2]]]].
  set (WAB := TPr (wty A) (wty B)).
  set (xa := pi1 (wty A) (wty B) (pi2 TN WAB t0)). set (xb := pi2 (wty A) (wty B) (pi2 TN WAB t0)).
  set (zt := pi1 TN WAB t0).
  assert (Hxa : wt (hctx Γ) xa (wty A)) by (unfold xa; wtac; exact Ht0).
  assert (Hxb : wt (hctx Γ) xb (wty B)) by (unfold xb; wtac; exact Ht0).
  assert (Hzt : wt (hctx Γ) zt TN) by (unfold zt; wtac; exact Ht0).
  set (ymain := tpair (cty A) (cty B) (tsub (xsub xa) (s1 0)) (tsub (xsub xb) (s2 0))).
  pose (sm := fun i => tsub (ysub ymain) (s0 i)).
  pose (sc := fun i => cond (cty (nth i Γ Bot)) (tsub shs zt) (tsub (xsub xa) (s1 (S i))) (tsub (xsub xb) (s2 (S i)))).
  assert (Hym : wt (sctx C Γ) ymain (cty (Or A B))).
  { apply wt_tpair.
    - eapply wt_xsub; [apply (Hs1 0); reflexivity | exact Hxa].
    - eapply wt_xsub; [apply (Hs2 0); reflexivity | exact Hxb]. }
  assert (Hsm : forall i D, nth_error Γ i = Some D -> wt (sctx C Γ) (sm i) (cty D)).
  { intros i D HD. eapply wt_ysub; eauto. }
  assert (Hsc : forall i D, nth_error Γ i = Some D -> wt (sctx C Γ) (sc i) (cty D)).
  { intros i D HD. unfold sc. rewrite (nth_error_nth' _ _ _ HD).
    apply wt_cond; [apply wt_shs; auto | |].
    - eapply wt_xsub; [apply (Hs1 (S i)); exact HD | exact Hxa].
    - eapply wt_xsub; [apply (Hs2 (S i)); exact HD | exact Hxb]. }
  exists (cond (wty C) zt (tsub (prepend [xa] var) t1) (tsub (prepend [xb] var) t2)), (mergeS Γ sm sc).
  split; [|split].
  - apply wt_cond; auto; eapply wt_hsub; eauto.
  - intros i D HD. apply wt_mergeS; auto.
  - intros xs y ns Hx Hy Hn Hh.
    destruct (merge_sem _ _ _ _ _ _ Hx Hn (fun i C HC => inst_s _ _ _ _ _ _ _ (Hsm i C HC) Hx Hy Hn) Hh)
      as [Hhm Hhc].
    set (t0i := tsub (prepend xs ns) t0).
    assert (Ht0i : typing [] t0i (wty (Or A B))) by (eapply inst_t; eauto).
    assert (Hymi : typing [] (tsub (prepend (y :: xs) ns) ymain) (cty (Or A B))) by (eapply inst_s; eauto).
    assert (HO : Dsem (Or A B) t0i (tsub (prepend (y :: xs) ns) ymain) ns).
    { apply H0; auto. apply (Hyps_ext' _ _ _ _ _ Hhm). intro i. apply inst_ysub. }
    apply D_or in HO; [|repeat split; auto].
    assert (Hxai : typing [] (tsub (prepend xs ns) xa) (wty A)) by (eapply inst_t; eauto).
    assert (Hxbi : typing [] (tsub (prepend xs ns) xb) (wty B)) by (eapply inst_t; eauto).
    destruct HO as [[Hz HA]|[[m Hm] HB]].
    + eapply Dsem_red; [apply cond_0; exact Hz | apply star_refl|]. rewrite inst_hsub.
      apply H1; auto; [apply XT_cons; auto|]. apply Hyps_cons.
      * cbv beta. rewrite <- inst_xsub.
        eapply Dsem_fwd; [apply star_refl | apply star_pi1 | exact HA].
      * cbv beta. intros i D HD. specialize (Hhc i D HD). cbv beta in Hhc.
        unfold sc in Hhc. rewrite tsub_cond, inst_shs, inst_xsub in Hhc.
        eapply Dsem_fwd; [apply star_refl | apply cond_0; exact Hz | exact Hhc].
    + eapply Dsem_red; [eapply cond_S; exact Hm | apply star_refl|]. rewrite inst_hsub.
      apply H2; auto; [apply XT_cons; auto|]. apply Hyps_cons.
      * cbv beta. rewrite <- inst_xsub.
        eapply Dsem_fwd; [apply star_refl | apply star_pi2 | exact HB].
      * cbv beta. intros i D HD. specialize (Hhc i D HD). cbv beta in Hhc.
        unfold sc in Hhc. rewrite tsub_cond, inst_shs, !inst_xsub in Hhc.
        eapply Dsem_fwd; [apply star_refl | eapply cond_S; exact Hm | exact Hhc].
Qed.

(** Inserting a number variable after the hypotheses. *)
Lemma prepend_lt_indep {X} (xs:list X) f g k : k < length xs -> prepend xs f k = prepend xs g k.
Proof. revert k. induction xs; intros [|k] H; simpl in *; auto; try lia. apply IHxs. lia. Qed.

Lemma ins_prepend {X} (xs:list X) ns a k : ins (length xs) a (prepend xs ns) k = prepend xs (prepend [a] ns) k.
Proof.
  unfold ins. destruct (Nat.ltb_spec k (length xs)); [apply prepend_lt_indep; auto|].
  destruct (Nat.eqb_spec k (length xs)) as [->|].
  - pose proof (prepend_ge xs (prepend [a] ns) 0) as E. rewrite Nat.add_0_r in E. rewrite E. reflexivity.
  - rewrite !prepend_ge' by lia. destruct (k - length xs) eqn:E; [lia|]. simpl. f_equal. lia.
Qed.

Lemma tsub_ins ρ n a f k : tsub ρ (ins n a f k) = ins n (tsub ρ a) (fun k => tsub ρ (f k)) k.
Proof. unfold ins. destruct (k <? n); [|destruct (k =? n)]; reflexivity. Qed.

Lemma ins_ext {X} n (a:X) f g k : (forall k, f k = g k) -> ins n a f k = ins n a g k.
Proof. intro H. unfold ins. destruct (k <? n); [|destruct (k =? n)]; auto. Qed.

Lemma wt_ins Δ Γ n a f : (forall k, k < n -> wt Δ (f k) (Γ k)) -> wt Δ a (Γ n) ->
  (forall k, n < k -> wt Δ (f (pred k)) (Γ k)) -> forall k, wt Δ (ins n a f k) (Γ k).
Proof.
  intros H1 H2 H3 k. unfold ins. destruct (Nat.ltb_spec k n); auto.
  destruct (Nat.eqb_spec k n) as [->|]; auto. apply H3. lia.
Qed.

Lemma hctx_shift Γ : hctx (map fshift Γ) = hctx Γ.
Proof. unfold hctx. rewrite map_map. f_equal. apply map_ext. intro. apply wty_subst. Qed.

Lemma sctx_shift A Γ : sctx A (map fshift Γ) = sctx A Γ.
Proof.
  unfold sctx. replace (map wty (map fshift Γ)) with (map wty Γ); [reflexivity|].
  rewrite map_map. apply map_ext. intro. symmetry. apply wty_subst.
Qed.

Lemma XT_shift Γ xs : XT Γ xs -> XT (map fshift Γ) xs.
Proof. induction 1; simpl; constructor; auto. unfold fshift. rewrite wty_subst. auto. Qed.

Lemma XT_unshift Γ xs : XT (map fshift Γ) xs -> XT Γ xs.
Proof.
  revert xs. induction Γ as [|D Γ IH]; intros xs H; inversion H; subst; constructor.
  - unfold fshift in *. match goal with Hd : typing _ _ (wty (fsubst _ _)) |- _ => rewrite wty_subst in Hd; exact Hd end.
  - apply IH. assumption.
Qed.

Lemma nth_error_shift Γ i D : nth_error (map fshift Γ) i = Some D -> exists D', D = fshift D' /\ nth_error Γ i = Some D'.
Proof.
  intro H. rewrite nth_error_map in H. destruct (nth_error Γ i) as [D'|]; [|discriminate].
  injection H as <-. eauto.
Qed.

Lemma nth_error_shift' Γ i D : nth_error Γ i = Some D -> nth_error (map fshift Γ) i = Some (fshift D).
Proof. intro H. rewrite nth_error_map, H. reflexivity. Qed.

Lemma D_shift1 A x y z ns : Dsem (fshift A) x y (prepend [z] ns) <-> Dsem A x y ns.
Proof. rewrite D_shift. apply Dsem_ext. reflexivity. Qed.

Lemma Ns_star ns z z' : star z z' -> forall j, star (prepend [z] ns j) (prepend [z'] ns j).
Proof. intros H [|j]; simpl; auto using star_refl. Qed.

Lemma R_allI Γ A : Real (map fshift Γ) A -> Real Γ (All A).
Proof.
  intros [t [s [Ht [Hs H]]]]. rewrite hctx_shift in Ht.
  set (n := length Γ).
  set (ρ := prepend [pi2 TN (cty A) (var 0)] (ins n (pi1 TN (cty A) (var 0)) shs)).
  exists (lam_at (hctx Γ) n t), (fun i => tsub ρ (s i)). split; [|split].
  - apply (wt_ext (rem n (hctx Γ))).
    + intro k. unfold rem. destruct (Nat.ltb_spec k n); auto. rewrite !hctx_ge; auto; unfold n in *; lia.
    + replace (wty (All A)) with (TAr (hctx Γ n) (wty A)) by (rewrite hctx_ge; [reflexivity | unfold n; lia]).
      apply wt_lam_at. exact Ht.
  - intros i D HD. apply (wt_tsub (sctx A Γ)).
    { rewrite <- sctx_shift. replace (cty D) with (cty (fshift D)) by apply cty_subst.
      apply Hs, nth_error_shift', HD. }
    intros [|k]; simpl; [wtac|].
    revert k. apply wt_ins.
    + intros k Hk. apply wt_var'. reflexivity.
    + change (sctx A Γ (S n)) with (hctx Γ n). rewrite hctx_ge by (unfold n; lia). wtac.
    + intros k Hk. destruct k; [lia|]. apply wt_var'. simpl.
      change (hctx Γ k = hctx Γ (S k)). rewrite !hctx_ge; auto; unfold n in *; lia.
  - intros xs y ns Hx Hy Hn Hh.
    pose proof (XT_length _ _ Hx) as Hlen.
    apply D_all.
    eapply Dsem_red; [apply star_lam_at | apply star_refl|].
    rewrite (tsub_ext (ins n _ _) (prepend xs (prepend [pi1 TN (cty A) y] ns)))
      by (intro k; unfold n; rewrite <- Hlen; apply ins_prepend).
    assert (Hz : typing [] (pi1 TN (cty A) y) TN) by (apply typing_pi1; exact Hy).
    apply H; auto using XT_shift, Ns_cons; [apply typing_pi2; exact Hy|].
    intros i D HD. apply nth_error_shift in HD as [D' [-> HD]].
    apply D_shift1. specialize (Hh i D' HD). cbv beta in Hh |- *.
    rewrite tsub_comp in Hh. erewrite tsub_ext; [exact Hh|].
    intros [|k]; [reflexivity|].
    change (prepend xs (prepend [pi1 TN (cty A) y] ns) k =
            tsub (prepend (y :: xs) ns) (ins n (pi1 TN (cty A) (var 0)) shs k)).
    rewrite tsub_ins. unfold n. rewrite <- Hlen, <- ins_prepend. apply ins_ext. reflexivity.
Qed.

Lemma wt_tr_at Γ k t : (forall j, Γ (k + j) = TN) -> wt Γ (tsub (fun j => var (k + j)) (tr t)) TN.
Proof. intro H. eapply wt_tsub; [apply (wt_tr TN0); reflexivity|]. intro j. apply wt_var'. auto. Qed.

Lemma inst_tr_at xs ns t : tsub (prepend xs ns) (tsub (fun j => var (length xs + j)) (tr t)) = tsub ns (tr t).
Proof. rewrite tsub_comp. apply tsub_ext. intro j. apply prepend_ge. Qed.

Lemma R_allE Γ A r : Real Γ (All A) -> Real Γ (sub1 A r).
Proof.
  intros [t [s [Ht [Hs H]]]].
  set (n := length Γ).
  set (rt := tsub (fun j => var (n + j)) (tr r)).
  set (rts := tsub (fun j => var (S n + j)) (tr r)).
  assert (Hrt : wt (hctx Γ) rt TN) by (apply wt_tr_at; intro; apply hctx_ge; unfold n; lia).
  assert (Hrts : wt (sctx (sub1 A r) Γ) rts TN).
  { apply wt_tr_at. intro j. change (hctx Γ (n + j) = TN). apply hctx_ge. unfold n. lia. }
  assert (EW : wty (sub1 A r) = wty A) by apply wty_subst.
  assert (EC : cty (sub1 A r) = cty A) by apply cty_subst.
  exists (app TN t rt), (fun i => tsub (ysub (tpair TN (cty A) rts (var 0))) (s i)). split; [|split].
  - rewrite EW. econstructor; eauto.
  - intros i D HD. eapply wt_ysub; [eauto|]. apply wt_tpair; auto. apply wt_var'. simpl. auto.
  - intros xs y ns Hx Hy Hn Hh.
    pose proof (XT_length _ _ Hx) as Hlen.
    set (rr := tsub ns (tr r)).
    assert (Hrr : typing [] rr TN) by (apply typing_tr; auto).
    assert (Erts : tsub (prepend (y :: xs) ns) rts = rr).
    { unfold rts, n. rewrite <- Hlen. apply (inst_tr_at (y :: xs)). }
    assert (Ert : tsub (prepend xs ns) rt = rr) by (unfold rt, n; rewrite <- Hlen; apply inst_tr_at).
    assert (HA : Dsem (All A) (tsub (prepend xs ns) t) (tpair TN (cty A) rr y) ns).
    { apply H; auto.
      - rewrite EC in Hy. unfold tpair. repeat econstructor; auto.
      - apply (Hyps_ext' _ _ _ _ _ Hh). intro i. apply inst_ysub_eq.
        unfold tpair. cbn [tsub]. rewrite Erts. reflexivity. }
    apply D_all in HA. apply D_sub1. cbn [tsub]. rewrite Ert. fold rr.
    exact (proj1 (Dsem_star _ _ _ _ _ _ _ (star_app_r _ _ _ _ (star_pi1 _ _ _ _ _ _)) (star_pi2 _ _ _ _ _ _)
                    (Ns_star _ _ _ (star_pi1 _ _ _ _ _ _))) HA).
Qed.

Lemma R_exI Γ A r : Real Γ (sub1 A r) -> Real Γ (Ex A).
Proof.
  intros [t [s [Ht [Hs H]]]].
  set (n := length Γ).
  set (rt := tsub (fun j => var (n + j)) (tr r)).
  assert (Hrt : wt (hctx Γ) rt TN) by (apply wt_tr_at; intro; apply hctx_ge; unfold n; lia).
  assert (EW : wty (sub1 A r) = wty A) by apply wty_subst.
  assert (EC : cty (sub1 A r) = cty A) by apply cty_subst.
  assert (ES : sctx (sub1 A r) Γ = sctx (Ex A) Γ) by (unfold sctx; simpl; rewrite EC; reflexivity).
  exists (tpair TN (wty A) rt t), s. split; [|split].
  - rewrite EW in Ht. apply wt_tpair; auto.
  - intros i D HD. rewrite <- ES. auto.
  - intros xs y ns Hx Hy Hn Hh.
    pose proof (XT_length _ _ Hx) as Hlen.
    assert (Ert : tsub (prepend xs ns) rt = tsub ns (tr r)) by (unfold rt, n; rewrite <- Hlen; apply inst_tr_at).
    apply D_ex.
    assert (HA : Dsem (sub1 A r) (tsub (prepend xs ns) t) y ns).
    { apply H; auto. simpl in Hy. rewrite EC. exact Hy. }
    apply D_sub1 in HA.
    refine (proj2 (Dsem_star _ _ _ _ _ _ _ (star_pi2 _ _ _ _ _ _) (star_refl _) _) HA).
    intros [|j]; [|apply star_refl]. cbn [prepend]. unfold pi1, tpair. cbn [tsub].
    rewrite Ert. apply star_pi1.
Qed.

Lemma R_exE Γ A B : Real Γ (Ex A) -> Real (A :: map fshift Γ) (fshift B) -> Real Γ B.
Proof.
  intros [t0 [s0 [Ht0 [Hs0 H0]]]] [t1 [s1 [Ht1 [Hs1 H1]]]].
  set (n := length Γ).
  set (xa := pi2 TN (wty A) t0). set (zt := pi1 TN (wty A) t0).
  assert (Hxa : wt (hctx Γ) xa (wty A)) by (unfold xa; wtac; exact Ht0).
  assert (Hzt : wt (hctx Γ) zt TN) by (unfold zt; wtac; exact Ht0).
  set (σ := prepend [xa] (ins n zt var)).
  set (τ := prepend [var 0; tsub shs xa] (ins n (tsub shs zt) shs)).
  assert (Hτ : forall M T, wt (sctx (fshift B) (A :: map fshift Γ)) M T -> wt (sctx B Γ) (tsub τ M) T).
  { intros M T HM. eapply wt_tsub; [exact HM|]. intros [|[|k]].
    - apply wt_var'. change (cty B = cty (fshift B)). symmetry. apply cty_subst.
    - apply wt_shs. exact Hxa.
    - change (wt (sctx B Γ) (ins n (tsub shs zt) shs k) (hctx (map fshift Γ) k)). rewrite hctx_shift.
      revert k. apply wt_ins.
      + intros k _. apply wt_var'. reflexivity.
      + rewrite hctx_ge by (unfold n; lia). apply wt_shs. exact Hzt.
      + intros k Hk. destruct k; [lia|]. apply wt_var'. simpl.
        change (hctx Γ k = hctx Γ (S k)). rewrite !hctx_ge; auto; unfold n in *; lia. }
  pose (sm := fun i => tsub (ysub (tsub τ (s1 0))) (s0 i)).
  pose (ss := fun i => tsub τ (s1 (S i))).
  assert (Hsm : forall i D, nth_error Γ i = Some D -> wt (sctx B Γ) (sm i) (cty D)).
  { intros i D HD. eapply wt_ysub; [apply Hs0, HD|]. apply Hτ. exact (Hs1 0 A eq_refl). }
  assert (Hss : forall i D, nth_error Γ i = Some D -> wt (sctx B Γ) (ss i) (cty D)).
  { intros i D HD. apply Hτ. replace (cty D) with (cty (fshift D)) by apply cty_subst.
    apply (Hs1 (S i)). apply nth_error_shift', HD. }
  exists (tsub σ t1), (mergeS Γ sm ss). split; [|split].
  - eapply wt_tsub; [unfold fshift in Ht1; rewrite wty_subst in Ht1; exact Ht1|].
    intros [|k]; [exact Hxa|].
    change (wt (hctx Γ) (ins n zt var k) (hctx (map fshift Γ) k)). rewrite hctx_shift.
    revert k. apply wt_ins.
    + intros k _. apply wt_var'. reflexivity.
    + rewrite hctx_ge by (unfold n; lia). exact Hzt.
    + intros k Hk. apply wt_var'. rewrite !hctx_ge; auto; unfold n in *; lia.
  - intros i D HD. apply wt_mergeS; auto.
  - intros xs y ns Hx Hy Hn Hh.
    pose proof (XT_length _ _ Hx) as Hlen.
    destruct (merge_sem _ _ _ _ _ _ Hx Hn (fun i C HC => inst_s _ _ _ _ _ _ _ (Hsm i C HC) Hx Hy Hn) Hh)
      as [Hhm Hhs].
    set (t0i := tsub (prepend xs ns) t0).
    assert (Ht0i : typing [] t0i (wty (Ex A))) by (eapply inst_t; eauto).
    set (xai := pi2 TN (wty A) t0i). set (zti := pi1 TN (wty A) t0i).
    assert (Hxai : typing [] xai (wty A)) by (apply typing_pi2; exact Ht0i).
    assert (Hzti : typing [] zti TN) by (apply typing_pi1; exact Ht0i).
    assert (Eτ : forall M, tsub (prepend (y :: xs) ns) (tsub τ M) =
                           tsub (prepend (y :: xai :: xs) (prepend [zti] ns)) M).
    { intro M. rewrite tsub_comp. apply tsub_ext. intros [|[|k]]; [reflexivity | apply inst_shs |].
      change (tsub (prepend (y :: xs) ns) (ins n (tsub shs zt) shs k) = prepend xs (prepend [zti] ns) k).
      rewrite tsub_ins, inst_shs. unfold n. rewrite <- Hlen, <- ins_prepend. apply ins_ext. reflexivity. }
    assert (Eσ : tsub (prepend xs ns) (tsub σ t1) = tsub (prepend (xai :: xs) (prepend [zti] ns)) t1).
    { rewrite tsub_comp. apply tsub_ext. intros [|k]; [reflexivity|].
      change (tsub (prepend xs ns) (ins n zt var k) = prepend xs (prepend [zti] ns) k).
      rewrite tsub_ins. unfold n. rewrite <- Hlen, <- ins_prepend. apply ins_ext. reflexivity. }
    assert (Hyi : typing [] (tsub (prepend (y :: xs) ns) (tsub τ (s1 0))) (cty A)).
    { eapply inst_s; [apply Hτ; exact (Hs1 0 A eq_refl) | auto | auto | auto]. }
    assert (HE : Dsem (Ex A) t0i (tsub (prepend (y :: xs) ns) (tsub τ (s1 0))) ns).
    { apply H0; auto. apply (Hyps_ext' _ _ _ _ _ Hhm). intro i. apply inst_ysub. }
    apply D_ex in HE. rewrite Eτ in HE.
    rewrite Eσ. apply D_shift1 with (z := zti).
    apply H1; auto using Ns_cons.
    + apply XT_cons; auto using XT_shift.
    + unfold fshift. rewrite cty_subst. exact Hy.
    + apply Hyps_cons; [exact HE|].
      intros i D' HD'. apply nth_error_shift in HD' as [D [-> HD]].
      apply D_shift1. specialize (Hhs i D HD). cbv beta in Hhs. unfold ss in Hhs. rewrite Eτ in Hhs.
      exact Hhs.
Qed.

(** Axioms with trivial realizers. *)
Lemma R_axiom Γ A : (forall x y ns, DT A x y ns -> Dsem A x y ns) -> Real Γ A.
Proof.
  intro H. exists (zero (wty A)), (zeros Γ). split; [apply wt_zero | split; [intros; apply wt_zeros; auto|]].
  intros xs y ns Hx Hy Hn _. rewrite tsub_zero. apply H. repeat split; auto using typing_zero.
Qed.

Lemma tr_value ns t : Ns ns -> exists k, star (tsub ns (tr t)) (num k).
Proof. intro Hn. apply T_eval, typing_tr, Hn. Qed.

Lemma R_refl Γ t : Real Γ (Eq t t).
Proof.
  apply R_axiom. intros x y ns [_ [_ Hn]]. apply D_eq; auto.
  destruct (tr_value ns t Hn) as [k Hk]. eauto.
Qed.

Lemma R_plus0 Γ t : Real Γ (Eq (tplus t tz) t).
Proof.
  apply R_axiom. intros x y ns [_ [_ Hn]]. apply D_eq; auto.
  destruct (tr_value ns t Hn) as [k Hk]. exists k. split; auto.
  cbn [tr]. rewrite tsub_addT. eapply star_trans; [apply addT_eval; [exact Hk | apply (star_refl (num 0))]|].
  rewrite Nat.add_0_r. apply star_refl.
Qed.

Lemma R_plusS Γ s t : Real Γ (Eq (tplus s (ts t)) (ts (tplus s t))).
Proof.
  apply R_axiom. intros x y ns [_ [_ Hn]]. apply D_eq; auto.
  destruct (tr_value ns s Hn) as [a Ha]. destruct (tr_value ns t Hn) as [b Hb].
  exists (S (a + b)). cbn [tr]. rewrite !tsub_addT. split.
  - rewrite <- Nat.add_succ_r. apply addT_eval; auto. simpl. apply star_app_r. exact Hb.
  - simpl. apply star_app_r. apply addT_eval; auto.
Qed.

Lemma R_mult0 Γ t : Real Γ (Eq (tmult t tz) tz).
Proof.
  apply R_axiom. intros x y ns [_ [_ Hn]]. apply D_eq; auto.
  destruct (tr_value ns t Hn) as [k Hk]. exists 0. split; [|apply star_refl].
  cbn [tr]. rewrite tsub_mulT. eapply star_trans; [apply mulT_eval; [exact Hk | apply (star_refl (num 0))]|].
  rewrite Nat.mul_0_r. apply star_refl.
Qed.

Lemma R_multS Γ s t : Real Γ (Eq (tmult s (ts t)) (tplus (tmult s t) s)).
Proof.
  apply R_axiom. intros x y ns [_ [_ Hn]]. apply D_eq; auto.
  destruct (tr_value ns s Hn) as [a Ha]. destruct (tr_value ns t Hn) as [b Hb].
  exists (a * b + a). cbn [tr]. rewrite tsub_addT, !tsub_mulT. split.
  - rewrite <- Nat.mul_succ_r. apply mulT_eval; auto. simpl. apply star_app_r. exact Hb.
  - apply addT_eval; auto. apply mulT_eval; auto.
Qed.

Lemma R_succ_ne Γ t : Real Γ (Neg (Eq (ts t) tz)).
Proof.
  apply R_axiom. intros x y ns HT. unfold Neg. apply D_imp; auto. cbv zeta. intro HE.
  destruct HT as [_ [_ Hn]]. apply D_eq in HE; auto. destruct HE as [m [H1 H2]].
  change (star (num 0) (num m)) in H2. apply star_from_num in H2. apply num_inj in H2. subst m.
  destruct (tr_value ns t Hn) as [k Hk].
  assert (H3 : star (tsub ns (tr (ts t))) (num (S k))) by (simpl; apply star_app_r; exact Hk).
  pose proof (star_num_unique _ _ _ H1 H3). discriminate.
Qed.

Lemma R_succ_inj Γ s t : Real Γ (Eq (ts s) (ts t)) -> Real Γ (Eq s t).
Proof.
  intros [t0 [s0 [Ht [Hs H]]]]. exists t0, s0. split; [exact Ht | split; [exact Hs|]].
  intros xs y ns Hx Hy Hn Hh. specialize (H xs y ns Hx Hy Hn Hh).
  apply D_eq in H; auto. apply D_eq; auto. destruct H as [m [H1 H2]].
  destruct (tr_value ns s Hn) as [a Ha]. destruct (tr_value ns t Hn) as [b Hb].
  assert (Ea : star (tsub ns (tr (ts s))) (num (S a))) by (simpl; apply star_app_r; exact Ha).
  assert (Eb : star (tsub ns (tr (ts t))) (num (S b))) by (simpl; apply star_app_r; exact Hb).
  pose proof (star_num_unique _ _ _ Ea H1). pose proof (star_num_unique _ _ _ Eb H2).
  assert (a = b) by lia. subst. eauto.
Qed.

Lemma sctx_cty A A' Γ : cty A = cty A' -> sctx A Γ = sctx A' Γ.
Proof. intro E. unfold sctx. rewrite E. reflexivity. Qed.

Lemma R_leib Γ A a b : Real Γ (Eq a b) -> Real Γ (sub1 A a) -> Real Γ (sub1 A b).
Proof.
  intros [t1 [s1 [Ht1 [Hs1 H1]]]] [t2 [s2 [Ht2 [Hs2 H2]]]].
  assert (EW : wty (sub1 A a) = wty (sub1 A b)) by (unfold sub1; rewrite !wty_subst; reflexivity).
  assert (EC : cty (sub1 A a) = cty (sub1 A b)) by (unfold sub1; rewrite !cty_subst; reflexivity).
  pose (sa := fun i => tsub (ysub Zc) (s1 i)).
  assert (Hsa : forall i D, nth_error Γ i = Some D -> wt (sctx (sub1 A b) Γ) (sa i) (cty D)).
  { intros i D HD. eapply wt_ysub; [apply Hs1, HD | constructor]. }
  assert (Hs2' : forall i D, nth_error Γ i = Some D -> wt (sctx (sub1 A b) Γ) (s2 i) (cty D)).
  { intros i D HD. rewrite <- (sctx_cty _ _ _ EC). auto. }
  exists t2, (mergeS Γ sa s2). split; [rewrite <- EW; exact Ht2 | split].
  - intros i D HD. apply wt_mergeS; auto.
  - intros xs y ns Hx Hy Hn Hh.
    destruct (merge_sem _ _ _ _ _ _ Hx Hn (fun i C HC => inst_s _ _ _ _ _ _ _ (Hsa i C HC) Hx Hy Hn) Hh)
      as [Hha Hhb].
    assert (HE : Dsem (Eq a b) (tsub (prepend xs ns) t1) Zc ns).
    { apply H1; auto; [constructor|]. apply (Hyps_ext' _ _ _ _ _ Hha). intro i. apply inst_ysub. }
    apply D_eq in HE; auto. destruct HE as [m [Ham Hbm]].
    assert (HA : Dsem (sub1 A a) (tsub (prepend xs ns) t2) y ns) by (apply H2; auto; rewrite EC; auto).
    apply D_sub1 in HA. apply D_sub1.
    refine (proj2 (Dsem_star _ _ _ _ _ _ _ (star_refl _) (star_refl _) (Ns_star _ _ _ Hbm)) _).
    exact (proj1 (Dsem_star _ _ _ _ _ _ _ (star_refl _) (star_refl _) (Ns_star _ _ _ Ham)) HA).
Qed.

(** Induction: the witness of [∀x A] is defined by the recursor, at the
    type of the witnesses of [A]. *)
Lemma R_ind Γ A : Real [] (sub1 A tz) -> Real [A] (fsubst suc_sub A) -> Real Γ (All A).
Proof.
  intros [t0 [s0 [Ht0 [_ H0]]]] [t1 [s1 [Ht1 [Hs1 H1]]]].
  set (n := length Γ). set (WA := wty A).
  assert (EW0 : wty (sub1 A tz) = WA) by apply wty_subst.
  assert (EW1 : wty (fsubst suc_sub A) = WA) by apply wty_subst.
  assert (EC0 : cty (sub1 A tz) = cty A) by apply cty_subst.
  assert (EC1 : cty (fsubst suc_sub A) = cty A) by apply cty_subst.
  set (C2 := prepend [WA; TN] (hctx Γ)).
  set (base := tsub (fun j => var (S n + j)) t0).
  set (M := tsub (dsub (var 0) (var 1) (fun j => var (3 + n + j))) t1).
  set (stepF := lam_at (prepend [TN] (hctx Γ)) 0 (lam_at C2 0 M)).
  set (rec := app (TAr TN (TAr WA WA)) (app WA (app TN (Rc WA) (var n)) base) stepF).
  assert (Hbase : wt (hctx Γ) base WA).
  { eapply wt_tsub; [rewrite <- EW0; exact Ht0|]. intro j. apply wt_var'.
    rewrite hctx_ge by (unfold n; lia). reflexivity. }
  assert (HM : wt C2 M WA).
  { eapply wt_tsub; [rewrite <- EW1; exact Ht1|].
    intros [|[|j]]; apply wt_var'; try reflexivity.
    change (hctx Γ (S (n + j)) = TN). apply hctx_ge. unfold n. lia. }
  assert (Hstep : wt (hctx Γ) stepF (TAr TN (TAr WA WA))).
  { apply (wt_ext (rem 0 (prepend [TN] (hctx Γ)))); [reflexivity|].
    apply wt_lam_at. apply (wt_ext (rem 0 C2)); [reflexivity|]. apply wt_lam_at. exact HM. }
  assert (Hrec : wt (hctx Γ) rec WA).
  { unfold rec. econstructor; [econstructor; [econstructor; [constructor|] | exact Hbase] | exact Hstep].
    apply wt_var'. apply hctx_ge. unfold n. lia. }
  exists (lam_at (hctx Γ) n rec), (zeros Γ). split; [|split].
  - apply (wt_ext (rem n (hctx Γ))).
    + intro k. unfold rem. destruct (Nat.ltb_spec k n); auto. rewrite !hctx_ge; auto; unfold n in *; lia.
    + replace (wty (All A)) with (TAr (hctx Γ n) WA) by (rewrite hctx_ge; [reflexivity | unfold n; lia]).
      apply wt_lam_at. exact Hrec.
  - intros i D HD. apply wt_zeros. exact HD.
  - intros xs y ns Hx Hy Hn _.
    pose proof (XT_length _ _ Hx) as Hlen.
    set (z := pi1 TN (cty A) y).
    assert (Hz : typing [] z TN) by (apply typing_pi1; exact Hy).
    set (ρ' := prepend xs (prepend [z] ns)).
    assert (Hρ' : forall i, typing [] (ρ' i) (hctx Γ i)) by (apply hctx_typed; auto using Ns_cons).
    set (base' := tsub ρ' base). set (step' := tsub ρ' stepF).
    assert (Ebase : base' = tsub ns t0).
    { unfold base', base. rewrite tsub_comp. apply tsub_ext. intro j. unfold ρ'. cbn [tsub].
      rewrite prepend_ge' by (unfold n in *; lia).
      replace (S n + j - length xs) with (S j) by (unfold n in *; lia). reflexivity. }
    pose (Fm := fun m => app (TAr TN (TAr WA WA)) (app WA (app TN (Rc WA) (num m)) base') step').
    assert (HbaseT : typing [] base' WA) by (eapply wt_typing; eauto).
    assert (HstepT : typing [] step' (TAr TN (TAr WA WA))) by (eapply wt_typing; eauto).
    assert (HF : forall m, typing [] (Fm m) WA).
    { intro m. unfold Fm.
      econstructor; [econstructor; [econstructor; [constructor | apply typing_num] | exact HbaseT] | exact HstepT]. }
    assert (Hclaim : forall m y', typing [] y' (cty A) -> Dsem A (Fm m) y' (prepend [num m] ns)).
    { induction m as [|m IH]; intros y' Hy'.
      - eapply Dsem_red; [apply star_one, st_R0; reflexivity | apply star_refl|].
        rewrite Ebase.
        assert (H := H0 [] y' ns (Forall2_nil _) ltac:(rewrite EC0; exact Hy') Hn
                        ltac:(intros i D HD; destruct i; discriminate)).
        apply D_sub1 in H. rewrite (tsub_ext (prepend [] ns) ns) in H by reflexivity. exact H.
      - eapply Dsem_red; [apply star_one, st_RS; apply is_num_num | apply star_refl|].
        eapply Dsem_red; [| apply star_refl |].
        { eapply star_trans; [apply star_app_l; unfold step', stepF; apply star_lam_at|].
          apply star_lam_at. }
        assert (EM : tsub (ins 0 (Fm m) (ins 0 (num m) ρ')) M = tsub (prepend [Fm m] (prepend [num m] ns)) t1).
        { unfold M. rewrite tsub_comp. apply tsub_ext. intros [|[|j]]; try reflexivity.
          change (ρ' (S (n + j)) = ns j). unfold ρ'.
          rewrite prepend_ge' by (unfold n in *; lia).
          replace (S (n + j) - length xs) with (S j) by (unfold n in *; lia). reflexivity. }
        change (Dsem A (tsub (ins 0 (Fm m) (ins 0 (num m) ρ')) M) y' (prepend [num (S m)] ns)).
        rewrite EM.
        assert (HXT : XT [A] [Fm m]) by (constructor; [exact (HF m) | constructor]).
        assert (Hy'' : typing [] y' (cty (fsubst suc_sub A))) by (rewrite EC1; exact Hy').
        assert (Hn' : Ns (prepend [num m] ns)) by (apply Ns_cons; auto using typing_num).
        assert (HH : Hyps [A] [Fm m] (fun i => tsub (prepend [y'; Fm m] (prepend [num m] ns)) (s1 i))
                          (prepend [num m] ns)).
        { apply Hyps_cons; [|intros i D HD; destruct i; discriminate].
          apply IH. eapply inst_s; [exact (Hs1 0 A eq_refl) | exact HXT | exact Hy'' | exact Hn']. }
        assert (H := H1 [Fm m] y' (prepend [num m] ns) HXT Hy'' Hn' HH).
        apply D_subst in H.
        refine (proj1 (Dsem_ext _ _ _ _ _ _) H). intros [|j]; reflexivity. }
    apply D_all.
    destruct (T_eval _ Hz) as [k Hk].
    eapply Dsem_red; [apply star_lam_at | apply star_refl|].
    rewrite (tsub_ext (ins n z (prepend xs ns)) ρ') by (intro i; unfold n, ρ'; rewrite <- Hlen; apply ins_prepend).
    refine (proj2 (Dsem_star A _ (Fm k) _ _ _ _ _ (star_refl _) (Ns_star _ _ _ Hk))
                  (Hclaim k _ (typing_pi2 _ _ _ Hy))).
    unfold rec, Fm. cbn [tsub]. fold base' step'.
    apply star_app_l, star_app_l, star_app_r.
    unfold ρ'. unfold n. rewrite <- Hlen, <- (Nat.add_0_r (length xs)), prepend_ge. exact Hk.
Qed.

(** ** Consistency *)

Theorem HA_sound Γ A : HA Γ A -> Real Γ A.
Proof.
  induction 1.
  - apply R_hyp; auto.
  - apply R_botE; auto.
  - discriminate.
  - apply R_andI; auto.
  - eapply R_andE1; eauto.
  - eapply R_andE2; eauto.
  - apply R_orI1; auto.
  - apply R_orI2; auto.
  - eapply R_orE; eauto.
  - apply R_impI; auto.
  - eapply R_impE; eauto.
  - apply R_allI; auto.
  - apply R_allE; auto.
  - eapply R_exI; eauto.
  - eapply R_exE; eauto.
  - apply R_refl.
  - eapply R_leib; eauto.
  - apply R_succ_ne.
  - apply R_succ_inj; auto.
  - apply R_plus0.
  - apply R_plusS.
  - apply R_mult0.
  - apply R_multS.
  - apply R_ind; auto.
Qed.

(** A closed proof of [⊥] in Heyting arithmetic would give a closed
    term of T whose matrix [⊥_D] holds; but [⊥_D] is the numeral [1]. *)
Theorem HA_consistent : ~ HA [] Bot.
Proof.
  intro H. destruct (HA_sound _ _ H) as [t [s [Ht [_ Hr]]]].
  apply (D_bot (tsub (prepend [] (fun _ => Zc)) t) Zc (fun _ => Zc)).
  apply Hr; [constructor | constructor | intro; constructor | intros i B HB; destruct i; discriminate].
Qed.

(** Peano arithmetic is consistent: by the negative translation, a proof
    of [⊥] in PA gives one in HA. *)
Theorem PA_consistent : ~ PA [] Bot.
Proof. intro H. apply HA_consistent, PA_HA_consistency, H. Qed.
