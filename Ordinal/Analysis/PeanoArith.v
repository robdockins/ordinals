From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

(** * Peano and Heyting arithmetic, and the negative translation

    First-order arithmetic with [0], [S], [+] and [·], formulas built
    from equations and atoms [X t] with [⊥], [∧], [∨], [→], [∀] and [∃],
    and variables as de Bruijn indices.  [X] is a unary predicate
    variable with no axioms: the theory is [PA(X)], which proves its
    instances of the induction schema for formulas mentioning [X], and
    so can state transfinite induction [TI(≺, X)] as a single
    sentence.  The proof system is natural deduction with
    hypotheses in a list; Peano arithmetic adds double-negation
    elimination to Heyting arithmetic.  The Gödel–Gentzen negative
    translation embeds Peano arithmetic in Heyting arithmetic
    ([negative_translation]), so a proof of [⊥] in PA gives one in HA
    ([PA_HA_consistency]). *)

(** ** Syntax *)

Inductive aterm : Set :=
| tv : nat -> aterm
| tz : aterm
| ts : aterm -> aterm
| tplus : aterm -> aterm -> aterm
| tmult : aterm -> aterm -> aterm.

Inductive form : Set :=
| Eq : aterm -> aterm -> form
| Bot : form
| And : form -> form -> form
| Or : form -> form -> form
| Imp : form -> form -> form
| All : form -> form
| Ex : form -> form
| PX : aterm -> form.

Definition Neg (A:form) : form := Imp A Bot.

(** ** Substitution *)

Fixpoint asubst (σ:nat -> aterm) (t:aterm) : aterm :=
  match t with
  | tv i => σ i
  | tz => tz
  | ts t => ts (asubst σ t)
  | tplus s t => tplus (asubst σ s) (asubst σ t)
  | tmult s t => tmult (asubst σ s) (asubst σ t)
  end.

Definition shift_sub : nat -> aterm := fun i => tv (S i).

Definition up (σ:nat -> aterm) : nat -> aterm :=
  fun i => match i with O => tv 0 | S i => asubst shift_sub (σ i) end.

Fixpoint fsubst (σ:nat -> aterm) (A:form) : form :=
  match A with
  | Eq s t => Eq (asubst σ s) (asubst σ t)
  | Bot => Bot
  | And A B => And (fsubst σ A) (fsubst σ B)
  | Or A B => Or (fsubst σ A) (fsubst σ B)
  | Imp A B => Imp (fsubst σ A) (fsubst σ B)
  | All A => All (fsubst (up σ) A)
  | Ex A => Ex (fsubst (up σ) A)
  | PX t => PX (asubst σ t)
  end.

(** Shifting past a new variable, substituting for variable [0], and
    replacing variable [0] by its successor. *)
Definition fshift (A:form) : form := fsubst shift_sub A.

Definition inst1 (t:aterm) : nat -> aterm :=
  fun i => match i with O => t | S i => tv i end.

Definition sub1 (A:form) (t:aterm) : form := fsubst (inst1 t) A.

Definition suc_sub : nat -> aterm :=
  fun i => match i with O => ts (tv 0) | S i => tv (S i) end.

Lemma asubst_ext σ τ t : (forall i, σ i = τ i) -> asubst σ t = asubst τ t.
Proof. intro H. induction t; simpl; f_equal; auto. Qed.

Lemma up_ext σ τ : (forall i, σ i = τ i) -> forall i, up σ i = up τ i.
Proof. intros H [|i]; simpl; auto. rewrite H. reflexivity. Qed.

Lemma fsubst_ext A : forall σ τ, (forall i, σ i = τ i) -> fsubst σ A = fsubst τ A.
Proof.
  induction A; intros σ τ H; simpl; f_equal; auto using asubst_ext, up_ext.
Qed.

Lemma asubst_comp σ τ t : asubst σ (asubst τ t) = asubst (fun i => asubst σ (τ i)) t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma asubst_id t : asubst tv t = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma up_comp σ τ i : asubst (up σ) (up τ i) = up (fun j => asubst σ (τ j)) i.
Proof.
  destruct i; simpl; auto.
  rewrite !asubst_comp. apply asubst_ext. intro j. reflexivity.
Qed.

Lemma fsubst_comp A : forall σ τ, fsubst σ (fsubst τ A) = fsubst (fun i => asubst σ (τ i)) A.
Proof.
  induction A; intros σ τ; simpl; f_equal; auto using asubst_comp.
  - rewrite IHA. apply fsubst_ext. apply up_comp.
  - rewrite IHA. apply fsubst_ext. apply up_comp.
Qed.

Lemma fsubst_id A : forall σ, (forall i, σ i = tv i) -> fsubst σ A = A.
Proof.
  induction A; intros σ H; simpl; f_equal; auto.
  - rewrite (asubst_ext _ tv), asubst_id; auto.
  - rewrite (asubst_ext _ tv), asubst_id; auto.
  - apply IHA. intros [|i]; simpl; auto. rewrite H. reflexivity.
  - apply IHA. intros [|i]; simpl; auto. rewrite H. reflexivity.
  - rewrite (asubst_ext _ tv), asubst_id; auto.
Qed.

(** Instantiating a shifted quantifier body with the new variable gives
    back the body. *)
Lemma sub1_up_shift A : sub1 (fsubst (up shift_sub) A) (tv 0) = A.
Proof.
  unfold sub1. rewrite fsubst_comp. apply fsubst_id.
  intros [|i]; reflexivity.
Qed.

Lemma fshift_sub1 A t : fshift (sub1 A t) = sub1 (fsubst (up shift_sub) A) (asubst shift_sub t).
Proof.
  unfold fshift, sub1. rewrite !fsubst_comp. apply fsubst_ext.
  intros [|i]; reflexivity.
Qed.

(** ** Natural deduction

    [prov cl Γ A]: [A] is provable from the hypotheses [Γ], classically
    if [cl] is [true].  The induction rule has its premises in fixed
    contexts; with the other rules it gives the induction axiom
    ([induction_axiom]). *)

Inductive prov (cl:bool) : list form -> form -> Prop :=
| p_hyp Γ A : In A Γ -> prov cl Γ A
| p_botE Γ A : prov cl Γ Bot -> prov cl Γ A
| p_dne Γ A : cl = true -> prov cl Γ (Neg (Neg A)) -> prov cl Γ A
| p_andI Γ A B : prov cl Γ A -> prov cl Γ B -> prov cl Γ (And A B)
| p_andE1 Γ A B : prov cl Γ (And A B) -> prov cl Γ A
| p_andE2 Γ A B : prov cl Γ (And A B) -> prov cl Γ B
| p_orI1 Γ A B : prov cl Γ A -> prov cl Γ (Or A B)
| p_orI2 Γ A B : prov cl Γ B -> prov cl Γ (Or A B)
| p_orE Γ A B C : prov cl Γ (Or A B) -> prov cl (A :: Γ) C -> prov cl (B :: Γ) C -> prov cl Γ C
| p_impI Γ A B : prov cl (A :: Γ) B -> prov cl Γ (Imp A B)
| p_impE Γ A B : prov cl Γ (Imp A B) -> prov cl Γ A -> prov cl Γ B
| p_allI Γ A : prov cl (map fshift Γ) A -> prov cl Γ (All A)
| p_allE Γ A t : prov cl Γ (All A) -> prov cl Γ (sub1 A t)
| p_exI Γ A t : prov cl Γ (sub1 A t) -> prov cl Γ (Ex A)
| p_exE Γ A B : prov cl Γ (Ex A) -> prov cl (A :: map fshift Γ) (fshift B) -> prov cl Γ B
| p_refl Γ t : prov cl Γ (Eq t t)
| p_leib Γ A s t : prov cl Γ (Eq s t) -> prov cl Γ (sub1 A s) -> prov cl Γ (sub1 A t)
| p_succ_ne Γ t : prov cl Γ (Neg (Eq (ts t) tz))
| p_succ_inj Γ s t : prov cl Γ (Eq (ts s) (ts t)) -> prov cl Γ (Eq s t)
| p_plus0 Γ t : prov cl Γ (Eq (tplus t tz) t)
| p_plusS Γ s t : prov cl Γ (Eq (tplus s (ts t)) (ts (tplus s t)))
| p_mult0 Γ t : prov cl Γ (Eq (tmult t tz) tz)
| p_multS Γ s t : prov cl Γ (Eq (tmult s (ts t)) (tplus (tmult s t) s))
| p_ind Γ A : prov cl [] (sub1 A tz) -> prov cl [A] (fsubst suc_sub A) -> prov cl Γ (All A).

Abbreviation PA := (prov true).
Abbreviation HA := (prov false).

Lemma prov_weaken cl Γ A : prov cl Γ A -> forall Γ', incl Γ Γ' -> prov cl Γ' A.
Proof.
  induction 1; intros Γ' Hi.
  - apply p_hyp. auto.
  - apply p_botE. auto.
  - apply p_dne; auto.
  - apply p_andI; auto.
  - eapply p_andE1; eauto.
  - eapply p_andE2; eauto.
  - apply p_orI1; auto.
  - apply p_orI2; auto.
  - apply p_orE with A B; auto using incl_cons, in_eq, incl_tl.
  - apply p_impI. auto using incl_cons, in_eq, incl_tl.
  - eapply p_impE; eauto.
  - apply p_allI. auto using incl_map.
  - apply p_allE. auto.
  - eapply p_exI. eauto.
  - apply p_exE with A; auto. apply IHprov2. apply incl_cons; [apply in_eq|].
    apply incl_tl, incl_map, Hi.
  - apply p_refl.
  - eapply p_leib; eauto.
  - apply p_succ_ne.
  - apply p_succ_inj. auto.
  - apply p_plus0.
  - apply p_plusS.
  - apply p_mult0.
  - apply p_multS.
  - apply p_ind; auto.
Qed.

Lemma hyp0 cl Γ A : prov cl (A :: Γ) A.
Proof. apply p_hyp, in_eq. Qed.

Lemma hyp1 cl Γ A B : prov cl (B :: A :: Γ) A.
Proof. apply p_hyp. right. apply in_eq. Qed.

Lemma hyp2 cl Γ A B C : prov cl (C :: B :: A :: Γ) A.
Proof. apply p_hyp. right. right. apply in_eq. Qed.

Lemma weak1 cl Γ A B : prov cl Γ A -> prov cl (B :: Γ) A.
Proof. intro H. eapply prov_weaken; eauto using incl_tl, incl_refl. Qed.

Lemma weak2 cl Γ A B C : prov cl Γ A -> prov cl (C :: B :: Γ) A.
Proof. intro H. eapply prov_weaken; eauto using incl_tl, incl_refl. Qed.

Lemma weak3 cl Γ A B C D : prov cl Γ A -> prov cl (D :: C :: B :: Γ) A.
Proof. intro H. eapply prov_weaken; eauto using incl_tl, incl_refl. Qed.

(** Derivations are closed under substitution. *)
Lemma up_shift σ i : asubst (up σ) (shift_sub i) = asubst shift_sub (σ i).
Proof. reflexivity. Qed.

Lemma fsubst_shift_comm σ A : fsubst (up σ) (fshift A) = fshift (fsubst σ A).
Proof. unfold fshift. rewrite !fsubst_comp. apply fsubst_ext. intro i. reflexivity. Qed.

Lemma fsubst_sub1 σ A t : fsubst σ (sub1 A t) = sub1 (fsubst (up σ) A) (asubst σ t).
Proof.
  unfold sub1. rewrite !fsubst_comp. apply fsubst_ext.
  intros [|i]; simpl; auto. rewrite asubst_comp. rewrite asubst_ext with (τ := tv), asubst_id; auto.
Qed.

Lemma fsubst_suc σ A : fsubst (up σ) (fsubst suc_sub A) = fsubst suc_sub (fsubst (up σ) A).
Proof.
  rewrite !fsubst_comp. apply fsubst_ext.
  intros [|i]; simpl; auto. rewrite !asubst_comp. apply asubst_ext. intros j. reflexivity.
Qed.

Lemma prov_subst cl Γ A : prov cl Γ A -> forall σ, prov cl (map (fsubst σ) Γ) (fsubst σ A).
Proof.
  induction 1; intro σ; simpl in *.
  - apply p_hyp, in_map. auto.
  - apply p_botE. auto.
  - apply p_dne; auto.
  - apply p_andI; auto.
  - eapply p_andE1; eauto.
  - eapply p_andE2; eauto.
  - apply p_orI1; auto.
  - apply p_orI2; auto.
  - eapply p_orE; [apply IHprov1 | apply IHprov2 | apply IHprov3].
  - apply p_impI. auto.
  - eapply p_impE; eauto.
  - apply p_allI. specialize (IHprov (up σ)).
    rewrite map_map in *. erewrite map_ext; [exact IHprov|]. intro. symmetry. apply fsubst_shift_comm.
  - rewrite fsubst_sub1. apply p_allE. auto.
  - eapply p_exI. rewrite <- fsubst_sub1. auto.
  - eapply p_exE; [apply IHprov1|]. specialize (IHprov2 (up σ)). simpl in IHprov2.
    rewrite fsubst_shift_comm in IHprov2. rewrite map_map in *.
    erewrite map_ext in IHprov2; [exact IHprov2|]. intro. simpl. apply fsubst_shift_comm.
  - apply p_refl.
  - rewrite fsubst_sub1. eapply p_leib; [apply IHprov1|]. rewrite <- fsubst_sub1. auto.
  - apply p_succ_ne.
  - apply p_succ_inj. auto.
  - apply p_plus0.
  - apply p_plusS.
  - apply p_mult0.
  - apply p_multS.
  - apply p_ind.
    + specialize (IHprov1 σ). rewrite fsubst_sub1 in IHprov1. exact IHprov1.
    + specialize (IHprov2 (up σ)). simpl in IHprov2. rewrite fsubst_suc in IHprov2. exact IHprov2.
Qed.

(** ** The induction axiom *)

Theorem induction_axiom cl Γ A :
  prov cl Γ (Imp (sub1 A tz) (Imp (All (Imp A (fsubst suc_sub A))) (All A))).
Proof.
  (* Induction on [B := A(0) → ∀x (A x → A (S x)) → A], with the first
     two shifted past the induction variable. *)
  pose (Hz := All (Imp A (fsubst suc_sub A))).
  pose (B := Imp (fshift (sub1 A tz)) (Imp (fshift Hz) A)).
  assert (E1 : forall σ, (forall i, σ (S i) = tv (S i)) -> fsubst σ (fshift (sub1 A tz)) = fshift (sub1 A tz)).
  { intros σ Hσ. unfold fshift. rewrite fsubst_comp. apply fsubst_ext. intro i. simpl. apply Hσ. }
  assert (E2 : forall σ, (forall i, σ (S i) = tv (S i)) -> fsubst σ (fshift Hz) = fshift Hz).
  { intros σ Hσ. unfold fshift. rewrite fsubst_comp. apply fsubst_ext. intro i. simpl. apply Hσ. }
  assert (HB : prov cl [] (All B)).
  { apply p_ind.
    - unfold sub1 at 1. unfold B. cbn [fsubst].
      assert (E3 : forall X, fsubst (inst1 tz) (fshift X) = X).
      { intro X. unfold fshift. rewrite fsubst_comp. apply fsubst_id. intros [|i]; reflexivity. }
      rewrite !E3. apply p_impI, p_impI. change (fsubst (inst1 tz) A) with (sub1 A tz). apply hyp1.
    - unfold B. cbn [fsubst]. rewrite E1, E2 by reflexivity.
      apply p_impI, p_impI.
      assert (HA0 : prov cl [fshift Hz; fshift (sub1 A tz); B] A).
      { eapply p_impE; [eapply p_impE; [apply hyp2 | apply hyp1] | apply hyp0]. }
      assert (Hstep : prov cl [fshift Hz; fshift (sub1 A tz); B]
                        (sub1 (fsubst (up shift_sub) (Imp A (fsubst suc_sub A))) (tv 0))).
      { apply p_allE. apply hyp0. }
      rewrite sub1_up_shift in Hstep.
      eapply p_impE; [exact Hstep | exact HA0]. }
  apply p_impI, p_impI, p_allI.
  assert (Hi : prov cl (map fshift (Hz :: sub1 A tz :: Γ)) (sub1 (fsubst (up shift_sub) B) (tv 0))).
  { apply p_allE. eapply prov_weaken; [apply (prov_subst _ _ _ HB shift_sub) | intros ? []]. }
  rewrite sub1_up_shift in Hi. unfold B in Hi.
  eapply p_impE; [eapply p_impE; [exact Hi|] |].
  - apply p_hyp. right. left. reflexivity.
  - apply p_hyp. left. reflexivity.
Qed.

(** ** The Gödel–Gentzen negative translation *)

Fixpoint gg (A:form) : form :=
  match A with
  | Eq s t => Neg (Neg (Eq s t))
  | Bot => Bot
  | And A B => And (gg A) (gg B)
  | Or A B => Neg (And (Neg (gg A)) (Neg (gg B)))
  | Imp A B => Imp (gg A) (gg B)
  | All A => All (gg A)
  | Ex A => Neg (All (Neg (gg A)))
  | PX t => Neg (Neg (PX t))
  end.

Lemma gg_subst A : forall σ, gg (fsubst σ A) = fsubst σ (gg A).
Proof. induction A; intro σ; simpl; unfold Neg; f_equal; rewrite ?IHA, ?IHA1, ?IHA2; reflexivity. Qed.

Lemma gg_shift Γ : map gg (map fshift Γ) = map fshift (map gg Γ).
Proof. rewrite !map_map. apply map_ext. intro. apply gg_subst. Qed.

Lemma dni Γ A : HA Γ A -> HA Γ (Neg (Neg A)).
Proof. intro H. apply p_impI. eapply p_impE; [apply hyp0 | apply weak1, H]. Qed.

Lemma tneg Γ A : HA Γ (Imp (Neg (Neg (Neg A))) (Neg A)).
Proof.
  apply p_impI, p_impI. eapply p_impE; [apply hyp1|].
  apply p_impI. eapply p_impE; [apply hyp0 | apply hyp1].
Qed.

(** Translated formulas are stable under double negation. *)
Theorem gg_stable A : forall Γ, HA Γ (Imp (Neg (Neg (gg A))) (gg A)).
Proof.
  induction A; intro Γ; simpl; try apply tneg.
  - apply p_impI. eapply p_impE; [apply hyp0 | apply p_impI, hyp0].
  - apply p_impI. apply p_andI.
    + eapply p_impE; [apply IHA1|]. apply p_impI. eapply p_impE; [apply hyp1|].
      apply p_impI. eapply p_impE; [apply hyp1 | eapply p_andE1, hyp0].
    + eapply p_impE; [apply IHA2|]. apply p_impI. eapply p_impE; [apply hyp1|].
      apply p_impI. eapply p_impE; [apply hyp1 | eapply p_andE2, hyp0].
  - apply p_impI, p_impI. eapply p_impE; [apply IHA2|].
    apply p_impI. eapply p_impE; [apply hyp2|].
    apply p_impI. eapply p_impE; [apply hyp1|]. eapply p_impE; [apply hyp0 | apply hyp2].
  - apply p_impI, p_allI.
    eapply p_impE; [apply IHA|].
    apply p_impI. eapply p_impE; [apply hyp1|].
    apply p_impI. eapply p_impE; [apply hyp1|].
    match goal with |- prov _ ?Δ _ =>
      assert (Hx : HA Δ (sub1 (fsubst (up shift_sub) (gg A)) (tv 0))) by (apply p_allE, hyp0) end.
    rewrite sub1_up_shift in Hx. exact Hx.
Qed.

Lemma gg_dne Γ A : HA Γ (Neg (Neg (gg A))) -> HA Γ (gg A).
Proof. intro H. eapply p_impE; [apply gg_stable | exact H]. Qed.

Theorem negative_translation Γ A : PA Γ A -> HA (map gg Γ) (gg A).
Proof.
  induction 1; simpl in *.
  - apply p_hyp, in_map. auto.
  - apply p_botE. auto.
  - apply gg_dne. auto.
  - apply p_andI; auto.
  - eapply p_andE1; eauto.
  - eapply p_andE2; eauto.
  - apply p_impI. eapply p_impE; [eapply p_andE1, hyp0 | apply weak1; auto].
  - apply p_impI. eapply p_impE; [eapply p_andE2, hyp0 | apply weak1; auto].
  - apply gg_dne. apply p_impI. eapply p_impE; [apply weak1, IHprov1|].
    apply p_andI.
    + apply p_impI. eapply p_impE; [apply hyp1|].
      eapply prov_weaken; [exact IHprov2|]. intros D [<-|HD]; [left; auto | right; right; auto].
    + apply p_impI. eapply p_impE; [apply hyp1|].
      eapply prov_weaken; [exact IHprov3|]. intros D [<-|HD]; [left; auto | right; right; auto].
  - apply p_impI. auto.
  - eapply p_impE; eauto.
  - apply p_allI. rewrite <- gg_shift. auto.
  - unfold sub1. rewrite gg_subst. apply p_allE. auto.
  - apply p_impI. eapply p_impE; [|apply weak1; unfold sub1 in IHprov; rewrite gg_subst in IHprov; exact IHprov].
    change (HA (All (Neg (gg A)) :: map gg Γ) (sub1 (Neg (gg A)) t)). apply p_allE, hyp0.
  - apply gg_dne. apply p_impI. eapply p_impE; [apply weak1, IHprov1|].
    apply p_allI. simpl. apply p_impI.
    eapply p_impE; [apply hyp1|].
    rewrite gg_shift in IHprov2. unfold fshift in IHprov2 at 2. rewrite gg_subst in IHprov2.
    eapply prov_weaken; [exact IHprov2|]. intros D [<-|HD]; [left; auto | right; right; auto].
  - apply dni, p_refl.
  - unfold sub1 in *. rewrite gg_subst in IHprov2.
    apply gg_dne. rewrite gg_subst. apply p_impI.
    eapply p_impE; [apply weak1, IHprov1|]. apply p_impI.
    eapply p_impE; [apply hyp1|].
    change (fsubst (inst1 t) (gg A)) with (sub1 (gg A) t).
    apply p_leib with s; [apply hyp0 | apply weak2, IHprov2].
  - apply p_impI. eapply p_impE; [apply hyp0 | apply p_succ_ne].
  - apply p_impI. eapply p_impE; [apply weak1, IHprov|].
    apply p_impI. eapply p_impE; [apply hyp1 | apply p_succ_inj, hyp0].
  - apply dni, p_plus0.
  - apply dni, p_plusS.
  - apply dni, p_mult0.
  - apply dni, p_multS.
  - apply p_ind.
    + unfold sub1 in *. rewrite <- gg_subst. auto.
    + rewrite <- gg_subst. auto.
Qed.

Theorem PA_HA_consistency : PA [] Bot -> HA [] Bot.
Proof. intro H. apply (negative_translation _ _ H). Qed.
