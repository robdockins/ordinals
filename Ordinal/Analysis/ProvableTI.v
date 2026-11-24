From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Cantor.
From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import WellFounded.
From Ordinal Require Import Notation.VNotation.
From Ordinal Require Import Analysis.PeanoArith.
From Ordinal Require Import Analysis.Hardy.
From Ordinal Require Import Analysis.OmegaLogic.
From Ordinal Require Import Analysis.Embedding.

Local Open Scope nat_scope.

(** * Peano arithmetic proves transfinite induction only below ε₀

    Let [≺] be given by a bounded formula [R], with [y ≺ x] when [R]
    holds of [y] (variable [0]) and [x] (variable [1]).  Transfinite
    induction along [≺] is the sentence [TI(R)] of [PA(X)]:
    [Prog(X) → ∀x X(x)], where [Prog(X)] is [∀x (∀y (y ≺ x → X y) → X x)].

    If PA proves [TI(R)], then [≺] has height below ε₀ ([PA_TI_bound]):
    for some [L < ε₀], every [x] is [below L].  The proof is the
    _boundedness_ argument of Gentzen and Schütte: embed the proof in the
    ω-logic, eliminate the cuts down to bounded formulas
    ([od_elim_all]), and show by induction on a derivation of height [α]
    of a sequent [¬Prog(X), Δ] that [Δ] holds when [X] is read as "below
    level [γ + ω^α]", where [γ] bounds the negated [X]-atoms
    ([od_TI_bound]).

    A classical proof of [TI(R)] carries only "not not" information about
    well-foundedness, so the conclusion is stated classically: [below L x]
    says that each predecessor of [x] is not not below some predecessor
    of [L].  This is the faithful constructive reading of "PA proves [≺]
    well-founded"; it excludes infinite descending sequences
    ([PA_TI_no_descent]).  Only the classical corollary [PA_TI_wf_EM],
    which gives well-foundedness with order type below ε₀, assumes the
    excluded middle, as an explicit hypothesis. *)

(** ** Transfinite induction as a sentence *)

Definition ProgB (R:form) : form := Imp (All (Imp R (PX (tv 0)))) (PX (tv 0)).
Definition Prog (R:form) : form := All (ProgB R).
Definition TI (R:form) : form := Imp (Prog R) (All (PX (tv 0))).

(** [prec R y x]: [y ≺ x]; the other free variables of [R] are [0]. *)
Definition prec (R:form) (y x:nat) : Prop := sat (scons y (scons x ρ0)) R.

(** ** Height below an ordinal, classically *)

Section Below.
  Variable P : nat -> nat -> Prop.

  (** [below L x]: every predecessor of [x] is (classically) below some
      predecessor of [L]. *)
  Fixpoint below (L:Ord) (x:nat) : Prop :=
    match L with
    | ord A f => forall y, P y x -> ~ ~ exists a:A, below (f a) y
    end.

  Lemma below_stable L x : ~ ~ below L x -> below L x.
  Proof. destruct L as [A f]. simpl. intros H y Hy Hn. apply H. intro H'. exact (H' y Hy Hn). Qed.

  Lemma below_mono : forall L L' x, (L ≤ L')%ord -> below L x -> below L' x.
  Proof.
    induction L as [A f IH]. intros [B g] x Hle H y Hy Hn.
    apply (H y Hy). intros [a Ha].
    assert (Hlt : (f a < ord B g)%ord) by exact (Hle a).
    rewrite ord_lt_unfold in Hlt. destruct Hlt as [b Hb].
    apply Hn. exists b. exact (IH a (g b) y Hb Ha).
  Qed.

  Lemma below_succ L x : (forall y, P y x -> below L y) -> below (succOrd L) x.
  Proof. intros H y Hy Hn. apply Hn. exists tt. apply H. exact Hy. Qed.

  (** No infinite descending sequence starts below an ordinal. *)
  Theorem below_no_descent : forall L f, below L (f 0) -> (forall i, P (f (S i)) (f i)) -> False.
  Proof.
    induction L as [A g IH]. intros f H Hd.
    apply (H (f 1) (Hd 0)). intros [a Ha].
    apply (IH a (fun i => f (S i))); [exact Ha | intro i; apply Hd].
  Qed.

  (** With the excluded middle, [below] is the usual rank bound. *)
  Lemma below_Acc_EM (EM:excluded_middle) : forall L x, below L x -> Acc P x.
  Proof.
    induction L as [A f IH]. intros x H. constructor. intros y Hy.
    destruct (EM (exists a:A, below (f a) y)) as [[a Ha]|Hn]; [exact (IH a y Ha)|].
    exfalso. exact (H y Hy Hn).
  Qed.

  Lemma below_wf_ord_EM (EM:excluded_middle) :
    forall L x (Hx:Acc P x), below L x -> (mk_wf_ord nat P x Hx ≤ L)%ord.
  Proof.
    induction L as [A f IH]. intros x [Hx] H. simpl.
    rewrite ord_le_unfold. intros [y Hy]. simpl.
    rewrite ord_lt_unfold.
    destruct (EM (exists a:A, below (f a) y)) as [[a Ha]|Hn]; [|exfalso; exact (H y Hy Hn)].
    exists a. apply IH. exact Ha.
  Qed.
End Below.

Lemma below_ext (P P':nat -> nat -> Prop) : (forall y x, P' y x -> P y x) ->
  forall L x, below P L x -> below P' L x.
Proof.
  intro HP. induction L as [A f IH]. intros x H y Hy Hn.
  apply (H y (HP y x Hy)). intros [a Ha]. apply Hn. exists a. apply IH. exact Ha.
Qed.

(** ** A negative semantics for formulas with [X]

    Disjunction and existence are read classically, so every formula is
    stable when [X] is. *)

Fixpoint nsat (X:nat -> Prop) (ρ:nat -> nat) (A:form) : Prop :=
  match A with
  | Eq s t => teval ρ s = teval ρ t
  | Bot => False
  | And A B => nsat X ρ A /\ nsat X ρ B
  | Or A B => ~ (~ nsat X ρ A /\ ~ nsat X ρ B)
  | Imp A B => nsat X ρ A -> nsat X ρ B
  | All A => forall x, nsat X (scons x ρ) A
  | Ex A => ~ forall x, ~ nsat X (scons x ρ) A
  | PX t => X (teval ρ t)
  end.

Lemma nsat_ext X A : forall ρ ρ', (forall i, ρ i = ρ' i) -> (nsat X ρ A <-> nsat X ρ' A).
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u]; intros ρ ρ' H; simpl.
  - rewrite (teval_ext ρ ρ' s H), (teval_ext ρ ρ' t H). reflexivity.
  - reflexivity.
  - rewrite (IHA ρ ρ' H), (IHB ρ ρ' H). reflexivity.
  - rewrite (IHA ρ ρ' H), (IHB ρ ρ' H). reflexivity.
  - rewrite (IHA ρ ρ' H), (IHB ρ ρ' H). reflexivity.
  - split; intros Hx x; specialize (Hx x); revert Hx; apply IHA; intros [|i]; simpl; auto.
  - split; intros Hx Hy; apply Hx; intros x Hx'; apply (Hy x); revert Hx'; apply IHA;
      intros [|i]; simpl; auto.
  - rewrite (teval_ext ρ ρ' u H). reflexivity.
Qed.

Lemma nsat_fsubst X A : forall ρ σ, nsat X ρ (fsubst σ A) <-> nsat X (fun i => teval ρ (σ i)) A.
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u]; intros ρ σ; simpl.
  - rewrite !teval_asubst. reflexivity.
  - reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - split; intros Hx x; specialize (Hx x); revert Hx; rewrite IHA; apply nsat_ext;
      intros [|i]; simpl; [reflexivity | first [apply teval_shift | symmetry; apply teval_shift]
                          |reflexivity | first [apply teval_shift | symmetry; apply teval_shift]].
  - split; intros Hx Hy; apply Hx; intros x Hx'; apply (Hy x); revert Hx'; rewrite IHA; apply nsat_ext;
      intros [|i]; simpl; [reflexivity | first [apply teval_shift | symmetry; apply teval_shift]
                          |reflexivity | first [apply teval_shift | symmetry; apply teval_shift]].
  - rewrite teval_asubst. reflexivity.
Qed.

Lemma nsat_sub1_num X ρ A i : nsat X ρ (sub1 A (num i)) <-> nsat X (scons i ρ) A.
Proof.
  unfold sub1. rewrite nsat_fsubst. apply nsat_ext. intros [|j]; simpl; [apply teval_num | reflexivity].
Qed.

Lemma nsat_stable X (HX : forall n, ~ ~ X n -> X n) A : forall ρ, ~ ~ nsat X ρ A -> nsat X ρ A.
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u]; intros ρ H; simpl in *.
  - destruct (Nat.eq_dec (teval ρ s) (teval ρ t)) as [E|E]; [exact E | exfalso; apply H; exact E].
  - apply H. intro Hf. exact Hf.
  - split; [apply IHA | apply IHB]; intro Hn; apply H; intros [H1 H2]; auto.
  - intro Hn. apply H. intro H'. apply H'. exact Hn.
  - intro Ha. apply IHB. intro Hn. apply H. intro H'. apply Hn. apply H'. exact Ha.
  - intro x. apply IHA. intro Hn. apply H. intro H'. apply Hn. apply H'.
  - intro Hn. apply H. intro H'. apply H'. exact Hn.
  - apply HX. exact H.
Qed.

Lemma sat_dec_D A ρ : isD A = true -> sat ρ A \/ ~ sat ρ A.
Proof.
  intro H. destruct (deval ρ A) eqn:E; [left; apply deval_sat | right; apply deval_false]; assumption.
Qed.

(** On bounded formulas the negative semantics is the usual one. *)
Lemma nsat_DP X A : DP A -> forall ρ, nsat X ρ A <-> sat ρ A.
Proof.
  induction 1 as [s t| |A B HA IHA HB IHB|A B HA IHA HB IHB|A B HA IHA HB IHB|v B Hv0 Hv1 HB IHB|u v Hu Hv];
    intro ρ; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHA, IHB.
    destruct (sat_dec_D A ρ (DP_isD _ HA)), (sat_dec_D B ρ (DP_isD _ HB)); tauto.
  - rewrite IHA, IHB. reflexivity.
  - assert (HG : isD (Ex (Eq (tplus (tv 1) (tv 0)) v)) = true) by (simpl; rewrite Hv0; reflexivity).
    split.
    + intros H x [d Hd]. apply IHB. apply H. intro Hn. exact (Hn d Hd).
    + intros H x Hx. apply IHB. apply H.
      destruct (sat_dec_D _ (scons x ρ) HG) as [Hs|Hs]; [exact Hs|].
      exfalso. apply Hx. intros d Hd. apply Hs. exists d. exact Hd.
  - assert (HG : isD (Ex (Eq (tplus u (tv 0)) v)) = true) by (simpl; rewrite Hu, Hv; reflexivity).
    split.
    + intro H. destruct (sat_dec_D _ ρ HG) as [Hs|Hs]; [exact Hs|].
      exfalso. apply H. intros d Hd. apply Hs. exists d. exact Hd.
    + intros [d Hd] Hn. exact (Hn d Hd).
Qed.

Lemma nsat_D X A ρ : isD A = true -> (nsat X ρ A <-> sat ρ A).
Proof. intro H. apply nsat_DP. apply isD_DP. exact H. Qed.

(** *** Polarity of [X] *)

Fixpoint xpol (p:bool) (A:form) : bool :=
  match A with
  | Eq _ _ | Bot => true
  | And A B | Or A B => xpol p A && xpol p B
  | Imp A B => xpol (negb p) A && xpol p B
  | All A | Ex A => xpol p A
  | PX _ => p
  end.

Lemma xpol_fsubst A : forall p σ, xpol p (fsubst σ A) = xpol p A.
Proof. induction A; intros p σ; simpl; rewrite ?IHA, ?IHA1, ?IHA2; reflexivity. Qed.

Lemma xpol_DP A : DP A -> forall p, xpol p A = true.
Proof. induction 1; intro p; simpl; rewrite ?IHDP, ?IHDP1, ?IHDP2; reflexivity. Qed.

Lemma xpol_D p A : isD A = true -> xpol p A = true.
Proof. intro H. apply xpol_DP. apply isD_DP. exact H. Qed.

(** Formulas in which [X] is positive are monotone in [X]. *)
Lemma nsat_mono X Y (HXY : forall n, X n -> Y n) A : forall p ρ, xpol p A = true ->
  (p = true -> nsat X ρ A -> nsat Y ρ A) /\ (p = false -> nsat Y ρ A -> nsat X ρ A).
Proof.
  induction A as [s t| |A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA|A IHA|u]; intros p ρ Hp;
    simpl in Hp |- *.
  - split; auto.
  - split; auto.
  - apply andb_prop in Hp as [H1 H2].
    destruct (IHA p ρ H1), (IHB p ρ H2). tauto.
  - apply andb_prop in Hp as [H1 H2].
    destruct (IHA p ρ H1), (IHB p ρ H2). tauto.
  - apply andb_prop in Hp as [H1 H2]. destruct p.
    + destruct (IHA false ρ H1) as [_ A2]. destruct (IHB true ρ H2) as [B1 _].
      split; [|discriminate]. intros _ H Ha. apply B1; auto.
    + destruct (IHA true ρ H1) as [A1 _]. destruct (IHB false ρ H2) as [_ B2].
      split; [discriminate|]. intros _ H Ha. apply B2; auto.
  - split; intros Hpp H x; [apply (proj1 (IHA p (scons x ρ) Hp)) | apply (proj2 (IHA p (scons x ρ) Hp))];
      auto.
  - split; intros Hpp H Hn; apply H; intros x Hx; apply (Hn x);
      [apply (proj1 (IHA p (scons x ρ) Hp)) | apply (proj2 (IHA p (scons x ρ) Hp))]; auto.
  - subst p. split; [intros _; apply HXY | discriminate].
Qed.

(** *** Signed formulas *)

Definition spos (s:sform) : Prop := xpol (fst s) (snd s) = true.

Definition ssem (X:nat -> Prop) (s:sform) : Prop :=
  if fst s then nsat X ρ0 (snd s) else ~ nsat X ρ0 (snd s).

Lemma ssem_mono X Y s : (forall n, X n -> Y n) -> spos s -> ssem X s -> ssem Y s.
Proof.
  destruct s as [[|] A]; unfold spos, ssem; simpl; intros HXY Hp H.
  - exact (proj1 (nsat_mono X Y HXY A true ρ0 Hp) eq_refl H).
  - intro HY. apply H. exact (proj2 (nsat_mono X Y HXY A false ρ0 Hp) eq_refl HY).
Qed.

Lemma ssem_stable X s : (forall n, ~ ~ X n -> X n) -> ~ ~ ssem X s -> ssem X s.
Proof.
  destruct s as [[|] A]; unfold ssem; simpl; intros HX H.
  - apply nsat_stable; assumption.
  - intro Ha. apply H. intro Hn. exact (Hn Ha).
Qed.

Lemma ssem_dax X s : dax s -> ssem X s.
Proof.
  destruct s as [[|] A]; unfold dax, ssem; simpl; intros [HD Hv].
  - apply (nsat_D X A ρ0 HD). apply deval_sat; assumption.
  - rewrite (nsat_D X A ρ0 HD). apply deval_false; assumption.
Qed.

Lemma ssem_dfalse X s : dfalse s -> ~ ssem X s.
Proof.
  intro H. apply (proj1 (dfalse_sneg s)) in H. apply (ssem_dax X) in H.
  destruct s as [[|] A]; unfold ssem in *; simpl in *; tauto.
Qed.

Lemma spos_D s : isD (snd s) = true -> spos s.
Proof. intro H. unfold spos. apply xpol_D. exact H. Qed.

Lemma ssem_conj X s s1 s2 : kindof s = KConj s1 s2 -> ssem X s1 -> ssem X s2 -> ssem X s.
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intro H; try discriminate;
    injection H as <- <-; unfold ssem; simpl; tauto.
Qed.

Lemma ssem_disj X s s1 s2 s' : kindof s = KDisj s1 s2 -> (s' = s1 \/ s' = s2) -> ssem X s' -> ssem X s.
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intro H; try discriminate;
    injection H as <- <-; intros [->| ->]; unfold ssem; simpl; tauto.
Qed.

Lemma ssem_univ X s b A : kindof s = KUniv b A -> (forall i, ssem X (inst b A i)) -> ssem X s.
Proof.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intro H; try discriminate;
    injection H as <- <-; unfold ssem, inst; simpl; intro Hi.
  - intro x. apply nsat_sub1_num. apply Hi.
  - intro H. apply H. intros x Hx. apply (Hi x). apply nsat_sub1_num. exact Hx.
Qed.

Lemma ssem_exis X s b A m : kindof s = KExis b A -> ssem X (inst b A m) -> ssem X s.
Proof.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intro H; try discriminate;
    injection H as <- <-; unfold ssem, inst; simpl; intro Hi.
  - intro H. apply (H m). apply nsat_sub1_num. exact Hi.
  - intro H. apply Hi. apply nsat_sub1_num. apply H.
Qed.

Lemma spos_conj s s1 s2 : kindof s = KConj s1 s2 -> spos s -> spos s1 /\ spos s2.
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intro H; try discriminate;
    injection H as <- <-; unfold spos; simpl; apply andb_prop.
Qed.

Lemma spos_disj s s1 s2 s' : kindof s = KDisj s1 s2 -> (s' = s1 \/ s' = s2) -> spos s -> spos s'.
Proof.
  destruct s as [[|] [| |A B|A B|A B|A|A|u]]; simpl; intro H; try discriminate;
    injection H as <- <-; intros [->| ->]; unfold spos; simpl; intro Hp;
    apply andb_prop in Hp; tauto.
Qed.

Lemma spos_inst s b A i : (kindof s = KUniv b A \/ kindof s = KExis b A) -> spos s -> spos (inst b A i).
Proof.
  destruct s as [[|] [| |A' B|A' B|A' B|A'|A'|u]]; simpl; intros [H|H]; try discriminate;
    injection H as <- <-; unfold spos, inst, sub1; simpl; rewrite xpol_fsubst; auto.
Qed.

Lemma not_spos_PX u : ~ spos (false, PX u).
Proof. unfold spos. simpl. discriminate. Qed.

Lemma D_not_PX (x:sform) b u : isD (snd x) = true -> x <> (b, PX u).
Proof. intros H E. subst x. discriminate. Qed.

(** ** The bounds *)

Definition Bd (γ:Ord) (a:VForm) : Ord := (γ + expOrd ω (sz a))%ord.

Lemma Bd_ge γ a : (γ ≤ Bd γ a)%ord.
Proof. apply addOrd_le1. Qed.

Lemma Bd_le γ a b : (a ⊴ b) -> (Bd γ a ≤ Bd γ b)%ord.
Proof. intro H. apply addOrd_monotone; [apply ord_le_refl | apply expOrd_monotone; exact H]. Qed.

Lemma olt_lt n b a : olt n b a -> (b ◃ a).
Proof.
  intros [a1 [HP Hr]]. apply ord_le_lt_trans with (sz a1); [apply reach_le with n; exact Hr | apply Pn_lt with n; exact HP].
Qed.

(** Restarting at the successor of [Bd γ β] costs another [ω^β], which
    still fits below [ω^α]. *)
Lemma Bd_step γ a b : (a ◃ b) -> (Bd (succOrd (Bd γ a)) a ≤ Bd γ b)%ord.
Proof.
  intro Hab. unfold Bd.
  set (e := expOrd ω (sz a)).
  rewrite <- addOrd_succ. rewrite <- addOrd_assoc.
  apply addOrd_monotone; [apply ord_le_refl|].
  apply ord_le_trans with (e * ω)%ord.
  - apply ord_le_trans with (e * natOrdSize 3)%ord.
    + simpl. rewrite !mulOrd_succ. rewrite mulOrd_zero_r, addOrd_zero_l.
      apply addOrd_monotone; [|apply ord_le_refl].
      apply succ_least. rewrite <- (addOrd_zero_r e) at 1.
      apply addOrd_increasing. apply expOrd_nonzero.
    + apply mulOrd_monotone2. apply ord_lt_le. apply (index_lt ω 3%nat).
  - unfold e. rewrite <- expOrd_succ; [|apply omega_gt0].
    apply expOrd_monotone. apply succ_least. exact Hab.
Qed.

(** ** The boundedness lemma *)

Section Bounding.
  Variable Q : form.
  Hypothesis HQ : isD Q = true.

  Definition B (L:Ord) : nat -> Prop := below (prec Q) L.

  Definition special (s:sform) : Prop := s = (false, Prog Q) \/ exists a, s = inst false (ProgB Q) a.

  (** Each formula of the sequent has [X] positive, or is a negated
      [X]-atom, or comes from [¬Prog(X)]. *)
  Definition cls (s:sform) : Prop := spos s \/ special s \/ exists u, s = (false, PX u).

  Definition Qinst (a:nat) : form := fsubst (up (inst1 (num a))) Q.

  Lemma special_kind s : special s ->
    kindof s = KExis false (ProgB Q) \/
    exists a, kindof s = KConj (true, All (Imp (Qinst a) (PX (tv 0)))) (false, PX (num a)).
  Proof. intros [->|[a ->]]; [left; reflexivity | right; exists a; reflexivity]. Qed.

  Lemma special_not_pos s : special s -> ~ spos s.
  Proof.
    intros [->|[a ->]]; unfold spos; simpl; rewrite andb_false_r; discriminate.
  Qed.

  Lemma comp_sem L a :
    nsat (B L) ρ0 (All (Imp (Qinst a) (PX (tv 0)))) -> forall y, prec Q y a -> B L y.
  Proof.
    intros H y Hy. apply (H y). apply nsat_D; [unfold Qinst; rewrite isD_fsubst_eq; exact HQ|].
    unfold Qinst. apply sat_fsubst. unfold prec in Hy. revert Hy. apply sat_ext.
    intros [|[|i]]; simpl; [reflexivity | rewrite teval_shift, teval_num; reflexivity | reflexivity].
  Qed.

  Lemma comp_pos a : spos (true, All (Imp (Qinst a) (PX (tv 0)))).
  Proof.
    unfold spos. simpl. rewrite xpol_D; [reflexivity|]. unfold Qinst. rewrite isD_fsubst_eq. exact HQ.
  Qed.

  Lemma B_stable L n : ~ ~ B L n -> B L n.
  Proof. apply below_stable. Qed.

  Lemma B_mono L L' n : (L ≤ L')%ord -> B L n -> B L' n.
  Proof. apply below_mono. Qed.

  (** The positive formulas of a premise give the principal formula, when
      those of the conclusion fail. *)
  Lemma extract L L' x Γ : (L ≤ L')%ord -> spos x ->
    (forall s, In s Γ -> spos s -> ~ ssem (B L') s) ->
    ((forall s, In s (x :: Γ) -> spos s -> ~ ssem (B L) s) -> False) -> ssem (B L) x.
  Proof.
    intros Hle Hx Hpos IH. apply ssem_stable; [apply B_stable|].
    intro Hn. apply IH. intros s [<-|Hs] Hp; [exact Hn|].
    intro H. apply (Hpos s Hs Hp). revert H. apply ssem_mono; [intro m; apply B_mono; exact Hle | exact Hp].
  Qed.

  Lemma pos_lift L L' Γ : (L ≤ L')%ord ->
    (forall s, In s Γ -> spos s -> ~ ssem (B L') s) -> forall s, In s Γ -> spos s -> ~ ssem (B L) s.
  Proof.
    intros Hle H s Hs Hp Hsem. apply (H s Hs Hp). revert Hsem. apply ssem_mono; [|exact Hp].
    intro m. apply B_mono. exact Hle.
  Qed.

  Theorem od_TI_bound n ρ α Γ : OD n ρ α Γ -> ρ <= 1 ->
    (forall s, In s Γ -> cls s) ->
    forall γ, (forall u, In (false, PX u) Γ -> B γ (teval ρ0 u)) ->
    (forall s, In s Γ -> spos s -> ~ ssem (B (Bd γ α)) s) -> False.
  Proof.
    induction 1 as [n ρ α Γ s Hs Hax
                   |n ρ α Γ u v Hu Hv Huv
                   |n ρ α β Γ s s1 s2 Hs Hk _ IH1 _ IH2 Hlt
                   |n ρ α β Γ s s1 s2 s' Hs Hk Hsel _ IH Hlt
                   |n ρ α β Γ s b A Hs Hk HD _ IH Hlt
                   |n ρ α β Γ s b A m Hs Hk Hm _ IH Hlt
                   |n ρ α β Γ s Hr _ IH1 _ IH2 Hlt
                   |n m ρ α β γ' h Γ Hnm _ IH Hh Hmh Hlt];
      intros Hρ Hcls γ Hneg Hpos.
    - (* a true bounded formula *)
      exact (Hpos s Hs (spos_D s (proj1 Hax)) (ssem_dax _ s Hax)).
    - (* [X t, ¬X t'] *)
      apply (Hpos _ Hu eq_refl). unfold ssem. simpl. rewrite Huv.
      apply B_mono with γ; [apply Bd_ge | apply Hneg; exact Hv].
    - (* conjunction *)
      assert (Hle : (Bd γ β ≤ Bd γ α)%ord) by (apply Bd_le; apply ord_lt_le; apply (olt_lt n); exact Hlt).
      destruct (Hcls s Hs) as [Hp|[Hsp|[w ->]]].
      + destruct (spos_conj s s1 s2 Hk Hp) as [Hp1 Hp2].
        assert (H1 : ssem (B (Bd γ β)) s1).
        { apply extract with (Bd γ α) Γ; [exact Hle | exact Hp1 | exact Hpos|].
          apply (IH1 Hρ); [intros x [<-|Hx]; [left; exact Hp1 | apply Hcls; exact Hx]|].
          intros u [E|Hu]; [exfalso; rewrite E in Hp1; exact (not_spos_PX u Hp1) | apply Hneg; exact Hu]. }
        assert (H2 : ssem (B (Bd γ β)) s2).
        { apply extract with (Bd γ α) Γ; [exact Hle | exact Hp2 | exact Hpos|].
          apply (IH2 Hρ); [intros x [<-|Hx]; [left; exact Hp2 | apply Hcls; exact Hx]|].
          intros u [E|Hu]; [exfalso; rewrite E in Hp2; exact (not_spos_PX u Hp2) | apply Hneg; exact Hu]. }
        apply (Hpos s Hs Hp). apply ssem_mono with (B (Bd γ β)); [intro x; apply B_mono; exact Hle | exact Hp|].
        apply ssem_conj with s1 s2; assumption.
      + destruct (special_kind s Hsp) as [E|[a E]]; rewrite E in Hk; [discriminate|].
        injection Hk as <- <-.
        assert (H1 : ssem (B (Bd γ β)) (true, All (Imp (Qinst a) (PX (tv 0))))).
        { apply extract with (Bd γ α) Γ; [exact Hle | apply comp_pos | exact Hpos|].
          apply (IH1 Hρ); [intros x [<-|Hx]; [left; apply comp_pos | apply Hcls; exact Hx]|].
          intros u [E'|Hu]; [discriminate | apply Hneg; exact Hu]. }
        assert (Ha : B (succOrd (Bd γ β)) a) by (apply below_succ; apply (comp_sem _ a H1)).
        refine (IH2 Hρ _ (succOrd (Bd γ β)) _ _).
        * intros x [<-|Hx]; [right; right; exists (num a); reflexivity | apply Hcls; exact Hx].
        * intros u [E'|Hu].
          -- injection E' as <-. rewrite teval_num. exact Ha.
          -- apply B_mono with γ; [|apply Hneg; exact Hu].
             apply ord_le_trans with (Bd γ β); [apply Bd_ge | apply ord_lt_le, succ_lt].
        * intros x [<-|Hx] Hp; [exfalso; exact (not_spos_PX _ Hp)|].
          apply pos_lift with (Bd γ α) Γ; [|exact Hpos | exact Hx | exact Hp].
          apply Bd_step. apply (olt_lt n). exact Hlt.
      + rewrite kind_PX in Hk. discriminate.
    - (* disjunction *)
      assert (Hle : (Bd γ β ≤ Bd γ α)%ord) by (apply Bd_le; apply ord_lt_le; apply (olt_lt n); exact Hlt).
      destruct (Hcls s Hs) as [Hp|[Hsp|[w ->]]].
      + assert (Hp' := spos_disj s s1 s2 s' Hk Hsel Hp).
        assert (H' : ssem (B (Bd γ β)) s').
        { apply extract with (Bd γ α) Γ; [exact Hle | exact Hp' | exact Hpos|].
          apply (IH Hρ); [intros x [<-|Hx]; [left; exact Hp' | apply Hcls; exact Hx]|].
          intros u [E|Hu]; [exfalso; rewrite E in Hp'; exact (not_spos_PX u Hp') | apply Hneg; exact Hu]. }
        apply (Hpos s Hs Hp). apply ssem_mono with (B (Bd γ β)); [intro x; apply B_mono; exact Hle | exact Hp|].
        apply ssem_disj with s1 s2 s'; assumption.
      + destruct (special_kind s Hsp) as [E|[a E]]; rewrite E in Hk; discriminate.
      + rewrite kind_PX in Hk. discriminate.
    - (* ω-rule *)
      destruct (Hcls s Hs) as [Hp|[Hsp|[w ->]]].
      + apply (Hpos s Hs Hp). apply ssem_univ with b A; [exact Hk|]. intro i.
        assert (Hle : (Bd γ (β i) ≤ Bd γ α)%ord) by (apply Bd_le; apply ord_lt_le; apply (olt_lt (Nat.max n (S i))); apply Hlt).
        assert (Hpi : spos (inst b A i)) by (apply spos_inst with s; [left; exact Hk | exact Hp]).
        apply ssem_mono with (B (Bd γ (β i))); [intro x; apply B_mono; exact Hle | exact Hpi|].
        apply extract with (Bd γ α) Γ; [exact Hle | exact Hpi | exact Hpos|].
        apply (IH i Hρ); [intros x [<-|Hx]; [left; exact Hpi | apply Hcls; exact Hx]|].
        intros u [E|Hu]; [exfalso; rewrite E in Hpi; exact (not_spos_PX u Hpi) | apply Hneg; exact Hu].
      + destruct (special_kind s Hsp) as [E|[a E]]; rewrite E in Hk; discriminate.
      + rewrite kind_PX in Hk. discriminate.
    - (* existential *)
      assert (Hle : (Bd γ β ≤ Bd γ α)%ord) by (apply Bd_le; apply ord_lt_le; apply (olt_lt n); exact Hlt).
      destruct (Hcls s Hs) as [Hp|[Hsp|[w ->]]].
      + assert (Hpi : spos (inst b A m)) by (apply spos_inst with s; [right; exact Hk | exact Hp]).
        apply (Hpos s Hs Hp). apply ssem_exis with b A m; [exact Hk|].
        apply ssem_mono with (B (Bd γ β)); [intro x; apply B_mono; exact Hle | exact Hpi|].
        apply extract with (Bd γ α) Γ; [exact Hle | exact Hpi | exact Hpos|].
        apply (IH Hρ); [intros x [<-|Hx]; [left; exact Hpi | apply Hcls; exact Hx]|].
        intros u [E|Hu]; [exfalso; rewrite E in Hpi; exact (not_spos_PX u Hpi) | apply Hneg; exact Hu].
      + destruct (special_kind s Hsp) as [E|[a E]]; rewrite E in Hk; [|discriminate].
        injection Hk as <- <-.
        assert (Hsi : special (inst false (ProgB Q) m)) by (right; exists m; reflexivity).
        refine (IH Hρ _ γ _ _).
        * intros x [<-|Hx]; [right; left; exact Hsi | apply Hcls; exact Hx].
        * intros u [E'|Hu]; [discriminate | apply Hneg; exact Hu].
        * intros x [<-|Hx] Hp; [exfalso; exact (special_not_pos _ Hsi Hp)|].
          apply pos_lift with (Bd γ α) Γ; [exact Hle | exact Hpos | exact Hx | exact Hp].
      + rewrite kind_PX in Hk. discriminate.
    - (* cut on a bounded formula *)
      assert (Hle : (Bd γ β ≤ Bd γ α)%ord) by (apply Bd_le; apply ord_lt_le; apply (olt_lt n); exact Hlt).
      assert (HDs : isD (snd s) = true) by (apply rank_0_D; lia).
      assert (HDn : isD (snd (sneg s)) = true) by exact HDs.
      destruct (dax_dec s HDs) as [Hax|Hf].
      + assert (Hf : dfalse (sneg s)) by (apply dfalse_sneg; rewrite sneg_sneg; exact Hax).
        refine (IH2 Hρ _ γ _ _).
        * intros x [<-|Hx]; [left; apply spos_D; exact HDn | apply Hcls; exact Hx].
        * intros u [E|Hu]; [exfalso; exact (D_not_PX _ false u HDn E) | apply Hneg; exact Hu].
        * intros x [<-|Hx] Hp; [apply ssem_dfalse; exact Hf|].
          apply pos_lift with (Bd γ α) Γ; [exact Hle | exact Hpos | exact Hx | exact Hp].
      + refine (IH1 Hρ _ γ _ _).
        * intros x [<-|Hx]; [left; apply spos_D; exact HDs | apply Hcls; exact Hx].
        * intros u [E|Hu]; [exfalso; exact (D_not_PX _ false u HDs E) | apply Hneg; exact Hu].
        * intros x [<-|Hx] Hp; [apply ssem_dfalse; exact Hf|].
          apply pos_lift with (Bd γ α) Γ; [exact Hle | exact Hpos | exact Hx | exact Hp].
    - (* raising the control *)
      apply (IH Hρ Hcls γ Hneg). apply pos_lift with (Bd γ α); [|exact Hpos].
      apply Bd_le. apply ord_le_trans with (sz (vcat β γ')); [apply reach_le with m; apply reach_prefix|].
      apply ord_lt_le. apply (olt_lt n). exact Hlt.
  Qed.
End Bounding.

(** ** Provable transfinite induction *)

Definition sigma0 : nat -> nat := fun _ => 0.

Lemma prec_R0 R y x : prec (fsubst (up (up (nsub sigma0))) R) y x <-> prec R y x.
Proof.
  unfold prec. rewrite sat_fsubst. apply sat_ext.
  intros [|[|i]]; [reflexivity | reflexivity|]. unfold nsub, sigma0, ρ0. reflexivity.
Qed.

(** If PA proves transfinite induction along a bounded relation [≺], then
    [≺] has height below ε₀. *)
Theorem PA_TI_bound R : isD R = true -> PA [] (TI R) ->
  exists L, (L < ε 0)%ord /\ forall x, below (prec R) L x.
Proof.
  intros HR Hprov.
  assert (Hp : PA [Prog R] (All (PX (tv 0)))).
  { eapply p_impE; [eapply prov_weaken; [exact Hprov | intros ? []] | apply hyp0]. }
  destruct (embed _ _ _ Hp) as [k [ρ [N [HN Hemb]]]].
  set (R0 := fsubst (up (up (nsub sigma0))) R).
  assert (HR0 : isD R0 = true) by (unfold R0; rewrite isD_fsubst_eq; exact HR).
  assert (Hd : OD N (S ρ) (W k) [(true, All (PX (tv 0))); (false, Prog R0)]).
  { apply od_rank with ρ; [|lia]. apply (Hemb N sigma0); [lia | intro i; unfold sigma0; lia]. }
  apply od_elim_all in Hd; [|exact HN].
  set (α := otower ρ (W k)) in Hd.
  exists (Bd zeroOrd α). split.
  - unfold Bd. rewrite addOrd_zero_l. rewrite <- VZ_eq. apply VNotation_below_ε₀.
  - intro x. apply below_ext with (prec R0); [intros y z; apply prec_R0|].
    apply below_stable. intro Hn.
    apply (od_TI_bound R0 HR0 N 1 α _ Hd (le_n 1)) with zeroOrd.
    + intros s [<-|[<-|[]]]; [left; reflexivity | right; left; left; reflexivity].
    + intros u [E|[E|[]]]; discriminate.
    + intros s [<-|[<-|[]]] Hs; [|exfalso; exact (special_not_pos R0 _ (or_introl eq_refl) Hs)].
      intro H. apply Hn. exact (H x).
Qed.

(** In particular there is no infinite descending sequence. *)
Corollary PA_TI_no_descent R : isD R = true -> PA [] (TI R) ->
  forall f, (forall i, prec R (f (S i)) (f i)) -> False.
Proof.
  intros HR Hprov f Hd. destruct (PA_TI_bound R HR Hprov) as [L [_ HL]].
  exact (below_no_descent _ L f (HL (f 0)) Hd).
Qed.

(** Classical corollary.  With the excluded middle as a hypothesis: if PA
    proves transfinite induction along [≺], then [≺] is well-founded with
    order type below ε₀. *)
Theorem PA_TI_wf_EM (EM:excluded_middle) R : isD R = true -> PA [] (TI R) ->
  exists Hwf : well_founded (prec R), (wf_ord (prec R) Hwf < ε 0)%ord.
Proof.
  intros HR Hprov. destruct (PA_TI_bound R HR Hprov) as [L [HL Hb]].
  assert (Hwf : well_founded (prec R)) by (intro x; apply (below_Acc_EM _ EM L x (Hb x))).
  exists Hwf.
  apply ord_le_lt_trans with (succOrd L).
  - unfold wf_ord. rewrite ord_le_unfold. intro x. simpl.
    apply ord_le_lt_trans with L; [apply below_wf_ord_EM; [exact EM | apply Hb] | apply succ_lt].
  - rewrite <- addOrd_zero_r with (x := L) at 1. rewrite <- addOrd_succ.
    apply epslion_additively_closed; [apply zero_complete | exact HL |].
    rewrite ε_fixpoint. apply ord_lt_le_trans with (expOrd ω 1)%ord.
    + rewrite expOrd_one'; [apply omega_gt1 | apply omega_gt0].
    + apply expOrd_monotone. apply succ_least. rewrite ε_fixpoint. apply expOrd_nonzero.
Qed.
