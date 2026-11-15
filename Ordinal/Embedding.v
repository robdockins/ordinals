From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import Notation.VNotation.
From Ordinal Require Import PeanoArith.
From Ordinal Require Import Hardy.
From Ordinal Require Import OmegaLogic.

Local Open Scope nat_scope.

(** * Embedding Peano arithmetic in the ω-logic

    A derivation of [Γ ⊢ A] in [PeanoArith] becomes, for every assignment
    [σ] of numerals below the control [n], an ω-derivation of the sequent
    [A⟨σ⟩, ¬Γ⟨σ⟩] ([embed]).  Its height is [ω^3·k] and its cut rank
    is fixed, both depending only on the derivation, and [n] has to be
    large enough.  Most of the rules become one or two inferences with
    a cut; the induction rule becomes an ω-rule whose [i]-th premise
    chains [i] cuts.  Witnesses given by terms are raised to the
    control with [od_up], at a cost [ω^2·k] that bounds the value of the
    term ([term_bound]).  Bounded formulas are decided: a true one is an
    axiom, and a false one is deleted from a premise. *)

(** ** Small ordinals and their Hardy functions *)

Definition e1 : VForm := V Z Z.
Definition e2 : VForm := V Z e1.
Definition e3 : VForm := V Z e2.

Definition fin (c:nat) : VForm := vrep c Z Z.

Lemma fin_S c : fin (S c) = vcat (fin c) e1.
Proof. unfold fin. rewrite vrep_S_r, vrep_vcat. reflexivity. Qed.

Lemma Pn_fin n c : Pn n (fin (S c)) (fin c).
Proof.
  rewrite fin_S. rewrite <- (vcat_Z (fin c)) at 2. apply Pn_vcat. apply Pn_one.
Qed.

Lemma hardy_fin c : forall x, hardy (fin c) x (x + c).
Proof.
  induction c as [|c IH]; intro x.
  - rewrite Nat.add_0_r. apply hardy_Z.
  - apply hardy_P with (fin c); [apply Pn_fin|].
    replace (x + S c) with (S x + c) by lia. apply IH.
Qed.

Lemma Pn_omega n : Pn n (V e1 Z) (fin (n-1)).
Proof. apply (Pn_exp n e1 Z Z); apply Pn_one. Qed.

Lemma Pn_e2 n : Pn n e2 e1.
Proof. apply Pn_tail. apply Pn_one. Qed.

Lemma Pn_omega2 n : Pn n (V e2 Z) (vrep (n-1) e1 (fin (n-1))).
Proof. apply Pn_exp; [apply Pn_e2 | apply Pn_omega]. Qed.

Lemma hardy_omega_k j : forall x, 1 <= x -> hardy (vrep j e1 Z) x (2^j * x).
Proof.
  induction j as [|j IH]; intros x Hx.
  - simpl. rewrite Nat.add_0_r. apply hardy_Z.
  - rewrite vrep_S_r, vrep_vcat.
    apply hardy_P with (vcat (vrep j e1 Z) (fin (x-1))).
    + apply Pn_vcat. apply Pn_omega.
    + apply hardy_vcat with (S x + (x-1)); [apply hardy_fin|].
      replace (S x + (x - 1)) with (2 * x) by lia.
      replace (2 ^ S j * x) with (2 ^ j * (2 * x)) by (simpl; lia).
      apply IH. lia.
Qed.

Lemma hardy_omega2 x : 1 <= x -> hardy (V e2 Z) x (2^x * x).
Proof.
  intro Hx. apply hardy_P with (vrep (x-1) e1 (fin (x-1))); [apply Pn_omega2|].
  rewrite vrep_vcat. apply hardy_vcat with (S x + (x-1)); [apply hardy_fin|].
  replace (S x + (x - 1)) with (2 * x) by lia.
  replace (2 ^ x * x) with (2 ^ (x-1) * (2 * x)).
  - apply hardy_omega_k. lia.
  - assert (E : 2 ^ x = 2 * 2 ^ (x - 1)).
    { destruct x as [|x]; [lia|]. simpl. rewrite Nat.sub_0_r. lia. }
    rewrite E. ring.
Qed.

Lemma pow2_ge x : x + 1 <= 2^x.
Proof.
  induction x as [|x IH]; simpl; lia.
Qed.

Lemma hardy_omega2_ge x h : 1 <= x -> hardy (V e2 Z) x h -> x * (x + 1) <= h.
Proof.
  intros Hx H. rewrite (hardy_fun _ _ _ H _ (hardy_omega2 x Hx)).
  rewrite Nat.mul_comm. apply Nat.mul_le_mono_r. apply pow2_ge.
Qed.

Definition om2 (k:nat) : VForm := vrep k e2 Z.

Lemma hardy_om2_add a b n h : hardy (om2 (a + b)) n h ->
  exists m, hardy (om2 b) n m /\ hardy (om2 a) m h.
Proof.
  unfold om2. rewrite vrep_add, vrep_vcat. intro H.
  destruct (hardy_vcat_inv _ _ _ _ H) as [m [H1 H2]]. exists m. split; assumption.
Qed.

Lemma hardy_om2_S k n h : hardy (om2 (S k)) n h ->
  exists m, hardy (om2 k) n m /\ hardy (V e2 Z) m h.
Proof.
  replace (S k) with (1 + k) by reflexivity. intro H.
  destruct (hardy_om2_add 1 k n h H) as [m [H1 H2]]. exists m. split; [exact H1|].
  unfold om2 in H2. simpl in H2. exact H2.
Qed.

(** Every term is bounded by [H_(ω^2·k)] of the control, for assignments
    below the control. *)
Lemma term_bound t : exists k, forall n σ h, 1 <= n -> (forall i, σ i < n) ->
  hardy (om2 k) n h -> teval σ t < h.
Proof.
  induction t as [i| |t [k IH]|s [ks IHs] t [kt IHt]|s [ks IHs] t [kt IHt]].
  - exists 1. intros n σ h Hn Hσ H. simpl.
    apply hardy_om2_S in H as [m [Hm H]]. inversion Hm; subst.
    + apply hardy_omega2_ge in H; [|exact Hn]. specialize (Hσ i). nia.
    + exfalso; eapply Pn_Z; eassumption.
  - exists 1. intros n σ h Hn Hσ H. simpl.
    apply hardy_ge in H. lia.
  - exists (S k). intros n σ h Hn Hσ H. simpl.
    apply hardy_om2_S in H as [m [Hm H]].
    assert (Hv := IH n σ m Hn Hσ Hm).
    apply hardy_omega2_ge in H; [nia | lia].
  - exists (S (ks + kt)). intros n σ h Hn Hσ H. simpl.
    apply hardy_om2_S in H as [m [Hm H]].
    destruct (hardy_om2_add ks kt n m Hm) as [mt [Ht Hs]].
    destruct (hardy_exists (om2 ks) n) as [ms Hms].
    assert (Hvs := IHs n σ ms Hn Hσ Hms). assert (Hvt := IHt n σ mt Hn Hσ Ht).
    assert (Hmsm : ms <= m) by (apply (hardy_mono_arg (om2 ks) n mt); [eapply hardy_ge; exact Ht | exact Hms | exact Hs]).
    assert (Hmtm : mt <= m) by (eapply hardy_ge; exact Hs).
    apply hardy_omega2_ge in H; [nia | lia].
  - exists (S (ks + kt)). intros n σ h Hn Hσ H. simpl.
    apply hardy_om2_S in H as [m [Hm H]].
    destruct (hardy_om2_add ks kt n m Hm) as [mt [Ht Hs]].
    destruct (hardy_exists (om2 ks) n) as [ms Hms].
    assert (Hvs := IHs n σ ms Hn Hσ Hms). assert (Hvt := IHt n σ mt Hn Hσ Ht).
    assert (Hmsm : ms <= m) by (apply (hardy_mono_arg (om2 ks) n mt); [eapply hardy_ge; exact Ht | exact Hms | exact Hs]).
    assert (Hmtm : mt <= m) by (eapply hardy_ge; exact Hs).
    apply hardy_omega2_ge in H; [|lia].
    assert (teval σ s * teval σ t <= (m - 1) * (m - 1)) by (apply Nat.mul_le_mono; lia).
    nia.
Qed.

(** ** Heights [ω^3·k + δ] *)

Definition W (k:nat) : VForm := vrep k e3 Z.

(** [ω^2·j + c] *)
Definition sm (j c:nat) : VForm := vrep j e2 (fin c).

Local Open Scope ord_scope.

Lemma normal_vrep j e x : VF_normal e -> VF_normal x ->
  match x with Z => True | V b _ => VF_denote b <= VF_denote e end -> VF_normal (vrep j e x).
Proof.
  intros He Hx Hlead. induction j as [|j IH]; simpl; [exact Hx|].
  split; [exact He|]. split; [exact IH|].
  destruct j; simpl; [exact Hlead | reflexivity].
Qed.

Lemma e1_normal : VF_normal e1.
Proof. simpl. auto. Qed.

Lemma e2_normal : VF_normal e2.
Proof. simpl. split; [exact I|]. split; [auto|]. reflexivity. Qed.

Lemma e3_normal : VF_normal e3.
Proof. split; [exact I|]. split; [exact e2_normal|]. simpl. apply ord_le_refl. Qed.

Lemma fin_normal c : VF_normal (fin c).
Proof. apply normal_vrep; [exact I | exact I | destruct c; reflexivity]. Qed.

Lemma Z_lt_V a x : Z ◃ V a x.
Proof.
  apply ord_le_lt_trans with (sz a); [apply zero_least | apply VF_denote_shrink1].
Qed.

Lemma sm_normal j c : VF_normal (sm j c).
Proof.
  apply normal_vrep; [exact e2_normal | apply fin_normal|].
  destruct c; simpl; [exact I | apply zero_least].
Qed.

Lemma Ve3_normal : VF_normal (V e3 Z).
Proof. split; [exact e3_normal|]. split; exact I. Qed.

Lemma Ve2_normal : VF_normal (V e2 Z).
Proof. split; [exact e2_normal|]. split; exact I. Qed.

Lemma e2_lt_e3 : e2 ◃ e3.
Proof. apply VF_denote_shrink2. exact e3_normal. Qed.

Lemma fin_lt_exp c e : Z ◃ e -> fin c ◃ V e Z.
Proof. intro H. apply vrep_lt; [exact H | apply Z_lt_V]. Qed.

Lemma sm_lt j c : sm j c ◃ V e3 Z.
Proof. apply vrep_lt; [exact e2_lt_e3 | apply fin_lt_exp; apply Z_lt_V]. Qed.

Local Close Scope ord_scope.

Lemma VF_size_fin c : VF_size (fin c) = c.
Proof. unfold fin. induction c as [|c IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma VF_size_sm j c : VF_size (sm j c) = 3 * j + c.
Proof.
  unfold sm. induction j as [|j IH]; simpl vrep; [apply VF_size_fin|].
  change (VF_size (V e2 (vrep j e2 (fin c)))) with (S (VF_size e2 + VF_size (vrep j e2 (fin c)))).
  rewrite IH. simpl. lia.
Qed.

Lemma reach_ne_olt n b a : reach n b a -> b <> a -> olt n b a.
Proof.
  intros H Hne. destruct H as [a|a a1 b Ha1 Hr]; [contradiction|].
  exists a1. split; assumption.
Qed.

Lemma olt_of_lt n a b : VF_normal a -> VF_normal b -> (a ◃ b)%ord -> VF_size a < n -> olt n a b.
Proof.
  intros Ha Hb Hab Hn. apply reach_ne_olt; [apply reach_of_lt; assumption|].
  intros ->. exact (VF_lt_irrefl _ Hab).
Qed.

Lemma vcat_vrep k e x : vcat (vrep k e Z) x = vrep k e x.
Proof. symmetry. apply vrep_vcat. Qed.

Lemma reach_fin n a b : a <= b -> reach n (fin a) (fin b).
Proof. intro H. unfold fin. apply reach_vrep_le. exact H. Qed.

Lemma olt_fin n a b : a < b -> olt n (fin a) (fin b).
Proof.
  intro H. destruct b as [|b]; [lia|].
  exists (fin b). split; [apply Pn_fin | apply reach_fin; lia].
Qed.

Lemma olt_W_fin n k a b : a < b -> olt n (vcat (W k) (fin a)) (vcat (W k) (fin b)).
Proof. intro H. apply olt_vcat. apply olt_fin. exact H. Qed.

Lemma reach_W n k1 k : k1 <= k -> reach n (W k1) (W k).
Proof. intro H. unfold W. apply reach_vrep_le. exact H. Qed.

Lemma W_S k : W (S k) = vcat (W k) (V e3 Z).
Proof. unfold W. rewrite vrep_S_r, vrep_vcat. reflexivity. Qed.

(** A small ordinal on top of [ω^3·k] is below [ω^3·(k+1)]. *)
Lemma reach_bump n k δ : VF_normal δ -> (δ ◃ V e3 Z)%ord -> VF_size δ < n ->
  reach n (vcat (W k) δ) (W (S k)).
Proof.
  intros Hδ Hlt Hn. rewrite W_S. apply reach_vcat. apply reach_of_lt; auto. exact Ve3_normal.
Qed.

Lemma od_bump n ρ k δ Γ : OD n ρ (vcat (W k) δ) Γ -> VF_normal δ -> (δ ◃ V e3 Z)%ord -> VF_size δ < n ->
  OD n ρ (W (S k)) Γ.
Proof. intros H Hδ Hlt Hn. apply od_height with (vcat (W k) δ); [exact H | apply reach_bump; assumption]. Qed.

Lemma od_bump_fin n ρ k c Γ : OD n ρ (vcat (W k) (fin c)) Γ -> c < n -> OD n ρ (W (S k)) Γ.
Proof.
  intros H Hc. apply od_bump with (fin c); [exact H | apply fin_normal | | rewrite VF_size_fin; exact Hc].
  apply fin_lt_exp. apply Z_lt_V.
Qed.

Lemma od_bump_sm n ρ k j c Γ : OD n ρ (vcat (W k) (sm j c)) Γ -> 3 * j + c < n -> OD n ρ (W (S k)) Γ.
Proof.
  intros H Hc. apply od_bump with (sm j c); [exact H | apply sm_normal | apply sm_lt | rewrite VF_size_sm; exact Hc].
Qed.

(** Small heights lie below [ω^3·k] for [k ≥ 1]. *)
Lemma reach_fin_W n k c : 1 <= k -> c < n -> reach n (fin c) (W k).
Proof.
  intros Hk Hc. eapply reach_trans; [|apply (reach_W n 1 k Hk)].
  replace (W 1) with (vcat (W 0) (V e3 Z)) by reflexivity.
  apply reach_of_lt; [apply fin_normal | exact Ve3_normal | apply fin_lt_exp; apply Z_lt_V | rewrite VF_size_fin; exact Hc].
Qed.

Lemma reach_sm_W n k j c : 1 <= k -> 3 * j + c < n -> reach n (sm j c) (W k).
Proof.
  intros Hk Hc. eapply reach_trans; [|apply (reach_W n 1 k Hk)].
  replace (W 1) with (vcat (W 0) (V e3 Z)) by reflexivity.
  apply reach_of_lt; [apply sm_normal | exact Ve3_normal | apply sm_lt | rewrite VF_size_sm; exact Hc].
Qed.

Lemma reach_W_vcat n k δ : reach n (W k) (vcat (W k) δ).
Proof. apply reach_prefix. Qed.

(** [c ≺_n ω^2] for [c < n]. *)
Lemma olt_fin_om2 n c : c < n -> olt n (fin c) (V e2 Z).
Proof.
  intro Hc. apply olt_of_lt; [apply fin_normal | exact Ve2_normal | | rewrite VF_size_fin; exact Hc].
  apply fin_lt_exp. apply Z_lt_V.
Qed.

(** ** Numeral instances *)

Definition nsub (σ:nat -> nat) : nat -> aterm := fun i => num (σ i).
Definition ninst (σ:nat -> nat) (A:form) : form := fsubst (nsub σ) A.

Lemma asubst_num τ m : asubst τ (num m) = num m.
Proof. induction m as [|m IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma asubst_inst1_shift u t : asubst (inst1 u) (asubst shift_sub t) = t.
Proof. rewrite asubst_comp. rewrite asubst_ext with (τ := tv); [apply asubst_id | reflexivity]. Qed.

Lemma ninst_inst σ A i : sub1 (fsubst (up (nsub σ)) A) (num i) = ninst (scons i σ) A.
Proof.
  unfold sub1, ninst. rewrite fsubst_comp. apply fsubst_ext.
  intros [|j]; simpl; [reflexivity | apply asubst_inst1_shift].
Qed.

Lemma ninst_fshift σ i G : ninst (scons i σ) (fshift G) = ninst σ G.
Proof. unfold ninst, fshift. rewrite fsubst_comp. apply fsubst_ext. intro j. reflexivity. Qed.

Lemma ninst_suc σ A i : ninst (scons i σ) (fsubst suc_sub A) = sub1 (fsubst (up (nsub σ)) A) (num (S i)).
Proof.
  unfold sub1, ninst. rewrite !fsubst_comp. apply fsubst_ext.
  intros [|j]; simpl; [reflexivity | symmetry; apply asubst_inst1_shift].
Qed.

Lemma ninst_sub1 σ A t : ninst σ (sub1 A t) = sub1 (fsubst (up (nsub σ)) A) (asubst (nsub σ) t).
Proof. unfold ninst. apply fsubst_sub1. Qed.

Lemma ninst_sub1_tz σ A : ninst σ (sub1 A tz) = sub1 (fsubst (up (nsub σ)) A) (num 0).
Proof. rewrite ninst_sub1. reflexivity. Qed.

Lemma teval_nsub ρ σ t : teval ρ (asubst (nsub σ) t) = teval σ t.
Proof. rewrite teval_asubst. apply teval_ext. intro i. apply teval_num. Qed.

Lemma ninst_All σ A : ninst σ (All A) = All (fsubst (up (nsub σ)) A).
Proof. reflexivity. Qed.

Lemma ninst_Ex σ A : ninst σ (Ex A) = Ex (fsubst (up (nsub σ)) A).
Proof. reflexivity. Qed.

Lemma isD_ninst σ A : isD (ninst σ A) = isD A.
Proof. apply isD_fsubst_eq. Qed.

Lemma rank_ninst σ A : rank (ninst σ A) = rank A.
Proof. apply rank_fsubst. Qed.

(** ** The identity sequent, up to the values of terms *)

Fixpoint fsize (A:form) : nat :=
  match A with
  | Eq _ _ | Bot => 0
  | And A B | Or A B | Imp A B => S (fsize A + fsize B)
  | All A | Ex A => S (fsize A)
  end.

Definition teq (τ1 τ2:nat -> aterm) : Prop := forall i ρ, teval ρ (τ1 i) = teval ρ (τ2 i).

Lemma teq_sym τ1 τ2 : teq τ1 τ2 -> teq τ2 τ1.
Proof. intros H i ρ. symmetry. apply H. Qed.

Lemma teq_inst τ1 τ2 i : teq τ1 τ2 ->
  teq (fun j => asubst (inst1 (num i)) (up τ1 j)) (fun j => asubst (inst1 (num i)) (up τ2 j)).
Proof.
  intros H [|j] ρ; simpl; [reflexivity|]. rewrite !asubst_inst1_shift. apply H.
Qed.

Lemma sub1_up_comp τ B i : sub1 (fsubst (up τ) B) (num i) = fsubst (fun j => asubst (inst1 (num i)) (up τ j)) B.
Proof. unfold sub1. apply fsubst_comp. Qed.

Lemma sat_teq τ1 τ2 B : teq τ1 τ2 -> (sat ρ0 (fsubst τ1 B) <-> sat ρ0 (fsubst τ2 B)).
Proof. intro H. rewrite !sat_fsubst. apply sat_ext. intro i. apply H. Qed.

Lemma od_id_D B τ1 τ2 n ρ α Γ : teq τ1 τ2 -> isD B = true ->
  In (false, fsubst τ1 B) Γ -> In (true, fsubst τ2 B) Γ -> OD n ρ α Γ.
Proof.
  intros Hτ HD H1 H2.
  assert (HD1 : isD (fsubst τ1 B) = true) by (rewrite isD_fsubst_eq; exact HD).
  assert (HD2 : isD (fsubst τ2 B) = true) by (rewrite isD_fsubst_eq; exact HD).
  destruct (deval ρ0 (fsubst τ1 B)) eqn:Hv.
  - apply od_ax with (true, fsubst τ2 B); [exact H2|]. split; [exact HD2|].
    apply deval_sat; [exact HD2|]. apply (sat_teq τ1 τ2 B Hτ). apply deval_sat; assumption.
  - apply od_ax with (false, fsubst τ1 B); [exact H1|]. split; [exact HD1 | exact Hv].
Qed.

Theorem od_id B : forall τ1 τ2 n ρ Γ, teq τ1 τ2 ->
  In (false, fsubst τ1 B) Γ -> In (true, fsubst τ2 B) Γ -> OD n ρ (fin (2 * fsize B)) Γ.
Proof.
  induction B as [s t| |B1 IH1 B2 IH2|B1 IH1 B2 IH2|B1 IH1 B2 IH2|B IH|B IH];
    intros τ1 τ2 n ρ Γ Hτ H1 H2;
    match goal with |- OD _ _ (fin (2 * fsize ?B0)) _ =>
      destruct (isD B0) eqn:HD; [apply (od_id_D B0 τ1 τ2); assumption|] end.
  - simpl in HD. discriminate.
  - simpl in HD. discriminate.
  - (* And *)
    apply od_conj with (fin (2 * fsize (And B1 B2) - 1)) (true, fsubst τ2 (And B1 B2))
      (true, fsubst τ2 B1) (true, fsubst τ2 B2); [exact H2 | reflexivity | | | apply olt_fin; simpl; lia].
    + apply od_disj with (fin (2 * fsize (And B1 B2) - 2)) (false, fsubst τ1 (And B1 B2))
        (false, fsubst τ1 B1) (false, fsubst τ1 B2) (false, fsubst τ1 B1);
        [right; exact H1 | reflexivity | left; reflexivity | | apply olt_fin; simpl; lia].
      apply od_height with (fin (2 * fsize B1)); [|apply reach_fin; simpl; lia].
      apply (IH1 τ1 τ2); [exact Hτ | left; reflexivity | right; left; reflexivity].
    + apply od_disj with (fin (2 * fsize (And B1 B2) - 2)) (false, fsubst τ1 (And B1 B2))
        (false, fsubst τ1 B1) (false, fsubst τ1 B2) (false, fsubst τ1 B2);
        [right; exact H1 | reflexivity | right; reflexivity | | apply olt_fin; simpl; lia].
      apply od_height with (fin (2 * fsize B2)); [|apply reach_fin; simpl; lia].
      apply (IH2 τ1 τ2); [exact Hτ | left; reflexivity | right; left; reflexivity].
  - (* Or *)
    apply od_conj with (fin (2 * fsize (Or B1 B2) - 1)) (false, fsubst τ1 (Or B1 B2))
      (false, fsubst τ1 B1) (false, fsubst τ1 B2); [exact H1 | reflexivity | | | apply olt_fin; simpl; lia].
    + apply od_disj with (fin (2 * fsize (Or B1 B2) - 2)) (true, fsubst τ2 (Or B1 B2))
        (true, fsubst τ2 B1) (true, fsubst τ2 B2) (true, fsubst τ2 B1);
        [right; exact H2 | reflexivity | left; reflexivity | | apply olt_fin; simpl; lia].
      apply od_height with (fin (2 * fsize B1)); [|apply reach_fin; simpl; lia].
      apply (IH1 τ1 τ2); [exact Hτ | right; left; reflexivity | left; reflexivity].
    + apply od_disj with (fin (2 * fsize (Or B1 B2) - 2)) (true, fsubst τ2 (Or B1 B2))
        (true, fsubst τ2 B1) (true, fsubst τ2 B2) (true, fsubst τ2 B2);
        [right; exact H2 | reflexivity | right; reflexivity | | apply olt_fin; simpl; lia].
      apply od_height with (fin (2 * fsize B2)); [|apply reach_fin; simpl; lia].
      apply (IH2 τ1 τ2); [exact Hτ | right; left; reflexivity | left; reflexivity].
  - (* Imp *)
    apply od_conj with (fin (2 * fsize (Imp B1 B2) - 1)) (false, fsubst τ1 (Imp B1 B2))
      (true, fsubst τ1 B1) (false, fsubst τ1 B2); [exact H1 | reflexivity | | | apply olt_fin; simpl; lia].
    + apply od_disj with (fin (2 * fsize (Imp B1 B2) - 2)) (true, fsubst τ2 (Imp B1 B2))
        (false, fsubst τ2 B1) (true, fsubst τ2 B2) (false, fsubst τ2 B1);
        [right; exact H2 | reflexivity | left; reflexivity | | apply olt_fin; simpl; lia].
      apply od_height with (fin (2 * fsize B1)); [|apply reach_fin; simpl; lia].
      apply (IH1 τ2 τ1); [apply teq_sym; exact Hτ | left; reflexivity | right; left; reflexivity].
    + apply od_disj with (fin (2 * fsize (Imp B1 B2) - 2)) (true, fsubst τ2 (Imp B1 B2))
        (false, fsubst τ2 B1) (true, fsubst τ2 B2) (true, fsubst τ2 B2);
        [right; exact H2 | reflexivity | right; reflexivity | | apply olt_fin; simpl; lia].
      apply od_height with (fin (2 * fsize B2)); [|apply reach_fin; simpl; lia].
      apply (IH2 τ1 τ2); [exact Hτ | right; left; reflexivity | left; reflexivity].
  - (* All *)
    apply od_univ with (fun _ => fin (2 * fsize (All B) - 1)) (true, fsubst τ2 (All B)) true (fsubst (up τ2) B);
      [exact H2 | reflexivity | exact (eq_trans (isD_fsubst_eq (All B) τ2) HD) | | intro i; apply olt_fin; simpl; lia].
    intro i.
    apply od_exis with (fin (2 * fsize (All B) - 2)) (false, fsubst τ1 (All B)) false (fsubst (up τ1) B) i;
      [right; exact H1 | reflexivity | lia | | apply olt_fin; simpl; lia].
    apply od_height with (fin (2 * fsize B)); [|apply reach_fin; simpl; lia].
    unfold inst. rewrite !sub1_up_comp.
    apply (IH _ _ _ _ _ (teq_inst τ1 τ2 i Hτ)); [left; reflexivity | right; left; reflexivity].
  - (* Ex *)
    apply od_univ with (fun _ => fin (2 * fsize (Ex B) - 1)) (false, fsubst τ1 (Ex B)) false (fsubst (up τ1) B);
      [exact H1 | reflexivity | exact (eq_trans (isD_fsubst_eq (Ex B) τ1) HD) | | intro i; apply olt_fin; simpl; lia].
    intro i.
    apply od_exis with (fin (2 * fsize (Ex B) - 2)) (true, fsubst τ2 (Ex B)) true (fsubst (up τ2) B) i;
      [right; exact H2 | reflexivity | lia | | apply olt_fin; simpl; lia].
    apply od_height with (fin (2 * fsize B)); [|apply reach_fin; simpl; lia].
    unfold inst. rewrite !sub1_up_comp.
    apply (IH _ _ _ _ _ (teq_inst τ1 τ2 i Hτ)); [right; left; reflexivity | left; reflexivity].
Qed.

(** ** Bounded quantifiers have small counterexamples *)

Definition dbound (A:form) : nat :=
  match A with
  | All (Imp (Ex (Eq (tplus (tv 1) (tv 0)) v)) _) => teval (scons 0 (scons 0 ρ0)) v
  | Ex (Eq (tplus u (tv 0)) v) => teval (scons 0 ρ0) v
  | _ => 0
  end.

Lemma fall_false b f : fall b f = false -> exists z, z <= b /\ f z = false.
Proof.
  induction b as [|b IH]; simpl; intro H.
  - exists 0. split; [lia | exact H].
  - apply andb_false_iff in H as [H|H].
    + destruct (IH H) as [z [Hz Hf]]. exists z. split; [lia | exact Hf].
    + exists (S b). split; [lia | exact H].
Qed.

Lemma teval_occ01 ρ a b a' b' v : occ 0 v = false -> occ 1 v = false ->
  teval (scons a (scons b ρ)) v = teval (scons a' (scons b' ρ)) v.
Proof.
  intros H0 H1. apply teval_occ. intros [|[|i]] Hi; simpl; auto.
  - rewrite H0 in Hi. discriminate.
  - rewrite H1 in Hi. discriminate.
Qed.

Lemma teval_occ0 ρ a a' v : occ 0 v = false -> teval (scons a ρ) v = teval (scons a' ρ) v.
Proof.
  intro H0. apply teval_occ. intros [|i] Hi; simpl; auto. rewrite H0 in Hi. discriminate.
Qed.

Lemma D_univ_witness s b A : isD (snd s) = true -> kindof s = KUniv b A -> dfalse s ->
  exists i, i <= dbound (snd s) /\ dfalse (inst b A i).
Proof.
  destruct s as [[|] F]; intros HD Hk Hf;
    destruct F as [| | | | |F|F]; simpl in Hk; try discriminate; injection Hk as <- <-;
    cbn [snd] in HD; apply isD_DP in HD; inversion HD as [| | | | |v B Hv0 Hv1 HB|u v Hu Hv]; subst.
  - destruct Hf as [_ Hf]. simpl in Hf. apply fall_false in Hf as [z [Hz HB']].
    exists z. split; [exact Hz|].
    assert (Hi : isD (sub1 (Imp (Ex (Eq (tplus (tv 1) (tv 0)) v)) B) (num z)) = true).
    { apply isD_quant_inst. left. exact (DP_isD _ HD). }
    split; [exact Hi|]. simpl snd. rewrite deval_sub1 by (apply (isD_fsubst_back _ (inst1 (num z))); exact Hi).
    simpl. rewrite HB'.
    rewrite (teval_occ01 ρ0 0 z 0 0 v Hv0 Hv1).
    assert (E : (z <=? teval (scons 0 (scons 0 ρ0)) v) = true) by (apply Nat.leb_le; exact Hz).
    rewrite E. reflexivity.
  - destruct Hf as [_ Hf]. simpl in Hf. apply Nat.leb_le in Hf.
    exists (teval (scons 0 ρ0) v - teval (scons 0 ρ0) u). split; [simpl; lia|].
    assert (Hi : isD (sub1 (Eq (tplus u (tv 0)) v) (num (teval (scons 0 ρ0) v - teval (scons 0 ρ0) u))) = true)
      by reflexivity.
    split; [exact Hi|]. simpl snd. rewrite deval_sub1 by reflexivity.
    set (d := teval (scons 0 ρ0) v - teval (scons 0 ρ0) u). simpl.
    rewrite (teval_occ0 ρ0 d 0 u Hu), (teval_occ0 ρ0 d 0 v Hv).
    apply Nat.eqb_eq. unfold d. lia.
Qed.

Lemma dbound_ninst F : isD F = true -> exists k, forall n σ h, 1 <= n -> (forall i, σ i < n) ->
  hardy (om2 k) n h -> dbound (ninst σ F) < h.
Proof.
  intro HD. apply isD_DP in HD.
  inversion HD as [s t| |A B _ _|A B _ _|A B _ _|v B Hv0 Hv1 HB|u v Hu Hv]; subst;
    try (exists 0; intros n σ h Hn Hσ Hh; apply hardy_ge in Hh; simpl; lia).
  - destruct (term_bound v) as [k Hk]. exists k. intros n σ h Hn Hσ Hh.
    unfold ninst. simpl. rewrite teval_asubst.
    rewrite (teval_ext _ (scons 0 (scons 0 σ))).
    + apply (Hk n (scons 0 (scons 0 σ)) h Hn); [intros [|[|i]]; simpl; auto; lia | exact Hh].
    + intros [|[|i]]; simpl; auto. rewrite !teval_shift. apply teval_num.
  - destruct (term_bound v) as [k Hk]. exists k. intros n σ h Hn Hσ Hh.
    unfold ninst. simpl. rewrite teval_asubst.
    rewrite (teval_ext _ (scons 0 σ)).
    + apply (Hk n (scons 0 σ) h Hn); [intros [|i]; simpl; auto; lia | exact Hh].
    + intros [|i]; simpl; auto. rewrite !teval_shift. apply teval_num.
Qed.

(** ** Introducing a universal

    From instances at the raised controls, below [ω^3·k + ω^2].  For a
    bounded universal the ω-rule is unavailable: a true one is an axiom,
    and a false one has a counterexample below the bound of its
    quantifier, whose premise is used after raising the control. *)
Lemma od_univ_intro n ρ k kv s b A Γ (β:nat -> VForm) :
  In s Γ -> kindof s = KUniv b A ->
  (isD (snd s) = true -> forall h, hardy (om2 kv) n h -> dbound (snd s) < h) ->
  (forall i, OD (Nat.max n (S i)) ρ (β i) (inst b A i :: Γ)) ->
  (forall i, olt (Nat.max n (S i)) (β i) (vcat (W k) (V e2 Z))) ->
  OD n ρ (vcat (W k) (sm (S kv) 1)) Γ.
Proof.
  intros Hs Hk Hb Hprem Hlt.
  assert (Htop : reach n (vcat (W k) (V e2 Z)) (vcat (W k) (sm (S kv) 1))).
  { apply reach_vcat. apply (reach_prefix n (V e2 Z)). }
  destruct (isD (snd s)) eqn:HD.
  - destruct (dax_dec s HD) as [Hax|Hf]; [apply od_ax with s; assumption|].
    destruct (D_univ_witness s b A HD Hk Hf) as [i [Hi Hfi]].
    destruct (hardy_exists (om2 kv) n) as [h Hh].
    assert (Hih : i < h) by (specialize (Hb eq_refl h Hh); lia).
    apply od_up with (Nat.max n (S i)) (vcat (W k) (V e2 Z)) (om2 kv) h; [lia | | exact Hh | |].
    + eapply od_struct; [apply (Hprem i) | lia | lia | apply olt_reach; apply (Hlt i) |].
      apply sub_mod_drop; [exact Hfi|]. intros x Hx. left. exact Hx.
    + apply Nat.max_lub; [eapply hardy_ge; exact Hh | lia].
    + rewrite vcat_assoc. apply olt_vcat.
      change (vcat (V e2 Z) (om2 kv)) with (om2 (S kv)).
      unfold sm. rewrite vrep_vcat. apply olt_vcat_r. discriminate.
  - apply od_univ with β s b A; [exact Hs | exact Hk | exact HD | exact Hprem |].
    intro i. apply olt_reach_trans with (vcat (W k) (V e2 Z)); [apply Hlt|].
    apply reach_mono with n; [lia | exact Htop].
Qed.

(** ** The embedding *)

Definition seqof (σ:nat -> nat) (Γ:list form) (A:form) : list sform :=
  (true, ninst σ A) :: map (fun G => (false, ninst σ G)) Γ.

Definition bnd (σ:nat -> nat) (n:nat) : Prop := forall i, σ i < n.

Definition Emb (Γ:list form) (A:form) : Prop :=
  exists k ρ N, 3 <= N /\ forall n σ, N <= n -> bnd σ n -> OD n ρ (W k) (seqof σ Γ A).

Ltac incl_tac := let y := fresh "y" in let Hy := fresh "Hy" in
  intros y Hy; simpl in *; intuition.

Lemma In_neg σ Γ G : In G Γ -> In (false, ninst σ G) (map (fun G => (false, ninst σ G)) Γ).
Proof. intro H. apply in_map with (f := fun G => (false, ninst σ G)). exact H. Qed.

Lemma bnd_mono σ n m : n <= m -> bnd σ n -> bnd σ m.
Proof. intros H Hσ i. specialize (Hσ i). lia. Qed.

Lemma bnd_scons σ n i : bnd σ n -> bnd (scons i σ) (Nat.max n (S i)).
Proof. intros Hσ [|j]; simpl; [lia | specialize (Hσ j); lia]. Qed.

Lemma od_lift n ρ k Γ ρ' k' Δ : OD n ρ (W k) Γ -> ρ <= ρ' -> k <= k' -> incl Γ Δ -> OD n ρ' (W k') Δ.
Proof.
  intros H Hρ Hk Hi. eapply od_struct; [exact H | lia | exact Hρ | apply reach_W; exact Hk |].
  apply sub_mod_incl. exact Hi.
Qed.

Lemma od_lift_to n ρ k Γ ρ' α Δ : OD n ρ (W k) Γ -> ρ <= ρ' -> reach n (W k) α -> incl Γ Δ -> OD n ρ' α Δ.
Proof.
  intros H Hρ Hk Hi. eapply od_struct; [exact H | lia | exact Hρ | exact Hk |].
  apply sub_mod_incl. exact Hi.
Qed.

Lemma fsize_fsubst A : forall σ, fsize (fsubst σ A) = fsize A.
Proof. induction A; intro σ; simpl; auto. Qed.

(** The identity sequent for an instance. *)
Lemma od_id_inst n ρ k σ A Γ : 1 <= k -> 2 * fsize A < n ->
  In (false, ninst σ A) Γ -> In (true, ninst σ A) Γ -> OD n ρ (W k) Γ.
Proof.
  intros Hk Hn H1 H2. apply od_height with (fin (2 * fsize A)).
  - apply od_id with (nsub σ) (nsub σ); [intros i ρ'; reflexivity | exact H1 | exact H2].
  - apply reach_fin_W; assumption.
Qed.

Lemma emb_hyp Γ A : In A Γ -> Emb Γ A.
Proof.
  intro H. exists 1, 0, (Nat.max 3 (S (2 * fsize A))). split; [lia|].
  intros n σ Hn Hσ. apply od_id_inst with σ A; [lia | lia | right; apply In_neg; exact H | left; reflexivity].
Qed.

Lemma emb_botE Γ A : Emb Γ Bot -> Emb Γ A.
Proof.
  intros [k [ρ [N [HN H]]]]. exists k, ρ, N. split; [exact HN|]. intros n σ Hn Hσ.
  eapply od_struct; [apply H; eassumption | lia | lia | apply reach_refl |].
  intros x [<-|Hx]; [right; split; reflexivity | left; right; exact Hx].
Qed.

Lemma emb_dne Γ A : Emb Γ (Neg (Neg A)) -> Emb Γ A.
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]].
  exists (S (Nat.max k1 1)), (Nat.max ρ1 (S (rank (Neg (Neg A))))), (Nat.max N1 (2 * fsize A + 4)).
  split; [lia|]. intros n σ Hn Hσ.
  set (k := Nat.max k1 1). set (A' := ninst σ A).
  apply od_bump_fin with 1; [|lia].
  apply od_cut with (W k) (true, Imp (Imp A' Bot) Bot); [| | | apply olt_vcat_r; discriminate].
  - simpl snd. change (Imp (Imp A' Bot) Bot) with (ninst σ (Neg (Neg A))). rewrite rank_ninst. lia.
  - apply od_lift with ρ1 k1 (seqof σ Γ (Neg (Neg A))); [apply H1; [lia | exact Hσ] | lia | lia | incl_tac].
  - apply od_conj with (fin (2 * fsize A + 1)) (false, Imp (Imp A' Bot) Bot) (true, Imp A' Bot) (false, Bot);
      [left; reflexivity | reflexivity | | | ].
    + apply od_disj with (fin (2 * fsize A)) (true, Imp A' Bot) (false, A') (true, Bot) (false, A');
        [left; reflexivity | reflexivity | left; reflexivity | | apply olt_fin; lia].
      apply od_id with (nsub σ) (nsub σ); [intros i ρ'; reflexivity | left; reflexivity | simpl; tauto].
    + apply od_ax with (false, Bot); [left; reflexivity | split; reflexivity].
    + apply olt_reach_trans with (fin (2 * fsize A + 2)); [apply olt_fin; lia|].
      apply reach_fin_W; lia.
Qed.

Lemma emb_andI Γ A B : Emb Γ A -> Emb Γ B -> Emb Γ (And A B).
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]] [k2 [ρ2 [N2 [HN2 H2]]]].
  exists (S (Nat.max k1 k2)), (Nat.max ρ1 ρ2), (Nat.max N1 N2). split; [lia|]. intros n σ Hn Hσ.
  apply od_bump_fin with 1; [|lia].
  apply od_conj with (W (Nat.max k1 k2)) (true, ninst σ (And A B)) (true, ninst σ A) (true, ninst σ B);
    [left; reflexivity | reflexivity | | | apply olt_vcat_r; discriminate].
  - apply od_lift with ρ1 k1 (seqof σ Γ A); [apply H1; [lia | exact Hσ] | lia | lia | incl_tac].
  - apply od_lift with ρ2 k2 (seqof σ Γ B); [apply H2; [lia | exact Hσ] | lia | lia | incl_tac].
Qed.

Lemma emb_andE Γ A B C : (C = A \/ C = B) -> Emb Γ (And A B) -> Emb Γ C.
Proof.
  intros HC [k1 [ρ1 [N1 [HN1 H1]]]].
  exists (S (Nat.max k1 1)), (Nat.max ρ1 (S (rank (And A B)))), (Nat.max N1 (2 * fsize C + 2)).
  split; [lia|]. intros n σ Hn Hσ.
  set (k := Nat.max k1 1).
  apply od_bump_fin with 1; [|lia].
  apply od_cut with (W k) (true, ninst σ (And A B)); [| | | apply olt_vcat_r; discriminate].
  - simpl snd. rewrite rank_ninst. lia.
  - apply od_lift with ρ1 k1 (seqof σ Γ (And A B)); [apply H1; [lia | exact Hσ] | lia | lia | incl_tac].
  - apply od_disj with (fin (2 * fsize C)) (false, ninst σ (And A B)) (false, ninst σ A) (false, ninst σ B)
      (false, ninst σ C); [left; reflexivity | reflexivity | destruct HC as [->| ->]; auto | |].
    + apply od_id with (nsub σ) (nsub σ); [intros i ρ'; reflexivity | left; reflexivity | simpl; tauto].
    + apply olt_reach_trans with (fin (2 * fsize C + 1)); [apply olt_fin; lia|]. apply reach_fin_W; lia.
Qed.

Lemma emb_orI Γ A B C : (C = A \/ C = B) -> Emb Γ C -> Emb Γ (Or A B).
Proof.
  intros HC [k1 [ρ1 [N1 [HN1 H1]]]].
  exists (S k1), ρ1, N1. split; [lia|]. intros n σ Hn Hσ.
  apply od_bump_fin with 1; [|lia].
  apply od_disj with (W k1) (true, ninst σ (Or A B)) (true, ninst σ A) (true, ninst σ B) (true, ninst σ C);
    [left; reflexivity | reflexivity | destruct HC as [->| ->]; auto | | apply olt_vcat_r; discriminate].
  apply od_lift with ρ1 k1 (seqof σ Γ C); [apply H1; [lia | exact Hσ] | lia | lia | incl_tac].
Qed.

Lemma emb_orE Γ A B C : Emb Γ (Or A B) -> Emb (A :: Γ) C -> Emb (B :: Γ) C -> Emb Γ C.
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]] [k2 [ρ2 [N2 [HN2 H2]]]] [k3 [ρ3 [N3 [HN3 H3]]]].
  set (k := Nat.max k1 (Nat.max k2 k3)).
  exists (S k), (Nat.max (Nat.max ρ1 (Nat.max ρ2 ρ3)) (S (rank (Or A B)))), (Nat.max N1 (Nat.max N2 N3)).
  split; [lia|]. intros n σ Hn Hσ.
  apply od_bump_fin with 2; [|lia].
  apply od_cut with (vcat (W k) (fin 1)) (true, ninst σ (Or A B)); [| | | apply olt_W_fin; lia].
  - simpl snd. rewrite rank_ninst. lia.
  - apply od_lift_to with ρ1 k1 (seqof σ Γ (Or A B)); [apply H1; [lia | exact Hσ] | lia | | incl_tac].
    eapply reach_trans; [apply reach_W with (k := k); lia | apply reach_prefix].
  - apply od_conj with (W k) (false, ninst σ (Or A B)) (false, ninst σ A) (false, ninst σ B);
      [left; reflexivity | reflexivity | | | apply olt_vcat_r; discriminate].
    + apply od_lift with ρ2 k2 (seqof σ (A :: Γ) C); [apply H2; [lia | exact Hσ] | lia | lia | incl_tac].
    + apply od_lift with ρ3 k3 (seqof σ (B :: Γ) C); [apply H3; [lia | exact Hσ] | lia | lia | incl_tac].
Qed.

Lemma emb_impI Γ A B : Emb (A :: Γ) B -> Emb Γ (Imp A B).
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]].
  exists (S k1), ρ1, N1. split; [lia|]. intros n σ Hn Hσ.
  apply od_bump_fin with 2; [|lia].
  apply od_disj with (vcat (W k1) (fin 1)) (true, ninst σ (Imp A B)) (false, ninst σ A) (true, ninst σ B)
    (false, ninst σ A); [left; reflexivity | reflexivity | left; reflexivity | | apply olt_W_fin; lia].
  apply od_disj with (W k1) (true, ninst σ (Imp A B)) (false, ninst σ A) (true, ninst σ B)
    (true, ninst σ B); [right; left; reflexivity | reflexivity | right; reflexivity | | apply olt_vcat_r; discriminate].
  apply od_lift with ρ1 k1 (seqof σ (A :: Γ) B); [apply H1; [lia | exact Hσ] | lia | lia | incl_tac].
Qed.

Lemma emb_impE Γ A B : Emb Γ (Imp A B) -> Emb Γ A -> Emb Γ B.
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]] [k2 [ρ2 [N2 [HN2 H2]]]].
  set (k := Nat.max (Nat.max k1 k2) 1).
  exists (S k), (Nat.max (Nat.max ρ1 ρ2) (S (rank (Imp A B)))), (Nat.max (Nat.max N1 N2) (2 * fsize B + 3)).
  split; [lia|]. intros n σ Hn Hσ.
  apply od_bump_fin with 2; [|lia].
  apply od_cut with (vcat (W k) (fin 1)) (true, ninst σ (Imp A B)); [| | | apply olt_W_fin; lia].
  - simpl snd. rewrite rank_ninst. lia.
  - apply od_lift_to with ρ1 k1 (seqof σ Γ (Imp A B)); [apply H1; [lia | exact Hσ] | lia | | incl_tac].
    eapply reach_trans; [apply reach_W with (k := k); lia | apply reach_prefix].
  - apply od_conj with (W k) (false, ninst σ (Imp A B)) (true, ninst σ A) (false, ninst σ B);
      [left; reflexivity | reflexivity | | | apply olt_vcat_r; discriminate].
    + apply od_lift with ρ2 k2 (seqof σ Γ A); [apply H2; [lia | exact Hσ] | lia | lia | incl_tac].
    + apply od_id_inst with σ B; [lia | lia | left; reflexivity | simpl; tauto].
Qed.

(** Axioms: true bounded sentences. *)
Lemma emb_ax Γ A : isD A = true -> (forall σ, sat ρ0 (ninst σ A)) -> Emb Γ A.
Proof.
  intros HD Ht. exists 0, 0, 3. split; [lia|]. intros n σ Hn Hσ.
  apply od_ax with (true, ninst σ A); [left; reflexivity|].
  split; [simpl; rewrite isD_ninst; exact HD|]. simpl. apply deval_sat; [rewrite isD_ninst; exact HD | apply Ht].
Qed.

Lemma sat_ninst_eq σ s t : sat ρ0 (ninst σ (Eq s t)) <-> teval σ s = teval σ t.
Proof. unfold ninst. simpl. rewrite !teval_nsub. reflexivity. Qed.

(** Equations whose sides may differ: either true, or the premise is
    a false bounded formula and can be dropped. *)
Lemma emb_eq_cond Γ s t s' t' : (forall σ, teval σ s = teval σ t -> teval σ s' = teval σ t') ->
  Emb Γ (Eq s t) -> Emb Γ (Eq s' t').
Proof.
  intros Himp [k [ρ [N [HN H]]]]. exists k, ρ, N. split; [exact HN|]. intros n σ Hn Hσ.
  destruct (Nat.eq_dec (teval σ s) (teval σ t)) as [E|E].
  - apply od_ax with (true, ninst σ (Eq s' t')); [left; reflexivity|].
    split; [reflexivity|]. apply deval_sat; [reflexivity|]. apply sat_ninst_eq. apply Himp. exact E.
  - eapply od_struct; [apply H; eassumption | lia | lia | apply reach_refl |].
    intros x [<-|Hx]; [right|left; right; exact Hx].
    split; [reflexivity|]. simpl. apply Nat.eqb_neq. rewrite !teval_nsub. exact E.
Qed.

Lemma map_neg_fshift σ i Γ :
  map (fun G => (false, ninst (scons i σ) G)) (map fshift Γ) = map (fun G => (false, ninst σ G)) Γ.
Proof. rewrite map_map. apply map_ext. intro G. rewrite ninst_fshift. reflexivity. Qed.

Lemma dbound_exists F : exists kv, isD F = true -> forall n σ h, 1 <= n -> bnd σ n ->
  hardy (om2 kv) n h -> dbound (ninst σ F) < h.
Proof.
  destruct (isD F) eqn:HD.
  - destruct (dbound_ninst F HD) as [kv Hkv]. exists kv. intros _. exact Hkv.
  - exists 0. discriminate.
Qed.

Lemma olt_om2_sm n kv : olt n (om2 (S kv)) (sm (S kv) 1).
Proof. unfold sm. rewrite vrep_vcat. apply olt_vcat_r. discriminate. Qed.

Lemma olt_up_sm n k kv :
  olt n (vcat (vcat (W k) (V e2 Z)) (om2 kv)) (vcat (W k) (sm (S kv) 1)).
Proof. rewrite vcat_assoc. apply olt_vcat. apply olt_om2_sm. Qed.

Lemma emb_allI Γ A : Emb (map fshift Γ) A -> Emb Γ (All A).
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]]. destruct (dbound_exists (All A)) as [kv Hkv].
  exists (S k1), ρ1, (Nat.max N1 (3 * S kv + 2)). split; [lia|]. intros n σ Hn Hσ.
  apply od_bump_sm with (S kv) 1; [|lia].
  apply od_univ_intro with (true, All (fsubst (up (nsub σ)) A)) true (fsubst (up (nsub σ)) A) (fun _ => W k1); [left; reflexivity | reflexivity | | |].
  - intros HD h Hh. change (isD (ninst σ (All A)) = true) in HD. rewrite isD_ninst in HD.
    apply (Hkv HD n σ h); [lia | exact Hσ | exact Hh].
  - intro i. apply od_lift with ρ1 k1 (seqof (scons i σ) (map fshift Γ) A);
      [apply H1; [lia | apply bnd_scons; exact Hσ] | lia | lia |].
    unfold seqof. rewrite map_neg_fshift. unfold inst. rewrite ninst_inst. incl_tac.
  - intro i. apply olt_vcat_r. discriminate.
Qed.

Lemma emb_allE Γ A t : Emb Γ (All A) -> Emb Γ (sub1 A t).
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]]. destruct (term_bound t) as [kt Hkt].
  set (k := Nat.max k1 1).
  exists (S k), (Nat.max ρ1 (S (rank (All A)))), (Nat.max N1 (Nat.max (2 * fsize A + 2) (3 * S kt + 2))).
  split; [lia|]. intros n σ Hn Hσ.
  set (t' := asubst (nsub σ) t).
  apply od_bump_fin with 1; [|lia].
  apply od_cut with (W k) (true, ninst σ (All A)); [| | | apply olt_vcat_r; discriminate].
  - simpl snd. rewrite rank_ninst. lia.
  - apply od_lift with ρ1 k1 (seqof σ Γ (All A)); [apply H1; [lia | exact Hσ] | lia | lia | incl_tac].
  - apply od_height with (sm (S kt) 1); [|apply reach_sm_W; lia].
    destruct (hardy_exists (om2 kt) n) as [h Hh].
    assert (Hw : teval σ t < h) by (apply (Hkt n σ h); [lia | exact Hσ | exact Hh]).
    apply od_up with (Nat.max n (S (teval σ t))) (V e2 Z) (om2 kt) h; [lia | | exact Hh | | apply olt_om2_sm].
    + apply od_height with (fin (2 * fsize A + 1)); [|apply olt_reach; apply olt_fin_om2; lia].
      apply od_exis with (fin (2 * fsize A)) (false, ninst σ (All A)) false (fsubst (up (nsub σ)) A) (teval σ t);
        [left; reflexivity | reflexivity | lia | | apply olt_fin; lia].
      rewrite <- (fsize_fsubst A (up (nsub σ))).
      apply od_id with (inst1 (num (teval σ t))) (inst1 t').
      * intros [|j] ρ'; simpl; [rewrite teval_num; unfold t'; rewrite teval_nsub; reflexivity | reflexivity].
      * left. reflexivity.
      * right. right. left. unfold seqof. rewrite ninst_sub1. reflexivity.
    + apply Nat.max_lub; [eapply hardy_ge; exact Hh | lia].
Qed.

Lemma emb_exI Γ A t : Emb Γ (sub1 A t) -> Emb Γ (Ex A).
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]]. destruct (term_bound t) as [kt Hkt].
  set (k := Nat.max k1 1).
  exists (S k), (Nat.max ρ1 (S (rank A))), (Nat.max N1 (Nat.max (2 * fsize A + 2) (3 * S kt + 2))).
  split; [lia|]. intros n σ Hn Hσ.
  set (t' := asubst (nsub σ) t).
  apply od_bump_sm with (S kt) 1; [|lia].
  destruct (hardy_exists (om2 kt) n) as [h Hh].
  assert (Hw : teval σ t < h) by (apply (Hkt n σ h); [lia | exact Hσ | exact Hh]).
  set (m := Nat.max n (S (teval σ t))).
  apply od_up with m (vcat (W k) (V e2 Z)) (om2 kt) h; [lia | | exact Hh | | apply olt_up_sm].
  - apply od_height with (vcat (W k) (fin 2)); [|apply olt_reach; apply olt_vcat; apply olt_fin_om2; lia].
    apply od_exis with (vcat (W k) (fin 1)) (true, ninst σ (Ex A)) true (fsubst (up (nsub σ)) A) (teval σ t);
      [left; reflexivity | reflexivity | lia | | apply olt_W_fin; lia].
    apply od_cut with (W k) (true, sub1 (fsubst (up (nsub σ)) A) t'); [| | | apply olt_vcat_r; discriminate].
    + simpl snd. unfold sub1. rewrite !rank_fsubst. lia.
    + apply od_lift with ρ1 k1 (seqof σ Γ (sub1 A t)); [apply H1; [lia | apply bnd_mono with n; [lia | exact Hσ]] | lia | lia |].
      unfold seqof. rewrite ninst_sub1. incl_tac.
    + apply od_height with (fin (2 * fsize A)); [|apply reach_fin_W; lia].
      rewrite <- (fsize_fsubst A (up (nsub σ))).
      apply od_id with (inst1 t') (inst1 (num (teval σ t))).
      * intros [|j] ρ'; simpl; [rewrite teval_num; unfold t'; rewrite teval_nsub; reflexivity | reflexivity].
      * left. reflexivity.
      * right. left. reflexivity.
  - apply Nat.max_lub; [eapply hardy_ge; exact Hh | lia].
Qed.

Lemma emb_exE Γ A B : Emb Γ (Ex A) -> Emb (A :: map fshift Γ) (fshift B) -> Emb Γ B.
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]] [k2 [ρ2 [N2 [HN2 H2]]]]. destruct (dbound_exists (Ex A)) as [kv Hkv].
  set (k := Nat.max k1 k2).
  exists (S k), (Nat.max (Nat.max ρ1 ρ2) (S (rank (Ex A)))), (Nat.max (Nat.max N1 N2) (3 * S kv + 3)).
  split; [lia|]. intros n σ Hn Hσ.
  apply od_bump_sm with (S kv) 2; [|lia].
  apply od_cut with (vcat (W k) (sm (S kv) 1)) (true, ninst σ (Ex A)); [| | |].
  - simpl snd. rewrite rank_ninst. lia.
  - apply od_lift_to with ρ1 k1 (seqof σ Γ (Ex A)); [apply H1; [lia | exact Hσ] | lia | | incl_tac].
    eapply reach_trans; [apply reach_W with (k := k); lia | apply reach_prefix].
  - apply od_univ_intro with (false, ninst σ (Ex A)) false (fsubst (up (nsub σ)) A) (fun _ => W k2); [left; reflexivity | reflexivity | | |].
    + intros HD h Hh. simpl snd in HD. rewrite isD_ninst in HD.
      apply (Hkv HD n σ h); [lia | exact Hσ | exact Hh].
    + intro i. apply od_lift with (Nat.max ρ1 ρ2) k2 (seqof (scons i σ) (A :: map fshift Γ) (fshift B)).
      * eapply od_rank; [apply H2; [lia | apply bnd_scons; exact Hσ] | lia].
      * lia.
      * lia.
      * unfold seqof. simpl map. rewrite map_neg_fshift, ninst_fshift.
        unfold inst. rewrite ninst_inst. incl_tac.
    + intro i. apply reach_olt_trans with (W k); [apply reach_W; lia | apply olt_vcat_r; discriminate].
  - unfold sm. rewrite (vrep_vcat (S kv) e2 (fin 1)), (vrep_vcat (S kv) e2 (fin 2)).
    apply olt_vcat. apply olt_vcat. apply olt_fin. lia.
Qed.

Lemma emb_leib Γ A s t : Emb Γ (Eq s t) -> Emb Γ (sub1 A s) -> Emb Γ (sub1 A t).
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]] [k2 [ρ2 [N2 [HN2 H2]]]].
  set (k := Nat.max (Nat.max k1 k2) 1).
  exists (S k), (Nat.max (Nat.max ρ1 ρ2) (S (rank A))), (Nat.max (Nat.max N1 N2) (2 * fsize A + 2)).
  split; [lia|]. intros n σ Hn Hσ.
  destruct (Nat.eq_dec (teval σ s) (teval σ t)) as [E|E].
  - apply od_bump_fin with 1; [|lia].
    apply od_cut with (W k) (true, ninst σ (sub1 A s)); [| | | apply olt_vcat_r; discriminate].
    + simpl snd. rewrite rank_ninst. unfold sub1. rewrite rank_fsubst. lia.
    + apply od_lift with ρ2 k2 (seqof σ Γ (sub1 A s)); [apply H2; [lia | exact Hσ] | lia | lia | incl_tac].
    + apply od_height with (fin (2 * fsize A)); [|apply reach_fin_W; lia].
      rewrite <- (fsize_fsubst A (up (nsub σ))).
      apply od_id with (inst1 (asubst (nsub σ) s)) (inst1 (asubst (nsub σ) t)).
      * intros [|j] ρ'; simpl; [rewrite !teval_nsub; exact E | reflexivity].
      * left. rewrite ninst_sub1. reflexivity.
      * right. left. unfold seqof. rewrite ninst_sub1. reflexivity.
  - eapply od_struct; [apply (H1 n σ); [lia | exact Hσ] | lia | lia | apply reach_W; lia |].
    intros x [<-|Hx]; [right|left; right; exact Hx].
    split; [reflexivity|]. simpl. apply Nat.eqb_neq. rewrite !teval_nsub. exact E.
Qed.

Lemma emb_ind Γ A : Emb [] (sub1 A tz) -> Emb [A] (fsubst suc_sub A) -> Emb Γ (All A).
Proof.
  intros [k1 [ρ1 [N1 [HN1 H1]]]] [k2 [ρ2 [N2 [HN2 H2]]]]. destruct (dbound_exists (All A)) as [kv Hkv].
  set (k := Nat.max k1 k2). set (ρ := Nat.max (Nat.max ρ1 ρ2) (S (rank A))).
  exists (S k), ρ, (Nat.max (Nat.max N1 N2) (3 * S kv + 2)). split; [lia|]. intros n σ Hn Hσ.
  assert (Hchain : forall i, OD (Nat.max n (S i)) ρ (vcat (W k) (fin i)) [(true, sub1 (fsubst (up (nsub σ)) A) (num i))]).
  { induction i as [|i IH].
    - simpl. rewrite vcat_Z.
      apply od_lift with ρ1 k1 (seqof σ [] (sub1 A tz)); [apply H1; [lia | apply bnd_mono with n; [lia | exact Hσ]] | lia | lia |].
      unfold seqof. rewrite ninst_sub1_tz. incl_tac.
    - apply od_cut with (vcat (W k) (fin i)) (true, sub1 (fsubst (up (nsub σ)) A) (num i)); [| | | apply olt_W_fin; lia].
      + simpl snd. unfold sub1. rewrite !rank_fsubst. lia.
      + eapply od_struct; [exact IH | lia | lia | apply reach_refl |]. apply sub_mod_incl. incl_tac.
      + apply od_lift_to with ρ2 k2 (seqof (scons i σ) [A] (fsubst suc_sub A)).
        * apply H2; [lia|]. intros [|j]; simpl; [lia | specialize (Hσ j); lia].
        * lia.
        * eapply reach_trans; [apply reach_W with (k := k); lia | apply reach_prefix].
        * unfold seqof. simpl map. rewrite ninst_suc, <- ninst_inst. incl_tac. }
  apply od_bump_sm with (S kv) 1; [|lia].
  apply od_univ_intro with (true, All (fsubst (up (nsub σ)) A)) true (fsubst (up (nsub σ)) A) (fun i => vcat (W k) (fin i));
    [left; reflexivity | reflexivity | | |].
  - intros HD h Hh. change (isD (ninst σ (All A)) = true) in HD. rewrite isD_ninst in HD.
    apply (Hkv HD n σ h); [lia | exact Hσ | exact Hh].
  - intro i. eapply od_struct; [apply (Hchain i) | lia | lia | apply reach_refl |].
    apply sub_mod_incl. unfold inst. incl_tac.
  - intro i. apply olt_vcat. apply olt_fin_om2. lia.
Qed.

Theorem embed cl Γ A : prov cl Γ A -> Emb Γ A.
Proof.
  induction 1 as [Γ A H|Γ A _ IH|Γ A _ _ IH|Γ A B _ IH1 _ IH2|Γ A B _ IH|Γ A B _ IH|Γ A B _ IH|Γ A B _ IH
                 |Γ A B C _ IH1 _ IH2 _ IH3|Γ A B _ IH|Γ A B _ IH1 _ IH2|Γ A _ IH|Γ A t _ IH|Γ A t _ IH
                 |Γ A B _ IH1 _ IH2|Γ t|Γ A s t _ IH1 _ IH2|Γ t|Γ s t _ IH|Γ t|Γ s t|Γ t|Γ s t|Γ A _ IH1 _ IH2].
  - apply emb_hyp. exact H.
  - apply emb_botE. exact IH.
  - apply emb_dne. exact IH.
  - apply emb_andI; assumption.
  - apply emb_andE with A B; [left; reflexivity | exact IH].
  - apply emb_andE with A B; [right; reflexivity | exact IH].
  - apply emb_orI with A; [left; reflexivity | exact IH].
  - apply emb_orI with B; [right; reflexivity | exact IH].
  - apply emb_orE with A B; assumption.
  - apply emb_impI. exact IH.
  - apply emb_impE with A; assumption.
  - apply emb_allI. exact IH.
  - apply emb_allE. exact IH.
  - apply emb_exI with t. exact IH.
  - apply emb_exE with A; assumption.
  - apply emb_ax; [reflexivity|]. intro σ. apply sat_ninst_eq. reflexivity.
  - apply emb_leib with s; assumption.
  - apply emb_ax; [reflexivity|]. intros σ H. simpl in H. discriminate.
  - apply emb_eq_cond with (ts s) (ts t); [intros σ E; simpl in E; lia | exact IH].
  - apply emb_ax; [reflexivity|]. intro σ. apply sat_ninst_eq. simpl. lia.
  - apply emb_ax; [reflexivity|]. intro σ. apply sat_ninst_eq. simpl. lia.
  - apply emb_ax; [reflexivity|]. intro σ. apply sat_ninst_eq. simpl. lia.
  - apply emb_ax; [reflexivity|]. intro σ. apply sat_ninst_eq. simpl. lia.
  - apply emb_ind; assumption.
Qed.
