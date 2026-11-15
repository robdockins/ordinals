From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wellfounded.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import Notation.VNotation.

Local Open Scope nat_scope.

(** * The Hardy hierarchy below ε₀

    Ordinals are V forms ([VNotation]): [V a x] denotes [ω^a + x].
    The forms are lists of exponents, and need not be normal; the
    standard fundamental sequences

      (γ + ω^(a+1))[n] = γ + ω^a·n        (γ + ω^λ)[n] = γ + ω^(λ[n])

    give the predecessor functions [P_n], with [P_n(γ+1) = γ] and
    [P_n(λ) = P_n(λ[n])].  Unfolding the limit steps, [P_n] only ever
    changes the last summand, and

      P_n(ω^a) = ω^(P_n a)·(n-1) + P_n(ω^(P_n a))      (a ≠ 0).

    This is the relation [Pn] below.  [reach n β α] (β ≼_n α) says [β] is
    reached from [α] by [P_n] steps, and the Hardy functions are

      H_0(n) = n        H_α(n) = H_(P_n α)(n+1)      (α ≠ 0),

    the relation [hardy α n m] (m = H_α(n)).  All three are inductive
    relations; [Pn] and [hardy] are total and functional, by
    well-founded induction on the denotation.

    The main results are the Bachmann property [P_n α ≼_(n+1) P_(n+1) α]
    ([Pn_bachmann]), so that [≼_n] grows with [n] ([reach_S]); that
    [H_α] is monotone in its argument and along [≼_n] ([hardy_mono]);
    composition [H_(γ+δ) = H_γ ∘ H_δ] ([hardy_vcat]); and that for
    normal forms, [α < β] gives [α ≼_n β] once [n] exceeds the size of
    [α] ([reach_of_lt]).  Hence [H_α(n) ≤ H_β(n)] for all large [n]
    ([hardy_dominated]). *)

(** ** Sums and repeated summands *)

Fixpoint vcat (a b:VForm) : VForm :=
  match a with Z => b | V e x => V e (vcat x b) end.

(** [vrep k e x] is [ω^e·k + x]. *)
Fixpoint vrep (k:nat) (e x:VForm) : VForm :=
  match k with O => x | S k => V e (vrep k e x) end.

Lemma vcat_Z a : vcat a Z = a.
Proof. induction a as [|e _ x IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma vcat_assoc a b c : vcat (vcat a b) c = vcat a (vcat b c).
Proof. induction a as [|e _ x IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma vrep_vcat k e x : vrep k e x = vcat (vrep k e Z) x.
Proof. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma vrep_add j k e x : vrep (j + k) e x = vrep j e (vrep k e x).
Proof. induction j as [|j IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma vrep_S_r k e x : vrep (S k) e x = vrep k e (V e x).
Proof.
  replace (S k) with (k + 1) by lia. rewrite vrep_add. reflexivity.
Qed.

(** ** Denotations *)

Local Open Scope ord_scope.

Local Hint Resolve VF_complete zero_complete : core.

Lemma V_eq (a x:VForm) : sz (V a x) ≈ expOrd ω (sz a) + sz x.
Proof. apply veblen_onePlus; apply VF_complete. Qed.

Lemma VZ_eq (a:VForm) : sz (V a Z) ≈ expOrd ω (sz a).
Proof. rewrite V_eq. apply addOrd_zero_r. Qed.

Lemma below_exp_add (c:VForm) (x y:Ord) :
  x < expOrd ω (sz c) -> y < expOrd ω (sz c) -> x + y < expOrd ω (sz c).
Proof. apply expOmega_additively_closed. apply VF_complete. Qed.

Lemma VF_ind (P : VForm -> Prop) : (forall a, (forall b, b ◃ a -> P b) -> P a) -> forall a, P a.
Proof.
  intros H a.
  induction a as [a IH] using (well_founded_induction (wf_inverse_image VForm Ord ord_lt sz ord_lt_wf)).
  apply H. exact IH.
Qed.

Lemma V_tail_lt e x y : x ◃ y -> V e x ◃ V e y.
Proof.
  intro H. rewrite !V_eq. apply addOrd_increasing. exact H.
Qed.

Lemma exp_lt e f : e ◃ f -> V e Z ◃ V f Z.
Proof.
  intro H. rewrite !VZ_eq. apply expOrd_increasing; [apply omega_gt1 | exact H].
Qed.

Lemma vrep_lt k e f y : e ◃ f -> y ◃ V e Z -> vrep k e y ◃ V f Z.
Proof.
  intros Hef Hy. induction k as [|k IH]; simpl vrep.
  - eapply ord_lt_trans; [exact Hy | apply exp_lt; exact Hef].
  - rewrite V_eq. rewrite VZ_eq in IH |- *.
    apply below_exp_add; [apply expOrd_increasing; [apply omega_gt1 | exact Hef] | exact IH].
Qed.

Lemma exp_le_V e x : V e Z ⊴ V e x.
Proof. rewrite (V_eq e x), (VZ_eq e). apply addOrd_le1. Qed.

Lemma tail_le_V e x : x ⊴ V e x.
Proof. rewrite V_eq. apply addOrd_le2. Qed.

Lemma exp_shrink e : e ◃ V e Z.
Proof. apply VF_denote_shrink1. Qed.

Local Close Scope ord_scope.

(** ** The predecessor relation *)

Inductive Pn (n:nat) : VForm -> VForm -> Prop :=
| Pn_one : Pn n (V Z Z) Z
| Pn_tail e x y : Pn n x y -> Pn n (V e x) (V e y)
| Pn_exp e e' y : Pn n e e' -> Pn n (V e' Z) y -> Pn n (V e Z) (vrep (n-1) e' y).

Lemma Pn_nonzero n a b : Pn n a b -> a <> Z.
Proof. intro H. destruct H; discriminate. Qed.

Lemma Pn_Z n b : ~ Pn n Z b.
Proof. intro H. exact (Pn_nonzero n Z b H eq_refl). Qed.

Lemma Pn_fun n a b : Pn n a b -> forall c, Pn n a c -> b = c.
Proof.
  intro H. induction H as [|e x y H IH|e e' y H1 IH1 H2 IH2]; intros c Hc.
  - inversion Hc; subst.
    + reflexivity.
    + exfalso; eapply Pn_Z; eassumption.
    + exfalso; eapply Pn_Z; eassumption.
  - inversion Hc; subst.
    + exfalso; eapply Pn_Z; eassumption.
    + f_equal. apply IH. assumption.
    + exfalso; eapply Pn_Z; eassumption.
  - inversion Hc; subst.
    + exfalso; eapply Pn_Z; eassumption.
    + exfalso; eapply Pn_Z; eassumption.
    + match goal with
      | [ H : Pn n e ?e2 |- _ ] => assert (e' = e2) by (apply IH1; exact H); subst e2
      end.
      f_equal. apply IH2. assumption.
Qed.

Local Open Scope ord_scope.

Lemma Pn_lt n a b : Pn n a b -> b ◃ a.
Proof.
  intro H. induction H as [|e x y H IH|e e' y H1 IH1 H2 IH2].
  - apply VF_denote_shrink1.
  - apply V_tail_lt. exact IH.
  - apply vrep_lt; assumption.
Qed.

Lemma Pn_exists_of_exps n a :
  a <> Z ->
  (forall c, V c Z ⊴ a -> exists y, Pn n (V c Z) y) ->
  exists b, Pn n a b.
Proof.
  induction a as [|e _ x IHx]; intros Ha H.
  - contradiction.
  - destruct x as [|f x'].
    + destruct e as [|e1 e2].
      * exists Z. apply Pn_one.
      * apply H. apply exp_le_V.
    + destruct (IHx ltac:(discriminate)) as [y Hy].
      * intros c Hc. apply H. eapply ord_le_trans; [exact Hc | apply tail_le_V].
      * exists (V e y). apply Pn_tail. exact Hy.
Qed.

Lemma Pn_exists_exp n : forall e, exists y, Pn n (V e Z) y.
Proof.
  induction e as [e IH] using VF_ind.
  destruct e as [|f x].
  - exists Z. apply Pn_one.
  - destruct (Pn_exists_of_exps n (V f x)) as [e' He'].
    + discriminate.
    + intros c Hc. apply IH.
      eapply ord_lt_le_trans; [apply exp_shrink | exact Hc].
    + destruct (IH e') as [y Hy].
      * apply Pn_lt with n. exact He'.
      * exists (vrep (n-1) e' y). apply Pn_exp; assumption.
Qed.

Lemma Pn_exists n a : a <> Z -> exists b, Pn n a b.
Proof.
  intro Ha. apply Pn_exists_of_exps; auto.
  intros c _. apply Pn_exists_exp.
Qed.

Local Close Scope ord_scope.

(** [P_0] and [P_1] agree. *)
Lemma Pn_0_1 a b : Pn 0 a b -> Pn 1 a b.
Proof.
  intro H. induction H as [|e x y H IH|e e' y H1 IH1 H2 IH2].
  - apply Pn_one.
  - apply Pn_tail. exact IH.
  - apply (Pn_exp 1 e e' y); assumption.
Qed.

(** [P_n] only changes the tail of a sum. *)
Lemma Pn_vcat n g x y : Pn n x y -> Pn n (vcat g x) (vcat g y).
Proof.
  intro H. induction g as [|e _ g IH]; simpl; [exact H | apply Pn_tail; exact IH].
Qed.

(** ** Reachability: [reach n β α] is [β ≼_n α] *)

Inductive reach (n:nat) : VForm -> VForm -> Prop :=
| reach_refl a : reach n a a
| reach_step a b c : Pn n a b -> reach n c b -> reach n c a.

Lemma reach_trans n a b c : reach n a b -> reach n b c -> reach n a c.
Proof.
  intros H1 H2. induction H2 as [b|b d c' Hb _ IH].
  - exact H1.
  - apply reach_step with d; auto.
Qed.

Lemma reach_one n a b : Pn n a b -> reach n b a.
Proof. intro H. apply reach_step with b; [exact H | apply reach_refl]. Qed.

Lemma reach_vcat n g x y : reach n y x -> reach n (vcat g y) (vcat g x).
Proof.
  intro H. induction H as [x|x x' y Hx _ IH].
  - apply reach_refl.
  - apply reach_step with (vcat g x'); [apply Pn_vcat; exact Hx | exact IH].
Qed.

Lemma reach_le n b a : reach n b a -> (b ⊴ a)%ord.
Proof.
  intro H. induction H as [a|a b c Hab _ IH].
  - reflexivity.
  - eapply ord_le_trans; [exact IH|]. apply ord_lt_le. apply Pn_lt with n. exact Hab.
Qed.

Lemma reach_Z n a : reach n Z a.
Proof.
  induction a as [a IH] using VF_ind.
  destruct a as [|e x].
  - apply reach_refl.
  - destruct (Pn_exists n (V e x)) as [b Hb]; [discriminate|].
    apply reach_step with b; [exact Hb|]. apply IH. apply Pn_lt with n. exact Hb.
Qed.

Lemma reach_prefix n g x : reach n g (vcat g x).
Proof.
  rewrite <- (vcat_Z g) at 1. apply reach_vcat. apply reach_Z.
Qed.

(** A reachable form either is the start or is reached from its
    predecessor. *)
Lemma reach_inv n c a b : reach n c a -> Pn n a b -> c = a \/ reach n c b.
Proof.
  intros H Hab. destruct H as [a|a b' c Hab' Hc].
  - left; reflexivity.
  - right. rewrite (Pn_fun n a b Hab b' Hab'). exact Hc.
Qed.

(** ** The Bachmann property *)

(** Descending into the copies of [ω^e]. *)
Lemma reach_vrep_le n j k e x : j <= k -> reach n (vrep j e Z) (vrep k e x).
Proof.
  intro H. replace k with (j + (k - j)) by lia.
  rewrite vrep_add, (vrep_vcat j e (vrep (k-j) e x)). apply reach_prefix.
Qed.

Lemma reach_exp_mono n e f : 2 <= n -> reach n e f -> reach n (V e Z) (V f Z).
Proof.
  intros Hn H. induction H as [f|f f' e Hf _ IH].
  - apply reach_refl.
  - destruct (Pn_exists_exp n f') as [y Hy].
    apply reach_step with (vrep (n-1) f' y); [apply Pn_exp; assumption|].
    eapply reach_trans; [exact IH|].
    apply (reach_vrep_le n 1 (n-1) f' y). lia.
Qed.

(** [ω^e·(n-1) + P_n(ω^e)] lies below [ω^f] when [e ≼_n P_n f]. *)
Lemma reach_vrep_exp n e g : 2 <= n -> reach n e g ->
  forall y f, Pn n (V e Z) y -> Pn n f g -> reach n (vrep (n-1) e y) (V f Z).
Proof.
  intros Hn H. induction H as [g|g g' e Hg _ IH]; intros y f Hy Hf.
  - apply reach_one. apply Pn_exp; assumption.
  - eapply reach_trans; [apply (IH y g Hy Hg)|].
    destruct (Pn_exists_exp n g) as [z Hz].
    apply reach_step with (vrep (n-1) g z); [apply Pn_exp; assumption|].
    apply (reach_vrep_le n 1 (n-1) g z). lia.
Qed.

Theorem Pn_bachmann n a b c : Pn n a b -> Pn (S n) a c -> reach (S n) b c.
Proof.
  destruct n as [|n].
  { intros Hb Hc. apply Pn_0_1 in Hb. rewrite (Pn_fun 1 a b Hb c Hc). apply reach_refl. }
  intro H. revert c.
  induction H as [|e x y H IH|e e' y H1 IH1 H2 IH2]; intros c Hc.
  - inversion Hc; subst.
    + apply reach_refl.
    + exfalso; eapply Pn_Z; eassumption.
    + exfalso; eapply Pn_Z; eassumption.
  - inversion Hc; subst.
    + exfalso; eapply Pn_Z; eassumption.
    + apply (reach_vcat _ (V e Z)). apply IH. assumption.
    + exfalso; eapply Pn_Z; eassumption.
  - inversion Hc as [| |e0 e'' y2 He'' Hy2]; subst.
    + exfalso; eapply Pn_Z; eassumption.
    + exfalso; eapply Pn_Z; eassumption.
    + replace (S n - 1) with n by lia. replace (S (S n) - 1) with (S n) by lia.
      (* [y] lies below [ω^e' + z] for any [z], via [P_(n+2)(ω^e')] *)
      assert (Hy : forall z, reach (S (S n)) y (V e' z)).
      { intro z. destruct (Pn_exists_exp (S (S n)) e') as [y' Hy'].
        eapply reach_trans; [apply (IH2 y' Hy')|].
        eapply reach_trans; [apply reach_one; exact Hy'|].
        apply (reach_prefix _ (V e' Z)). }
      destruct (IH1 e'' He'') as [e''|e'' g e' Hg Hrest].
      * rewrite vrep_S_r, (vrep_vcat n e'' y), (vrep_vcat n e'' (V e'' y2)).
        apply reach_vcat. apply Hy.
      * destruct (Pn_exists_exp (S (S n)) e') as [y' Hy'].
        assert (Hlow : reach (S (S n)) (vrep n e' y) (vrep (S n) e' y')).
        { rewrite vrep_S_r, (vrep_vcat n e' y), (vrep_vcat n e' (V e' y')).
          apply reach_vcat. apply Hy. }
        eapply reach_trans; [exact Hlow|].
        eapply reach_trans.
        -- replace (S n) with (S (S n) - 1) at 1 by lia.
           apply (reach_vrep_exp (S (S n)) e' g ltac:(lia) Hrest y' e'' Hy' Hg).
        -- apply (reach_prefix _ (V e'' Z)).
Qed.

(** Hence [≼_n] grows with [n]. *)
Lemma reach_S n b a : reach n b a -> reach (S n) b a.
Proof.
  intro H. induction H as [a|a a1 b Ha _ IH].
  - apply reach_refl.
  - destruct (Pn_exists (S n) a (Pn_nonzero n a a1 Ha)) as [c Hc].
    apply reach_step with c; [exact Hc|].
    eapply reach_trans; [exact IH|]. apply Pn_bachmann with a; assumption.
Qed.

Lemma reach_mono n m b a : n <= m -> reach n b a -> reach m b a.
Proof.
  intros Hnm H. induction Hnm as [|m _ IH]; [exact H | apply reach_S; exact IH].
Qed.

(** ** The Hardy functions: [hardy α n m] is [H_α(n) = m] *)

Inductive hardy : VForm -> nat -> nat -> Prop :=
| hardy_Z n : hardy Z n n
| hardy_P a b n m : Pn n a b -> hardy b (S n) m -> hardy a n m.

Lemma hardy_fun a n m : hardy a n m -> forall m', hardy a n m' -> m = m'.
Proof.
  intro H. induction H as [n|a b n m Hab _ IH]; intros m' H'.
  - inversion H' as [|a0 b0 n0 m0 Hb _]; subst.
    + reflexivity.
    + exfalso; eapply Pn_Z; eassumption.
  - inversion H' as [n0|a0 b0 n0 m0 Hb Hm]; subst.
    + exfalso; eapply Pn_Z; eassumption.
    + apply IH. rewrite (Pn_fun n a b Hab b0 Hb). exact Hm.
Qed.

Lemma hardy_exists a : forall n, exists m, hardy a n m.
Proof.
  induction a as [a IH] using VF_ind. intro n.
  destruct a as [|e x].
  - exists n. apply hardy_Z.
  - destruct (Pn_exists n (V e x)) as [b Hb]; [discriminate|].
    destruct (IH b (Pn_lt n _ _ Hb) (S n)) as [m Hm].
    exists m. apply hardy_P with b; assumption.
Qed.

Lemma hardy_ge a n m : hardy a n m -> n <= m.
Proof. intro H. induction H; lia. Qed.

Lemma hardy_gt a n m : hardy a n m -> a <> Z -> n < m.
Proof.
  intros H Ha. destruct H as [n|a b n m _ H].
  - contradiction.
  - apply hardy_ge in H. lia.
Qed.

Lemma hardy_P_inv a b n m : Pn n a b -> hardy a n m -> hardy b (S n) m.
Proof.
  intros Hab H. inversion H as [n0|a0 b0 n0 m0 Hb Hm]; subst.
  - exfalso; eapply Pn_Z; eassumption.
  - rewrite (Pn_fun n a b Hab b0 Hb). exact Hm.
Qed.

(** [H_(γ+δ) = H_γ ∘ H_δ] *)
Lemma hardy_vcat g x n k m : hardy x n k -> hardy g k m -> hardy (vcat g x) n m.
Proof.
  intro H. induction H as [n|x y n k Hxy _ IH]; intro Hg.
  - rewrite vcat_Z. exact Hg.
  - apply hardy_P with (vcat g y); [apply Pn_vcat; exact Hxy | apply IH; exact Hg].
Qed.

Lemma hardy_vcat_inv g x n m : hardy (vcat g x) n m -> exists k, hardy x n k /\ hardy g k m.
Proof.
  intro H. destruct (hardy_exists x n) as [k Hk].
  destruct (hardy_exists g k) as [m' Hm'].
  exists k. split; [exact Hk|].
  rewrite (hardy_fun _ _ _ H m' (hardy_vcat g x n k m' Hk Hm')). exact Hm'.
Qed.

(** [H_α] is strictly increasing, and monotone along [≼_n]. *)
Theorem hardy_mono a :
  (forall n m m', hardy a n m -> hardy a (S n) m' -> m < m') /\
  (forall n b mb ma, reach n b a -> hardy b n mb -> hardy a n ma -> mb <= ma).
Proof.
  induction a as [a IH] using VF_ind.
  assert (Hreach : forall n b mb ma, reach n b a -> hardy b n mb -> hardy a n ma -> mb <= ma).
  { intros n b mb ma Hr Hb Ha.
    destruct Hr as [a|a a1 b Ha1 Hr].
    - rewrite (hardy_fun _ _ _ Hb ma Ha). apply le_n.
    - destruct (hardy_exists a1 n) as [m1 Hm1].
      destruct (IH a1 (Pn_lt n _ _ Ha1)) as [IH1 IH2].
      apply Nat.le_trans with m1; [exact (IH2 n b mb m1 Hr Hb Hm1)|].
      apply Nat.lt_le_incl. apply (IH1 n m1 ma Hm1). apply hardy_P_inv with a; assumption. }
  split; [|exact Hreach].
  intros n m m' Hm Hm'.
  destruct a as [|e x].
  - inversion Hm as [n0|a0 b0 n0 m0 Hb _]; subst; [|exfalso; eapply Pn_Z; eassumption].
    inversion Hm' as [n0|a0 b0 n0 m0 Hb _]; subst; [lia|exfalso; eapply Pn_Z; eassumption].
  - destruct (Pn_exists n (V e x)) as [a1 Ha1]; [discriminate|].
    destruct (Pn_exists (S n) (V e x)) as [a2 Ha2]; [discriminate|].
    apply (hardy_P_inv _ _ _ _ Ha1) in Hm.
    apply (hardy_P_inv _ _ _ _ Ha2) in Hm'.
    destruct (hardy_exists a2 (S n)) as [k Hk].
    destruct (IH a2 (Pn_lt _ _ _ Ha2)) as [IH1 IH2].
    apply Nat.le_lt_trans with k.
    + apply (IH2 (S n) a1 m k); [apply Pn_bachmann with (V e x); assumption | exact Hm | exact Hk].
    + apply (IH1 (S n) k m'); assumption.
Qed.

Lemma hardy_mono_arg a n n' m m' : n <= n' -> hardy a n m -> hardy a n' m' -> m <= m'.
Proof.
  intros Hn. revert m'. induction Hn as [|n' Hn IH]; intros m' Hm Hm'.
  - rewrite (hardy_fun _ _ _ Hm m' Hm'). apply le_n.
  - destruct (hardy_exists a n') as [k Hk].
    apply Nat.le_trans with k; [apply IH; assumption|].
    apply Nat.lt_le_incl. apply (proj1 (hardy_mono a) n' k m'); assumption.
Qed.

Lemma hardy_mono_reach n b a mb ma : reach n b a -> hardy b n mb -> hardy a n ma -> mb <= ma.
Proof. apply (proj2 (hardy_mono a)). Qed.

(** ** Domination: [α < β] gives [α ≼_n β] for large [n] *)

Lemma VF_eq_dec (a b:VForm) : {a = b} + {a <> b}.
Proof. decide equality. Qed.

Local Open Scope ord_scope.

Lemma VF_lt_irrefl (a:VForm) : ~ (a ◃ a).
Proof. intro H. exact (ord_lt_irreflexive (sz a) H). Qed.

Lemma VF_not_lt_Z (a:VForm) : ~ (a ◃ Z).
Proof.
  intro H. apply (ord_lt_irreflexive 0).
  apply ord_le_lt_trans with (sz a); [apply zero_least | exact H].
Qed.

(** Normal forms are compared by their leading exponents. *)
Lemma normal_lead_lt f y g : VF_normal (V f y) -> f ◃ g -> V f y ◃ V g Z.
Proof.
  revert f. induction y as [|h _ y IH]; intros f Hn Hfg.
  - apply exp_lt. exact Hfg.
  - destruct Hn as [Hf [Hy Hhf]].
    rewrite V_eq, VZ_eq. rewrite <- VZ_eq.
    apply below_exp_add.
    + rewrite <- VZ_eq. apply exp_lt. exact Hfg.
    + rewrite <- VZ_eq. apply IH; [exact Hy|].
      eapply ord_le_lt_trans; [exact Hhf | exact Hfg].
Qed.

Lemma VF_trichotomy (a b:VForm) : VF_normal a -> VF_normal b ->
  a ◃ b \/ a = b \/ b ◃ a.
Proof.
  intros Ha Hb. generalize (VF_compare_correct a b).
  destruct (VF_compare a b); intro H.
  - left; exact H.
  - right; left. apply V_normal_forms_unique; assumption.
  - right; right; exact H.
Qed.

Lemma VF_lt_of_le_neq (a b:VForm) : VF_normal a -> VF_normal b ->
  a ⊴ b -> a <> b -> a ◃ b.
Proof.
  intros Ha Hb Hle Hne.
  destruct (VF_trichotomy a b Ha Hb) as [H|[H|H]].
  - exact H.
  - contradiction.
  - exfalso. apply (ord_lt_irreflexive (sz a)). eapply ord_le_lt_trans; [exact Hle | exact H].
Qed.

Local Close Scope ord_scope.

(** A normal form [ω^g + x] is [ω^g·(k+1) + x'] with [x' < ω^g]. *)
Lemma normal_split g x : VF_normal (V g x) ->
  exists k x', V g x = vrep (S k) g x' /\ (x' ◃ V g Z)%ord /\ VF_normal x'.
Proof.
  induction x as [|h _ x IH]; intro Hn.
  - exists 0, Z. split; [reflexivity|]. split; [|exact I].
    rewrite VZ_eq. apply expOrd_nonzero.
  - destruct Hn as [Hg [Hx Hhg]].
    destruct (VF_eq_dec h g) as [->|Hne].
    + destruct (IH Hx) as [k [x' [Heq [Hlt Hn']]]].
      exists (S k), x'. split; [rewrite Heq; reflexivity|]. split; assumption.
    + exists 0, (V h x). split; [reflexivity|]. split; [|exact Hx].
      apply normal_lead_lt; [exact Hx|].
      apply VF_lt_of_le_neq; [exact (proj1 Hx) | exact Hg | exact Hhg | exact Hne].
Qed.

Lemma VF_size_vrep k g x : k + VF_size x <= VF_size (vrep k g x).
Proof. induction k as [|k IH]; simpl; lia. Qed.

(** Everything below [ω^g·(j+1) + P_n(ω^g)] down to [ω^g·j] is reached. *)
Lemma reach_below_exp n j g y x : Pn n (V g Z) y -> reach n x y -> reach n x (vrep j g y).
Proof.
  intros Hy Hx. destruct j as [|j].
  - exact Hx.
  - eapply reach_trans; [|apply (reach_vrep_le n 1 (S j) g y); lia].
    apply reach_step with y; assumption.
Qed.

Theorem reach_of_lt : forall b a n, VF_normal a -> VF_normal b -> (a ◃ b)%ord ->
  VF_size a < n -> reach n a b.
Proof.
  induction b as [b IH] using VF_ind.
  intros a n Ha Hb Hab Hn.
  destruct a as [|g x]; [apply reach_Z|].
  destruct b as [|f y]; [exfalso; exact (VF_not_lt_Z _ Hab)|].
  pose proof Ha as Ha'. pose proof Hb as Hb'.
  destruct Ha' as [Hg [Hx _]]. destruct Hb' as [Hf [Hy _]].
  destruct (VF_trichotomy g f Hg Hf) as [Hgf|[->|Hfg]].
  - (* [g < f]: descend to [ω^f], then to [ω^g·(k+1) + x'] *)
    destruct (normal_split g x Ha) as [k [x' [Heq [Hx'lt Hx']]]].
    assert (Hsz := VF_size_vrep (S k) g x'). rewrite <- Heq in Hsz.
    assert (Hrg : reach n g f).
    { apply IH; auto.
      - apply VF_denote_shrink1.
      - simpl in Hn. lia. }
    destruct Hrg as [g|f f3 g Hf3 Hgf3].
    { exfalso. exact (VF_lt_irrefl _ Hgf). }
    destruct (Pn_exists_exp n g) as [yg Hyg].
    assert (Hx'r : reach n x' (V g Z)).
    { apply IH; auto.
      - eapply ord_lt_le_trans; [apply exp_lt; exact Hgf | apply exp_le_V].
      - split; [exact Hg | split; exact I].
      - lia. }
    destruct (reach_inv _ _ _ _ Hx'r Hyg) as [Heq'|Hx'yg].
    { exfalso. rewrite Heq' in Hx'lt. exact (VF_lt_irrefl _ Hx'lt). }
    eapply reach_trans; [|apply (reach_prefix n (V f Z) y)].
    eapply reach_trans; [|apply (reach_vrep_exp n g f3 ltac:(lia) Hgf3 yg f Hyg Hf3)].
    rewrite Heq.
    replace (n-1) with (S k + (n - 1 - S k)) by lia.
    rewrite vrep_add, (vrep_vcat (S k) g x'), (vrep_vcat (S k) g (vrep _ g yg)).
    apply reach_vcat. apply reach_below_exp; assumption.
  - (* same leading exponent: compare the tails *)
    assert (Hxy : (x ◃ y)%ord).
    { destruct (V_decide_order x y) as [H|H]; [exact H|].
      exfalso. apply (ord_lt_irreflexive (sz (V f x))).
      eapply ord_lt_le_trans; [exact Hab|].
      rewrite !V_eq. apply addOrd_monotone; [reflexivity | exact H]. }
    apply (reach_vcat n (V f Z)). apply IH; auto.
    + apply VF_denote_shrink2. exact Hb.
    + simpl in Hn. lia.
  - exfalso. apply (ord_lt_irreflexive (sz (V g x))).
    eapply ord_lt_le_trans; [exact Hab|].
    eapply ord_le_trans; [apply ord_lt_le; apply normal_lead_lt; [exact Hb | exact Hfg]|].
    apply exp_le_V.
Qed.

Theorem hardy_dominated a b n ma mb : VF_normal a -> VF_normal b -> (a ◃ b)%ord ->
  VF_size a < n -> hardy a n ma -> hardy b n mb -> ma <= mb.
Proof.
  intros Ha Hb Hab Hn. apply hardy_mono_reach. apply reach_of_lt; assumption.
Qed.

(** ** The strict relation [β ≺_n α]

    These are the facts about heights used by cut elimination: [≺_n] is
    compatible with sums ([olt_vcat]) and with [ω^-] ([olt_exp]), and
    [ω^α] lies above [ω^(P_n α)·2] ([olt_two]). *)

Definition olt n b a := exists a1, Pn n a a1 /\ reach n b a1.

Lemma olt_reach n b a : olt n b a -> reach n b a.
Proof.
  intros [a1 [H1 H2]]. eapply reach_trans; [exact H2 | apply reach_one; exact H1].
Qed.

Lemma olt_nonzero n b a : olt n b a -> a <> Z.
Proof. intros [a1 [H _]]. exact (Pn_nonzero n a a1 H). Qed.

Lemma olt_reach_trans n b a a' : olt n b a -> reach n a a' -> olt n b a'.
Proof.
  intros H1 H2. destruct H2 as [a'|a' a'1 a Hstep Hr].
  - exact H1.
  - exists a'1. split; [exact Hstep|]. eapply reach_trans; [apply olt_reach; exact H1 | exact Hr].
Qed.

Lemma reach_olt_trans n c b a : reach n c b -> olt n b a -> olt n c a.
Proof.
  intros H1 [a1 [H2 H3]]. exists a1. split; [exact H2 | eapply reach_trans; eassumption].
Qed.

Lemma Pn_reach_mono n m a a1 a2 : n <= m -> Pn n a a1 -> Pn m a a2 -> reach m a1 a2.
Proof.
  intro Hnm. revert a2. induction Hnm as [|m Hnm IH]; intros a2 H1 H2.
  - rewrite (Pn_fun n a a1 H1 a2 H2). apply reach_refl.
  - destruct (Pn_exists m a (Pn_nonzero n a a1 H1)) as [a3 H3].
    eapply reach_trans; [apply reach_S; exact (IH a3 H1 H3)|].
    apply Pn_bachmann with a; assumption.
Qed.

Lemma olt_mono n m b a : n <= m -> olt n b a -> olt m b a.
Proof.
  intros Hnm [a1 [H1 H2]].
  destruct (Pn_exists m a (Pn_nonzero n a a1 H1)) as [a2 H3].
  exists a2. split; [exact H3|].
  eapply reach_trans; [apply (reach_mono n m); [exact Hnm | exact H2]|].
  apply Pn_reach_mono with n a; assumption.
Qed.

Lemma olt_vcat n g b a : olt n b a -> olt n (vcat g b) (vcat g a).
Proof.
  intros [a1 [H1 H2]]. exists (vcat g a1).
  split; [apply Pn_vcat; exact H1 | apply reach_vcat; exact H2].
Qed.

Lemma olt_Z n a : a <> Z -> olt n Z a.
Proof.
  intro Ha. destruct (Pn_exists n a Ha) as [a1 H]. exists a1. split; [exact H | apply reach_Z].
Qed.

Lemma olt_vcat_r n a b : b <> Z -> olt n a (vcat a b).
Proof.
  intro Hb. rewrite <- (vcat_Z a) at 1. apply olt_vcat. apply olt_Z. exact Hb.
Qed.

Lemma olt_exp n b a : 2 <= n -> olt n b a -> olt n (V b Z) (V a Z).
Proof.
  intros Hn [a1 [H1 H2]].
  destruct (Pn_exists_exp n a1) as [y Hy].
  exists (vrep (n-1) a1 y). split; [apply Pn_exp; assumption|].
  eapply reach_trans; [apply reach_exp_mono; [exact Hn | exact H2]|].
  apply (reach_vrep_le n 1 (n-1) a1 y). lia.
Qed.

Lemma olt_two n a a1 : 3 <= n -> Pn n a a1 -> olt n (vcat (V a1 Z) (V a1 Z)) (V a Z).
Proof.
  intros Hn H1. destruct (Pn_exists_exp n a1) as [y Hy].
  exists (vrep (n-1) a1 y). split; [apply Pn_exp; assumption|].
  apply (reach_vrep_le n 2 (n-1) a1 y). lia.
Qed.

Lemma olt_hardy n b a hb ha : olt n b a -> hardy b n hb -> hardy a n ha -> hb <= ha.
Proof. intro H. apply hardy_mono_reach. apply olt_reach. exact H. Qed.

(** [H_δ(x) ≥ x], so a summand on the left only increases [H]. *)
Lemma hardy_vcat_ge g x n h hx : hardy (vcat g x) n h -> hardy x n hx -> hx <= h.
Proof.
  intros H Hx. destruct (hardy_vcat_inv g x n h H) as [k [Hk Hg]].
  rewrite (hardy_fun _ _ _ Hx k Hk). apply hardy_ge with g. exact Hg.
Qed.

(** [H_α(n) ≤ H_(ω^α)(n)] *)
Lemma hardy_exp_ge a : forall n h h', 2 <= n -> hardy a n h -> hardy (V a Z) n h' -> h <= h'.
Proof.
  induction a as [a IH] using VF_ind. intros n h h' Hn Ha Ha'.
  destruct a as [|e x].
  - inversion Ha as [n0|a0 b0 n0 m0 Hb _]; subst; [|exfalso; eapply Pn_Z; eassumption].
    eapply hardy_ge. exact Ha'.
  - destruct (Pn_exists n (V e x)) as [a1 Ha1]; [discriminate|].
    destruct (Pn_exists_exp n a1) as [y Hy].
    apply (hardy_P_inv _ _ _ _ Ha1) in Ha.
    apply (hardy_P_inv _ _ _ _ (Pn_exp n _ _ _ Ha1 Hy)) in Ha'.
    destruct (hardy_exists (V a1 Z) (S n)) as [k Hk].
    apply Nat.le_trans with k.
    + apply (IH a1 (Pn_lt _ _ _ Ha1) (S n)); [lia | exact Ha | exact Hk].
    + (* [ω^a1·(n-1) + y] has [ω^a1] as a leading summand *)
      replace (n-1) with (S (n-2)) in Ha' by lia.
      change (vrep (S (n-2)) a1 y) with (vcat (V a1 Z) (vrep (n-2) a1 y)) in Ha'.
      destruct (hardy_vcat_inv _ _ _ _ Ha') as [k' [Hk' Hg]].
      apply (hardy_mono_arg (V a1 Z) (S n) k' k h'); [eapply hardy_ge; exact Hk' | exact Hk | exact Hg].
Qed.
