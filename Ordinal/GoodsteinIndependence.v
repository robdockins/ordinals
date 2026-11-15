From Stdlib Require Import Arith.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Notation.VNotation.
From Ordinal Require Import GoodsteinSequences.
From Ordinal Require Import PeanoArith.
From Ordinal Require Import Hardy.
From Ordinal Require Import Cichon.
From Ordinal Require Import OmegaLogic.
From Ordinal Require Import Embedding.

Local Open Scope nat_scope.

Local Opaque hbn_decompose.

(** * Goodstein's theorem is not provable in Peano arithmetic

    If PA proves [∀x ∃y θ(x,y)] with [θ] bounded, then embedding the
    proof in the ω-logic ([embed]), inverting the universal, eliminating
    the cuts ([od_elim_all]) and bounding the witness ([od_witness])
    give a fixed [α < ε₀] with a witness [y < H_α(x+1)] for every large
    [x] ([PA_sigma1_bound]).  Goodstein's sequence from [x] takes
    [H_(o(x))(3) - 3] steps ([Cichon]), and [o(x)] can be made larger
    than [α] while [x] stays small enough that [H_(o(x))(3)] exceeds
    [H_α(x+1) + 3] ([goodstein_diagonal]).  So no bounded [θ] whose truth
    at [(x,y)] implies that the sequence from [x] reaches zero within [y]
    steps has [∀x ∃y θ] provable in PA ([goodstein_unprovable]). *)

(** ** The provable Σ₁ sentences are bounded below ε₀ *)

Lemma otower_normal k a : VF_normal a -> VF_normal (otower k a).
Proof.
  revert a. induction k as [|k IH]; intros a Ha; simpl; [exact Ha|].
  apply IH. split; [exact Ha | split; exact I].
Qed.

Lemma W_normal k : VF_normal (W k).
Proof. apply normal_vrep; [exact e3_normal | exact I | exact I]. Qed.

Lemma sat_inst2 θ x m :
  sat ρ0 (sub1 (fsubst (up (inst1 (num x))) (fsubst (up (up (nsub (fun _ => 0)))) θ)) (num m)) <->
  sat (scons m (scons x ρ0)) θ.
Proof.
  rewrite sat_sub1_num, !sat_fsubst. apply sat_ext.
  intros [|[|j]]; simpl; [reflexivity | | reflexivity].
  rewrite teval_shift. apply teval_num.
Qed.

Theorem PA_sigma1_bound θ : PA [] (All (Ex θ)) -> isD θ = true -> isD (Ex θ) = false ->
  exists α N, VF_normal α /\ forall x h, N <= x -> hardy α (S x) h ->
    exists y, y < h /\ sat (scons y (scons x ρ0)) θ.
Proof.
  intros Hprov HD HE. destruct (embed _ _ _ Hprov) as [k [ρ [N [HN Hemb]]]].
  exists (otower ρ (W k)), N. split; [apply otower_normal; apply W_normal|].
  intros x h Hx Hh.
  set (σ := fun _ : nat => 0).
  assert (H0 := Hemb (S x) σ ltac:(lia) ltac:(intro i; unfold σ; lia)).
  unfold seqof in H0. simpl map in H0.
  set (θ1 := fsubst (up (up (nsub σ))) θ) in *.
  assert (H1 : OD (S x) ρ (W k) [inst true (Ex θ1) x]).
  { replace (S x) with (Nat.max (S x) (S x)) by lia.
    apply (od_inv_univ _ _ _ _ H0 (true, All (Ex θ1)) true (Ex θ1) []); [reflexivity | reflexivity |].
    intros y [<-|[]]. left. reflexivity. }
  assert (H2 : OD (S x) 1 (otower ρ (W k)) [inst true (Ex θ1) x]).
  { apply od_elim_all; [|lia]. apply od_rank with ρ; [exact H1 | lia]. }
  unfold inst in H2. change (sub1 (Ex θ1) (num x)) with (Ex (fsubst (up (inst1 (num x))) θ1)) in H2.
  assert (HD2 : isD (fsubst (up (inst1 (num x))) θ1) = true).
  { unfold θ1. rewrite !isD_fsubst_eq. exact HD. }
  assert (HE2 : isD (Ex (fsubst (up (inst1 (num x))) θ1)) = false).
  { change (isD (fsubst (inst1 (num x)) (Ex θ1)) = false). unfold θ1.
    change (Ex (fsubst (up (up (nsub σ))) θ)) with (fsubst (up (nsub σ)) (Ex θ)).
    rewrite !isD_fsubst_eq. exact HE. }
  destruct (od_witness _ _ _ h H2 HD2 HE2 Hh) as [m [Hm Hsat]].
  exists m. split; [exact Hm|]. apply sat_inst2. exact Hsat.
Qed.

(** ** Slow growth below fast growth

    [G_b(α)] replaces [ω] by [b] in [α]; for [b ≤ n], [H_α(n) ≥ n + G_b(α)],
    since each step [P_n] lowers [G_b] by at most one. *)

Fixpoint vval (b:nat) (a:VForm) : nat :=
  match a with Z => 0 | V e x => b ^ vval b e + vval b x end.

Lemma vval_vrep b k e x : vval b (vrep k e x) = k * b ^ vval b e + vval b x.
Proof. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma vval_Pn b n a a' : 1 <= b -> b <= n -> Pn n a a' -> vval b a <= vval b a' + 1.
Proof.
  intros Hb Hbn H. induction H as [|e x y H IH|e e' y H1 IH1 H2 IH2].
  - simpl. lia.
  - simpl. lia.
  - simpl in *. rewrite vval_vrep.
    assert (Hp : b ^ vval b e <= b ^ (vval b e' + 1)) by (apply Nat.pow_le_mono_r; lia).
    rewrite Nat.pow_add_r, Nat.pow_1_r in Hp.
    assert (b ^ vval b e' * b <= (n - 1) * b ^ vval b e' + b ^ vval b e') by nia.
    lia.
Qed.

Lemma hardy_vval b a n h : 1 <= b -> b <= n -> hardy a n h -> n + vval b a <= h.
Proof.
  intros Hb Hbn H. induction H as [n|a a1 n h Ha1 _ IH].
  - simpl. lia.
  - assert (IH' := IH ltac:(lia)). assert (Hv := vval_Pn b n a a1 Hb Hbn Ha1). lia.
Qed.

Lemma VF_size_vval a : VF_size a <= vval 2 a.
Proof.
  induction a as [|e IHe x IHx]; simpl; [lia|].
  assert (vval 2 e + 1 <= 2 ^ vval 2 e) by apply Embedding.pow2_ge. lia.
Qed.

(** ** Hereditary base-2 notation for powers of two *)

Lemma hbn_vval h : vval 2 (hbn_vf h) = N.to_nat (hbn_interp 2 h).
Proof.
  induction h as [|e IHe n x IHx]; simpl; [reflexivity|].
  rewrite vval_vrep, IHe, IHx.
  rewrite N2Nat.inj_add, N2Nat.inj_mul, N2Nat.inj_pow.
  replace (N.to_nat 2) with 2 by reflexivity. ring.
Qed.

Lemma ord2_vval t : vval 2 (ord2 t) = N.to_nat t.
Proof. unfold ord2. rewrite hbn_vval, hbn_decompose_correct. reflexivity. Qed.

Lemma ord2_pow t : ord2 (2 ^ t)%N = V (ord2 t) Z.
Proof.
  unfold ord2.
  rewrite (hbn_decompose_unique 2 (plus2_base 0) (2 ^ t)%N
             (HBN_Term (hbn_decompose 2 (plus2_base 0) t) 1 HBN_Z)).
  - reflexivity.
  - constructor; [apply hbn_decompose_proper | lia | constructor | constructor].
  - simpl. rewrite hbn_decompose_correct. lia.
Qed.

Lemma ord2_pow_succ t : (0 < t)%N -> ord2 (2 ^ t + 1)%N = V (ord2 t) (V Z Z).
Proof.
  intro Ht. unfold ord2.
  rewrite (hbn_decompose_unique 2 (plus2_base 0) (2 ^ t + 1)%N
             (HBN_Term (hbn_decompose 2 (plus2_base 0) t) 1 (HBN_Term HBN_Z 1 HBN_Z))).
  - reflexivity.
  - constructor; [apply hbn_decompose_proper | lia | | ].
    + constructor; [constructor | lia | constructor | constructor].
    + constructor. destruct (hbn_decompose 2 (plus2_base 0) t) eqn:E; [|constructor].
      apply hbn_decompose_zero in E. lia.
  - simpl. rewrite hbn_decompose_correct. lia.
Qed.

(** The tower [1, 2, 2^2, ...]; its notations are [ω^ω^...]. *)
Fixpoint tw (j:nat) : N := match j with O => 1%N | S j => (2 ^ tw j)%N end.

Lemma ord2_tw j : ord2 (tw j) = V (match j with O => Z | S j => ord2 (tw j) end) Z.
Proof.
  destruct j as [|j]; simpl.
  - replace 1%N with (2 ^ 0)%N by reflexivity. rewrite ord2_pow.
    unfold ord2. replace (hbn_decompose 2 (plus2_base 0) 0%N) with HBN_Z; [reflexivity|].
    symmetry. apply hbn_decompose_unique; [constructor | reflexivity].
  - apply ord2_pow.
Qed.

Lemma ord2_tw_normal j : VF_normal (ord2 (tw j)).
Proof.
  induction j as [|j IH]; rewrite ord2_tw; [simpl; auto|].
  split; [exact IH | split; exact I].
Qed.

Lemma tw_pos j : (0 < tw j)%N.
Proof. destruct j; simpl; [lia|]. apply N.neq_0_lt_0. apply N.pow_nonzero. lia. Qed.

Lemma tw_ge j : j <= N.to_nat (tw j).
Proof.
  induction j as [|j IH]; simpl; [lia|].
  rewrite N2Nat.inj_pow. change (N.to_nat 2) with 2.
  assert (H := Embedding.pow2_ge (N.to_nat (tw j))). lia.
Qed.

Local Open Scope ord_scope.

Lemma ord2_tw_lt_S j : ord2 (tw j) ◃ ord2 (tw (S j)).
Proof. rewrite (ord2_tw (S j)). apply exp_shrink. Qed.

Lemma ord2_tw_mono j j' : (j <= j')%nat -> ord2 (tw j) ⊴ ord2 (tw j').
Proof.
  intro H. induction H as [|j' _ IH]; [reflexivity|].
  eapply ord_le_trans; [exact IH | apply ord_lt_le; apply ord2_tw_lt_S].
Qed.

(** The towers are cofinal in the normal forms. *)
Lemma tw_cofinal a : VF_normal a -> exists j, a ◃ ord2 (tw j).
Proof.
  induction a as [|e IHe x _]; intro Ha.
  - exists 0%nat. rewrite ord2_tw. apply Z_lt_V.
  - destruct Ha as [He [Hx Hlead]]. destruct (IHe He) as [j Hj].
    exists (S j). rewrite (ord2_tw (S j)). apply normal_lead_lt; [split; auto | exact Hj].
Qed.

Lemma e1_le_V a x : e1 ⊴ V a x.
Proof.
  eapply ord_le_trans; [|apply exp_le_V].
  unfold e1. rewrite !VZ_eq. apply expOrd_monotone. apply zero_least.
Qed.

Local Close Scope ord_scope.

(** ** The diagonal argument *)

Lemma hardy_lt_arg a n n' m m' : n < n' -> hardy a n m -> hardy a n' m' -> m < m'.
Proof.
  intros Hn. revert m'. induction Hn as [|n' Hn IH]; intros m' Hm Hm'.
  - apply (proj1 (hardy_mono a) n m m'); assumption.
  - destruct (hardy_exists a n') as [k Hk].
    apply Nat.lt_trans with k; [apply IH; assumption|].
    apply (proj1 (hardy_mono a) n' k m'); assumption.
Qed.

Lemma hardy_add_arg a n d m m' : hardy a n m -> hardy a (n + d) m' -> m + d <= m'.
Proof.
  revert m'. induction d as [|d IH]; intros m' Hm Hm'.
  - rewrite Nat.add_0_r in *. rewrite (hardy_fun _ _ _ Hm _ Hm'). lia.
  - destruct (hardy_exists a (n + d)) as [k Hk].
    assert (IH' := IH k Hm Hk).
    assert (k < m') by (apply (hardy_lt_arg a (n + d) (n + S d)); [lia | exact Hk | exact Hm']).
    lia.
Qed.

Lemma hardy_omega u : 1 <= u -> hardy (V e1 Z) u (2 * u).
Proof. intro Hu. replace (2 * u) with (2 ^ 1 * u) by reflexivity. apply (hardy_omega_k 1). exact Hu. Qed.

Theorem goodstein_diagonal α M : VF_normal α -> exists x, M <= x /\
  forall h h', hardy α (S x) h -> hardy (ord2 (N.of_nat x)) 3 h' -> h + 3 < h'.
Proof.
  intro Hα. destruct (tw_cofinal α Hα) as [j0 Hj0].
  set (j := Nat.max j0 (M + VF_size α)).
  set (t := tw j). set (τ := ord2 t).
  assert (Hτn : VF_normal τ) by apply ord2_tw_normal.
  assert (Hατ : (α ◃ τ)%ord).
  { eapply ord_lt_le_trans; [exact Hj0 | apply ord2_tw_mono; lia]. }
  assert (Ht : N.to_nat t >= M + VF_size α) by (assert (H := tw_ge j); unfold t; lia).
  assert (Htv : vval 2 τ = N.to_nat t) by apply ord2_vval.
  assert (Hτsz : VF_size τ <= N.to_nat t) by (rewrite <- Htv; apply VF_size_vval).
  set (z := (2 ^ t)%N). set (x := (2 ^ (z + 1))%N).
  assert (Hζ : ord2 z = V τ Z) by apply ord2_pow.
  assert (Hx : ord2 x = V (V τ (V Z Z)) Z).
  { unfold x, z. rewrite ord2_pow, ord2_pow_succ; [reflexivity | apply tw_pos]. }
  assert (Hzn : N.to_nat z = 2 ^ N.to_nat t) by (unfold z; rewrite N2Nat.inj_pow; reflexivity).
  assert (Hxn : N.to_nat x = 2 ^ (2 ^ N.to_nat t + 1)).
  { unfold x. rewrite N2Nat.inj_pow, N2Nat.inj_add, Hzn. reflexivity. }
  assert (Hpow : N.to_nat t + 1 <= 2 ^ N.to_nat t) by apply Embedding.pow2_ge.
  assert (Hpow2 : 2 ^ N.to_nat t + 1 <= 2 ^ (2 ^ N.to_nat t)) by apply Embedding.pow2_ge.
  assert (Hpow3 : 2 ^ (2 ^ N.to_nat t + 1) = 2 * 2 ^ (2 ^ N.to_nat t)) by (rewrite Nat.pow_add_r; simpl; lia).
  exists (N.to_nat x). split; [rewrite Hxn; lia|].
  intros h h' Hh Hh'. rewrite N2Nat.id, Hx in Hh'.
  set (ζ0 := V τ Z).
  destruct (Pn_exists_exp 3 ζ0) as [y Hy].
  assert (Hstep : Pn 3 (V (V τ (V Z Z)) Z) (vrep 2 ζ0 y)).
  { apply (Pn_exp 3 (V τ (V Z Z)) ζ0 y); [apply Pn_tail; apply Pn_one | exact Hy]. }
  apply (hardy_P_inv _ _ _ _ Hstep) in Hh'.
  change (vrep 2 ζ0 y) with (vcat (V ζ0 Z) (vcat (V ζ0 Z) y)) in Hh'.
  destruct (hardy_vcat_inv _ _ _ _ Hh') as [b [Hb Hh'']].
  destruct (hardy_vcat_inv _ _ _ _ Hb) as [a [Ha Hb']].
  assert (Ha4 : 4 < a).
  { apply (hardy_gt y 4 a Ha). intro Hz. subst y. inversion Hy. }
  destruct (hardy_exists (V ζ0 Z) 4) as [u Hu].
  assert (Hub : u < b) by (apply (hardy_lt_arg (V ζ0 Z) 4 a); assumption).
  assert (Hu_ge : 4 + 2 ^ (2 ^ N.to_nat t) <= u).
  { assert (Hv := hardy_vval 2 (V ζ0 Z) 4 u ltac:(lia) ltac:(lia) Hu).
    unfold ζ0 in Hv. simpl vval in Hv. rewrite Htv, !Nat.add_0_r in Hv. lia. }
  (* the chain [H_α(x+1) + 3 ≤ H_α(2u) ≤ H_(ω^τ)(2u) = H_(ω^τ+ω)(u) ≤ H_(ω^ζ0)(u) < h'] *)
  destruct (hardy_exists α (S (N.to_nat x) + 3)) as [h3 Hh3].
  assert (E1 : h + 3 <= h3) by (apply (hardy_add_arg α (S (N.to_nat x)) 3); assumption).
  destruct (hardy_exists α (2 * u)) as [h4 Hh4].
  assert (E2 : h3 <= h4).
  { apply (hardy_mono_arg α (S (N.to_nat x) + 3) (2 * u)); [rewrite Hxn; lia | exact Hh3 | exact Hh4]. }
  destruct (hardy_exists (V τ Z) (2 * u)) as [h5 Hh5].
  assert (E3 : h4 <= h5).
  { apply (hardy_dominated α (V τ Z) (2 * u)); [exact Hα | split; [exact Hτn | split; exact I] | | lia | exact Hh4 | exact Hh5].
    eapply ord_lt_trans; [exact Hατ | apply exp_shrink]. }
  assert (Hc : hardy (V τ (V e1 Z)) u h5).
  { change (V τ (V e1 Z)) with (vcat (V τ Z) (V e1 Z)).
    apply hardy_vcat with (2 * u); [apply hardy_omega; lia | exact Hh5]. }
  destruct (hardy_exists (V ζ0 Z) u) as [h6 Hh6].
  assert (E4 : h5 <= h6).
  { apply (hardy_dominated (V τ (V e1 Z)) (V ζ0 Z) u); [| | | | exact Hc | exact Hh6].
    - split; [exact Hτn|]. split; [split; [exact e1_normal | split; exact I]|].
      unfold τ, t. rewrite ord2_tw. apply e1_le_V.
    - split; [split; [exact Hτn | split; exact I] | split; exact I].
    - apply normal_lead_lt; [|apply exp_shrink].
      split; [exact Hτn|]. split; [split; [exact e1_normal | split; exact I]|].
      unfold τ, t. rewrite ord2_tw. apply e1_le_V.
    - simpl. lia. }
  assert (E5 : h6 < h') by (apply (hardy_lt_arg (V ζ0 Z) u b); assumption).
  lia.
Qed.

(** ** Unprovability *)

Theorem goodstein_unprovable θ :
  isD θ = true -> isD (Ex θ) = false ->
  (forall x y, sat (scons y (scons x ρ0)) θ ->
     exists k, k <= y /\ goodstein_sequence (N.of_nat x) (N.of_nat k) = 0%N) ->
  ~ PA [] (All (Ex θ)).
Proof.
  intros HD HE Hsound Hprov.
  destruct (PA_sigma1_bound θ Hprov HD HE) as [α [N [Hα Hbound]]].
  destruct (goodstein_diagonal α N Hα) as [x [Hx Hdiag]].
  destruct (hardy_exists α (S x)) as [h Hh].
  destruct (hardy_exists (ord2 (N.of_nat x)) 3) as [h' Hh'].
  destruct (Hbound x h Hx Hh) as [y [Hy Hsat]].
  destruct (Hsound x y Hsat) as [k [Hk Hg]].
  assert (Hlow := goodstein_length_lower (N.of_nat x) k h' Hg Hh').
  assert (Hd := Hdiag h h' Hh Hh'). lia.
Qed.
