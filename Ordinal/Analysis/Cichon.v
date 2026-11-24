From Stdlib Require Import Arith.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.

From Ordinal Require Import Notation.VNotation.
From Ordinal Require Import GoodsteinSequences.
From Ordinal Require Import Analysis.Hardy.

Local Open Scope nat_scope.

Local Opaque hbn_decompose.

(** * Goodstein sequences and the Hardy hierarchy (Cichon)

    Reading a hereditary base-[b] numeral as an ordinal, by replacing
    the base with [ω], does not depend on [b], so changing the base is
    the identity on ordinals.  Subtracting one in base [b] is the
    predecessor [P_b] ([hbn_dec_Pn]): the numeral

      b^e - 1 = (b-1)·b^(e-1) + (b^(e-1) - 1)

    is [P_b(ω^e) = ω^(P_b e)·(b-1) + P_b(ω^(P_b e))].  The [i]-th step of
    the Goodstein sequence works in base [i+2] and subtracts one in base
    [i+3], so the ordinals [α_i] of the sequence satisfy
    [α_(i+1) = P_(i+3)(α_i)], the steps of the Hardy function
    [H_(α_0)(3)].  Hence the sequence starting at [m] first reaches zero at
    step [k] exactly when [H_(o(m))(3) = k + 3], where [o(m)] is the
    ordinal of [m] in hereditary base 2 ([cichon]). *)

Fixpoint hbn_vf (h:HBN) : VForm :=
  match h with
  | HBN_Z => Z
  | HBN_Term e n x => vrep (N.to_nat n) (hbn_vf e) (hbn_vf x)
  end.

(** All multiplicities are positive. *)
Fixpoint hbn_pos (h:HBN) : Prop :=
  match h with
  | HBN_Z => True
  | HBN_Term e n x => (0 < n)%N /\ hbn_pos e /\ hbn_pos x
  end.

Lemma hbn_proper_pos base h : hbn_proper base h -> hbn_pos h.
Proof.
  intro H. induction H as [|e n x _ IHe Hn _ IHx _]; simpl; auto.
  split; [lia | auto].
Qed.

Lemma hbn_vf_Z h : hbn_pos h -> hbn_vf h = Z -> h = HBN_Z.
Proof.
  destruct h as [|e n x]; [reflexivity|]. simpl. intros [Hn _] H.
  destruct (N.to_nat n) eqn:E; [lia | discriminate].
Qed.

Scheme hbn_dec_mut := Induction for hbn_dec Sort Prop
  with hbn_exp_dec_mut := Induction for hbn_exp_dec Sort Prop.
Combined Scheme hbn_dec_comb from hbn_dec_mut, hbn_exp_dec_mut.

Lemma hbn_term_vf e n x : hbn_vf (hbn_term e n x) = vrep (N.to_nat n) (hbn_vf e) (hbn_vf x).
Proof.
  unfold hbn_term. destruct (N.eq_dec n 0) as [->|_]; reflexivity.
Qed.

Lemma hbn_term_pos e n x : hbn_pos e -> hbn_pos x -> hbn_pos (hbn_term e n x).
Proof.
  intros He Hx. unfold hbn_term. destruct (N.eq_dec n 0); simpl; auto.
  split; [lia | auto].
Qed.

(** Subtracting one is the predecessor [P_b]. *)
Theorem hbn_dec_Pn base : (1 < base)%N ->
  (forall x x', hbn_dec base x x' -> hbn_pos x ->
     hbn_pos x' /\ Pn (N.to_nat base) (hbn_vf x) (hbn_vf x')) /\
  (forall e z, hbn_exp_dec base e z -> hbn_pos e ->
     hbn_pos z /\ Pn (N.to_nat base) (V (hbn_vf e) Z) (hbn_vf z)).
Proof.
  intro Hbase.
  apply (hbn_dec_comb base
    (fun x x' _ => hbn_pos x -> hbn_pos x' /\ Pn (N.to_nat base) (hbn_vf x) (hbn_vf x'))
    (fun e z _ => hbn_pos e -> hbn_pos z /\ Pn (N.to_nat base) (V (hbn_vf e) Z) (hbn_vf z))).
  - intros e n x x' _ IH [Hn [He Hx]].
    destruct (IH Hx) as [Hx' HP]. split; [simpl; auto|].
    simpl hbn_vf.
    rewrite (vrep_vcat _ (hbn_vf e) (hbn_vf x)), (vrep_vcat _ (hbn_vf e) (hbn_vf x')).
    apply Pn_vcat. exact HP.
  - intros e n x _ IH [Hn [He _]].
    destruct (IH He) as [Hx HP]. split; [apply hbn_term_pos; auto|].
    rewrite hbn_term_vf. simpl hbn_vf.
    rewrite N2Nat.inj_pred.
    destruct (N.to_nat n) as [|k] eqn:E; [lia|].
    simpl Nat.pred. rewrite (vrep_S_r k).
    rewrite (vrep_vcat k (hbn_vf e) (V (hbn_vf e) Z)), (vrep_vcat k (hbn_vf e) (hbn_vf x)).
    apply Pn_vcat. exact HP.
  - intros _. split; [exact I | apply Pn_one].
  - intros e e' z _ IH1 _ IH2 He.
    destruct (IH1 He) as [He' HP1]. destruct (IH2 He') as [Hz HP2].
    split; [simpl; split; [lia | auto]|].
    simpl hbn_vf. rewrite N2Nat.inj_pred. rewrite <- Nat.sub_1_r.
    apply Pn_exp; assumption.
Qed.

(** ** The ordinals of a Goodstein sequence *)

Definition goodstein_ord (m:N) (i:nat) : VForm := hbn_vf (goodstein_hbn m (N.of_nat i)).

(** The ordinal of [m] in hereditary base 2. *)
Definition ord2 (m:N) : VForm := hbn_vf (hbn_decompose 2 (plus2_base 0) m).

Lemma goodstein_ord_0 m : goodstein_ord m 0 = ord2 m.
Proof.
  unfold goodstein_ord, goodstein_hbn, ord2. simpl N.of_nat.
  rewrite goodstein_sequence0. reflexivity.
Qed.

Lemma goodstein_hbn_pos m i : hbn_pos (goodstein_hbn m i).
Proof. unfold goodstein_hbn. eapply hbn_proper_pos. apply hbn_decompose_proper. Qed.

Lemma goodstein_ord_Z m i : goodstein_ord m i = Z <-> goodstein_sequence m (N.of_nat i) = 0%N.
Proof.
  unfold goodstein_ord. split; intro H.
  - apply hbn_vf_Z in H; [|apply goodstein_hbn_pos].
    unfold goodstein_hbn in H. apply hbn_decompose_zero in H. exact H.
  - unfold goodstein_hbn. rewrite H.
    replace (hbn_decompose _ _ 0%N) with HBN_Z; [reflexivity|].
    symmetry. apply hbn_decompose_unique; [constructor | reflexivity].
Qed.

Lemma goodstein_ord_step m i : goodstein_ord m i <> Z ->
  Pn (i + 3) (goodstein_ord m i) (goodstein_ord m (S i)).
Proof.
  intro H. unfold goodstein_ord.
  destruct (goodstein_hbn_decreasing m (N.of_nat i)) as [Hz|Hd].
  - exfalso. apply H. unfold goodstein_ord. rewrite Hz. reflexivity.
  - rewrite Nat2N.inj_succ.
    replace (i + 3) with (N.to_nat (N.of_nat i + 3)) by (rewrite N2Nat.inj_add, Nat2N.id; reflexivity).
    apply (proj1 (hbn_dec_Pn _ (plus3_base (N.of_nat i)))); [exact Hd | apply goodstein_hbn_pos].
Qed.

(** ** Cichon's theorem *)

Lemma goodstein_hardy_from m d : forall i,
  goodstein_sequence m (N.of_nat (i + d)) = 0%N ->
  (forall j, i <= j < i + d -> goodstein_sequence m (N.of_nat j) <> 0%N) ->
  hardy (goodstein_ord m i) (i + 3) (i + d + 3).
Proof.
  induction d as [|d IH]; intros i H0 Hne.
  - rewrite Nat.add_0_r in *. apply goodstein_ord_Z in H0. rewrite H0. apply hardy_Z.
  - assert (Hi : goodstein_ord m i <> Z).
    { intro Hz. apply goodstein_ord_Z in Hz. apply (Hne i); [lia | exact Hz]. }
    apply hardy_P with (goodstein_ord m (S i)); [apply goodstein_ord_step; exact Hi|].
    replace (S (i + 3)) with (S i + 3) by lia.
    replace (i + S d + 3) with (S i + d + 3) by lia.
    apply IH.
    + replace (S i + d) with (i + S d) by lia. exact H0.
    + intros j Hj. apply Hne. lia.
Qed.

(** A least zero of the sequence. *)
Lemma goodstein_least_zero m k : goodstein_sequence m (N.of_nat k) = 0%N ->
  exists k0, k0 <= k /\ goodstein_sequence m (N.of_nat k0) = 0%N /\
    forall j, j < k0 -> goodstein_sequence m (N.of_nat j) <> 0%N.
Proof.
  induction k as [k IH] using lt_wf_ind. intro Hk.
  assert (Hdec : (exists j, j < k /\ goodstein_sequence m (N.of_nat j) = 0%N) \/
                 (forall j, j < k -> goodstein_sequence m (N.of_nat j) <> 0%N)).
  { clear IH Hk. induction k as [|k IHk].
    - right. intros j Hj. lia.
    - destruct IHk as [[j [Hj Hz]]|Hall].
      + left. exists j. split; [lia | exact Hz].
      + destruct (N.eq_dec (goodstein_sequence m (N.of_nat k)) 0%N) as [Hz|Hnz].
        * left. exists k. split; [lia | exact Hz].
        * right. intros j Hj. destruct (Nat.eq_dec j k) as [->|Hne]; [exact Hnz|].
          apply Hall. lia. }
  destruct Hdec as [[j [Hj Hz]]|Hall].
  - destruct (IH j Hj Hz) as [k0 [Hk0 Hrest]]. exists k0. split; [lia | exact Hrest].
  - exists k. split; [lia|]. split; [exact Hk | exact Hall].
Qed.

Theorem cichon m k :
  (goodstein_sequence m (N.of_nat k) = 0%N /\
     forall j, j < k -> goodstein_sequence m (N.of_nat j) <> 0%N) <->
  hardy (ord2 m) 3 (k + 3).
Proof.
  rewrite <- goodstein_ord_0. split.
  - intros [Hz Hne]. apply (goodstein_hardy_from m k 0); [exact Hz|].
    intros j Hj. apply Hne. lia.
  - intro H.
    destruct (goodstein_zero m) as [i Hi].
    destruct (goodstein_least_zero m (N.to_nat i)) as [k0 [_ [Hz Hne]]].
    { rewrite N2Nat.id. exact Hi. }
    assert (H0 := goodstein_hardy_from m k0 0 Hz ltac:(intros j Hj; apply Hne; lia)).
    assert (E := hardy_fun _ _ _ H _ H0).
    replace k with k0 by lia. split; assumption.
Qed.

(** The form used for lower bounds: the sequence takes at least
    [H_(o(m))(3) - 3] steps to reach zero. *)
Corollary goodstein_length_lower m k h :
  goodstein_sequence m (N.of_nat k) = 0%N -> hardy (ord2 m) 3 h -> h <= k + 3.
Proof.
  intros Hk Hh.
  destruct (goodstein_least_zero m k Hk) as [k0 [Hle [Hz Hne]]].
  assert (H0 : hardy (ord2 m) 3 (k0 + 3)) by (apply cichon; split; assumption).
  rewrite (hardy_fun _ _ _ Hh _ H0). lia.
Qed.
