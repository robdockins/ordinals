From Stdlib Require Import Arith.
From Stdlib Require Import NArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
Import ListNotations.

From Ordinal Require Import GoodsteinSequences.
From Ordinal Require Import Analysis.PeanoArith.
From Ordinal Require Import Analysis.Cichon.
From Ordinal Require Import Analysis.OmegaLogic.
From Ordinal Require Import Analysis.GoodsteinIndependence.

Local Open Scope nat_scope.

Local Opaque hbn_decompose.

(** * Goodstein's theorem as a sentence of arithmetic

    A bounded formula [goodstein_θ] with free variables [x] and [y] such
    that [∀x ∃y θ] states Goodstein's theorem: [θ(x,y)] holds when [y]
    bounds a _certificate_ that the sequence from [x] reaches zero
    ([goodstein_θ_sound]), and every [x] has one ([goodstein_θ_true]).
    By [goodstein_unprovable], Peano arithmetic does not prove it
    ([goodstein_independent]).

    The certificate is coded with Gödel's β-function
    [β(c,d,i) = c mod (1 + (i+1)·d)].  Besides the sequence itself, it
    holds for each step [i] (in base [b = i+2]) tables of [b^e], of
    [(b+1)^w], and of the base change [j ↦ T(j)] for [j] up to the
    current value, checked through the leading term:
    [T(d·b^e + r) = d·(b+1)^(T(e)) + T(r)] when [1 ≤ d < b] and [r < b^e]. *)

(** ** The β-function *)

Definition beta (c d i:nat) : nat := c mod (1 + (i + 1) * d).

Lemma beta_le c d i : beta c d i <= c.
Proof. unfold beta. apply Nat.Div0.mod_le. Qed.

Definition modulus (d i:nat) : nat := 1 + (i + 1) * d.

Fixpoint prodm (d j:nat) : nat :=
  match j with O => 1 | S j => prodm d j * modulus d j end.

Lemma prodm_pos d j : 0 < prodm d j.
Proof. induction j as [|j IH]; simpl; [lia|]. unfold modulus. nia. Qed.

Lemma prodm_divide d i j : i < j -> Nat.divide (modulus d i) (prodm d j).
Proof.
  intro H. induction j as [|j IH]; [lia|]. simpl.
  destruct (Nat.eq_dec i j) as [->|Hne].
  - apply Nat.divide_mul_r. apply Nat.divide_refl.
  - apply Nat.divide_mul_l. apply IH. lia.
Qed.

Lemma divide_fact k D : 1 <= k <= D -> Nat.divide k (fact D).
Proof.
  induction D as [|D IH]; intro H; [lia|].
  simpl fact. replace (fact D + D * fact D) with (S D * fact D) by (simpl; lia).
  destruct (Nat.eq_dec k (S D)) as [->|Hne].
  - apply Nat.divide_mul_l. apply Nat.divide_refl.
  - apply Nat.divide_mul_r. apply IH. lia.
Qed.

Lemma fact_ge D : D <= fact D.
Proof. induction D as [|D IH]; simpl; [lia|]. assert (1 <= fact D) by apply lt_O_fact. nia. Qed.

Lemma coprime_moduli d i j : (forall k, 1 <= k <= j - i -> Nat.divide k d) -> i < j ->
  Nat.gcd (modulus d i) (modulus d j) = 1.
Proof.
  intros Hd Hij. set (g := Nat.gcd (modulus d i) (modulus d j)).
  assert (Hgi : Nat.divide g (modulus d i)) by apply Nat.gcd_divide_l.
  assert (Hgj : Nat.divide g (modulus d j)) by apply Nat.gcd_divide_r.
  assert (E : (j + 1) * modulus d i = (i + 1) * modulus d j + (j - i)).
  { unfold modulus. replace j with (i + (j - i)) at 1 2 by lia. ring_simplify.
    replace (i + (j - i)) with j by lia. ring. }
  assert (Hji : Nat.divide g (j - i)).
  { apply (Nat.divide_add_cancel_r g ((i + 1) * modulus d j)); [apply Nat.divide_mul_r; exact Hgj|].
    rewrite <- E. apply Nat.divide_mul_r. exact Hgi. }
  assert (Hgd : Nat.divide g d) by (apply Nat.divide_trans with (j - i); [exact Hji | apply Hd; lia]).
  assert (H1 : Nat.divide g 1).
  { apply (Nat.divide_add_cancel_r g ((i + 1) * d)); [apply Nat.divide_mul_r; exact Hgd|].
    replace ((i + 1) * d + 1) with (modulus d i) by (unfold modulus; lia). exact Hgi. }
  apply Nat.divide_1_r. exact H1.
Qed.

Lemma coprime_mul a b c : Nat.gcd a c = 1 -> Nat.gcd b c = 1 -> Nat.gcd (a * b) c = 1.
Proof.
  intros Ha Hb. set (g := Nat.gcd (a * b) c).
  assert (Hgc : Nat.divide g c) by apply Nat.gcd_divide_r.
  assert (Hga : Nat.gcd g a = 1).
  { apply Nat.divide_1_r. rewrite <- Ha. apply Nat.gcd_greatest; [apply Nat.gcd_divide_r|].
    apply Nat.divide_trans with g; [apply Nat.gcd_divide_l | exact Hgc]. }
  assert (Hgb : Nat.divide g b).
  { apply Nat.gauss with a; [apply Nat.gcd_divide_l | exact Hga]. }
  apply Nat.divide_1_r. rewrite <- Hb. apply Nat.gcd_greatest; assumption.
Qed.

Lemma coprime_prodm d j : (forall i, i < j -> Nat.gcd (modulus d i) (modulus d j) = 1) ->
  forall j', j' <= j -> Nat.gcd (prodm d j') (modulus d j) = 1.
Proof.
  intros H j' Hj'. induction j' as [|j' IH]; cbn [prodm].
  - apply Nat.divide_1_r. apply Nat.gcd_divide_l.
  - apply coprime_mul; [apply IH; lia | apply H; lia].
Qed.

(** The Chinese remainder theorem for the moduli of the β-function. *)
Lemma crt d (f:nat -> nat) L : (forall i j, i < j < L -> Nat.gcd (modulus d i) (modulus d j) = 1) ->
  exists c, forall i, i < L -> c mod modulus d i = f i mod modulus d i.
Proof.
  intro Hcop. induction L as [|L IH].
  - exists 0. intros i Hi. lia.
  - destruct IH as [c Hc]; [intros i j Hij; apply Hcop; lia|].
    set (P := prodm d L). set (m := modulus d L).
    assert (Hm : 0 < m) by (unfold m, modulus; lia).
    assert (Hg : Nat.gcd P m = 1) by (apply coprime_prodm; [intros i Hi; apply Hcop; lia | lia]).
    destruct (Nat.gcd_bezout_pos P m (prodm_pos d L)) as [u [v Huv]]. rewrite Hg in Huv.
    set (t := f L mod m + m - c mod m).
    exists (c + (u * t) * P). intros i Hi.
    destruct (Nat.eq_dec i L) as [->|Hne].
    + fold m. assert (Hcm : c mod m < m) by (apply Nat.mod_upper_bound; lia).
      replace (c + u * t * P) with ((c + t) + (t * v) * m) by (rewrite <- Nat.mul_assoc, (Nat.mul_comm u t), <- Nat.mul_assoc, Huv; ring).
      rewrite Nat.Div0.mod_add.
      rewrite (Nat.div_mod_eq c m) at 1.
      replace (m * (c / m) + c mod m + t) with (f L mod m + (c / m + 1) * m) by (unfold t; lia).
      rewrite Nat.Div0.mod_add. apply Nat.Div0.mod_mod.
    + destruct (prodm_divide d i L ltac:(lia)) as [q Hq]. fold P in Hq. rewrite Hq.
      replace (c + u * t * (q * modulus d i)) with (c + (u * t * q) * modulus d i) by ring.
      rewrite Nat.Div0.mod_add. apply Hc. lia.
Qed.

Fixpoint sumf (f:nat -> nat) (n:nat) : nat :=
  match n with O => 0 | S n => sumf f n + f n end.

Lemma sumf_ge f n i : i < n -> f i <= sumf f n.
Proof. induction n as [|n IH]; simpl; intro H; [lia|]. destruct (Nat.eq_dec i n) as [->|]; [lia|]. specialize (IH ltac:(lia)). lia. Qed.

Theorem beta_exists (f:nat -> nat) L : exists c d, forall i, i < L -> beta c d i = f i.
Proof.
  set (D := L + sumf f L). set (d := fact D).
  destruct (crt d f L) as [c Hc].
  - intros i j Hij. apply coprime_moduli; [|lia].
    intros k Hk. apply divide_fact. unfold D. lia.
  - exists c, d. intros i Hi. unfold beta. fold (modulus d i). rewrite (Hc i Hi).
    apply Nat.mod_small. unfold modulus.
    assert (f i <= D) by (assert (H := sumf_ge f L i Hi); unfold D; lia).
    assert (D <= d) by apply fact_ge. nia.
Qed.

(** ** Bounded formulas with known meanings

    Formulas are written with de Bruijn indices.  A _macro_ is a formula
    whose free variables [0..k-1] are its arguments; [call F l] plugs
    terms into them.  Inside [ball v B] and [bex v B] the bound variable
    is [0] and the others shift by one. *)

Definition lift (t:aterm) : aterm := asubst shift_sub t.
Definition ball (v:aterm) (B:form) : form := All (Imp (Ex (Eq (tplus (tv 1) (tv 0)) (lift (lift v)))) B).
Definition fneg (A:form) : form := Imp A Bot.
Definition bex (v:aterm) (B:form) : form := fneg (ball v (fneg B)).
Definition fle (u v:aterm) : form := Ex (Eq (tplus (lift u) (tv 0)) (lift v)).
Definition flt (u v:aterm) : form := fle (ts u) v.
Definition call (F:form) (l:list aterm) : form := fsubst (fun i => nth i l tz) F.

Lemma occ0_lift t : occ 0 (lift t) = false.
Proof. unfold lift. rewrite occ_shift. reflexivity. Qed.

Lemma occ1_lift2 t : occ 1 (lift (lift t)) = false.
Proof. unfold lift at 1. rewrite occ_shift. apply occ0_lift. Qed.

Lemma isD_ball v B : isD (ball v B) = isD B.
Proof. unfold ball. cbn [isD]. rewrite occ0_lift, occ1_lift2. reflexivity. Qed.

Lemma isD_bex v B : isD (bex v B) = isD B.
Proof. unfold bex, fneg. cbn [isD]. rewrite isD_ball. cbn [isD]. destruct (isD B); reflexivity. Qed.

Lemma isD_fle u v : isD (fle u v) = true.
Proof. unfold fle. cbn [isD]. rewrite !occ0_lift. reflexivity. Qed.

Lemma isD_call F l : isD (call F l) = isD F.
Proof. apply isD_fsubst_eq. Qed.

Lemma teval_lift x ρ t : teval (scons x ρ) (lift t) = teval ρ t.
Proof. apply teval_shift. Qed.

Lemma sat_ball ρ v B : sat ρ (ball v B) <-> forall z, z <= teval ρ v -> sat (scons z ρ) B.
Proof.
  unfold ball. cbn [sat teval]. split.
  - intros H z Hz. apply H. exists (teval ρ v - z). simpl. rewrite !teval_lift. lia.
  - intros H z [d Hd]. apply H. simpl in Hd. rewrite !teval_lift in Hd. lia.
Qed.

Lemma sat_dec ρ B : isD B = true -> sat ρ B \/ ~ sat ρ B.
Proof.
  intro H. destruct (deval ρ B) eqn:E; [left; apply deval_sat; assumption | right; apply deval_false; assumption].
Qed.

Lemma bounded_search (P:nat -> Prop) b : (forall z, P z \/ ~ P z) ->
  ~ (forall z, z <= b -> ~ P z) -> exists z, z <= b /\ P z.
Proof.
  intros Hd. induction b as [|b IH]; intro H.
  - destruct (Hd 0) as [H0|H0]; [exists 0; split; [lia | exact H0]|].
    exfalso. apply H. intros z Hz. replace z with 0 by lia. exact H0.
  - destruct (Hd (S b)) as [H1|H1]; [exists (S b); split; [lia | exact H1]|].
    destruct IH as [z [Hz Pz]].
    + intro H2. apply H. intros z Hz. destruct (Nat.eq_dec z (S b)) as [->|]; [exact H1 | apply H2; lia].
    + exists z. split; [lia | exact Pz].
Qed.

Lemma sat_bex ρ v B : isD B = true -> (sat ρ (bex v B) <-> exists z, z <= teval ρ v /\ sat (scons z ρ) B).
Proof.
  intro HD. unfold bex, fneg. cbn [sat]. rewrite sat_ball. cbn [sat]. split.
  - intro H. apply bounded_search; [intro z; apply sat_dec; exact HD|].
    intro H'. apply H. intros z Hz HB. exact (H' z Hz HB).
  - intros [z [Hz HB]] H. exact (H z Hz HB).
Qed.

Lemma sat_fle ρ u v : sat ρ (fle u v) <-> teval ρ u <= teval ρ v.
Proof.
  unfold fle. cbn [sat teval]. split.
  - intros [d Hd]. simpl in Hd. rewrite !teval_lift in Hd. lia.
  - intro H. exists (teval ρ v - teval ρ u). simpl. rewrite !teval_lift. lia.
Qed.

Lemma sat_flt ρ u v : sat ρ (flt u v) <-> teval ρ u < teval ρ v.
Proof. unfold flt. rewrite sat_fle. simpl. lia. Qed.

Lemma sat_call ρ F l : sat ρ (call F l) <-> sat (fun i => teval ρ (nth i l tz)) F.
Proof. apply sat_fsubst. Qed.

(** [a mod m = r], with arguments [a, m, r]. *)
Definition MODf : form :=
  And (flt (tv 2) (tv 1)) (bex (tv 0) (Eq (tv 1) (tplus (tmult (tv 0) (tv 2)) (tv 3)))).

Lemma sat_MODf ρ : sat ρ MODf <-> 0 < ρ 1 /\ ρ 0 mod ρ 1 = ρ 2.
Proof.
  unfold MODf. cbn [sat]. rewrite sat_flt, sat_bex by reflexivity. simpl. split.
  - intros [Hr [q [Hq Ha]]]. split; [lia|]. rewrite Ha.
    rewrite Nat.add_comm, Nat.Div0.mod_add. apply Nat.mod_small. exact Hr.
  - intros [Hm Hr]. split; [rewrite <- Hr; apply Nat.mod_upper_bound; lia|].
    exists (ρ 0 / ρ 1). split; [apply Nat.Div0.div_le_upper_bound; nia|].
    rewrite <- Hr. rewrite (Nat.div_mod_eq (ρ 0) (ρ 1)) at 1. lia.
Qed.

(** Table lookups: entry [j] of table [tag] at step [i]. *)
Definition bt (c d M tag i j:nat) : nat := beta c d (4 * (i * M + j) + tag).

Lemma bt_le c d M tag i j : bt c d M tag i j <= c.
Proof. apply beta_le. Qed.

(** Arguments [c, d, M, i, j, v]: [bt c d M tag i j = v]. *)
Definition LOOK (tag:nat) : form :=
  call MODf [tv 0; ts (tmult (ts (tplus (tmult (num 4) (tplus (tmult (tv 3) (tv 2)) (tv 4))) (num tag))) (tv 1)); tv 5].

Lemma sat_LOOK ρ tag : sat ρ (LOOK tag) <-> bt (ρ 0) (ρ 1) (ρ 2) tag (ρ 3) (ρ 4) = ρ 5.
Proof.
  unfold LOOK. rewrite sat_call, sat_MODf. cbn [teval nth]. rewrite !teval_num.
  unfold bt, beta.
  replace (S (S (4 * (ρ 3 * ρ 2 + ρ 4) + tag) * ρ 1)) with (1 + (4 * (ρ 3 * ρ 2 + ρ 4) + tag + 1) * ρ 1) by ring.
  split; [intros [_ H]; exact H | intro H; split; [lia | exact H]].
Qed.

Definition flook (tag:nat) (c d M i j v:aterm) : form := call (LOOK tag) [c; d; M; i; j; v].

Lemma sat_flook ρ tag c d M i j v : sat ρ (flook tag c d M i j v) <->
  bt (teval ρ c) (teval ρ d) (teval ρ M) tag (teval ρ i) (teval ρ j) = teval ρ v.
Proof. unfold flook. rewrite sat_call, sat_LOOK. reflexivity. Qed.

Lemma isD_flook tag c d M i j v : isD (flook tag c d M i j v) = true.
Proof. unfold flook, LOOK. rewrite !isD_call. reflexivity. Qed.

(** [let v := bt .. in B], as a bounded universal. *)
Definition flet (tag:nat) (c d M i j:aterm) (B:form) : form :=
  ball c (Imp (flook tag (lift c) (lift d) (lift M) (lift i) (lift j) (tv 0)) B).

Lemma sat_flet ρ tag c d M i j B : sat ρ (flet tag c d M i j B) <->
  sat (scons (bt (teval ρ c) (teval ρ d) (teval ρ M) tag (teval ρ i) (teval ρ j)) ρ) B.
Proof.
  unfold flet. rewrite sat_ball. cbn [sat]. setoid_rewrite sat_flook. simpl. setoid_rewrite teval_lift.
  split.
  - intro H. apply H; [apply bt_le | reflexivity].
  - intros H z Hz <-. exact H.
Qed.

Lemma isD_flet tag c d M i j B : isD (flet tag c d M i j B) = isD B.
Proof. unfold flet. rewrite isD_ball. cbn [isD]. rewrite isD_flook. reflexivity. Qed.

(** ** The certificate

    Tables, at step [i] with base [b = i+2]:
    - [0]: entry [0] is the [i]-th term of the sequence;
    - [1]: the base change [T(j)], for [j] up to the current term;
    - [2]: the powers [b^e];
    - [3]: the powers [(b+1)^w], for [w + 1 < M]. *)

(** Arguments [c, d, M, i, n]. *)
Definition PBf : form :=
  And (flook 2 (tv 0) (tv 1) (tv 2) (tv 3) tz (num 1))
      (ball (tv 4) (Imp (flt (tv 0) (tv 5))
         (flet 2 (tv 1) (tv 2) (tv 3) (tv 4) (tv 0)
            (flook 2 (tv 2) (tv 3) (tv 4) (tv 5) (ts (tv 1)) (tmult (ts (ts (tv 5))) (tv 0)))))).

Definition PBok (c d M i n:nat) : Prop :=
  bt c d M 2 i 0 = 1 /\
  forall e, e <= n -> e < n -> bt c d M 2 i (S e) = S (S i) * bt c d M 2 i e.

Lemma sat_PBf ρ : sat ρ PBf <-> PBok (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4).
Proof.
  unfold PBf, PBok. cbn [sat]. rewrite sat_flook, sat_ball. cbn [sat].
  setoid_rewrite sat_flt. setoid_rewrite sat_flet. setoid_rewrite sat_flook.
  cbn [teval scons]. rewrite !teval_num. reflexivity.
Qed.

(** Arguments [c, d, M, i]. *)
Definition Qf : form :=
  And (flook 3 (tv 0) (tv 1) (tv 2) (tv 3) tz (num 1))
      (ball (tv 2) (Imp (flt (ts (tv 0)) (tv 3))
         (flet 3 (tv 1) (tv 2) (tv 3) (tv 4) (tv 0)
            (flook 3 (tv 2) (tv 3) (tv 4) (tv 5) (ts (tv 1)) (tmult (ts (ts (ts (tv 5)))) (tv 0)))))).

Definition Qok (c d M i:nat) : Prop :=
  bt c d M 3 i 0 = 1 /\
  forall w, w <= M -> S w < M -> bt c d M 3 i (S w) = S (S (S i)) * bt c d M 3 i w.

Lemma sat_Qf ρ : sat ρ Qf <-> Qok (ρ 0) (ρ 1) (ρ 2) (ρ 3).
Proof.
  unfold Qf, Qok. cbn [sat]. rewrite sat_flook, sat_ball. cbn [sat].
  setoid_rewrite sat_flt. setoid_rewrite sat_flet. setoid_rewrite sat_flook.
  cbn [teval scons]. rewrite !teval_num. reflexivity.
Qed.

(** Arguments [c, d, M, i, n]: the base change, through leading terms. *)
Definition Tf : form :=
  And (flook 1 (tv 0) (tv 1) (tv 2) (tv 3) tz tz)
      (ball (tv 4) (Imp (fle (num 1) (tv 0))
        (bex (tv 0) (bex (tv 1) (bex (tv 2)
          (flet 2 (tv 4) (tv 5) (tv 6) (tv 7) (tv 2)
          (flet 1 (tv 5) (tv 6) (tv 7) (tv 8) (tv 3)
          (flet 3 (tv 6) (tv 7) (tv 8) (tv 9) (tv 0)
          (flet 1 (tv 7) (tv 8) (tv 9) (tv 10) (tv 3)
            (And (Eq (tv 7) (tplus (tmult (tv 5) (tv 3)) (tv 4)))
            (And (flt (tv 4) (tv 3))
            (And (fle (num 1) (tv 5))
            (And (flt (tv 5) (ts (ts (tv 11))))
            (And (flt (tv 2) (tv 10))
                 (flook 1 (tv 8) (tv 9) (tv 10) (tv 11) (tv 7) (tplus (tmult (tv 5) (tv 1)) (tv 0))))))))))))))))).

Definition Tok (c d M i n:nat) : Prop :=
  bt c d M 1 i 0 = 0 /\
  forall j, j <= n -> 1 <= j ->
    exists e, e <= j /\ exists dd, dd <= j /\ exists r, r <= j /\
      j = dd * bt c d M 2 i e + r /\ r < bt c d M 2 i e /\ 1 <= dd /\ dd < S (S i) /\
      bt c d M 1 i e < M /\
      bt c d M 1 i j = dd * bt c d M 3 i (bt c d M 1 i e) + bt c d M 1 i r.

Lemma sat_Tf ρ : sat ρ Tf <-> Tok (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4).
Proof.
  unfold Tf, Tok. cbn [sat]. rewrite sat_flook, sat_ball. cbn [sat].
  setoid_rewrite sat_fle.
  do 3 (setoid_rewrite sat_bex; [|reflexivity]).
  repeat setoid_rewrite sat_flet. cbn [sat]. repeat setoid_rewrite sat_flt. repeat setoid_rewrite sat_fle.
  repeat setoid_rewrite sat_flook. cbn [teval scons num]. reflexivity.
Qed.

(** Arguments [c, d, M, i]: step [i] of the sequence is checked. *)
Definition STEPf : form :=
  flet 0 (tv 0) (tv 1) (tv 2) (tv 3) tz
    (And (fle (num 1) (tv 0))
    (And (flt (tv 0) (tv 3))
    (And (flet 0 (tv 1) (tv 2) (tv 3) (ts (tv 4)) tz
            (flook 1 (tv 2) (tv 3) (tv 4) (tv 5) (tv 1) (ts (tv 0))))
    (And (call PBf [tv 1; tv 2; tv 3; tv 4; tv 0])
    (And (call Qf [tv 1; tv 2; tv 3; tv 4])
         (call Tf [tv 1; tv 2; tv 3; tv 4; tv 0])))))).

Definition STEPok (c d M i:nat) : Prop :=
  let n := bt c d M 0 i 0 in
  1 <= n /\ n < M /\ bt c d M 1 i n = S (bt c d M 0 (S i) 0) /\
  PBok c d M i n /\ Qok c d M i /\ Tok c d M i n.

Lemma sat_STEPf ρ : sat ρ STEPf <-> STEPok (ρ 0) (ρ 1) (ρ 2) (ρ 3).
Proof.
  unfold STEPf, STEPok. rewrite sat_flet. cbn [sat].
  rewrite sat_fle, sat_flt, sat_flet, sat_flook, !sat_call, sat_PBf, sat_Qf, sat_Tf.
  cbn [teval scons num nth]. reflexivity.
Qed.

(** Arguments [x, k, M, c, d]. *)
Definition CHECKf : form :=
  And (flook 0 (tv 3) (tv 4) (tv 2) tz tz (tv 0))
  (And (flook 0 (tv 3) (tv 4) (tv 2) (tv 1) tz tz)
       (ball (tv 1) (Imp (flt (tv 0) (tv 2)) (call STEPf [tv 4; tv 5; tv 3; tv 0])))).

Definition CHECKok (x k M c d:nat) : Prop :=
  bt c d M 0 0 0 = x /\ bt c d M 0 k 0 = 0 /\
  forall i, i <= k -> i < k -> STEPok c d M i.

Lemma sat_CHECKf ρ : sat ρ CHECKf <-> CHECKok (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4).
Proof.
  unfold CHECKf, CHECKok. cbn [sat]. rewrite !sat_flook, sat_ball. cbn [sat].
  setoid_rewrite sat_flt. setoid_rewrite sat_call. setoid_rewrite sat_STEPf.
  cbn [teval scons num nth]. reflexivity.
Qed.

Lemma isD_STEPf : isD STEPf = true.
Proof. reflexivity. Qed.

Lemma isD_CHECKf : isD CHECKf = true.
Proof. reflexivity. Qed.

(** The Goodstein sentence is [∀x ∃y θ], with [x] variable [1] and [y]
    variable [0] of [θ]. *)
Definition goodstein_θ : form :=
  bex (tv 0) (bex (tv 1) (bex (tv 2) (bex (tv 3) (call CHECKf [tv 5; tv 3; tv 2; tv 1; tv 0])))).

Definition goodstein_sentence : form := All (Ex goodstein_θ).

Lemma isD_goodstein_θ : isD goodstein_θ = true.
Proof. reflexivity. Qed.

Lemma isD_goodstein_Ex : isD (Ex goodstein_θ) = false.
Proof. reflexivity. Qed.

Lemma sat_goodstein_θ x y ρ : sat (scons y (scons x ρ)) goodstein_θ <->
  exists k, k <= y /\ exists M, M <= y /\ exists c, c <= y /\ exists d, d <= y /\ CHECKok x k M c d.
Proof.
  unfold goodstein_θ. do 4 (setoid_rewrite sat_bex; [|reflexivity]).
  setoid_rewrite sat_call. setoid_rewrite sat_CHECKf. cbn [teval scons nth]. reflexivity.
Qed.

(** ** Soundness: a certificate is the Goodstein sequence *)

(** The base change at step [i], from base [i+2] to [i+3]. *)
Definition bumpi (i j:nat) : nat :=
  N.to_nat (hbn_interp (N.of_nat i + 3) (hbn_decompose (N.of_nat i + 2) (plus2_base (N.of_nat i)) (N.of_nat j))).

Definition gs (x i:nat) : nat := N.to_nat (goodstein_sequence (N.of_nat x) (N.of_nat i)).

Lemma gs_0 x : gs x 0 = x.
Proof. unfold gs. simpl N.of_nat. rewrite goodstein_sequence0. apply Nat2N.id. Qed.

Lemma gs_succ x i : gs x (S i) = bumpi i (gs x i) - 1.
Proof.
  unfold gs, bumpi. rewrite Nat2N.inj_succ, goodstein_sequence_succ. simpl.
  rewrite N2Nat.id. rewrite N2Nat.inj_sub. reflexivity.
Qed.

Lemma dec_zero i : hbn_decompose (N.of_nat i + 2) (plus2_base (N.of_nat i)) 0%N = HBN_Z.
Proof. apply hbn_decompose_unique; [constructor | reflexivity]. Qed.

Lemma bumpi_0 i : bumpi i 0 = 0.
Proof. unfold bumpi. simpl N.of_nat. rewrite dec_zero. reflexivity. Qed.

Lemma bumpi_lead i j e dd r : 1 <= dd -> dd < i + 2 -> r < (i + 2) ^ e -> j = dd * (i + 2) ^ e + r ->
  bumpi i j = dd * (i + 3) ^ bumpi i e + bumpi i r.
Proof.
  intros Hd1 Hd2 Hr Hj. unfold bumpi.
  set (B := (N.of_nat i + 2)%N). set (HB := plus2_base (N.of_nat i)).
  assert (HBr : (N.of_nat r < B ^ N.of_nat e)%N).
  { unfold B. replace (N.of_nat i + 2)%N with (N.of_nat (i + 2)) by lia.
    rewrite <- Nat2N.inj_pow. lia. }
  rewrite (hbn_decompose_unique B HB (N.of_nat j)
             (HBN_Term (hbn_decompose B HB (N.of_nat e)) (N.of_nat dd) (hbn_decompose B HB (N.of_nat r)))).
  - simpl hbn_interp. rewrite N2Nat.inj_add, N2Nat.inj_mul, N2Nat.inj_pow, Nat2N.id.
    replace (N.to_nat (N.of_nat i + 3)) with (i + 3) by lia. ring.
  - constructor; [apply hbn_decompose_proper | unfold B; lia | apply hbn_decompose_proper |].
    apply (hbn_smaller_exp_equiv B HB); [apply hbn_decompose_proper | apply hbn_decompose_proper|].
    rewrite !hbn_decompose_correct. exact HBr.
  - simpl. rewrite !hbn_decompose_correct. subst j.
    rewrite Nat2N.inj_add, Nat2N.inj_mul, Nat2N.inj_pow. unfold B.
    replace (N.of_nat (i + 2)) with (N.of_nat i + 2)%N by lia. ring.
Qed.

Section Tables.
  Variables c d M i n : nat.

  Lemma PB_table : PBok c d M i n -> forall e, e <= n -> bt c d M 2 i e = (i + 2) ^ e.
  Proof.
    intros [H0 HS] e. induction e as [|e IH]; intro He; [exact H0|].
    rewrite HS by lia. rewrite IH by lia. simpl. lia.
  Qed.

  Lemma Q_table : Qok c d M i -> forall w, w < M -> bt c d M 3 i w = (i + 3) ^ w.
  Proof.
    intros [H0 HS] w. induction w as [|w IH]; intro Hw; [exact H0|].
    rewrite HS by lia. rewrite IH by lia. simpl. lia.
  Qed.

  Lemma T_table : PBok c d M i n -> Qok c d M i -> Tok c d M i n ->
    forall j, j <= n -> bt c d M 1 i j = bumpi i j.
  Proof.
    intros HP HQ [HT0 HT].
    induction j as [j IH] using lt_wf_ind. intro Hj.
    destruct j as [|j']; [rewrite HT0, bumpi_0; reflexivity|].
    destruct (HT (S j') Hj ltac:(lia)) as [e [He [dd [Hdd [r [Hr [Ej [Hrp [Hd1 [Hd2 [HeM Hval]]]]]]]]]]].
    rewrite (PB_table HP e) in Ej, Hrp by lia.
    assert (Hpow : e < (i + 2) ^ e) by (apply Nat.pow_gt_lin_r; lia).
    assert (Hej : e < S j') by nia.
    assert (Hrj : r < S j') by nia.
    rewrite Hval, (IH e Hej ltac:(lia)), (IH r Hrj ltac:(lia)).
    rewrite (IH e Hej ltac:(lia)) in HeM.
    rewrite (Q_table HQ) by exact HeM.
    symmetry. apply bumpi_lead; lia.
  Qed.
End Tables.

Theorem check_sound x k M c d : CHECKok x k M c d ->
  goodstein_sequence (N.of_nat x) (N.of_nat k) = 0%N.
Proof.
  intros [H0 [Hk Hsteps]].
  assert (Hg : forall i, i <= k -> bt c d M 0 i 0 = gs x i).
  { induction i as [|i IH]; intro Hi; [rewrite gs_0; exact H0|].
    destruct (Hsteps i ltac:(lia) ltac:(lia)) as [Hn1 [HnM [Hnext [HP [HQ HT]]]]].
    rewrite gs_succ, <- IH by lia.
    rewrite (T_table c d M i _ HP HQ HT) in Hnext by lia. lia. }
  rewrite <- (N2Nat.id (goodstein_sequence _ _)). fold (gs x k).
  rewrite <- (Hg k (le_n k)), Hk. reflexivity.
Qed.

(** ** Truth: every sequence has a certificate *)

Lemma lead_exists i j : 1 <= j ->
  exists e dd r, 1 <= dd /\ dd < i + 2 /\ r < (i + 2) ^ e /\ j = dd * (i + 2) ^ e + r.
Proof.
  intro Hj. set (B := (N.of_nat i + 2)%N). set (HB := plus2_base (N.of_nat i)).
  assert (Hp := hbn_decompose_proper B HB (N.of_nat j)).
  assert (Hc := hbn_decompose_correct B HB (N.of_nat j)).
  destruct (hbn_decompose B HB (N.of_nat j)) as [|E D R] eqn:Edec.
  - simpl in Hc. lia.
  - inversion Hp as [|E' D' R' HE HD HR Hsm]; subst.
    apply (hbn_smaller_exp_equiv B HB) in Hsm; [|exact HR | exact HE].
    exists (N.to_nat (hbn_interp B E)), (N.to_nat D), (N.to_nat (hbn_interp B R)).
    assert (HBn : N.to_nat B = i + 2) by (unfold B; lia).
    split; [lia|]. split; [lia|]. split.
    + rewrite <- HBn, <- N2Nat.inj_pow. lia.
    + simpl in Hc. rewrite <- HBn, <- N2Nat.inj_pow. lia.
Qed.

Lemma bumpi_pos i n : 1 <= n -> 1 <= bumpi i n.
Proof.
  intro Hn. destruct (lead_exists i n Hn) as [e [dd [r [H1 [H2 [H3 H4]]]]]].
  rewrite (bumpi_lead i n e dd r H1 H2 H3 H4).
  assert (0 < (i + 3) ^ bumpi i e) by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia). nia.
Qed.

Section Certificate.
  Variable x : nat.
  Variable k0 : nat.
  Hypothesis Hk0 : gs x k0 = 0.
  Hypothesis Hbefore : forall j, j < k0 -> gs x j <> 0.

  Definition Mc : nat := S (sumf (fun i => gs x i + sumf (bumpi i) (S (gs x i))) k0).

  Lemma Mc_gs i : i < k0 -> gs x i < Mc.
  Proof.
    intro Hi. unfold Mc.
    assert (H := sumf_ge (fun i => gs x i + sumf (bumpi i) (S (gs x i))) k0 i Hi). cbv beta in H. lia.
  Qed.

  Lemma Mc_bump i e : i < k0 -> e <= gs x i -> bumpi i e < Mc.
  Proof.
    intros Hi He. unfold Mc.
    assert (H := sumf_ge (fun i => gs x i + sumf (bumpi i) (S (gs x i))) k0 i Hi).
    assert (H' := sumf_ge (bumpi i) (S (gs x i)) e ltac:(lia)). cbv beta in H. lia.
  Qed.

  Definition entry (idx:nat) : nat :=
    let p := idx / 4 in
    let i := p / Mc in
    let j := p mod Mc in
    match idx mod 4 with
    | 0 => if j =? 0 then gs x i else 0
    | 1 => bumpi i j
    | 2 => (i + 2) ^ j
    | _ => (i + 3) ^ j
    end.

  Lemma entry_decode tag i j : tag < 4 -> j < Mc ->
    entry (4 * (i * Mc + j) + tag) =
    match tag with
    | 0 => if j =? 0 then gs x i else 0
    | 1 => bumpi i j
    | 2 => (i + 2) ^ j
    | _ => (i + 3) ^ j
    end.
  Proof.
    intros Ht Hj. unfold entry.
    assert (E1 : (4 * (i * Mc + j) + tag) mod 4 = tag) by (symmetry; apply Nat.mod_unique with (i * Mc + j); lia).
    assert (E2 : (4 * (i * Mc + j) + tag) / 4 = i * Mc + j) by (symmetry; apply Nat.div_unique with tag; lia).
    assert (E3 : (i * Mc + j) / Mc = i) by (symmetry; apply Nat.div_unique with j; lia).
    assert (E4 : (i * Mc + j) mod Mc = j) by (symmetry; apply Nat.mod_unique with i; lia).
    rewrite E1, E2, E3, E4. reflexivity.
  Qed.

  Definition Lc : nat := 4 * (S k0 * Mc).

  Variables c d : nat.
  Hypothesis Hcd : forall idx, idx < Lc -> beta c d idx = entry idx.

  Lemma bt_val tag i j : tag < 4 -> i <= k0 -> j < Mc ->
    bt c d Mc tag i j =
    match tag with
    | 0 => if j =? 0 then gs x i else 0
    | 1 => bumpi i j
    | 2 => (i + 2) ^ j
    | _ => (i + 3) ^ j
    end.
  Proof.
    intros Ht Hi Hj. unfold bt. rewrite Hcd; [apply entry_decode; assumption|].
    unfold Lc. nia.
  Qed.

  Lemma Mc_pos : 0 < Mc.
  Proof. unfold Mc. lia. Qed.

  Lemma check_true : CHECKok x k0 Mc c d.
  Proof.
    assert (HM := Mc_pos).
    split; [rewrite bt_val by lia; rewrite gs_0; reflexivity|].
    split; [rewrite bt_val by lia; exact Hk0|].
    intros i _ Hi.
    assert (Hn1 : 1 <= gs x i) by (specialize (Hbefore i Hi); lia).
    assert (HnM := Mc_gs i Hi).
    unfold STEPok. rewrite (bt_val 0 i 0) by lia. simpl.
    split; [exact Hn1|]. split; [exact HnM|]. split.
    { rewrite bt_val by lia. rewrite (bt_val 0 (S i) 0) by lia. simpl.
      rewrite gs_succ. assert (H := bumpi_pos i (gs x i) Hn1). lia. }
    split.
    { split; [rewrite bt_val by lia; reflexivity|].
      intros e _ He. rewrite !bt_val by lia. simpl. lia. }
    split.
    { split; [rewrite bt_val by lia; reflexivity|].
      intros w _ Hw. rewrite !bt_val by lia. simpl. lia. }
    split; [rewrite bt_val by lia; apply bumpi_0|].
    intros j Hj Hj1.
    destruct (lead_exists i j Hj1) as [e [dd [r [Hd1 [Hd2 [Hr Ej]]]]]].
    assert (Hpow : e < (i + 2) ^ e) by (apply Nat.pow_gt_lin_r; lia).
    assert (Hej : e <= j) by nia.
    assert (Hrj : r <= j) by nia.
    assert (HeM := Mc_bump i e Hi ltac:(lia)).
    exists e. split; [exact Hej|]. exists dd. split; [nia|]. exists r. split; [exact Hrj|].
    rewrite !(bt_val 2 i e) by lia. rewrite !(bt_val 1 i e) by lia.
    rewrite (bt_val 3 i (bumpi i e)) by lia. rewrite (bt_val 1 i j) by lia. rewrite (bt_val 1 i r) by lia.
    simpl. split; [exact Ej|]. split; [exact Hr|]. split; [exact Hd1|]. split; [lia|]. split; [exact HeM|].
    apply bumpi_lead; assumption.
  Qed.
End Certificate.

Theorem goodstein_θ_true x : exists y, sat (scons y (scons x ρ0)) goodstein_θ.
Proof.
  destruct (goodstein_zero (N.of_nat x)) as [i Hi].
  destruct (goodstein_least_zero (N.of_nat x) (N.to_nat i)) as [k0 [_ [Hz Hne]]].
  { rewrite N2Nat.id. exact Hi. }
  assert (Hk0 : gs x k0 = 0) by (unfold gs; rewrite Hz; reflexivity).
  assert (Hbefore : forall j, j < k0 -> gs x j <> 0).
  { intros j Hj H. apply (Hne j Hj). unfold gs in H. lia. }
  destruct (beta_exists (entry x k0) (Lc x k0)) as [c [d Hcd]].
  exists (k0 + Mc x k0 + c + d). apply sat_goodstein_θ.
  exists k0. split; [lia|]. exists (Mc x k0). split; [lia|].
  exists c. split; [lia|]. exists d. split; [lia|].
  apply check_true; assumption.
Qed.

Theorem goodstein_θ_sound x y : sat (scons y (scons x ρ0)) goodstein_θ ->
  exists k, k <= y /\ goodstein_sequence (N.of_nat x) (N.of_nat k) = 0%N.
Proof.
  intro H. apply sat_goodstein_θ in H as [k [Hk [M [_ [c [_ [d [_ Hc]]]]]]]].
  exists k. split; [exact Hk | apply (check_sound x k M c d Hc)].
Qed.

(** ** Goodstein's theorem: true, and independent of PA *)

Theorem goodstein_sentence_true : sat ρ0 goodstein_sentence.
Proof.
  intro x. destruct (goodstein_θ_true x) as [y Hy]. exists y. exact Hy.
Qed.

Theorem goodstein_independent : ~ PA [] goodstein_sentence.
Proof.
  apply goodstein_unprovable; [exact isD_goodstein_θ | exact isD_goodstein_Ex | exact goodstein_θ_sound].
Qed.
