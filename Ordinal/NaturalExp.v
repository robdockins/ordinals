From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import NaturalArith.
From Ordinal Require Import NaturalProduct.

From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Open Scope ord_scope.

(** * There is no natural exponentiation

  There is no operation [e(α,β)] on the ordinals satisfying

    (1) [e(α,1) = α],
    (2) [e(α,β)] weakly increasing in [β], for [α > 1],
    (3) [e(α,β)] weakly increasing in [α], for [β > 0],
    (4) [e(α, β ⊕ γ) = e(α,β) ⊗ e(α,γ)],
    (5) [e(α, β ⊗ γ) = e(e(α,β), γ)],

  where [⊕] and [⊗] are the natural (Hessenberg) sum and product
  ([natural_exp_impossible]).  This is Altman's theorem ("Intermediate
  arithmetic operations on ordinal numbers", MLQ 63, 2017, Theorem 4.1),
  with slightly weaker monotonicity hypotheses: Altman assumes (2) for
  [α > 0] and (3) for all [β].  (The 2015 arXiv version, Appendix B,
  Theorem B.1, also assumed a degree law, which the published version
  drops.)  A version was proved independently by Asperó and Tsaprounis
  ("Long reals", J. Log. Anal. 10, 2018, Theorem 3.2 and Corollary 3.3).

  The proof splits into a constructive reduction and a classical lemma
  about ordinals that does not mention [e]:
  - constructively ([laws_log23_ratio]): (1) and (4) force
    [e(n,k) = n^k] for finite [n, k ≥ 1]; with (5) and the
    commutativity of [⊗], [e(n^k, ω) = e(n,ω)^⊗k].  So [X = e(2,ω)] and
    [Y = e(3,ω)] satisfy [X ≥ ω] and, by (3), [X^⊗a ≤ Y^⊗k] whenever
    [2^a ≤ 3^k] and conversely ([log23_ratio]): their ⊗-logarithms are in
    the ratio [log₂ 3];
  - classically ([no_log23_ratio]), no ordinals are in that ratio:
    the leading exponents [D₂], [D₃] of [X], [Y] satisfy
    [D₂ ⊕ ... ⊕ D₂ ≤ D₃ ⊕ ... ⊕ D₃] ([a] and [k] copies) whenever
    [2^a ≤ 3^k], and conversely, with [D₂ > 0] since [X ≥ ω].  So [D₂]
    and [D₃] have the same leading exponent; with [c₂], [c₃] their
    leading coefficients, [2^a ≤ 3^k] gives [a·c₂ ≤ k·c₃], and
    [3^k ≤ 2^a] gives [k·c₃ ≤ a·c₂].  Since [3^c₂ ≠ 2^c₃] (parity), one
    of the two powers dominates, and a Bernoulli-type bound gives
    exponents for which these inequalities fail ([nat_no_ratio]).

  The finite products in the reduction are constructive because the
  finite ordinals form a universe with a decidable order
  ([nmul_nat_nat], via [nmulOrd_distrib_lower_Q]).

  The classical part follows Altman's proof, which also works with the
  leading coefficient of the leading exponent of [e(n,ω)]; the endgame
  here replaces his logarithms by a parity and Bernoulli argument.  The
  ratio lemma [no_log23_ratio] also implies Asperó and Tsaprounis's
  Theorem 3.2 (no monotone [f : ω → Ord] with [f(2) ≥ ω] and
  [f(n·m) = f(n) ⊗ f(m)]): take [X = f(2)] and [Y = f(3)].

  Since the conclusion is a negation, double-negated excluded middle
  suffices ([natural_exp_impossible_nn]); see the remark there on why no
  reverse result to weak excluded middle is possible.  Whether the
  theorem holds outright reduces to whether [no_log23_ratio] does.

  The natural product here is [NaturalProduct.nmulOrd] (not the
  [⊗] of [NaturalArith.v]).  All operations are compared up to [≈]. *)

(** ** Finite arithmetic *)

Fixpoint npow (k:nat) (x:Ord) : Ord :=
  match k with
  | O => 1
  | S k => nmulOrd (npow k x) x
  end.

Lemma npow_mono k x y : x ≤ y -> npow k x ≤ npow k y.
Proof.
  intro H. induction k; simpl; [reflexivity|].
  apply nmulOrd_monotone; auto.
Qed.

Add Parametric Morphism k : (npow k) with signature
    ord_eq ==> ord_eq as npow_eq_mor.
Proof. intros x y [H1 H2]. split; apply npow_mono; auto. Qed.

Lemma nadd_nat m n : natOrdSize m ⊕ natOrdSize n ≈ natOrdSize (m + n).
Proof.
  induction n; simpl.
  - rewrite naddOrd_zero_r. rewrite Nat.add_0_r. reflexivity.
  - rewrite naddOrd_succ2. rewrite IHn.
    replace (m + S n)%nat with (S (m + n)) by lia. reflexivity.
Qed.

Lemma nrep_nat k m : nrep k (natOrdSize m) ≈ natOrdSize (k * m).
Proof.
  induction k; simpl; [reflexivity|].
  rewrite IHk. rewrite nadd_nat.
  replace (k * m + m)%nat with (m + k * m)%nat by lia. reflexivity.
Qed.

Lemma nrep_add a b x : nrep (a + b) x ≈ nrep a x ⊕ nrep b x.
Proof.
  induction b; simpl.
  - rewrite Nat.add_0_r. rewrite naddOrd_zero_r. reflexivity.
  - replace (a + S b)%nat with (S (a + b)) by lia. simpl.
    rewrite IHb. rewrite naddOrd_assoc. reflexivity.
Qed.

Lemma nrep_nadd k x y : nrep k (x ⊕ y) ≈ nrep k x ⊕ nrep k y.
Proof.
  induction k; simpl.
  - rewrite naddOrd_zero_r. reflexivity.
  - rewrite IHk.
    rewrite <- !naddOrd_assoc. apply naddOrd_eq_mor; [reflexivity|].
    rewrite !naddOrd_assoc. apply naddOrd_eq_mor; [|reflexivity].
    apply naddOrd_comm.
Qed.

Lemma nrep_nrep k c x : nrep k (nrep c x) ≈ nrep (k * c) x.
Proof.
  induction k; simpl; [reflexivity|].
  rewrite IHk. rewrite <- nrep_add.
  replace (k * c + c)%nat with (c + k * c)%nat by lia. reflexivity.
Qed.

Lemma nrep_count_le a b x : (a <= b)%nat -> nrep a x ≤ nrep b x.
Proof.
  intro H. replace b with (a + (b - a))%nat by lia.
  rewrite nrep_add. rewrite <- (naddOrd_zero_r (nrep a x)) at 1.
  apply naddOrd_monotone; auto with ord.
Qed.

(** ** The arithmetic endgame *)

Section arith.
Local Open Scope nat_scope.

Lemma bernoulli x m : x ^ m * (x + m) <= x * (x + 1) ^ m.
Proof.
  induction m; simpl; [lia|].
  set (p := x ^ m) in *. set (q := (x + 1) ^ m) in *.
  assert (H1 : x * p * (x + S m) <= (x + 1) * (p * (x + m))) by nia.
  assert (H2 : (x + 1) * (p * (x + m)) <= (x + 1) * (x * q)).
  { apply Nat.mul_le_mono_l. exact IHm. }
  nia.
Qed.

Lemma pow_gap x y : (1 <= x)%nat -> (x < y)%nat ->
  exists m, (1 <= m)%nat /\ (3 * x ^ m <= y ^ m)%nat.
Proof.
  intros Hx Hxy. exists (2 * x)%nat. split; [lia|].
  pose proof (bernoulli x (2 * x)) as Hb.
  apply Nat.le_trans with ((x + 1) ^ (2 * x))%nat.
  - apply (Nat.mul_le_mono_pos_l _ _ x); [lia|]. nia.
  - apply Nat.pow_le_mono_l. lia.
Qed.

Lemma pow3_ne_pow2 c2 c3 : (0 < c2)%nat -> (0 < c3)%nat -> 3 ^ c2 <> 2 ^ c3.
Proof.
  intros H2 H3 Heq.
  assert (E : Nat.even (3 ^ c2) = Nat.even (2 ^ c3)) by (rewrite Heq; auto).
  rewrite !Nat.even_pow in E by lia. discriminate.
Qed.

(** No positive integers [c₂], [c₃] can satisfy both
    [2^a ≤ 3^k → a·c₂ ≤ k·c₃] and [3^k ≤ 2^a → k·c₃ ≤ a·c₂]: they would
    force [c₃/c₂ = log₂ 3]. *)
Lemma nat_no_ratio c2 c3 : (0 < c2)%nat -> (0 < c3)%nat ->
  (forall a k, (1 <= a)%nat -> (1 <= k)%nat -> (2 ^ a <= 3 ^ k)%nat -> (a * c2 <= k * c3)%nat) ->
  (forall a k, (1 <= a)%nat -> (1 <= k)%nat -> (3 ^ k <= 2 ^ a)%nat -> (k * c3 <= a * c2)%nat) ->
  False.
Proof.
  intros Hc2 Hc3 Hup Hdown.
  assert (P2 : (1 <= 2 ^ c3)%nat) by (pose proof (Nat.pow_nonzero 2 c3); lia).
  assert (P3 : (1 <= 3 ^ c2)%nat) by (pose proof (Nat.pow_nonzero 3 c2); lia).
  destruct (lt_eq_lt_dec (2 ^ c3) (3 ^ c2)) as [[Hlt|Heq]|Hgt].
  - destruct (pow_gap _ _ P2 Hlt) as [m [Hm Hg]].
    rewrite <- !Nat.pow_mul_r in Hg.
    assert (H : (2 ^ S (c3 * m) <= 3 ^ (c2 * m))%nat).
    { rewrite Nat.pow_succ_r'. lia. }
    apply Hup in H; nia.
  - apply (pow3_ne_pow2 c2 c3); auto.
  - destruct (pow_gap _ _ P3 Hgt) as [m [Hm Hg]].
    rewrite <- !Nat.pow_mul_r in Hg.
    assert (H : (3 ^ S (c2 * m) <= 2 ^ (c3 * m))%nat).
    { rewrite Nat.pow_succ_r'. lia. }
    apply Hdown in H; nia.
Qed.

End arith.

(** ** Finite products, constructively

  On the universe of finite ordinals, which has a decidable order and is
  closed under natural sums, the lower half of distributivity holds
  constructively ([nmulOrd_distrib_lower_Q]); with the constructive upper
  half of the successor law, this gives [m ⊗ k ≈ m·k]. *)

Definition QN (x:Ord) : Prop := exists n, x ≈ natOrdSize n.

Lemma QN_eq x y : x ≈ y -> QN x -> QN y.
Proof. intros H [n Hn]. exists n. rewrite <- H. auto. Qed.

Lemma QN_dec x y : QN x -> QN y -> x < y \/ y ≤ x.
Proof.
  intros [m Hm] [n Hn]. rewrite Hm, Hn.
  destruct (le_lt_dec n m) as [H|H].
  - right. apply natOrdSize_monotone; auto.
  - left. apply natOrdSize_increasing; auto.
Qed.

Lemma QN_zero : QN 0.
Proof. exists 0%nat. reflexivity. Qed.

Lemma QN_nadd x y : QN x -> QN y -> QN (x ⊕ y).
Proof. intros [m Hm] [n Hn]. exists (m + n)%nat. rewrite Hm, Hn. apply nadd_nat. Qed.

Lemma QH_nat n : QH QN (natOrdSize n).
Proof.
  induction n as [|n IH]; split.
  - apply QN_zero.
  - intros [].
  - exists (S n). reflexivity.
  - intros _. exact IH.
Qed.

Lemma nmul_succ_nat m k :
  nmulOrd (natOrdSize m) (succOrd (natOrdSize k)) ≈
  nmulOrd (natOrdSize m) (natOrdSize k) ⊕ natOrdSize m.
Proof.
  split; [apply nmulOrd_succ_upper|].
  transitivity (nmulOrd (natOrdSize m) (natOrdSize k) ⊕ nmulOrd (natOrdSize m) 1).
  { apply naddOrd_monotone; [reflexivity | apply (nmulOrd_one (natOrdSize m))]. }
  transitivity (nmulOrd (natOrdSize m) (natOrdSize k ⊕ 1)).
  { apply (nmulOrd_distrib_lower_Q QN QN_eq QN_dec QN_zero);
      [apply (QH_nat m) | apply (QH_nat k) | apply (QH_nat 1)]. }
  apply nmulOrd_monotone; [reflexivity|].
  rewrite naddOrd_succ2, naddOrd_zero_r. reflexivity.
Qed.

Lemma nmul_nat_nat m k : nmulOrd (natOrdSize m) (natOrdSize k) ≈ nrep k (natOrdSize m).
Proof.
  induction k; simpl.
  - apply nmulOrd_zero.
  - rewrite nmul_succ_nat, IHk. reflexivity.
Qed.

Lemma npow_nat k m : npow k (natOrdSize m) ≈ natOrdSize (m ^ k).
Proof.
  induction k; simpl; [reflexivity|].
  rewrite IHk. rewrite nmul_nat_nat. rewrite nrep_nat.
  rewrite Nat.mul_comm. reflexivity.
Qed.

Lemma npow_one x : npow 1 x ≈ x.
Proof. simpl. rewrite nmulOrd_comm. apply nmulOrd_one. Qed.

(** ** The laws *)

Definition natural_exp_laws (e : Ord -> Ord -> Ord) : Prop :=
  (forall a, e a 1 ≈ a) /\
  (forall a b b', 1 < a -> b ≤ b' -> e a b ≤ e a b') /\
  (forall a a' b, 0 < b -> a ≤ a' -> e a b ≤ e a' b) /\
  (forall a b c, e a (b ⊕ c) ≈ nmulOrd (e a b) (e a c)) /\
  (forall a b c, e a (nmulOrd b c) ≈ e (e a b) c).

(** [X] and [Y] behave as if [Y = X^(log₂ 3)] for the natural product:
    [X^⊗a ≤ Y^⊗k] whenever [2^a ≤ 3^k], and conversely. *)
Definition log23_ratio (X Y:Ord) : Prop :=
  ω ≤ X /\
  (forall a k, (2 ^ S a <= 3 ^ S k)%nat -> npow (S a) X ≤ npow (S k) Y) /\
  (forall a k, (3 ^ S k <= 2 ^ S a)%nat -> npow (S k) Y ≤ npow (S a) X).

(** The laws restricted to a class [D] of ordinals, e.g. the ordinals
    denoted by a notation system. *)
Definition natural_exp_laws_on (D:Ord -> Prop) (e : Ord -> Ord -> Ord) : Prop :=
  (forall a, D a -> e a 1 ≈ a) /\
  (forall a b b', D a -> D b -> D b' -> 1 < a -> b ≤ b' -> e a b ≤ e a b') /\
  (forall a a' b, D a -> D a' -> D b -> 0 < b -> a ≤ a' -> e a b ≤ e a' b) /\
  (forall a b c, D a -> D b -> D c -> e a (b ⊕ c) ≈ nmulOrd (e a b) (e a c)) /\
  (forall a b c, D a -> D b -> D c -> e a (nmulOrd b c) ≈ e (e a b) c).

(** The closure properties of [D] that the reduction uses: [D] contains
    the natural numbers and [ω], is closed under the natural operations,
    and [e] maps [D] to itself. *)
Definition exp_domain (D:Ord -> Prop) (e : Ord -> Ord -> Ord) : Prop :=
  (forall n, D (natOrdSize n)) /\ D ω /\
  (forall x y, D x -> D y -> D (x ⊕ y)) /\
  (forall x y, D x -> D y -> D (nmulOrd x y)) /\
  (forall a b, D a -> D b -> D (e a b)).

Lemma natural_exp_laws_on_all e : natural_exp_laws e -> natural_exp_laws_on (fun _ => True) e.
Proof.
  intros [H1 [H2 [H3 [H4 H5]]]].
  exact (conj (fun a _ => H1 a) (conj (fun a b b' _ _ _ => H2 a b b')
    (conj (fun a a' b _ _ _ => H3 a a' b) (conj (fun a b c _ _ _ => H4 a b c)
      (fun a b c _ _ _ => H5 a b c))))).
Qed.

Lemma exp_domain_all e : exp_domain (fun _ => True) e.
Proof. exact (conj (fun _ => I) (conj I (conj (fun _ _ _ _ => I) (conj (fun _ _ _ _ => I) (fun _ _ _ _ => I))))). Qed.

Lemma log23_ratio_eq X X' Y Y' : X ≈ X' -> Y ≈ Y' -> log23_ratio X Y -> log23_ratio X' Y'.
Proof.
  intros HX HY [H0 [Hup Hdown]]. split; [|split].
  - rewrite <- HX. auto.
  - intros a k H. rewrite <- (npow_eq_mor _ _ _ HX), <- (npow_eq_mor _ _ _ HY). auto.
  - intros a k H. rewrite <- (npow_eq_mor _ _ _ HX), <- (npow_eq_mor _ _ _ HY). auto.
Qed.

Section laws.
Variable D : Ord -> Prop.
Variable e : Ord -> Ord -> Ord.
Hypothesis HD : exp_domain D e.
Hypothesis He : natural_exp_laws_on D e.

Let Dnat : forall n, D (natOrdSize n) := proj1 HD.
Let Domega : D ω := proj1 (proj2 HD).
Let Dnadd : forall x y, D x -> D y -> D (x ⊕ y) := proj1 (proj2 (proj2 HD)).
Let Dnmul : forall x y, D x -> D y -> D (nmulOrd x y) := proj1 (proj2 (proj2 (proj2 HD))).
Let De : forall a b, D a -> D b -> D (e a b) := proj2 (proj2 (proj2 (proj2 HD))).

Let H1 : forall a, D a -> e a 1 ≈ a := proj1 He.
Let H2 : forall a b b', D a -> D b -> D b' -> 1 < a -> b ≤ b' -> e a b ≤ e a b' :=
  proj1 (proj2 He).
Let H3 : forall a a' b, D a -> D a' -> D b -> 0 < b -> a ≤ a' -> e a b ≤ e a' b :=
  proj1 (proj2 (proj2 He)).
Let H4 : forall a b c, D a -> D b -> D c -> e a (b ⊕ c) ≈ nmulOrd (e a b) (e a c) :=
  proj1 (proj2 (proj2 (proj2 He))).
Let H5 : forall a b c, D a -> D b -> D c -> e a (nmulOrd b c) ≈ e (e a b) c :=
  proj2 (proj2 (proj2 (proj2 He))).

Lemma D_nrep k x : D x -> D (nrep k x).
Proof. intro Hx. induction k; simpl; [exact (Dnat 0) | apply Dnadd; auto]. Qed.

Lemma e_eq2 a b b' : D a -> D b -> D b' -> 1 < a -> b ≈ b' -> e a b ≈ e a b'.
Proof. intros Da Db Db' Ha [Hb1 Hb2]. split; apply H2; auto. Qed.

Lemma e_eq1 a a' b : D a -> D a' -> D b -> 0 < b -> a ≈ a' -> e a b ≈ e a' b.
Proof. intros Da Da' Db Hb [Ha1 Ha2]. split; apply H3; auto. Qed.

Lemma e_nrep a k x : D a -> D x -> 1 < a -> e a (nrep (S k) x) ≈ npow (S k) (e a x).
Proof.
  intros Da Dx Ha. induction k.
  - simpl. rewrite (e_eq2 a _ x Da (Dnadd _ _ (Dnat 0) Dx) Dx Ha (naddOrd_zero_l x)).
    rewrite nmulOrd_comm. rewrite nmulOrd_one. reflexivity.
  - change (nrep (S (S k)) x) with (nrep (S k) x ⊕ x).
    rewrite H4; [|auto | apply D_nrep; auto | auto]. rewrite IHk. reflexivity.
Qed.

Lemma e_nat a k : D a -> 1 < a -> e a (natOrdSize (S k)) ≈ npow (S k) a.
Proof.
  intros Da Ha.
  assert (Hk : natOrdSize (S k) ≈ nrep (S k) 1).
  { rewrite (nrep_nat (S k) 1). rewrite Nat.mul_1_r. reflexivity. }
  rewrite (e_eq2 a _ _ Da (Dnat _) (D_nrep _ _ (Dnat 1)) Ha Hk).
  rewrite (e_nrep a k 1 Da (Dnat 1) Ha).
  rewrite (H1 a Da). reflexivity.
Qed.

Lemma e_omega_ge n : 1 < natOrdSize n -> ω ≤ e (natOrdSize n) ω.
Proof.
  intro Hn. rewrite ord_le_unfold. intro k. simpl.
  apply ord_lt_le_trans with (e (natOrdSize n) (natOrdSize (S k))).
  - rewrite e_nat; auto. rewrite npow_nat.
    apply natOrdSize_increasing.
    assert (H2n : (2 <= n)%nat).
    { destruct (le_lt_dec n 1) as [Hle|Hlt]; [|lia].
      elim (ord_lt_irreflexive 1). apply ord_lt_le_trans with (natOrdSize n); auto.
      apply (natOrdSize_monotone n 1); auto. }
    clear Hn. induction k; simpl; [lia|].
    simpl in IHk. nia.
  - apply H2; auto. apply ord_lt_le. apply (index_lt ω (S k)).
Qed.

Lemma e_pow_omega n k : 1 < natOrdSize n ->
  e (natOrdSize (n ^ S k)) ω ≈ npow (S k) (e (natOrdSize n) ω).
Proof.
  intro Hn.
  assert (HX : 1 < e (natOrdSize n) ω).
  { apply ord_lt_le_trans with ω; [apply omega_gt1 | apply e_omega_ge; auto]. }
  rewrite <- (e_eq1 (e (natOrdSize n) (natOrdSize (S k))) _ ω (De _ _ (Dnat _) (Dnat _))
                (Dnat _) Domega omega_gt0).
  2: { rewrite e_nat; auto. apply npow_nat. }
  rewrite <- H5; auto.
  rewrite (e_eq2 _ _ (nmulOrd ω (natOrdSize (S k))) (Dnat _) (Dnmul _ _ (Dnat _) Domega)
             (Dnmul _ _ Domega (Dnat _)) Hn (nmulOrd_comm _ _)).
  rewrite H5; auto.
  apply e_nat; auto.
Qed.

(** Constructively, the laws put [e(2,ω)] and [e(3,ω)] in the ratio
    [log₂ 3]. *)
Theorem laws_log23_ratio_on : log23_ratio (e (natOrdSize 2) ω) (e (natOrdSize 3) ω).
Proof.
  assert (H12 : 1 < natOrdSize 2) by apply succ_lt.
  assert (H13 : 1 < natOrdSize 3).
  { apply ord_lt_le_trans with (natOrdSize 2); auto. apply natOrdSize_monotone. lia. }
  split; [apply e_omega_ge; auto|]. split; intros a k H.
  - rewrite <- (e_pow_omega 2 a H12), <- (e_pow_omega 3 k H13).
    apply H3; auto; [apply omega_gt0 | apply natOrdSize_monotone; auto].
  - rewrite <- (e_pow_omega 2 a H12), <- (e_pow_omega 3 k H13).
    apply H3; auto; [apply omega_gt0 | apply natOrdSize_monotone; auto].
Qed.

End laws.

(** Constructively, the laws put [e(2,ω)] and [e(3,ω)] in the ratio
    [log₂ 3]. *)
Theorem laws_log23_ratio e :
  natural_exp_laws e -> log23_ratio (e (natOrdSize 2) ω) (e (natOrdSize 3) ω).
Proof.
  intro He.
  exact (laws_log23_ratio_on _ e (exp_domain_all e) (natural_exp_laws_on_all e He)).
Qed.

Section classical.
Variable EM : excluded_middle.

Let cpl x : complete x := classical.ord_complete EM x.

(** ** Leading exponents

  [has_deg δ x]: [x] lies in [[ω^δ, ω^(δ+1))], i.e. [δ] is the leading
  exponent of the Cantor normal form of [x]. *)

Definition has_deg (δ x:Ord) : Prop :=
  expOrd ω δ ≤ x /\ exists n, x < nrep n (expOrd ω δ).

Lemma has_deg_eq δ x x' : x ≈ x' -> has_deg δ x -> has_deg δ x'.
Proof.
  intros [H1 H2] [Hl [n Hu]]. split.
  - transitivity x; auto.
  - exists n. apply ord_le_lt_trans with x; auto.
Qed.

Lemma has_deg_eq_exp δ δ' x : δ ≈ δ' -> has_deg δ x -> has_deg δ' x.
Proof.
  intros Hδ [Hl [n Hu]]. split.
  - rewrite <- Hδ. auto.
  - exists n. rewrite <- Hδ. auto.
Qed.

Lemma exp_reflect a b : expOrd ω a < expOrd ω b -> a < b.
Proof.
  intro H. destruct (classical.order_total EM b a) as [Hba|Hab]; auto.
  elim (ord_lt_irreflexive (expOrd ω a)).
  apply ord_lt_le_trans with (expOrd ω b); auto. apply expOrd_monotone; auto.
Qed.

Lemma lt_succ_le a b : a < succOrd b -> a ≤ b.
Proof. intro H. rewrite ord_lt_unfold in H. destruct H as [u Hu]. exact Hu. Qed.

Lemma has_deg_le δ δ' x x' :
  has_deg δ x -> has_deg δ' x' -> x ≤ x' -> δ ≤ δ'.
Proof.
  intros [Hl _] [_ [n Hu]] Hxx'.
  apply lt_succ_le. apply exp_reflect.
  apply ord_le_lt_trans with x; auto.
  apply ord_le_lt_trans with x'; auto.
  apply ord_lt_le_trans with (nrep n (expOrd ω δ')); auto.
  apply ord_lt_le. apply nrep_below; auto. apply succ_lt.
Qed.

Lemma nrep_one x : nrep 1 x ≈ x.
Proof. simpl. apply naddOrd_zero_l. Qed.

Lemma nrep_lt_succ k x : 0 < x -> nrep k x < nrep (S k) x.
Proof.
  intro Hx. simpl. rewrite <- (naddOrd_zero_r (nrep k x)) at 1.
  apply naddOrd_increasing2. auto.
Qed.

Lemma zero_lt_cases x : 0 < x \/ x ≤ 0.
Proof.
  destruct (classical.order_total EM x 0) as [H|H]; auto.
Qed.

Lemma has_deg_exists x : 0 < x -> exists δ, has_deg δ x.
Proof.
  intro Hx.
  destruct (cantor_decomposition EM x) as [ls [Hls Hd]].
  destruct ls as [|y ys].
  - elim (ord_lt_irreflexive 0). apply ord_lt_le_trans with x; auto. apply Hd.
  - exists y. split.
    + rewrite <- Hd. simpl. apply addOrd_le1.
    + assert (Hb : x < expOrd ω (succOrd y)).
      { rewrite <- Hd. apply (cantor_below EM).
        intros a Ha. apply succ_trans.
        destruct Ha as [<-|Ha]; [reflexivity|].
        simpl in Hls. destruct Hls as [_ Hys].
        apply (cantor_sequence_le1 ys y Hys a Ha). }
      destruct (exp_below x (succOrd y) Hb) as [H|[i [k Hk]]].
      * exists 1%nat. rewrite nrep_one.
        apply ord_lt_le_trans with 1; auto.
        apply succ_least. apply expOrd_nonzero.
      * exists (S k). apply ord_le_lt_trans with (nrep k (expOrd ω y)); auto.
        apply nrep_lt_succ. apply expOrd_nonzero.
Qed.

Lemma has_deg_mul δ δ' x y :
  has_deg δ x -> has_deg δ' y -> has_deg (δ ⊕ δ') (nmulOrd x y).
Proof.
  intros [Hl [n Hu]] [Hl' [m Hu']]. split.
  - rewrite <- (nmulOrd_exp EM δ δ'). apply nmulOrd_monotone; auto.
  - exists (n * m)%nat.
    apply ord_le_lt_trans with (nmulOrd x (nrep m (expOrd ω δ'))).
    { apply nmulOrd_monotone; [reflexivity | apply ord_lt_le; auto]. }
    apply ord_lt_le_trans with (nmulOrd (nrep n (expOrd ω δ)) (nrep m (expOrd ω δ'))).
    { apply nmulOrd_increasing1; auto.
      apply ord_le_lt_trans with y; auto with ord. }
    rewrite (nmul_nrep_l EM). rewrite (nmulOrd_comm (expOrd ω δ)).
    rewrite (nmul_nrep_l EM). rewrite (nmulOrd_comm (expOrd ω δ')).
    rewrite (nmulOrd_exp EM). rewrite nrep_nrep. reflexivity.
Qed.

Lemma has_deg_npow k δ x : has_deg δ x -> has_deg (nrep k δ) (npow k x).
Proof.
  intro H. induction k.
  - simpl. split.
    + rewrite expOrd_zero. reflexivity.
    + exists 2%nat. rewrite expOrd_zero. rewrite (nrep_nat 2 1). simpl. apply succ_lt.
  - simpl. apply has_deg_mul; auto.
Qed.

(** ** Leading coefficients

  [has_lead γ c d]: [d = ω^γ·c + r] with [r < ω^γ] and [c > 0], using
  natural sums. *)

Definition has_lead (γ:Ord) (c:nat) (d:Ord) : Prop :=
  (0 < c)%nat /\ exists r, r < expOrd ω γ /\ d ≈ nrep c (expOrd ω γ) ⊕ r.

Lemma nrep_ge_one c x : (0 < c)%nat -> x ≤ nrep c x.
Proof.
  intro Hc. rewrite <- (nrep_one x) at 1. apply nrep_count_le. lia.
Qed.

Lemma lead_lower γ c d : has_lead γ c d -> nrep c (expOrd ω γ) ≤ d.
Proof.
  intros [_ [r [_ Hd]]]. rewrite Hd.
  rewrite <- (naddOrd_zero_r (nrep c (expOrd ω γ))) at 1.
  apply naddOrd_monotone; auto with ord.
Qed.

Lemma lead_deg γ c d : has_lead γ c d -> has_deg γ d.
Proof.
  intro H. split.
  - transitivity (nrep c (expOrd ω γ)); [apply nrep_ge_one; apply H | apply lead_lower; auto].
  - destruct H as [_ [r [Hr Hd]]]. exists (S c). rewrite Hd. simpl.
    apply naddOrd_increasing2; auto.
Qed.

Lemma nrep_lt_closed k γ r : r < expOrd ω γ -> nrep k r < expOrd ω γ.
Proof.
  intro Hr. induction k; simpl.
  - apply expOrd_nonzero.
  - apply nadd_closed; auto.
Qed.

Lemma lead_nrep γ c d k : has_lead γ c d -> has_lead γ (S k * c) (nrep (S k) d).
Proof.
  intros [Hc [r [Hr Hd]]]. split; [lia|].
  exists (nrep (S k) r). split; [apply nrep_lt_closed; auto|].
  rewrite Hd. rewrite nrep_nadd. rewrite nrep_nrep. reflexivity.
Qed.

Lemma cantor_nadd_below γ : forall suf,
  (forall a, In a suf -> a < γ) -> cantor_denote_nadd suf < expOrd ω γ.
Proof.
  induction suf as [|a suf IH]; simpl; intros H.
  - apply expOrd_nonzero.
  - apply nadd_closed; auto.
    apply expOrd_increasing; auto with ord.
Qed.

Lemma cantor_nadd_all_eq γ : forall pre,
  (forall a, In a pre -> a ≈ γ) ->
  cantor_denote_nadd pre ≈ nrep (length pre) (expOrd ω γ).
Proof.
  induction pre as [|a pre IH]; simpl; intros H; [reflexivity|].
  rewrite IH; auto. rewrite naddOrd_comm.
  apply naddOrd_eq_mor; [reflexivity|].
  apply expOrd_eq_mor; [reflexivity | apply H; auto].
Qed.

Lemma lead_exists d : 0 < d -> exists γ c, has_lead γ c d.
Proof.
  intro Hpos.
  destruct (cantor_decomposition EM d) as [ls [Hls Hd]].
  destruct ls as [|y ys].
  - elim (ord_lt_irreflexive 0). apply ord_lt_le_trans with d; auto. apply Hd.
  - destruct (cantor_split EM y (y::ys) d Hls) as [pre [suf [Heq [Hpre Hsuf]]]].
    assert (Hle : forall a, In a (y::ys) -> a ≤ y).
    { intros a [<-|Ha]; [reflexivity|].
      simpl in Hls. destruct Hls as [_ Hys].
      apply (cantor_sequence_le1 ys y Hys a Ha). }
    exists y, (length pre). split.
    + destruct pre as [|p pre]; simpl; [|lia].
      simpl in Heq. subst suf.
      elim (ord_lt_irreflexive y). apply Hsuf. simpl; auto.
    + exists (cantor_denote_nadd suf). split.
      * apply cantor_nadd_below; auto.
      * rewrite <- Hd.
        rewrite (cantor_denote_nadd_eq EM (y::ys) d (each_complete EM _) Hls).
        rewrite Heq. rewrite cantor_denote_nadd_app.
        apply naddOrd_eq_mor; [|reflexivity].
        apply cantor_nadd_all_eq.
        intros a Ha. split.
        -- apply Hle. rewrite Heq. apply in_or_app. auto.
        -- apply Hpre; auto.
Qed.

Lemma lead_le γ c d γ' c' d' :
  has_lead γ c d -> has_lead γ' c' d' -> d ≤ d' -> γ' ≤ γ -> (c <= c')%nat.
Proof.
  intros Hd Hd' Hle Hγ.
  destruct (le_lt_dec c c') as [|Hlt]; auto. exfalso.
  pose proof (lead_lower _ _ _ Hd) as Hlow.
  destruct Hd' as [_ [r' [Hr' Hd']]].
  apply (ord_lt_irreflexive (nrep (S c') (expOrd ω γ))).
  apply ord_le_lt_trans with (nrep c (expOrd ω γ)); [apply nrep_count_le; lia|].
  apply ord_le_lt_trans with d; auto.
  apply ord_le_lt_trans with d'; auto.
  rewrite Hd'. simpl.
  apply ord_lt_le_trans with (nrep c' (expOrd ω γ') ⊕ expOrd ω γ').
  - apply naddOrd_increasing2; auto.
  - apply naddOrd_monotone; [apply nrep_mono|]; apply expOrd_monotone; auto.
Qed.

(** ** The theorem *)

(** Classically, no ordinals are in the ratio [log₂ 3]. *)
Theorem no_log23_ratio X Y : ~ log23_ratio X Y.
Proof.
  intros [HX [Hup Hdown]].
  assert (HXY : X ≤ Y).
  { rewrite <- (npow_one X), <- (npow_one Y). apply (Hup 0%nat 0%nat). simpl; lia. }
  destruct (has_deg_exists X) as [δ2 Hδ2].
  { apply ord_lt_le_trans with ω; auto with ord. }
  destruct (has_deg_exists Y) as [δ3 Hδ3].
  { apply ord_lt_le_trans with ω; auto with ord. transitivity X; auto. }
  assert (Hmono : forall a k, (2 ^ S a <= 3 ^ S k)%nat -> nrep (S a) δ2 ≤ nrep (S k) δ3).
  { intros a k H.
    exact (has_deg_le _ _ _ _ (has_deg_npow (S a) δ2 X Hδ2) (has_deg_npow (S k) δ3 Y Hδ3)
             (Hup a k H)). }
  assert (Hmono' : forall a k, (3 ^ S k <= 2 ^ S a)%nat -> nrep (S k) δ3 ≤ nrep (S a) δ2).
  { intros a k H.
    exact (has_deg_le _ _ _ _ (has_deg_npow (S k) δ3 Y Hδ3) (has_deg_npow (S a) δ2 X Hδ2)
             (Hdown a k H)). }
  (* [δ2 > 0], since [X ≥ ω]. *)
  assert (Hδ2pos : 0 < δ2).
  { destruct (zero_lt_cases δ2) as [Hp|Hz]; auto. exfalso.
    destruct Hδ2 as [_ [n Hn]].
    apply (ord_lt_irreflexive ω).
    apply ord_le_lt_trans with X; auto.
    apply ord_lt_le_trans with (nrep n (expOrd ω δ2)); auto.
    rewrite Hz. rewrite expOrd_zero.
    rewrite (nrep_nat n 1). apply ord_lt_le. apply index_lt. }
  assert (Hδ23 : δ2 ≤ δ3) by exact (has_deg_le _ _ _ _ Hδ2 Hδ3 HXY).
  destruct (lead_exists δ2) as [γ2 [c2 Hl2]]; auto.
  destruct (lead_exists δ3) as [γ3 [c3 Hl3]].
  { apply ord_lt_le_trans with δ2; auto. }
  (* [δ2] and [δ3] have the same leading exponent. *)
  assert (Hγ23 : γ2 ≤ γ3).
  { exact (has_deg_le _ _ _ _ (lead_deg _ _ _ Hl2) (lead_deg _ _ _ Hl3) Hδ23). }
  assert (Hγ32 : γ3 ≤ γ2).
  { apply (has_deg_le _ _ _ _ (lead_deg _ _ _ Hl3) (lead_deg _ _ _ (lead_nrep _ _ _ 1 Hl2))).
    rewrite <- (nrep_one δ3). apply (Hmono' 1%nat 0%nat). simpl; lia. }
  apply (nat_no_ratio c2 c3); [apply Hl2 | apply Hl3 | |].
  - intros a k Ha Hk H.
    destruct a as [|a]; [lia|]. destruct k as [|k]; [lia|].
    exact (lead_le _ _ _ _ _ _ (lead_nrep _ _ _ a Hl2) (lead_nrep _ _ _ k Hl3)
             (Hmono a k H) Hγ32).
  - intros a k Ha Hk H.
    destruct a as [|a]; [lia|]. destruct k as [|k]; [lia|].
    exact (lead_le _ _ _ _ _ _ (lead_nrep _ _ _ k Hl3) (lead_nrep _ _ _ a Hl2)
             (Hmono' a k H) Hγ23).
Qed.

Theorem natural_exp_impossible : ~ exists e, natural_exp_laws e.
Proof.
  intros [e He]. exact (no_log23_ratio _ _ (laws_log23_ratio e He)).
Qed.

End classical.

(** ** Without excluded middle

  The conclusion is a negation, so excluded middle can be weakened to
  its double negation.  [~~excluded_middle] is not provable, but it holds
  in every finite Kripke model, since the maximal worlds are classical.
  So the theorem cannot imply weak excluded middle, or any other
  principle that some finite Kripke model refutes: in the model with a
  root and two incomparable leaves, one forcing [P] and one forcing
  [~P], [~~excluded_middle] holds at the root but [~P \/ ~~P] fails
  there.  Whether the theorem holds outright is open.  Since
  [laws_log23_ratio] is constructive, it would follow from a constructive
  proof of [no_log23_ratio], a statement about ordinals alone; a
  countermodel would have to refute [~~excluded_middle], so it would be
  infinitary. *)
Theorem natural_exp_impossible_nn :
  ~~excluded_middle -> ~ exists e, natural_exp_laws e.
Proof.
  intros HEM He. apply HEM. intro EM. exact (natural_exp_impossible EM He).
Qed.
