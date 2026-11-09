import ConstructiveOrdinals.NaturalProduct

/-!
# There is no natural exponentiation

Port of `Ordinal/NaturalExp.v`.

There is no operation `e(α,β)` on the ordinals satisfying

1. `e(α,1) = α`,
2. `e(α,β)` weakly increasing in `β`, for `α > 1`,
3. `e(α,β)` weakly increasing in `α`, for `β > 0`,
4. `e(α, β ♯ γ) = e(α,β) ⊗ e(α,γ)`,
5. `e(α, β ⊗ γ) = e(e(α,β), γ)`,

where `♯` and `⊗` are the natural (Hessenberg) sum and product
(`natural_exp_impossible`). This is Altman's theorem ("Intermediate arithmetic
operations on ordinal numbers", MLQ 63, 2017, Theorem 4.1), with slightly
weaker monotonicity hypotheses: Altman assumes (2) for `α > 0` and (3) for all
`β`. (The 2015 arXiv version, Appendix B, Theorem B.1, also assumed a degree
law, which the published version drops.) A version was proved independently by
Asperó and Tsaprounis ("Long reals", J. Log. Anal. 10, 2018, Theorem 3.2 and
Corollary 3.3).

The proof splits into a constructive reduction and a classical lemma about
ordinals that does not mention `e`:
- constructively (`laws_log23_ratio`): (1) and (4) force `e(n,k) = n^k` for
  finite `n, k ≥ 1`; with (5) and the commutativity of `⊗`,
  `e(n^k, ω) = e(n,ω)^⊗k`. So `X = e(2,ω)` and `Y = e(3,ω)` satisfy `X ≥ ω`
  and, by (3), `X^⊗a ≤ Y^⊗k` whenever `2^a ≤ 3^k` and conversely
  (`Log23Ratio`): their ⊗-logarithms are in the ratio `log₂ 3`;
- classically (`no_log23_ratio`), no ordinals are in that ratio: the leading
  exponents `D₂`, `D₃` of `X`, `Y` satisfy `a·D₂ ≤ k·D₃` (natural multiples)
  whenever `2^a ≤ 3^k`, and conversely, with `D₂ > 0`. So `D₂` and `D₃` have
  the same leading exponent; with `c₂`, `c₃` their leading coefficients,
  `2^a ≤ 3^k` gives `a·c₂ ≤ k·c₃`, and `3^k ≤ 2^a` gives `k·c₃ ≤ a·c₂`. Since
  `3^c₂ ≠ 2^c₃` (parity), one of the two powers dominates, and a
  Bernoulli-type bound gives exponents for which these inequalities fail
  (`nat_no_ratio`).

The finite products in the reduction are constructive because the finite
ordinals form a universe with a decidable order (`nmul_nat_nat`, via
`nmul_distrib_lower_Q`).

Since the conclusion is a negation, double-negated excluded middle suffices
(`natural_exp_impossible_nn`). Whether the theorem holds outright reduces to
whether `no_log23_ratio` does.

Lean notes:
- The natural-number arithmetic is done by hand, with local axiom-free
  versions of `Nat.mul_assoc`, `Nat.right_distrib` and `Nat.pow_mul`, and a
  parity argument without `%`.
-/

namespace ConstructiveOrdinals.NaturalExp

open Ordinal NaturalProduct

universe u

/-! ## Natural-number arithmetic -/

private theorem mul_assoc' (a b : Nat) : ∀ c, a * b * c = a * (b * c)
  | 0 => rfl
  | c + 1 => by
    show a * b * c + a * b = a * (b * c + b)
    rw [Nat.left_distrib, mul_assoc' a b c]

private theorem right_distrib' (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm, Nat.left_distrib, Nat.mul_comm c a, Nat.mul_comm c b]

private theorem pow_add' (a m : Nat) : ∀ n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => (Nat.mul_one _).symm
  | n + 1 => by
    show a ^ (m + n) * a = a ^ m * (a ^ n * a)
    rw [pow_add' a m n, mul_assoc']

private theorem pow_mul' (a b : Nat) : ∀ c, a ^ (b * c) = (a ^ b) ^ c
  | 0 => rfl
  | c + 1 => by
    show a ^ (b * c + b) = (a ^ b) ^ c * a ^ b
    rw [pow_add', pow_mul' a b c]

/-- Rocq: `NaturalExp.bernoulli`. -/
theorem bernoulli (x : Nat) : ∀ m, x ^ m * (x + m) ≤ x * (x + 1) ^ m
  | 0 => by
    show 1 * x ≤ x * 1
    rw [Nat.one_mul, Nat.mul_one]
    exact Nat.le_refl x
  | m + 1 =>
    calc x ^ (m + 1) * (x + (m + 1))
        = x ^ m * (x * (x + m) + x) := mul_assoc' (x ^ m) x (x + m + 1)
      _ ≤ x ^ m * (x * (x + m) + (x + m)) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_add_right x m) _)
      _ = x ^ m * ((x + m) * (x + 1)) := by rw [Nat.mul_comm x (x + m)]; rfl
      _ = x ^ m * (x + m) * (x + 1) := (mul_assoc' _ _ _).symm
      _ ≤ x * (x + 1) ^ m * (x + 1) := Nat.mul_le_mul_right _ (bernoulli x m)
      _ = x * (x + 1) ^ (m + 1) := mul_assoc' _ _ _

/-- The Rocq statement has `3 * x ^ m`; here `x ^ m + x ^ m + x ^ m`.
Rocq: `NaturalExp.pow_gap`. -/
theorem pow_gap (x y : Nat) (hx : 1 ≤ x) (hxy : x < y) :
    ∃ m, 1 ≤ m ∧ x ^ m + x ^ m + x ^ m ≤ y ^ m := by
  refine ⟨x + x, Nat.le_trans hx (Nat.le_add_right x x), ?_⟩
  have hb := bernoulli x (x + x)
  have e : x ^ (x + x) * (x + (x + x)) = x * (x ^ (x + x) + (x ^ (x + x) + x ^ (x + x))) := by
    rw [Nat.left_distrib, Nat.left_distrib, Nat.left_distrib, Nat.left_distrib,
      Nat.mul_comm (x ^ (x + x)) x]
  rw [e] at hb
  have h3 := Nat.le_of_mul_le_mul_left hb hx
  rw [← Nat.add_assoc] at h3
  exact Nat.le_trans h3 (Nat.pow_le_pow_left hxy _)

private theorem two_mul_ne (a : Nat) : ∀ b, 2 * a ≠ 2 * b + 1 := by
  induction a with
  | zero => intro b h; exact Nat.noConfusion h
  | succ a ih =>
    intro b h
    cases b with
    | zero => exact Nat.noConfusion (Nat.succ.inj h)
    | succ b => exact ih b (Nat.succ.inj (Nat.succ.inj h))

private theorem three_pow_odd : ∀ c, ∃ k, 3 ^ c = 2 * k + 1
  | 0 => ⟨0, rfl⟩
  | c + 1 => by
    obtain ⟨k, hk⟩ := three_pow_odd c
    refine ⟨3 * k + 1, ?_⟩
    show 3 ^ c * 3 = 2 * (3 * k + 1) + 1
    rw [hk, Nat.mul_comm, Nat.left_distrib, Nat.left_distrib, ← mul_assoc' 3 2 k,
      ← mul_assoc' 2 3 k]

/-- Rocq: `NaturalExp.pow3_ne_pow2`. -/
theorem pow3_ne_pow2 (c2 c3 : Nat) (_h2 : 0 < c2) (h3 : 0 < c3) : 3 ^ c2 ≠ 2 ^ c3 := by
  intro heq
  obtain ⟨k, hk⟩ := three_pow_odd c2
  cases c3 with
  | zero => exact Nat.lt_irrefl 0 h3
  | succ d =>
    have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := Nat.mul_comm _ _
    exact two_mul_ne (2 ^ d) k (h2 ▸ heq ▸ hk)

private theorem lin_contra {p q r : Nat} (hq : 0 < q) (h : (p + 1) * q ≤ r) (e : r = p * q) :
    False := by
  rw [e, right_distrib', Nat.one_mul] at h
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hq) h)

private theorem comm3 (a m b : Nat) : a * m * b = b * m * a := by
  rw [mul_assoc', Nat.mul_comm a, Nat.mul_comm b m]

/-- No positive integers `c₂`, `c₃` can satisfy both `2^a ≤ 3^k → a·c₂ ≤ k·c₃`
and `3^k ≤ 2^a → k·c₃ ≤ a·c₂`: they would force `c₃/c₂ = log₂ 3`.
Rocq: `NaturalExp.nat_no_ratio`. -/
theorem nat_no_ratio (c2 c3 : Nat) (hc2 : 0 < c2) (hc3 : 0 < c3)
    (hup : ∀ a k, 1 ≤ a → 1 ≤ k → 2 ^ a ≤ 3 ^ k → a * c2 ≤ k * c3)
    (hdown : ∀ a k, 1 ≤ a → 1 ≤ k → 3 ^ k ≤ 2 ^ a → k * c3 ≤ a * c2) : False := by
  have P2 : 1 ≤ 2 ^ c3 := Nat.pow_pos (Nat.zero_lt_succ 1)
  have P3 : 1 ≤ 3 ^ c2 := Nat.pow_pos (Nat.zero_lt_succ 2)
  rcases Nat.lt_trichotomy (2 ^ c3) (3 ^ c2) with hlt | heq | hgt
  · obtain ⟨m, hm, hg⟩ := pow_gap _ _ P2 hlt
    rw [← pow_mul', ← pow_mul'] at hg
    have H : 2 ^ (c3 * m + 1) ≤ 3 ^ (c2 * m) := by
      show 2 ^ (c3 * m) * 2 ≤ _
      rw [Nat.mul_two]
      exact Nat.le_trans (Nat.le_add_right _ _) hg
    exact lin_contra hc2 (hup _ _ (Nat.le_add_left 1 _) (Nat.mul_le_mul hc2 hm) H)
      (comm3 c2 m c3)
  · exact pow3_ne_pow2 c2 c3 hc2 hc3 heq.symm
  · obtain ⟨m, hm, hg⟩ := pow_gap _ _ P3 hgt
    rw [← pow_mul', ← pow_mul'] at hg
    have H : 3 ^ (c2 * m + 1) ≤ 2 ^ (c3 * m) := by
      show 3 ^ (c2 * m) * 3 ≤ _
      rw [Nat.mul_succ, Nat.mul_two]
      exact hg
    exact lin_contra hc3 (hdown _ _ (Nat.mul_le_mul hc3 hm) (Nat.le_add_left 1 _) H)
      (comm3 c3 m c2)

/-! ## Finite arithmetic on ordinals -/

/-- Natural powers `x^⊗k`. Rocq: `NaturalExp.npow`. -/
def npow : Nat → Ordinal.{u} → Ordinal.{u}
  | 0, _ => 1
  | k + 1, x => nmul (npow k x) x

/-- Rocq: `NaturalExp.npow_mono`. -/
theorem npow_mono : ∀ (k : Nat) {x y : Ordinal.{u}}, x ≤ y → npow k x ≤ npow k y
  | 0, _, _, _ => le_refl _
  | k + 1, _, _, h => nmul_monotone (npow_mono k h) h

/-- Rocq: `NaturalExp.npow_eq_mor`. -/
theorem npow_congr (k : Nat) {x y : Ordinal.{u}} (h : x ≈ y) : npow k x ≈ npow k y :=
  equiv_intro (npow_mono k h.le) (npow_mono k h.ge)

/-- Rocq: `NaturalExp.nadd_nat`. -/
theorem nadd_nat (m : Nat) : ∀ n, ofNat.{u} m ♯ ofNat n ≈ ofNat (m + n)
  | 0 => nadd_zero_r _
  | n + 1 => equiv_trans (nadd_succ2 _ _) (succ_congruence (nadd_nat m n))

/-- Rocq: `NaturalExp.nrep_nat`. -/
theorem nrep_nat : ∀ (k m : Nat), nrep k (ofNat.{u} m) ≈ ofNat (k * m)
  | 0, m => by rw [Nat.zero_mul]; exact equiv_refl _
  | k + 1, m => by
    rw [Nat.add_one_mul]
    exact equiv_trans (nadd_congr (nrep_nat k m) (equiv_refl _)) (nadd_nat _ _)

/-- Rocq: `NaturalExp.nrep_add`. -/
theorem nrep_add (a b : Nat) (x : Ordinal.{u}) : nrep (a + b) x ≈ nrep a x ♯ nrep b x := by
  induction b with
  | zero => exact equiv_symm (nadd_zero_r _)
  | succ b ih =>
    exact equiv_trans (nadd_congr ih (equiv_refl x)) (equiv_symm (nadd_assoc _ _ _))

/-- Rocq: `NaturalExp.nrep_nadd`. -/
theorem nrep_nadd : ∀ (k : Nat) (x y : Ordinal.{u}), nrep k (x ♯ y) ≈ nrep k x ♯ nrep k y
  | 0, _, _ => equiv_symm (nadd_zero_r 0)
  | k + 1, x, y =>
    equiv_trans (nadd_congr (nrep_nadd k x y) (equiv_refl _))
      (equiv_trans (equiv_symm (nadd_assoc _ _ _))
        (equiv_trans (nadd_congr (equiv_refl _) (nadd_left_comm _ _ _)) (nadd_assoc _ _ _)))

/-- Rocq: `NaturalExp.nrep_nrep`. -/
theorem nrep_nrep : ∀ (k c : Nat) (x : Ordinal.{u}), nrep k (nrep c x) ≈ nrep (k * c) x
  | 0, c, _ => by rw [Nat.zero_mul]; exact equiv_refl _
  | k + 1, c, x => by
    rw [Nat.add_one_mul]
    exact equiv_trans (nadd_congr (nrep_nrep k c x) (equiv_refl _)) (equiv_symm (nrep_add _ _ _))

/-- Rocq: `NaturalExp.nrep_count_le`. -/
theorem nrep_count_le (a b : Nat) (x : Ordinal.{u}) (h : a ≤ b) : nrep a x ≤ nrep b x := by
  induction h with
  | refl => exact le_refl _
  | step _ ih =>
    exact le_trans ih (le_trans (nadd_zero_r _).ge (nadd_le_nadd (le_refl _) (zero_least x)))

/-! ## Finite products, constructively

On the universe of finite ordinals, which has a decidable order and is closed
under natural sums, the lower half of distributivity holds constructively
(`nmul_distrib_lower_Q`); with the constructive upper half of the successor
law, this gives `m ⊗ k ≈ m·k`. -/

/-- Rocq: `NaturalExp.QN`. -/
def QN (x : Ordinal.{u}) : Prop := ∃ n, x ≈ ofNat n

/-- Rocq: `NaturalExp.QN_eq`. -/
theorem QN_eq (x y : Ordinal.{u}) (h : x ≈ y) (hx : QN x) : QN y :=
  let ⟨n, hn⟩ := hx
  ⟨n, equiv_trans (equiv_symm h) hn⟩

/-- Rocq: `NaturalExp.QN_dec`. -/
theorem QN_dec (x y : Ordinal.{u}) (hx : QN x) (hy : QN y) : x < y ∨ y ≤ x :=
  let ⟨m, hm⟩ := hx
  let ⟨n, hn⟩ := hy
  match Nat.lt_or_ge m n with
  | .inl h => .inl (lt_of_le_of_lt hm.le (lt_of_lt_of_le (ofNat_increasing h) hn.ge))
  | .inr h => .inr (le_trans hn.le (le_trans (ofNat_monotone h) hm.ge))

/-- Rocq: `NaturalExp.QN_zero`. -/
theorem QN_zero : QN (0 : Ordinal.{u}) := ⟨0, equiv_refl _⟩

/-- Rocq: `NaturalExp.QN_nadd`. -/
theorem QN_nadd (x y : Ordinal.{u}) (hx : QN x) (hy : QN y) : QN (x ♯ y) :=
  let ⟨m, hm⟩ := hx
  let ⟨n, hn⟩ := hy
  ⟨m + n, equiv_trans (nadd_congr hm hn) (nadd_nat m n)⟩

/-- Rocq: `NaturalExp.QH_nat`. -/
theorem QH_nat : ∀ n : Nat, QH QN (ofNat.{u} n)
  | 0 => ⟨QN_zero, fun a => PEmpty.elim a⟩
  | n + 1 => ⟨⟨n + 1, equiv_refl _⟩, fun _ => QH_nat n⟩

/-- Rocq: `NaturalExp.nmul_succ_nat`. -/
theorem nmul_succ_nat (m k : Nat) :
    nmul (ofNat.{u} m) (succ (ofNat k)) ≈ nmul (ofNat m) (ofNat k) ♯ ofNat m :=
  equiv_intro (nmul_succ_upper _ _)
    (le_trans (nadd_le_nadd (le_refl _) (nmul_one _).ge)
      (le_trans (nmul_distrib_lower_Q QN QN_eq QN_dec QN_zero _ _ 1 (QH_nat m) (QH_nat k)
          (QH_nat 1))
        (nmul_monotone (le_refl _)
          (le_trans (nadd_succ2 (ofNat k) 0).le (succ_monotone (nadd_zero_r _).le)))))

/-- Rocq: `NaturalExp.nmul_nat_nat`. -/
theorem nmul_nat_nat (m : Nat) : ∀ k, nmul (ofNat.{u} m) (ofNat k) ≈ nrep k (ofNat m)
  | 0 => nmul_zero _
  | k + 1 => equiv_trans (nmul_succ_nat m k) (nadd_congr (nmul_nat_nat m k) (equiv_refl _))

/-- Rocq: `NaturalExp.npow_nat`. -/
theorem npow_nat (m : Nat) : ∀ k, npow k (ofNat.{u} m) ≈ ofNat (m ^ k)
  | 0 => equiv_refl _
  | k + 1 => by
    show nmul (npow k (ofNat m)) (ofNat m) ≈ ofNat (m ^ k * m)
    rw [Nat.mul_comm (m ^ k) m]
    exact equiv_trans (nmul_congr (npow_nat m k) (equiv_refl _))
      (equiv_trans (nmul_nat_nat _ m) (nrep_nat m (m ^ k)))

/-- Rocq: `NaturalExp.npow_one`. -/
theorem npow_one (x : Ordinal.{u}) : npow 1 x ≈ x :=
  equiv_trans (nmul_comm 1 x) (nmul_one x)

/-! ## The laws -/

/-- Altman's laws (1)–(5). Rocq: `NaturalExp.natural_exp_laws`. -/
def NaturalExpLaws (e : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) : Prop :=
  (∀ a, e a 1 ≈ a) ∧
  (∀ a b b', 1 < a → b ≤ b' → e a b ≤ e a b') ∧
  (∀ a a' b, 0 < b → a ≤ a' → e a b ≤ e a' b) ∧
  (∀ a b c, e a (b ♯ c) ≈ nmul (e a b) (e a c)) ∧
  (∀ a b c, e a (nmul b c) ≈ e (e a b) c)

/-- `X` and `Y` behave as if `Y = X^(log₂ 3)` for the natural product:
`X^⊗a ≤ Y^⊗k` whenever `2^a ≤ 3^k`, and conversely.
Rocq: `NaturalExp.log23_ratio`. -/
def Log23Ratio (X Y : Ordinal.{u}) : Prop :=
  ω ≤ X ∧
  (∀ a k : Nat, 2 ^ (a + 1) ≤ 3 ^ (k + 1) → npow (a + 1) X ≤ npow (k + 1) Y) ∧
  (∀ a k : Nat, 3 ^ (k + 1) ≤ 2 ^ (a + 1) → npow (k + 1) Y ≤ npow (a + 1) X)

private theorem two_le_of_one_lt (n : Nat) (hn : 1 < ofNat.{u} n) : 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact absurd (lt_of_lt_of_le hn (ofNat_monotone (Nat.le_of_lt_succ h))) (lt_irrefl _)
  · exact h

private theorem lt_pow_succ (n : Nat) (hn : 2 ≤ n) : ∀ k, k < n ^ (k + 1)
  | 0 => by
    show 0 < 1 * n
    rw [Nat.one_mul]; exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hn
  | k + 1 => by
    have ih := lt_pow_succ n hn k
    show k + 1 < n ^ (k + 1) * n
    refine Nat.lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ hn)
    rw [Nat.mul_two]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right ih 1)
      (Nat.add_le_add_left (Nat.lt_of_le_of_lt (Nat.zero_le k) ih) _)

section laws

variable (e : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) (he : NaturalExpLaws e)

include he

/-- Rocq: `NaturalExp.e_eq2`. -/
theorem e_eq2 (a b b' : Ordinal.{u}) (ha : 1 < a) (h : b ≈ b') : e a b ≈ e a b' :=
  equiv_intro (he.2.1 a b b' ha h.le) (he.2.1 a b' b ha h.ge)

/-- Rocq: `NaturalExp.e_eq1`. -/
theorem e_eq1 (a a' b : Ordinal.{u}) (hb : 0 < b) (h : a ≈ a') : e a b ≈ e a' b :=
  equiv_intro (he.2.2.1 a a' b hb h.le) (he.2.2.1 a' a b hb h.ge)

/-- Rocq: `NaturalExp.e_nrep`. -/
theorem e_nrep (a : Ordinal.{u}) (k : Nat) (x : Ordinal.{u}) (ha : 1 < a) :
    e a (nrep (k + 1) x) ≈ npow (k + 1) (e a x) := by
  induction k with
  | zero =>
    exact equiv_trans (e_eq2 e he a _ x ha (nadd_zero_l x))
      (equiv_symm (equiv_trans (nmul_comm 1 _) (nmul_one _)))
  | succ k ih =>
    exact equiv_trans (he.2.2.2.1 a _ x) (nmul_congr ih (equiv_refl _))

/-- Rocq: `NaturalExp.e_nat`. -/
theorem e_nat (a : Ordinal.{u}) (k : Nat) (ha : 1 < a) :
    e a (ofNat (k + 1)) ≈ npow (k + 1) a := by
  have hk : ofNat.{u} (k + 1) ≈ nrep (k + 1) 1 := by
    have h := nrep_nat.{u} (k + 1) 1
    rw [Nat.mul_one] at h
    exact equiv_symm h
  exact equiv_trans (e_eq2 e he a _ _ ha hk)
    (equiv_trans (e_nrep e he a k 1 ha) (npow_congr _ (he.1 a)))

/-- Rocq: `NaturalExp.e_omega_ge`. -/
theorem e_omega_ge (n : Nat) (hn : 1 < ofNat.{u} n) : ω ≤ e (ofNat n) ω :=
  le_intro fun ⟨k⟩ => by
    have h1 : e (ofNat n) (ofNat (k + 1)) ≈ ofNat (n ^ (k + 1)) :=
      equiv_trans (e_nat e he _ k hn) (npow_nat n (k + 1))
    exact lt_of_lt_of_le
      (lt_of_lt_of_le (ofNat_increasing (lt_pow_succ n (two_le_of_one_lt n hn) k)) h1.ge)
      (he.2.1 _ _ _ hn (le_of_lt (index_lt ω ⟨k + 1⟩)))

/-- Rocq: `NaturalExp.e_pow_omega`. -/
theorem e_pow_omega (n k : Nat) (hn : 1 < ofNat.{u} n) :
    e (ofNat (n ^ (k + 1))) ω ≈ npow (k + 1) (e (ofNat n) ω) := by
  have hX : 1 < e (ofNat n) ω := lt_of_lt_of_le omega_gt1 (e_omega_ge e he n hn)
  have h1 : e (ofNat n) (ofNat (k + 1)) ≈ ofNat (n ^ (k + 1)) :=
    equiv_trans (e_nat e he _ k hn) (npow_nat n (k + 1))
  refine equiv_trans (e_eq1 e he _ _ ω omega_gt0 (equiv_symm h1)) ?_
  refine equiv_trans (equiv_symm (he.2.2.2.2 _ _ ω)) ?_
  refine equiv_trans (e_eq2 e he _ _ (nmul ω (ofNat (k + 1))) hn (nmul_comm _ _)) ?_
  exact equiv_trans (he.2.2.2.2 _ ω _) (e_nat e he _ k hX)

/-- Constructively, the laws put `e(2,ω)` and `e(3,ω)` in the ratio `log₂ 3`.
Rocq: `NaturalExp.laws_log23_ratio`. -/
theorem laws_log23_ratio : Log23Ratio (e (ofNat 2) ω) (e (ofNat 3) ω) := by
  have H12 : (1 : Ordinal.{u}) < ofNat 2 := succ_lt 1
  have H13 : (1 : Ordinal.{u}) < ofNat 3 := lt_of_lt_of_le H12 (ofNat_monotone (Nat.le_succ 2))
  refine ⟨e_omega_ge e he 2 H12, fun a k h => ?_, fun a k h => ?_⟩
  · exact le_trans (e_pow_omega e he 2 a H12).ge
      (le_trans (he.2.2.1 _ _ _ omega_gt0 (ofNat_monotone h)) (e_pow_omega e he 3 k H13).le)
  · exact le_trans (e_pow_omega e he 3 k H13).ge
      (le_trans (he.2.2.1 _ _ _ omega_gt0 (ofNat_monotone h)) (e_pow_omega e he 2 a H12).le)

end laws

/-! ## Leading exponents -/

/-- `x` lies in `[ω^δ, ω^(δ+1))`, i.e. `δ` is the leading exponent of the
Cantor normal form of `x`. Rocq: `NaturalExp.has_deg`. -/
def HasDeg (δ x : Ordinal.{u}) : Prop :=
  ω ^ δ ≤ x ∧ ∃ n, x < nrep n (ω ^ δ)

/-- Rocq: `NaturalExp.has_deg_eq`. -/
theorem has_deg_eq (δ x x' : Ordinal.{u}) (h : x ≈ x') (hd : HasDeg δ x) : HasDeg δ x' :=
  ⟨le_trans hd.1 h.le, let ⟨n, hn⟩ := hd.2; ⟨n, lt_of_le_of_lt h.ge hn⟩⟩

/-- Rocq: `NaturalExp.has_deg_eq_exp`. -/
theorem has_deg_eq_exp (δ δ' x : Ordinal.{u}) (h : δ ≈ δ') (hd : HasDeg δ x) : HasDeg δ' x :=
  ⟨le_trans (pow_le_pow_right ω h.ge) hd.1,
    let ⟨n, hn⟩ := hd.2; ⟨n, lt_of_lt_of_le hn (nrep_mono n (pow_le_pow_right ω h.le))⟩⟩

/-- Rocq: `NaturalExp.exp_reflect`. -/
theorem exp_reflect (em : ExcludedMiddle) (a b : Ordinal.{u}) (h : ω ^ a < ω ^ b) : a < b :=
  match order_total em b a with
  | .inl hba => absurd (lt_of_lt_of_le h (pow_le_pow_right ω hba)) (lt_irrefl _)
  | .inr hab => hab

/-- Rocq: `NaturalExp.lt_succ_le`. -/
theorem lt_succ_le (a b : Ordinal.{u}) (h : a < succ b) : a ≤ b := by
  obtain ⟨_, h⟩ := lt_elim h
  exact h

/-- Rocq: `NaturalExp.has_deg_le`. -/
theorem has_deg_le (em : ExcludedMiddle) (δ δ' x x' : Ordinal.{u}) (hd : HasDeg δ x) (hd' : HasDeg δ' x')
    (h : x ≤ x') : δ ≤ δ' :=
  let ⟨n, hn⟩ := hd'.2
  lt_succ_le _ _ (exp_reflect em _ _ (lt_of_le_of_lt hd.1 (lt_of_le_of_lt h
    (lt_of_lt_of_le hn (le_of_lt (nrep_below em (succ_lt δ') n))))))

/-- Rocq: `NaturalExp.nrep_one`. -/
theorem nrep_one (x : Ordinal.{u}) : nrep 1 x ≈ x := nadd_zero_l x

/-- Rocq: `NaturalExp.nrep_lt_succ`. -/
theorem nrep_lt_succ (k : Nat) (x : Ordinal.{u}) (hx : 0 < x) : nrep k x < nrep (k + 1) x :=
  lt_of_le_of_lt (nadd_zero_r _).ge (nadd_increasing2 _ hx)

/-- Rocq: `NaturalExp.zero_lt_cases`. -/
theorem zero_lt_cases (em : ExcludedMiddle) (x : Ordinal.{u}) : 0 < x ∨ x ≤ 0 :=
  match order_total em x 0 with
  | .inl h => .inr h
  | .inr h => .inl h

/-- Rocq: `NaturalExp.has_deg_exists`. -/
theorem has_deg_exists (em : ExcludedMiddle) (x : Ordinal.{u}) (hx : 0 < x) : ∃ δ, HasDeg δ x := by
  obtain ⟨ls, hls, hd⟩ := cantor_decomposition em x
  match ls, hls, hd with
  | [], _, hd => exact absurd (lt_of_lt_of_le hx hd.ge) (lt_irrefl 0)
  | y :: ys, hls, hd =>
    refine ⟨y, le_trans (le_add_right _ _) hd.le, ?_⟩
    have hb : x < ω ^ succ y := lt_of_le_of_lt hd.ge (cantor_below em (succ y) (y :: ys)
      fun a ha => succ_trans (by
        cases ha with
        | head => exact le_refl _
        | tail _ h => exact cantor_sequence_le1 ys y hls.2 a h))
    match exp_below x (succ y) hb with
    | .inl h => exact ⟨1, lt_of_lt_of_le h (le_trans (succ_least (pow_pos ω y)) (nrep_one _).ge)⟩
    | .inr ⟨_, k, hk⟩ => exact ⟨k + 1, lt_of_le_of_lt hk (nrep_lt_succ k _ (pow_pos ω _))⟩

/-- Rocq: `NaturalExp.has_deg_mul`. -/
theorem has_deg_mul (em : ExcludedMiddle) (δ δ' x y : Ordinal.{u}) (hx : HasDeg δ x) (hy : HasDeg δ' y) :
    HasDeg (δ ♯ δ') (nmul x y) := by
  obtain ⟨hl, n, hu⟩ := hx
  obtain ⟨hl', m, hu'⟩ := hy
  refine ⟨le_trans (nmul_exp em δ δ').ge (nmul_monotone hl hl'), n * m, ?_⟩
  have E : nmul (nrep n (ω ^ δ)) (nrep m (ω ^ δ')) ≈ nrep (n * m) (ω ^ (δ ♯ δ')) :=
    equiv_trans (nmul_nrep_l em n _ _)
      (equiv_trans (nrep_congr n (equiv_trans (nmul_comm _ _) (equiv_trans (nmul_nrep_l em m _ _)
        (nrep_congr m (equiv_trans (nmul_comm _ _) (nmul_exp em δ δ'))))))
        (nrep_nrep n m _))
  exact lt_of_le_of_lt (nmul_monotone (le_refl x) (le_of_lt hu'))
    (lt_of_lt_of_le (nmul_increasing1 hu (lt_of_le_of_lt (zero_least y) hu')) E.le)

/-- Rocq: `NaturalExp.has_deg_npow`. -/
theorem has_deg_npow (em : ExcludedMiddle) (k : Nat) (δ x : Ordinal.{u}) (h : HasDeg δ x) :
    HasDeg (nrep k δ) (npow k x) := by
  induction k with
  | zero =>
    refine ⟨(pow_zero ω).le, 2, ?_⟩
    exact lt_of_lt_of_le (succ_lt 1) (le_trans (nrep_nat 2 1).ge (nrep_mono 2 (pow_zero ω).ge))
  | succ k ih => exact has_deg_mul em _ _ _ _ ih h

/-! ## Leading coefficients -/

/-- `d = ω^γ·c + r` with `r < ω^γ` and `c > 0`, using natural sums.
Rocq: `NaturalExp.has_lead`. -/
def HasLead (γ : Ordinal.{u}) (c : Nat) (d : Ordinal.{u}) : Prop :=
  0 < c ∧ ∃ r, r < ω ^ γ ∧ d ≈ nrep c (ω ^ γ) ♯ r

/-- Rocq: `NaturalExp.nrep_ge_one`. -/
theorem nrep_ge_one (c : Nat) (x : Ordinal.{u}) (hc : 0 < c) : x ≤ nrep c x :=
  le_trans (nrep_one x).ge (nrep_count_le 1 c x hc)

/-- Rocq: `NaturalExp.lead_lower`. -/
theorem lead_lower (γ : Ordinal.{u}) (c : Nat) (d : Ordinal.{u}) (h : HasLead γ c d) :
    nrep c (ω ^ γ) ≤ d :=
  let ⟨_, r, _, hd⟩ := h
  le_trans (nadd_zero_r _).ge (le_trans (nadd_le_nadd (le_refl _) (zero_least r)) hd.ge)

/-- Rocq: `NaturalExp.lead_deg`. -/
theorem lead_deg (γ : Ordinal.{u}) (c : Nat) (d : Ordinal.{u}) (h : HasLead γ c d) :
    HasDeg γ d :=
  let ⟨hc, _, hr, hd⟩ := h
  ⟨le_trans (nrep_ge_one c _ hc) (lead_lower γ c d h),
    c + 1, lt_of_le_of_lt hd.le (nadd_increasing2 _ hr)⟩

/-- Rocq: `NaturalExp.nrep_lt_closed`. -/
theorem nrep_lt_closed (em : ExcludedMiddle) (k : Nat) (γ r : Ordinal.{u}) (hr : r < ω ^ γ) : nrep k r < ω ^ γ := by
  induction k with
  | zero => exact pow_pos ω γ
  | succ k ih => exact nadd_closed em γ _ _ (ord_complete em γ) ih hr

/-- Rocq: `NaturalExp.lead_nrep`. -/
theorem lead_nrep (em : ExcludedMiddle) (γ : Ordinal.{u}) (c : Nat) (d : Ordinal.{u}) (k : Nat) (h : HasLead γ c d) :
    HasLead γ ((k + 1) * c) (nrep (k + 1) d) :=
  let ⟨hc, r, hr, hd⟩ := h
  ⟨Nat.mul_le_mul (Nat.le_add_left 1 k) hc, nrep (k + 1) r, nrep_lt_closed em _ γ r hr,
    equiv_trans (nrep_congr _ hd)
      (equiv_trans (nrep_nadd _ _ _) (nadd_congr (nrep_nrep _ _ _) (equiv_refl _)))⟩

/-- Rocq: `NaturalExp.cantor_nadd_below`. -/
theorem cantor_nadd_below (em : ExcludedMiddle) (γ : Ordinal.{u}) : ∀ suf : List Ordinal.{u},
    (∀ a, a ∈ suf → a < γ) → cantorDenoteNadd suf < ω ^ γ
  | [], _ => pow_pos ω γ
  | a :: suf, h => nadd_closed em γ _ _ (ord_complete em γ)
      (pow_lt_pow_right omega_gt1 (h a (.head _)))
      (cantor_nadd_below em γ suf fun b hb => h b (.tail _ hb))

/-- Rocq: `NaturalExp.cantor_nadd_all_eq`. -/
theorem cantor_nadd_all_eq (γ : Ordinal.{u}) : ∀ pre : List Ordinal.{u},
    (∀ a, a ∈ pre → a ≈ γ) → cantorDenoteNadd pre ≈ nrep pre.length (ω ^ γ)
  | [], _ => equiv_refl _
  | a :: pre, h =>
    equiv_trans (nadd_congr (pow_congr (equiv_refl ω) (h a (.head _)))
      (cantor_nadd_all_eq γ pre fun b hb => h b (.tail _ hb))) (nadd_comm _ _)

/-- Rocq: `NaturalExp.lead_exists`. -/
theorem lead_exists (em : ExcludedMiddle) (d : Ordinal.{u}) (hpos : 0 < d) : ∃ γ c, HasLead γ c d := by
  obtain ⟨ls, hls, hd⟩ := cantor_decomposition em d
  match ls, hls, hd with
  | [], _, hd => exact absurd (lt_of_lt_of_le hpos hd.ge) (lt_irrefl 0)
  | y :: ys, hls, hd =>
    obtain ⟨pre, suf, heq, hpre, hsuf⟩ := cantor_split em y (y :: ys) d hls
    have hle : ∀ a, a ∈ y :: ys → a ≤ y := fun a ha => by
      cases ha with
      | head => exact le_refl _
      | tail _ h => exact cantor_sequence_le1 ys y hls.2 a h
    refine ⟨y, pre.length, ?_, cantorDenoteNadd suf, cantor_nadd_below em y suf hsuf, ?_⟩
    · cases pre with
      | nil =>
        have hy : y ∈ suf := by
          have h0 : y ∈ y :: ys := .head _
          rw [heq] at h0
          exact h0
        exact absurd (hsuf y hy) (lt_irrefl _)
      | cons _ _ => exact Nat.succ_pos _
    · have e1 : cantorDenoteNadd (y :: ys) ≈ cantorDenoteNadd pre ♯ cantorDenoteNadd suf := by
        rw [heq]; exact cantor_denote_nadd_app pre suf
      refine equiv_trans (equiv_symm hd) (equiv_trans
        (cantor_denote_nadd_eq em (y :: ys) d (each_complete em _) hls) (equiv_trans e1 ?_))
      refine nadd_congr (cantor_nadd_all_eq y pre fun a ha => equiv_intro ?_ (hpre a ha))
        (equiv_refl _)
      exact hle a (by rw [heq]; exact List.mem_append_left suf ha)

/-- Rocq: `NaturalExp.lead_le`. -/
theorem lead_le (γ : Ordinal.{u}) (c : Nat) (d γ' : Ordinal.{u}) (c' : Nat) (d' : Ordinal.{u})
    (hd : HasLead γ c d) (hd' : HasLead γ' c' d') (hle : d ≤ d') (hγ : γ' ≤ γ) : c ≤ c' := by
  rcases Nat.lt_or_ge c' c with hlt | hge
  · obtain ⟨_, r', hr', he'⟩ := hd'
    exact absurd
      (lt_of_le_of_lt (nrep_count_le _ _ _ hlt) (lt_of_le_of_lt (lead_lower γ c d hd)
        (lt_of_le_of_lt hle (lt_of_le_of_lt he'.le (lt_of_lt_of_le (nadd_increasing2 _ hr')
          (nadd_le_nadd (nrep_mono c' (pow_le_pow_right ω hγ)) (pow_le_pow_right ω hγ)))))))
      (lt_irrefl _)
  · exact hge

/-! ## The theorem -/

/-- Classically, no ordinals are in the ratio `log₂ 3`.
Rocq: `NaturalExp.no_log23_ratio`. -/
theorem no_log23_ratio (em : ExcludedMiddle) (X Y : Ordinal.{u}) : ¬ Log23Ratio X Y := by
  intro ⟨HX, Hup, Hdown⟩
  have HXY : X ≤ Y :=
    le_trans (npow_one X).ge (le_trans (Hup 0 0 (Nat.le_succ 2)) (npow_one Y).le)
  obtain ⟨δ2, hδ2⟩ := has_deg_exists em X (lt_of_lt_of_le omega_gt0 HX)
  obtain ⟨δ3, hδ3⟩ := has_deg_exists em Y (lt_of_lt_of_le omega_gt0 (le_trans HX HXY))
  have Hmono : ∀ a k : Nat, 2 ^ (a + 1) ≤ 3 ^ (k + 1) → nrep (a + 1) δ2 ≤ nrep (k + 1) δ3 :=
    fun a k h => has_deg_le em _ _ _ _ (has_deg_npow em (a + 1) δ2 X hδ2)
      (has_deg_npow em (k + 1) δ3 Y hδ3) (Hup a k h)
  have Hmono' : ∀ a k : Nat, 3 ^ (k + 1) ≤ 2 ^ (a + 1) → nrep (k + 1) δ3 ≤ nrep (a + 1) δ2 :=
    fun a k h => has_deg_le em _ _ _ _ (has_deg_npow em (k + 1) δ3 Y hδ3)
      (has_deg_npow em (a + 1) δ2 X hδ2) (Hdown a k h)
  -- `δ2 > 0`, since `X ≥ ω`.
  have Hδ2pos : 0 < δ2 := by
    rcases zero_lt_cases em δ2 with hp | hz
    · exact hp
    · obtain ⟨n, hn⟩ := hδ2.2
      have hn1 : nrep n (1 : Ordinal.{u}) ≈ ofNat n := by
        have h := nrep_nat.{u} n 1
        rw [Nat.mul_one] at h
        exact h
      exact absurd (lt_of_le_of_lt HX (lt_of_lt_of_le hn (le_trans
        (nrep_mono n (le_trans (pow_le_pow_right ω hz) (pow_zero ω).le))
        (le_trans hn1.le (le_of_lt (index_lt ω ⟨n⟩)))))) (lt_irrefl _)
  have Hδ23 : δ2 ≤ δ3 := has_deg_le em _ _ _ _ hδ2 hδ3 HXY
  obtain ⟨γ2, c2, hl2⟩ := lead_exists em δ2 Hδ2pos
  obtain ⟨γ3, c3, hl3⟩ := lead_exists em δ3 (lt_of_lt_of_le Hδ2pos Hδ23)
  -- `δ2` and `δ3` have the same leading exponent.
  have Hγ23 : γ2 ≤ γ3 :=
    has_deg_le em _ _ _ _ (lead_deg _ _ _ hl2) (lead_deg _ _ _ hl3) Hδ23
  have Hγ32 : γ3 ≤ γ2 :=
    has_deg_le em _ _ _ _ (lead_deg _ _ _ hl3) (lead_deg _ _ _ (lead_nrep em _ _ _ 1 hl2))
      (le_trans (nrep_one δ3).ge (Hmono' 1 0 (by decide)))
  refine nat_no_ratio c2 c3 hl2.1 hl3.1 ?_ ?_
  · intro a k ha hk h
    match a, k, ha, hk, h with
    | a + 1, k + 1, _, _, h =>
      exact lead_le _ _ _ _ _ _ (lead_nrep em _ _ _ a hl2) (lead_nrep em _ _ _ k hl3)
        (Hmono a k h) Hγ32
  · intro a k ha hk h
    match a, k, ha, hk, h with
    | a + 1, k + 1, _, _, h =>
      exact lead_le _ _ _ _ _ _ (lead_nrep em _ _ _ k hl3) (lead_nrep em _ _ _ a hl2)
        (Hmono' a k h) Hγ23

/-- Rocq: `NaturalExp.natural_exp_impossible`. -/
theorem natural_exp_impossible (em : ExcludedMiddle) :
    ¬ ∃ e : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}, NaturalExpLaws e :=
  fun ⟨e, he⟩ => no_log23_ratio em _ _ (laws_log23_ratio e he)

/-- Since the conclusion is a negation, double-negated excluded middle
suffices. `¬¬ExcludedMiddle` is not provable, but it holds in every finite
Kripke model, whose maximal worlds are classical. So the theorem cannot imply
weak excluded middle, or any other principle that some finite Kripke model
refutes. Whether it holds outright is open. Since `laws_log23_ratio` is
constructive, it would follow from a constructive proof of `no_log23_ratio`, a
statement about ordinals alone; a countermodel would have to refute
`¬¬ExcludedMiddle`, so it would be infinitary.
Rocq: `NaturalExp.natural_exp_impossible_nn`. -/
theorem natural_exp_impossible_nn (hem : ¬¬ExcludedMiddle) :
    ¬ ∃ e : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}, NaturalExpLaws e :=
  fun he => hem fun em => natural_exp_impossible em he

end ConstructiveOrdinals.NaturalExp
