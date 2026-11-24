import ConstructiveOrdinals.Analysis.GoodsteinIndependence
import ConstructiveOrdinals.Tactic.NatRing

/-!
# Goodstein's theorem as a sentence of arithmetic

Port of `Ordinal/Analysis/GoodsteinFormula.v`.

A bounded formula `goodsteinθ` with free variables `x` and `y` such that
`∀x ∃y θ` states Goodstein's theorem: `θ(x,y)` holds when `y` bounds a
certificate that the sequence from `x` reaches zero (`goodstein_θ_sound`),
and every `x` has one (`goodstein_θ_true`). By `goodstein_unprovable`, Peano
arithmetic does not prove it (`goodstein_independent`).

The certificate is coded with Gödel's β-function `β(c,d,i) = c mod (1 +
(i+1)·d)`. Besides the sequence itself, it holds for each step `i` (in base
`b = i+2`) tables of `b^e`, of `(b+1)^w`, and of the base change `T(j)`,
checked through the leading term: `T(d·b^e + r) = d·(b+1)^(T(e)) + T(r)`
when `1 ≤ d < b` and `r < b^e`.

Lean notes:

- Remainders are `ConstructiveOrdinals.Nat.mod`, since the core lemmas about
  `%` use `propext`. For the same reason the Chinese remainder theorem does
  not go through `gcd`: for `i < j` the moduli satisfy
  `X·m_i + 1 = Y·m_j` explicitly (`inv_moduli`), which gives an inverse of
  `m_i` modulo `m_j`. Rocq's `coprime_moduli`, `coprime_mul` and
  `coprime_prodm` are replaced by `inv_moduli` and `inv_prodm`.
- Rocq's `fact` is defined here.
- Rocq's `setoid_rewrite` under binders becomes `Iff` congruences.
-/

namespace ConstructiveOrdinals.GoodsteinFormula

open PeanoArith ATerm Form OmegaLogic Embedding Cichon Goodstein GoodsteinIndependence

/-! ## Division with remainder -/

theorem divmod_inj {m r1 r2 : Nat} (h1 : r1 < m) (h2 : r2 < m) :
    ∀ q1 q2, q1 * m + r1 = q2 * m + r2 → q1 = q2 ∧ r1 = r2
  | 0, 0, h => ⟨rfl, by rw [Nat.zero_mul, Nat.zero_add, Nat.zero_add] at h; exact h⟩
  | 0, q2 + 1, h => by
    rw [Nat.zero_mul, Nat.zero_add, Nat.succ_mul, Nat.add_assoc] at h
    exact absurd (h ▸ Nat.le_trans (Nat.le_add_right m r2) (Nat.le_add_left _ _)) (Nat.not_le_of_lt h1)
  | q1 + 1, 0, h => by
    rw [Nat.zero_mul, Nat.zero_add, Nat.succ_mul, Nat.add_assoc] at h
    exact absurd (h ▸ Nat.le_trans (Nat.le_add_right m r1) (Nat.le_add_left _ _)) (Nat.not_le_of_lt h2)
  | q1 + 1, q2 + 1, h => by
    have h' : q1 * m + r1 = q2 * m + r2 := by
      apply Nat.add_left_cancel (n := m)
      calc m + (q1 * m + r1) = (q1 + 1) * m + r1 := by nat_ring
        _ = (q2 + 1) * m + r2 := h
        _ = m + (q2 * m + r2) := by nat_ring
    obtain ⟨e1, e2⟩ := divmod_inj h1 h2 q1 q2 h'
    exact ⟨congrArg (· + 1) e1, e2⟩

theorem mod_unique {a m q r : Nat} (hr : r < m) (h : a = q * m + r) : Nat.mod a m = r := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  exact (divmod_inj (Nat.mod_lt a hm) hr _ _ ((Nat.div_add_mod a hm).trans h)).2

theorem div_unique {a m q r : Nat} (hr : r < m) (h : a = q * m + r) : Nat.div a m = q := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  exact (divmod_inj (Nat.mod_lt a hm) hr _ _ ((Nat.div_add_mod a hm).trans h)).1

theorem mod_le' (a : Nat) {m : Nat} (hm : 0 < m) : Nat.mod a m ≤ a :=
  Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq (Nat.div_add_mod a hm))

/-! ## The β-function -/

/-- Rocq: `Analysis.GoodsteinFormula.beta`. -/
def beta (c d i : Nat) : Nat := Nat.mod c (1 + (i + 1) * d)

/-- Rocq: `Analysis.GoodsteinFormula.modulus`. -/
def modulus (d i : Nat) : Nat := 1 + (i + 1) * d

theorem modulus_pos (d i : Nat) : 0 < modulus d i := by
  unfold modulus; rw [Nat.add_comm]; exact Nat.succ_pos _

/-- Rocq: `Analysis.GoodsteinFormula.beta_le`. -/
theorem beta_le (c d i : Nat) : beta c d i ≤ c := mod_le' c (modulus_pos d i)

/-- Rocq: `Analysis.GoodsteinFormula.prodm`. -/
def prodm (d : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => prodm d j * modulus d j

/-- Rocq: `Analysis.GoodsteinFormula.prodm_pos`. -/
theorem prodm_pos (d : Nat) : ∀ j, 0 < prodm d j
  | 0 => Nat.zero_lt_one
  | j + 1 => Nat.mul_pos (prodm_pos d j) (modulus_pos d j)

/-- Rocq: `Analysis.GoodsteinFormula.prodm_divide`. -/
theorem prodm_divide (d i : Nat) : ∀ j, i < j → ∃ q, prodm d j = modulus d i * q
  | 0, h => absurd h (Nat.not_lt_zero _)
  | j + 1, h => by
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | inl hlt =>
      obtain ⟨q, hq⟩ := prodm_divide d i j hlt
      exact ⟨q * modulus d j, by show prodm d j * modulus d j = _; rw [hq, Nat.mul_assoc]⟩
    | inr e => subst e; exact ⟨prodm d i, Nat.mul_comm _ _⟩

/-- Rocq: `Stdlib.fact`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- Rocq: `Analysis.GoodsteinFormula.divide_fact`. -/
theorem divide_fact (k : Nat) : ∀ D, 1 ≤ k → k ≤ D → ∃ e, fact D = k * e
  | 0, h1, h2 => absurd (Nat.le_trans h1 h2) (Nat.not_succ_le_zero 0)
  | D + 1, h1, h2 => by
    cases Nat.lt_or_eq_of_le h2 with
    | inl hlt =>
      obtain ⟨e, he⟩ := divide_fact k D h1 (Nat.le_of_lt_succ hlt)
      exact ⟨(D + 1) * e, by show (D + 1) * fact D = _; rw [he, Nat.mul_left_comm]⟩
    | inr e => subst e; exact ⟨fact D, rfl⟩

/-- Rocq: `Analysis.GoodsteinFormula.fact_ge`. -/
theorem fact_ge : ∀ D, D ≤ fact D
  | 0 => Nat.zero_le _
  | D + 1 => Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (Nat.mul_le_mul_left _ (fact_pos D))

theorem mod_add_mul (a k : Nat) {m : Nat} (hm : 0 < m) : Nat.mod (a + k * m) m = Nat.mod a m :=
  mod_unique (Nat.mod_lt a hm) (by
    have h := Nat.div_add_mod a hm
    calc a + k * m = (Nat.div a m * m + Nat.mod a m) + k * m := by rw [h]
      _ = (Nat.div a m + k) * m + Nat.mod a m := by nat_ring)

theorem mod_small {a m : Nat} (h : a < m) : Nat.mod a m = a := mod_unique (q := 0) h (by rw [Nat.zero_mul, Nat.zero_add])

/-! ### Explicit inverses for the moduli -/

/-- For `i < j` the modulus `m_i` is invertible modulo `m_j`, when `j - i`
divides `d`: with `a = j+1`, `b = i+1` and `d = s·e`, one has
`a·a·e·m_i + 1 = (a·b·e + 1)·m_j`. Replaces Rocq's `coprime_moduli`. -/
theorem inv_moduli (i s e : Nat) (hs : 1 ≤ s) (he : 1 ≤ e) :
    ∃ w z, w * modulus (s * e) i = 1 + z * modulus (s * e) (i + s) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.sub_add_cancel hs).symm⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.sub_add_cancel he).symm⟩
  -- `K + 1 = (j+1)·d`
  refine ⟨(i + s' + 2) * (i + s' + 2) * (e' + 1) * ((i + s' + 2) * ((s' + 1) * (e' + 1))),
    ((i + s' + 1) * (s' + 1) * (e' + 1) + s' * e' + s' + e') * ((i + s' + 2) * (i + 1) * (e' + 1) + 1)
      + (i + s' + 2) * (i + 1) * (e' + 1), ?_⟩
  unfold modulus
  nat_ring

/-- Products of invertible numbers are invertible. Replaces Rocq's
`coprime_mul` and `coprime_prodm`. -/
theorem inv_prodm (d j : Nat) (h : ∀ i, i < j → ∃ w z, w * modulus d i = 1 + z * modulus d j) :
    ∀ j', j' ≤ j → ∃ u v, u * prodm d j' = 1 + v * modulus d j
  | 0, _ => ⟨1, 0, by show 1 * 1 = 1 + 0 * _; rw [Nat.zero_mul]⟩
  | j' + 1, hj' => by
    obtain ⟨u1, v1, h1⟩ := inv_prodm d j h j' (Nat.le_of_succ_le hj')
    obtain ⟨u2, v2, h2⟩ := h j' hj'
    refine ⟨u1 * u2, v1 + v2 + v1 * v2 * modulus d j, ?_⟩
    calc u1 * u2 * (prodm d j' * modulus d j') = (u1 * prodm d j') * (u2 * modulus d j') := by nat_ring
      _ = (1 + v1 * modulus d j) * (1 + v2 * modulus d j) := by rw [h1, h2]
      _ = 1 + (v1 + v2 + v1 * v2 * modulus d j) * modulus d j := by nat_ring

/-- The Chinese remainder theorem for the moduli of the β-function.
Rocq: `Analysis.GoodsteinFormula.crt`, whose hypothesis is that the moduli are
pairwise coprime. -/
theorem crt (d : Nat) (f : Nat → Nat) : ∀ L,
    (∀ i j, i < j → j < L → ∃ w z, w * modulus d i = 1 + z * modulus d j) →
    ∃ c, ∀ i, i < L → Nat.mod c (modulus d i) = Nat.mod (f i) (modulus d i)
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | L + 1, hinv => by
    obtain ⟨c, hc⟩ := crt d f L (fun i j hij hj => hinv i j hij (Nat.lt_succ_of_lt hj))
    obtain ⟨u, v, huv⟩ := inv_prodm d L (fun i hi => hinv i L hi (Nat.lt_succ_self L)) L (Nat.le_refl L)
    -- `t ≡ f L - c` modulo `m_L`, since `m_L - 1 = (L+1)·d`
    refine ⟨c + (f L + (L + 1) * d * c) * u * prodm d L, fun i hi => ?_⟩
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
    | inl hlt =>
      obtain ⟨q, hq⟩ := prodm_divide d i L hlt
      rw [hq]
      have e : c + (f L + (L + 1) * d * c) * u * (modulus d i * q) =
          c + ((f L + (L + 1) * d * c) * u * q) * modulus d i := by nat_ring
      rw [e, mod_add_mul _ _ (modulus_pos d i)]
      exact hc i hlt
    | inr e =>
      subst e
      have e : c + (f i + (i + 1) * d * c) * u * prodm d i =
          f i + (c + (f i + (i + 1) * d * c) * v) * modulus d i := by
        calc c + (f i + (i + 1) * d * c) * u * prodm d i
            = c + (f i + (i + 1) * d * c) * (u * prodm d i) := by nat_ring
          _ = c + (f i + (i + 1) * d * c) * (1 + v * modulus d i) := by rw [huv]
          _ = f i + (c + (f i + (i + 1) * d * c) * v) * modulus d i := by unfold modulus; nat_ring
      rw [e, mod_add_mul _ _ (modulus_pos d i)]

/-- Rocq: `Analysis.GoodsteinFormula.sumf`. -/
def sumf (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumf f n + f n

/-- Rocq: `Analysis.GoodsteinFormula.sumf_ge`. -/
theorem sumf_ge (f : Nat → Nat) : ∀ n i, i < n → f i ≤ sumf f n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | inl hlt => exact Nat.le_trans (sumf_ge f n i hlt) (Nat.le_add_right _ _)
    | inr e => subst e; exact Nat.le_add_left _ _

/-- Rocq: `Analysis.GoodsteinFormula.beta_exists`. -/
theorem beta_exists (f : Nat → Nat) (L : Nat) : ∃ c d, ∀ i, i < L → beta c d i = f i := by
  obtain ⟨c, hc⟩ := crt (fact (L + sumf f L)) f L (fun i j hij hj => by
    obtain ⟨s, rfl⟩ : ∃ s, j = i + s := ⟨j - i, (Nat.add_comm _ _).trans (Nat.sub_add_cancel (Nat.le_of_lt hij)) |>.symm⟩
    have hs : 1 ≤ s := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.lt_irrefl _ hij)
    have hsD : s ≤ L + sumf f L := Nat.le_trans (Nat.le_trans (Nat.le_add_left s i) (Nat.le_of_lt hj)) (Nat.le_add_right _ _)
    obtain ⟨e, he⟩ := divide_fact s _ hs hsD
    have he1 : 1 ≤ e := Nat.pos_of_ne_zero (fun h => by
      have := fact_pos (L + sumf f L); rw [he, h, Nat.mul_zero] at this; exact Nat.lt_irrefl _ this)
    rw [he]
    exact inv_moduli i s e hs he1)
  refine ⟨c, fact (L + sumf f L), fun i hi => ?_⟩
  show Nat.mod c (modulus _ i) = f i
  rw [hc i hi]
  apply mod_small
  show f i < 1 + (i + 1) * fact (L + sumf f L)
  have h1 : f i ≤ fact (L + sumf f L) :=
    Nat.le_trans (Nat.le_trans (sumf_ge f L i hi) (Nat.le_add_left _ _)) (fact_ge _)
  exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (by rw [Nat.add_comm 1]; exact Nat.succ_le_succ (Nat.le_trans (Nat.le_of_eq (Nat.one_mul _).symm)
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le i))))))

/-! ## Bounded formulas with known meanings

Formulas are written with de Bruijn indices. A _macro_ is a formula whose
free variables `0..k-1` are its arguments; `call F l` plugs terms into them.
Inside `ball v B` and `bex v B` the bound variable is `0` and the others shift
by one. -/

/-- Rocq: `Analysis.GoodsteinFormula.lift`. -/
def lift (t : ATerm) : ATerm := asubst shiftSub t

/-- `∀z ≤ v. B`. Rocq: `Analysis.GoodsteinFormula.ball`. -/
def ball (v : ATerm) (B : Form) : Form :=
  all (imp (ex (Form.eq (tplus (tv 1) (tv 0)) (lift (lift v)))) B)

/-- Rocq: `Analysis.GoodsteinFormula.fneg`. -/
def fneg (A : Form) : Form := imp A bot

/-- `∃z ≤ v. B`. Rocq: `Analysis.GoodsteinFormula.bex`. -/
def bex (v : ATerm) (B : Form) : Form := fneg (ball v (fneg B))

/-- Rocq: `Analysis.GoodsteinFormula.fle`. -/
def fle (u v : ATerm) : Form := ex (Form.eq (tplus (lift u) (tv 0)) (lift v))

/-- Rocq: `Analysis.GoodsteinFormula.flt`. -/
def flt (u v : ATerm) : Form := fle (ts u) v

/-- The `i`-th term of a list, `tz` when out of range (Rocq: `nth i l tz`). -/
def tnth : List ATerm → Nat → ATerm
  | [], _ => tz
  | t :: _, 0 => t
  | _ :: l, i + 1 => tnth l i

/-- Rocq: `Analysis.GoodsteinFormula.call`. -/
def call (F : Form) (l : List ATerm) : Form := fsubst (fun i => tnth l i) F

/-- Rocq: `Analysis.GoodsteinFormula.occ0_lift`. -/
theorem occ0_lift (t : ATerm) : occ 0 (lift t) = false := occ0_shift t

/-- Rocq: `Analysis.GoodsteinFormula.occ1_lift2`. -/
theorem occ1_lift2 (t : ATerm) : occ 1 (lift (lift t)) = false := (occ_shift 1 _).trans (occ0_lift t)

/-- Rocq: `Analysis.GoodsteinFormula.isD_ball`. -/
theorem isD_ball (v : ATerm) (B : Form) : isD (ball v B) = isD B := by
  show ((isT10 (tplus (tv 1) (tv 0)) && !occ 0 (lift (lift v)) && !occ 1 (lift (lift v))) && isD B) = isD B
  rw [occ0_lift, occ1_lift2]; rfl

/-- Rocq: `Analysis.GoodsteinFormula.isD_bex`. -/
theorem isD_bex (v : ATerm) (B : Form) : isD (bex v B) = isD B := by
  show (isD (ball v (fneg B)) && true) = isD B
  rw [isD_ball]
  show ((isD B && true) && true) = isD B
  cases isD B <;> rfl

/-- Rocq: `Analysis.GoodsteinFormula.isD_fle`. -/
theorem isD_fle (u v : ATerm) : isD (fle u v) = true := by
  show (isTv 0 (tv 0) && !occ 0 (lift u) && !occ 0 (lift v)) = true
  rw [occ0_lift u, occ0_lift v]; rfl

/-- Rocq: `Analysis.GoodsteinFormula.isD_call`. -/
theorem isD_call (F : Form) (l : List ATerm) : isD (call F l) = isD F := isD_fsubst_eq F _

/-- Rocq: `Analysis.GoodsteinFormula.teval_lift`. -/
theorem teval_lift (x : Nat) (ρ : Nat → Nat) (t : ATerm) : teval (scons x ρ) (lift t) = teval ρ t :=
  teval_shift x ρ t

/-- Rocq: `Analysis.GoodsteinFormula.sat_ball`. -/
theorem sat_ball (ρ : Nat → Nat) (v : ATerm) (B : Form) :
    sat ρ (ball v B) ↔ ∀ z, z ≤ teval ρ v → sat (scons z ρ) B := by
  have hv : ∀ z k, teval (scons k (scons z ρ)) (lift (lift v)) = teval ρ v := fun z k =>
    (teval_lift k _ _).trans (teval_lift z ρ v)
  constructor
  · intro H z hz
    obtain ⟨k, hk⟩ := Nat.le.dest hz
    exact H z ⟨k, (show z + k = _ from hk).trans (hv z k).symm⟩
  · intro H z ⟨k, hk⟩
    exact H z (Nat.le.intro (n := z) (k := k) ((show z + k = _ from hk).trans (hv z k)))

/-- Rocq: `Analysis.GoodsteinFormula.sat_dec`. -/
theorem sat_dec (ρ : Nat → Nat) (B : Form) (h : isD B = true) : sat ρ B ∨ ¬ sat ρ B := by
  cases e : deval ρ B with
  | true => exact .inl ((deval_sat h ρ).1 e)
  | false => exact .inr ((deval_false ρ h).1 e)

/-- Rocq: `Analysis.GoodsteinFormula.bounded_search`. -/
theorem bounded_search (P : Nat → Prop) (hd : ∀ z, P z ∨ ¬ P z) :
    ∀ b, ¬ (∀ z, z ≤ b → ¬ P z) → ∃ z, z ≤ b ∧ P z
  | 0, H => by
    cases hd 0 with
    | inl h0 => exact ⟨0, Nat.le_refl 0, h0⟩
    | inr h0 => exact absurd (fun z hz => (Nat.le_antisymm hz (Nat.zero_le z)) ▸ h0) H
  | b + 1, H => by
    cases hd (b + 1) with
    | inl h1 => exact ⟨b + 1, Nat.le_refl _, h1⟩
    | inr h1 =>
      obtain ⟨z, hz, pz⟩ := bounded_search P hd b (fun H2 => H (fun z hz =>
        match Nat.lt_or_eq_of_le hz with
        | .inl hlt => H2 z (Nat.le_of_lt_succ hlt)
        | .inr e => e ▸ h1))
      exact ⟨z, Nat.le_succ_of_le hz, pz⟩

/-- Rocq: `Analysis.GoodsteinFormula.sat_bex`. -/
theorem sat_bex (ρ : Nat → Nat) (v : ATerm) (B : Form) (HD : isD B = true) :
    sat ρ (bex v B) ↔ ∃ z, z ≤ teval ρ v ∧ sat (scons z ρ) B :=
  ⟨fun H => bounded_search _ (fun _ => sat_dec _ B HD) _
      (fun H' => H ((sat_ball ρ v (fneg B)).2 fun z hz hB => H' z hz hB)),
   fun ⟨z, hz, hB⟩ H => (sat_ball ρ v (fneg B)).1 H z hz hB⟩

/-- Rocq: `Analysis.GoodsteinFormula.sat_fle`. -/
theorem sat_fle (ρ : Nat → Nat) (u v : ATerm) : sat ρ (fle u v) ↔ teval ρ u ≤ teval ρ v := by
  constructor
  · intro ⟨k, hk⟩
    change teval (scons k ρ) (lift u) + k = teval (scons k ρ) (lift v) at hk
    rw [teval_lift, teval_lift] at hk
    exact Nat.le.intro hk
  · intro h
    obtain ⟨k, hk⟩ := Nat.le.dest h
    refine ⟨k, ?_⟩
    change teval (scons k ρ) (lift u) + k = teval (scons k ρ) (lift v)
    rw [teval_lift, teval_lift]; exact hk

/-- Rocq: `Analysis.GoodsteinFormula.sat_flt`. -/
theorem sat_flt (ρ : Nat → Nat) (u v : ATerm) : sat ρ (flt u v) ↔ teval ρ u < teval ρ v :=
  sat_fle ρ (ts u) v

/-- Rocq: `Analysis.GoodsteinFormula.sat_call`. -/
theorem sat_call (ρ : Nat → Nat) (F : Form) (l : List ATerm) :
    sat ρ (call F l) ↔ sat (fun i => teval ρ (tnth l i)) F :=
  sat_fsubst F ρ _

/-- `a mod m = r`, with arguments `a, m, r`. Rocq: `Analysis.GoodsteinFormula.MODf`. -/
def MODf : Form :=
  conj (flt (tv 2) (tv 1)) (bex (tv 0) (Form.eq (tv 1) (tplus (tmult (tv 0) (tv 2)) (tv 3))))

/-- Rocq: `Analysis.GoodsteinFormula.sat_MODf`. -/
theorem sat_MODf (ρ : Nat → Nat) : sat ρ MODf ↔ 0 < ρ 1 ∧ Nat.mod (ρ 0) (ρ 1) = ρ 2 := by
  refine (and_congr (sat_flt ρ _ _) (sat_bex ρ _ _ rfl)).trans ?_
  constructor
  · intro ⟨hr, q, _, ha⟩
    exact ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hr, mod_unique hr ha⟩
  · intro ⟨hm, hr⟩
    have hd := Nat.div_add_mod (ρ 0) hm
    refine ⟨show ρ 2 < ρ 1 by rw [← hr]; exact Nat.mod_lt _ hm, Nat.div (ρ 0) (ρ 1), ?_, ?_⟩
    · exact Nat.le_trans (Nat.le_mul_of_pos_right _ hm) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hd))
    · show ρ 0 = Nat.div (ρ 0) (ρ 1) * ρ 1 + ρ 2
      rw [← hr]; exact hd.symm

/-- Table lookups: entry `j` of table `tag` at step `i`.
Rocq: `Analysis.GoodsteinFormula.bt`. -/
def bt (c d M tag i j : Nat) : Nat := beta c d (4 * (i * M + j) + tag)

/-- Rocq: `Analysis.GoodsteinFormula.bt_le`. -/
theorem bt_le (c d M tag i j : Nat) : bt c d M tag i j ≤ c := beta_le _ _ _

theorem beta_alt (c d k : Nat) : beta c d k = Nat.mod c ((k + 1) * d + 1) := by
  unfold beta; rw [Nat.add_comm 1]

/-- Arguments `c, d, M, i, j, v`: `bt c d M tag i j = v`.
Rocq: `Analysis.GoodsteinFormula.LOOK`. -/
def LOOK (tag : Nat) : Form :=
  call MODf [tv 0, ts (tmult (ts (tplus (tmult (num 4) (tplus (tmult (tv 3) (tv 2)) (tv 4))) (num tag))) (tv 1)), tv 5]

/-- Rocq: `Analysis.GoodsteinFormula.sat_LOOK`. -/
theorem sat_LOOK (ρ : Nat → Nat) (tag : Nat) : sat ρ (LOOK tag) ↔ bt (ρ 0) (ρ 1) (ρ 2) tag (ρ 3) (ρ 4) = ρ 5 := by
  refine (sat_call ρ MODf _).trans ((sat_MODf _).trans ?_)
  show 0 < (teval ρ (num 4) * (ρ 3 * ρ 2 + ρ 4) + teval ρ (num tag) + 1) * ρ 1 + 1 ∧
      Nat.mod (ρ 0) ((teval ρ (num 4) * (ρ 3 * ρ 2 + ρ 4) + teval ρ (num tag) + 1) * ρ 1 + 1) = ρ 5 ↔ _
  rw [teval_num ρ 4, teval_num ρ tag]
  show _ ↔ beta (ρ 0) (ρ 1) (4 * (ρ 3 * ρ 2 + ρ 4) + tag) = ρ 5
  rw [beta_alt]
  exact ⟨fun h => h.2, fun h => ⟨Nat.succ_pos _, h⟩⟩

/-- Rocq: `Analysis.GoodsteinFormula.flook`. -/
def flook (tag : Nat) (c d M i j v : ATerm) : Form := call (LOOK tag) [c, d, M, i, j, v]

/-- Rocq: `Analysis.GoodsteinFormula.sat_flook`. -/
theorem sat_flook (ρ : Nat → Nat) (tag : Nat) (c d M i j v : ATerm) :
    sat ρ (flook tag c d M i j v) ↔
      bt (teval ρ c) (teval ρ d) (teval ρ M) tag (teval ρ i) (teval ρ j) = teval ρ v :=
  (sat_call ρ _ _).trans (sat_LOOK _ tag)

/-- Rocq: `Analysis.GoodsteinFormula.isD_flook`. -/
theorem isD_flook (tag : Nat) (c d M i j v : ATerm) : isD (flook tag c d M i j v) = true :=
  (isD_call _ _).trans ((isD_call _ _).trans rfl)

/-- `let v := bt … in B`, as a bounded universal. Rocq: `Analysis.GoodsteinFormula.flet`. -/
def flet (tag : Nat) (c d M i j : ATerm) (B : Form) : Form :=
  ball c (imp (flook tag (lift c) (lift d) (lift M) (lift i) (lift j) (tv 0)) B)

/-- Rocq: `Analysis.GoodsteinFormula.sat_flet`. -/
theorem sat_flet (ρ : Nat → Nat) (tag : Nat) (c d M i j : ATerm) (B : Form) :
    sat ρ (flet tag c d M i j B) ↔
      sat (scons (bt (teval ρ c) (teval ρ d) (teval ρ M) tag (teval ρ i) (teval ρ j)) ρ) B := by
  have hlook : ∀ z, sat (scons z ρ) (flook tag (lift c) (lift d) (lift M) (lift i) (lift j) (tv 0)) ↔
      bt (teval ρ c) (teval ρ d) (teval ρ M) tag (teval ρ i) (teval ρ j) = z := fun z => by
    have h := sat_flook (scons z ρ) tag (lift c) (lift d) (lift M) (lift i) (lift j) (tv 0)
    rw [teval_lift z ρ c, teval_lift z ρ d, teval_lift z ρ M, teval_lift z ρ i, teval_lift z ρ j] at h
    exact h
  refine (sat_ball ρ c _).trans ⟨fun H => H _ (bt_le _ _ _ _ _ _) ((hlook _).2 rfl), fun H z _ hz => ?_⟩
  have e := (hlook z).1 hz
  subst e
  exact H

/-- Rocq: `Analysis.GoodsteinFormula.isD_flet`. -/
theorem isD_flet (tag : Nat) (c d M i j : ATerm) (B : Form) : isD (flet tag c d M i j B) = isD B := by
  rw [flet, isD_ball]
  show (isD (flook tag (lift c) (lift d) (lift M) (lift i) (lift j) (tv 0)) && isD B) = isD B
  rw [isD_flook]; rfl

/-! ## The certificate

Tables, at step `i` with base `b = i+2`:
- `0`: entry `0` is the `i`-th term of the sequence;
- `1`: the base change `T(j)`, for `j` up to the current term;
- `2`: the powers `b^e`;
- `3`: the powers `(b+1)^w`, for `w + 1 < M`. -/

/-- Arguments `c, d, M, i, n`. Rocq: `Analysis.GoodsteinFormula.PBf`. -/
def PBf : Form :=
  conj (flook 2 (tv 0) (tv 1) (tv 2) (tv 3) tz (num 1))
    (ball (tv 4) (imp (flt (tv 0) (tv 5))
      (flet 2 (tv 1) (tv 2) (tv 3) (tv 4) (tv 0)
        (flook 2 (tv 2) (tv 3) (tv 4) (tv 5) (ts (tv 1)) (tmult (ts (ts (tv 5))) (tv 0))))))

/-- Rocq: `Analysis.GoodsteinFormula.PBok`. -/
def PBok (c d M i n : Nat) : Prop :=
  bt c d M 2 i 0 = 1 ∧ ∀ e, e ≤ n → e < n → bt c d M 2 i (e + 1) = (i + 2) * bt c d M 2 i e

/-- Rocq: `Analysis.GoodsteinFormula.sat_PBf`. -/
theorem sat_PBf (ρ : Nat → Nat) : sat ρ PBf ↔ PBok (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) :=
  and_congr (sat_flook _ _ _ _ _ _ _ _)
    ((sat_ball _ _ _).trans (forall_congr' fun _ => imp_congr_right fun _ =>
      imp_congr (sat_flt _ _ _) ((sat_flet _ _ _ _ _ _ _ _).trans (sat_flook _ _ _ _ _ _ _ _))))

/-- Arguments `c, d, M, i`. Rocq: `Analysis.GoodsteinFormula.Qf`. -/
def Qf : Form :=
  conj (flook 3 (tv 0) (tv 1) (tv 2) (tv 3) tz (num 1))
    (ball (tv 2) (imp (flt (ts (tv 0)) (tv 3))
      (flet 3 (tv 1) (tv 2) (tv 3) (tv 4) (tv 0)
        (flook 3 (tv 2) (tv 3) (tv 4) (tv 5) (ts (tv 1)) (tmult (ts (ts (ts (tv 5)))) (tv 0))))))

/-- Rocq: `Analysis.GoodsteinFormula.Qok`. -/
def Qok (c d M i : Nat) : Prop :=
  bt c d M 3 i 0 = 1 ∧ ∀ w, w ≤ M → w + 1 < M → bt c d M 3 i (w + 1) = (i + 3) * bt c d M 3 i w

/-- Rocq: `Analysis.GoodsteinFormula.sat_Qf`. -/
theorem sat_Qf (ρ : Nat → Nat) : sat ρ Qf ↔ Qok (ρ 0) (ρ 1) (ρ 2) (ρ 3) :=
  and_congr (sat_flook _ _ _ _ _ _ _ _)
    ((sat_ball _ _ _).trans (forall_congr' fun _ => imp_congr_right fun _ =>
      imp_congr (sat_flt _ _ _) ((sat_flet _ _ _ _ _ _ _ _).trans (sat_flook _ _ _ _ _ _ _ _))))

/-- Arguments `c, d, M, i, n`: the base change, through leading terms.
Rocq: `Analysis.GoodsteinFormula.Tf`. -/
def Tf : Form :=
  conj (flook 1 (tv 0) (tv 1) (tv 2) (tv 3) tz tz)
    (ball (tv 4) (imp (fle (num 1) (tv 0))
      (bex (tv 0) (bex (tv 1) (bex (tv 2)
        (flet 2 (tv 4) (tv 5) (tv 6) (tv 7) (tv 2)
        (flet 1 (tv 5) (tv 6) (tv 7) (tv 8) (tv 3)
        (flet 3 (tv 6) (tv 7) (tv 8) (tv 9) (tv 0)
        (flet 1 (tv 7) (tv 8) (tv 9) (tv 10) (tv 3)
          (conj (Form.eq (tv 7) (tplus (tmult (tv 5) (tv 3)) (tv 4)))
          (conj (flt (tv 4) (tv 3))
          (conj (fle (num 1) (tv 5))
          (conj (flt (tv 5) (ts (ts (tv 11))))
          (conj (flt (tv 2) (tv 10))
            (flook 1 (tv 8) (tv 9) (tv 10) (tv 11) (tv 7) (tplus (tmult (tv 5) (tv 1)) (tv 0)))))))))))))))))

/-- Rocq: `Analysis.GoodsteinFormula.Tok`. -/
def Tok (c d M i n : Nat) : Prop :=
  bt c d M 1 i 0 = 0 ∧
  ∀ j, j ≤ n → 1 ≤ j →
    ∃ e, e ≤ j ∧ ∃ dd, dd ≤ j ∧ ∃ r, r ≤ j ∧
      j = dd * bt c d M 2 i e + r ∧ r < bt c d M 2 i e ∧ 1 ≤ dd ∧ dd < i + 2 ∧
      bt c d M 1 i e < M ∧
      bt c d M 1 i j = dd * bt c d M 3 i (bt c d M 1 i e) + bt c d M 1 i r

/-- Rocq: `Analysis.GoodsteinFormula.sat_Tf`. -/
theorem sat_Tf (ρ : Nat → Nat) : sat ρ Tf ↔ Tok (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) :=
  and_congr (sat_flook _ _ _ _ _ _ _ _)
    ((sat_ball _ _ _).trans (forall_congr' fun _ => imp_congr_right fun _ =>
      imp_congr (sat_fle _ _ _)
      ((sat_bex _ _ _ (by rfl)).trans (exists_congr fun _ => and_congr_right fun _ =>
      (sat_bex _ _ _ (by rfl)).trans (exists_congr fun _ => and_congr_right fun _ =>
      (sat_bex _ _ _ (by rfl)).trans (exists_congr fun _ => and_congr_right fun _ =>
      (sat_flet _ _ _ _ _ _ _ _).trans ((sat_flet _ _ _ _ _ _ _ _).trans ((sat_flet _ _ _ _ _ _ _ _).trans
      ((sat_flet _ _ _ _ _ _ _ _).trans
        (and_congr Iff.rfl (and_congr (sat_flt _ _ _) (and_congr (sat_fle _ _ _)
          (and_congr (sat_flt _ _ _) (and_congr (sat_flt _ _ _) (sat_flook _ _ _ _ _ _ _ _)))))))))))))))

/-- Arguments `c, d, M, i`: step `i` of the sequence is checked.
Rocq: `Analysis.GoodsteinFormula.STEPf`. -/
def STEPf : Form :=
  flet 0 (tv 0) (tv 1) (tv 2) (tv 3) tz
    (conj (fle (num 1) (tv 0))
    (conj (flt (tv 0) (tv 3))
    (conj (flet 0 (tv 1) (tv 2) (tv 3) (ts (tv 4)) tz
            (flook 1 (tv 2) (tv 3) (tv 4) (tv 5) (tv 1) (ts (tv 0))))
    (conj (call PBf [tv 1, tv 2, tv 3, tv 4, tv 0])
    (conj (call Qf [tv 1, tv 2, tv 3, tv 4])
          (call Tf [tv 1, tv 2, tv 3, tv 4, tv 0]))))))

/-- Rocq: `Analysis.GoodsteinFormula.STEPok`, where `n` is a `let`. -/
def STEPok (c d M i : Nat) : Prop :=
  1 ≤ bt c d M 0 i 0 ∧ bt c d M 0 i 0 < M ∧ bt c d M 1 i (bt c d M 0 i 0) = bt c d M 0 (i + 1) 0 + 1 ∧
  PBok c d M i (bt c d M 0 i 0) ∧ Qok c d M i ∧ Tok c d M i (bt c d M 0 i 0)

/-- Rocq: `Analysis.GoodsteinFormula.sat_STEPf`. -/
theorem sat_STEPf (ρ : Nat → Nat) : sat ρ STEPf ↔ STEPok (ρ 0) (ρ 1) (ρ 2) (ρ 3) :=
  (sat_flet _ _ _ _ _ _ _ _).trans
    (and_congr (sat_fle _ _ _) (and_congr (sat_flt _ _ _)
    (and_congr ((sat_flet _ _ _ _ _ _ _ _).trans (sat_flook _ _ _ _ _ _ _ _))
    (and_congr ((sat_call _ _ _).trans (sat_PBf _))
    (and_congr ((sat_call _ _ _).trans (sat_Qf _)) ((sat_call _ _ _).trans (sat_Tf _)))))))

/-- Arguments `x, k, M, c, d`. Rocq: `Analysis.GoodsteinFormula.CHECKf`. -/
def CHECKf : Form :=
  conj (flook 0 (tv 3) (tv 4) (tv 2) tz tz (tv 0))
  (conj (flook 0 (tv 3) (tv 4) (tv 2) (tv 1) tz tz)
        (ball (tv 1) (imp (flt (tv 0) (tv 2)) (call STEPf [tv 4, tv 5, tv 3, tv 0]))))

/-- Rocq: `Analysis.GoodsteinFormula.CHECKok`. -/
def CHECKok (x k M c d : Nat) : Prop :=
  bt c d M 0 0 0 = x ∧ bt c d M 0 k 0 = 0 ∧ ∀ i, i ≤ k → i < k → STEPok c d M i

/-- Rocq: `Analysis.GoodsteinFormula.sat_CHECKf`. -/
theorem sat_CHECKf (ρ : Nat → Nat) : sat ρ CHECKf ↔ CHECKok (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) :=
  and_congr (sat_flook _ _ _ _ _ _ _ _) (and_congr (sat_flook _ _ _ _ _ _ _ _)
    ((sat_ball _ _ _).trans (forall_congr' fun _ => imp_congr_right fun _ =>
      imp_congr (sat_flt _ _ _) ((sat_call _ _ _).trans (sat_STEPf _)))))

/-- Rocq: `Analysis.GoodsteinFormula.isD_STEPf`. -/
theorem isD_STEPf : isD STEPf = true := rfl

/-- Rocq: `Analysis.GoodsteinFormula.isD_CHECKf`. -/
theorem isD_CHECKf : isD CHECKf = true := rfl

/-- The Goodstein sentence is `∀x ∃y θ`, with `x` variable `1` and `y`
variable `0` of `θ`. Rocq: `Analysis.GoodsteinFormula.goodstein_θ`. -/
def goodsteinθ : Form :=
  bex (tv 0) (bex (tv 1) (bex (tv 2) (bex (tv 3) (call CHECKf [tv 5, tv 3, tv 2, tv 1, tv 0]))))

/-- Rocq: `Analysis.GoodsteinFormula.goodstein_sentence`. -/
def goodsteinSentence : Form := all (ex goodsteinθ)

/-- Rocq: `Analysis.GoodsteinFormula.isD_goodstein_θ`. -/
theorem isD_goodstein_θ : isD goodsteinθ = true := rfl

/-- Rocq: `Analysis.GoodsteinFormula.isD_goodstein_Ex`. -/
theorem isD_goodstein_Ex : isD (ex goodsteinθ) = false := rfl

/-- Rocq: `Analysis.GoodsteinFormula.sat_goodstein_θ`. -/
theorem sat_goodstein_θ (x y : Nat) (ρ : Nat → Nat) :
    sat (scons y (scons x ρ)) goodsteinθ ↔
      ∃ k, k ≤ y ∧ ∃ M, M ≤ y ∧ ∃ c, c ≤ y ∧ ∃ d, d ≤ y ∧ CHECKok x k M c d :=
  (sat_bex _ _ _ (by rfl)).trans (exists_congr fun _ => and_congr_right fun _ =>
  (sat_bex _ _ _ (by rfl)).trans (exists_congr fun _ => and_congr_right fun _ =>
  (sat_bex _ _ _ (by rfl)).trans (exists_congr fun _ => and_congr_right fun _ =>
  (sat_bex _ _ _ (by rfl)).trans (exists_congr fun _ => and_congr_right fun _ =>
  (sat_call _ _ _).trans (sat_CHECKf _)))))

/-! ## Soundness: a certificate is the Goodstein sequence -/

/-- The base change at step `i`, from base `i+2` to `i+3`.
Rocq: `Analysis.GoodsteinFormula.bumpi`. -/
def bumpi (i j : Nat) : Nat := hbnInterp (i + 3) (hbnDecompose (i + 2) (plus2_base i) j)

/-- Rocq: `Analysis.GoodsteinFormula.gs`, which converts from `N`. -/
def gs (x i : Nat) : Nat := goodsteinSequence x i

/-- Rocq: `Analysis.GoodsteinFormula.gs_0`. -/
theorem gs_0 (x : Nat) : gs x 0 = x := rfl

/-- Rocq: `Analysis.GoodsteinFormula.gs_succ`. -/
theorem gs_succ (x i : Nat) : gs x (i + 1) = bumpi i (gs x i) - 1 := rfl

/-- Rocq: `Analysis.GoodsteinFormula.dec_zero`. -/
theorem dec_zero (i : Nat) : hbnDecompose (i + 2) (plus2_base i) 0 = .z :=
  hbn_decompose_unique _ _ 0 .z .z rfl

/-- Rocq: `Analysis.GoodsteinFormula.bumpi_0`. -/
theorem bumpi_0 (i : Nat) : bumpi i 0 = 0 := by
  unfold bumpi; rw [dec_zero]; rfl

/-- Rocq: `Analysis.GoodsteinFormula.bumpi_lead`. -/
theorem bumpi_lead (i j e dd r : Nat) (hd1 : 1 ≤ dd) (hd2 : dd < i + 2) (hr : r < (i + 2) ^ e)
    (hj : j = dd * (i + 2) ^ e + r) : bumpi i j = dd * (i + 3) ^ bumpi i e + bumpi i r := by
  have hE := hbn_decompose_proper (i + 2) (plus2_base i) e
  have hR := hbn_decompose_proper (i + 2) (plus2_base i) r
  have hsm : HbnSmallerExp (hbnDecompose (i + 2) (plus2_base i) e) (hbnDecompose (i + 2) (plus2_base i) r) :=
    (hbn_smaller_exp_equiv (plus2_base i) _ _ hR hE).2 (by
      rw [hbn_decompose_correct, hbn_decompose_correct]; exact hr)
  have h := hbn_decompose_unique (i + 2) (plus2_base i) j
    (.term (hbnDecompose (i + 2) (plus2_base i) e) dd (hbnDecompose (i + 2) (plus2_base i) r))
    (.term hE ⟨hd1, hd2⟩ hR hsm)
    (by show (i + 2) ^ hbnInterp (i + 2) _ * dd + hbnInterp (i + 2) _ = j
        rw [hbn_decompose_correct, hbn_decompose_correct, hj, Nat.mul_comm])
  unfold bumpi
  rw [h]
  show (i + 3) ^ bumpi i e * dd + bumpi i r = _
  rw [Nat.mul_comm]; rfl

/-- Rocq: `Analysis.GoodsteinFormula.PB_table`. -/
theorem PB_table (c d M i n : Nat) (h : PBok c d M i n) : ∀ e, e ≤ n → bt c d M 2 i e = (i + 2) ^ e
  | 0, _ => h.1
  | e + 1, he => by
    rw [h.2 e (Nat.le_of_succ_le he) he, PB_table c d M i n h e (Nat.le_of_succ_le he), Nat.pow_succ,
      Nat.mul_comm]

/-- Rocq: `Analysis.GoodsteinFormula.Q_table`. -/
theorem Q_table (c d M i : Nat) (h : Qok c d M i) : ∀ w, w < M → bt c d M 3 i w = (i + 3) ^ w
  | 0, _ => h.1
  | w + 1, hw => by
    rw [h.2 w (Nat.le_of_lt (Nat.lt_of_succ_lt hw)) hw, Q_table c d M i h w (Nat.lt_of_succ_lt hw), Nat.pow_succ,
      Nat.mul_comm]

/-- Rocq: `Analysis.GoodsteinFormula.T_table`. -/
theorem T_table (c d M i n : Nat) (HP : PBok c d M i n) (HQ : Qok c d M i) (HT : Tok c d M i n) :
    ∀ j, j ≤ n → bt c d M 1 i j = bumpi i j := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j IH =>
    intro hj
    cases j with
    | zero => exact HT.1.trans (bumpi_0 i).symm
    | succ j' =>
      obtain ⟨e, he, dd, _, r, _, Ej, Hrp, Hd1, Hd2, HeM, Hval⟩ := HT.2 (j' + 1) hj (Nat.succ_pos _)
      have hen : e ≤ n := Nat.le_trans he hj
      rw [PB_table c d M i n HP e hen] at Ej Hrp
      have hpos : 1 ≤ (i + 2) ^ e := Nat.pow_pos (Nat.succ_pos _)
      have hle : (i + 2) ^ e ≤ j' + 1 := by
        rw [Ej]
        exact Nat.le_trans (Nat.le_mul_of_pos_left _ Hd1) (Nat.le_add_right _ _)
      have Hej : e < j' + 1 := Nat.lt_of_lt_of_le (Nat.lt_pow_self (Nat.succ_lt_succ (Nat.succ_pos i))) hle
      have Hrj : r < j' + 1 := Nat.lt_of_lt_of_le Hrp hle
      have hrn : r ≤ n := Nat.le_trans (Nat.le_of_lt Hrj) hj
      rw [IH e Hej hen] at HeM
      rw [Hval, IH e Hej hen, IH r Hrj hrn, Q_table c d M i HQ _ HeM]
      exact (bumpi_lead i (j' + 1) e dd r Hd1 Hd2 Hrp Ej).symm

/-- Rocq: `Analysis.GoodsteinFormula.check_sound`. -/
theorem check_sound (x k M c d : Nat) (h : CHECKok x k M c d) : goodsteinSequence x k = 0 := by
  obtain ⟨H0, Hk, Hsteps⟩ := h
  have Hg : ∀ i, i ≤ k → bt c d M 0 i 0 = gs x i := by
    intro i
    induction i with
    | zero => intro _; exact H0
    | succ i IH =>
      intro hi
      obtain ⟨_, _, Hnext, HP, HQ, HT⟩ := Hsteps i (Nat.le_of_succ_le hi) hi
      rw [T_table c d M i _ HP HQ HT _ (Nat.le_refl _), IH (Nat.le_of_succ_le hi)] at Hnext
      rw [gs_succ, Hnext]
      rfl
  exact (Hg k (Nat.le_refl k)).symm.trans Hk

/-! ## Truth: every sequence has a certificate -/

/-- Rocq: `Analysis.GoodsteinFormula.lead_exists`. -/
theorem lead_exists (i j : Nat) (hj : 1 ≤ j) :
    ∃ e dd r, 1 ≤ dd ∧ dd < i + 2 ∧ r < (i + 2) ^ e ∧ j = dd * (i + 2) ^ e + r := by
  have Hp := hbn_decompose_proper (i + 2) (plus2_base i) j
  have Hc := hbn_decompose_correct (i + 2) (plus2_base i) j
  revert Hp Hc
  cases hbnDecompose (i + 2) (plus2_base i) j with
  | z => intro _ Hc; exact absurd (Nat.le_trans hj (Nat.le_of_eq Hc.symm)) (Nat.not_succ_le_zero 0)
  | term E D R =>
    intro Hp Hc
    cases Hp with
    | term hE hD hR hs =>
      refine ⟨hbnInterp (i + 2) E, D, hbnInterp (i + 2) R, hD.1, hD.2,
        (hbn_smaller_exp_equiv (plus2_base i) R E hR hE).1 hs, ?_⟩
      rw [← Hc]
      show (i + 2) ^ hbnInterp (i + 2) E * D + hbnInterp (i + 2) R = _
      rw [Nat.mul_comm]

/-- Rocq: `Analysis.GoodsteinFormula.bumpi_pos`. -/
theorem bumpi_pos (i n : Nat) (hn : 1 ≤ n) : 1 ≤ bumpi i n := by
  obtain ⟨e, dd, r, H1, H2, H3, H4⟩ := lead_exists i n hn
  rw [bumpi_lead i n e dd r H1 H2 H3 H4]
  exact Nat.le_trans (Nat.mul_pos H1 (Nat.pow_pos (Nat.succ_pos _))) (Nat.le_add_right _ _)

/-- Rocq: `Analysis.GoodsteinFormula.Mc`. -/
def Mc (x k0 : Nat) : Nat := sumf (fun i => gs x i + sumf (bumpi i) (gs x i + 1)) k0 + 1

/-- Rocq: `Analysis.GoodsteinFormula.Mc_gs`. -/
theorem Mc_gs (x k0 i : Nat) (hi : i < k0) : gs x i < Mc x k0 :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _)
    (sumf_ge (fun i => gs x i + sumf (bumpi i) (gs x i + 1)) k0 i hi))

/-- Rocq: `Analysis.GoodsteinFormula.Mc_bump`. -/
theorem Mc_bump (x k0 i e : Nat) (hi : i < k0) (he : e ≤ gs x i) : bumpi i e < Mc x k0 :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_trans (sumf_ge (bumpi i) _ e (Nat.lt_succ_of_le he))
    (Nat.le_add_left _ _)) (sumf_ge (fun i => gs x i + sumf (bumpi i) (gs x i + 1)) k0 i hi))

/-- Rocq: `Analysis.GoodsteinFormula.Mc_pos`. -/
theorem Mc_pos (x k0 : Nat) : 0 < Mc x k0 := Nat.succ_pos _

/-- The entry `j` of table `tag` at step `i`; the `match` inside Rocq's `entry`. -/
def entryAt (x tag i j : Nat) : Nat :=
  match tag with
  | 0 => if j = 0 then gs x i else 0
  | 1 => bumpi i j
  | 2 => (i + 2) ^ j
  | _ => (i + 3) ^ j

/-- Rocq: `Analysis.GoodsteinFormula.entry`. -/
def entry (x k0 idx : Nat) : Nat :=
  entryAt x (Nat.mod idx 4) (Nat.div (Nat.div idx 4) (Mc x k0)) (Nat.mod (Nat.div idx 4) (Mc x k0))

/-- Rocq: `Analysis.GoodsteinFormula.entry_decode`. -/
theorem entry_decode (x k0 tag i j : Nat) (ht : tag < 4) (hj : j < Mc x k0) :
    entry x k0 (4 * (i * Mc x k0 + j) + tag) = entryAt x tag i j := by
  have e0 : 4 * (i * Mc x k0 + j) + tag = (i * Mc x k0 + j) * 4 + tag := by rw [Nat.mul_comm]
  unfold entry
  rw [mod_unique ht e0, div_unique ht e0, div_unique hj rfl, mod_unique hj rfl]

/-- Rocq: `Analysis.GoodsteinFormula.Lc`. -/
def Lc (x k0 : Nat) : Nat := 4 * ((k0 + 1) * Mc x k0)

/-- Rocq: `Analysis.GoodsteinFormula.bt_val`. -/
theorem bt_val (x k0 c d : Nat) (Hcd : ∀ idx, idx < Lc x k0 → beta c d idx = entry x k0 idx)
    (tag i j : Nat) (ht : tag < 4) (hi : i ≤ k0) (hj : j < Mc x k0) :
    bt c d (Mc x k0) tag i j = entryAt x tag i j := by
  unfold bt
  rw [Hcd _ ?_, entry_decode x k0 tag i j ht hj]
  have h1 : i * Mc x k0 + j + 1 ≤ (k0 + 1) * Mc x k0 :=
    Nat.le_trans (Nat.add_le_add_left hj _) (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (Nat.succ_le_succ hi))
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left ht _) (Nat.mul_le_mul_left 4 h1)

/-- Rocq: `Analysis.GoodsteinFormula.check_true`. -/
theorem check_true (x k0 : Nat) (Hk0 : gs x k0 = 0) (Hbefore : ∀ j, j < k0 → gs x j ≠ 0) (c d : Nat)
    (Hcd : ∀ idx, idx < Lc x k0 → beta c d idx = entry x k0 idx) : CHECKok x k0 (Mc x k0) c d := by
  have HM := Mc_pos x k0
  have bv := bt_val x k0 c d Hcd
  refine ⟨bv 0 0 0 (by decide) (Nat.zero_le _) HM, (bv 0 k0 0 (by decide) (Nat.le_refl _) HM).trans Hk0,
    fun i _ hi => ?_⟩
  have hik : i ≤ k0 := Nat.le_of_lt hi
  have Hn1 : 1 ≤ gs x i := Nat.pos_of_ne_zero (Hbefore i hi)
  have HnM := Mc_gs x k0 i hi
  have hn : bt c d (Mc x k0) 0 i 0 = gs x i := bv 0 i 0 (by decide) hik HM
  unfold STEPok
  rw [hn]
  refine ⟨Hn1, HnM, ?_, ⟨bv 2 i 0 (by decide) hik HM, fun e _ he => ?_⟩,
    ⟨bv 3 i 0 (by decide) hik HM, fun w _ hw => ?_⟩, ⟨(bv 1 i 0 (by decide) hik HM).trans (bumpi_0 i), ?_⟩⟩
  · rw [bv 1 i (gs x i) (by decide) hik HnM, bv 0 (i + 1) 0 (by decide) hi HM]
    show bumpi i (gs x i) = bumpi i (gs x i) - 1 + 1
    exact (Nat.sub_add_cancel (bumpi_pos i _ Hn1)).symm
  · rw [bv 2 i (e + 1) (by decide) hik (Nat.lt_of_le_of_lt he HnM), bv 2 i e (by decide) hik
      (Nat.lt_trans (Nat.lt_succ_self e) (Nat.lt_of_le_of_lt he HnM))]
    show (i + 2) ^ (e + 1) = (i + 2) * (i + 2) ^ e
    rw [Nat.pow_succ, Nat.mul_comm]
  · rw [bv 3 i (w + 1) (by decide) hik hw, bv 3 i w (by decide) hik (Nat.lt_of_succ_lt hw)]
    show (i + 3) ^ (w + 1) = (i + 3) * (i + 3) ^ w
    rw [Nat.pow_succ, Nat.mul_comm]
  · intro j hj hj1
    obtain ⟨e, dd, r, Hd1, Hd2, Hr, Ej⟩ := lead_exists i j hj1
    have hpos : 1 ≤ (i + 2) ^ e := Nat.pow_pos (Nat.succ_pos _)
    have hle : (i + 2) ^ e ≤ j := by
      rw [Ej]; exact Nat.le_trans (Nat.le_mul_of_pos_left _ Hd1) (Nat.le_add_right _ _)
    have Hej : e ≤ j := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_pow_self (Nat.succ_lt_succ (Nat.succ_pos i))) hle)
    have Hrj : r ≤ j := Nat.le_of_lt (Nat.lt_of_lt_of_le Hr hle)
    have Hdd : dd ≤ j := by
      rw [Ej]; exact Nat.le_trans (Nat.le_mul_of_pos_right _ hpos) (Nat.le_add_right _ _)
    have hjM : j < Mc x k0 := Nat.lt_of_le_of_lt hj HnM
    have heM : e < Mc x k0 := Nat.lt_of_le_of_lt Hej hjM
    have hrM : r < Mc x k0 := Nat.lt_of_le_of_lt Hrj hjM
    have HeM := Mc_bump x k0 i e hi (Nat.le_trans Hej hj)
    refine ⟨e, Hej, dd, Hdd, r, Hrj, ?_⟩
    rw [bv 2 i e (by decide) hik heM, bv 1 i e (by decide) hik heM, bv 3 i (entryAt x 1 i e) (by decide) hik HeM,
      bv 1 i j (by decide) hik hjM, bv 1 i r (by decide) hik hrM]
    exact ⟨Ej, Hr, Hd1, Hd2, HeM, bumpi_lead i j e dd r Hd1 Hd2 Hr Ej⟩

/-- Rocq: `Analysis.GoodsteinFormula.goodstein_θ_true`. -/
theorem goodstein_θ_true (x : Nat) : ∃ y, sat (scons y (scons x ρ0)) goodsteinθ := by
  obtain ⟨i, hi⟩ := goodstein_zero x
  obtain ⟨k0, _, Hk0, Hbefore⟩ := goodstein_least_zero x i hi
  obtain ⟨c, d, Hcd⟩ := beta_exists (entry x k0) (Lc x k0)
  refine ⟨k0 + Mc x k0 + c + d, (sat_goodstein_θ _ _ _).2 ⟨k0, ?_, Mc x k0, ?_, c, ?_, d, ?_,
    check_true x k0 Hk0 Hbefore c d Hcd⟩⟩
  · exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ c) (Nat.le_add_right _ d))
  · exact Nat.le_trans (Nat.le_add_left _ k0) (Nat.le_trans (Nat.le_add_right _ c) (Nat.le_add_right _ d))
  · exact Nat.le_trans (Nat.le_add_left c _) (Nat.le_add_right _ d)
  · exact Nat.le_add_left d _

/-- Rocq: `Analysis.GoodsteinFormula.goodstein_θ_sound`. -/
theorem goodstein_θ_sound (x y : Nat) (h : sat (scons y (scons x ρ0)) goodsteinθ) :
    ∃ k, k ≤ y ∧ goodsteinSequence x k = 0 := by
  obtain ⟨k, hk, M, _, c, _, d, _, hc⟩ := (sat_goodstein_θ x y ρ0).1 h
  exact ⟨k, hk, check_sound x k M c d hc⟩

/-! ## Goodstein's theorem: true, and independent of PA -/

/-- Rocq: `Analysis.GoodsteinFormula.goodstein_sentence_true`. -/
theorem goodstein_sentence_true : sat ρ0 goodsteinSentence := fun x => goodstein_θ_true x

/-- Rocq: `Analysis.GoodsteinFormula.goodstein_independent`. -/
theorem goodstein_independent : ¬ PA [] goodsteinSentence :=
  goodstein_unprovable goodsteinθ isD_goodstein_θ isD_goodstein_Ex goodstein_θ_sound

end ConstructiveOrdinals.GoodsteinFormula
