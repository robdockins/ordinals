import ConstructiveOrdinals.Cantor
import ConstructiveOrdinals.Prelude.List

/-!
# Goodstein sequences

Hereditary base-`b` notation (`HBN`), its interpretation as natural numbers,
and its "shadow" as an ordinal below ε₀, obtained by replacing the base with ω.
Each step of a Goodstein sequence strictly decreases the shadow, so every
Goodstein sequence reaches zero (`goodstein_zero`). The first terms of the
sequence starting at 4 are checked against OEIS A056193 by kernel computation.

Rocq works with binary `N`. Here everything is `Nat`, which the kernel also
computes with in binary. Rocq's `lia` steps are replaced by explicit
arithmetic. Division and remainder are `ConstructiveOrdinals.Nat.div` and
`ConstructiveOrdinals.Nat.mod`, which have axiom-free specifications.
Rocq's well-founded `Program Fixpoint`s become recursion on explicit fuel, with
equations proved separately. This keeps them computable in the kernel, as
Rocq's `Acc_intro_generator` trick does.

Ported from the Rocq file `GoodsteinSequences.v`.
-/

namespace ConstructiveOrdinals

universe u

open Ordinal

namespace Goodstein

/-! ## Arithmetic lemmas -/

private theorem base_pos {base : Nat} (h : 1 < base) : 0 < base :=
  Nat.lt_trans Nat.zero_lt_one h

private theorem pow_pos' {base : Nat} (h : 1 < base) (e : Nat) : 0 < base ^ e :=
  Nat.pow_pos (base_pos h)

/-- `n = m + 1` for a positive `n`. -/
private theorem exists_succ {n : Nat} (h : 0 < n) : ∃ m, n = m + 1 :=
  match n, h with
  | m + 1, _ => ⟨m, rfl⟩

private theorem mul_add_one' (a m : Nat) : a * (m + 1) = a * m + a := Nat.mul_succ a m

private theorem pow_add_one' (a k : Nat) : a ^ (k + 1) = a ^ k * a := Nat.pow_succ a k

/-- `b ^ (k + 1) = b ^ k * (b - 1) + b ^ k`. -/
private theorem pow_succ_pred {base : Nat} (h : 1 < base) (k : Nat) :
    base ^ (k + 1) = base ^ k * (base - 1) + base ^ k := by
  obtain ⟨m, rfl⟩ := exists_succ (base_pos h)
  exact (pow_add_one' _ _).trans (mul_add_one' _ m)

private theorem pred_base {base : Nat} (h : 1 < base) : 0 < base - 1 ∧ base - 1 < base := by
  obtain ⟨m, rfl⟩ := exists_succ (base_pos h)
  exact ⟨Nat.lt_of_succ_lt_succ h, Nat.lt_succ_self m⟩

/-- `b^e * n + x < b^e * (n + 1)` when `x < b^e`. -/
private theorem term_lt_succ {p n x : Nat} (hx : x < p) : p * n + x < p * (n + 1) :=
  Nat.add_lt_add_left hx _

/-- `b^e * (n + 1) ≤ b^(e+1)` when `n < b`. -/
private theorem mul_succ_le_pow {base n : Nat} (e : Nat) (hn : n < base) :
    base ^ e * (n + 1) ≤ base ^ (e + 1) :=
  Nat.mul_le_mul_left _ hn

/-- Rocq: `GoodsteinSequences.base_term_lt_lemma1`. -/
theorem base_term_lt_lemma1 (base e1 n1 x1 e2 n2 x2 : Nat) (hbase : 1 < base)
    (_hn1 : 0 < n1 ∧ n1 < base) (hn2 : 0 < n2 ∧ n2 < base) (hx1 : x1 < base ^ e1) (he : e1 < e2) :
    base ^ e1 * n1 + x1 < base ^ e2 * n2 + x2 :=
  calc base ^ e1 * n1 + x1
      < base ^ e1 * (n1 + 1) := term_lt_succ hx1
    _ ≤ base ^ (e1 + 1) := mul_succ_le_pow e1 _hn1.2
    _ ≤ base ^ e2 := Nat.pow_le_pow_right (base_pos hbase) he
    _ ≤ base ^ e2 * n2 := Nat.le_mul_of_pos_right _ hn2.1
    _ ≤ base ^ e2 * n2 + x2 := Nat.le_add_right _ _

/-- Rocq: `GoodsteinSequences.base_term_lt_lemma2`. -/
theorem base_term_lt_lemma2 (base e1 n1 x1 e2 n2 x2 : Nat) (_hbase : 1 < base)
    (_hn1 : 0 < n1 ∧ n1 < base) (_hn2 : 0 < n2 ∧ n2 < base) (hx1 : x1 < base ^ e1) (he : e1 = e2)
    (hn : n1 < n2) : base ^ e1 * n1 + x1 < base ^ e2 * n2 + x2 := by
  subst he
  calc base ^ e1 * n1 + x1
      < base ^ e1 * (n1 + 1) := term_lt_succ hx1
    _ ≤ base ^ e1 * n2 := Nat.mul_le_mul_left _ hn
    _ ≤ base ^ e1 * n2 + x2 := Nat.le_add_right _ _

private theorem lt_irrefl_of_eq {a b : Nat} (h : a = b) (hlt : a < b) : False :=
  Nat.lt_irrefl b (h ▸ hlt)

/-- Rocq: `GoodsteinSequences.base_term_eq_lemma`. -/
theorem base_term_eq_lemma (base e1 n1 x1 e2 n2 x2 : Nat) (hbase : 1 < base)
    (hn1 : 0 < n1 ∧ n1 < base) (hn2 : 0 < n2 ∧ n2 < base) (hx1 : x1 < base ^ e1) (hx2 : x2 < base ^ e2)
    (h : base ^ e1 * n1 + x1 = base ^ e2 * n2 + x2) : e1 = e2 ∧ n1 = n2 ∧ x1 = x2 := by
  match Nat.lt_trichotomy e1 e2 with
  | .inl he =>
    exact (lt_irrefl_of_eq h (base_term_lt_lemma1 base e1 n1 x1 e2 n2 x2 hbase hn1 hn2 hx1 he)).elim
  | .inr (.inr he) =>
    exact (lt_irrefl_of_eq h.symm (base_term_lt_lemma1 base e2 n2 x2 e1 n1 x1 hbase hn2 hn1 hx2 he)).elim
  | .inr (.inl he) =>
    subst he
    match Nat.lt_trichotomy n1 n2 with
    | .inl hn =>
      exact (lt_irrefl_of_eq h (base_term_lt_lemma2 base e1 n1 x1 e1 n2 x2 hbase hn1 hn2 hx1 rfl hn)).elim
    | .inr (.inr hn) =>
      exact (lt_irrefl_of_eq h.symm
        (base_term_lt_lemma2 base e1 n2 x2 e1 n1 x1 hbase hn2 hn1 hx2 rfl hn)).elim
    | .inr (.inl hn) =>
      subst hn
      exact ⟨rfl, rfl, Nat.add_left_cancel h⟩

/-- Rocq: `GoodsteinSequences.base_term_eq_lemma'`. -/
theorem base_term_eq_lemma' (base e1 n1 x1 e2 n2 x2 : Nat) (hbase : 1 < base)
    (hn1 : 0 < n1 ∧ n1 < base) (hn2 : 0 < n2 ∧ n2 < base) (hx1 : 0 < x1 ∧ x1 ≤ base ^ e1)
    (hx2 : 0 < x2 ∧ x2 ≤ base ^ e2) (h : base ^ e1 * n1 + x1 = base ^ e2 * n2 + x2) :
    e1 = e2 ∧ n1 = n2 ∧ x1 = x2 := by
  have h₁ : x1 - 1 + 1 = x1 := Nat.sub_one_add_one (Nat.ne_of_gt hx1.1)
  have h₂ : x2 - 1 + 1 = x2 := Nat.sub_one_add_one (Nat.ne_of_gt hx2.1)
  have h' : base ^ e1 * n1 + (x1 - 1) = base ^ e2 * n2 + (x2 - 1) := by
    refine Nat.add_right_cancel (m := 1) ?_
    rw [Nat.add_assoc, Nat.add_assoc, h₁, h₂, h]
  obtain ⟨he, hn, hx⟩ := base_term_eq_lemma base e1 n1 (x1 - 1) e2 n2 (x2 - 1) hbase hn1 hn2
    (Nat.lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hx1.1)) hx1.2)
    (Nat.lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hx2.1)) hx2.2) h'
  refine ⟨he, hn, ?_⟩
  rw [← h₁, ← h₂, hx]

/-- Rocq: `GoodsteinSequences.exp_lt_lemma`. -/
theorem exp_lt_lemma (e n base x : Nat) (h : 0 < n ∧ n < base) : e < base ^ e * n + x :=
  calc e < base ^ e := Nat.lt_pow_self (Nat.lt_of_le_of_lt h.1 h.2)
    _ ≤ base ^ e * n := Nat.le_mul_of_pos_right _ h.1
    _ ≤ base ^ e * n + x := Nat.le_add_right _ _

/-- Rocq: `GoodsteinSequences.x_lt_lemma`. -/
theorem x_lt_lemma (e n base x : Nat) (h : 0 < n ∧ n < base) : x < base ^ e * n + x := by
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.pow_pos (Nat.lt_trans h.1 h.2)) h.1)

/-! ## Hereditary base notation -/

/-- Hereditary base notation, with the base left implicit. `term e n x`
stands for `base ^ e * n + x`; see `hbnInterp`. Rocq: `GoodsteinSequences.HBN`. -/
inductive HBN : Type
  /-- Rocq: `HBN_Z`. -/
  | z : HBN
  /-- Rocq: `HBN_Term`. -/
  | term : HBN → Nat → HBN → HBN

/-- Rocq: `GoodsteinSequences.hbn_interp`. -/
def hbnInterp (base : Nat) : HBN → Nat
  | .z => 0
  | .term e n x => base ^ hbnInterp base e * n + hbnInterp base x

/-- A strict order on the syntax, which agrees with `<` on interpretations
of proper terms (`hbn_lt_equiv`). Rocq: `GoodsteinSequences.hbn_lt`. -/
inductive HbnLt : HBN → HBN → Prop
  /-- Rocq: `HBN_LT_Z`. -/
  | z (e n x) : HbnLt .z (.term e n x)
  /-- Rocq: `HBN_LT_e`. -/
  | e {e1 n1 x1 e2 n2 x2} : HbnLt e1 e2 → HbnLt (.term e1 n1 x1) (.term e2 n2 x2)
  /-- Rocq: `HBN_LT_n`. -/
  | n {e1 n1 x1 e2 n2 x2} : e1 = e2 → n1 < n2 → HbnLt (.term e1 n1 x1) (.term e2 n2 x2)
  /-- Rocq: `HBN_LT_x`. -/
  | x {e1 n1 x1 e2 n2 x2} : e1 = e2 → n1 = n2 → HbnLt x1 x2 → HbnLt (.term e1 n1 x1) (.term e2 n2 x2)

/-- Rocq: `GoodsteinSequences.hbn_lt_total`. -/
theorem hbn_lt_total : ∀ a b : HBN, HbnLt a b ∨ a = b ∨ HbnLt b a
  | .z, .z => .inr (.inl rfl)
  | .z, .term _ _ _ => .inl (.z _ _ _)
  | .term _ _ _, .z => .inr (.inr (.z _ _ _))
  | .term e1 n1 x1, .term e2 n2 x2 =>
    match hbn_lt_total e1 e2 with
    | .inl h => .inl (.e h)
    | .inr (.inr h) => .inr (.inr (.e h))
    | .inr (.inl he) =>
      match Nat.lt_trichotomy n1 n2 with
      | .inl h => .inl (.n he h)
      | .inr (.inr h) => .inr (.inr (.n he.symm h))
      | .inr (.inl hn) =>
        match hbn_lt_total x1 x2 with
        | .inl h => .inl (.x he hn h)
        | .inr (.inr h) => .inr (.inr (.x he.symm hn.symm h))
        | .inr (.inl hx) => .inr (.inl (by subst he; subst hn; subst hx; rfl))

/-- `HbnSmallerExp e x`: every exponent in the sum `x` is below `e`.
Rocq: `GoodsteinSequences.hbn_smaller_exp`. -/
inductive HbnSmallerExp : HBN → HBN → Prop
  /-- Rocq: `HBN_smaller_exp_Z`. -/
  | z (e) : HbnSmallerExp e .z
  /-- Rocq: `HBN_smaller_exp_Term`. -/
  | term {e e'} (n x) : HbnLt e' e → HbnSmallerExp e (.term e' n x)

/-- A term is proper for `base` if every multiplicity is nonzero and below
the base, and the exponents of each sum strictly decrease.
Rocq: `GoodsteinSequences.hbn_proper`. -/
inductive HbnProper (base : Nat) : HBN → Prop
  /-- Rocq: `HBN_proper_Z`. -/
  | z : HbnProper base .z
  /-- Rocq: `HBN_proper_Term`. -/
  | term {e n x} : HbnProper base e → 0 < n ∧ n < base → HbnProper base x → HbnSmallerExp e x →
      HbnProper base (.term e n x)

private theorem proper_term_inv {base n : Nat} {e x : HBN} (h : HbnProper base (.term e n x)) :
    HbnProper base e ∧ (0 < n ∧ n < base) ∧ HbnProper base x ∧ HbnSmallerExp e x := by
  cases h with
  | term he hn hx hs => exact ⟨he, hn, hx, hs⟩

private theorem interp_term_pos {base n : Nat} {e x : HBN} (h : HbnProper base (.term e n x)) :
    0 < hbnInterp base (.term e n x) :=
  have hn := (proper_term_inv h).2.1
  Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.pow_pos (Nat.lt_trans hn.1 hn.2)) hn.1) (Nat.le_add_right _ _)

/-- Rocq: `GoodsteinSequences.interp0_iff`. -/
theorem interp0_iff (base : Nat) (x : HBN) (h : HbnProper base x) : hbnInterp base x < 1 ↔ x = .z := by
  refine ⟨fun hlt => ?_, fun hx => hx ▸ Nat.zero_lt_one⟩
  match x, h with
  | .z, _ => rfl
  | .term _ _ _, h => exact absurd hlt (Nat.not_lt_of_le (interp_term_pos h))

section lt_equiv

variable {base : Nat} (hbase : 1 < base)
include hbase

/-- Soundness of `HbnLt`, together with the bound `I x < base ^ I e` for a
proper sum `x` with exponents below `e`. -/
private theorem lt_sound : ∀ t : HBN,
    (∀ b, HbnProper base t → HbnProper base b → HbnLt t b → hbnInterp base t < hbnInterp base b) ∧
    (∀ e, HbnProper base e → HbnProper base t → HbnSmallerExp e t →
      hbnInterp base t < base ^ hbnInterp base e)
  | .z => by
    refine ⟨fun b _ hb h => ?_, fun _ _ _ _ => pow_pos' hbase _⟩
    cases h
    exact interp_term_pos hb
  | .term e' n' x' => by
    have ihe := lt_sound e'
    have ihx := lt_sound x'
    refine ⟨fun b ht hb h => ?_, fun e he ht hs => ?_⟩
    · obtain ⟨he', hn', hx', hs'⟩ := proper_term_inv ht
      cases h with
      | e h =>
        obtain ⟨he2, hn2, _, _⟩ := proper_term_inv hb
        exact base_term_lt_lemma1 _ _ _ _ _ _ _ hbase hn' hn2 (ihx.2 e' he' hx' hs') (ihe.1 _ he' he2 h)
      | n he hn =>
        obtain ⟨_, hn2, _, _⟩ := proper_term_inv hb
        exact base_term_lt_lemma2 _ _ _ _ _ _ _ hbase hn' hn2 (ihx.2 e' he' hx' hs')
          (congrArg (hbnInterp base) he) hn
      | x he hn h =>
        subst he; subst hn
        exact Nat.add_lt_add_left (ihx.1 _ hx' (proper_term_inv hb).2.2.1 h) _
    · obtain ⟨he', hn', hx', hs'⟩ := proper_term_inv ht
      cases hs with
      | term _ _ hlt =>
        calc base ^ hbnInterp base e' * n' + hbnInterp base x'
            < base ^ hbnInterp base e' * (n' + 1) := term_lt_succ (ihx.2 e' he' hx' hs')
          _ ≤ base ^ (hbnInterp base e' + 1) := mul_succ_le_pow _ hn'.2
          _ ≤ base ^ hbnInterp base e := Nat.pow_le_pow_right (base_pos hbase) (ihe.1 e he' he hlt)

/-- Rocq: `GoodsteinSequences.hbn_lt_equiv`. -/
theorem hbn_lt_equiv (a b : HBN) (ha : HbnProper base a) (hb : HbnProper base b) :
    HbnLt a b ↔ hbnInterp base a < hbnInterp base b := by
  refine ⟨(lt_sound hbase a).1 b ha hb, fun h => ?_⟩
  match hbn_lt_total a b with
  | .inl h' => exact h'
  | .inr (.inl e) => subst e; exact absurd h (Nat.lt_irrefl _)
  | .inr (.inr h') => exact absurd ((lt_sound hbase b).1 a hb ha h') (Nat.lt_asymm h)

/-- Rocq: `GoodsteinSequences.hbn_smaller_exp_equiv`. -/
theorem hbn_smaller_exp_equiv (a b : HBN) (ha : HbnProper base a) (hb : HbnProper base b) :
    HbnSmallerExp b a ↔ hbnInterp base a < base ^ hbnInterp base b := by
  refine ⟨(lt_sound hbase a).2 b hb ha, fun h => ?_⟩
  match a, ha with
  | .z, _ => exact .z b
  | .term e' n' x', ha =>
    obtain ⟨he', hn', _, _⟩ := proper_term_inv ha
    have hge : base ^ hbnInterp base e' ≤ hbnInterp base (.term e' n' x') :=
      Nat.le_trans (Nat.le_mul_of_pos_right _ hn'.1) (Nat.le_add_right _ _)
    match hbn_lt_total e' b with
    | .inl hlt => exact .term n' x' hlt
    | .inr (.inl e) => subst e; exact absurd h (Nat.not_lt_of_le hge)
    | .inr (.inr hgt) =>
      exact absurd h (Nat.not_lt_of_le (Nat.le_trans
        (Nat.pow_le_pow_right (base_pos hbase) (Nat.le_of_lt ((lt_sound hbase b).1 e' hb he' hgt))) hge))

/-- Rocq: `GoodsteinSequences.lt_equiv`. -/
theorem lt_equiv (sz : Nat) (a b : HBN) (_hsz : hbnInterp base a + hbnInterp base b ≤ sz)
    (ha : HbnProper base a) (hb : HbnProper base b) :
    (HbnLt a b ↔ hbnInterp base a < hbnInterp base b) ∧
      (HbnSmallerExp b a ↔ hbnInterp base a < base ^ hbnInterp base b) :=
  ⟨hbn_lt_equiv hbase a b ha hb, hbn_smaller_exp_equiv hbase a b ha hb⟩

/-- Rocq: `GoodsteinSequences.hbn_proper_unique`. -/
theorem hbn_proper_unique (a b : HBN) (ha : HbnProper base a) (hb : HbnProper base b)
    (h : hbnInterp base a = hbnInterp base b) : a = b :=
  match hbn_lt_total a b with
  | .inl hlt => (Nat.lt_irrefl (hbnInterp base b) (h ▸ (hbn_lt_equiv hbase a b ha hb).1 hlt)).elim
  | .inr (.inl e) => e
  | .inr (.inr hgt) => (Nat.lt_irrefl (hbnInterp base b) (h ▸ (hbn_lt_equiv hbase b a hb ha).1 hgt)).elim

end lt_equiv

/-- Rocq: `GoodsteinSequences.hbn_proper_mono`. -/
theorem hbn_proper_mono {a b : Nat} (x : HBN) (hab : a ≤ b) (h : HbnProper a x) : HbnProper b x := by
  induction h with
  | z => exact .z
  | term _ hn _ hs ihe ihx => exact .term ihe ⟨hn.1, Nat.lt_of_lt_of_le hn.2 hab⟩ ihx hs

/-- `term e n x`, or just `x` when `n = 0`. Rocq: `GoodsteinSequences.hbn_term`. -/
def hbnTerm (e : HBN) (n : Nat) (x : HBN) : HBN := if n = 0 then x else .term e n x

private theorem hbnTerm_zero (e x : HBN) : hbnTerm e 0 x = x := ite_eq_left rfl

private theorem hbnTerm_ne {e x : HBN} {n : Nat} (h : n ≠ 0) : hbnTerm e n x = .term e n x := ite_eq_right h

/-- Rocq: `GoodsteinSequences.hbn_term_correct`. -/
theorem hbn_term_correct (base : Nat) (e : HBN) (n : Nat) (x : HBN) :
    hbnInterp base (hbnTerm e n x) = hbnInterp base (.term e n x) := by
  by_cases h : n = 0
  · subst h
    rw [hbnTerm_zero]
    show hbnInterp base x = base ^ hbnInterp base e * 0 + hbnInterp base x
    rw [Nat.mul_zero, Nat.zero_add]
  · rw [hbnTerm_ne h]

/-! ## Decomposition into hereditary base notation -/

section hbn_decompose

variable (base : Nat) (Hbase : 1 < base) (sz : Nat) (rec : (n : Nat) → n < sz → HBN)
include Hbase

/-- The first proof obligation of `hbn_decompose_step`. -/
theorem hbn_decompose_step_obligation_1 {n i : Nat} (Hni : n * base ^ i ≤ sz) (Hnz : n ≠ 0) :
    i < sz :=
  calc i < base ^ i := Nat.lt_pow_self Hbase
    _ ≤ base ^ i * n := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero Hnz)
    _ = n * base ^ i := Nat.mul_comm _ _
    _ ≤ sz := Hni

/-- The second proof obligation of `hbn_decompose_step`. -/
theorem hbn_decompose_step_obligation_2 {n i : Nat} (Hni : n * base ^ i ≤ sz) :
    Nat.div n base * base ^ (i + 1) ≤ sz :=
  calc Nat.div n base * base ^ (i + 1)
      = Nat.div n base * base * base ^ i := by
        rw [pow_add_one', Nat.mul_comm (base ^ i) base, Nat.mul_assoc]
    _ ≤ n * base ^ i := Nat.mul_le_mul_right _ (Nat.div_mul_le n (base_pos Hbase))
    _ ≤ sz := Hni

/-- `hbn_decompose_step` with explicit fuel. -/
def hbnDecomposeStepFuel : (fuel n i : Nat) → HBN → n * base ^ i ≤ sz → HBN
  | 0, _, _, tail, _ => tail
  | fuel + 1, n, i, tail, Hni =>
    if Hnz : n = 0 then tail
    else hbnDecomposeStepFuel fuel (Nat.div n base) (i + 1)
      (hbnTerm (rec i (hbn_decompose_step_obligation_1 base Hbase sz Hni Hnz)) (Nat.mod n base) tail)
      (hbn_decompose_step_obligation_2 base Hbase sz Hni)

/-- Adds the base-`base` digits of `n`, scaled by `base ^ i`, to the front of
`tail`, decomposing each exponent with `rec`.
Rocq: `GoodsteinSequences.hbn_decompose_step`. -/
def hbnDecomposeStep (n i : Nat) (tail : HBN) (Hni : n * base ^ i ≤ sz) : HBN :=
  hbnDecomposeStepFuel base Hbase sz rec (n + 1) n i tail Hni

private theorem hbnDecomposeStepFuel_succ (fuel n i : Nat) (tail : HBN) (Hni : n * base ^ i ≤ sz) :
    hbnDecomposeStepFuel base Hbase sz rec (fuel + 1) n i tail Hni =
      if Hnz : n = 0 then tail
      else hbnDecomposeStepFuel base Hbase sz rec fuel (Nat.div n base) (i + 1)
        (hbnTerm (rec i (hbn_decompose_step_obligation_1 base Hbase sz Hni Hnz)) (Nat.mod n base) tail)
        (hbn_decompose_step_obligation_2 base Hbase sz Hni) :=
  rfl

private theorem hbnDecomposeStepFuel_congr : ∀ (fuel₁ fuel₂ n i : Nat) (tail : HBN)
    (Hni : n * base ^ i ≤ sz), n < fuel₁ → n < fuel₂ →
    hbnDecomposeStepFuel base Hbase sz rec fuel₁ n i tail Hni =
      hbnDecomposeStepFuel base Hbase sz rec fuel₂ n i tail Hni
  | 0, _, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel₁ + 1, fuel₂ + 1, n, i, tail, Hni, h₁, h₂ => by
    rw [hbnDecomposeStepFuel_succ, hbnDecomposeStepFuel_succ]
    by_cases hn : n = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
    · rw [dite_eq_right hn, dite_eq_right hn]
      have hd := Nat.div_lt (Nat.pos_of_ne_zero hn) Hbase
      exact hbnDecomposeStepFuel_congr fuel₁ fuel₂ _ _ _ _
        (Nat.lt_of_lt_of_le hd (Nat.le_of_lt_succ h₁)) (Nat.lt_of_lt_of_le hd (Nat.le_of_lt_succ h₂))

/-- Rocq: `GoodsteinSequences.hbn_decompose_step_eq`. -/
theorem hbn_decompose_step_eq (n i : Nat) (tail : HBN) (Hni : n * base ^ i ≤ sz) :
    hbnDecomposeStep base Hbase sz rec n i tail Hni =
      if Hnz : n = 0 then tail
      else hbnDecomposeStep base Hbase sz rec (Nat.div n base) (i + 1)
        (hbnTerm (rec i (hbn_decompose_step_obligation_1 base Hbase sz Hni Hnz)) (Nat.mod n base) tail)
        (hbn_decompose_step_obligation_2 base Hbase sz Hni) := by
  unfold hbnDecomposeStep
  rw [hbnDecomposeStepFuel_succ]
  by_cases hn : n = 0
  · rw [dite_eq_left hn, dite_eq_left hn]
  · rw [dite_eq_right hn, dite_eq_right hn]
    have hd := Nat.div_lt (Nat.pos_of_ne_zero hn) Hbase
    exact hbnDecomposeStepFuel_congr base Hbase sz rec _ _ _ _ _ _ hd (Nat.lt_succ_self _)

/-- Rocq: `GoodsteinSequences.hbn_decompose_step_correct`. -/
theorem hbn_decompose_step_correct (rec_correct : ∀ n H, hbnInterp base (rec n H) = n) :
    ∀ (n i : Nat) (tail : HBN) (Hni : n * base ^ i ≤ sz),
      hbnInterp base (hbnDecomposeStep base Hbase sz rec n i tail Hni) = n * base ^ i + hbnInterp base tail := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i tail Hni
    rw [hbn_decompose_step_eq]
    by_cases hn : n = 0
    · rw [dite_eq_left hn]; subst hn; rw [Nat.zero_mul, Nat.zero_add]
    · rw [dite_eq_right hn, ih _ (Nat.div_lt (Nat.pos_of_ne_zero hn) Hbase), hbn_term_correct]
      show Nat.div n base * base ^ (i + 1) +
          (base ^ hbnInterp base (rec i _) * Nat.mod n base + hbnInterp base tail) = _
      rw [rec_correct, ← Nat.add_assoc]
      refine congrArg (· + hbnInterp base tail) ?_
      calc Nat.div n base * base ^ (i + 1) + base ^ i * Nat.mod n base
          = (Nat.div n base * base) * base ^ i + Nat.mod n base * base ^ i := by
            rw [pow_add_one', Nat.mul_comm (base ^ i) base, ← Nat.mul_assoc,
              Nat.mul_comm (base ^ i) (Nat.mod n base)]
        _ = (Nat.div n base * base + Nat.mod n base) * base ^ i := (Nat.add_mul _ _ _).symm
        _ = n * base ^ i := by rw [Nat.div_add_mod n (base_pos Hbase)]

/-- Rocq: `GoodsteinSequences.hbn_decompose_step_proper`. -/
theorem hbn_decompose_step_proper (rec_correct : ∀ n H, hbnInterp base (rec n H) = n)
    (rec_proper : ∀ n H, HbnProper base (rec n H)) :
    ∀ (n i : Nat) (tail : HBN) (Hni : n * base ^ i ≤ sz),
      hbnInterp base tail < base ^ i → HbnProper base tail →
      HbnProper base (hbnDecomposeStep base Hbase sz rec n i tail Hni) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i tail Hni htail1 htail2
    rw [hbn_decompose_step_eq]
    by_cases hn : n = 0
    · rw [dite_eq_left hn]; exact htail2
    · rw [dite_eq_right hn]
      have hmod := Nat.mod_lt n (base_pos Hbase)
      refine ih _ (Nat.div_lt (Nat.pos_of_ne_zero hn) Hbase) _ _ _ ?_ ?_
      · rw [hbn_term_correct]
        show base ^ hbnInterp base (rec i _) * Nat.mod n base + hbnInterp base tail < _
        rw [rec_correct]
        exact Nat.lt_of_lt_of_le (term_lt_succ htail1) (mul_succ_le_pow i hmod)
      · by_cases hm : Nat.mod n base = 0
        · rw [hm, hbnTerm_zero]; exact htail2
        · rw [hbnTerm_ne hm]
          refine .term (rec_proper _ _) ⟨Nat.pos_of_ne_zero hm, hmod⟩ htail2
            ((hbn_smaller_exp_equiv Hbase _ _ htail2 (rec_proper _ _)).2 ?_)
          rw [rec_correct]
          exact htail1

end hbn_decompose

/-- Rocq: `GoodsteinSequences.hbn_decompose_step_cong`. -/
theorem hbn_decompose_step_cong (base : Nat) (Hbase : 1 < base) (n sz : Nat)
    (f g : (x : Nat) → x < sz → HBN) (i : Nat) (tail : HBN) (Hni : n * base ^ i ≤ sz)
    (Hfg : ∀ x r, f x r = g x r) :
    hbnDecomposeStep base Hbase sz f n i tail Hni = hbnDecomposeStep base Hbase sz g n i tail Hni := by
  unfold hbnDecomposeStep
  generalize n + 1 = fuel
  induction fuel generalizing n i tail Hni with
  | zero => rfl
  | succ fuel ih =>
    rw [hbnDecomposeStepFuel_succ, hbnDecomposeStepFuel_succ]
    by_cases hn : n = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
    · rw [dite_eq_right hn, dite_eq_right hn, Hfg i]
      exact ih _ _ _ _

private theorem n_mul_pow_zero (base n : Nat) : n * base ^ 0 ≤ n := Nat.le_of_eq (Nat.mul_one n)

/-- `hbn_decompose` with explicit fuel. -/
def hbnDecomposeFuel (base : Nat) (Hbase : 1 < base) : Nat → Nat → HBN
  | 0, _ => .z
  | fuel + 1, n =>
    hbnDecomposeStep base Hbase n (fun x _ => hbnDecomposeFuel base Hbase fuel x) n 0 .z (n_mul_pow_zero base n)

/-- The hereditary base-`base` representation of `n`.
Rocq: `GoodsteinSequences.hbn_decompose`. -/
def hbnDecompose (base : Nat) (Hbase : 1 < base) (n : Nat) : HBN := hbnDecomposeFuel base Hbase (n + 1) n

private theorem hbnDecomposeFuel_congr (base : Nat) (Hbase : 1 < base) :
    ∀ fuel₁ fuel₂ n : Nat, n < fuel₁ → n < fuel₂ →
      hbnDecomposeFuel base Hbase fuel₁ n = hbnDecomposeFuel base Hbase fuel₂ n
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel₁ + 1, fuel₂ + 1, n, h₁, h₂ =>
    hbn_decompose_step_cong base Hbase n n _ _ 0 .z _ fun x r =>
      hbnDecomposeFuel_congr base Hbase fuel₁ fuel₂ x
        (Nat.lt_of_lt_of_le r (Nat.le_of_lt_succ h₁)) (Nat.lt_of_lt_of_le r (Nat.le_of_lt_succ h₂))

/-- Rocq: `GoodsteinSequences.hbn_decompose_eq`. -/
theorem hbn_decompose_eq (base : Nat) (Hbase : 1 < base) (n : Nat) :
    hbnDecompose base Hbase n =
      hbnDecomposeStep base Hbase n (fun x _ => hbnDecompose base Hbase x) n 0 .z (n_mul_pow_zero base n) :=
  hbn_decompose_step_cong base Hbase n n _ _ 0 .z _ fun x r =>
    hbnDecomposeFuel_congr base Hbase n (x + 1) x r (Nat.lt_succ_self x)

/-- Rocq: `GoodsteinSequences.hbn_decompose_correct`. -/
theorem hbn_decompose_correct (base : Nat) (Hbase : 1 < base) (n : Nat) :
    hbnInterp base (hbnDecompose base Hbase n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [hbn_decompose_eq, hbn_decompose_step_correct base Hbase n _ (fun x h => ih x h)]
    show n * 1 + 0 = n
    rw [Nat.mul_one, Nat.add_zero]

/-- Rocq: `GoodsteinSequences.hbn_decompose_proper`. -/
theorem hbn_decompose_proper (base : Nat) (Hbase : 1 < base) (n : Nat) :
    HbnProper base (hbnDecompose base Hbase n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [hbn_decompose_eq]
    exact hbn_decompose_step_proper base Hbase n _ (fun x _ => hbn_decompose_correct base Hbase x)
      (fun x h => ih x h) n 0 .z _ Nat.zero_lt_one .z

/-- Rocq: `GoodsteinSequences.hbn_decompose_unique`. -/
theorem hbn_decompose_unique (base : Nat) (Hbase : 1 < base) (n : Nat) (hbn : HBN)
    (h₁ : HbnProper base hbn) (h₂ : hbnInterp base hbn = n) : hbnDecompose base Hbase n = hbn :=
  hbn_proper_unique Hbase _ _ (hbn_decompose_proper base Hbase n) h₁
    ((hbn_decompose_correct base Hbase n).trans h₂.symm)

/-! ## Goodstein sequences -/

/-- Rocq: `GoodsteinSequences.plus2_base`. -/
theorem plus2_base (i : Nat) : 1 < i + 2 := Nat.le_add_left 2 i

/-- Rocq: `GoodsteinSequences.plus3_base`. -/
theorem plus3_base (i : Nat) : 1 < i + 3 := Nat.lt_of_lt_of_le (plus2_base i) (Nat.le_succ _)

/-- The Goodstein sequence starting at `init`: write the current value in
hereditary base `i + 2`, replace the base by `i + 3`, and subtract one.
Rocq: `GoodsteinSequences.goodstein_sequence`. -/
def goodsteinSequence (init : Nat) : Nat → Nat
  | 0 => init
  | i + 1 =>
    let hbn := hbnDecompose (i + 2) (plus2_base i) (goodsteinSequence init i)
    hbnInterp (i + 3) hbn - 1

/-- Rocq: `GoodsteinSequences.goodstein_sequence0`. -/
theorem goodstein_sequence0 (x : Nat) : goodsteinSequence x 0 = x := rfl

/-- Rocq: `GoodsteinSequences.goodstein_sequence_succ`. -/
theorem goodstein_sequence_succ (x i : Nat) :
    goodsteinSequence x (i + 1) =
      let hbn := hbnDecompose (i + 2) (plus2_base i) (goodsteinSequence x i)
      hbnInterp (i + 3) hbn - 1 :=
  rfl

/-- The start of the Goodstein sequence for 4, from the OEIS
(https://oeis.org/A056193). Rocq: `GoodsteinSequences.A056193`. -/
def A056193 : List Nat :=
  [4, 26, 41, 60, 83, 109, 139, 173, 211, 253, 299, 348, 401, 458, 519, 584, 653, 726, 803, 884, 969,
   1058, 1151, 1222, 1295, 1370, 1447, 1526, 1607, 1690, 1775, 1862, 1951, 2042, 2135, 2230, 2327,
   2426, 2527, 2630, 2735, 2842, 2951, 3062, 3175, 3290, 3407]

/-- Rocq: `GoodsteinSequences.all_index`. -/
def allIndex : List Nat := List.range' 0 A056193.length

/-- Rocq: `GoodsteinSequences.compute_goodstein4`. -/
def computeGoodstein4 : List Nat := allIndex.map fun i => goodsteinSequence 4 i

/-- Checked by kernel computation. Rocq: `GoodsteinSequences.compute_goodstein_eq`. -/
theorem compute_goodstein_eq : computeGoodstein4 = A056193 := by decide +kernel

private theorem nthError_map_range' {α : Type} (f : Nat → α) (n : Nat) :
    ∀ (s i : Nat), i < n → List.nthError ((List.range' s n).map f) i = some (f (s + i)) := by
  induction n with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro s i h
    cases i with
    | zero => rfl
    | succ i =>
      show List.nthError ((List.range' (s + 1) n).map f) i = some (f (s + (i + 1)))
      rw [ih (s + 1) i (Nat.lt_of_succ_lt_succ h), Nat.add_right_comm, Nat.add_assoc]

/-- The computed sequence agrees with the OEIS sequence A056193.
Rocq: `GoodsteinSequences.goodstein4_correct_initial_sequence`. -/
theorem goodstein4_correct_initial_sequence (i : Nat) (hi : i < A056193.length) :
    List.nthError A056193 i = some (goodsteinSequence 4 i) := by
  have h : List.nthError computeGoodstein4 i = some (goodsteinSequence 4 (0 + i)) :=
    nthError_map_range' (fun i => goodsteinSequence 4 i) A056193.length 0 i hi
  rw [compute_goodstein_eq, Nat.zero_add] at h
  exact h

/-- Rocq: `GoodsteinSequences.goodstein_hbn`. -/
def goodsteinHbn (init i : Nat) : HBN := hbnDecompose (i + 2) (plus2_base i) (goodsteinSequence init i)

/-- Rocq: `GoodsteinSequences.goodstein_alt`. -/
theorem goodstein_alt (init i : Nat) :
    goodsteinSequence init (i + 1) = hbnInterp (i + 3) (goodsteinHbn init i) - 1 :=
  rfl

/-! ## One step of a Goodstein sequence -/

mutual
/-- `HbnDec base x x'`: `x'` is the proper representation of `x - 1`.
Rocq: `GoodsteinSequences.hbn_dec`. -/
inductive HbnDec (base : Nat) : HBN → HBN → Prop
  /-- Rocq: `hbn_dec_Term_x`. -/
  | term_x {e n x x'} : HbnDec base x x' → HbnDec base (.term e n x) (.term e n x')
  /-- Rocq: `hbn_dec_Term_n`. -/
  | term_n {e n x} : HbnExpDec base e x → HbnDec base (.term e n .z) (hbnTerm e (n - 1) x)
/-- `HbnExpDec base x x'`: `x'` is the proper representation of
`base ^ x - 1`. Rocq: `GoodsteinSequences.hbn_exp_dec`. -/
inductive HbnExpDec (base : Nat) : HBN → HBN → Prop
  /-- Rocq: `hbn_exp_dec_Z`. -/
  | z : HbnExpDec base .z .z
  /-- Rocq: `hbn_exp_dec_Term_x`. -/
  | term_x {e e' w} : HbnDec base e e' → HbnExpDec base e' w → HbnExpDec base e (.term e' (base - 1) w)
end

section hbn_dec

variable {base : Nat} (Hbase : 1 < base)
include Hbase

omit Hbase in
private theorem proper_hbnTerm_inv {e x : HBN} {n : Nat} (h : HbnProper base (hbnTerm e n x)) :
    HbnProper base x := by
  by_cases hn : n = 0
  · rw [hn, hbnTerm_zero] at h; exact h
  · rw [hbnTerm_ne hn] at h; exact (proper_term_inv h).2.2.1

/-- The `→` directions of `hbn_dec_correct`, by induction on derivations. -/
private theorem hbn_dec_sound :
    (∀ x x', HbnDec base x x' → HbnProper base x → HbnProper base x' →
      hbnInterp base x = hbnInterp base x' + 1) ∧
    (∀ x x', HbnExpDec base x x' → HbnProper base x → HbnProper base x' →
      base ^ hbnInterp base x = hbnInterp base x' + 1) := by
  have m₁ : ∀ {e n x x'}, HbnDec base x x' →
      (HbnProper base x → HbnProper base x' → hbnInterp base x = hbnInterp base x' + 1) →
      HbnProper base (.term e n x) → HbnProper base (.term e n x') →
      hbnInterp base (.term e n x) = hbnInterp base (.term e n x') + 1 :=
    fun {e n _ _} _ ih hx hx' =>
      congrArg (base ^ hbnInterp base e * n + ·) (ih (proper_term_inv hx).2.2.1 (proper_term_inv hx').2.2.1)
  have m₂ : ∀ {e n x}, HbnExpDec base e x →
      (HbnProper base e → HbnProper base x → base ^ hbnInterp base e = hbnInterp base x + 1) →
      HbnProper base (.term e n .z) → HbnProper base (hbnTerm e (n - 1) x) →
      hbnInterp base (.term e n .z) = hbnInterp base (hbnTerm e (n - 1) x) + 1 := by
    intro e n x _ ih hx hx'
    obtain ⟨he, hn, _, _⟩ := proper_term_inv hx
    obtain ⟨m, rfl⟩ := exists_succ hn.1
    rw [hbn_term_correct]
    show base ^ hbnInterp base e * (m + 1) + 0 = base ^ hbnInterp base e * m + hbnInterp base x + 1
    rw [Nat.add_zero, mul_add_one']
    exact congrArg (base ^ hbnInterp base e * m + ·) (ih he (proper_hbnTerm_inv hx'))
  have m₃ : HbnProper base .z → HbnProper base .z → base ^ hbnInterp base .z = hbnInterp base .z + 1 :=
    fun _ _ => rfl
  have m₄ : ∀ {e e' w}, HbnDec base e e' → HbnExpDec base e' w →
      (HbnProper base e → HbnProper base e' → hbnInterp base e = hbnInterp base e' + 1) →
      (HbnProper base e' → HbnProper base w → base ^ hbnInterp base e' = hbnInterp base w + 1) →
      HbnProper base e → HbnProper base (.term e' (base - 1) w) →
      base ^ hbnInterp base e = hbnInterp base (.term e' (base - 1) w) + 1 := by
    intro e e' w _ _ ih₁ ih₂ hx hx'
    obtain ⟨he', _, hz, _⟩ := proper_term_inv hx'
    show base ^ hbnInterp base e = base ^ hbnInterp base e' * (base - 1) + hbnInterp base w + 1
    rw [ih₁ hx he', pow_succ_pred Hbase]
    exact congrArg (base ^ hbnInterp base e' * (base - 1) + ·) (ih₂ he' hz)
  exact ⟨fun x x' h => HbnDec.rec
      (motive_1 := fun x x' _ => HbnProper base x → HbnProper base x' →
        hbnInterp base x = hbnInterp base x' + 1)
      (motive_2 := fun x x' _ => HbnProper base x → HbnProper base x' →
        base ^ hbnInterp base x = hbnInterp base x' + 1) m₁ m₂ m₃ m₄ h,
    fun x x' h => HbnExpDec.rec
      (motive_1 := fun x x' _ => HbnProper base x → HbnProper base x' →
        hbnInterp base x = hbnInterp base x' + 1)
      (motive_2 := fun x x' _ => HbnProper base x → HbnProper base x' →
        base ^ hbnInterp base x = hbnInterp base x' + 1) m₁ m₂ m₃ m₄ h⟩

/-- The `←` directions of `hbn_dec_correct`, by strong induction on the
interpretation of `x`. -/
private theorem hbn_dec_complete : ∀ (k : Nat) (x : HBN), hbnInterp base x = k → HbnProper base x →
    (∀ x', HbnProper base x' → hbnInterp base x = hbnInterp base x' + 1 → HbnDec base x x') ∧
    (∀ x', HbnProper base x' → base ^ hbnInterp base x = hbnInterp base x' + 1 → HbnExpDec base x x') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro x hk hx
  have ih' : ∀ y, hbnInterp base y < k → HbnProper base y →
      (∀ x', HbnProper base x' → hbnInterp base y = hbnInterp base x' + 1 → HbnDec base y x') ∧
      (∀ x', HbnProper base x' → base ^ hbnInterp base y = hbnInterp base x' + 1 → HbnExpDec base y x') :=
    fun y hy hy' => ih _ hy y rfl hy'
  clear ih
  subst hk
  have hdec : ∀ x', HbnProper base x' → hbnInterp base x = hbnInterp base x' + 1 → HbnDec base x x' := by
    intro x' hx' h
    cases x with
    | z => exact Nat.noConfusion h
    | term e n x2 =>
      obtain ⟨he, hn, hx2, hs⟩ := proper_term_inv hx
      cases x2 with
      | z =>
        have hlt : hbnInterp base e < hbnInterp base (.term e n .z) := exp_lt_lemma _ _ _ _ hn
        obtain ⟨m, rfl⟩ := exists_succ hn.1
        have h' : base ^ hbnInterp base e * m + base ^ hbnInterp base e = hbnInterp base x' + 1 :=
          (mul_add_one' _ _).symm.trans h
        cases m with
        | zero =>
          have hexp := (ih' e hlt he).2 x' hx' (by rw [← h', Nat.mul_zero, Nat.zero_add])
          exact HbnDec.term_n (n := 1) hexp
        | succ m =>
          cases x' with
          | z =>
            have h2 : 1 < base ^ hbnInterp base e * (m + 1) + base ^ hbnInterp base e :=
              Nat.add_le_add (Nat.mul_pos (pow_pos' Hbase _) (Nat.zero_lt_succ m)) (pow_pos' Hbase _)
            exact absurd (h' ▸ h2 : 1 < hbnInterp base .z + 1) (Nat.lt_irrefl 1)
          | term e' n' x2' =>
            obtain ⟨he', hn', hx2', hs'⟩ := proper_term_inv hx'
            have hbound := (hbn_smaller_exp_equiv Hbase _ _ hx2' he').1 hs'
            obtain ⟨hee, hnn, hxx⟩ := base_term_eq_lemma' base _ (m + 1) _ _ n' (hbnInterp base x2' + 1)
              Hbase ⟨Nat.zero_lt_succ m, Nat.lt_of_succ_lt hn.2⟩ hn'
              ⟨pow_pos' Hbase _, Nat.le_refl _⟩ ⟨Nat.zero_lt_succ _, hbound⟩ h'
            have hee' : e' = e := hbn_proper_unique Hbase _ _ he' he hee.symm
            subst hee'; subst hnn
            exact HbnDec.term_n (n := m + 2) ((ih' e' hlt he).2 x2' hx2' hxx)
      | term e2 n2 x3 =>
        have hpos : 0 < hbnInterp base (.term e2 n2 x3) := interp_term_pos hx2
        have hbound := (hbn_smaller_exp_equiv Hbase _ _ hx2 he).1 hs
        have hlt : hbnInterp base (.term e2 n2 x3) < hbnInterp base (.term e n (.term e2 n2 x3)) :=
          x_lt_lemma _ _ _ _ hn
        cases x' with
        | z =>
          have h2 : 1 < hbnInterp base (.term e n (.term e2 n2 x3)) :=
            Nat.add_le_add (Nat.mul_pos (pow_pos' Hbase _) hn.1) hpos
          exact absurd (h ▸ h2 : 1 < hbnInterp base .z + 1) (Nat.lt_irrefl 1)
        | term e' n' x2' =>
          obtain ⟨he', hn', hx2', hs'⟩ := proper_term_inv hx'
          have hbound' := (hbn_smaller_exp_equiv Hbase _ _ hx2' he').1 hs'
          obtain ⟨hee, hnn, hxx⟩ := base_term_eq_lemma' base _ n _ _ n' (hbnInterp base x2' + 1) Hbase hn hn'
            ⟨hpos, Nat.le_of_lt hbound⟩ ⟨Nat.zero_lt_succ _, hbound'⟩ h
          have hee' : e' = e := hbn_proper_unique Hbase _ _ he' he hee.symm
          subst hee'; subst hnn
          exact .term_x ((ih' _ hlt hx2).1 x2' hx2' hxx)
  refine ⟨hdec, fun x' hx' h => ?_⟩
  cases x with
  | z =>
    have h0 : hbnInterp base x' = 0 := Nat.succ.inj (h.symm : hbnInterp base x' + 1 = 0 + 1)
    rw [(interp0_iff base x' hx').1 (h0 ▸ Nat.zero_lt_one)]
    exact .z
  | term e n x2 =>
    have hpos := interp_term_pos hx
    obtain ⟨e', he', hk⟩ : ∃ e', HbnProper base e' ∧ hbnInterp base e' + 1 = hbnInterp base (.term e n x2) :=
      ⟨_, hbn_decompose_proper base Hbase (hbnInterp base (.term e n x2) - 1), by
        rw [hbn_decompose_correct]; exact Nat.sub_one_add_one (Nat.ne_of_gt hpos)⟩
    obtain ⟨w, hz, hzi⟩ : ∃ w, HbnProper base w ∧ hbnInterp base w + 1 = base ^ hbnInterp base e' :=
      ⟨_, hbn_decompose_proper base Hbase (base ^ hbnInterp base e' - 1), by
        rw [hbn_decompose_correct]; exact Nat.sub_one_add_one (Nat.ne_of_gt (pow_pos' Hbase _))⟩
    have hlt : hbnInterp base e' < hbnInterp base (.term e n x2) := hk ▸ Nat.lt_succ_self _
    have hterm : HbnProper base (.term e' (base - 1) w) :=
      .term he' (pred_base Hbase) hz ((hbn_smaller_exp_equiv Hbase _ _ hz he').2 (hzi ▸ Nat.lt_succ_self _))
    have hx'eq : x' = .term e' (base - 1) w := by
      refine hbn_proper_unique Hbase _ _ hx' hterm (Nat.add_right_cancel (m := 1) ?_)
      show hbnInterp base x' + 1 = base ^ hbnInterp base e' * (base - 1) + hbnInterp base w + 1
      rw [← h, ← hk, pow_succ_pred Hbase, Nat.add_assoc, hzi]
    subst hx'eq
    exact .term_x (hdec e' he' hk.symm) ((ih' e' hlt he').2 w hz hzi.symm)

/-- Rocq: `GoodsteinSequences.hbn_dec_correct`. -/
theorem hbn_dec_correct (x x' : HBN) (hx : HbnProper base x) (hx' : HbnProper base x') :
    (HbnDec base x x' ↔ hbnInterp base x = hbnInterp base x' + 1) ∧
      (HbnExpDec base x x' ↔ base ^ hbnInterp base x = hbnInterp base x' + 1) :=
  ⟨⟨fun h => (hbn_dec_sound Hbase).1 x x' h hx hx',
     fun h => (hbn_dec_complete Hbase _ x rfl hx).1 x' hx' h⟩,
   ⟨fun h => (hbn_dec_sound Hbase).2 x x' h hx hx',
     fun h => (hbn_dec_complete Hbase _ x rfl hx).2 x' hx' h⟩⟩

end hbn_dec

/-- Rocq: `GoodsteinSequences.goodstein_hbn_decreasing`. -/
theorem goodstein_hbn_decreasing (x i : Nat) :
    goodsteinHbn x i = .z ∨ HbnDec (i + 3) (goodsteinHbn x i) (goodsteinHbn x (i + 1)) := by
  have hp : HbnProper (i + 3) (goodsteinHbn x i) :=
    hbn_proper_mono _ (Nat.le_succ _) (hbn_decompose_proper _ _ _)
  have hp' : HbnProper (i + 3) (goodsteinHbn x (i + 1)) := hbn_decompose_proper _ _ _
  match h : goodsteinHbn x i, hp with
  | .z, _ => exact .inl rfl
  | .term e n y, hp =>
    refine .inr ((hbn_dec_correct (plus3_base i) _ _ hp hp').1.2 ?_)
    have hpos := interp_term_pos hp
    show _ = hbnInterp (i + 3) (hbnDecompose (i + 3) (plus2_base (i + 1)) (goodsteinSequence x (i + 1))) + 1
    rw [hbn_decompose_correct, goodstein_alt, h]
    exact (Nat.sub_one_add_one (Nat.ne_of_gt hpos)).symm

/-! ## The ordinal shadow -/

/-- The ordinal obtained by replacing the base by ω.
Rocq: `GoodsteinSequences.hbn_shadow`. -/
def hbnShadow : HBN → Ordinal.{u}
  | .z => 0
  | .term e n x => ω ^ hbnShadow e * ofNat n + hbnShadow x

section shadow

variable {base : Nat} (Hbase : 1 < base)
include Hbase

omit Hbase in
/-- `ω ^ a * n + x < ω ^ a * (n + 1)` when `x < ω ^ a`. -/
private theorem shadow_term_lt {a x : Ordinal.{u}} (n : Nat) (h : x < ω ^ a) :
    ω ^ a * ofNat n + x < ω ^ a * ofNat (n + 1) :=
  lt_of_lt_of_le (add_lt_add_left _ h) (mul_succ _ _).ge

private theorem hbn_shadow_dec :
    (∀ x y, HbnDec base x y → HbnProper base x →
      HbnProper base y ∧ hbnShadow.{u} y < hbnShadow.{u} x) ∧
    (∀ x y, HbnExpDec base x y → HbnProper base x →
      HbnProper base y ∧ hbnShadow.{u} y < ω ^ hbnShadow.{u} x) := by
  have s₁ : ∀ {e n x x'}, HbnDec base x x' →
      (HbnProper base x → HbnProper base x' ∧ hbnShadow.{u} x' < hbnShadow.{u} x) →
      HbnProper base (.term e n x) →
      HbnProper base (.term e n x') ∧ hbnShadow.{u} (.term e n x') < hbnShadow.{u} (.term e n x) := by
    intro e n x x' hd ih hx
    obtain ⟨he, hn, hx0, hs⟩ := proper_term_inv hx
    obtain ⟨hx0', hlt⟩ := ih hx0
    have hi := (hbn_dec_sound Hbase).1 _ _ hd hx0 hx0'
    refine ⟨.term he hn hx0' ((hbn_smaller_exp_equiv Hbase _ _ hx0' he).2 ?_), add_lt_add_left _ hlt⟩
    exact Nat.lt_trans (hi ▸ Nat.lt_succ_self _) ((hbn_smaller_exp_equiv Hbase _ _ hx0 he).1 hs)
  have s₂ : ∀ {e n x}, HbnExpDec base e x →
      (HbnProper base e → HbnProper base x ∧ hbnShadow.{u} x < ω ^ hbnShadow.{u} e) →
      HbnProper base (.term e n .z) →
      HbnProper base (hbnTerm e (n - 1) x) ∧
        hbnShadow.{u} (hbnTerm e (n - 1) x) < hbnShadow.{u} (.term e n .z) := by
    intro e n x hd ih hx
    obtain ⟨he, hn, _, _⟩ := proper_term_inv hx
    obtain ⟨hx0, hlt⟩ := ih he
    have hi := (hbn_dec_sound Hbase).2 _ _ hd he hx0
    obtain ⟨m, rfl⟩ := exists_succ hn.1
    show HbnProper base (hbnTerm e m x) ∧
      hbnShadow (hbnTerm e m x) < ω ^ hbnShadow e * ofNat (m + 1) + 0
    cases m with
    | zero =>
      rw [hbnTerm_zero]
      exact ⟨hx0, lt_of_lt_of_le hlt (le_trans (mul_one _).ge (le_add_right _ _))⟩
    | succ m =>
      rw [hbnTerm_ne (Nat.add_one_ne_zero m)]
      refine ⟨.term he ⟨Nat.zero_lt_succ m, Nat.lt_of_succ_lt hn.2⟩ hx0
        ((hbn_smaller_exp_equiv Hbase _ _ hx0 he).2 (hi ▸ Nat.lt_succ_self _)), ?_⟩
      exact lt_of_lt_of_le (shadow_term_lt (m + 1) hlt) (le_add_right _ _)
  have s₃ : HbnProper base .z → HbnProper base .z ∧ hbnShadow.{u} .z < ω ^ hbnShadow.{u} .z :=
    fun _ => ⟨.z, pow_pos ω _⟩
  have s₄ : ∀ {e e' w}, HbnDec base e e' → HbnExpDec base e' w →
      (HbnProper base e → HbnProper base e' ∧ hbnShadow.{u} e' < hbnShadow.{u} e) →
      (HbnProper base e' → HbnProper base w ∧ hbnShadow.{u} w < ω ^ hbnShadow.{u} e') →
      HbnProper base e →
      HbnProper base (.term e' (base - 1) w) ∧ hbnShadow.{u} (.term e' (base - 1) w) < ω ^ hbnShadow.{u} e := by
    intro e e' w _ hz ih₁ ih₂ hx
    obtain ⟨he', hlt₁⟩ := ih₁ hx
    obtain ⟨hz', hlt₂⟩ := ih₂ he'
    have hi := (hbn_dec_sound Hbase).2 _ _ hz he' hz'
    refine ⟨.term he' (pred_base Hbase) hz'
      ((hbn_smaller_exp_equiv Hbase _ _ hz' he').2 (hi ▸ Nat.lt_succ_self _)), ?_⟩
    calc ω ^ hbnShadow e' * ofNat (base - 1) + hbnShadow w
        < ω ^ hbnShadow e' * ofNat (base - 1 + 1) := shadow_term_lt _ hlt₂
      _ = ω ^ hbnShadow e' * ofNat base := by
          rw [Nat.sub_one_add_one (Nat.ne_of_gt (base_pos Hbase))]
      _ < ω ^ hbnShadow e' * ω := mul_lt_mul_left (pow_pos ω _) (index_lt ω ⟨base⟩)
      _ ≈ ω ^ succ (hbnShadow e') := equiv_symm (pow_succ _ omega_gt0)
      _ ≤ ω ^ hbnShadow e := pow_le_pow_right ω (succ_least hlt₁)
  exact ⟨fun x y h => HbnDec.rec
      (motive_1 := fun x y _ => HbnProper base x → HbnProper base y ∧ hbnShadow.{u} y < hbnShadow.{u} x)
      (motive_2 := fun x y _ => HbnProper base x → HbnProper base y ∧ hbnShadow.{u} y < ω ^ hbnShadow.{u} x)
      s₁ s₂ s₃ s₄ h,
    fun x y h => HbnExpDec.rec
      (motive_1 := fun x y _ => HbnProper base x → HbnProper base y ∧ hbnShadow.{u} y < hbnShadow.{u} x)
      (motive_2 := fun x y _ => HbnProper base x → HbnProper base y ∧ hbnShadow.{u} y < ω ^ hbnShadow.{u} x)
      s₁ s₂ s₃ s₄ h⟩

/-- Each step of a Goodstein sequence decreases the shadow.
Rocq: `GoodsteinSequences.hbn_dec_shadow_dec`. -/
theorem hbn_dec_shadow_dec (x : HBN) (hx : HbnProper base x) :
    (∀ y, HbnDec base x y → HbnProper base y ∧ hbnShadow.{u} y < hbnShadow.{u} x) ∧
      (∀ y, HbnExpDec base x y → HbnProper base y ∧ hbnShadow.{u} y < ω ^ hbnShadow.{u} x) :=
  ⟨fun y h => (hbn_shadow_dec Hbase).1 x y h hx, fun y h => (hbn_shadow_dec Hbase).2 x y h hx⟩

end shadow

/-- Rocq: `GoodsteinSequences.shadow_le0_hbn_Z`. -/
theorem shadow_le0_hbn_Z (base : Nat) (hbn : HBN) (h : HbnProper base hbn) (h0 : hbnShadow.{u} hbn ≤ 0) :
    hbn = .z := by
  match hbn, h with
  | .z, _ => rfl
  | .term e n x, h =>
    obtain ⟨_, hn, _, _⟩ := proper_term_inv h
    refine (lt_irrefl (0 : Ordinal.{u}) (lt_of_lt_of_le ?_ h0)).elim
    calc (0 : Ordinal.{u}) < ω ^ hbnShadow e := pow_pos ω _
      _ ≈ ω ^ hbnShadow e * 1 := equiv_symm (mul_one _)
      _ ≤ ω ^ hbnShadow e * ofNat n := mul_le_mul_left _ (ofNat_monotone hn.1)
      _ ≤ ω ^ hbnShadow e * ofNat n + hbnShadow x := le_add_right _ _

/-- Rocq: `GoodsteinSequences.hbn_decompose_zero`. -/
theorem hbn_decompose_zero (base : Nat) (Hbase : 1 < base) (x : Nat) (h : hbnDecompose base Hbase x = .z) :
    x = 0 :=
  (hbn_decompose_correct base Hbase x).symm.trans (congrArg (hbnInterp base) h)

/-- Rocq: `GoodsteinSequences.goodstein_hbn_zero`. -/
theorem goodstein_hbn_zero (o : Ordinal.{u}) :
    ∀ x i : Nat, hbnShadow.{u} (goodsteinHbn x i) ≤ o → ∃ j, hbnShadow.{u} (goodsteinHbn x j) ≤ 0 := by
  induction o using ltRec with
  | ind o ih =>
    intro x i h
    match goodstein_hbn_decreasing x i with
    | .inl hz => exact ⟨i, hz ▸ le_refl _⟩
    | .inr hd =>
      have hp : HbnProper (i + 3) (goodsteinHbn x i) :=
        hbn_proper_mono _ (Nat.le_succ _) (hbn_decompose_proper _ _ _)
      obtain ⟨_, hlt⟩ := (hbn_dec_shadow_dec.{u} (plus3_base i) _ hp).1 _ hd
      exact ih _ (lt_of_lt_of_le hlt h) x (i + 1) (le_refl _)

/-- Every Goodstein sequence reaches zero.
Rocq: `GoodsteinSequences.goodstein_zero`. -/
theorem goodstein_zero (x : Nat) : ∃ i, goodsteinSequence x i = 0 := by
  obtain ⟨i, hi⟩ := goodstein_hbn_zero.{0} (hbnShadow (goodsteinHbn x 0)) x 0 (le_refl _)
  exact ⟨i, hbn_decompose_zero _ _ _ (shadow_le0_hbn_Z (i + 2) _ (hbn_decompose_proper _ _ _) hi)⟩

end Goodstein

end ConstructiveOrdinals
