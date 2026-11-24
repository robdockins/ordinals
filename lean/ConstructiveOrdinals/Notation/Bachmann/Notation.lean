import ConstructiveOrdinals.Bachmann.Enumeration

/-!
# A notation system up to the Bachmann–Howard ordinal

A small notation is 0 or `φ_T(y)`, where `y` is a small notation and `T` is an
index. An index is 0 or `Ω^e·c + r`, where the exponent `e` and the rest `r`
are indices and the coefficient `c` is a small notation; in normal form the
exponents strictly decrease, so an index is an Ω-Cantor normal form. Indices
denote canonical index trees, built from `embed`, `badd`, `bmul` and `bexpΩ`;
`φ` is taken at the base `1+x`.

We denote `φ_T(y)` by the provably normal hierarchy `bphi`, whose values are
complete; Bachmann's `φ` (`bach`) agrees with it on every notation
(`BS_denote_bach`). The argument `y` cannot be folded into the index:
`bach f (T + ξ) 0` is `veblen G ξ 0`, not `G ξ`.

## Layout of the development

- `Notation/Bachmann/Notation`: syntax, denotation, normal forms, the
  comparison algorithm and its correctness (this file).
- `Notation/Bachmann/Fragment`: Schütte's Klammersymbols embed as the indices
  below `Ω^Ω`; the fragment has order type the Large Veblen Ordinal.
- `Notation/Bachmann/Cantor`: Cantor decomposition, hence the arithmetic.
- `Notation/Bachmann/Bound`: every normal form lies below the
  Bachmann–Howard ordinal; dominance of coefficients.
- `Notation/Bachmann/Normalize`: normalization of proper terms by rewriting
  (strong normalization, confluence).
- `Notation/Bachmann/Interpolants`: fundamental sequences and interpolants.
- `Notation/Bachmann/OrderType`: natural product; the normal forms have order
  type the Bachmann–Howard ordinal.
- `Notation/Bachmann/Absorb`: offsets and absorption of the leading summand.
- `Notation/Bachmann/Improper`: hereditary absorption and the normalizer
  `normSX` for improper terms; every notation lies below `BHO₁`.

Ported from the Rocq file `Notation/BachmannNotation.v`.

Lean notes:

- The notation keeps its Rocq names (`BS_denote`, `cmpS`, `BS_nf`, …).
- Rocq's mutual induction schemes are mutual structural recursions.
- The local `below` of Rocq's `cmpS` is `coefsBelowWith`, parameterized by the
  comparison, so that `cmpS`/`cmpI` are structural in the fuel.
- `BS_decide_order` returns a `PSum`.
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd

mutual
/-- Small notations. Rocq: `Notation.BachmannNotation.BSmall`. -/
inductive BSmall : Type where
  | BZ : BSmall
  | BN : BIdx → BSmall → BSmall

/-- Indices. Rocq: `Notation.BachmannNotation.BIdx`. -/
inductive BIdx : Type where
  | BIZ : BIdx
  | BIC : BIdx → BSmall → BIdx → BIdx
end

open BSmall BIdx

mutual
/-- Rocq: `Notation.BachmannNotation.BS_denote`. -/
def BS_denote : BSmall → Ordinal.{0}
  | BZ => 0
  | BN T y => bphi (fun x => 1 + x) (BI_denote T) (BS_denote y)

/-- Rocq: `Notation.BachmannNotation.BI_denote`. -/
def BI_denote : BIdx → BOrd.{0}
  | BIZ => bzero
  | BIC e c r => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r)
end

/-! ## Denotations are complete, canonical and directed -/

/-- Rocq: `Notation.BachmannNotation.idx_ok`. -/
def idx_ok (T : BOrd.{0}) : Prop := BCd T ∧ BSdirH T

/-- Rocq: `Notation.BachmannNotation.bcd_bzero`. -/
theorem bcd_bzero : BCd bzero.{0} := ⟨bcanon_bzero, bdec_bzero⟩

/-- Rocq: `Notation.BachmannNotation.idx_ok_bzero`. -/
theorem idx_ok_bzero : idx_ok bzero := ⟨bcd_bzero, bsdirH_bzero⟩

/-- Rocq: `Notation.BachmannNotation.idx_ok_term`. -/
theorem idx_ok_term (e : BOrd.{0}) (c : Ordinal.{0}) (He : idx_ok e) (Hc : Complete c) :
    idx_ok (bmul (bexpΩ e) (embed c)) :=
  ⟨bcd_bmul _ _ (bcd_bexpΩ _ He.1) (bpos_bexpΩ _) (bcd_embed c Hc),
    bsdirH_bmul _ _ (bcd_bexpΩ _ He.1) (bpos_bexpΩ _) (bsdirH_bexpΩ _ He.1 He.2) (bcd_embed c Hc) (bsdirH_embed c Hc)⟩

/-- Rocq: `Notation.BachmannNotation.idx_ok_badd`. -/
theorem idx_ok_badd (x y : BOrd.{0}) (Hx : idx_ok x) (Hy : idx_ok y) : idx_ok (badd x y) :=
  ⟨bcd_badd _ _ Hx.1 Hy.1, bsdirH_badd _ _ Hx.1 Hx.2 Hy.1 Hy.2⟩

mutual
/-- Rocq: `Notation.BachmannNotation.BS_complete`. -/
theorem BS_complete : ∀ x : BSmall, Complete (BS_denote x)
  | BZ => zero_complete
  | BN T y => (bcanon_normal _ onePlus_normal _ (BI_ok T).1).complete _ (BS_complete y)

/-- Rocq: `Notation.BachmannNotation.BI_ok`. -/
theorem BI_ok : ∀ T : BIdx, idx_ok (BI_denote T)
  | BIZ => idx_ok_bzero
  | BIC e c r => idx_ok_badd _ _ (idx_ok_term _ _ (BI_ok e) (BS_complete c)) (BI_ok r)
end

/-- Rocq: `Notation.BachmannNotation.BNotation_ok`. -/
theorem BNotation_ok : (∀ x, Complete (BS_denote x)) ∧ ∀ T, idx_ok (BI_denote T) := ⟨BS_complete, BI_ok⟩

/-- Rocq: `Notation.BachmannNotation.BI_bfam`. -/
theorem BI_bfam (T : BIdx) : BFam (BI_denote T) := bcanon_bfam _ (BI_ok T).1.1

/-- Rocq: `Notation.BachmannNotation.BI_good`. -/
theorem BI_good (T : BIdx) : BGood (fun x => 1 + x) (BI_denote T) :=
  (bcanon_good _ onePlus_normal _ (BI_ok T).1.1 (BI_ok T).1.2).2

/-- For each index, `ξ ↦ φ_T(ξ)` is a normal function. Rocq: `Notation.BachmannNotation.BI_normal`. -/
theorem BI_normal (T : BIdx) : NormalFunction (bphi (fun x => 1 + x) (BI_denote T)) :=
  bcanon_normal _ onePlus_normal _ (BI_ok T).1

/-- Bachmann's `φ`, one component at a time, agrees with the denotation.
Rocq: `Notation.BachmannNotation.BS_denote_bach`. -/
theorem BS_denote_bach (T : BIdx) (y : BSmall) :
    BS_denote (BN T y) ≈ bach (fun x => 1 + x) (BI_denote T) (BS_denote y) :=
  equiv_symm ((bach_bphi_canon _ onePlus_normal _ (BI_ok T).1 (BI_ok T).2).2.1 _ (BS_complete y))

/-! ## Basic calibrations -/

/-- Rocq: `Notation.BachmannNotation.BS_denote_onePlus`. -/
theorem BS_denote_onePlus (y : BSmall) : BS_denote (BN BIZ y) ≈ 1 + BS_denote y :=
  bphi_bzero _ onePlus_normal _

/-- Rocq: `Notation.BachmannNotation.BS_pos`. -/
theorem BS_pos (T : BIdx) (y : BSmall) : 0 < BS_denote (BN T y) := bphi_nonzero onePlus_normal _ _

/-- Rocq: `Notation.BachmannNotation.badd_inh_l`. -/
theorem badd_inh_l (x y : BOrd.{0}) (H : Nonempty (bsmall x ⊕ bbig x)) :
    Nonempty (bsmall (badd x y) ⊕ bbig (badd x y)) :=
  match H with
  | ⟨.inl a⟩ => let ⟨a', _⟩ := badd_small_l x y a; ⟨.inl a'⟩
  | ⟨.inr c⟩ => let ⟨c', _⟩ := badd_big_l x y c; ⟨.inr c'⟩

/-- A leading summand with positive coefficient gives the index a component.
Rocq: `Notation.BachmannNotation.BI_inh`. -/
theorem BI_inh (e : BIdx) (c : BSmall) (r : BIdx) (Hc : 0 < BS_denote c) :
    Nonempty (bsmall (BI_denote (BIC e c r)) ⊕ bbig (BI_denote (BIC e c r))) :=
  badd_inh_l _ _ (let ⟨t⟩ := bsmall_mul_embed_inh (BI_denote e) (BS_denote c) Hc; ⟨.inl t⟩)

/-- With a nonempty index of positive leading coefficient, `φ_T(y)` is
infinite, i.e., absorbs `1+`. Rocq: `Notation.BachmannNotation.BS_denote_absorb`. -/
theorem BS_denote_absorb (e : BIdx) (c : BSmall) (r : BIdx) (y : BSmall) (Hc : 0 < BS_denote c) :
    1 + BS_denote (BN (BIC e c r) y) ≈ BS_denote (BN (BIC e c r) y) :=
  bphi_onePlus_absorb (BI_denote (BIC e c r)) (BS_denote y) (BI_good _) (BI_inh e c r Hc) (BS_complete y)

/-! ## Indices below `Ω^Ω`

An exponent is small when it is 0 or `Ω^0·s`; the index then lies below
`Ω^Ω` and corresponds to a list of (exponent, coefficient) pairs of
ordinals. -/

/-- Rocq: `Notation.BachmannNotation.exp_small`. -/
def exp_small : BIdx → Option BSmall
  | BIZ => some BZ
  | BIC BIZ s BIZ => some s
  | BIC BIZ _ (BIC _ _ _) => none
  | BIC (BIC _ _ _) _ _ => none

/-- Rocq: `Notation.BachmannNotation.exp_s`. -/
def exp_s (e : BIdx) : BSmall :=
  match exp_small e with
  | some s => s
  | none => BZ

/-- The exponent `Ω^0·s`. Rocq: `Notation.BachmannNotation.idx_small`. -/
def idx_small (s : BSmall) : BIdx := BIC BIZ s BIZ

/-- Rocq: `Notation.BachmannNotation.bequiv_bzero_embed0`. -/
theorem bequiv_bzero_embed0 : BEquiv bzero (embed (0 : Ordinal.{0})) :=
  ⟨⟨fun e => (nomatch e), fun e => (nomatch e)⟩, ⟨fun e => (nomatch e), fun e => (nomatch e)⟩⟩

/-- Rocq: `Notation.BachmannNotation.exp_equiv`. -/
theorem exp_equiv (e : BIdx) (s : BSmall) (H : exp_small e = some s) : BEquiv (BI_denote e) (embed (BS_denote s)) := by
  match e, H with
  | BIZ, H =>
    cases H
    exact bequiv_bzero_embed0
  | BIC BIZ s0 BIZ, H =>
    cases H
    exact bequiv_trans (bequiv_badd_zero_r _) (bequiv_one_mul _)
  | BIC BIZ _ (BIC _ _ _), H => exact nomatch H
  | BIC (BIC _ _ _) _ _, H => exact nomatch H

/-- Rocq: `Notation.BachmannNotation.olist`. -/
def olist : BIdx → List (Ordinal.{0} × Ordinal.{0})
  | BIZ => []
  | BIC e c r => (BS_denote (exp_s e), BS_denote c) :: olist r

/-- Rocq: `Notation.BachmannNotation.idx_shape`. -/
def idx_shape : BIdx → Prop
  | BIZ => True
  | BIC e _ r => exp_small e ≠ none ∧ idx_shape r

/-- Rocq: `Notation.BachmannNotation.BI_osum`. -/
theorem BI_osum : ∀ T : BIdx, idx_shape T → BEquiv (BI_denote T) (osum (olist T))
  | BIZ, _ => bequiv_refl _
  | BIC e c r, ⟨He, Hr⟩ => by
    refine bequiv_badd _ _ _ _ (bequiv_bmul _ _ _ _ (bequiv_bexpΩ _ _ ?_) (bequiv_refl _)) (BI_osum r Hr)
    match h : exp_small e with
    | some s =>
      have hs : exp_s e = s := by unfold exp_s; rw [h]
      rw [hs]
      exact exp_equiv e s h
    | none => exact absurd h He

/-- Rocq: `Notation.BachmannNotation.ord_eq_normal`. -/
theorem ord_eq_normal (G : Ordinal.{0} → Ordinal.{0}) (HG : NormalFunction G) (x y : Ordinal.{0}) (H : x ≈ y) :
    G x ≈ G y :=
  equiv_intro (HG.monotone _ _ H.le) (HG.monotone _ _ H.ge)

/-! # Normal forms and comparison

`φ_T(y)` is normal when `T` is a normal Ω-Cantor normal form (exponents
strictly decreasing in the index order, coefficients positive), the argument
is not a fixpoint (`y < φ_T(y)`), and every coefficient occurring in `T`, at
any depth, lies below `φ_T(y)`. Comparison is Bachmann's rule: for `T < T'`,
`φ_T(a) < φ_{T'}(b)` iff `a` and every coefficient of `T` lie below
`φ_{T'}(b)`, because then `φ_{T'}(b)` is a fixpoint of `φ_T` (the nesting
theorem `nest`). -/

/-! ## The order on indices -/

/-- Rocq: `Notation.BachmannNotation.ieq`. -/
inductive ieq : BIdx → BIdx → Prop
  /-- Rocq: `Notation.BachmannNotation.ieq_nil`. -/
  | nil : ieq BIZ BIZ
  /-- Rocq: `Notation.BachmannNotation.ieq_cons`. -/
  | cons (e : BIdx) (c : BSmall) (r e' : BIdx) (c' : BSmall) (r' : BIdx) :
      ieq e e' → BS_denote c ≈ BS_denote c' → ieq r r' → ieq (BIC e c r) (BIC e' c' r')

/-- Rocq: `Notation.BachmannNotation.ilt`. -/
inductive ilt : BIdx → BIdx → Prop
  /-- Rocq: `Notation.BachmannNotation.ilt_nil`. -/
  | nil (e : BIdx) (c : BSmall) (r : BIdx) : ilt BIZ (BIC e c r)
  /-- Rocq: `Notation.BachmannNotation.ilt_exp`. -/
  | exp (e : BIdx) (c : BSmall) (r e' : BIdx) (c' : BSmall) (r' : BIdx) : ilt e e' → ilt (BIC e c r) (BIC e' c' r')
  /-- Rocq: `Notation.BachmannNotation.ilt_coef`. -/
  | coef (e : BIdx) (c : BSmall) (r e' : BIdx) (c' : BSmall) (r' : BIdx) :
      ieq e e' → BS_denote c < BS_denote c' → ilt (BIC e c r) (BIC e' c' r')
  /-- Rocq: `Notation.BachmannNotation.ilt_tail`. -/
  | tail (e : BIdx) (c : BSmall) (r e' : BIdx) (c' : BSmall) (r' : BIdx) :
      ieq e e' → BS_denote c ≈ BS_denote c' → ilt r r' → ilt (BIC e c r) (BIC e' c' r')

/-- Rocq: `Notation.BachmannNotation.ieq_sym`. -/
theorem ieq_sym {T T' : BIdx} (H : ieq T T') : ieq T' T := by
  induction H with
  | nil => exact .nil
  | cons e c r e' c' r' _ hc _ ihe ihr => exact .cons _ _ _ _ _ _ ihe (equiv_symm hc) ihr

/-- Rocq: `Notation.BachmannNotation.ieq_bequiv`. -/
theorem ieq_bequiv {T T' : BIdx} (H : ieq T T') : BEquiv (BI_denote T) (BI_denote T') := by
  induction H with
  | nil => exact bequiv_refl _
  | cons e c r e' c' r' _ hc _ ihe ihr =>
    exact bequiv_badd _ _ _ _ (bequiv_bmul _ _ _ _ (bequiv_bexpΩ _ _ ihe) (bequiv_embed _ _ hc)) ihr

/-- Every coefficient, at any depth, lies below `z`. Rocq: `Notation.BachmannNotation.Klt`. -/
def Klt (z : Ordinal.{0}) : BIdx → Prop
  | BIZ => True
  | BIC e c r => Klt z e ∧ BS_denote c < z ∧ Klt z r

/-- Some coefficient, at some depth, is at least `z`. Rocq: `Notation.BachmannNotation.Kge`. -/
def Kge (z : Ordinal.{0}) : BIdx → Prop
  | BIZ => False
  | BIC e c r => Kge z e ∨ z ≤ BS_denote c ∨ Kge z r

/-- Rocq: `Notation.BachmannNotation.Kge_lt`. -/
theorem Kge_lt (z w : Ordinal.{0}) : ∀ T : BIdx, Kge z T → Klt w T → z < w
  | BIZ, h, _ => h.elim
  | BIC e _ r, h, ⟨h1, h2, h3⟩ =>
    match h with
    | .inl h => Kge_lt z w e h h1
    | .inr (.inl h) => lt_of_le_of_lt h h2
    | .inr (.inr h) => Kge_lt z w r h h3

/-- Rocq: `Notation.BachmannNotation.lead_below`. -/
def lead_below (r e : BIdx) : Prop :=
  match r with
  | BIZ => True
  | BIC e2 _ _ => ilt e2 e

mutual
/-- Rocq: `Notation.BachmannNotation.BS_nf`. -/
def BS_nf : BSmall → Prop
  | BZ => True
  | BN T y => BI_nf T ∧ BS_nf y ∧ BS_denote y < BS_denote (BN T y) ∧ Klt (BS_denote (BN T y)) T

/-- Rocq: `Notation.BachmannNotation.BI_nf`. -/
def BI_nf : BIdx → Prop
  | BIZ => True
  | BIC e c r => BI_nf e ∧ BS_nf c ∧ 0 < BS_denote c ∧ BI_nf r ∧ lead_below r e
end

/-! ## Sizes -/

mutual
/-- Rocq: `Notation.BachmannNotation.BS_size`. -/
def BS_size : BSmall → Nat
  | BZ => 1
  | BN T y => BI_size T + BS_size y + 1

/-- Rocq: `Notation.BachmannNotation.BI_size`. -/
def BI_size : BIdx → Nat
  | BIZ => 1
  | BIC e c r => BI_size e + BS_size c + BI_size r + 1
end

theorem size_N_T (T : BIdx) (y : BSmall) : BI_size T < BS_size (BN T y) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)

theorem size_N_y (T : BIdx) (y : BSmall) : BS_size y < BS_size (BN T y) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

theorem size_C_e (e : BIdx) (c : BSmall) (r : BIdx) : BI_size e < BI_size (BIC e c r) :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem size_C_c (e : BIdx) (c : BSmall) (r : BIdx) : BS_size c < BI_size (BIC e c r) :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))

theorem size_C_r (e : BIdx) (c : BSmall) (r : BIdx) : BI_size r < BI_size (BIC e c r) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

/-- Fuel arithmetic: if `a + b < n + 1`, `a' < a` and `b' ≤ b` then `a' + b' < n`. -/
theorem size_add_lt {a b a' b' n : Nat} (h : a + b < n + 1) (ha : a' < a) (hb : b' ≤ b) : a' + b' < n :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le ha hb) (Nat.le_of_lt_succ h)

theorem size_lt_pred {a b n : Nat} (h : b < n + 1) (ha : a < b) : a < n :=
  Nat.lt_of_lt_of_le ha (Nat.le_of_lt_succ h)

/-! ## The nesting theorem

A smaller normal index, whose coefficients all lie below an infinite `z`, is
z-reachably below a larger one; and an index whose leading exponent is
z-reachably below `a` lies z-reachably below `Ω^a`. -/

/-- Rocq: `Notation.BachmannNotation.term_pos`. -/
theorem term_pos (e : BIdx) (c : BSmall) (Hc : 0 < BS_denote c) :
    bpos (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) :=
  bslt_bsub_r _ _ _ (bpos_bexpΩ _) (bsub_P_Pz _ _ Hc)

/-- Rocq: `Notation.BachmannNotation.lead_pos`. -/
theorem lead_pos (e : BIdx) (c : BSmall) (r : BIdx) (Hc : 0 < BS_denote c) : bpos (BI_denote (BIC e c r)) :=
  bslt_bsub_r _ _ _ (term_pos e c Hc) (bsub_le_badd _ _)

/-- The second clause of `nest`: the match in its Rocq statement. -/
def leadZlt (z : Ordinal.{0}) (T : BIdx) (a : BOrd.{0}) : Prop :=
  match T with
  | BIZ => True
  | BIC e _ _ => zlt z (BI_denote e) a

/-- Rocq: `Notation.BachmannNotation.nest`. -/
theorem nest (z : Ordinal.{0}) (Hz : OInf z) : ∀ (n : Nat) (T : BIdx), BI_size T < n → BI_nf T → Klt z T →
    (∀ T', BI_nf T' → ilt T T' → zlt z (BI_denote T) (BI_denote T')) ∧
      (∀ a, leadZlt z T a → zlt z (BI_denote T) (bexpΩ a)) := by
  intro n
  induction n with
  | zero => exact fun _ h => absurd h (Nat.not_lt_zero _)
  | succ n IH =>
  intro T hsz HT HK
  -- the tail of a normal index lies below Ω^(its leading exponent)
  have Hrb : ∀ e c r, BI_size (BIC e c r) < n + 1 → BI_nf (BIC e c r) → Klt z (BIC e c r) →
      zlt z (BI_denote r) (bexpΩ (BI_denote e)) := by
    intro e c r hsz' HT' HK'
    obtain ⟨He, _, _, Hr, Hlead⟩ := HT'
    obtain ⟨_, _, HKr⟩ := HK'
    refine (IH r (size_lt_pred hsz' (size_C_r e c r)) Hr HKr).2 _ ?_
    match r, Hr, HKr, Hlead with
    | BIZ, _, _, _ => trivial
    | BIC e2 c2 r2, Hr, HKr, Hlead =>
      exact (IH e2 (size_lt_pred hsz' (Nat.lt_trans (size_C_e e2 c2 r2) (size_C_r e c (BIC e2 c2 r2)))) Hr.1 HKr.1).1
        e He Hlead
  have B : ∀ a, leadZlt z T a → zlt z (BI_denote T) (bexpΩ a) := by
    intro a Ha
    match T, hsz, HT, HK, Ha with
    | BIZ, _, _, _, _ => exact zlt_bslt _ _ _ (bpos_bexpΩ _)
    | BIC e c r, hsz, HT, HK, Ha =>
      refine zlt_bleZ z _ (bmul (bexpΩ (BI_denote e)) (embed z)) _ ?_ (zlt_exp z _ _ Ha Hz)
      exact zlt_mono_r _ _ _ _ (zlt_shift z _ _ _ (Hrb e c r hsz HT HK))
        (bsub_trans (bsub_mul_succ _ _) (bsub_bmul_r _ _ _ (bsub_embed _ _ (succ_least HK.2.1))))
  refine ⟨fun T' HT' Hlt => ?_, B⟩
  cases Hlt with
  | nil e' c' r' => exact zlt_bslt _ _ _ (lead_pos e' c' r' HT'.2.2.1)
  | exp e c r e' c' r' hee =>
    exact zlt_mono_r _ _ _ _ (B (BI_denote e') ((IH e (size_lt_pred hsz (size_C_e e c r)) HT.1 HK.1).1 e' HT'.1 hee))
      (bsub_trans (bsub_P_Pz _ _ HT'.2.2.1) (bsub_le_badd _ _))
  | coef e c r e' c' r' hee hcc =>
    refine zlt_mono_r _ _ _ _ (zlt_shift z _ _ _ (Hrb e c r hsz HT HK)) ?_
    exact bsub_trans (bsub_mul_succ _ _) (bsub_trans (bsub_trans (bsub_bmul_r _ _ _ (bsub_embed _ _ (succ_least hcc)))
      (bsub_bmul_l _ _ (bsub_bexpΩ _ _ (ieq_bequiv hee).1) _)) (bsub_le_badd _ _))
  | tail e c r e' c' r' hee hcc hrr =>
    refine zlt_mono_r _ _ _ _ (zlt_shift z _ _ _
      ((IH r (size_lt_pred hsz (size_C_r e c r)) HT.2.2.2.1 HK.2.2).1 r' HT'.2.2.2.1 hrr)) ?_
    exact bsub_badd_l _ _ (bsub_trans (bsub_bmul_r _ _ _ (bsub_embed _ _ hcc.le))
      (bsub_bmul_l _ _ (bsub_bexpΩ _ _ (ieq_bequiv hee).1) _)) _

/-! ## Semantic cases of the comparison -/

/-- Rocq: `Notation.BachmannNotation.BN_inf`. -/
theorem BN_inf (T : BIdx) (y : BSmall) (HT : BI_nf T) (Hne : T ≠ BIZ) : OInf (BS_denote (BN T y)) := by
  match T, HT, Hne with
  | BIZ, _, Hne => exact absurd rfl Hne
  | BIC e c r, HT, _ =>
    exact bphi_value_inf (fun x => 1 + x) onePlus_normal (BI_denote (BIC e c r)) (BS_denote y)
      (fun x => le_add_left 1 x) (fun _ _ => le_refl _) (BI_good _) (BI_inh e c r HT.2.2.1) (BS_complete y)

/-- Bachmann's rule for distinct indices. Rocq: `Notation.BachmannNotation.nest_lt`. -/
theorem nest_lt (T : BIdx) (a : BSmall) (T' : BIdx) (b : BSmall) (Hx : BS_nf (BN T a)) (Hy : BS_nf (BN T' b))
    (Hlt : ilt T T') (Ha : BS_denote a < BS_denote (BN T' b)) (Hc : Klt (BS_denote (BN T' b)) T) :
    BS_denote (BN T a) < BS_denote (BN T' b) := by
  have HT := Hx.1
  have HT' := Hy.1
  have Hne : T' ≠ BIZ := by intro E; subst E; cases Hlt
  have Hz := (nest _ (BN_inf T' b HT' Hne) (BI_size T + 1) T (Nat.lt_succ_self _) HT Hc).1 T' HT' Hlt
  have Hi : Nonempty (bsmall (BI_denote T') ⊕ bbig (BI_denote T')) := by
    match T', HT', Hne with
    | BIZ, _, Hne => exact absurd rfl Hne
    | BIC e' c' r', HT', _ => exact BI_inh e' c' r' HT'.2.2.1
  have Hfix := zlt_value (fun x => 1 + x) onePlus_normal (BI_denote T) (BI_denote T') (BS_denote b) Hz (BI_good T')
    (BI_bfam T') Hi (BS_complete b)
  exact lt_of_lt_of_le ((BI_normal T).increasing _ _ (BS_complete (BN T' b)) Ha) Hfix

/-- Rocq: `Notation.BachmannNotation.bphi_ieq`. -/
theorem bphi_ieq (T T' : BIdx) (y : Ordinal.{0}) (H : ieq T T') :
    bphi (fun x => 1 + x) (BI_denote T) y ≈ bphi (fun x => 1 + x) (BI_denote T') y :=
  bphi_bequiv _ onePlus_normal.monotone _ _ y (ieq_bequiv H) (BI_bfam T) (BI_bfam T')

/-! ## The comparison algorithm -/

/-- Rocq: `Notation.BachmannNotation.isLT`. -/
def isLT : Ordering → Bool
  | .lt => true
  | .eq => false
  | .gt => false

/-- Whether every coefficient of `T` lies below `z`, by a given comparison. -/
def coefsBelowWith (cmp : BSmall → BSmall → Ordering) : BIdx → BSmall → Bool
  | BIZ, _ => true
  | BIC e c r, z => coefsBelowWith cmp e z && isLT (cmp c z) && coefsBelowWith cmp r z

mutual
/-- Rocq: `Notation.BachmannNotation.cmpS`. -/
def cmpS : Nat → BSmall → BSmall → Ordering
  | 0, _, _ => .eq
  | _ + 1, BZ, BZ => .eq
  | _ + 1, BZ, BN _ _ => .lt
  | _ + 1, BN _ _, BZ => .gt
  | n + 1, BN T a, BN T' b =>
    match cmpI n T T' with
    | .eq => cmpS n a b
    | .lt =>
      match isLT (cmpS n a (BN T' b)) && coefsBelowWith (cmpS n) T (BN T' b) with
      | true => .lt
      | false => .gt
    | .gt =>
      match isLT (cmpS n b (BN T a)) && coefsBelowWith (cmpS n) T' (BN T a) with
      | true => .gt
      | false => .lt

/-- Rocq: `Notation.BachmannNotation.cmpI`. -/
def cmpI : Nat → BIdx → BIdx → Ordering
  | 0, _, _ => .eq
  | _ + 1, BIZ, BIZ => .eq
  | _ + 1, BIZ, BIC _ _ _ => .lt
  | _ + 1, BIC _ _ _, BIZ => .gt
  | n + 1, BIC e c r, BIC e' c' r' =>
    match cmpI n e e' with
    | .lt => .lt
    | .gt => .gt
    | .eq =>
      match cmpS n c c' with
      | .lt => .lt
      | .gt => .gt
      | .eq => cmpI n r r'
end

/-- Rocq: `Notation.BachmannNotation.coefs_below`. -/
def coefs_below (n : Nat) : BIdx → BSmall → Bool := coefsBelowWith (cmpS n)

/-- Rocq: `Notation.BachmannNotation.cmpS_BN`. -/
theorem cmpS_BN (n : Nat) (T : BIdx) (a : BSmall) (T' : BIdx) (b : BSmall) :
    cmpS (n + 1) (BN T a) (BN T' b) =
      match cmpI n T T' with
      | .eq => cmpS n a b
      | .lt =>
        match isLT (cmpS n a (BN T' b)) && coefs_below n T (BN T' b) with
        | true => .lt
        | false => .gt
      | .gt =>
        match isLT (cmpS n b (BN T a)) && coefs_below n T' (BN T a) with
        | true => .gt
        | false => .lt := rfl

/-- Rocq: `Notation.BachmannNotation.cmpI_ok`. -/
def cmpI_ok : Ordering → BIdx → BIdx → Prop
  | .lt, T, T' => ilt T T'
  | .eq, T, T' => ieq T T'
  | .gt, T, T' => ilt T' T

/-- Rocq: `Notation.BachmannNotation.isLT_spec`. -/
theorem isLT_spec (o : Ordering) (a b : Ordinal.{0}) (H : OrderingCorrect o a b) :
    (isLT o = true → a < b) ∧ (isLT o = false → b ≤ a) := by
  cases o with
  | lt => exact ⟨fun _ => H, fun h => nomatch h⟩
  | eq => exact ⟨fun h => (nomatch h), fun _ => H.ge⟩
  | gt => exact ⟨fun h => (nomatch h), fun _ => le_of_lt H⟩

/-- Rocq: `Notation.BachmannNotation.coefs_below_spec`. -/
theorem coefs_below_spec (n : Nat) (y : BSmall) : ∀ T : BIdx,
    (∀ c, BS_size c ≤ BI_size T → BS_nf c → OrderingCorrect (cmpS n c y) (BS_denote c) (BS_denote y)) →
    BI_nf T → (coefs_below n T y = true → Klt (BS_denote y) T) ∧ (coefs_below n T y = false → Kge (BS_denote y) T)
  | BIZ, _, _ => ⟨fun _ => trivial, fun h => nomatch h⟩
  | BIC e c r, Hc, ⟨He, Hcn, _, Hr, _⟩ => by
    obtain ⟨E1, E2⟩ := coefs_below_spec n y e (fun c0 h => Hc c0 (Nat.le_trans h (Nat.le_of_lt (size_C_e e c r)))) He
    obtain ⟨R1, R2⟩ := coefs_below_spec n y r (fun c0 h => Hc c0 (Nat.le_trans h (Nat.le_of_lt (size_C_r e c r)))) Hr
    obtain ⟨S1, S2⟩ := isLT_spec _ _ _ (Hc c (Nat.le_of_lt (size_C_c e c r)) Hcn)
    show ((coefs_below n e y && isLT (cmpS n c y) && coefs_below n r y) = true → _) ∧
      ((coefs_below n e y && isLT (cmpS n c y) && coefs_below n r y) = false → _)
    revert E1 E2 R1 R2 S1 S2
    cases coefs_below n e y <;> cases isLT (cmpS n c y) <;> cases coefs_below n r y <;>
      intro E1 E2 R1 R2 S1 S2 <;>
      first
        | exact ⟨fun h => (nomatch h), fun _ => .inl (E2 rfl)⟩
        | exact ⟨fun h => (nomatch h), fun _ => .inr (.inl (S2 rfl))⟩
        | exact ⟨fun h => (nomatch h), fun _ => .inr (.inr (R2 rfl))⟩
        | exact ⟨fun _ => ⟨E1 rfl, S1 rfl, R1 rfl⟩, fun h => nomatch h⟩

/-- Rocq: `Notation.BachmannNotation.cmp_correct`. -/
theorem cmp_correct (n : Nat) :
    (∀ x y, BS_size x + BS_size y < n → BS_nf x → BS_nf y → OrderingCorrect (cmpS n x y) (BS_denote x) (BS_denote y)) ∧
      ∀ T T', BI_size T + BI_size T' < n → BI_nf T → BI_nf T' → cmpI_ok (cmpI n T T') T T' := by
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
  obtain ⟨IHS, IHI⟩ := ih
  refine ⟨fun x y hsz hx hy => ?_, fun T T' hsz hT hT' => ?_⟩
  · match x, y, hsz, hx, hy with
    | BZ, BZ, _, _, _ => exact equiv_refl _
    | BZ, BN T' b, _, _, _ => exact BS_pos T' b
    | BN T a, BZ, _, _, _ => exact BS_pos T a
    | BN T a, BN T' b, hsz, hx, hy =>
      rw [cmpS_BN]
      have hx' := hx
      have hy' := hy
      obtain ⟨HT, Ha, Hax, Hcx⟩ := hx'
      obtain ⟨HT', Hb, _, Hcy⟩ := hy'
      have HI := IHI T T' (size_add_lt hsz (size_N_T T a) (Nat.le_of_lt (size_N_T T' b))) HT HT'
      revert HI
      cases cmpI n T T' with
      | lt =>
        intro HI
        obtain ⟨A1, A2⟩ := isLT_spec _ _ _ (IHS a (BN T' b) (size_add_lt hsz (size_N_y T a) (Nat.le_refl _)) Ha hy)
        obtain ⟨C1, C2⟩ := coefs_below_spec n (BN T' b) T
          (fun c hc hcn => IHS c (BN T' b) (size_add_lt hsz (Nat.lt_of_le_of_lt hc (size_N_T T a)) (Nat.le_refl _)) hcn hy)
          HT
        revert A1 A2 C1 C2
        cases isLT (cmpS n a (BN T' b)) <;> cases coefs_below n T (BN T' b) <;> intro A1 A2 C1 C2
        · exact lt_of_le_of_lt (A2 rfl) Hax
        · exact lt_of_le_of_lt (A2 rfl) Hax
        · exact Kge_lt _ _ T (C2 rfl) Hcx
        · exact nest_lt T a T' b hx hy HI (A1 rfl) (C1 rfl)
      | eq =>
        intro HI
        have Heq := bphi_ieq T T' (BS_denote b) HI
        have Hab := IHS a b (size_add_lt hsz (size_N_y T a) (Nat.le_of_lt (size_N_y T' b))) Ha Hb
        show OrderingCorrect (cmpS n a b) (bphi (fun x => 1 + x) (BI_denote T) (BS_denote a))
          (bphi (fun x => 1 + x) (BI_denote T') (BS_denote b))
        revert Hab
        cases cmpS n a b with
        | lt => intro Hab; exact lt_of_lt_of_le ((BI_normal T).increasing _ _ (BS_complete b) Hab) Heq.le
        | eq => intro Hab; exact equiv_trans (ord_eq_normal _ (BI_normal T) _ _ Hab) Heq
        | gt => intro Hab; exact lt_of_le_of_lt Heq.ge ((BI_normal T).increasing _ _ (BS_complete a) Hab)
      | gt =>
        intro HI
        obtain ⟨A1, A2⟩ := isLT_spec _ _ _ (IHS b (BN T a)
          (by rw [Nat.add_comm] at hsz; exact size_add_lt hsz (size_N_y T' b) (Nat.le_refl _)) Hb hx)
        obtain ⟨C1, C2⟩ := coefs_below_spec n (BN T a) T'
          (fun c hc hcn => IHS c (BN T a)
            (by rw [Nat.add_comm] at hsz; exact size_add_lt hsz (Nat.lt_of_le_of_lt hc (size_N_T T' b)) (Nat.le_refl _))
            hcn hx) HT'
        revert A1 A2 C1 C2
        cases isLT (cmpS n b (BN T a)) <;> cases coefs_below n T' (BN T a) <;> intro A1 A2 C1 C2
        · exact lt_of_le_of_lt (A2 rfl) hy.2.2.1
        · exact lt_of_le_of_lt (A2 rfl) hy.2.2.1
        · exact Kge_lt _ _ T' (C2 rfl) Hcy
        · exact nest_lt T' b T a hy hx HI (A1 rfl) (C1 rfl)
  · match T, T', hsz, hT, hT' with
    | BIZ, BIZ, _, _, _ => exact .nil
    | BIZ, BIC _ _ _, _, _, _ => exact .nil _ _ _
    | BIC _ _ _, BIZ, _, _, _ => exact .nil _ _ _
    | BIC e c r, BIC e' c' r', hsz, ⟨He, Hc, _, Hr, _⟩, ⟨He', Hc', _, Hr', _⟩ =>
      show cmpI_ok (match cmpI n e e' with
        | .lt => .lt
        | .gt => .gt
        | .eq =>
          match cmpS n c c' with
          | .lt => .lt
          | .gt => .gt
          | .eq => cmpI n r r') _ _
      have HE := IHI e e' (size_add_lt hsz (size_C_e e c r) (Nat.le_of_lt (size_C_e e' c' r'))) He He'
      revert HE
      cases cmpI n e e' with
      | lt => intro HE; exact .exp _ _ _ _ _ _ HE
      | gt => intro HE; exact .exp _ _ _ _ _ _ HE
      | eq =>
        intro HE
        have HC := IHS c c' (size_add_lt hsz (size_C_c e c r) (Nat.le_of_lt (size_C_c e' c' r'))) Hc Hc'
        revert HC
        cases cmpS n c c' with
        | lt => intro HC; exact .coef _ _ _ _ _ _ HE HC
        | gt => intro HC; exact .coef _ _ _ _ _ _ (ieq_sym HE) HC
        | eq =>
          intro HC
          have HR := IHI r r' (size_add_lt hsz (size_C_r e c r) (Nat.le_of_lt (size_C_r e' c' r'))) Hr Hr'
          revert HR
          cases cmpI n r r' with
          | lt => intro HR; exact .tail _ _ _ _ _ _ HE HC HR
          | eq => intro HR; exact .cons _ _ _ _ _ _ HE HC HR
          | gt => intro HR; exact .tail _ _ _ _ _ _ (ieq_sym HE) (equiv_symm HC) HR

/-- Rocq: `Notation.BachmannNotation.BS_compare`. -/
def BS_compare (x y : BSmall) : Ordering := cmpS (BS_size x + BS_size y + 1) x y

/-- Rocq: `Notation.BachmannNotation.BS_compare_correct`. -/
theorem BS_compare_correct (x y : BSmall) (Hx : BS_nf x) (Hy : BS_nf y) :
    OrderingCorrect (BS_compare x y) (BS_denote x) (BS_denote y) :=
  (cmp_correct _).1 x y (Nat.lt_succ_self _) Hx Hy

/-- Rocq: `Notation.BachmannNotation.BS_decide_order`. -/
def BS_decide_order (x y : BSmall) (Hx : BS_nf x) (Hy : BS_nf y) :
    PSum (BS_denote x < BS_denote y) (BS_denote y ≤ BS_denote x) :=
  match BS_compare x y, BS_compare_correct x y Hx Hy with
  | .lt, h => .inl h
  | .eq, h => .inr h.ge
  | .gt, h => .inr (le_of_lt h)

/-! ## Uniqueness of normal forms -/

/-- Rocq: `Notation.BachmannNotation.cmp_eq`. -/
theorem cmp_eq (n : Nat) :
    (∀ x y, BS_size x + BS_size y < n → BS_nf x → BS_nf y → cmpS n x y = .eq → x = y) ∧
      ∀ T T', BI_size T + BI_size T' < n → BI_nf T → BI_nf T' → cmpI n T T' = .eq → T = T' := by
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
  obtain ⟨IHS, IHI⟩ := ih
  refine ⟨fun x y hsz hx hy => ?_, fun T T' hsz hT hT' => ?_⟩
  · match x, y, hsz, hx, hy with
    | BZ, BZ, _, _, _ => exact fun _ => rfl
    | BZ, BN _ _, _, _, _ => exact fun h => nomatch h
    | BN _ _, BZ, _, _, _ => exact fun h => nomatch h
    | BN T a, BN T' b, hsz, ⟨HT, Ha, _⟩, ⟨HT', Hb, _⟩ =>
      rw [cmpS_BN]
      cases hI : cmpI n T T' with
      | lt =>
        cases isLT (cmpS n a (BN T' b)) && coefs_below n T (BN T' b) <;> exact fun h => nomatch h
      | gt =>
        cases isLT (cmpS n b (BN T a)) && coefs_below n T' (BN T a) <;> exact fun h => nomatch h
      | eq =>
        intro h
        rw [IHI T T' (size_add_lt hsz (size_N_T T a) (Nat.le_of_lt (size_N_T T' b))) HT HT' hI,
          IHS a b (size_add_lt hsz (size_N_y T a) (Nat.le_of_lt (size_N_y T' b))) Ha Hb h]
  · match T, T', hsz, hT, hT' with
    | BIZ, BIZ, _, _, _ => exact fun _ => rfl
    | BIZ, BIC _ _ _, _, _, _ => exact fun h => nomatch h
    | BIC _ _ _, BIZ, _, _, _ => exact fun h => nomatch h
    | BIC e c r, BIC e' c' r', hsz, ⟨He, Hc, _, Hr, _⟩, ⟨He', Hc', _, Hr', _⟩ =>
      show (match cmpI n e e' with
        | .lt => .lt
        | .gt => .gt
        | .eq =>
          match cmpS n c c' with
          | .lt => .lt
          | .gt => .gt
          | .eq => cmpI n r r') = Ordering.eq → _
      cases h1 : cmpI n e e' with
      | lt => exact fun h => nomatch h
      | gt => exact fun h => nomatch h
      | eq =>
        cases h2 : cmpS n c c' with
        | lt => exact fun h => nomatch h
        | gt => exact fun h => nomatch h
        | eq =>
          intro h3
          rw [IHI e e' (size_add_lt hsz (size_C_e e c r) (Nat.le_of_lt (size_C_e e' c' r'))) He He' h1,
            IHS c c' (size_add_lt hsz (size_C_c e c r) (Nat.le_of_lt (size_C_c e' c' r'))) Hc Hc' h2,
            IHI r r' (size_add_lt hsz (size_C_r e c r) (Nat.le_of_lt (size_C_r e' c' r'))) Hr Hr' h3]

/-- Rocq: `Notation.BachmannNotation.BS_nf_unique`. -/
theorem BS_nf_unique (x y : BSmall) (Hx : BS_nf x) (Hy : BS_nf y) (Heq : BS_denote x ≈ BS_denote y) : x = y :=
  match h : BS_compare x y, BS_compare_correct x y Hx Hy with
  | .lt, H => absurd (lt_of_lt_of_le H Heq.ge) (lt_irrefl _)
  | .eq, _ => (cmp_eq _).1 x y (Nat.lt_succ_self _) Hx Hy h
  | .gt, H => absurd (lt_of_lt_of_le H Heq.le) (lt_irrefl _)

/-! ## Examples, by computation -/

/-- `1`. Rocq: `Notation.BachmannNotation.BS_one`. -/
def BS_one : BSmall := BN BIZ BZ

/-- The index 1. Rocq: `Notation.BachmannNotation.BI_one`. -/
def BI_one : BIdx := BIC BIZ BS_one BIZ

/-- The index `Ω`. Rocq: `Notation.BachmannNotation.BI_Ω`. -/
def BI_Ω : BIdx := BIC BI_one BS_one BIZ

/-- The index `Ω^Ω`. Rocq: `Notation.BachmannNotation.BI_ΩΩ`. -/
def BI_ΩΩ : BIdx := BIC BI_Ω BS_one BIZ

/-- `Γ₀ = φ_Ω(0)` lies below the Large Veblen Ordinal `φ_{Ω^Ω}(0)`. -/
example : BS_compare (BN BI_Ω BZ) (BN BI_ΩΩ BZ) = .lt := rfl

/-- `Γ₁ = φ_Ω(1)` lies above `Γ₀`, and `φ_1(0) = ω` below it. -/
example : BS_compare (BN BI_Ω BS_one) (BN BI_Ω BZ) = .gt := rfl

example : BS_compare (BN BI_one BZ) (BN BI_Ω BZ) = .lt := rfl

end BachmannNotation

end ConstructiveOrdinals
