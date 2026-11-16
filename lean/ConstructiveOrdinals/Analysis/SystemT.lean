import ConstructiveOrdinals.Notation.V
import ConstructiveOrdinals.Prelude.Index

/-!
# An ordinal analysis of Gödel's System T below ε₀

Port of `Ordinal/Analysis/SystemT.v`.

Following Tait ("Infinitely long terms of transfinite type", 1965), the
recursor of System T is replaced by an ω-branching term: `rec C z s t`
becomes `Ω_C(f) t`, where `Ω_C(f) : nat → C` has one branch
`f n = s (n-1) (... (s 0 z))` per numeral. The resulting infinitary
simply-typed terms are normalized by cut elimination, one type level at a
time.

Derivations carry a height and a cut rank. The heights are V forms, so every
ordinal in this file is a notation, and lies below ε₀. The analysis:

- the translation of a term `t` has height `h t` and cut rank `tlev t`
  (`tr_typed`); `h t` is below `ω^ω` (`h_below_ω_ω`);
- one pass of cut elimination (`elim`) lowers the cut rank by one, sending
  height `α` to `ω^α` (`elim_typed`);
- hence the normal form of `t` has height at most the tower `ω^ω^...^(h t)` of
  height `tlev t` (`T_normalization`), the ordinal `ord_of t`, below the tower
  `ω_{tlev t + 2}` (`ord_of_bound`);
- a closed normal term of type `nat` is a numeral, so every closed term of
  type `nat` reduces to a numeral (`T_total`).

Lean notes:

- Matches that Rocq writes with wildcards spell out every constructor, since
  a wildcard would make the definitions depend on `propext`.
- Index arithmetic goes through `Prelude/Index`, and boolean reasoning about
  `cut_ok` is by case analysis on the booleans.
-/

namespace ConstructiveOrdinals.SystemT

open Ordinal VNotation VForm Index

/-! ## Types and levels -/

/-- Rocq: `Analysis.SystemT.ty`. -/
inductive Ty : Type where
  | TN : Ty
  | TAr : Ty → Ty → Ty

open Ty

/-- Levels start at 1: an ω-redex has level 1, and substituting at any type
may create one. Rocq: `Analysis.SystemT.lev`. -/
def lev : Ty → Nat
  | TN => 1
  | TAr A B => Nat.max (lev A + 1) (lev B)

/-- Rocq: `Analysis.SystemT.lev_pos`. -/
theorem lev_pos : ∀ τ : Ty, 1 ≤ lev τ
  | TN => Nat.le_refl 1
  | TAr _ _ => Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_max_left _ _)

/-! ## Infinitary terms

Applications are annotated with the type `A → B` of the function, so that the
level of a potential cut can be read off the term. -/

/-- Rocq: `Analysis.SystemT.iterm`. -/
inductive ITerm : Type where
  | ivar : Nat → ITerm
  | ilam : Ty → ITerm → ITerm
  | iapp : Ty → Ty → ITerm → ITerm → ITerm
  | izero : ITerm
  | isucc : ITerm → ITerm
  /-- `Ω_C(f) : nat → C` -/
  | iomega : Ty → (Nat → ITerm) → ITerm

open ITerm

/-- Rocq: `Analysis.SystemT.lift`. -/
def lift (c : Nat) : ITerm → ITerm
  | ivar y => ivar (if y < c then y else y + 1)
  | ilam A K => ilam A (lift (c + 1) K)
  | iapp A B M N => iapp A B (lift c M) (lift c N)
  | izero => izero
  | isucc K => isucc (lift c K)
  | iomega C f => iomega C (fun n => lift c (f n))

/-- Rocq: `Analysis.SystemT.unshift`. -/
def unshift (k y : Nat) : Nat := if y < k then y else y - 1

/-- `subst M k N` replaces the variable `k` of `M` by `N`. Rocq: `Analysis.SystemT.subst`. -/
def subst : ITerm → Nat → ITerm → ITerm
  | ivar y, k, N => if y = k then N else ivar (unshift k y)
  | ilam A K, k, N => ilam A (subst K (k + 1) (lift 0 N))
  | iapp A B M1 M2, k, N => iapp A B (subst M1 k N) (subst M2 k N)
  | izero, _, _ => izero
  | isucc K, k, N => isucc (subst K k N)
  | iomega C f, k, N => iomega C (fun n => subst (f n) k N)

/-- Rocq: `Analysis.SystemT.inum`. -/
def inum : Nat → ITerm
  | 0 => izero
  | n + 1 => isucc (inum n)

/-- The head variable of an application spine, if any. Rocq: `Analysis.SystemT.head_var`. -/
def headVar : ITerm → Option Nat
  | ivar x => some x
  | iapp _ _ M _ => headVar M
  | ilam _ _ => none
  | izero => none
  | isucc _ => none
  | iomega _ _ => none

/-- Rocq: `Analysis.SystemT.isvh`. -/
def isvh (M : ITerm) : Bool :=
  match headVar M with
  | some _ => true
  | none => false

/-- Rocq: `Analysis.SystemT.is_om`. -/
def isOm : ITerm → Bool
  | iomega _ _ => true
  | ivar _ => false
  | ilam _ _ => false
  | iapp _ _ _ _ => false
  | izero => false
  | isucc _ => false

/-- An application `M N` at `A → B` is admissible at cut rank `ρ` when `M` has
a variable head, or it is an ω-term applied to a neutral argument (or
ω-redexes are allowed, `1 ≤ ρ`), or its level is at most `ρ`.
Rocq: `Analysis.SystemT.cut_ok`. -/
def cutOk (ρ : Nat) (A B : Ty) (M N : ITerm) : Bool :=
  isvh M || (isOm M && (isvh N || Nat.ble 1 ρ)) || Nat.ble (lev (TAr A B)) ρ

/-! ## Ordinal heights as V forms

Heights are V forms: `V a x` denotes `ω^a + x`. The forms need not be normal:
`vplus` appends the summands, which denotes ordinal addition. -/

/-- Rocq: `Analysis.SystemT.vplus`. -/
def vplus : VForm → VForm → VForm
  | Z, b => b
  | V e x, b => V e (vplus x b)

/-- Rocq: `Analysis.SystemT.vexp`. -/
def vexp (a : VForm) : VForm := V a Z
/-- Rocq: `Analysis.SystemT.vsucc`. -/
def vsucc (a : VForm) : VForm := vplus a (vexp Z)

/-- Rocq: `Analysis.SystemT.tower`. -/
def tower : Nat → VForm → VForm
  | 0, a => a
  | k + 1, a => tower k (vexp a)

/-- Rocq: `Analysis.SystemT.V_eq`. -/
theorem V_eq (a x : VForm) : sz (V a x) ≈ ω ^ sz a + sz x :=
  veblen_onePlus _ (complete a) _ (complete x)

/-- Rocq: `Analysis.SystemT.vplus_eq`. -/
theorem vplus_eq : ∀ a b : VForm, sz (vplus a b) ≈ sz a + sz b
  | Z, b => equiv_symm (zero_add (sz b))
  | V e x, b =>
    equiv_trans (V_eq e _) (equiv_trans (add_congr (equiv_refl _) (vplus_eq x b))
      (equiv_trans (add_assoc _ _ _) (add_congr (equiv_symm (V_eq e x)) (equiv_refl _))))

/-- Rocq: `Analysis.SystemT.vexp_eq`. -/
theorem vexp_eq (a : VForm) : sz (vexp a) ≈ ω ^ sz a := equiv_trans (V_eq a Z) (add_zero _)

/-- Rocq: `Analysis.SystemT.Z_eq`. -/
theorem Z_eq : sz Z ≈ 0 := equiv_refl _

/-- Rocq: `Analysis.SystemT.vsucc_eq`. -/
theorem vsucc_eq (a : VForm) : sz (vsucc a) ≈ succ (sz a) :=
  equiv_trans (vplus_eq _ _) (equiv_trans (add_congr (equiv_refl _) (equiv_trans (vexp_eq Z) (pow_zero ω)))
    (equiv_trans (add_succ _ _) (succ_congruence (add_zero _))))

/-- Rocq: `Analysis.SystemT.vplus_le1`. -/
theorem vplus_le1 (a b : VForm) : sz a ≤ sz (vplus a b) := le_trans (le_add_right _ _) (vplus_eq a b).ge

/-- Rocq: `Analysis.SystemT.vplus_le2`. -/
theorem vplus_le2 (a b : VForm) : sz b ≤ sz (vplus a b) := le_trans (le_add_left _ _) (vplus_eq a b).ge

/-- Rocq: `Analysis.SystemT.vsucc_lt`. -/
theorem vsucc_lt (a : VForm) : sz a < sz (vsucc a) := lt_of_lt_of_le (succ_lt _) (vsucc_eq a).ge

/-- Rocq: `Analysis.SystemT.vsucc_least`. -/
theorem vsucc_least {a b : VForm} (h : sz a < sz b) : sz (vsucc a) ≤ sz b :=
  le_trans (vsucc_eq a).le (succ_least h)

/-- `ω^c` is closed under addition, for complete `c`. Rocq: `Analysis.SystemT.below_exp_add`. -/
theorem below_exp_add (c : VForm) {x y : Ordinal.{0}} (hx : x < ω ^ sz c) (hy : y < ω ^ sz c) :
    x + y < ω ^ sz c :=
  powOmega_additively_closed (complete c) x y hx hy

/-- Rocq: `Analysis.SystemT.vexp_increasing`. -/
theorem vexp_increasing {a b : VForm} (h : sz a < sz b) : sz (vexp a) < sz (vexp b) :=
  lt_of_le_of_lt (vexp_eq a).le (lt_of_lt_of_le (pow_lt_pow_right omega_gt1 h) (vexp_eq b).ge)

/-- Every V form is below its own power of `ω`. Rocq: `Analysis.SystemT.VF_shrink`. -/
theorem VF_shrink : ∀ x : VForm, sz x < ω ^ sz x
  | Z => pow_pos ω _
  | V a x =>
    lt_of_le_of_lt (V_eq a x).le
      (below_exp_add (V a x) (pow_lt_pow_right omega_gt1 (denote_shrink1 a x))
        (lt_of_lt_of_le (VF_shrink x) (pow_le_pow_right ω (denote_le2 x a))))

/-- The bound used by the reduction lemmas: `a + b + 1 < ω^c` when
`a, b < ω^c` and `c > 0`. Rocq: `Analysis.SystemT.below_exp_sum`. -/
theorem below_exp_sum {a b c : VForm} (ha : sz a < sz (vexp c)) (hb : sz b < sz (vexp c)) (hc : sz Z < sz c) :
    sz (vsucc (vplus a b)) < sz (vexp c) := by
  refine lt_of_le_of_lt (le_trans (vsucc_eq _).le (succ_monotone (vplus_eq a b).le)) ?_
  refine lt_of_le_of_lt (le_trans (succ_congruence (add_zero _)).ge (add_succ _ _).ge) ?_
  refine lt_of_lt_of_le ?_ (vexp_eq c).ge
  refine below_exp_add c (below_exp_add c (lt_of_lt_of_le ha (vexp_eq c).le) (lt_of_lt_of_le hb (vexp_eq c).le)) ?_
  exact lt_of_le_of_lt (pow_zero ω).ge (pow_lt_pow_right omega_gt1 hc)

/-! ## Derivations with heights and cut ranks

`D ρ Γ M A α`: `M` has type `A` in `Γ`, by a derivation of height `α` whose
cuts all have level at most `ρ`. Premises have strictly smaller heights;
leaves may have any height. -/

/-- Rocq: `Analysis.SystemT.D`. -/
inductive D (ρ : Nat) : List Ty → ITerm → Ty → VForm → Prop where
  | var (Γ : List Ty) (x : Nat) (A : Ty) (α : VForm) : List.nthError Γ x = some A → D ρ Γ (ivar x) A α
  | lam (Γ : List Ty) (A : Ty) (M : ITerm) (B : Ty) (β α : VForm) :
      D ρ (A :: Γ) M B β → sz β < sz α → D ρ Γ (ilam A M) (TAr A B) α
  | app (Γ : List Ty) (A B : Ty) (M N : ITerm) (β1 β2 α : VForm) :
      D ρ Γ M (TAr A B) β1 → D ρ Γ N A β2 → sz β1 < sz α → sz β2 < sz α →
      cutOk ρ A B M N = true → D ρ Γ (iapp A B M N) B α
  | zero (Γ : List Ty) (α : VForm) : D ρ Γ izero TN α
  | succ (Γ : List Ty) (M : ITerm) (β α : VForm) : D ρ Γ M TN β → sz β < sz α → D ρ Γ (isucc M) TN α
  | omega (Γ : List Ty) (C : Ty) (f : Nat → ITerm) (β : Nat → VForm) (α : VForm) :
      (∀ n, D ρ Γ (f n) C (β n)) → (∀ n, sz (β n) < sz α) → D ρ Γ (iomega C f) (TAr TN C) α

theorem or_true_cases {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> first | exact .inl rfl | exact .inr rfl | cases h

theorem and_true_cases {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem or_true_l {a : Bool} (b : Bool) (h : a = true) : (a || b) = true := by subst h; rfl
theorem or_true_r (a : Bool) {b : Bool} (h : b = true) : (a || b) = true := by subst h; cases a <;> rfl

/-- Rocq: `Analysis.SystemT.cut_ok_cases`. -/
theorem cutOk_cases {ρ : Nat} {A B : Ty} {M N : ITerm} (h : cutOk ρ A B M N = true) :
    isvh M = true ∨ (isOm M = true ∧ (isvh N = true ∨ 1 ≤ ρ)) ∨ lev (TAr A B) ≤ ρ := by
  rcases or_true_cases h with h | h
  · rcases or_true_cases h with h | h
    · exact .inl h
    · obtain ⟨h1, h2⟩ := and_true_cases h
      rcases or_true_cases h2 with h2 | h2
      · exact .inr (.inl ⟨h1, .inl h2⟩)
      · exact .inr (.inl ⟨h1, .inr (Nat.le_of_ble_eq_true h2)⟩)
  · exact .inr (.inr (Nat.le_of_ble_eq_true h))

/-- Rocq: `Analysis.SystemT.cut_ok_vh`. -/
theorem cutOk_vh (ρ : Nat) (A B : Ty) {M : ITerm} (N : ITerm) (h : isvh M = true) : cutOk ρ A B M N = true :=
  or_true_l _ (or_true_l _ h)

/-- Rocq: `Analysis.SystemT.cut_ok_om`. -/
theorem cutOk_om (ρ : Nat) (A B : Ty) {M N : ITerm} (h1 : isOm M = true) (h2 : isvh N = true ∨ 1 ≤ ρ) :
    cutOk ρ A B M N = true := by
  refine or_true_l _ (or_true_r _ ?_)
  rw [h1]
  rcases h2 with h2 | h2
  · exact or_true_l _ h2
  · exact or_true_r _ (Nat.ble_eq_true_of_le h2)

/-- Rocq: `Analysis.SystemT.cut_ok_lev`. -/
theorem cutOk_lev {ρ : Nat} {A B : Ty} (M N : ITerm) (h : lev (TAr A B) ≤ ρ) : cutOk ρ A B M N = true :=
  or_true_r _ (Nat.ble_eq_true_of_le h)

/-- Rocq: `Analysis.SystemT.cut_ok_mono`. -/
theorem cutOk_mono {ρ ρ' : Nat} {A B : Ty} {M N : ITerm} (hr : ρ ≤ ρ') (h : cutOk ρ A B M N = true) :
    cutOk ρ' A B M N = true := by
  rcases cutOk_cases h with h1 | ⟨h1, h2⟩ | h1
  · exact cutOk_vh _ _ _ _ h1
  · exact cutOk_om _ _ _ h1 (h2.imp id (fun h => Nat.le_trans h hr))
  · exact cutOk_lev _ _ (Nat.le_trans h1 hr)

/-- Raising the height or the cut rank preserves derivability. Rocq: `Analysis.SystemT.D_mono`. -/
theorem D_mono {ρ : Nat} {Γ : List Ty} {M : ITerm} {A : Ty} {α : VForm} (h : D ρ Γ M A α) :
    ∀ {ρ' : Nat} {α' : VForm}, ρ ≤ ρ' → sz α ≤ sz α' → D ρ' Γ M A α' := by
  induction h with
  | var Γ x A α hx => intro ρ' α' _ _; exact .var _ _ _ _ hx
  | lam Γ A M B β α _ hβ ih =>
    intro ρ' α' hr ha; exact .lam _ _ _ _ _ _ (ih hr (le_refl _)) (lt_of_lt_of_le hβ ha)
  | app Γ A B M N β1 β2 α _ _ hb1 hb2 hc ih1 ih2 =>
    intro ρ' α' hr ha
    exact .app _ _ _ _ _ _ _ _ (ih1 hr (le_refl _)) (ih2 hr (le_refl _)) (lt_of_lt_of_le hb1 ha)
      (lt_of_lt_of_le hb2 ha) (cutOk_mono hr hc)
  | zero => intro _ _ _ _; exact .zero _ _
  | succ Γ M β α _ hβ ih =>
    intro ρ' α' hr ha; exact .succ _ _ _ _ (ih hr (le_refl _)) (lt_of_lt_of_le hβ ha)
  | omega Γ C f β α _ hβ ih =>
    intro ρ' α' hr ha
    exact .omega _ _ _ β _ (fun n => ih n hr (le_refl _)) (fun n => lt_of_lt_of_le (hβ n) ha)

/-- Rocq: `Analysis.SystemT.D_height`. -/
theorem D_height {ρ : Nat} {Γ : List Ty} {M : ITerm} {A : Ty} {α α' : VForm} (h : D ρ Γ M A α)
    (ha : sz α ≤ sz α') : D ρ Γ M A α' :=
  D_mono h (Nat.le_refl ρ) ha

/-! ## Weakening -/

/-- Rocq: `Analysis.SystemT.head_var_lift`. -/
theorem headVar_lift (c : Nat) : ∀ M : ITerm,
    headVar (lift c M) = (headVar M).map (fun y => if y < c then y else y + 1)
  | ivar _ => rfl
  | iapp _ _ M _ => headVar_lift c M
  | ilam _ _ => rfl
  | izero => rfl
  | isucc _ => rfl
  | iomega _ _ => rfl

/-- Rocq: `Analysis.SystemT.isvh_lift`. -/
theorem isvh_lift (c : Nat) (M : ITerm) : isvh (lift c M) = isvh M := by
  unfold isvh; rw [headVar_lift]; cases headVar M <;> rfl

/-- Rocq: `Analysis.SystemT.is_om_lift`. -/
theorem isOm_lift (c : Nat) : ∀ M : ITerm, isOm (lift c M) = isOm M
  | ivar _ => rfl
  | ilam _ _ => rfl
  | iapp _ _ _ _ => rfl
  | izero => rfl
  | isucc _ => rfl
  | iomega _ _ => rfl

/-- Rocq: `Analysis.SystemT.cut_ok_lift`. -/
theorem cutOk_lift (ρ : Nat) (A B : Ty) (c : Nat) (M N : ITerm) :
    cutOk ρ A B (lift c M) (lift c N) = cutOk ρ A B M N := by
  unfold cutOk; rw [isvh_lift, isvh_lift, isOm_lift]

theorem nthError_sv {X : Type} : ∀ (Γ1 Γ2 : List X) (a : X) (y : Nat),
    List.nthError (Γ1 ++ a :: Γ2) (sv Γ1.length y) = List.nthError (Γ1 ++ Γ2) y
  | [], _, _, _ => rfl
  | _ :: _, _, _, 0 => rfl
  | _ :: Γ1, Γ2, a, y + 1 => nthError_sv Γ1 Γ2 a y

/-- Rocq: `Analysis.SystemT.nth_error_insert`. -/
theorem nthError_insert {X : Type} (Γ1 Γ2 : List X) (a : X) (y : Nat) :
    List.nthError (Γ1 ++ a :: Γ2) (if y < Γ1.length then y else y + 1) = List.nthError (Γ1 ++ Γ2) y := by
  rw [sv_eq]; exact nthError_sv Γ1 Γ2 a y

theorem nthError_svar {X : Type} : ∀ (Γ1 Γ2 : List X) (a : X) {y z : Nat},
    svar Γ1.length y = some z → List.nthError (Γ1 ++ Γ2) z = List.nthError (Γ1 ++ a :: Γ2) y
  | [], _, _, 0, _, h => nomatch h
  | [], _, _, _ + 1, _, h => by cases h; rfl
  | _ :: _, _, _, 0, _, h => by cases h; rfl
  | _ :: Γ1, Γ2, a, y + 1, z, h => by
    obtain ⟨z0, h0, rfl⟩ := map_succ_some h
    exact nthError_svar Γ1 Γ2 a h0

/-- Rocq: `Analysis.SystemT.nth_error_remove`. -/
theorem nthError_remove {X : Type} (Γ1 Γ2 : List X) (a : X) {y : Nat} (h : y ≠ Γ1.length) :
    List.nthError (Γ1 ++ Γ2) (unshift Γ1.length y) = List.nthError (Γ1 ++ a :: Γ2) y := by
  have e := svar_spec Γ1.length y
  rw [ite_eq_right h] at e
  exact nthError_svar Γ1 Γ2 a e

/-- Rocq: `Analysis.SystemT.nth_error_at`. -/
theorem nthError_at {X : Type} : ∀ (Γ1 Γ2 : List X) (a : X), List.nthError (Γ1 ++ a :: Γ2) Γ1.length = some a
  | [], _, _ => rfl
  | _ :: Γ1, Γ2, a => nthError_at Γ1 Γ2 a

/-- Rocq: `Analysis.SystemT.D_weaken`. -/
theorem D_weaken {ρ : Nat} {Γ : List Ty} {M : ITerm} {A : Ty} {α : VForm} (h : D ρ Γ M A α) :
    ∀ (Γ1 Γ2 : List Ty) (B : Ty), Γ = Γ1 ++ Γ2 → D ρ (Γ1 ++ B :: Γ2) (lift Γ1.length M) A α := by
  induction h with
  | var Γ x A α hx =>
    intro Γ1 Γ2 B E; subst E
    exact .var _ _ _ _ ((nthError_insert Γ1 Γ2 B x).trans hx)
  | lam Γ A M B β α _ hβ ih =>
    intro Γ1 Γ2 B0 E; subst E
    exact .lam _ _ _ _ _ _ (ih (A :: Γ1) Γ2 B0 rfl) hβ
  | app Γ A B M N β1 β2 α _ _ hb1 hb2 hc ih1 ih2 =>
    intro Γ1 Γ2 B0 E
    refine .app _ _ _ _ _ _ _ _ (ih1 Γ1 Γ2 B0 E) (ih2 Γ1 Γ2 B0 E) hb1 hb2 ?_
    rw [cutOk_lift]; exact hc
  | zero => intro _ _ _ _; exact .zero _ _
  | succ Γ M β α _ hβ ih =>
    intro Γ1 Γ2 B0 E; exact .succ _ _ _ _ (ih Γ1 Γ2 B0 E) hβ
  | omega Γ C f β α _ hβ ih =>
    intro Γ1 Γ2 B0 E; exact .omega _ _ _ β _ (fun n => ih n Γ1 Γ2 B0 E) hβ

/-- Rocq: `Analysis.SystemT.D_weaken0`. -/
theorem D_weaken0 {ρ : Nat} {Γ : List Ty} {M : ITerm} {A : Ty} (B : Ty) {α : VForm} (h : D ρ Γ M A α) :
    D ρ (B :: Γ) (lift 0 M) A α :=
  D_weaken h [] Γ B rfl

/-! ## Substitution

The type of a variable-headed spine has level at most that of the head; so
substituting at `A` creates cuts of level at most `lev A`. -/

/-- Rocq: `Analysis.SystemT.head_lev`. -/
theorem head_lev {ρ : Nat} {Γ : List Ty} {M : ITerm} {T : Ty} {α : VForm} (h : D ρ Γ M T α) :
    ∀ x A, headVar M = some x → List.nthError Γ x = some A → lev T ≤ lev A := by
  induction h with
  | var Γ x A α hx =>
    intro x0 A0 hh hx0
    cases hh; rw [hx] at hx0; cases hx0; exact Nat.le_refl _
  | app Γ A B M N β1 β2 α _ _ _ _ _ ih1 _ =>
    intro x0 A0 hh hx0
    exact Nat.le_trans (Nat.le_max_right _ _) (ih1 x0 A0 hh hx0)
  | lam => intro _ _ hh; cases hh
  | zero => intro _ _ hh; cases hh
  | succ => intro _ _ hh; cases hh
  | omega => intro _ _ hh; cases hh

/-- Rocq: `Analysis.SystemT.head_var_subst`. -/
theorem headVar_subst : ∀ (M : ITerm) (k : Nat) (N : ITerm) {y : Nat},
    headVar M = some y → y ≠ k → headVar (subst M k N) = some (unshift k y)
  | ivar x, k, N, y, hh, hy => by
    cases hh
    show headVar (if x = k then N else ivar (unshift k x)) = _
    rw [ite_eq_right hy]; rfl
  | iapp _ _ M _, k, N, _, hh, hy => headVar_subst M k N hh hy
  | ilam _ _, _, _, _, hh, _ => nomatch hh
  | izero, _, _, _, hh, _ => nomatch hh
  | isucc _, _, _, _, hh, _ => nomatch hh
  | iomega _ _, _, _, _, hh, _ => nomatch hh

/-- Rocq: `Analysis.SystemT.is_om_subst`. -/
theorem isOm_subst : ∀ (M : ITerm) (k : Nat) (N : ITerm), isOm M = true → isOm (subst M k N) = true
  | iomega _ _, _, _, _ => rfl
  | ivar _, _, _, h => nomatch h
  | ilam _ _, _, _, h => nomatch h
  | iapp _ _ _ _, _, _, h => nomatch h
  | izero, _, _, h => nomatch h
  | isucc _, _, _, h => nomatch h

theorem vplus_lt_vplus (a : VForm) {b c : VForm} (h : sz b < sz c) : sz (vplus a b) < sz (vplus a c) :=
  lt_of_le_of_lt (vplus_eq a b).le (lt_of_lt_of_le (add_lt_add_left _ h) (vplus_eq a c).ge)

/-- Rocq: `Analysis.SystemT.subst_typed`. -/
theorem subst_typed {ρ : Nat} {Γ : List Ty} {M : ITerm} {B : Ty} {α : VForm} (h : D ρ Γ M B α) :
    ∀ (Γ1 Γ2 : List Ty) (A : Ty) (N : ITerm) (β : VForm), Γ = Γ1 ++ A :: Γ2 → D ρ (Γ1 ++ Γ2) N A β →
      lev A ≤ ρ → D ρ (Γ1 ++ Γ2) (subst M Γ1.length N) B (vplus β α) := by
  induction h with
  | var Γ x A α hx =>
    intro Γ1 Γ2 A0 N0 β0 E HN _
    subst E
    show D _ _ (if x = Γ1.length then N0 else ivar (unshift Γ1.length x)) _ _
    by_cases hxe : x = Γ1.length
    · rw [ite_eq_left hxe]
      subst hxe
      rw [nthError_at] at hx; cases hx
      exact D_height HN (vplus_le1 _ _)
    · rw [ite_eq_right hxe]
      exact .var _ _ _ _ ((nthError_remove Γ1 Γ2 A0 hxe).trans hx)
  | lam Γ A M B β α _ hβ ih =>
    intro Γ1 Γ2 A0 N0 β0 E HN Hl
    subst E
    exact .lam _ _ _ _ _ _ (ih (A :: Γ1) Γ2 A0 (lift 0 N0) β0 rfl (D_weaken0 A HN) Hl) (vplus_lt_vplus _ hβ)
  | app Γ A B M N β1 β2 α hM _ hb1 hb2 hc ih1 ih2 =>
    intro Γ1 Γ2 A0 N0 β0 E HN Hl
    refine .app _ _ _ _ _ _ _ _ (ih1 Γ1 Γ2 A0 N0 β0 E HN Hl) (ih2 Γ1 Γ2 A0 N0 β0 E HN Hl)
      (vplus_lt_vplus _ hb1) (vplus_lt_vplus _ hb2) ?_
    rcases cutOk_cases hc with h4 | ⟨h4, _⟩ | h4
    · unfold isvh at h4
      cases hy : headVar M with
      | none => rw [hy] at h4; cases h4
      | some y =>
        by_cases hye : y = Γ1.length
        · subst hye
          subst E
          exact cutOk_lev _ _ (Nat.le_trans (head_lev hM _ A0 hy (nthError_at Γ1 Γ2 A0)) Hl)
        · refine cutOk_vh _ _ _ _ ?_
          show (match headVar (subst M Γ1.length N0) with | some _ => true | none => false) = true
          rw [headVar_subst M _ N0 hy hye]
    · exact cutOk_om _ _ _ (isOm_subst _ _ _ h4) (.inr (Nat.le_trans (lev_pos A0) Hl))
    · exact cutOk_lev _ _ h4
  | zero => intro _ _ _ _ _ _ _ _; exact .zero _ _
  | succ Γ M β α _ hβ ih =>
    intro Γ1 Γ2 A0 N0 β0 E HN Hl
    exact .succ _ _ _ _ (ih Γ1 Γ2 A0 N0 β0 E HN Hl) (vplus_lt_vplus _ hβ)
  | omega Γ C f β α _ hβ ih =>
    intro Γ1 Γ2 A0 N0 β0 E HN Hl
    exact .omega _ _ _ (fun n => vplus β0 (β n)) _ (fun n => ih n Γ1 Γ2 A0 N0 β0 E HN Hl)
      (fun n => vplus_lt_vplus _ (hβ n))

/-! ## Reduction

The compatible closure of β-reduction, of the ω-rules (selecting a branch,
or stripping a successor), and of the commuting conversions for an ω-term
applied to a neutral argument. -/

/-- Rocq: `Analysis.SystemT.red`. -/
inductive Red : ITerm → ITerm → Prop where
  | refl (M : ITerm) : Red M M
  | trans (M N P : ITerm) : Red M N → Red N P → Red M P
  | lam (A : Ty) (M M' : ITerm) : Red M M' → Red (ilam A M) (ilam A M')
  | app (A B : Ty) (M M' N N' : ITerm) : Red M M' → Red N N' → Red (iapp A B M N) (iapp A B M' N')
  | succ (M M' : ITerm) : Red M M' → Red (isucc M) (isucc M')
  | omega (C : Ty) (f g : Nat → ITerm) : (∀ n, Red (f n) (g n)) → Red (iomega C f) (iomega C g)
  | beta (A B A' : Ty) (K N : ITerm) : Red (iapp A B (ilam A' K) N) (subst K 0 N)
  | om_zero (A B C : Ty) (f : Nat → ITerm) : Red (iapp A B (iomega C f) izero) (f 0)
  | om_succ (A B C : Ty) (f : Nat → ITerm) (K : ITerm) :
      Red (iapp A B (iomega C f) (isucc K)) (iapp A B (iomega C (fun n => f (n + 1))) K)
  | comm (A B A0 B0 C : Ty) (f : Nat → ITerm) (K N : ITerm) :
      Red (iapp A B (iapp A0 B0 (iomega C f) K) N) (iapp A0 B (iomega B (fun n => iapp A B (f n) N)) K)
  | case (A B A0 B0 C E : Ty) (f g : Nat → ITerm) (K : ITerm) :
      Red (iapp A B (iomega C f) (iapp A0 B0 (iomega E g) K))
        (iapp A0 B (iomega B (fun n => iapp A B (iomega C f) (g n))) K)

/-! ## The reduction lemmas -/

/-- `app_red A B M N` reduces the application `M N` at `A → B`: a λ is
substituted into, and an ω-term applied to an argument absorbs `N` into its
branches. Rocq: `Analysis.SystemT.app_red`. -/
def appRed (A B : Ty) : ITerm → ITerm → ITerm
  | ilam _ K, N => subst K 0 N
  | iapp A0 B0 M1 K, N =>
    match M1 with
    | iomega _ f => iapp A0 B (iomega B (fun n => appRed A B (f n) N)) K
    | ivar x => iapp A B (iapp A0 B0 (ivar x) K) N
    | ilam A' K' => iapp A B (iapp A0 B0 (ilam A' K') K) N
    | iapp A1 B1 M2 K' => iapp A B (iapp A0 B0 (iapp A1 B1 M2 K') K) N
    | izero => iapp A B (iapp A0 B0 izero K) N
    | isucc K' => iapp A B (iapp A0 B0 (isucc K') K) N
  | ivar x, N => iapp A B (ivar x) N
  | izero, N => iapp A B izero N
  | isucc K, N => iapp A B (isucc K) N
  | iomega C f, N => iapp A B (iomega C f) N

/-- `omega_red A B C f N` reduces the ω-redex `Ω_C(f) N`: a numeral selects a
branch, and an ω-term in `N` is commuted outwards. Rocq: `Analysis.SystemT.omega_red`. -/
def omegaRed (A B C : Ty) : (Nat → ITerm) → ITerm → ITerm
  | f, izero => f 0
  | f, isucc K => omegaRed A B C (fun n => f (n + 1)) K
  | f, iapp A0 B0 N1 K =>
    match N1 with
    | iomega _ g => iapp A0 B (iomega B (fun n => omegaRed A B C f (g n))) K
    | ivar x => iapp A B (iomega C f) (iapp A0 B0 (ivar x) K)
    | ilam A' K' => iapp A B (iomega C f) (iapp A0 B0 (ilam A' K') K)
    | iapp A1 B1 M2 K' => iapp A B (iomega C f) (iapp A0 B0 (iapp A1 B1 M2 K') K)
    | izero => iapp A B (iomega C f) (iapp A0 B0 izero K)
    | isucc K' => iapp A B (iomega C f) (iapp A0 B0 (isucc K') K)
  | f, ivar x => iapp A B (iomega C f) (ivar x)
  | f, ilam A' K => iapp A B (iomega C f) (ilam A' K)
  | f, iomega E g => iapp A B (iomega C f) (iomega E g)
termination_by structural _ N => N

/-- The reduction of a cut, once both sides are eliminated. -/
def cutRed (A B : Ty) (M' N' : ITerm) : ITerm :=
  match M' with
  | iomega C f => omegaRed A B C f N'
  | ivar x => appRed A B (ivar x) N'
  | ilam A' K => appRed A B (ilam A' K) N'
  | iapp A0 B0 M1 K => appRed A B (iapp A0 B0 M1 K) N'
  | izero => appRed A B izero N'
  | isucc K => appRed A B (isucc K) N'

/-- One pass of cut elimination: cuts of level `ρ+1` are reduced, those of
lower level are kept. Rocq: `Analysis.SystemT.elim`. -/
def elim (ρ : Nat) : ITerm → ITerm
  | ivar x => ivar x
  | ilam A K => ilam A (elim ρ K)
  | iapp A B M N =>
    if cutOk ρ A B (elim ρ M) (elim ρ N) then iapp A B (elim ρ M) (elim ρ N)
    else cutRed A B (elim ρ M) (elim ρ N)
  | izero => izero
  | isucc K => isucc (elim ρ K)
  | iomega C f => iomega C (fun n => elim ρ (f n))

/-- Rocq: `Analysis.SystemT.norm`. -/
def norm : Nat → ITerm → ITerm
  | 0, M => M
  | r + 1, M => norm r (elim r M)

/-- Rocq: `Analysis.SystemT.app_red_red`. -/
theorem appRed_red (A B : Ty) : ∀ M N : ITerm, Red (iapp A B M N) (appRed A B M N)
  | ilam _ _, _ => .beta _ _ _ _ _
  | iapp _ _ M1 _, N =>
    match M1 with
    | iomega _ f =>
      .trans _ _ _ (.comm _ _ _ _ _ _ _ _) (.app _ _ _ _ _ _ (.omega _ _ _ fun n => appRed_red A B (f n) N) (.refl _))
    | ivar _ => .refl _
    | ilam _ _ => .refl _
    | iapp _ _ _ _ => .refl _
    | izero => .refl _
    | isucc _ => .refl _
  | ivar _, _ => .refl _
  | izero, _ => .refl _
  | isucc _, _ => .refl _
  | iomega _ _, _ => .refl _

/-- Rocq: `Analysis.SystemT.omega_red_red`. -/
theorem omegaRed_red (A B C : Ty) : ∀ (f : Nat → ITerm) (N : ITerm),
    Red (iapp A B (iomega C f) N) (omegaRed A B C f N)
  | _, izero => .om_zero _ _ _ _
  | _, isucc K => .trans _ _ _ (.om_succ _ _ _ _ _) (omegaRed_red A B C _ K)
  | f, iapp _ _ N1 _ =>
    match N1 with
    | iomega _ g =>
      .trans _ _ _ (.case _ _ _ _ _ _ _ _ _)
        (.app _ _ _ _ _ _ (.omega _ _ _ fun n => omegaRed_red A B C f (g n)) (.refl _))
    | ivar _ => .refl _
    | ilam _ _ => .refl _
    | iapp _ _ _ _ => .refl _
    | izero => .refl _
    | isucc _ => .refl _
  | _, ivar _ => .refl _
  | _, ilam _ _ => .refl _
  | _, iomega _ _ => .refl _
termination_by structural _ N => N

theorem cutRed_red (A B : Ty) (M N : ITerm) : Red (iapp A B M N) (cutRed A B M N) := by
  cases M with
  | iomega C f => exact omegaRed_red A B C f N
  | ivar x => exact appRed_red A B _ N
  | ilam A' K => exact appRed_red A B _ N
  | iapp A0 B0 M1 K => exact appRed_red A B _ N
  | izero => exact appRed_red A B _ N
  | isucc K => exact appRed_red A B _ N

/-- Rocq: `Analysis.SystemT.elim_red`. -/
theorem elim_red (ρ : Nat) : ∀ M : ITerm, Red M (elim ρ M)
  | ivar _ => .refl _
  | ilam A K => .lam _ _ _ (elim_red ρ K)
  | iapp A B M N => by
    have h := Red.app A B _ _ _ _ (elim_red ρ M) (elim_red ρ N)
    show Red _ (if cutOk ρ A B (elim ρ M) (elim ρ N) then _ else _)
    cases cutOk ρ A B (elim ρ M) (elim ρ N) with
    | true => exact h
    | false => exact .trans _ _ _ h (cutRed_red A B _ _)
  | izero => .refl _
  | isucc K => .succ _ _ (elim_red ρ K)
  | iomega C f => .omega _ _ _ fun n => elim_red ρ (f n)

/-- Rocq: `Analysis.SystemT.norm_red`. -/
theorem norm_red : ∀ (ρ : Nat) (M : ITerm), Red M (norm ρ M)
  | 0, _ => .refl _
  | ρ + 1, M => .trans _ _ _ (elim_red ρ M) (norm_red ρ _)

/-! ## Inversion and bookkeeping -/

/-- Rocq: `Analysis.SystemT.inv_var`. -/
theorem inv_var {ρ : Nat} {Γ : List Ty} {x : Nat} {T : Ty} {α : VForm} (h : D ρ Γ (ivar x) T α) :
    List.nthError Γ x = some T := by
  cases h with | var _ _ _ _ hx => exact hx

/-- Rocq: `Analysis.SystemT.inv_lam`. -/
theorem inv_lam {ρ : Nat} {Γ : List Ty} {A : Ty} {K : ITerm} {T : Ty} {α : VForm} (h : D ρ Γ (ilam A K) T α) :
    ∃ B β, T = TAr A B ∧ D ρ (A :: Γ) K B β ∧ sz β < sz α := by
  cases h with | lam _ _ _ B β _ hK hβ => exact ⟨B, β, rfl, hK, hβ⟩

/-- Rocq: `Analysis.SystemT.inv_app`. -/
theorem inv_app {ρ : Nat} {Γ : List Ty} {A B : Ty} {M N : ITerm} {T : Ty} {α : VForm}
    (h : D ρ Γ (iapp A B M N) T α) :
    T = B ∧ ∃ β1 β2, D ρ Γ M (TAr A B) β1 ∧ D ρ Γ N A β2 ∧ sz β1 < sz α ∧ sz β2 < sz α ∧
      cutOk ρ A B M N = true := by
  cases h with | app _ _ _ _ _ β1 β2 _ hM hN hb1 hb2 hc => exact ⟨rfl, β1, β2, hM, hN, hb1, hb2, hc⟩

/-- Rocq: `Analysis.SystemT.inv_succ`. -/
theorem inv_succ {ρ : Nat} {Γ : List Ty} {K : ITerm} {T : Ty} {α : VForm} (h : D ρ Γ (isucc K) T α) :
    T = TN ∧ ∃ β, D ρ Γ K TN β ∧ sz β < sz α := by
  cases h with | succ _ _ β _ hK hβ => exact ⟨rfl, β, hK, hβ⟩

/-- Rocq: `Analysis.SystemT.inv_omega`. -/
theorem inv_omega {ρ : Nat} {Γ : List Ty} {C : Ty} {f : Nat → ITerm} {T : Ty} {α : VForm}
    (h : D ρ Γ (iomega C f) T α) :
    T = TAr TN C ∧ ∃ β : Nat → VForm, (∀ n, D ρ Γ (f n) C (β n)) ∧ ∀ n, sz (β n) < sz α := by
  cases h with | omega _ _ _ β _ hf hβ => exact ⟨rfl, β, hf, hβ⟩

/-- Rocq: `Analysis.SystemT.inv_zero`. -/
theorem inv_zero {ρ : Nat} {Γ : List Ty} {T : Ty} {α : VForm} (h : D ρ Γ izero T α) : T = TN := by
  cases h; rfl

/-- Rocq: `Analysis.SystemT.lev_dom`. -/
theorem lev_dom (A B : Ty) : lev A + 1 ≤ lev (TAr A B) := Nat.le_max_left _ _

/-- Rocq: `Analysis.SystemT.lev_cod`. -/
theorem lev_cod (A B : Ty) : lev B ≤ lev (TAr A B) := Nat.le_max_right _ _

/-- Rocq: `Analysis.SystemT.VF_ind`. -/
theorem VF_ind (P : VForm → Prop) (H : ∀ a, (∀ b, sz b < sz a → P b) → P a) (a : VForm) : P a :=
  (InvImage.wf (fun v : VForm => sz v) lt_wf).induction a H

/-- Rocq: `Analysis.SystemT.vplus_mono`. -/
theorem vplus_mono {a b c d : VForm} (h1 : sz a ≤ sz b) (h2 : sz c ≤ sz d) : sz (vplus a c) ≤ sz (vplus b d) :=
  le_trans (vplus_eq a c).le (le_trans (add_le_add h1 h2) (vplus_eq b d).ge)

/-- Rocq: `Analysis.SystemT.vsucc_mono`. -/
theorem vsucc_mono {a b : VForm} (h : sz a ≤ sz b) : sz (vsucc a) ≤ sz (vsucc b) :=
  le_trans (vsucc_eq a).le (le_trans (succ_monotone h) (vsucc_eq b).ge)

/-- Rocq: `Analysis.SystemT.vsucc_plus_le`. -/
theorem vsucc_plus_le (a : VForm) {b c : VForm} (h : sz b < sz c) : sz (vsucc (vplus a b)) ≤ sz (vplus a c) :=
  le_trans (vsucc_eq _).le (le_trans (succ_monotone (vplus_eq a b).le)
    (le_trans (add_succ _ _).ge (le_trans (add_le_add (le_refl _) (succ_least h)) (vplus_eq a c).ge)))

/-- Rocq: `Analysis.SystemT.lt_sum_l`. -/
theorem lt_sum_l (a b : VForm) : sz a < sz (vsucc (vplus a b)) := lt_of_le_of_lt (vplus_le1 a b) (vsucc_lt _)

/-- Rocq: `Analysis.SystemT.lt_sum_r`. -/
theorem lt_sum_r (a b : VForm) : sz b < sz (vsucc (vplus a b)) := lt_of_le_of_lt (vplus_le2 a b) (vsucc_lt _)

/-- Rocq: `Analysis.SystemT.lt_sum_r'`. -/
theorem lt_sum_r' (a : VForm) {b c : VForm} (h : sz c < sz b) : sz c < sz (vsucc (vplus a b)) :=
  lt_trans h (lt_sum_r a b)

/-- `a + b + 1` grows strictly in `b`. Rocq: `Analysis.SystemT.sum_step`. -/
theorem sum_step (a : VForm) {b c : VForm} (h : sz b < sz c) : sz (vsucc (vplus a b)) < sz (vsucc (vplus a c)) :=
  lt_of_le_of_lt (vsucc_plus_le a h) (vsucc_lt _)

/-! ## The reduction lemma for β and the commuting conversion

For `M : A → B` and `N : A` of cut rank `ρ`, with `lev (A → B) ≤ ρ+1`,
`app_red A B M N` has cut rank `ρ` and height `h N + h M + 1`, by transfinite
induction on the height of `M`. -/

/-- Rocq: `Analysis.SystemT.app_red_typed`. -/
theorem appRed_typed {ρ : Nat} {Γ : List Ty} {A B : Ty} {N : ITerm} {γ2 : VForm} (HN : D ρ Γ N A γ2)
    (Hl : lev (TAr A B) ≤ ρ + 1) :
    ∀ (γ1 : VForm) (M : ITerm), D ρ Γ M (TAr A B) γ1 → D ρ Γ (appRed A B M N) B (vsucc (vplus γ2 γ1)) := by
  have HlA : lev A ≤ ρ := Nat.le_of_succ_le_succ (Nat.le_trans (lev_dom A B) Hl)
  have Hρ : 1 ≤ ρ := Nat.le_trans (lev_pos A) HlA
  intro γ1
  refine VF_ind (fun γ1 => ∀ M, D ρ Γ M (TAr A B) γ1 → D ρ Γ (appRed A B M N) B (vsucc (vplus γ2 γ1)))
    (fun γ1 IH => ?_) γ1
  intro M HM
  have hdef : ∀ {M : ITerm}, D ρ Γ M (TAr A B) γ1 → cutOk ρ A B M N = true →
      D ρ Γ (iapp A B M N) B (vsucc (vplus γ2 γ1)) := fun hM hc =>
    .app _ _ _ _ _ _ _ _ hM HN (lt_sum_r _ _) (lt_sum_l _ _) hc
  cases M with
  | ivar x => exact hdef HM (cutOk_vh _ _ _ _ rfl)
  | ilam A' K =>
    obtain ⟨B', β, E, HK, hβ⟩ := inv_lam HM
    cases E
    exact D_height (subst_typed HK [] Γ A N γ2 rfl HN HlA)
      (le_of_lt (lt_of_le_of_lt (vplus_mono (le_refl _) (le_of_lt hβ)) (vsucc_lt _)))
  | iapp A0 B0 M1 K =>
    obtain ⟨E, β1, β2, HM1, HK, hb1, hb2, hc⟩ := inv_app HM
    subst E
    have hdef' : isOm M1 = false → D ρ Γ (iapp A B (iapp A0 (TAr A B) M1 K) N) B (vsucc (vplus γ2 γ1)) := by
      intro hno
      rcases cutOk_cases hc with hv | ⟨ho, _⟩ | hl'
      · exact hdef HM (cutOk_vh _ _ _ _ hv)
      · rw [hno] at ho; cases ho
      · exact hdef HM (cutOk_lev _ _ (Nat.le_trans (lev_cod _ _) hl'))
    cases M1 with
    | iomega C f =>
      obtain ⟨E, δ, hf, hδ⟩ := inv_omega HM1
      cases E
      exact .app _ _ _ _ _ (vsucc (vplus γ2 β1)) β2 _
        (.omega _ _ _ (fun n => vsucc (vplus γ2 (δ n))) _
          (fun n => IH (δ n) (lt_trans (hδ n) hb1) (f n) (hf n)) (fun n => sum_step γ2 (hδ n)))
        HK (sum_step γ2 hb1) (lt_sum_r' γ2 hb2) (cutOk_om _ _ _ rfl (.inr Hρ))
    | ivar _ => exact hdef' rfl
    | ilam _ _ => exact hdef' rfl
    | iapp _ _ _ _ => exact hdef' rfl
    | izero => exact hdef' rfl
    | isucc _ => exact hdef' rfl
  | izero => cases inv_zero HM
  | isucc K => cases (inv_succ HM).1
  | iomega C f =>
    obtain ⟨E, _⟩ := inv_omega HM
    cases E
    exact hdef HM (cutOk_om _ _ _ rfl (.inr Hρ))

/-! ## The reduction lemma for ω-redexes

At cut rank `0`, an ω-term applied to a normal argument of type `nat` reduces
to cut rank `0`, with height `h(Ω f) + h N + 1`; by transfinite induction on
the height of `N`. -/

/-- Rocq: `Analysis.SystemT.omega_red_typed`. -/
theorem omegaRed_typed (Γ : List Ty) (A B C : Ty) :
    ∀ (γ2 : VForm) (N : ITerm) (f : Nat → ITerm) (γ1 : VForm),
      D 0 Γ (iomega C f) (TAr A B) γ1 → D 0 Γ N A γ2 → D 0 Γ (omegaRed A B C f N) B (vsucc (vplus γ1 γ2)) := by
  intro γ2
  refine VF_ind (fun γ2 => ∀ N f γ1, D 0 Γ (iomega C f) (TAr A B) γ1 → D 0 Γ N A γ2 →
    D 0 Γ (omegaRed A B C f N) B (vsucc (vplus γ1 γ2))) (fun γ2 IH => ?_) γ2
  intro N f γ1 Hf HN
  obtain ⟨E, δ, hδ, hδlt⟩ := inv_omega Hf
  cases E
  have hdef : cutOk 0 TN B (iomega B f) N = true → D 0 Γ (iapp TN B (iomega B f) N) B (vsucc (vplus γ1 γ2)) :=
    fun hc => .app _ _ _ _ _ _ _ _ Hf HN (lt_sum_l _ _) (lt_sum_r _ _) hc
  cases N with
  | ivar x => exact hdef (cutOk_om _ _ _ rfl (.inl rfl))
  | ilam _ _ =>
    obtain ⟨_, _, E, _⟩ := inv_lam HN
    cases E
  | iapp A0 B0 N1 K =>
    obtain ⟨E0, β1, β2, HN1, HK, hb1, hb2, hc⟩ := inv_app HN
    subst E0
    have hlev : ¬ lev (TAr A0 TN) ≤ 0 := fun h => Nat.not_succ_le_zero 0 (Nat.le_trans (lev_pos _) h)
    have hdef' : isOm N1 = false → D 0 Γ (iapp TN B (iomega B f) (iapp A0 TN N1 K)) B (vsucc (vplus γ1 γ2)) := by
      intro hno
      rcases cutOk_cases hc with hv | ⟨ho, _⟩ | hl'
      · exact hdef (cutOk_om _ _ _ rfl (.inl hv))
      · rw [hno] at ho; cases ho
      · exact absurd hl' hlev
    cases N1 with
    | iomega E g =>
      obtain ⟨E', δ', hg, hδ'⟩ := inv_omega HN1
      cases E'
      have hvK : isvh K = true := by
        rcases cutOk_cases hc with hv | ⟨_, hv | hv⟩ | hl'
        · cases hv
        · exact hv
        · exact absurd hv (Nat.not_succ_le_zero 0)
        · exact absurd hl' hlev
      exact .app _ _ _ _ _ (vsucc (vplus γ1 β1)) β2 _
        (.omega _ _ _ (fun n => vsucc (vplus γ1 (δ' n))) _
          (fun n => IH (δ' n) (lt_trans (hδ' n) hb1) (g n) f γ1 Hf (hg n)) (fun n => sum_step γ1 (hδ' n)))
        HK (sum_step γ1 hb1) (lt_sum_r' γ1 hb2) (cutOk_om _ _ _ rfl (.inl hvK))
    | ivar _ => exact hdef' rfl
    | ilam _ _ => exact hdef' rfl
    | iapp _ _ _ _ => exact hdef' rfl
    | izero => exact hdef' rfl
    | isucc _ => exact hdef' rfl
  | izero => exact D_height (hδ 0) (le_of_lt (lt_trans (hδlt 0) (lt_sum_l _ _)))
  | isucc K =>
    obtain ⟨_, β, HK, hβ⟩ := inv_succ HN
    exact D_height (IH β hβ K (fun n => f (n + 1)) γ1 (.omega _ _ _ (fun n => δ (n + 1)) _ (fun n => hδ (n + 1))
      (fun n => hδlt (n + 1))) HK) (vsucc_mono (vplus_mono (le_refl _) (le_of_lt hβ)))
  | iomega E g =>
    obtain ⟨E', _⟩ := inv_omega HN
    cases E'

/-! ## One pass of cut elimination

A derivation of cut rank `ρ+1` and height `α` becomes one of cut rank `ρ` and
height `ω^α`. -/

theorem cutRed_app (A B : Ty) {M' : ITerm} (N' : ITerm) (h : isOm M' = false) :
    cutRed A B M' N' = appRed A B M' N' := by
  cases M' with
  | iomega _ _ => cases h
  | _ => rfl

/-- Rocq: `Analysis.SystemT.elim_typed`. -/
theorem elim_typed {ρ : Nat} {Γ : List Ty} {M : ITerm} {T : Ty} {α : VForm} (h : D (ρ + 1) Γ M T α) :
    D ρ Γ (elim ρ M) T (vexp α) ∧ (isvh M = true → isvh (elim ρ M) = true) ∧
      (isOm M = true → isOm (elim ρ M) = true) := by
  induction h with
  | var Γ x A α hx => exact ⟨.var _ _ _ _ hx, id, id⟩
  | lam Γ A M B β α _ hβ ih =>
    exact ⟨.lam _ _ _ _ _ _ ih.1 (vexp_increasing hβ), fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  | app Γ A B M N β1 β2 α _ _ hb1 hb2 hc ihM ihN =>
    obtain ⟨HM', HvM, HoM⟩ := ihM
    have HN' := ihN.1
    have hpos : sz Z < sz α := lt_of_le_of_lt (zero_least _) hb1
    show D ρ Γ (if cutOk ρ A B (elim ρ M) (elim ρ N) then _ else _) B _ ∧
      (isvh M = true → isvh (if cutOk ρ A B (elim ρ M) (elim ρ N) then _ else _) = true) ∧
      (false = true → _)
    generalize elim ρ M = M' at HM' HvM HoM ⊢
    generalize elim ρ N = N' at HN' ⊢
    cases hc' : cutOk ρ A B M' N' with
    | true =>
      exact ⟨.app _ _ _ _ _ _ _ _ HM' HN' (vexp_increasing hb1) (vexp_increasing hb2) hc',
        fun hv => HvM hv, fun h => Bool.noConfusion h⟩
    | false =>
      refine ⟨?_, fun hv => ?_, fun h => Bool.noConfusion h⟩
      · cases ho : isOm M' with
        | true =>
          cases ρ with
          | zero =>
            cases M' with
            | iomega C f =>
              exact D_height (omegaRed_typed Γ A B C (vexp β2) N' f (vexp β1) HM' HN')
                (le_of_lt (below_exp_sum (vexp_increasing hb1) (vexp_increasing hb2) hpos))
            | _ => cases ho
          | succ ρ =>
            rw [cutOk_om _ A B ho (.inr (Nat.succ_le_succ (Nat.zero_le ρ)))] at hc'
            cases hc'
        | false =>
          have Hl : lev (TAr A B) ≤ ρ + 1 := by
            rcases cutOk_cases hc with hv | ⟨ho', _⟩ | hl
            · rw [cutOk_vh _ A B N' (HvM hv)] at hc'; cases hc'
            · rw [HoM ho'] at ho; cases ho
            · exact hl
          rw [cutRed_app A B N' ho]
          exact D_height (appRed_typed HN' Hl _ _ HM')
            (le_of_lt (below_exp_sum (vexp_increasing hb2) (vexp_increasing hb1) hpos))
      · rw [cutOk_vh _ A B N' (HvM hv)] at hc'; cases hc'
  | zero => exact ⟨.zero _ _, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  | succ Γ M β α _ hβ ih =>
    exact ⟨.succ _ _ _ _ ih.1 (vexp_increasing hβ), fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  | omega Γ C f β α _ hβ ih =>
    exact ⟨.omega _ _ _ (fun n => vexp (β n)) _ (fun n => (ih n).1) (fun n => vexp_increasing (hβ n)),
      fun h => Bool.noConfusion h, fun _ => rfl⟩

/-- Iterating: cut rank `ρ` and height `α` give a normal derivation of height
`tower ρ α = ω^ω^...^α`. Rocq: `Analysis.SystemT.norm_typed`. -/
theorem norm_typed : ∀ (ρ : Nat) {Γ : List Ty} {M : ITerm} {T : Ty} {α : VForm},
    D ρ Γ M T α → D 0 Γ (norm ρ M) T (tower ρ α)
  | 0, _, _, _, _, h => h
  | ρ + 1, _, _, _, _, h => norm_typed ρ (elim_typed h).1

/-! ## Closed normal terms of type `nat` are numerals -/

/-- Rocq: `Analysis.SystemT.closed_head`. -/
theorem closed_head {ρ : Nat} {M : ITerm} {T : Ty} {α : VForm} (h : D ρ [] M T α) : headVar M = none := by
  have key : ∀ {Γ : List Ty} {M T α}, D ρ Γ M T α → Γ = [] → headVar M = none := by
    intro Γ M T α h
    induction h with
    | var Γ x A α hx => intro e; subst e; cases x <;> cases hx
    | app _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ => exact ih1
    | _ => intro _; rfl
  exact key h rfl

/-- Rocq: `Analysis.SystemT.canonical_nat`. -/
theorem canonical_nat {M : ITerm} {α : VForm} (h : D 0 [] M TN α) : ∃ k, M = inum k := by
  have key : ∀ {Γ : List Ty} {M T α}, D 0 Γ M T α → Γ = [] → T = TN → ∃ k, M = inum k := by
    intro Γ M T α h
    induction h with
    | var Γ x A α hx => intro e; subst e; cases x <;> cases hx
    | lam => intro _ e; cases e
    | app Γ A B M N β1 β2 α hM hN _ _ hc _ _ =>
      intro e _
      subst e
      have hvM : isvh M = false := by unfold isvh; rw [closed_head hM]
      have hvN : isvh N = false := by unfold isvh; rw [closed_head hN]
      rcases cutOk_cases hc with hv | ⟨_, hv | hv⟩ | hl
      · rw [hvM] at hv; cases hv
      · rw [hvN] at hv; cases hv
      · exact absurd hv (Nat.not_succ_le_zero 0)
      · exact absurd (Nat.le_trans (lev_pos _) hl) (Nat.not_succ_le_zero 0)
    | zero => intro _ _; exact ⟨0, rfl⟩
    | succ Γ M β α _ _ ih =>
      intro e _
      obtain ⟨k, hk⟩ := ih e rfl
      exact ⟨k + 1, by rw [hk]; rfl⟩
    | omega => intro _ e; cases e
  exact key h rfl rfl

/-! ## System T -/

/-- Rocq: `Analysis.SystemT.term`. The recursor `rec C z s t` is the constructor `recT`,
since `Term.rec` is the name of the recursor Lean generates. -/
inductive Term : Type where
  | var : Nat → Term
  | lam : Ty → Term → Term
  | app : Ty → Ty → Term → Term → Term
  | zero : Term
  | succ : Term → Term
  /-- `rec C z s t` -/
  | recT : Ty → Term → Term → Term → Term

open Term

/-- Rocq: `Analysis.SystemT.typing`. -/
inductive Typing : List Ty → Term → Ty → Prop where
  | var (Γ : List Ty) (x : Nat) (A : Ty) : List.nthError Γ x = some A → Typing Γ (var x) A
  | lam (Γ : List Ty) (A : Ty) (t : Term) (B : Ty) : Typing (A :: Γ) t B → Typing Γ (lam A t) (TAr A B)
  | app (Γ : List Ty) (A B : Ty) (t u : Term) : Typing Γ t (TAr A B) → Typing Γ u A → Typing Γ (app A B t u) B
  | zero (Γ : List Ty) : Typing Γ Term.zero TN
  | succ (Γ : List Ty) (t : Term) : Typing Γ t TN → Typing Γ (Term.succ t) TN
  | recT (Γ : List Ty) (C : Ty) (z s t : Term) : Typing Γ z C → Typing Γ s (TAr TN (TAr C C)) →
      Typing Γ t TN → Typing Γ (recT C z s t) C

/-- The `n`-th unfolding of the recursor: `s (n-1) (... (s 0 z))`. Rocq: `Analysis.SystemT.iter`. -/
def iter (C : Ty) (z s : ITerm) : Nat → ITerm
  | 0 => z
  | n + 1 => iapp C C (iapp TN (TAr C C) s (inum n)) (iter C z s n)

/-- Rocq: `Analysis.SystemT.tr`. -/
def tr : Term → ITerm
  | var x => ivar x
  | lam A t => ilam A (tr t)
  | app A B t u => iapp A B (tr t) (tr u)
  | Term.zero => izero
  | Term.succ t => isucc (tr t)
  | recT C z s t => iapp TN C (iomega C (iter C (tr z) (tr s))) (tr t)

/-- Rocq: `Analysis.SystemT.vnat`. -/
def vnat : Nat → VForm
  | 0 => Z
  | n + 1 => vsucc (vnat n)

/-- A finite exponent with `h t < ω^(hexp t)` (`h_below`). Rocq: `Analysis.SystemT.hexp`. -/
def hexp : Term → Nat
  | var _ => 1
  | Term.zero => 1
  | lam _ t => hexp t
  | Term.succ t => hexp t
  | app _ _ t u => Nat.max (hexp t) (hexp u)
  | recT _ z s t => Nat.max (Nat.max (hexp z) (hexp s) + 1) (hexp t) + 1

/-- The height of the translation. Rocq: `Analysis.SystemT.h`. -/
def h : Term → VForm
  | var _ => Z
  | lam _ t => vsucc (h t)
  | app _ _ t u => vsucc (vplus (h t) (h u))
  | Term.zero => Z
  | Term.succ t => vsucc (h t)
  | recT _ z s t => vsucc (vplus (vexp (vnat (Nat.max (hexp z) (hexp s) + 1))) (h t))

/-- The cut rank of the translation. Rocq: `Analysis.SystemT.tlev`. -/
def tlev : Term → Nat
  | var _ => 1
  | Term.zero => 1
  | lam _ t => tlev t
  | Term.succ t => tlev t
  | app A B t u => Nat.max (lev (TAr A B)) (Nat.max (tlev t) (tlev u))
  | recT C z s t => Nat.max (lev (TAr TN (TAr C C))) (Nat.max (tlev z) (Nat.max (tlev s) (tlev t)))

/-- The ordinal of a term: the height of its normal form. Rocq: `Analysis.SystemT.ord_of`. -/
def ordOf (t : Term) : VForm := tower (tlev t) (h t)

/-- Rocq: `Analysis.SystemT.ib`. -/
def ib (hz hs : VForm) : Nat → VForm
  | 0 => hz
  | n + 1 => vsucc (vplus (ib hz hs n) (vplus hs (vnat (n + 1))))

/-- Rocq: `Analysis.SystemT.inum_typed`. -/
theorem inum_typed (ρ : Nat) (Γ : List Ty) : ∀ n, D ρ Γ (inum n) TN (vnat n)
  | 0 => .zero _ _
  | n + 1 => .succ _ _ _ _ (inum_typed ρ Γ n) (vsucc_lt _)

/-- Rocq: `Analysis.SystemT.iter_typed`. -/
theorem iter_typed {ρ : Nat} {Γ : List Ty} {C : Ty} {z s : ITerm} {hz hs : VForm} (Hz : D ρ Γ z C hz)
    (Hs : D ρ Γ s (TAr TN (TAr C C)) hs) (Hl : lev (TAr TN (TAr C C)) ≤ ρ) :
    ∀ n, D ρ Γ (iter C z s n) C (ib hz hs n)
  | 0 => Hz
  | n + 1 =>
    .app _ _ _ _ _ (vplus hs (vnat (n + 1))) (ib hz hs n) _
      (.app _ _ _ _ _ hs (vnat n) _ Hs (inum_typed ρ Γ n)
        (lt_of_le_of_lt (add_zero _).ge (lt_of_lt_of_le (add_lt_add_left _
          (lt_of_le_of_lt (zero_least _) (vsucc_lt (vnat n)))) (vplus_eq _ _).ge))
        (lt_of_lt_of_le (vsucc_lt _) (vplus_le2 _ _)) (cutOk_lev _ _ Hl))
      (iter_typed Hz Hs Hl n) (lt_sum_r _ _) (lt_sum_l _ _)
      (cutOk_lev _ _ (Nat.le_trans (lev_cod _ _) Hl))

/-- Rocq: `Analysis.SystemT.vnat_eq`. -/
theorem vnat_eq : ∀ n, sz (vnat n) ≈ ofNat n
  | 0 => equiv_refl _
  | n + 1 => equiv_trans (vsucc_eq _) (succ_congruence (vnat_eq n))

/-- Rocq: `Analysis.SystemT.vnat_lt`. -/
theorem vnat_lt {m n : Nat} (h : m < n) : sz (vnat m) < sz (vnat n) :=
  lt_of_le_of_lt (vnat_eq m).le (lt_of_lt_of_le (ofNat_increasing h) (vnat_eq n).ge)

/-- Rocq: `Analysis.SystemT.vnat_le`. -/
theorem vnat_le {m n : Nat} (h : m ≤ n) : sz (vnat m) ≤ sz (vnat n) :=
  le_trans (vnat_eq m).le (le_trans (ofNat_monotone h) (vnat_eq n).ge)

/-- Rocq: `Analysis.SystemT.vexp_mono`. -/
theorem vexp_mono {a b : VForm} (h : sz a ≤ sz b) : sz (vexp a) ≤ sz (vexp b) :=
  le_trans (vexp_eq a).le (le_trans (pow_le_pow_right ω h) (vexp_eq b).ge)

/-- Rocq: `Analysis.SystemT.Z_lt_vnat`. -/
theorem Z_lt_vnat {n : Nat} (h : 1 ≤ n) : sz Z < sz (vnat n) := vnat_lt (m := 0) h

/-- Rocq: `Analysis.SystemT.vnat_below`. -/
theorem vnat_below (K : VForm) (hK : sz Z < sz K) : ∀ n, sz (vnat n) < sz (vexp K)
  | 0 => lt_of_lt_of_le (pow_pos ω _) (vexp_eq K).ge
  | n + 1 =>
    lt_of_le_of_lt (vplus_eq _ _).le (lt_of_lt_of_le
      (below_exp_add K (lt_of_lt_of_le (vnat_below K hK n) (vexp_eq K).le)
        (lt_of_le_of_lt (vexp_eq Z).le (pow_lt_pow_right omega_gt1 hK)))
      (vexp_eq K).ge)

/-- The branches of the ω-term for a recursor are below `ω^K`, as soon as
`h z` and `h s` are. Rocq: `Analysis.SystemT.ib_below`. -/
theorem ib_below {hz hs K : VForm} (Hz : sz hz < sz (vexp K)) (Hs : sz hs < sz (vexp K)) (Hpos : sz Z < sz K) :
    ∀ n, sz (ib hz hs n) < sz (vexp K)
  | 0 => Hz
  | n + 1 =>
    below_exp_sum (ib_below Hz Hs Hpos n)
      (lt_of_le_of_lt (vplus_eq _ _).le (lt_of_lt_of_le
        (below_exp_add K (lt_of_lt_of_le Hs (vexp_eq K).le)
          (lt_of_lt_of_le (vnat_below K Hpos _) (vexp_eq K).le)) (vexp_eq K).ge))
      Hpos

/-- Rocq: `Analysis.SystemT.hexp_pos`. -/
theorem hexp_pos : ∀ t : Term, 1 ≤ hexp t
  | var _ => Nat.le_refl 1
  | Term.zero => Nat.le_refl 1
  | lam _ t => hexp_pos t
  | Term.succ t => hexp_pos t
  | app _ _ t _ => Nat.le_trans (hexp_pos t) (Nat.le_max_left _ _)
  | recT _ _ _ _ => Nat.succ_le_succ (Nat.zero_le _)

/-- Rocq: `Analysis.SystemT.below_vexp_vnat`. -/
theorem below_vexp_vnat {a : VForm} {m n : Nat} (h : sz a < sz (vexp (vnat m))) (hmn : m ≤ n) :
    sz a < sz (vexp (vnat n)) :=
  lt_of_lt_of_le h (vexp_mono (vnat_le hmn))

theorem vsucc_below {a K : VForm} (ha : sz a < sz (vexp K)) (hK : sz Z < sz K) : sz (vsucc a) < sz (vexp K) :=
  lt_of_le_of_lt (vsucc_mono (vplus_le1 a Z)) (below_exp_sum ha (lt_of_lt_of_le (pow_pos ω _) (vexp_eq K).ge) hK)

/-- Rocq: `Analysis.SystemT.h_below`. -/
theorem h_below : ∀ t : Term, sz (h t) < sz (vexp (vnat (hexp t)))
  | var _ => lt_of_lt_of_le (pow_pos ω _) (vexp_eq _).ge
  | Term.zero => lt_of_lt_of_le (pow_pos ω _) (vexp_eq _).ge
  | lam _ t => vsucc_below (h_below t) (Z_lt_vnat (hexp_pos t))
  | Term.succ t => vsucc_below (h_below t) (Z_lt_vnat (hexp_pos t))
  | app _ _ t u =>
    below_exp_sum (below_vexp_vnat (h_below t) (Nat.le_max_left _ _))
      (below_vexp_vnat (h_below u) (Nat.le_max_right _ _))
      (Z_lt_vnat (Nat.le_trans (hexp_pos t) (Nat.le_max_left _ _)))
  | recT _ _ _ t =>
    below_exp_sum (vexp_increasing (vnat_lt (Nat.lt_succ_of_le (Nat.le_max_left _ _))))
      (below_vexp_vnat (h_below t) (Nat.le_succ_of_le (Nat.le_max_right _ _)))
      (Z_lt_vnat (Nat.succ_le_succ (Nat.zero_le _)))

/-- `ω` as a V form. Rocq: `Analysis.SystemT.vω`. -/
def vω : VForm := vexp (vnat 1)

/-- Rocq: `Analysis.SystemT.vω_eq`. -/
theorem vω_eq : sz vω ≈ ω :=
  equiv_trans (vexp_eq _) (equiv_trans (pow_congr (equiv_refl ω) (vnat_eq 1)) (pow_one' omega_gt0))

/-- The heights of translations are below `ω^ω`. Rocq: `Analysis.SystemT.h_below_ω_ω`. -/
theorem h_below_ω_ω (t : Term) : sz (h t) < sz (vexp vω) :=
  lt_of_lt_of_le (h_below t)
    (vexp_mono (le_of_lt (lt_of_le_of_lt (vnat_eq _).le (lt_of_lt_of_le (index_lt ω ⟨hexp t⟩) vω_eq.ge))))

/-- Rocq: `Analysis.SystemT.tower_increasing`. -/
theorem tower_increasing : ∀ (k : Nat) {a b : VForm}, sz a < sz b → sz (tower k a) < sz (tower k b)
  | 0, _, _, h => h
  | k + 1, _, _, h => tower_increasing k (vexp_increasing h)

/-- Rocq: `Analysis.SystemT.tlev_pos`. -/
theorem tlev_pos : ∀ t : Term, 1 ≤ tlev t
  | var _ => Nat.le_refl 1
  | Term.zero => Nat.le_refl 1
  | lam _ t => tlev_pos t
  | Term.succ t => tlev_pos t
  | app A B _ _ => Nat.le_trans (lev_pos (TAr A B)) (Nat.le_max_left _ _)
  | recT C _ _ _ => Nat.le_trans (lev_pos (TAr TN (TAr C C))) (Nat.le_max_left _ _)

/-- The translation of a term `t` has cut rank `tlev t` and height `h t`.
Rocq: `Analysis.SystemT.tr_typed`. -/
theorem tr_typed {Γ : List Ty} {t : Term} {A : Ty} (H : Typing Γ t A) : D (tlev t) Γ (tr t) A (h t) := by
  induction H with
  | var Γ x A hx => exact .var _ _ _ _ hx
  | lam Γ A t B _ ih => exact .lam _ _ _ _ _ _ ih (vsucc_lt _)
  | app Γ A B t u _ _ iht ihu =>
    exact .app _ _ _ _ _ (h t) (h u) _
      (D_mono iht (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (le_refl _))
      (D_mono ihu (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (le_refl _))
      (lt_sum_l _ _) (lt_sum_r _ _) (cutOk_lev _ _ (Nat.le_max_left _ _))
  | zero => exact .zero _ _
  | succ Γ t _ ih => exact .succ _ _ _ _ ih (vsucc_lt _)
  | recT Γ C z s t _ _ _ ihz ihs iht =>
    have Hl : lev (TAr TN (TAr C C)) ≤ tlev (recT C z s t) := Nat.le_max_left _ _
    have Hz' : tlev z ≤ tlev (recT C z s t) := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have Hs' : tlev s ≤ tlev (recT C z s t) :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    have Ht' : tlev t ≤ tlev (recT C z s t) :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    have hm : 1 ≤ Nat.max (hexp z) (hexp s) + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact .app _ _ _ _ _ (vexp (vnat (Nat.max (hexp z) (hexp s) + 1))) (h t) _
      (.omega _ _ _ (ib (h z) (h s)) _
        (iter_typed (D_mono ihz Hz' (le_refl _)) (D_mono ihs Hs' (le_refl _)) Hl)
        (ib_below (below_vexp_vnat (h_below z) (Nat.le_succ_of_le (Nat.le_max_left _ _)))
          (below_vexp_vnat (h_below s) (Nat.le_succ_of_le (Nat.le_max_right _ _))) (Z_lt_vnat hm)))
      (D_mono iht Ht' (le_refl _)) (lt_sum_l _ _) (lt_sum_r _ _)
      (cutOk_om _ _ _ rfl (.inr (Nat.le_trans (lev_pos _) Hl)))

/-! ## The ordinal analysis -/

/-- Rocq: `Analysis.SystemT.T_normalization`. -/
theorem T_normalization {Γ : List Ty} {t : Term} {A : Ty} (H : Typing Γ t A) :
    D 0 Γ (norm (tlev t) (tr t)) A (ordOf t) ∧ Red (tr t) (norm (tlev t) (tr t)) :=
  ⟨norm_typed _ (tr_typed H), norm_red _ _⟩

/-- Rocq: `Analysis.SystemT.ord_of_bound`. -/
theorem ordOf_bound (t : Term) : sz (ordOf t) < sz (tower (tlev t + 1) vω) :=
  tower_increasing _ (h_below_ω_ω t)

/-- Rocq: `Analysis.SystemT.ord_of_below_ε0`. -/
theorem ordOf_below_ε0 (t : Term) : sz (ordOf t) < ε 0 := below_ε₀ _

/-- Every closed term of type `nat` reduces to a numeral. Rocq: `Analysis.SystemT.T_total`. -/
theorem T_total {t : Term} (H : Typing [] t TN) :
    ∃ k, norm (tlev t) (tr t) = inum k ∧ Red (tr t) (inum k) := by
  obtain ⟨Hn, Hr⟩ := T_normalization H
  obtain ⟨k, hk⟩ := canonical_nat Hn
  exact ⟨k, hk, hk ▸ Hr⟩

/-- Doubling by recursion: `rec 0 (λ_ y. S (S y)) 3` normalizes to `6` in
`tlev = 2` passes. Rocq example `double_three`. -/
theorem double_three :
    norm (tlev (recT TN Term.zero (lam TN (lam TN (Term.succ (Term.succ (var 0))))) (Term.succ (Term.succ (Term.succ Term.zero)))))
      (tr (recT TN Term.zero (lam TN (lam TN (Term.succ (Term.succ (var 0))))) (Term.succ (Term.succ (Term.succ Term.zero))))) = inum 6 := rfl

end ConstructiveOrdinals.SystemT
