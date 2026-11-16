import ConstructiveOrdinals.Analysis.PeanoArith
import ConstructiveOrdinals.Analysis.Hardy

/-!
# An ω-logic for arithmetic, with bounding by the Hardy functions

Port of `Ordinal/Analysis/OmegaLogic.v`.

Sequents are lists of signed formulas of `PeanoArith`: `(true, A)` asserts
`A` and `(false, A)` its negation. The rules are those of Tait's one-sided
calculus with the ω-rule, but every derivation carries a control `n`, and
heights are V forms related by `β ≺_n α` (`Hardy.Olt`): the ω-rule has its
`i`-th premise at control `max n (i+1)`, an existential witness must be below
the control, and the control may be raised from `n` to `m ≤ H_γ(n)` at the
cost of adding `γ` to the height (`OD.up`).

Bounded formulas (the class `DP`) are decided by evaluation; a true one is an
axiom, and the ω-rule never applies to one. Cut elimination costs one
exponential `α ↦ ω^α` per cut rank (`od_elim`), and a derivation of a Σ₁
sequent without cuts of positive rank, at height `α` and control `n`, has
witnesses below `H_α(n)` (`od_bounding`).

Lean notes:

- Rocq's `isD` and `deval` match nested patterns with a wildcard; here the
  nested patterns are recognised by auxiliary functions that spell out every
  constructor (`isGuard`, `isDEx`, …), and `isD`/`deval` recurse mutually
  with `isDAll`/`devalAll`.
- `sform` is `SForm`, `kind` is `Kind`; the constructors of `OD` are
  `OD.ax`, `OD.conj`, …, `OD.up`.
- Rocq rewrites with `↔` lemmas; here they are applied with `.1`/`.2`.
-/

namespace ConstructiveOrdinals.OmegaLogic

open PeanoArith ATerm Form Hardy VNotation VForm

/-! ## Boolean and arithmetic helpers -/

theorem and_true_split : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩

theorem or_true_split : ∀ {a b : Bool}, (a || b) = true → a = true ∨ b = true
  | true, _, _ => .inl rfl
  | false, true, _ => .inr rfl

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

theorem max_le' {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : Nat.max a b ≤ c := by
  show (if a ≤ b then b else a) ≤ c
  by_cases h : a ≤ b
  · rw [ite_eq_left h]; exact hb
  · rw [ite_eq_right h]; exact ha

theorem max_mono {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') : Nat.max a b ≤ Nat.max a' b' :=
  max_le' (Nat.le_trans ha (Nat.le_max_left _ _)) (Nat.le_trans hb (Nat.le_max_right _ _))

/-! ## Semantics -/

/-- Rocq: `Analysis.OmegaLogic.teval`. -/
def teval (ρ : Nat → Nat) : ATerm → Nat
  | tv i => ρ i
  | tz => 0
  | ts t => teval ρ t + 1
  | tplus s t => teval ρ s + teval ρ t
  | tmult s t => teval ρ s * teval ρ t

/-- Rocq: `Analysis.OmegaLogic.scons`. -/
def scons (x : Nat) (ρ : Nat → Nat) : Nat → Nat
  | 0 => x
  | i + 1 => ρ i

/-- Rocq: `Analysis.OmegaLogic.sat`. -/
def sat : (Nat → Nat) → Form → Prop
  | ρ, eq s t => teval ρ s = teval ρ t
  | _, bot => False
  | ρ, conj A B => sat ρ A ∧ sat ρ B
  | ρ, disj A B => sat ρ A ∨ sat ρ B
  | ρ, imp A B => sat ρ A → sat ρ B
  | ρ, all A => ∀ x, sat (scons x ρ) A
  | ρ, ex A => ∃ x, sat (scons x ρ) A

/-- Rocq: `Analysis.OmegaLogic.num`. -/
def num : Nat → ATerm
  | 0 => tz
  | n + 1 => ts (num n)

/-- Rocq: `Analysis.OmegaLogic.teval_num`. -/
theorem teval_num (ρ : Nat → Nat) : ∀ n, teval ρ (num n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (teval_num ρ n)

/-- Rocq: `Analysis.OmegaLogic.teval_ext`. -/
theorem teval_ext {ρ ρ' : Nat → Nat} (h : ∀ i, ρ i = ρ' i) : ∀ t, teval ρ t = teval ρ' t
  | tv i => h i
  | tz => rfl
  | ts t => congrArg (· + 1) (teval_ext h t)
  | tplus s t => congrArg₂ (· + ·) (teval_ext h s) (teval_ext h t)
  | tmult s t => congrArg₂ (· * ·) (teval_ext h s) (teval_ext h t)

theorem scons_ext {ρ ρ' : Nat → Nat} (h : ∀ i, ρ i = ρ' i) (x : Nat) : ∀ i, scons x ρ i = scons x ρ' i
  | 0 => rfl
  | i + 1 => h i

/-- Rocq: `Analysis.OmegaLogic.sat_ext`. -/
theorem sat_ext : ∀ (A : Form) {ρ ρ' : Nat → Nat}, (∀ i, ρ i = ρ' i) → (sat ρ A ↔ sat ρ' A)
  | eq s t, _, _, h => by
    show teval _ s = teval _ t ↔ teval _ s = teval _ t
    rw [teval_ext h s, teval_ext h t]
  | bot, _, _, _ => Iff.rfl
  | conj A B, _, _, h => ⟨fun ⟨a, b⟩ => ⟨(sat_ext A h).1 a, (sat_ext B h).1 b⟩,
      fun ⟨a, b⟩ => ⟨(sat_ext A h).2 a, (sat_ext B h).2 b⟩⟩
  | disj A B, _, _, h => ⟨fun hab => hab.elim (fun a => .inl ((sat_ext A h).1 a)) (fun b => .inr ((sat_ext B h).1 b)),
      fun hab => hab.elim (fun a => .inl ((sat_ext A h).2 a)) (fun b => .inr ((sat_ext B h).2 b))⟩
  | imp A B, _, _, h => ⟨fun f a => (sat_ext B h).1 (f ((sat_ext A h).2 a)),
      fun f a => (sat_ext B h).2 (f ((sat_ext A h).1 a))⟩
  | all A, _, _, h => ⟨fun f x => (sat_ext A (scons_ext h x)).1 (f x),
      fun f x => (sat_ext A (scons_ext h x)).2 (f x)⟩
  | ex A, _, _, h => ⟨fun ⟨x, hx⟩ => ⟨x, (sat_ext A (scons_ext h x)).1 hx⟩,
      fun ⟨x, hx⟩ => ⟨x, (sat_ext A (scons_ext h x)).2 hx⟩⟩

/-- Rocq: `Analysis.OmegaLogic.teval_asubst`. -/
theorem teval_asubst (ρ : Nat → Nat) (σ : Nat → ATerm) :
    ∀ t, teval ρ (asubst σ t) = teval (fun i => teval ρ (σ i)) t
  | tv _ => rfl
  | tz => rfl
  | ts t => congrArg (· + 1) (teval_asubst ρ σ t)
  | tplus s t => congrArg₂ (· + ·) (teval_asubst ρ σ s) (teval_asubst ρ σ t)
  | tmult s t => congrArg₂ (· * ·) (teval_asubst ρ σ s) (teval_asubst ρ σ t)

/-- Rocq: `Analysis.OmegaLogic.teval_shift`. -/
theorem teval_shift (x : Nat) (ρ : Nat → Nat) (t : ATerm) :
    teval (scons x ρ) (asubst shiftSub t) = teval ρ t :=
  (teval_asubst _ _ t).trans (teval_ext (fun _ => rfl) t)

theorem up_env (ρ : Nat → Nat) (σ : Nat → ATerm) (x : Nat) :
    ∀ i, teval (scons x ρ) (up σ i) = scons x (fun i => teval ρ (σ i)) i
  | 0 => rfl
  | i + 1 => teval_shift x ρ (σ i)

/-- Rocq: `Analysis.OmegaLogic.sat_fsubst`. -/
theorem sat_fsubst : ∀ (A : Form) (ρ : Nat → Nat) (σ : Nat → ATerm),
    sat ρ (fsubst σ A) ↔ sat (fun i => teval ρ (σ i)) A
  | eq s t, ρ, σ => by
    show teval ρ (asubst σ s) = teval ρ (asubst σ t) ↔ _
    rw [teval_asubst, teval_asubst]; exact Iff.rfl
  | bot, _, _ => Iff.rfl
  | conj A B, ρ, σ => ⟨fun ⟨a, b⟩ => ⟨(sat_fsubst A ρ σ).1 a, (sat_fsubst B ρ σ).1 b⟩,
      fun ⟨a, b⟩ => ⟨(sat_fsubst A ρ σ).2 a, (sat_fsubst B ρ σ).2 b⟩⟩
  | disj A B, ρ, σ =>
    ⟨fun hab => hab.elim (fun a => .inl ((sat_fsubst A ρ σ).1 a)) (fun b => .inr ((sat_fsubst B ρ σ).1 b)),
     fun hab => hab.elim (fun a => .inl ((sat_fsubst A ρ σ).2 a)) (fun b => .inr ((sat_fsubst B ρ σ).2 b))⟩
  | imp A B, ρ, σ => ⟨fun f a => (sat_fsubst B ρ σ).1 (f ((sat_fsubst A ρ σ).2 a)),
      fun f a => (sat_fsubst B ρ σ).2 (f ((sat_fsubst A ρ σ).1 a))⟩
  | all A, ρ, σ =>
    ⟨fun f x => (sat_ext A (up_env ρ σ x)).1 ((sat_fsubst A (scons x ρ) (up σ)).1 (f x)),
     fun f x => (sat_fsubst A (scons x ρ) (up σ)).2 ((sat_ext A (up_env ρ σ x)).2 (f x))⟩
  | ex A, ρ, σ =>
    ⟨fun ⟨x, hx⟩ => ⟨x, (sat_ext A (up_env ρ σ x)).1 ((sat_fsubst A (scons x ρ) (up σ)).1 hx)⟩,
     fun ⟨x, hx⟩ => ⟨x, (sat_fsubst A (scons x ρ) (up σ)).2 ((sat_ext A (up_env ρ σ x)).2 hx)⟩⟩

theorem inst1_env (ρ : Nat → Nat) (t : ATerm) : ∀ i, teval ρ (inst1 t i) = scons (teval ρ t) ρ i
  | 0 => rfl
  | _ + 1 => rfl

/-- Rocq: `Analysis.OmegaLogic.sat_sub1`. -/
theorem sat_sub1 (ρ : Nat → Nat) (A : Form) (t : ATerm) : sat ρ (sub1 A t) ↔ sat (scons (teval ρ t) ρ) A :=
  (sat_fsubst A ρ (inst1 t)).trans (sat_ext A (inst1_env ρ t))

/-- Rocq: `Analysis.OmegaLogic.sat_sub1_num`. -/
theorem sat_sub1_num (ρ : Nat → Nat) (A : Form) (i : Nat) : sat ρ (sub1 A (num i)) ↔ sat (scons i ρ) A := by
  have h := sat_sub1 ρ A (num i)
  rw [teval_num] at h
  exact h

/-- Closed formulas are evaluated with all variables `0`. Rocq: `Analysis.OmegaLogic.ρ0`. -/
def ρ0 : Nat → Nat := fun _ => 0

/-! ## Bounded formulas -/

/-- Rocq: `Analysis.OmegaLogic.occ`. -/
def occ (k : Nat) : ATerm → Bool
  | tv i => Nat.beq i k
  | tz => false
  | ts t => occ k t
  | tplus s t => occ k s || occ k t
  | tmult s t => occ k s || occ k t

/-- `∀z ≤ v. B` is `∀z. (∃d. z + d = v) → B`, and `∃d. u + d = v` states
`u ≤ v`. Rocq: `Analysis.OmegaLogic.DP`. -/
inductive DP : Form → Prop
  /-- Rocq: `DP_eq`. -/
  | eq (s t : ATerm) : DP (eq s t)
  /-- Rocq: `DP_bot`. -/
  | bot : DP bot
  /-- Rocq: `DP_and`. -/
  | conj (A B : Form) : DP A → DP B → DP (conj A B)
  /-- Rocq: `DP_or`. -/
  | disj (A B : Form) : DP A → DP B → DP (disj A B)
  /-- Rocq: `DP_imp`. -/
  | imp (A B : Form) : DP A → DP B → DP (imp A B)
  /-- Rocq: `DP_ball`. -/
  | ball (v : ATerm) (B : Form) : occ 0 v = false → occ 1 v = false → DP B →
      DP (all (imp (ex (.eq (tplus (tv 1) (tv 0)) v)) B))
  /-- Rocq: `DP_bex`. -/
  | bex (u v : ATerm) : occ 0 u = false → occ 0 v = false → DP (ex (.eq (tplus u (tv 0)) v))

/-- Is the term the variable `k`? -/
def isTv (k : Nat) : ATerm → Bool
  | tv i => Nat.beq i k
  | tz => false
  | ts _ => false
  | tplus _ _ => false
  | tmult _ _ => false

/-- Is the term `tv 1 + tv 0`? -/
def isT10 : ATerm → Bool
  | tv _ => false
  | tz => false
  | ts _ => false
  | tplus a b => isTv 1 a && isTv 0 b
  | tmult _ _ => false

/-- The shape `∃d. z + d = v` of the guard of a bounded universal. -/
def guardShape : Form → Bool
  | ex (.eq w _) => isT10 w
  | ex bot => false
  | ex (conj _ _) => false
  | ex (disj _ _) => false
  | ex (imp _ _) => false
  | ex (all _) => false
  | ex (ex _) => false
  | .eq _ _ => false
  | bot => false
  | conj _ _ => false
  | disj _ _ => false
  | imp _ _ => false
  | all _ => false

/-- The bound `v` of a guard `∃d. z + d = v`. -/
def guardBound : Form → ATerm
  | ex (.eq _ v) => v
  | ex bot => tz
  | ex (conj _ _) => tz
  | ex (disj _ _) => tz
  | ex (imp _ _) => tz
  | ex (all _) => tz
  | ex (ex _) => tz
  | .eq _ _ => tz
  | bot => tz
  | conj _ _ => tz
  | disj _ _ => tz
  | imp _ _ => tz
  | all _ => tz

/-- A guard whose bound mentions neither `z` nor `d`. -/
def isGuard (G : Form) : Bool := guardShape G && !occ 0 (guardBound G) && !occ 1 (guardBound G)

/-- The body `u + d = v` of a bounded existential. -/
def bexShape : Form → Bool
  | .eq (tplus _ b) _ => isTv 0 b
  | .eq (tv _) _ => false
  | .eq tz _ => false
  | .eq (ts _) _ => false
  | .eq (tmult _ _) _ => false
  | bot => false
  | conj _ _ => false
  | disj _ _ => false
  | imp _ _ => false
  | all _ => false
  | ex _ => false

/-- The terms `u` and `v` of `u + d = v`. -/
def bexU : Form → ATerm
  | .eq (tplus u _) _ => u
  | .eq (tv _) _ => tz
  | .eq tz _ => tz
  | .eq (ts _) _ => tz
  | .eq (tmult _ _) _ => tz
  | bot => tz
  | conj _ _ => tz
  | disj _ _ => tz
  | imp _ _ => tz
  | all _ => tz
  | ex _ => tz

def bexV : Form → ATerm
  | .eq _ v => v
  | bot => tz
  | conj _ _ => tz
  | disj _ _ => tz
  | imp _ _ => tz
  | all _ => tz
  | ex _ => tz

/-- The body of a bounded existential, with the side conditions. -/
def isDEx (A : Form) : Bool := bexShape A && !occ 0 (bexU A) && !occ 0 (bexV A)

mutual
/-- Rocq: `Analysis.OmegaLogic.isD`. -/
def isD : Form → Bool
  | .eq _ _ => true
  | bot => true
  | conj A B => isD A && isD B
  | disj A B => isD A && isD B
  | imp A B => isD A && isD B
  | all A => isDAll A
  | ex A => isDEx A
/-- The body of a bounded universal. -/
def isDAll : Form → Bool
  | .eq _ _ => false
  | bot => false
  | conj _ _ => false
  | disj _ _ => false
  | imp G B => isGuard G && isD B
  | all _ => false
  | ex _ => false
end

theorem isTv_eq : ∀ {k : Nat} {t : ATerm}, isTv k t = true → t = tv k
  | _, tv i, h => by rw [Nat.eq_of_beq_eq_true h]
  | _, tz, h => Bool.noConfusion h
  | _, ts _, h => Bool.noConfusion h
  | _, tplus _ _, h => Bool.noConfusion h
  | _, tmult _ _, h => Bool.noConfusion h

theorem isT10_eq : ∀ {w : ATerm}, isT10 w = true → w = tplus (tv 1) (tv 0)
  | tv _, h => Bool.noConfusion h
  | tz, h => Bool.noConfusion h
  | ts _, h => Bool.noConfusion h
  | tplus a b, h => by
    obtain ⟨ha, hb⟩ := and_true_split h
    rw [isTv_eq ha, isTv_eq hb]
  | tmult _ _, h => Bool.noConfusion h

theorem guard_eq : ∀ {G : Form}, guardShape G = true → G = ex (.eq (tplus (tv 1) (tv 0)) (guardBound G))
  | ex (.eq w v), h => by rw [isT10_eq h]; rfl
  | ex bot, h => Bool.noConfusion h
  | ex (conj _ _), h => Bool.noConfusion h
  | ex (disj _ _), h => Bool.noConfusion h
  | ex (imp _ _), h => Bool.noConfusion h
  | ex (all _), h => Bool.noConfusion h
  | ex (ex _), h => Bool.noConfusion h
  | .eq _ _, h => Bool.noConfusion h
  | bot, h => Bool.noConfusion h
  | conj _ _, h => Bool.noConfusion h
  | disj _ _, h => Bool.noConfusion h
  | imp _ _, h => Bool.noConfusion h
  | all _, h => Bool.noConfusion h

theorem bex_eq : ∀ {A : Form}, bexShape A = true → A = .eq (tplus (bexU A) (tv 0)) (bexV A)
  | .eq (tplus _ b) _, h => by rw [isTv_eq h]; rfl
  | .eq (tv _) _, h => Bool.noConfusion h
  | .eq tz _, h => Bool.noConfusion h
  | .eq (ts _) _, h => Bool.noConfusion h
  | .eq (tmult _ _) _, h => Bool.noConfusion h
  | bot, h => Bool.noConfusion h
  | conj _ _, h => Bool.noConfusion h
  | disj _ _, h => Bool.noConfusion h
  | imp _ _, h => Bool.noConfusion h
  | all _, h => Bool.noConfusion h
  | ex _, h => Bool.noConfusion h

theorem not_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · exact Bool.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.DP_isD`. -/
theorem DP_isD {A : Form} (h : DP A) : isD A = true := by
  induction h with
  | eq => rfl
  | bot => rfl
  | conj _ _ _ _ ih1 ih2 => show (isD _ && isD _) = true; rw [ih1, ih2]; rfl
  | disj _ _ _ _ ih1 ih2 => show (isD _ && isD _) = true; rw [ih1, ih2]; rfl
  | imp _ _ _ _ ih1 ih2 => show (isD _ && isD _) = true; rw [ih1, ih2]; rfl
  | ball v B h0 h1 _ ih =>
    show ((true && !occ 0 v && !occ 1 v) && isD B) = true
    rw [h0, h1, ih]; rfl
  | bex u v h0 h1 =>
    show (isTv 0 (tv 0) && !occ 0 u && !occ 0 v) = true
    rw [h0, h1]; rfl

mutual
/-- Rocq: `Analysis.OmegaLogic.isD_DP`. -/
theorem isD_DP : ∀ {A : Form}, isD A = true → DP A
  | .eq _ _, _ => .eq _ _
  | bot, _ => .bot
  | conj _ _, h => let ⟨h1, h2⟩ := and_true_split h; .conj _ _ (isD_DP h1) (isD_DP h2)
  | disj _ _, h => let ⟨h1, h2⟩ := and_true_split h; .disj _ _ (isD_DP h1) (isD_DP h2)
  | imp _ _, h => let ⟨h1, h2⟩ := and_true_split h; .imp _ _ (isD_DP h1) (isD_DP h2)
  | all A, h => isDAll_DP h
  | ex A, h => by
    obtain ⟨h12, h3⟩ := and_true_split h
    obtain ⟨h1, h2⟩ := and_true_split h12
    rw [bex_eq h1]
    exact .bex _ _ (not_true h2) (not_true h3)
theorem isDAll_DP : ∀ {A : Form}, isDAll A = true → DP (all A)
  | .eq _ _, h => Bool.noConfusion h
  | bot, h => Bool.noConfusion h
  | conj _ _, h => Bool.noConfusion h
  | disj _ _, h => Bool.noConfusion h
  | imp G B, h => by
    obtain ⟨hg, hb⟩ := and_true_split h
    obtain ⟨hg12, hg3⟩ := and_true_split hg
    obtain ⟨hg1, hg2⟩ := and_true_split hg12
    rw [guard_eq hg1]
    exact .ball _ _ (not_true hg2) (not_true hg3) (isD_DP hb)
  | all _, h => Bool.noConfusion h
  | ex _, h => Bool.noConfusion h
end

/-! ## Substitution preserves boundedness -/

/-- Rocq: `Analysis.OmegaLogic.occ_shift`. -/
theorem occ_shift (k : Nat) : ∀ t : ATerm,
    occ k (asubst shiftSub t) = (match k with | 0 => false | k + 1 => occ k t)
  | tv i => by cases k <;> rfl
  | tz => by cases k <;> rfl
  | ts t => occ_shift k t
  | tplus s t => by
    show (occ k (asubst shiftSub s) || occ k (asubst shiftSub t)) = _
    rw [occ_shift k s, occ_shift k t]; cases k <;> rfl
  | tmult s t => by
    show (occ k (asubst shiftSub s) || occ k (asubst shiftSub t)) = _
    rw [occ_shift k s, occ_shift k t]; cases k <;> rfl

theorem occ0_shift (t : ATerm) : occ 0 (asubst shiftSub t) = false := occ_shift 0 t

theorem occS_shift (k : Nat) (t : ATerm) : occ (k + 1) (asubst shiftSub t) = occ k t := occ_shift (k + 1) t

theorem occ0_up (τ : Nat → ATerm) : ∀ t : ATerm, occ 0 (asubst (up τ) t) = occ 0 t
  | tv 0 => rfl
  | tv (i + 1) => occ0_shift (τ i)
  | tz => rfl
  | ts t => occ0_up τ t
  | tplus s t => congrArg₂ (· || ·) (occ0_up τ s) (occ0_up τ t)
  | tmult s t => congrArg₂ (· || ·) (occ0_up τ s) (occ0_up τ t)

theorem occ1_upup (σ : Nat → ATerm) : ∀ t : ATerm, occ 1 (asubst (up (up σ)) t) = occ 1 t
  | tv 0 => rfl
  | tv 1 => rfl
  | tv (i + 2) => (occS_shift 0 _).trans (occ0_shift (σ i))
  | tz => rfl
  | ts t => occ1_upup σ t
  | tplus s t => congrArg₂ (· || ·) (occ1_upup σ s) (occ1_upup σ t)
  | tmult s t => congrArg₂ (· || ·) (occ1_upup σ s) (occ1_upup σ t)

/-- Rocq: `Analysis.OmegaLogic.occ_asubst`. -/
theorem occ_asubst (k : Nat) (τ : Nat → ATerm) :
    ∀ t : ATerm, occ k (asubst τ t) = true → ∃ i, occ i t = true ∧ occ k (τ i) = true
  | tv i, h => ⟨i, beq_self i, h⟩
  | tz, h => Bool.noConfusion h
  | ts t, h => occ_asubst k τ t h
  | tplus s t, h =>
    match or_true_split h with
    | .inl h => let ⟨i, h1, h2⟩ := occ_asubst k τ s h
      ⟨i, by show (occ i s || occ i t) = true; rw [h1]; rfl, h2⟩
    | .inr h => let ⟨i, h1, h2⟩ := occ_asubst k τ t h
      ⟨i, by show (occ i s || occ i t) = true; rw [h1]; cases occ i s <;> rfl, h2⟩
  | tmult s t, h =>
    match or_true_split h with
    | .inl h => let ⟨i, h1, h2⟩ := occ_asubst k τ s h
      ⟨i, by show (occ i s || occ i t) = true; rw [h1]; rfl, h2⟩
    | .inr h => let ⟨i, h1, h2⟩ := occ_asubst k τ t h
      ⟨i, by show (occ i s || occ i t) = true; rw [h1]; cases occ i s <;> rfl, h2⟩

/-- Rocq: `Analysis.OmegaLogic.occ_up0`. -/
theorem occ_up0 (σ : Nat → ATerm) (t : ATerm) (h : occ 0 t = false) : occ 0 (asubst (up σ) t) = false :=
  (occ0_up σ t).trans h

/-- Rocq: `Analysis.OmegaLogic.occ_up1`. -/
theorem occ_up1 (σ : Nat → ATerm) (t : ATerm) (_h0 : occ 0 t = false) (h1 : occ 1 t = false) :
    occ 1 (asubst (up (up σ)) t) = false :=
  (occ1_upup σ t).trans h1

theorem isTv0_shift (t : ATerm) : isTv 0 (asubst shiftSub t) = false := by cases t <;> rfl

theorem isTvS_shift (k : Nat) (t : ATerm) : isTv (k + 1) (asubst shiftSub t) = isTv k t := by cases t <;> rfl

theorem isTv0_up (τ : Nat → ATerm) : ∀ t : ATerm, isTv 0 (asubst (up τ) t) = isTv 0 t
  | tv 0 => rfl
  | tv (i + 1) => isTv0_shift (τ i)
  | tz => rfl
  | ts _ => rfl
  | tplus _ _ => rfl
  | tmult _ _ => rfl

theorem isTv1_upup (σ : Nat → ATerm) : ∀ t : ATerm, isTv 1 (asubst (up (up σ)) t) = isTv 1 t
  | tv 0 => rfl
  | tv 1 => rfl
  | tv (i + 2) => (isTvS_shift 0 _).trans (isTv0_shift (σ i))
  | tz => rfl
  | ts _ => rfl
  | tplus _ _ => rfl
  | tmult _ _ => rfl

theorem isT10_shift2 (s : ATerm) : isT10 (asubst shiftSub (asubst shiftSub s)) = false := by
  cases s with
  | tplus a b =>
    show (isTv 1 (asubst shiftSub (asubst shiftSub a)) && _) = false
    rw [isTvS_shift, isTv0_shift]; rfl
  | tv _ => rfl
  | tz => rfl
  | ts _ => rfl
  | tmult _ _ => rfl

theorem isT10_upup (σ : Nat → ATerm) : ∀ w : ATerm, isT10 (asubst (up (up σ)) w) = isT10 w
  | tv 0 => rfl
  | tv 1 => rfl
  | tv (i + 2) => isT10_shift2 (σ i)
  | tz => rfl
  | ts _ => rfl
  | tplus a b => congrArg₂ (· && ·) (isTv1_upup σ a) (isTv0_up (up σ) b)
  | tmult _ _ => rfl

theorem isGuard_fsubst (σ : Nat → ATerm) : ∀ G : Form, isGuard (fsubst (up σ) G) = isGuard G
  | ex (.eq w v) => by
    show (isT10 (asubst (up (up σ)) w) && !occ 0 (asubst (up (up σ)) v) && !occ 1 (asubst (up (up σ)) v)) =
      (isT10 w && !occ 0 v && !occ 1 v)
    rw [isT10_upup, occ0_up, occ1_upup]
  | ex bot => rfl
  | ex (conj _ _) => rfl
  | ex (disj _ _) => rfl
  | ex (imp _ _) => rfl
  | ex (all _) => rfl
  | ex (ex _) => rfl
  | .eq _ _ => rfl
  | bot => rfl
  | conj _ _ => rfl
  | disj _ _ => rfl
  | imp _ _ => rfl
  | all _ => rfl

theorem bexShape_shift (s v : ATerm) : bexShape (.eq (asubst shiftSub s) v) = false := by
  cases s with
  | tplus a b => exact isTv0_shift b
  | tv _ => rfl
  | tz => rfl
  | ts _ => rfl
  | tmult _ _ => rfl

theorem isDEx_fsubst (σ : Nat → ATerm) : ∀ A : Form, isDEx (fsubst (up σ) A) = isDEx A
  | .eq (tplus u b) v => by
    show (isTv 0 (asubst (up σ) b) && !occ 0 (asubst (up σ) u) && !occ 0 (asubst (up σ) v)) =
      (isTv 0 b && !occ 0 u && !occ 0 v)
    rw [isTv0_up, occ0_up, occ0_up]
  | .eq (tv 0) _ => rfl
  | .eq (tv (i + 1)) v => by
    show (bexShape (.eq (asubst shiftSub (σ i)) (asubst (up σ) v)) && _ && _) = false
    rw [bexShape_shift]; rfl
  | .eq tz _ => rfl
  | .eq (ts _) _ => rfl
  | .eq (tmult _ _) _ => rfl
  | bot => rfl
  | conj _ _ => rfl
  | disj _ _ => rfl
  | imp _ _ => rfl
  | all _ => rfl
  | ex _ => rfl

mutual
/-- Rocq: `Analysis.OmegaLogic.isD_fsubst_eq`. -/
theorem isD_fsubst_eq : ∀ (A : Form) (σ : Nat → ATerm), isD (fsubst σ A) = isD A
  | .eq _ _, _ => rfl
  | bot, _ => rfl
  | conj A B, σ => congrArg₂ (· && ·) (isD_fsubst_eq A σ) (isD_fsubst_eq B σ)
  | disj A B, σ => congrArg₂ (· && ·) (isD_fsubst_eq A σ) (isD_fsubst_eq B σ)
  | imp A B, σ => congrArg₂ (· && ·) (isD_fsubst_eq A σ) (isD_fsubst_eq B σ)
  | all A, σ => isDAll_fsubst A σ
  | ex A, σ => isDEx_fsubst σ A
theorem isDAll_fsubst : ∀ (A : Form) (σ : Nat → ATerm), isDAll (fsubst (up σ) A) = isDAll A
  | .eq _ _, _ => rfl
  | bot, _ => rfl
  | conj _ _, _ => rfl
  | disj _ _, _ => rfl
  | imp G B, σ => congrArg₂ (· && ·) (isGuard_fsubst σ G) (isD_fsubst_eq B (up σ))
  | all _, _ => rfl
  | ex _, _ => rfl
end

/-- Rocq: `Analysis.OmegaLogic.DP_fsubst`. -/
theorem DP_fsubst {A : Form} (h : DP A) (σ : Nat → ATerm) : DP (fsubst σ A) :=
  isD_DP ((isD_fsubst_eq A σ).trans (DP_isD h))

/-- Rocq: `Analysis.OmegaLogic.isD_fsubst`. -/
theorem isD_fsubst (A : Form) (σ : Nat → ATerm) (h : isD A = true) : isD (fsubst σ A) = true :=
  (isD_fsubst_eq A σ).trans h

/-- Rocq: `Analysis.OmegaLogic.isD_fsubst_back`. -/
theorem isD_fsubst_back (A : Form) (σ : Nat → ATerm) (h : isD (fsubst σ A) = true) : isD A = true :=
  (isD_fsubst_eq A σ).symm.trans h

/-- Rocq: `Analysis.OmegaLogic.occ_asubst_back`. -/
theorem occ_asubst_back (k : Nat) (τ : Nat → ATerm) {i : Nat} (hk : occ k (τ i) = true) :
    ∀ t : ATerm, occ i t = true → occ k (asubst τ t) = true
  | tv j, h => by rw [Nat.eq_of_beq_eq_true h]; exact hk
  | tz, h => Bool.noConfusion h
  | ts t, h => occ_asubst_back k τ hk t h
  | tplus s t, h => match or_true_split h with
    | .inl h => by show (occ k (asubst τ s) || _) = true; rw [occ_asubst_back k τ hk s h]; rfl
    | .inr h => by
      show (_ || occ k (asubst τ t)) = true; rw [occ_asubst_back k τ hk t h]; cases occ k (asubst τ s) <;> rfl
  | tmult s t, h => match or_true_split h with
    | .inl h => by show (occ k (asubst τ s) || _) = true; rw [occ_asubst_back k τ hk s h]; rfl
    | .inr h => by
      show (_ || occ k (asubst τ t)) = true; rw [occ_asubst_back k τ hk t h]; cases occ k (asubst τ s) <;> rfl

/-- Rocq: `Analysis.OmegaLogic.shift_not_tv0`. -/
theorem shift_not_tv0 (t : ATerm) : asubst shiftSub t ≠ tv 0 := by
  cases t <;> intro h <;> cases h

/-- Rocq: `Analysis.OmegaLogic.up_tv0`. -/
theorem up_tv0 (σ : Nat → ATerm) : ∀ w : ATerm, asubst (up σ) w = tv 0 → w = tv 0
  | tv 0, _ => rfl
  | tv (i + 1), h => absurd h (shift_not_tv0 (σ i))
  | tz, h => ATerm.noConfusion h
  | ts _, h => ATerm.noConfusion h
  | tplus _ _, h => ATerm.noConfusion h
  | tmult _ _, h => ATerm.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.upup_tv1`. -/
theorem upup_tv1 (σ : Nat → ATerm) : ∀ w : ATerm, asubst (up (up σ)) w = tv 1 → w = tv 1
  | tv 0, h => Bool.noConfusion (congrArg (isTv 1) h)
  | tv 1, _ => rfl
  | tv (i + 2), h => by
    have h' : isTv 1 (asubst shiftSub (asubst shiftSub (σ i))) = isTv 1 (tv 1) := congrArg (isTv 1) h
    rw [isTvS_shift, isTv0_shift] at h'
    exact Bool.noConfusion h'
  | tz, h => ATerm.noConfusion h
  | ts _, h => ATerm.noConfusion h
  | tplus _ _, h => ATerm.noConfusion h
  | tmult _ _, h => ATerm.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.occ_up0_back`. -/
theorem occ_up0_back (σ : Nat → ATerm) (t : ATerm) (h : occ 0 (asubst (up σ) t) = false) : occ 0 t = false :=
  (occ0_up σ t).symm.trans h

/-- Rocq: `Analysis.OmegaLogic.occ_up1_back`. -/
theorem occ_up1_back (σ : Nat → ATerm) (t : ATerm) (h : occ 1 (asubst (up (up σ)) t) = false) : occ 1 t = false :=
  (occ1_upup σ t).symm.trans h

/-- Rocq: `Analysis.OmegaLogic.upup_pat`. -/
theorem upup_pat (σ : Nat → ATerm) (w : ATerm) (h : asubst (up (up σ)) w = tplus (tv 1) (tv 0)) :
    w = tplus (tv 1) (tv 0) := by
  have hs : isT10 w = true := (isT10_upup σ w).symm.trans (by rw [h]; rfl)
  exact isT10_eq hs

/-- Rocq: `Analysis.OmegaLogic.up_pat`. -/
theorem up_pat (σ : Nat → ATerm) (w u' : ATerm) (h : asubst (up σ) w = tplus u' (tv 0)) :
    ∃ u, w = tplus u (tv 0) := by
  have hs : bexShape (.eq (asubst (up σ) w) tz) = bexShape (.eq w tz) := by
    cases w with
    | tplus u b => exact isTv0_up σ b
    | tv i => cases i with
      | zero => rfl
      | succ i => exact bexShape_shift (σ i) tz
    | tz => rfl
    | ts _ => rfl
    | tmult _ _ => rfl
  have h1 : bexShape (.eq w tz) = true := hs.symm.trans (by rw [h]; rfl)
  exact ⟨bexU (.eq w tz), (Form.eq.inj (bex_eq h1)).1⟩

/-! ## Deciding bounded formulas -/

/-- Rocq: `Analysis.OmegaLogic.fall`. -/
def fall : Nat → (Nat → Bool) → Bool
  | 0, f => f 0
  | b + 1, f => fall b f && f (b + 1)

/-- Rocq: `Analysis.OmegaLogic.fall_spec`. -/
theorem fall_spec : ∀ (b : Nat) (f : Nat → Bool), fall b f = true ↔ ∀ z, z ≤ b → f z = true
  | 0, f => ⟨fun h z hz => Nat.le_zero.mp hz ▸ h, fun h => h 0 (Nat.le_refl 0)⟩
  | b + 1, f => ⟨fun h z hz => by
      obtain ⟨h1, h2⟩ := and_true_split h
      cases Nat.lt_or_eq_of_le hz with
      | inl hlt => exact (fall_spec b f).1 h1 z (Nat.le_of_lt_succ hlt)
      | inr e => rw [e]; exact h2,
    fun h => by
      show (fall b f && f (b + 1)) = true
      rw [(fall_spec b f).2 (fun z hz => h z (Nat.le_succ_of_le hz)), h (b + 1) (Nat.le_refl _)]; rfl⟩

mutual
/-- Rocq: `Analysis.OmegaLogic.deval`. -/
def deval : (Nat → Nat) → Form → Bool
  | ρ, .eq s t => Nat.beq (teval ρ s) (teval ρ t)
  | _, bot => false
  | ρ, conj A B => deval ρ A && deval ρ B
  | ρ, disj A B => deval ρ A || deval ρ B
  | ρ, imp A B => !deval ρ A || deval ρ B
  | ρ, all A => devalAll ρ A
  | ρ, ex A => (bexShape A && Nat.ble (teval (scons 0 ρ) (bexU A)) (teval (scons 0 ρ) (bexV A)))
/-- The bounded universal, by search below its bound. -/
def devalAll : (Nat → Nat) → Form → Bool
  | ρ, imp G B => guardShape G && fall (teval (scons 0 (scons 0 ρ)) (guardBound G)) (fun z => deval (scons z ρ) B)
  | _, .eq _ _ => false
  | _, bot => false
  | _, conj _ _ => false
  | _, disj _ _ => false
  | _, all _ => false
  | _, ex _ => false
end

/-- Rocq: `Analysis.OmegaLogic.teval_occ`. -/
theorem teval_occ {ρ ρ' : Nat → Nat} : ∀ (t : ATerm), (∀ i, occ i t = true → ρ i = ρ' i) → teval ρ t = teval ρ' t
  | tv i, h => h i (beq_self i)
  | tz, _ => rfl
  | ts t, h => congrArg (· + 1) (teval_occ t h)
  | tplus s t, h => congrArg₂ (· + ·)
      (teval_occ s (fun i hi => h i (by show (occ i s || occ i t) = true; rw [hi]; rfl)))
      (teval_occ t (fun i hi => h i (by show (occ i s || occ i t) = true; rw [hi]; cases occ i s <;> rfl)))
  | tmult s t, h => congrArg₂ (· * ·)
      (teval_occ s (fun i hi => h i (by show (occ i s || occ i t) = true; rw [hi]; rfl)))
      (teval_occ t (fun i hi => h i (by show (occ i s || occ i t) = true; rw [hi]; cases occ i s <;> rfl)))

/-- Rocq: `Analysis.Embedding.teval_occ01`. -/
theorem teval_occ01 {v : ATerm} (h0 : occ 0 v = false) (h1 : occ 1 v = false) (ρ : Nat → Nat) (a b a' b' : Nat) :
    teval (scons a (scons b ρ)) v = teval (scons a' (scons b' ρ)) v :=
  teval_occ v (fun i hi => match i with
    | 0 => absurd (h0 ▸ hi) (fun h => Bool.noConfusion h)
    | 1 => absurd (h1 ▸ hi) (fun h => Bool.noConfusion h)
    | _ + 2 => rfl)

/-- Rocq: `Analysis.Embedding.teval_occ0`. -/
theorem teval_occ0 {v : ATerm} (h0 : occ 0 v = false) (ρ : Nat → Nat) (a a' : Nat) :
    teval (scons a ρ) v = teval (scons a' ρ) v :=
  teval_occ v (fun i hi => match i with
    | 0 => absurd (h0 ▸ hi) (fun h => Bool.noConfusion h)
    | _ + 1 => rfl)

theorem add_sub_of_le {a b : Nat} (h : a ≤ b) : a + (b - a) = b :=
  (Nat.add_comm _ _).trans (Nat.sub_add_cancel h)

/-- Rocq: `Analysis.OmegaLogic.deval_correct`. -/
theorem deval_correct {A : Form} (h : DP A) : ∀ ρ, deval ρ A = true ↔ sat ρ A := by
  induction h with
  | eq s t =>
    intro ρ
    exact ⟨Nat.eq_of_beq_eq_true, fun h => by
      show Nat.beq (teval ρ s) (teval ρ t) = true
      rw [show teval ρ s = teval ρ t from h]; exact beq_self _⟩
  | bot => intro ρ; exact ⟨fun h => Bool.noConfusion h, False.elim⟩
  | conj A B _ _ ih1 ih2 =>
    intro ρ
    exact ⟨fun h => let ⟨a, b⟩ := and_true_split h; ⟨(ih1 ρ).1 a, (ih2 ρ).1 b⟩,
      fun ⟨a, b⟩ => by show (deval ρ A && deval ρ B) = true; rw [(ih1 ρ).2 a, (ih2 ρ).2 b]; rfl⟩
  | disj A B _ _ ih1 ih2 =>
    intro ρ
    exact ⟨fun h => (or_true_split h).elim (fun a => .inl ((ih1 ρ).1 a)) (fun b => .inr ((ih2 ρ).1 b)),
      fun hab => by
        show (deval ρ A || deval ρ B) = true
        cases hab with
        | inl a => rw [(ih1 ρ).2 a]; rfl
        | inr b => rw [(ih2 ρ).2 b]; cases deval ρ A <;> rfl⟩
  | imp A B _ _ ih1 ih2 =>
    intro ρ
    show (!deval ρ A || deval ρ B) = true ↔ (sat ρ A → sat ρ B)
    constructor
    · intro h ha
      cases or_true_split h with
      | inl h => exact absurd ((ih1 ρ).2 ha) (by rw [not_true h]; exact fun h => Bool.noConfusion h)
      | inr h => exact (ih2 ρ).1 h
    · intro f
      cases e : deval ρ A with
      | false => rfl
      | true => rw [(ih2 ρ).2 (f ((ih1 ρ).1 e))]; rfl
  | ball v B h0 h1 _ ih =>
    intro ρ
    show fall (teval (scons 0 (scons 0 ρ)) v) (fun z => deval (scons z ρ) B) = true ↔
      ∀ x, (∃ d, x + d = teval (scons d (scons x ρ)) v) → sat (scons x ρ) B
    constructor
    · intro h x ⟨d, hd⟩
      rw [teval_occ01 h0 h1 ρ d x 0 0] at hd
      exact (ih (scons x ρ)).1 ((fall_spec _ _).1 h x (Nat.le.intro hd))
    · intro h
      refine (fall_spec _ _).2 (fun z hz => (ih (scons z ρ)).2 (h z ⟨teval (scons 0 (scons 0 ρ)) v - z, ?_⟩))
      rw [teval_occ01 h0 h1 ρ _ z 0 0]
      exact add_sub_of_le hz
  | bex u v h0 h1 =>
    intro ρ
    show Nat.ble (teval (scons 0 ρ) u) (teval (scons 0 ρ) v) = true ↔
      ∃ d, teval (scons d ρ) u + d = teval (scons d ρ) v
    constructor
    · intro h
      refine ⟨teval (scons 0 ρ) v - teval (scons 0 ρ) u, ?_⟩
      rw [teval_occ0 h0 ρ (teval (scons 0 ρ) v - teval (scons 0 ρ) u) 0,
        teval_occ0 h1 ρ (teval (scons 0 ρ) v - teval (scons 0 ρ) u) 0]
      exact add_sub_of_le (Nat.le_of_ble_eq_true h)
    · intro ⟨d, hd⟩
      rw [teval_occ0 h0 ρ d 0, teval_occ0 h1 ρ d 0] at hd
      exact Nat.ble_eq_true_of_le (Nat.le.intro hd)

/-- Rocq: `Analysis.OmegaLogic.deval_sat`. -/
theorem deval_sat {A : Form} (h : isD A = true) (ρ : Nat → Nat) : deval ρ A = true ↔ sat ρ A :=
  deval_correct (isD_DP h) ρ

/-- Rocq: `Analysis.OmegaLogic.deval_false`. -/
theorem deval_false {A : Form} (ρ : Nat → Nat) (h : isD A = true) : deval ρ A = false ↔ ¬ sat ρ A :=
  ⟨fun e hs => by rw [(deval_sat h ρ).2 hs] at e; exact Bool.noConfusion e,
   fun hn => by
    cases e : deval ρ A with
    | false => rfl
    | true => exact absurd ((deval_sat h ρ).1 e) hn⟩

/-! ## Signed formulas -/

/-- Rocq: `Analysis.OmegaLogic.sform`. -/
abbrev SForm : Type := Bool × Form

/-- Rocq: `Analysis.OmegaLogic.sneg`. -/
def sneg (s : SForm) : SForm := (!s.1, s.2)

/-- Rocq: `Analysis.OmegaLogic.sneg_sneg`. -/
theorem sneg_sneg : ∀ s : SForm, sneg (sneg s) = s
  | (true, _) => rfl
  | (false, _) => rfl

/-- A true bounded formula. Rocq: `Analysis.OmegaLogic.dax`. -/
def Dax (s : SForm) : Prop := isD s.2 = true ∧ deval ρ0 s.2 = s.1

/-- A false bounded formula. Rocq: `Analysis.OmegaLogic.dfalse`. -/
def Dfalse (s : SForm) : Prop := isD s.2 = true ∧ deval ρ0 s.2 = !s.1

/-- Rocq: `Analysis.OmegaLogic.dfalse_sneg`. -/
theorem dfalse_sneg (s : SForm) : Dfalse s ↔ Dax (sneg s) := Iff.rfl

/-- Rocq: `Analysis.OmegaLogic.dax_dec`. -/
theorem dax_dec (s : SForm) (h : isD s.2 = true) : Dax s ∨ Dfalse s := by
  cases s with
  | mk b A =>
    cases b <;> cases e : deval ρ0 A
    · exact .inl ⟨h, e⟩
    · exact .inr ⟨h, e⟩
    · exact .inr ⟨h, e⟩
    · exact .inl ⟨h, e⟩

/-- Rocq: `Analysis.OmegaLogic.inst`. -/
def inst (b : Bool) (A : Form) (i : Nat) : SForm := (b, sub1 A (num i))

/-- Rocq: `Analysis.OmegaLogic.kind`. -/
inductive Kind : Type where
  /-- Rocq: `KAtom`. -/
  | atom : Kind
  /-- Rocq: `KConj`. -/
  | conj : SForm → SForm → Kind
  /-- Rocq: `KDisj`. -/
  | disj : SForm → SForm → Kind
  /-- Rocq: `KUniv`. -/
  | univ : Bool → Form → Kind
  /-- Rocq: `KExis`. -/
  | exis : Bool → Form → Kind

/-- Rocq: `Analysis.OmegaLogic.kindof`. -/
def kindof : SForm → Kind
  | (true, .eq _ _) => .atom
  | (false, .eq _ _) => .atom
  | (true, bot) => .atom
  | (false, bot) => .atom
  | (true, conj A B) => .conj (true, A) (true, B)
  | (false, conj A B) => .disj (false, A) (false, B)
  | (true, disj A B) => .disj (true, A) (true, B)
  | (false, disj A B) => .conj (false, A) (false, B)
  | (true, imp A B) => .disj (false, A) (true, B)
  | (false, imp A B) => .conj (true, A) (false, B)
  | (true, all A) => .univ true A
  | (false, all A) => .exis false A
  | (true, ex A) => .exis true A
  | (false, ex A) => .univ false A

/-- Rocq: `Analysis.OmegaLogic.kind_conj_neg`. -/
theorem kind_conj_neg : ∀ {s s1 s2 : SForm}, kindof s = .conj s1 s2 → kindof (sneg s) = .disj (sneg s1) (sneg s2)
  | (true, conj _ _), _, _, h => by cases h; rfl
  | (false, disj _ _), _, _, h => by cases h; rfl
  | (false, imp _ _), _, _, h => by cases h; rfl
  | (true, .eq _ _), _, _, h => Kind.noConfusion h
  | (false, .eq _ _), _, _, h => Kind.noConfusion h
  | (true, bot), _, _, h => Kind.noConfusion h
  | (false, bot), _, _, h => Kind.noConfusion h
  | (false, conj _ _), _, _, h => Kind.noConfusion h
  | (true, disj _ _), _, _, h => Kind.noConfusion h
  | (true, imp _ _), _, _, h => Kind.noConfusion h
  | (true, all _), _, _, h => Kind.noConfusion h
  | (false, all _), _, _, h => Kind.noConfusion h
  | (true, ex _), _, _, h => Kind.noConfusion h
  | (false, ex _), _, _, h => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.kind_disj_neg`. -/
theorem kind_disj_neg : ∀ {s s1 s2 : SForm}, kindof s = .disj s1 s2 → kindof (sneg s) = .conj (sneg s1) (sneg s2)
  | (false, conj _ _), _, _, h => by cases h; rfl
  | (true, disj _ _), _, _, h => by cases h; rfl
  | (true, imp _ _), _, _, h => by cases h; rfl
  | (true, .eq _ _), _, _, h => Kind.noConfusion h
  | (false, .eq _ _), _, _, h => Kind.noConfusion h
  | (true, bot), _, _, h => Kind.noConfusion h
  | (false, bot), _, _, h => Kind.noConfusion h
  | (true, conj _ _), _, _, h => Kind.noConfusion h
  | (false, disj _ _), _, _, h => Kind.noConfusion h
  | (false, imp _ _), _, _, h => Kind.noConfusion h
  | (true, all _), _, _, h => Kind.noConfusion h
  | (false, all _), _, _, h => Kind.noConfusion h
  | (true, ex _), _, _, h => Kind.noConfusion h
  | (false, ex _), _, _, h => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.kind_univ_neg`. -/
theorem kind_univ_neg : ∀ {s : SForm} {b : Bool} {A : Form}, kindof s = .univ b A → kindof (sneg s) = .exis (!b) A
  | (true, all _), _, _, h => by cases h; rfl
  | (false, ex _), _, _, h => by cases h; rfl
  | (true, .eq _ _), _, _, h => Kind.noConfusion h
  | (false, .eq _ _), _, _, h => Kind.noConfusion h
  | (true, bot), _, _, h => Kind.noConfusion h
  | (false, bot), _, _, h => Kind.noConfusion h
  | (true, conj _ _), _, _, h => Kind.noConfusion h
  | (false, conj _ _), _, _, h => Kind.noConfusion h
  | (true, disj _ _), _, _, h => Kind.noConfusion h
  | (false, disj _ _), _, _, h => Kind.noConfusion h
  | (true, imp _ _), _, _, h => Kind.noConfusion h
  | (false, imp _ _), _, _, h => Kind.noConfusion h
  | (false, all _), _, _, h => Kind.noConfusion h
  | (true, ex _), _, _, h => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.kind_exis_neg`. -/
theorem kind_exis_neg : ∀ {s : SForm} {b : Bool} {A : Form}, kindof s = .exis b A → kindof (sneg s) = .univ (!b) A
  | (false, all _), _, _, h => by cases h; rfl
  | (true, ex _), _, _, h => by cases h; rfl
  | (true, .eq _ _), _, _, h => Kind.noConfusion h
  | (false, .eq _ _), _, _, h => Kind.noConfusion h
  | (true, bot), _, _, h => Kind.noConfusion h
  | (false, bot), _, _, h => Kind.noConfusion h
  | (true, conj _ _), _, _, h => Kind.noConfusion h
  | (false, conj _ _), _, _, h => Kind.noConfusion h
  | (true, disj _ _), _, _, h => Kind.noConfusion h
  | (false, disj _ _), _, _, h => Kind.noConfusion h
  | (true, imp _ _), _, _, h => Kind.noConfusion h
  | (false, imp _ _), _, _, h => Kind.noConfusion h
  | (true, all _), _, _, h => Kind.noConfusion h
  | (false, ex _), _, _, h => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.inst_sneg`. -/
theorem inst_sneg (b : Bool) (A : Form) (i : Nat) : sneg (inst b A i) = inst (!b) A i := rfl

/-- Bounded formulas are closed under their components. Rocq: `Analysis.OmegaLogic.isD_conj`. -/
theorem isD_conj : ∀ {s s1 s2 : SForm}, kindof s = .conj s1 s2 → isD s.2 = true →
    isD s1.2 = true ∧ isD s2.2 = true
  | (true, conj _ _), _, _, h, hD => by cases h; exact and_true_split hD
  | (false, disj _ _), _, _, h, hD => by cases h; exact and_true_split hD
  | (false, imp _ _), _, _, h, hD => by cases h; exact and_true_split hD
  | (true, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, h, _ => Kind.noConfusion h
  | (false, conj _ _), _, _, h, _ => Kind.noConfusion h
  | (true, disj _ _), _, _, h, _ => Kind.noConfusion h
  | (true, imp _ _), _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, h, _ => Kind.noConfusion h
  | (false, all _), _, _, h, _ => Kind.noConfusion h
  | (true, ex _), _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, h, _ => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.isD_disj`. -/
theorem isD_disj : ∀ {s s1 s2 : SForm}, kindof s = .disj s1 s2 → isD s.2 = true →
    isD s1.2 = true ∧ isD s2.2 = true
  | (false, conj _ _), _, _, h, hD => by cases h; exact and_true_split hD
  | (true, disj _ _), _, _, h, hD => by cases h; exact and_true_split hD
  | (true, imp _ _), _, _, h, hD => by cases h; exact and_true_split hD
  | (true, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, h, _ => Kind.noConfusion h
  | (true, conj _ _), _, _, h, _ => Kind.noConfusion h
  | (false, disj _ _), _, _, h, _ => Kind.noConfusion h
  | (false, imp _ _), _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, h, _ => Kind.noConfusion h
  | (false, all _), _, _, h, _ => Kind.noConfusion h
  | (true, ex _), _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, h, _ => Kind.noConfusion h

theorem isD_of_all : ∀ {A : Form}, isD (all A) = true → isD A = true
  | imp G B, h => by
    obtain ⟨hg, hb⟩ := and_true_split h
    obtain ⟨hg12, _⟩ := and_true_split hg
    obtain ⟨hg1, hg2⟩ := and_true_split hg12
    show (isD G && isD B) = true
    rw [guard_eq hg1, hb]
    show (isDEx (.eq (tplus (tv 1) (tv 0)) (guardBound G)) && true) = true
    show ((true && !false && !occ 0 (guardBound G)) && true) = true
    rw [not_true hg2]; rfl
  | .eq _ _, h => Bool.noConfusion h
  | bot, h => Bool.noConfusion h
  | conj _ _, h => Bool.noConfusion h
  | disj _ _, h => Bool.noConfusion h
  | all _, h => Bool.noConfusion h
  | ex _, h => Bool.noConfusion h

theorem isD_of_ex {A : Form} (h : isD (ex A) = true) : isD A = true := by
  obtain ⟨h12, _⟩ := and_true_split h
  obtain ⟨h1, _⟩ := and_true_split h12
  rw [bex_eq h1]; rfl

/-- Rocq: `Analysis.OmegaLogic.isD_quant_inst`. -/
theorem isD_quant_inst (A : Form) (t : ATerm) (h : isD (all A) = true ∨ isD (ex A) = true) :
    isD (sub1 A t) = true :=
  isD_fsubst A _ (h.elim isD_of_all isD_of_ex)

/-- Rocq: `Analysis.OmegaLogic.deval_fsubst`. -/
theorem deval_fsubst (A : Form) (σ : Nat → ATerm) (ρ : Nat → Nat) (h : isD A = true) :
    deval ρ (fsubst σ A) = deval (fun i => teval ρ (σ i)) A := by
  have h' := isD_fsubst A σ h
  cases e : deval (fun i => teval ρ (σ i)) A with
  | true => exact (deval_sat h' ρ).2 ((sat_fsubst A ρ σ).2 ((deval_sat h _).1 e))
  | false => exact (deval_false ρ h').2 (fun hs => (deval_false _ h).1 e ((sat_fsubst A ρ σ).1 hs))

/-- Rocq: `Analysis.OmegaLogic.deval_ext`. -/
theorem deval_ext (A : Form) {ρ ρ' : Nat → Nat} (h : isD A = true) (E : ∀ i, ρ i = ρ' i) :
    deval ρ A = deval ρ' A := by
  cases e : deval ρ' A with
  | true => exact (deval_sat h ρ).2 ((sat_ext A E).2 ((deval_sat h ρ').1 e))
  | false => exact (deval_false ρ h).2 (fun hs => (deval_false ρ' h).1 e ((sat_ext A E).1 hs))

/-- Rocq: `Analysis.OmegaLogic.deval_sub1`. -/
theorem deval_sub1 (A : Form) (ρ : Nat → Nat) (i : Nat) (h : isD A = true) :
    deval ρ (sub1 A (num i)) = deval (scons i ρ) A :=
  (deval_fsubst A _ ρ h).trans (deval_ext A h (fun j => by
    cases j with
    | zero => exact teval_num ρ i
    | succ j => rfl))

/-! ## Ranks -/

/-- Rocq: `Analysis.OmegaLogic.rank`. -/
def rank : Form → Nat
  | .eq _ _ => 0
  | bot => 0
  | conj A B => if isD (conj A B) = true then 0 else Nat.max (rank A) (rank B) + 1
  | disj A B => if isD (disj A B) = true then 0 else Nat.max (rank A) (rank B) + 1
  | imp A B => if isD (imp A B) = true then 0 else Nat.max (rank A) (rank B) + 1
  | all A => if isD (all A) = true then 0 else rank A + 1
  | ex A => if isD (ex A) = true then 0 else rank A + 1

/-- Rocq: `Analysis.OmegaLogic.rank_D`. -/
theorem rank_D : ∀ {A : Form}, isD A = true → rank A = 0
  | .eq _ _, _ => rfl
  | bot, _ => rfl
  | conj _ _, h => ite_eq_left h
  | disj _ _, h => ite_eq_left h
  | imp _ _, h => ite_eq_left h
  | all _, h => ite_eq_left h
  | ex _, h => ite_eq_left h

theorem rank_ndD {X : Form} {k : Nat} (h : isD X = false) : (if isD X = true then 0 else k) = k :=
  ite_eq_right (fun e => Bool.noConfusion (e.symm.trans h))

/-- Rocq: `Analysis.OmegaLogic.rank_0_D`. -/
theorem rank_0_D : ∀ {A : Form}, rank A = 0 → isD A = true
  | .eq _ _, _ => rfl
  | bot, _ => rfl
  | conj A B, h => by
    cases e : isD (conj A B)
    · rw [show rank (conj A B) = _ from rank_ndD e] at h; exact Nat.noConfusion h
    · rfl
  | disj A B, h => by
    cases e : isD (disj A B)
    · rw [show rank (disj A B) = _ from rank_ndD e] at h; exact Nat.noConfusion h
    · rfl
  | imp A B, h => by
    cases e : isD (imp A B)
    · rw [show rank (imp A B) = _ from rank_ndD e] at h; exact Nat.noConfusion h
    · rfl
  | all A, h => by
    cases e : isD (all A)
    · rw [show rank (all A) = _ from rank_ndD e] at h; exact Nat.noConfusion h
    · rfl
  | ex A, h => by
    cases e : isD (ex A)
    · rw [show rank (ex A) = _ from rank_ndD e] at h; exact Nat.noConfusion h
    · rfl

/-- Rocq: `Analysis.OmegaLogic.rank_fsubst`. -/
theorem rank_fsubst : ∀ (A : Form) (σ : Nat → ATerm), rank (fsubst σ A) = rank A
  | .eq _ _, _ => rfl
  | bot, _ => rfl
  | conj A B, σ => by
    show (if isD (fsubst σ (conj A B)) = true then 0 else Nat.max (rank (fsubst σ A)) (rank (fsubst σ B)) + 1) = _
    rw [isD_fsubst_eq, rank_fsubst A σ, rank_fsubst B σ]; rfl
  | disj A B, σ => by
    show (if isD (fsubst σ (disj A B)) = true then 0 else Nat.max (rank (fsubst σ A)) (rank (fsubst σ B)) + 1) = _
    rw [isD_fsubst_eq, rank_fsubst A σ, rank_fsubst B σ]; rfl
  | imp A B, σ => by
    show (if isD (fsubst σ (imp A B)) = true then 0 else Nat.max (rank (fsubst σ A)) (rank (fsubst σ B)) + 1) = _
    rw [isD_fsubst_eq, rank_fsubst A σ, rank_fsubst B σ]; rfl
  | all A, σ => by
    show (if isD (fsubst σ (all A)) = true then 0 else rank (fsubst (up σ) A) + 1) = _
    rw [isD_fsubst_eq, rank_fsubst A (up σ)]; rfl
  | ex A, σ => by
    show (if isD (fsubst σ (ex A)) = true then 0 else rank (fsubst (up σ) A) + 1) = _
    rw [isD_fsubst_eq, rank_fsubst A (up σ)]; rfl

theorem lt_max_succ_l (a b : Nat) : a < Nat.max a b + 1 := Nat.lt_succ_of_le (Nat.le_max_left a b)
theorem lt_max_succ_r (a b : Nat) : b < Nat.max a b + 1 := Nat.lt_succ_of_le (Nat.le_max_right a b)

/-- Rocq: `Analysis.OmegaLogic.rank_conj`. -/
theorem rank_conj : ∀ {s s1 s2 : SForm}, kindof s = .conj s1 s2 → isD s.2 = false →
    rank s1.2 < rank s.2 ∧ rank s2.2 < rank s.2
  | (true, conj A B), _, _, h, hD => by
    cases h; show _ < (if _ then _ else _) ∧ _ < (if _ then _ else _)
    rw [rank_ndD hD]; exact ⟨lt_max_succ_l _ _, lt_max_succ_r _ _⟩
  | (false, disj A B), _, _, h, hD => by
    cases h; show _ < (if _ then _ else _) ∧ _ < (if _ then _ else _)
    rw [rank_ndD hD]; exact ⟨lt_max_succ_l _ _, lt_max_succ_r _ _⟩
  | (false, imp A B), _, _, h, hD => by
    cases h; show _ < (if _ then _ else _) ∧ _ < (if _ then _ else _)
    rw [rank_ndD hD]; exact ⟨lt_max_succ_l _ _, lt_max_succ_r _ _⟩
  | (true, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, h, _ => Kind.noConfusion h
  | (false, conj _ _), _, _, h, _ => Kind.noConfusion h
  | (true, disj _ _), _, _, h, _ => Kind.noConfusion h
  | (true, imp _ _), _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, h, _ => Kind.noConfusion h
  | (false, all _), _, _, h, _ => Kind.noConfusion h
  | (true, ex _), _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, h, _ => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.rank_disj`. -/
theorem rank_disj : ∀ {s s1 s2 : SForm}, kindof s = .disj s1 s2 → isD s.2 = false →
    rank s1.2 < rank s.2 ∧ rank s2.2 < rank s.2
  | (false, conj A B), _, _, h, hD => by
    cases h; show _ < (if _ then _ else _) ∧ _ < (if _ then _ else _)
    rw [rank_ndD hD]; exact ⟨lt_max_succ_l _ _, lt_max_succ_r _ _⟩
  | (true, disj A B), _, _, h, hD => by
    cases h; show _ < (if _ then _ else _) ∧ _ < (if _ then _ else _)
    rw [rank_ndD hD]; exact ⟨lt_max_succ_l _ _, lt_max_succ_r _ _⟩
  | (true, imp A B), _, _, h, hD => by
    cases h; show _ < (if _ then _ else _) ∧ _ < (if _ then _ else _)
    rw [rank_ndD hD]; exact ⟨lt_max_succ_l _ _, lt_max_succ_r _ _⟩
  | (true, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, h, _ => Kind.noConfusion h
  | (true, conj _ _), _, _, h, _ => Kind.noConfusion h
  | (false, disj _ _), _, _, h, _ => Kind.noConfusion h
  | (false, imp _ _), _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, h, _ => Kind.noConfusion h
  | (false, all _), _, _, h, _ => Kind.noConfusion h
  | (true, ex _), _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, h, _ => Kind.noConfusion h

theorem rank_quant {A : Form} {X : Form} (hX : rank X = (if isD X = true then 0 else rank A + 1))
    (hD : isD X = false) (i : Nat) : rank (sub1 A (num i)) < rank X := by
  rw [hX, rank_ndD hD]
  show rank (fsubst _ A) < _
  rw [rank_fsubst]; exact Nat.lt_succ_self _

/-- Rocq: `Analysis.OmegaLogic.rank_univ`. -/
theorem rank_univ : ∀ {s : SForm} {b : Bool} {A : Form} (i : Nat), kindof s = .univ b A → isD s.2 = false →
    rank (inst b A i).2 < rank s.2
  | (true, all _), _, _, i, h, hD => by cases h; exact rank_quant rfl hD i
  | (false, ex _), _, _, i, h, hD => by cases h; exact rank_quant rfl hD i
  | (true, .eq _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, _, h, _ => Kind.noConfusion h
  | (true, conj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, conj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, disj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, disj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, imp _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, imp _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, all _), _, _, _, h, _ => Kind.noConfusion h
  | (true, ex _), _, _, _, h, _ => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.rank_exis`. -/
theorem rank_exis : ∀ {s : SForm} {b : Bool} {A : Form} (i : Nat), kindof s = .exis b A → isD s.2 = false →
    rank (inst b A i).2 < rank s.2
  | (false, all _), _, _, i, h, hD => by cases h; exact rank_quant rfl hD i
  | (true, ex _), _, _, i, h, hD => by cases h; exact rank_quant rfl hD i
  | (true, .eq _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, _, h, _ => Kind.noConfusion h
  | (true, conj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, conj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, disj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, disj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, imp _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, imp _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, _, h, _ => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.kind_atom_D`. -/
theorem kind_atom_D : ∀ {s : SForm}, kindof s = .atom → isD s.2 = true
  | (true, .eq _ _), _ => rfl
  | (false, .eq _ _), _ => rfl
  | (true, bot), _ => rfl
  | (false, bot), _ => rfl
  | (true, conj _ _), h => Kind.noConfusion h
  | (false, conj _ _), h => Kind.noConfusion h
  | (true, disj _ _), h => Kind.noConfusion h
  | (false, disj _ _), h => Kind.noConfusion h
  | (true, imp _ _), h => Kind.noConfusion h
  | (false, imp _ _), h => Kind.noConfusion h
  | (true, all _), h => Kind.noConfusion h
  | (false, all _), h => Kind.noConfusion h
  | (true, ex _), h => Kind.noConfusion h
  | (false, ex _), h => Kind.noConfusion h

/-! ## False bounded formulas have false components -/

theorem bool_and_false {a b : Bool} (h : (a && b) = false) : a = false ∨ b = false := by
  cases a <;> cases b
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact Bool.noConfusion h

theorem bool_or_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b
  · exact ⟨rfl, rfl⟩
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.dfalse_conj`. -/
theorem dfalse_conj : ∀ {s s1 s2 : SForm}, kindof s = .conj s1 s2 → Dfalse s → Dfalse s1 ∨ Dfalse s2
  | (true, conj A B), _, _, h, ⟨hD, hv⟩ => by
    cases h
    obtain ⟨h1, h2⟩ := and_true_split hD
    exact (bool_and_false hv).elim (fun a => .inl ⟨h1, a⟩) (fun b => .inr ⟨h2, b⟩)
  | (false, disj A B), _, _, h, ⟨hD, hv⟩ => by
    cases h
    obtain ⟨h1, h2⟩ := and_true_split hD
    exact (or_true_split hv).elim (fun a => .inl ⟨h1, a⟩) (fun b => .inr ⟨h2, b⟩)
  | (false, imp A B), _, _, h, ⟨hD, hv⟩ => by
    cases h
    obtain ⟨h1, h2⟩ := and_true_split hD
    exact (or_true_split hv).elim (fun a => .inl ⟨h1, not_true a⟩) (fun b => .inr ⟨h2, b⟩)
  | (true, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, h, _ => Kind.noConfusion h
  | (false, conj _ _), _, _, h, _ => Kind.noConfusion h
  | (true, disj _ _), _, _, h, _ => Kind.noConfusion h
  | (true, imp _ _), _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, h, _ => Kind.noConfusion h
  | (false, all _), _, _, h, _ => Kind.noConfusion h
  | (true, ex _), _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, h, _ => Kind.noConfusion h

theorem not_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b
  · exact Bool.noConfusion h
  · rfl

/-- Rocq: `Analysis.OmegaLogic.dfalse_disj`. -/
theorem dfalse_disj : ∀ {s s1 s2 : SForm}, kindof s = .disj s1 s2 → Dfalse s → Dfalse s1 ∧ Dfalse s2
  | (false, conj A B), _, _, h, ⟨hD, hv⟩ => by
    cases h
    obtain ⟨h1, h2⟩ := and_true_split hD
    obtain ⟨a, b⟩ := and_true_split hv
    exact ⟨⟨h1, a⟩, ⟨h2, b⟩⟩
  | (true, disj A B), _, _, h, ⟨hD, hv⟩ => by
    cases h
    obtain ⟨h1, h2⟩ := and_true_split hD
    obtain ⟨a, b⟩ := bool_or_false hv
    exact ⟨⟨h1, a⟩, ⟨h2, b⟩⟩
  | (true, imp A B), _, _, h, ⟨hD, hv⟩ => by
    cases h
    obtain ⟨h1, h2⟩ := and_true_split hD
    obtain ⟨a, b⟩ := bool_or_false hv
    exact ⟨⟨h1, not_false a⟩, ⟨h2, b⟩⟩
  | (true, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, h, _ => Kind.noConfusion h
  | (true, conj _ _), _, _, h, _ => Kind.noConfusion h
  | (false, disj _ _), _, _, h, _ => Kind.noConfusion h
  | (false, imp _ _), _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, h, _ => Kind.noConfusion h
  | (false, all _), _, _, h, _ => Kind.noConfusion h
  | (true, ex _), _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, h, _ => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.dfalse_exis`. -/
theorem dfalse_exis : ∀ {s : SForm} {b : Bool} {A : Form} (i : Nat), kindof s = .exis b A → Dfalse s →
    Dfalse (inst b A i)
  | (true, ex A), _, _, i, h, ⟨hD, hv⟩ => by
    cases h
    have hi : isD (sub1 A (num i)) = true := isD_quant_inst A _ (.inr hD)
    exact ⟨hi, (deval_false ρ0 hi).2 (fun hs => (deval_false ρ0 hD).1 hv ⟨i, (sat_sub1_num ρ0 A i).1 hs⟩)⟩
  | (false, all A), _, _, i, h, ⟨hD, hv⟩ => by
    cases h
    have hi : isD (sub1 A (num i)) = true := isD_quant_inst A _ (.inl hD)
    exact ⟨hi, (deval_sat hi ρ0).2 ((sat_sub1_num ρ0 A i).2 ((deval_sat hD ρ0).1 hv i))⟩
  | (true, .eq _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, .eq _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, bot), _, _, _, h, _ => Kind.noConfusion h
  | (false, bot), _, _, _, h, _ => Kind.noConfusion h
  | (true, conj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, conj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, disj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, disj _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, imp _ _), _, _, _, h, _ => Kind.noConfusion h
  | (false, imp _ _), _, _, _, h, _ => Kind.noConfusion h
  | (true, all _), _, _, _, h, _ => Kind.noConfusion h
  | (false, ex _), _, _, _, h, _ => Kind.noConfusion h

/-- Rocq: `Analysis.OmegaLogic.dax_not_dfalse`. -/
theorem dax_not_dfalse {s : SForm} (h1 : Dax s) (h2 : Dfalse s) : False := by
  have e := h1.2.symm.trans h2.2
  cases s with
  | mk b A => cases b <;> exact Bool.noConfusion e

/-! ## Derivations

`OD n ρ α Γ`: the sequent `Γ` is derivable at control `n` with height `α`,
using cuts on formulas of rank below `ρ` only. Principal formulas stay in the
premises, so contraction is built in. -/

/-- Rocq: `Analysis.OmegaLogic.OD`. -/
inductive OD : Nat → Nat → VForm → List SForm → Prop
  /-- Rocq: `od_ax`. -/
  | ax (n ρ : Nat) (α : VForm) (Γ : List SForm) (s : SForm) : s ∈ Γ → Dax s → OD n ρ α Γ
  /-- Rocq: `od_conj`. -/
  | conj (n ρ : Nat) (α β : VForm) (Γ : List SForm) (s s1 s2 : SForm) :
      s ∈ Γ → kindof s = .conj s1 s2 → OD n ρ β (s1 :: Γ) → OD n ρ β (s2 :: Γ) → Olt n β α → OD n ρ α Γ
  /-- Rocq: `od_disj`. -/
  | disj (n ρ : Nat) (α β : VForm) (Γ : List SForm) (s s1 s2 s' : SForm) :
      s ∈ Γ → kindof s = .disj s1 s2 → (s' = s1 ∨ s' = s2) → OD n ρ β (s' :: Γ) → Olt n β α → OD n ρ α Γ
  /-- Rocq: `od_univ`. -/
  | univ (n ρ : Nat) (α : VForm) (β : Nat → VForm) (Γ : List SForm) (s : SForm) (b : Bool) (A : Form) :
      s ∈ Γ → kindof s = .univ b A → isD s.2 = false →
      (∀ i, OD (Nat.max n (i + 1)) ρ (β i) (inst b A i :: Γ)) →
      (∀ i, Olt (Nat.max n (i + 1)) (β i) α) → OD n ρ α Γ
  /-- Rocq: `od_exis`. -/
  | exis (n ρ : Nat) (α β : VForm) (Γ : List SForm) (s : SForm) (b : Bool) (A : Form) (m : Nat) :
      s ∈ Γ → kindof s = .exis b A → m < n → OD n ρ β (inst b A m :: Γ) → Olt n β α → OD n ρ α Γ
  /-- Rocq: `od_cut`. -/
  | cut (n ρ : Nat) (α β : VForm) (Γ : List SForm) (s : SForm) :
      rank s.2 < ρ → OD n ρ β (s :: Γ) → OD n ρ β (sneg s :: Γ) → Olt n β α → OD n ρ α Γ
  /-- Rocq: `od_up`. -/
  | up (n m ρ : Nat) (α β γ : VForm) (h : Nat) (Γ : List SForm) :
      n ≤ m → OD m ρ β Γ → Hardy γ n h → m ≤ h → Olt n (vcat β γ) α → OD n ρ α Γ

/-- `Γ ⊑ Γ'`: every formula of `Γ` is in `Γ'` or is a false bounded formula.
Rocq: `Analysis.OmegaLogic.sub_mod`. -/
def SubMod (Γ Γ' : List SForm) : Prop := ∀ s, s ∈ Γ → s ∈ Γ' ∨ Dfalse s

/-- Rocq: `Analysis.OmegaLogic.sub_mod_cons`. -/
theorem sub_mod_cons (s : SForm) {Γ Γ' : List SForm} (H : SubMod Γ Γ') : SubMod (s :: Γ) (s :: Γ') :=
  fun x hx => match hx with
    | .head _ => .inl (.head _)
    | .tail _ hx => (H x hx).elim (fun h => .inl (.tail _ h)) .inr

/-- Rocq: `Analysis.OmegaLogic.sub_mod_drop`. -/
theorem sub_mod_drop {s : SForm} {Γ Γ' : List SForm} (hs : Dfalse s) (H : SubMod Γ Γ') : SubMod (s :: Γ) Γ' :=
  fun x hx => match hx with
    | .head _ => .inr hs
    | .tail _ hx => H x hx

/-- Rocq: `Analysis.OmegaLogic.sub_mod_incl`. -/
theorem sub_mod_incl {Γ Γ' : List SForm} (H : ∀ s, s ∈ Γ → s ∈ Γ') : SubMod Γ Γ' :=
  fun x hx => .inl (H x hx)

theorem le_max_succ (n i : Nat) : i + 1 ≤ Nat.max n (i + 1) := Nat.le_max_right _ _

theorem max_mono_l {n n' : Nat} (h : n ≤ n') (k : Nat) : Nat.max n k ≤ Nat.max n' k := max_mono h (Nat.le_refl k)

/-- Weakening, raising the control, the cut rank and the height, and deleting
false bounded formulas. Rocq: `Analysis.OmegaLogic.od_struct`. -/
theorem od_struct {n ρ : Nat} {α : VForm} {Γ : List SForm} (h : OD n ρ α Γ) :
    ∀ (n' ρ' : Nat) (α' : VForm) (Γ' : List SForm), n ≤ n' → ρ ≤ ρ' → Reach n α α' → SubMod Γ Γ' →
      OD n' ρ' α' Γ' := by
  induction h with
  | ax n ρ α Γ s hs hax =>
    intro n' ρ' α' Γ' _ _ _ hΓ
    exact (hΓ s hs).elim (fun h => .ax _ _ _ _ s h hax) (fun hf => absurd hf (dax_not_dfalse hax ·))
  | conj n ρ α β Γ s s1 s2 hs hk _ _ hlt ih1 ih2 =>
    intro n' ρ' α' Γ' hn hρ hα hΓ
    have hβ : Reach n β α' := reach_trans (olt_reach hlt) hα
    cases hΓ s hs with
    | inl hs' =>
      exact .conj _ _ _ β _ s s1 s2 hs' hk (ih1 n' ρ' β _ hn hρ (.refl _) (sub_mod_cons _ hΓ))
        (ih2 n' ρ' β _ hn hρ (.refl _) (sub_mod_cons _ hΓ)) (olt_mono hn (olt_reach_trans hlt hα))
    | inr hf =>
      cases dfalse_conj hk hf with
      | inl h => exact ih1 n' ρ' α' Γ' hn hρ hβ (sub_mod_drop h hΓ)
      | inr h => exact ih2 n' ρ' α' Γ' hn hρ hβ (sub_mod_drop h hΓ)
  | disj n ρ α β Γ s s1 s2 s' hs hk hsel _ hlt ih =>
    intro n' ρ' α' Γ' hn hρ hα hΓ
    have hβ : Reach n β α' := reach_trans (olt_reach hlt) hα
    cases hΓ s hs with
    | inl hs'' =>
      exact .disj _ _ _ β _ s s1 s2 s' hs'' hk hsel (ih n' ρ' β _ hn hρ (.refl _) (sub_mod_cons _ hΓ))
        (olt_mono hn (olt_reach_trans hlt hα))
    | inr hf =>
      have ⟨h1, h2⟩ := dfalse_disj hk hf
      have hs' : Dfalse s' := hsel.elim (fun e => e ▸ h1) (fun e => e ▸ h2)
      exact ih n' ρ' α' Γ' hn hρ hβ (sub_mod_drop hs' hΓ)
  | univ n ρ α β Γ s b A hs hk hD _ hlt ih =>
    intro n' ρ' α' Γ' hn hρ hα hΓ
    have hs' : s ∈ Γ' := (hΓ s hs).elim id (fun hf => absurd (hf.1.symm.trans hD) (fun h => Bool.noConfusion h))
    exact .univ _ _ _ β _ s b A hs' hk hD
      (fun i => ih i _ ρ' (β i) _ (max_mono_l hn _) hρ (.refl _) (sub_mod_cons _ hΓ))
      (fun i => olt_mono (max_mono_l hn _) (olt_reach_trans (hlt i) (reach_mono (Nat.le_max_left _ _) hα)))
  | exis n ρ α β Γ s b A m hs hk hm _ hlt ih =>
    intro n' ρ' α' Γ' hn hρ hα hΓ
    have hβ : Reach n β α' := reach_trans (olt_reach hlt) hα
    cases hΓ s hs with
    | inl hs' =>
      exact .exis _ _ _ β _ s b A m hs' hk (Nat.lt_of_lt_of_le hm hn)
        (ih n' ρ' β _ hn hρ (.refl _) (sub_mod_cons _ hΓ)) (olt_mono hn (olt_reach_trans hlt hα))
    | inr hf => exact ih n' ρ' α' Γ' hn hρ hβ (sub_mod_drop (dfalse_exis m hk hf) hΓ)
  | cut n ρ α β Γ s hr _ _ hlt ih1 ih2 =>
    intro n' ρ' α' Γ' hn hρ hα hΓ
    exact .cut _ _ _ β _ s (Nat.lt_of_lt_of_le hr hρ) (ih1 n' ρ' β _ hn hρ (.refl _) (sub_mod_cons _ hΓ))
      (ih2 n' ρ' β _ hn hρ (.refl _) (sub_mod_cons _ hΓ)) (olt_mono hn (olt_reach_trans hlt hα))
  | up n m ρ α β γ h Γ _ _ hh hmh hlt ih =>
    intro n' ρ' α' Γ' hn hρ hα hΓ
    obtain ⟨h', hh'⟩ := hardy_exists γ n'
    have hhh : h ≤ h' := hardy_mono_arg γ hn hh hh'
    exact .up n' (Nat.max m n') ρ' α' β γ h' Γ' (Nat.le_max_right _ _)
      (ih _ ρ' β Γ' (Nat.le_max_left _ _) hρ (.refl _) hΓ) hh'
      (max_le' (Nat.le_trans hmh hhh) (hardy_ge hh')) (olt_mono hn (olt_reach_trans hlt hα))

/-- Rocq: `Analysis.OmegaLogic.od_weaken`. -/
theorem od_weaken {n ρ : Nat} {α : VForm} {Γ Γ' : List SForm} (h : OD n ρ α Γ) (hi : ∀ s, s ∈ Γ → s ∈ Γ') :
    OD n ρ α Γ' :=
  od_struct h n ρ α Γ' (Nat.le_refl _) (Nat.le_refl _) (.refl _) (sub_mod_incl hi)

/-- Rocq: `Analysis.OmegaLogic.od_height`. -/
theorem od_height {n ρ : Nat} {α α' : VForm} {Γ : List SForm} (h : OD n ρ α Γ) (hr : Reach n α α') :
    OD n ρ α' Γ :=
  od_struct h n ρ α' Γ (Nat.le_refl _) (Nat.le_refl _) hr (sub_mod_incl (fun _ h => h))

/-- Rocq: `Analysis.OmegaLogic.od_control`. -/
theorem od_control {n n' ρ : Nat} {α : VForm} {Γ : List SForm} (h : OD n ρ α Γ) (hn : n ≤ n') : OD n' ρ α Γ :=
  od_struct h n' ρ α Γ hn (Nat.le_refl _) (.refl _) (sub_mod_incl (fun _ h => h))

/-- Rocq: `Analysis.OmegaLogic.od_rank`. -/
theorem od_rank {n ρ ρ' : Nat} {α : VForm} {Γ : List SForm} (h : OD n ρ α Γ) (hρ : ρ ≤ ρ') : OD n ρ' α Γ :=
  od_struct h n ρ' α Γ (Nat.le_refl _) hρ (.refl _) (sub_mod_incl (fun _ h => h))

/-! ## Inversion -/

/-- Rocq: `Analysis.OmegaLogic.sub_rem_cons`. -/
theorem sub_rem_cons (x s : SForm) {Γ Δ : List SForm} (H : ∀ y, y ∈ Δ → y = s ∨ y ∈ Γ) :
    ∀ y, y ∈ x :: Δ → y = s ∨ y ∈ x :: Γ :=
  fun y hy => match hy with
    | .head _ => .inr (.head _)
    | .tail _ hy => (H y hy).elim .inl (fun h => .inr (.tail _ h))

theorem incl_swap {a b : SForm} {L : List SForm} : ∀ y, y ∈ a :: b :: L → y ∈ b :: a :: L
  | _, .head _ => .tail _ (.head _)
  | _, .tail _ (.head _) => .head _
  | _, .tail _ (.tail _ h) => .tail _ (.tail _ h)

theorem incl_dup {a : SForm} {L : List SForm} : ∀ y, y ∈ a :: a :: L → y ∈ a :: L
  | _, .head _ => .head _
  | _, .tail _ h => h

/-- Rocq: `Analysis.OmegaLogic.od_inv_conj`. -/
theorem od_inv_conj {n ρ : Nat} {α : VForm} {Δ : List SForm} (h : OD n ρ α Δ) :
    ∀ (s s1 s2 sj : SForm) (Γ : List SForm), kindof s = .conj s1 s2 → isD s.2 = false → (sj = s1 ∨ sj = s2) →
      (∀ y, y ∈ Δ → y = s ∨ y ∈ Γ) → OD n ρ α (sj :: Γ) := by
  induction h with
  | ax n ρ α Δ x hx hax =>
    intro s s1 s2 sj Γ _ hDs _ hΔ
    cases hΔ x hx with
    | inl e => subst e; exact absurd (hax.1.symm.trans hDs) (fun h => Bool.noConfusion h)
    | inr hin => exact .ax _ _ _ _ x (.tail _ hin) hax
  | conj n ρ α β Δ x x1 x2 hx hk _ _ hlt ih1 ih2 =>
    intro s s1 s2 sj Γ hks hDs hsj hΔ
    cases hΔ x hx with
    | inl e =>
      subst e
      rw [hks] at hk
      injection hk with e1 e2
      subst e1
      subst e2
      have H1 := ih1 x s1 s2 sj (s1 :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)
      have H2 := ih2 x s1 s2 sj (s2 :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)
      cases hsj with
      | inl e =>
        subst e
        exact od_struct H1 _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (olt_reach hlt) (sub_mod_incl incl_dup)
      | inr e =>
        subst e
        exact od_struct H2 _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (olt_reach hlt) (sub_mod_incl incl_dup)
    | inr hin =>
      exact .conj _ _ _ β _ x x1 x2 (.tail _ hin) hk
        (od_weaken (ih1 s s1 s2 sj (x1 :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)) incl_swap)
        (od_weaken (ih2 s s1 s2 sj (x2 :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)) incl_swap) hlt
  | disj n ρ α β Δ x x1 x2 x' hx hk hsel _ hlt ih =>
    intro s s1 s2 sj Γ hks hDs hsj hΔ
    cases hΔ x hx with
    | inl e => subst e; rw [hks] at hk; exact Kind.noConfusion hk
    | inr hin =>
      exact .disj _ _ _ β _ x x1 x2 x' (.tail _ hin) hk hsel
        (od_weaken (ih s s1 s2 sj (x' :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)) incl_swap) hlt
  | univ n ρ α β Δ x b A hx hk hD _ hlt ih =>
    intro s s1 s2 sj Γ hks hDs hsj hΔ
    cases hΔ x hx with
    | inl e => subst e; rw [hks] at hk; exact Kind.noConfusion hk
    | inr hin =>
      exact .univ _ _ _ β _ x b A (.tail _ hin) hk hD
        (fun i => od_weaken (ih i s s1 s2 sj (inst b A i :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)) incl_swap) hlt
  | exis n ρ α β Δ x b A m hx hk hm _ hlt ih =>
    intro s s1 s2 sj Γ hks hDs hsj hΔ
    cases hΔ x hx with
    | inl e => subst e; rw [hks] at hk; exact Kind.noConfusion hk
    | inr hin =>
      exact .exis _ _ _ β _ x b A m (.tail _ hin) hk hm
        (od_weaken (ih s s1 s2 sj (inst b A m :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)) incl_swap) hlt
  | cut n ρ α β Δ x hr _ _ hlt ih1 ih2 =>
    intro s s1 s2 sj Γ hks hDs hsj hΔ
    exact .cut _ _ _ β _ x hr
      (od_weaken (ih1 s s1 s2 sj (x :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)) incl_swap)
      (od_weaken (ih2 s s1 s2 sj (sneg x :: Γ) hks hDs hsj (sub_rem_cons _ _ hΔ)) incl_swap) hlt
  | up n m ρ α β γ h Δ hnm _ hh hmh hlt ih =>
    intro s s1 s2 sj Γ hks hDs hsj hΔ
    exact .up _ m _ _ β γ h _ hnm (ih s s1 s2 sj Γ hks hDs hsj hΔ) hh hmh hlt

/-- Rocq: `Analysis.OmegaLogic.max_swap`. -/
theorem max_swap (n i j : Nat) : Nat.max (Nat.max n (j + 1)) (i + 1) = Nat.max (Nat.max n (i + 1)) (j + 1) :=
  Nat.le_antisymm
    (max_le' (max_le' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
    (max_le' (max_le' (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))

theorem max_idem (n i : Nat) : Nat.max (Nat.max n (i + 1)) (i + 1) = Nat.max n (i + 1) :=
  Nat.le_antisymm (max_le' (Nat.le_refl _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)

/-- Rocq: `Analysis.OmegaLogic.od_inv_univ`. -/
theorem od_inv_univ {n ρ : Nat} {α : VForm} {Δ : List SForm} (h : OD n ρ α Δ) :
    ∀ (s : SForm) (b : Bool) (A : Form) (Γ : List SForm), kindof s = .univ b A → isD s.2 = false →
      (∀ y, y ∈ Δ → y = s ∨ y ∈ Γ) → ∀ i, OD (Nat.max n (i + 1)) ρ α (inst b A i :: Γ) := by
  induction h with
  | ax n ρ α Δ x hx hax =>
    intro s b A Γ _ hDs hΔ i
    cases hΔ x hx with
    | inl e => subst e; exact absurd (hax.1.symm.trans hDs) (fun h => Bool.noConfusion h)
    | inr hin => exact .ax _ _ _ _ x (.tail _ hin) hax
  | conj n ρ α β Δ x x1 x2 hx hk _ _ hlt ih1 ih2 =>
    intro s b A Γ hks hDs hΔ i
    cases hΔ x hx with
    | inl e => subst e; rw [hks] at hk; exact Kind.noConfusion hk
    | inr hin =>
      exact .conj _ _ _ β _ x x1 x2 (.tail _ hin) hk
        (od_weaken (ih1 s b A (x1 :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i) incl_swap)
        (od_weaken (ih2 s b A (x2 :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i) incl_swap)
        (olt_mono (Nat.le_max_left _ _) hlt)
  | disj n ρ α β Δ x x1 x2 x' hx hk hsel _ hlt ih =>
    intro s b A Γ hks hDs hΔ i
    cases hΔ x hx with
    | inl e => subst e; rw [hks] at hk; exact Kind.noConfusion hk
    | inr hin =>
      exact .disj _ _ _ β _ x x1 x2 x' (.tail _ hin) hk hsel
        (od_weaken (ih s b A (x' :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i) incl_swap)
        (olt_mono (Nat.le_max_left _ _) hlt)
  | univ n ρ α β Δ x b' A' hx hk hD _ hlt ih =>
    intro s b A Γ hks hDs hΔ i
    cases hΔ x hx with
    | inl e =>
      subst e
      rw [hks] at hk
      injection hk with e1 e2
      subst e1
      subst e2
      have H := ih i x b A (inst b A i :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i
      rw [max_idem] at H
      exact od_struct H _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (olt_reach (hlt i)) (sub_mod_incl incl_dup)
    | inr hin =>
      refine .univ _ _ _ β _ x b' A' (.tail _ hin) hk hD (fun j => ?_) (fun j => ?_)
      · rw [max_swap]
        exact od_weaken (ih j s b A (inst b' A' j :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i) incl_swap
      · exact olt_mono (max_mono_l (Nat.le_max_left _ _) _) (hlt j)
  | exis n ρ α β Δ x b' A' m hx hk hm _ hlt ih =>
    intro s b A Γ hks hDs hΔ i
    cases hΔ x hx with
    | inl e => subst e; rw [hks] at hk; exact Kind.noConfusion hk
    | inr hin =>
      exact .exis _ _ _ β _ x b' A' m (.tail _ hin) hk (Nat.lt_of_lt_of_le hm (Nat.le_max_left _ _))
        (od_weaken (ih s b A (inst b' A' m :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i) incl_swap)
        (olt_mono (Nat.le_max_left _ _) hlt)
  | cut n ρ α β Δ x hr _ _ hlt ih1 ih2 =>
    intro s b A Γ hks hDs hΔ i
    exact .cut _ _ _ β _ x hr
      (od_weaken (ih1 s b A (x :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i) incl_swap)
      (od_weaken (ih2 s b A (sneg x :: Γ) hks hDs (sub_rem_cons _ _ hΔ) i) incl_swap)
      (olt_mono (Nat.le_max_left _ _) hlt)
  | up n m ρ α β γ h Δ hnm _ hh hmh hlt ih =>
    intro s b A Γ hks hDs hΔ i
    obtain ⟨h', hh'⟩ := hardy_exists γ (Nat.max n (i + 1))
    have hhh : h ≤ h' := hardy_mono_arg γ (Nat.le_max_left _ _) hh hh'
    exact .up _ (Nat.max m (i + 1)) _ _ β γ h' _ (max_mono_l hnm _) (ih s b A Γ hks hDs hΔ i) hh'
      (max_le' (Nat.le_trans hmh hhh) (Nat.le_trans (Nat.le_max_right n (i + 1)) (hardy_ge hh')))
      (olt_mono (Nat.le_max_left _ _) hlt)

/-! ## Cut elimination -/

/-- Rocq: `Analysis.OmegaLogic.rem_head`. -/
theorem rem_head (C : SForm) (Γ : List SForm) : ∀ y, y ∈ C :: Γ → y = C ∨ y ∈ Γ
  | _, .head _ => .inl rfl
  | _, .tail _ h => .inr h

/-- Rocq: `Analysis.OmegaLogic.kind_conj_univ_neg`. -/
theorem kind_conj_univ_neg (C : SForm)
    (Hkind : (∃ c1 c2, kindof C = .conj c1 c2) ∨ (∃ b A, kindof C = .univ b A)) :
    (∀ x1 x2, kindof (sneg C) ≠ .conj x1 x2) ∧ (∀ b A, kindof (sneg C) ≠ .univ b A) := by
  rcases Hkind with ⟨c1, c2, H⟩ | ⟨b, A, H⟩
  · rw [kind_conj_neg H]; exact ⟨fun _ _ h => Kind.noConfusion h, fun _ _ h => Kind.noConfusion h⟩
  · rw [kind_univ_neg H]; exact ⟨fun _ _ h => Kind.noConfusion h, fun _ _ h => Kind.noConfusion h⟩

theorem incl_insert (C x : SForm) (Γ : List SForm) : ∀ y, y ∈ C :: Γ → y ∈ C :: x :: Γ
  | _, .head _ => .head _
  | _, .tail _ h => .tail _ (.tail _ h)

/-- The reduction lemma: a cut on an invertible formula `C` (a conjunction
or a universal) of maximal rank is removed at the cost of adding the heights.
Rocq: `Analysis.OmegaLogic.od_reduce`. -/
theorem od_reduce {ρ : Nat} {C : SForm} (HDC : isD C.2 = false)
    (Hkind : (∃ c1 c2, kindof C = .conj c1 c2) ∨ (∃ b A, kindof C = .univ b A))
    {n : Nat} {β : VForm} {Δ : List SForm} (h : OD n ρ β Δ) :
    rank C.2 = ρ → ∀ (n0 : Nat) (α : VForm) (Γ : List SForm), n0 ≤ n → OD n0 ρ α (C :: Γ) →
      (∀ y, y ∈ Δ → y = sneg C ∨ y ∈ Γ) → OD n ρ (vcat α β) Γ := by
  have ⟨HnC, HnU⟩ := kind_conj_univ_neg C Hkind
  induction h with
  | ax n ρ β Δ x hx hax =>
    intro _ n0 α Γ _ _ hΔ
    cases hΔ x hx with
    | inl e => subst e; exact absurd (hax.1.symm.trans HDC) (fun h => Bool.noConfusion h)
    | inr hin => exact .ax _ _ _ _ x hin hax
  | conj n ρ β βp Δ x x1 x2 hx hk _ _ hlt ih1 ih2 =>
    intro HrC n0 α Γ hn0 HC hΔ
    cases hΔ x hx with
    | inl e => subst e; exact absurd hk (HnC x1 x2)
    | inr hin =>
      exact .conj _ _ _ (vcat α βp) _ x x1 x2 hin hk
        (ih1 HrC n0 α (x1 :: Γ) hn0 (od_weaken HC (incl_insert C x1 Γ)) (sub_rem_cons _ _ hΔ))
        (ih2 HrC n0 α (x2 :: Γ) hn0 (od_weaken HC (incl_insert C x2 Γ)) (sub_rem_cons _ _ hΔ))
        (olt_vcat α hlt)
  | disj n ρ β βp Δ x x1 x2 x' hx hk hsel _ hlt ih =>
    intro HrC n0 α Γ hn0 HC hΔ
    have IH' := ih HrC n0 α (x' :: Γ) hn0 (od_weaken HC (incl_insert C x' Γ)) (sub_rem_cons _ _ hΔ)
    cases hΔ x hx with
    | inr hin => exact .disj _ _ _ (vcat α βp) _ x x1 x2 x' hin hk hsel IH' (olt_vcat α hlt)
    | inl e =>
      subst e
      rcases Hkind with ⟨c1, c2, HkC⟩ | ⟨b, A, HkC⟩
      · rw [kind_conj_neg HkC] at hk
        injection hk with e1 e2
        have Hcj : ∃ cj, (cj = c1 ∨ cj = c2) ∧ x' = sneg cj :=
          hsel.elim (fun e => ⟨c1, .inl rfl, e.trans e1.symm⟩) (fun e => ⟨c2, .inr rfl, e.trans e2.symm⟩)
        obtain ⟨cj, hcj, rfl⟩ := Hcj
        have Hr := rank_conj HkC HDC
        refine .cut _ _ _ (vcat α βp) _ cj ?_ ?_ IH' (olt_vcat α hlt)
        · rw [← HrC]; exact hcj.elim (fun e => e ▸ Hr.1) (fun e => e ▸ Hr.2)
        · exact od_struct (od_inv_conj HC C c1 c2 cj Γ HkC HDC hcj (rem_head C Γ)) _ _ _ _ hn0 (Nat.le_refl _)
            (reach_prefix _ α βp) (sub_mod_incl (fun _ h => h))
      · rw [kind_univ_neg HkC] at hk; exact Kind.noConfusion hk
  | univ n ρ β βp Δ x b A hx hk hD _ hlt ih =>
    intro HrC n0 α Γ hn0 HC hΔ
    cases hΔ x hx with
    | inl e => subst e; exact absurd hk (HnU b A)
    | inr hin =>
      exact .univ _ _ _ (fun i => vcat α (βp i)) _ x b A hin hk hD
        (fun i => ih i HrC n0 α (inst b A i :: Γ) (Nat.le_trans hn0 (Nat.le_max_left _ _))
          (od_weaken HC (incl_insert C _ Γ)) (sub_rem_cons _ _ hΔ))
        (fun i => olt_vcat α (hlt i))
  | exis n ρ β βp Δ x b A m hx hk hm _ hlt ih =>
    intro HrC n0 α Γ hn0 HC hΔ
    have IH' := ih HrC n0 α (inst b A m :: Γ) hn0 (od_weaken HC (incl_insert C _ Γ)) (sub_rem_cons _ _ hΔ)
    cases hΔ x hx with
    | inr hin => exact .exis _ _ _ (vcat α βp) _ x b A m hin hk hm IH' (olt_vcat α hlt)
    | inl e =>
      subst e
      rcases Hkind with ⟨c1, c2, HkC⟩ | ⟨b', A', HkC⟩
      · rw [kind_conj_neg HkC] at hk; exact Kind.noConfusion hk
      · rw [kind_univ_neg HkC] at hk
        injection hk with e1 e2
        subst e1
        subst e2
        refine .cut _ _ _ (vcat α βp) _ (inst b' A' m) ?_ ?_ IH' (olt_vcat α hlt)
        · rw [← HrC]; exact rank_univ m HkC HDC
        · exact od_struct (od_inv_univ HC C b' A' Γ HkC HDC (rem_head C Γ) m) _ _ _ _
            (max_le' hn0 hm) (Nat.le_refl _) (reach_prefix _ α βp) (sub_mod_incl (fun _ h => h))
  | cut n ρ β βp Δ x hr _ _ hlt ih1 ih2 =>
    intro HrC n0 α Γ hn0 HC hΔ
    exact .cut _ _ _ (vcat α βp) _ x hr
      (ih1 HrC n0 α (x :: Γ) hn0 (od_weaken HC (incl_insert C _ Γ)) (sub_rem_cons _ _ hΔ))
      (ih2 HrC n0 α (sneg x :: Γ) hn0 (od_weaken HC (incl_insert C _ Γ)) (sub_rem_cons _ _ hΔ))
      (olt_vcat α hlt)
  | up n m ρ β βp γ h Δ hnm _ hh hmh hlt ih =>
    intro HrC n0 α Γ hn0 HC hΔ
    refine .up _ m _ _ (vcat α βp) γ h _ hnm (ih HrC n0 α Γ (Nat.le_trans hn0 hnm) HC hΔ) hh hmh ?_
    rw [vcat_assoc]; exact olt_vcat α hlt

/-- The elimination lemma: removing the cuts of the top rank costs one
exponential. Rocq: `Analysis.OmegaLogic.od_elim`. -/
theorem od_elim {n ρ' : Nat} {α : VForm} {Γ : List SForm} (h : OD n ρ' α Γ) :
    ∀ ρ, ρ' = ρ + 1 → 1 ≤ ρ → 3 ≤ n → OD n ρ (V α Z) Γ := by
  induction h with
  | ax n _ α Γ x hx hax => intro _ _ _ _; exact .ax _ _ _ _ x hx hax
  | conj n _ α β Γ x x1 x2 hx hk _ _ hlt ih1 ih2 =>
    intro ρ E hρ hn
    exact .conj _ _ _ (V β Z) _ x x1 x2 hx hk (ih1 ρ E hρ hn) (ih2 ρ E hρ hn)
      (olt_exp (Nat.le_of_succ_le hn) hlt)
  | disj n _ α β Γ x x1 x2 x' hx hk hsel _ hlt ih =>
    intro ρ E hρ hn
    exact .disj _ _ _ (V β Z) _ x x1 x2 x' hx hk hsel (ih ρ E hρ hn) (olt_exp (Nat.le_of_succ_le hn) hlt)
  | univ n _ α β Γ x b A hx hk hD _ hlt ih =>
    intro ρ E hρ hn
    exact .univ _ _ _ (fun i => V (β i) Z) _ x b A hx hk hD
      (fun i => ih i ρ E hρ (Nat.le_trans hn (Nat.le_max_left _ _)))
      (fun i => olt_exp (Nat.le_trans (Nat.le_of_succ_le hn) (Nat.le_max_left _ _)) (hlt i))
  | exis n _ α β Γ x b A m hx hk hm _ hlt ih =>
    intro ρ E hρ hn
    exact .exis _ _ _ (V β Z) _ x b A m hx hk hm (ih ρ E hρ hn) (olt_exp (Nat.le_of_succ_le hn) hlt)
  | cut n ρ'' α β Γ x hr _ _ hlt ih1 ih2 =>
    intro ρ E hρ hn
    subst E
    have H1 := ih1 ρ rfl hρ hn
    have H2 := ih2 ρ rfl hρ hn
    cases Nat.lt_or_ge (rank x.2) ρ with
    | inl hlo => exact .cut _ _ _ (V β Z) _ x hlo H1 H2 (olt_exp (Nat.le_of_succ_le hn) hlt)
    | inr hhi =>
      have Hrx : rank x.2 = ρ := Nat.le_antisymm (Nat.le_of_lt_succ hr) hhi
      have HDx : isD x.2 = false := by
        cases e : isD x.2 with
        | false => rfl
        | true => rw [rank_D e] at Hrx; subst Hrx; exact absurd hρ (Nat.not_succ_le_zero 0)
      obtain ⟨α1, Hα1, Hβ⟩ := hlt
      have Hexp : Reach n (V β Z) (V α1 Z) := reach_exp_mono (Nat.le_of_succ_le hn) Hβ
      have H1' := od_height H1 Hexp
      have H2' := od_height H2 Hexp
      refine od_height ?_ (olt_reach (olt_two hn Hα1))
      cases hk : kindof x with
      | atom => exact absurd (kind_atom_D hk) (fun h => Bool.noConfusion (h.symm.trans HDx))
      | conj x1 x2 =>
        exact od_reduce HDx (.inl ⟨x1, x2, hk⟩) H2' Hrx n (V α1 Z) Γ (Nat.le_refl _) H1'
          (fun y hy => (rem_head _ Γ y hy).elim .inl .inr)
      | disj x1 x2 =>
        exact od_reduce (C := sneg x) HDx (.inl ⟨_, _, kind_disj_neg hk⟩) H1' Hrx n (V α1 Z) Γ (Nat.le_refl _) H2'
          (fun y hy => (rem_head _ Γ y hy).elim (fun e => .inl (e.trans (sneg_sneg x).symm)) .inr)
      | univ b A =>
        exact od_reduce HDx (.inr ⟨b, A, hk⟩) H2' Hrx n (V α1 Z) Γ (Nat.le_refl _) H1'
          (fun y hy => (rem_head _ Γ y hy).elim .inl .inr)
      | exis b A =>
        exact od_reduce (C := sneg x) HDx (.inr ⟨_, _, kind_exis_neg hk⟩) H1' Hrx n (V α1 Z) Γ (Nat.le_refl _) H2'
          (fun y hy => (rem_head _ Γ y hy).elim (fun e => .inl (e.trans (sneg_sneg x).symm)) .inr)
  | up n m _ α β γ h Γ hnm _ hh hmh hlt ih =>
    intro ρ E hρ hn
    have Hm3 : 3 ≤ m := Nat.le_trans hn hnm
    have H1 := ih ρ E hρ Hm3
    obtain ⟨α1, Hα1, Hβγ⟩ := hlt
    have Hβ : Reach n β α1 := reach_trans (reach_prefix _ β γ) Hβγ
    obtain ⟨h', hh'⟩ := hardy_exists (V α1 Z) n
    refine .up _ m _ _ (V α1 Z) (V α1 Z) h' _ hnm ?_ hh' ?_ (olt_two hn Hα1)
    · exact od_height H1 (reach_exp_mono (Nat.le_of_succ_le Hm3) (reach_mono hnm Hβ))
    · obtain ⟨k, hk⟩ := hardy_exists (vcat β γ) n
      obtain ⟨k1, hk1⟩ := hardy_exists α1 n
      exact Nat.le_trans hmh (Nat.le_trans (hardy_vcat_ge β γ hk hh)
        (Nat.le_trans (hardy_mono_reach Hβγ hk hk1)
          (hardy_exp_ge α1 n k1 h' (Nat.le_of_succ_le hn) hk1 hh')))

/-- Rocq: `Analysis.OmegaLogic.otower`. -/
def otower : Nat → VForm → VForm
  | 0, a => a
  | k + 1, a => otower k (V a Z)

/-- Rocq: `Analysis.OmegaLogic.od_elim_all`. -/
theorem od_elim_all : ∀ (k n : Nat) (α : VForm) (Γ : List SForm), OD n (k + 1) α Γ → 3 ≤ n →
    OD n 1 (otower k α) Γ
  | 0, _, _, _, h, _ => h
  | k + 1, n, α, Γ, h, hn => od_elim_all k n (V α Z) Γ (od_elim h (k + 1) rfl (Nat.succ_le_succ (Nat.zero_le k)) hn) hn

/-! ## Bounding

In a derivation of a Σ₁ sequent whose cuts are on bounded formulas only, the
existential witnesses can be bounded: some formula of the sequent is true
with all its witnesses below `H_α(n)`. -/

/-- Rocq: `Analysis.OmegaLogic.isS`. -/
def isS : Form → Bool
  | ex B => isD (ex B) || isS B
  | .eq s t => isD (.eq s t)
  | bot => isD bot
  | conj A B => isD (conj A B)
  | disj A B => isD (disj A B)
  | imp A B => isD (imp A B)
  | all A => isD (all A)

/-- Rocq: `Analysis.OmegaLogic.isS_iff`. -/
theorem isS_iff (A : Form) : isS A = true ↔ isD A = true ∨ ∃ B, A = ex B ∧ isS B = true := by
  cases A with
  | ex B =>
    exact ⟨fun h => (or_true_split h).elim .inl (fun h => .inr ⟨B, rfl, h⟩),
      fun h => h.elim (fun h => by show (isD (ex B) || isS B) = true; rw [h]; rfl)
        (fun ⟨B', e, h⟩ => by
          cases e; show (isD (ex B) || isS B) = true; rw [h]; cases isD (ex B) <;> rfl)⟩
  | eq _ _ => exact ⟨.inl, fun h => h.elim id (fun ⟨_, e, _⟩ => Form.noConfusion e)⟩
  | bot => exact ⟨.inl, fun h => h.elim id (fun ⟨_, e, _⟩ => Form.noConfusion e)⟩
  | conj _ _ => exact ⟨.inl, fun h => h.elim id (fun ⟨_, e, _⟩ => Form.noConfusion e)⟩
  | disj _ _ => exact ⟨.inl, fun h => h.elim id (fun ⟨_, e, _⟩ => Form.noConfusion e)⟩
  | imp _ _ => exact ⟨.inl, fun h => h.elim id (fun ⟨_, e, _⟩ => Form.noConfusion e)⟩
  | all _ => exact ⟨.inl, fun h => h.elim id (fun ⟨_, e, _⟩ => Form.noConfusion e)⟩

/-- Rocq: `Analysis.OmegaLogic.isS_fsubst`. -/
theorem isS_fsubst : ∀ (A : Form) (σ : Nat → ATerm), isS A = true → isS (fsubst σ A) = true
  | ex B, σ, h => by
    cases or_true_split h with
    | inl hd => exact (isS_iff _).2 (.inl (isD_fsubst (ex B) σ hd))
    | inr hs => exact (isS_iff _).2 (.inr ⟨_, rfl, isS_fsubst B (up σ) hs⟩)
  | .eq _ _, σ, h => isD_fsubst (.eq _ _) σ h
  | bot, σ, h => isD_fsubst bot σ h
  | conj A B, σ, h => isD_fsubst (conj A B) σ h
  | disj A B, σ, h => isD_fsubst (disj A B) σ h
  | imp A B, σ, h => isD_fsubst (imp A B) σ h
  | all A, σ, h => isD_fsubst (all A) σ h

/-- Rocq: `Analysis.OmegaLogic.sigf`. -/
def Sigf (s : SForm) : Prop := (s.1 = true ∧ isS s.2 = true) ∨ isD s.2 = true

/-- Rocq: `Analysis.OmegaLogic.tb`. -/
def tb (B : Nat) : (Nat → Nat) → Form → Prop
  | ρ, ex A => if isD (ex A) = true then deval ρ (ex A) = true else ∃ m, m < B ∧ tb B (scons m ρ) A
  | ρ, .eq s t => if isD (.eq s t) = true then deval ρ (.eq s t) = true else False
  | ρ, bot => if isD bot = true then deval ρ bot = true else False
  | ρ, conj A C => if isD (conj A C) = true then deval ρ (conj A C) = true else False
  | ρ, disj A C => if isD (disj A C) = true then deval ρ (disj A C) = true else False
  | ρ, imp A C => if isD (imp A C) = true then deval ρ (imp A C) = true else False
  | ρ, all A => if isD (all A) = true then deval ρ (all A) = true else False

/-- The non-bounded case of `tb`. -/
def tbMatch (B : Nat) (ρ : Nat → Nat) : Form → Prop
  | ex A => ∃ m, m < B ∧ tb B (scons m ρ) A
  | .eq _ _ => False
  | bot => False
  | conj _ _ => False
  | disj _ _ => False
  | imp _ _ => False
  | all _ => False

/-- Rocq: `Analysis.OmegaLogic.tb_eq`. -/
theorem tb_eq (B : Nat) (ρ : Nat → Nat) (A : Form) :
    tb B ρ A = if isD A = true then deval ρ A = true else tbMatch B ρ A := by
  cases A <;> rfl

/-- Rocq: `Analysis.OmegaLogic.Tbs`. -/
def Tbs (B : Nat) : SForm → Prop
  | (true, A) => tb B ρ0 A
  | (false, A) => isD A = true ∧ deval ρ0 A = false

theorem tb_D_cases {B : Nat} {ρ : Nat → Nat} {A : Form} (h : tb B ρ A) :
    (isD A = true ∧ deval ρ A = true) ∨ (isD A = false ∧ tbMatch B ρ A) := by
  rw [tb_eq] at h
  cases hd : isD A with
  | true => rw [ite_eq_left hd] at h; exact .inl ⟨rfl, h⟩
  | false => rw [ite_eq_right (fun e => Bool.noConfusion (e.symm.trans hd))] at h; exact .inr ⟨rfl, h⟩

theorem tb_of_D {B : Nat} {ρ : Nat → Nat} {A : Form} (hd : isD A = true) (hv : deval ρ A = true) : tb B ρ A := by
  rw [tb_eq, ite_eq_left hd]; exact hv

theorem tb_of_match {B : Nat} {ρ : Nat → Nat} {A : Form} (hd : isD A = false) (hm : tbMatch B ρ A) : tb B ρ A := by
  rw [tb_eq, ite_eq_right (fun e => Bool.noConfusion (e.symm.trans hd))]; exact hm

/-- Rocq: `Analysis.OmegaLogic.tb_mono`. -/
theorem tb_mono {B B' : Nat} (hB : B ≤ B') : ∀ (A : Form) (ρ : Nat → Nat), tb B ρ A → tb B' ρ A := by
  intro A
  induction A with
  | ex A ih =>
    intro ρ h
    rcases tb_D_cases h with ⟨hd, hv⟩ | ⟨hd, ⟨m, hm, ht⟩⟩
    · exact tb_of_D hd hv
    · exact tb_of_match hd ⟨m, Nat.lt_of_lt_of_le hm hB, ih _ ht⟩
  | eq | bot | conj | disj | imp | all =>
    intro ρ h
    rcases tb_D_cases h with ⟨hd, hv⟩ | ⟨_, hm⟩
    · exact tb_of_D hd hv
    · exact hm.elim

/-- Rocq: `Analysis.OmegaLogic.tb_ext`. -/
theorem tb_ext (B : Nat) : ∀ (A : Form) {ρ ρ' : Nat → Nat}, (∀ i, ρ i = ρ' i) → tb B ρ A → tb B ρ' A := by
  intro A
  induction A with
  | ex A ih =>
    intro ρ ρ' E h
    rcases tb_D_cases h with ⟨hd, hv⟩ | ⟨hd, ⟨m, hm, ht⟩⟩
    · exact tb_of_D hd ((deval_ext _ hd E).symm.trans hv)
    · exact tb_of_match hd ⟨m, hm, ih (scons_ext E m) ht⟩
  | eq | bot | conj | disj | imp | all =>
    intro ρ ρ' E h
    rcases tb_D_cases h with ⟨hd, hv⟩ | ⟨_, hm⟩
    · exact tb_of_D hd ((deval_ext _ hd E).symm.trans hv)
    · exact hm.elim

/-- Rocq: `Analysis.OmegaLogic.tb_fsubst`. -/
theorem tb_fsubst (B : Nat) : ∀ (A : Form) (ρ : Nat → Nat) (σ : Nat → ATerm),
    tb B ρ (fsubst σ A) → tb B (fun i => teval ρ (σ i)) A := by
  intro A
  induction A with
  | ex A ih =>
    intro ρ σ h
    rcases tb_D_cases h with ⟨hd, hv⟩ | ⟨hd, ⟨m, hm, ht⟩⟩
    · have hd' := isD_fsubst_back _ σ hd
      exact tb_of_D hd' ((deval_fsubst _ σ ρ hd').symm.trans hv)
    · exact tb_of_match ((isD_fsubst_eq _ σ).symm.trans hd) ⟨m, hm, tb_ext B A (up_env ρ σ m) (ih _ _ ht)⟩
  | eq | bot | conj | disj | imp | all =>
    intro ρ σ h
    rcases tb_D_cases h with ⟨hd, hv⟩ | ⟨_, hm⟩
    · have hd' := isD_fsubst_back _ σ hd
      exact tb_of_D hd' ((deval_fsubst _ σ ρ hd').symm.trans hv)
    · exact hm.elim

/-- Rocq: `Analysis.OmegaLogic.Tbs_mono`. -/
theorem Tbs_mono {B B' : Nat} (hB : B ≤ B') : ∀ s : SForm, Tbs B s → Tbs B' s
  | (true, A) => tb_mono hB A ρ0
  | (false, _) => id

/-- Rocq: `Analysis.OmegaLogic.Tbs_dax`. -/
theorem Tbs_dax (B : Nat) : ∀ s : SForm, Dax s → Tbs B s
  | (true, A), ⟨hD, hv⟩ => by
    show tb B ρ0 A
    rw [tb_eq, ite_eq_left hD]; exact hv
  | (false, _), h => h

/-- Rocq: `Analysis.OmegaLogic.Tbs_dfalse`. -/
theorem Tbs_dfalse (B : Nat) : ∀ s : SForm, Dfalse s → Tbs B s → False
  | (true, A), ⟨hD, hv⟩, h => by
    have h' : tb B ρ0 A := h
    rw [tb_eq, ite_eq_left hD] at h'
    exact Bool.noConfusion (h'.symm.trans hv)
  | (false, _), ⟨_, hv⟩, ⟨_, h⟩ => Bool.noConfusion (hv.symm.trans h)

/-- Rocq: `Analysis.OmegaLogic.sigf_D`. -/
theorem sigf_D (s : SForm) (hD : isD s.2 = false) (h : Sigf s) : ∃ A, s = (true, ex A) ∧ isS A = true := by
  rcases h with ⟨hb, hS⟩ | h
  · rcases (isS_iff _).1 hS with h | ⟨B, e, hB⟩
    · exact absurd (h.symm.trans hD) (fun h => Bool.noConfusion h)
    · cases s with
      | mk b A => cases hb; cases e; exact ⟨B, rfl, hB⟩
  · exact absurd (h.symm.trans hD) (fun h => Bool.noConfusion h)

theorem sig_cons {x : SForm} {Γ : List SForm} (hx : Sigf x) (hΓ : ∀ s, s ∈ Γ → Sigf s) :
    ∀ s, s ∈ x :: Γ → Sigf s
  | _, .head _ => hx
  | _, .tail _ h => hΓ _ h

theorem found_tail {x : SForm} {Γ : List SForm} {B B' : Nat} (hB : B ≤ B') (hx : Dfalse x)
    (h : ∃ s, s ∈ x :: Γ ∧ Tbs B s) : ∃ s, s ∈ Γ ∧ Tbs B' s :=
  let ⟨s, hs, ht⟩ := h
  match s, hs, ht with
  | _, .head _, ht => absurd ht (Tbs_dfalse B x hx)
  | s, .tail _ hs, ht => ⟨s, hs, Tbs_mono hB s ht⟩

/-- Rocq: `Analysis.OmegaLogic.od_bounding`. -/
theorem od_bounding {n ρ : Nat} {α : VForm} {Γ : List SForm} (h : OD n ρ α Γ) :
    ρ ≤ 1 → (∀ s, s ∈ Γ → Sigf s) → ∀ h, Hardy α n h → ∃ s, s ∈ Γ ∧ Tbs h s := by
  induction h with
  | ax n ρ α Γ s hs hax => intro _ _ hα _; exact ⟨s, hs, Tbs_dax _ s hax⟩
  | conj n ρ α β Γ s s1 s2 hs hk _ _ hlt ih1 ih2 =>
    intro hρ hΓ hα Hα
    cases hD : isD s.2 with
    | false =>
      obtain ⟨A, e, _⟩ := sigf_D s hD (hΓ s hs)
      rw [e] at hk; exact Kind.noConfusion hk
    | true =>
      cases dax_dec s hD with
      | inl hax => exact ⟨s, hs, Tbs_dax _ s hax⟩
      | inr hf =>
        obtain ⟨hβ, Hβ⟩ := hardy_exists β n
        have hle := olt_hardy hlt Hβ Hα
        have ⟨hD1, hD2⟩ := isD_conj hk hD
        cases dfalse_conj hk hf with
        | inl h1 => exact found_tail hle h1 (ih1 hρ (sig_cons (.inr hD1) hΓ) hβ Hβ)
        | inr h2 => exact found_tail hle h2 (ih2 hρ (sig_cons (.inr hD2) hΓ) hβ Hβ)
  | disj n ρ α β Γ s s1 s2 s' hs hk hsel _ hlt ih =>
    intro hρ hΓ hα Hα
    cases hD : isD s.2 with
    | false =>
      obtain ⟨A, e, _⟩ := sigf_D s hD (hΓ s hs)
      rw [e] at hk; exact Kind.noConfusion hk
    | true =>
      cases dax_dec s hD with
      | inl hax => exact ⟨s, hs, Tbs_dax _ s hax⟩
      | inr hf =>
        obtain ⟨hβ, Hβ⟩ := hardy_exists β n
        have hle := olt_hardy hlt Hβ Hα
        have ⟨hD1, hD2⟩ := isD_disj hk hD
        have ⟨h1, h2⟩ := dfalse_disj hk hf
        have hDs' : isD s'.2 = true := hsel.elim (fun e => e ▸ hD1) (fun e => e ▸ hD2)
        have hfs' : Dfalse s' := hsel.elim (fun e => e ▸ h1) (fun e => e ▸ h2)
        exact found_tail hle hfs' (ih hρ (sig_cons (.inr hDs') hΓ) hβ Hβ)
  | univ n ρ α β Γ s b A hs hk hD _ _ _ =>
    intro _ hΓ _ _
    obtain ⟨A', e, _⟩ := sigf_D s hD (hΓ s hs)
    rw [e] at hk; exact Kind.noConfusion hk
  | exis n ρ α β Γ s b A m hs hk hm _ hlt ih =>
    intro hρ hΓ hα Hα
    obtain ⟨hβ, Hβ⟩ := hardy_exists β n
    have hle := olt_hardy hlt Hβ Hα
    have hmα : m < hα := Nat.lt_of_lt_of_le hm (hardy_ge Hα)
    cases hD : isD s.2 with
    | true =>
      cases dax_dec s hD with
      | inl hax => exact ⟨s, hs, Tbs_dax _ s hax⟩
      | inr hf =>
        have hfi := dfalse_exis m hk hf
        exact found_tail hle hfi (ih hρ (sig_cons (.inr hfi.1) hΓ) hβ Hβ)
    | false =>
      obtain ⟨A', e, hS⟩ := sigf_D s hD (hΓ s hs)
      subst e
      injection hk with e1 e2
      cases e1
      cases e2
      have hsi : Sigf (inst true A m) := .inl ⟨rfl, isS_fsubst A _ hS⟩
      obtain ⟨x, hx, ht⟩ := ih hρ (sig_cons hsi hΓ) hβ Hβ
      cases hx with
      | head =>
        refine ⟨(true, ex A), hs, ?_⟩
        show tb hα ρ0 (ex A)
        rw [tb_eq, ite_eq_right (fun e => Bool.noConfusion (e.symm.trans hD))]
        refine ⟨m, hmα, tb_mono hle A _ (tb_ext hβ A ?_ (tb_fsubst hβ A ρ0 _ ht))⟩
        intro i
        cases i with
        | zero => exact teval_num ρ0 m
        | succ i => rfl
      | tail _ hx => exact ⟨x, hx, Tbs_mono hle x ht⟩
  | cut n ρ α β Γ x hr _ _ hlt ih1 ih2 =>
    intro hρ hΓ hα Hα
    obtain ⟨hβ, Hβ⟩ := hardy_exists β n
    have hle := olt_hardy hlt Hβ Hα
    have hDx : isD x.2 = true := rank_0_D (Nat.le_zero.mp (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr hρ)))
    cases dax_dec x hDx with
    | inl hax =>
      have hf : Dfalse (sneg x) := (dfalse_sneg (sneg x)).2 (by rw [sneg_sneg]; exact hax)
      exact found_tail hle hf (ih2 hρ (sig_cons (.inr hDx) hΓ) hβ Hβ)
    | inr hf => exact found_tail hle hf (ih1 hρ (sig_cons (.inr hDx) hΓ) hβ Hβ)
  | up n m ρ α β γ h Γ _ _ hh hmh hlt ih =>
    intro hρ hΓ hα Hα
    obtain ⟨hm, Hm⟩ := hardy_exists β m
    obtain ⟨hβh, Hβh⟩ := hardy_exists β h
    obtain ⟨x, hx, ht⟩ := ih hρ hΓ hm Hm
    exact ⟨x, hx, Tbs_mono (Nat.le_trans (hardy_mono_arg β hmh Hm Hβh)
      (olt_hardy hlt (hardy_vcat β hh Hβh) Hα)) x ht⟩

/-- A Σ₁ sentence `∃y. θ` with `θ` bounded, derived without unbounded cuts at
height `α` and control `n`, has a witness below `H_α(n)`.
Rocq: `Analysis.OmegaLogic.od_witness`. -/
theorem od_witness {n : Nat} {α : VForm} {A : Form} {h : Nat} (H : OD n 1 α [(true, ex A)])
    (HA : isD A = true) (HE : isD (ex A) = false) (Hh : Hardy α n h) :
    ∃ m, m < h ∧ sat ρ0 (sub1 A (num m)) := by
  have hsig : ∀ s, s ∈ [(true, ex A)] → Sigf s := by
    intro s hs
    cases hs with
    | head => exact .inl ⟨rfl, (isS_iff _).2 (.inr ⟨A, rfl, (isS_iff A).2 (.inl HA)⟩)⟩
    | tail _ h => cases h
  obtain ⟨s, hs, ht⟩ := od_bounding H (Nat.le_refl 1) hsig h Hh
  cases hs with
  | tail _ h => cases h
  | head =>
    have ht' : tb h ρ0 (ex A) := ht
    rw [tb_eq, ite_eq_right (fun e => Bool.noConfusion (e.symm.trans HE))] at ht'
    obtain ⟨m, hm, hmt⟩ := ht'
    rw [tb_eq, ite_eq_left HA] at hmt
    exact ⟨m, hm, (sat_sub1_num ρ0 A m).2 ((deval_sat HA _).1 hmt)⟩

end ConstructiveOrdinals.OmegaLogic
