import ConstructiveOrdinals.Analysis.Embedding
import ConstructiveOrdinals.Cantor
import ConstructiveOrdinals.WellFounded

/-!
# Peano arithmetic proves transfinite induction only below ε₀

Port of `Ordinal/Analysis/ProvableTI.v`.

Let `≺` be given by a bounded formula `R`, with `y ≺ x` when `R` holds of `y`
(variable `0`) and `x` (variable `1`). Transfinite induction along `≺` is the
sentence `TI(R)` of `PA(X)`: `Prog(X) → ∀x X(x)`, where `Prog(X)` is
`∀x (∀y (y ≺ x → X y) → X x)`.

If PA proves `TI(R)`, then `≺` has height below ε₀ (`PA_TI_bound`): for some
`L < ε₀`, every `x` is `below L`. The proof is the _boundedness_ argument of
Gentzen and Schütte: embed the proof in the ω-logic, eliminate the cuts down
to bounded formulas (`od_elim_all`), and show by induction on a derivation of
height `α` of a sequent `¬Prog(X), Δ` that `Δ` holds when `X` is read as
"below level `γ + ω^α`", where `γ` bounds the negated `X`-atoms
(`od_TI_bound`).

A classical proof of `TI(R)` carries only "not not" information about
well-foundedness, so the conclusion is stated classically: `below L x` says
that each predecessor of `x` is not not below some predecessor of `L`. This
is the faithful constructive reading of "PA proves `≺` well-founded"; it
excludes infinite descending sequences (`PA_TI_no_descent`). Only the
classical corollary `PA_TI_wf_EM`, which gives well-foundedness with order
type below ε₀, assumes the excluded middle, as an explicit hypothesis.

Lean notes:

- Rocq's `excluded_middle` is `ExcludedMiddle`, and `well_founded` is
  `WellFounded`.
- The section variables `Q` and `HQ` of Rocq's `Bounding` section are
  explicit arguments.
- Rocq proves the propositional steps with `tauto`; here they are written out.
-/

namespace ConstructiveOrdinals.ProvableTI

open Ordinal PeanoArith ATerm Form Hardy VNotation VForm OmegaLogic Embedding

/-! ## Transfinite induction as a sentence -/

/-- Rocq: `Analysis.ProvableTI.ProgB`. -/
def ProgB (R : Form) : Form := imp (all (imp R (px (tv 0)))) (px (tv 0))

/-- Rocq: `Analysis.ProvableTI.Prog`. -/
def Prog (R : Form) : Form := all (ProgB R)

/-- Rocq: `Analysis.ProvableTI.TI`. -/
def TI (R : Form) : Form := imp (Prog R) (all (px (tv 0)))

/-- `prec R y x`: `y ≺ x`; the other free variables of `R` are `0`.
Rocq: `Analysis.ProvableTI.prec`. -/
def prec (R : Form) (y x : Nat) : Prop := sat (scons y (scons x ρ0)) R

/-! ## Height below an ordinal, classically -/

section Below

variable (P : Nat → Nat → Prop)

/-- `below L x`: every predecessor of `x` is (classically) below some
predecessor of `L`. Rocq: `Analysis.ProvableTI.below`. -/
def below : Ordinal.{0} → Nat → Prop
  | ⟨A, f⟩, x => ∀ y, P y x → ¬¬∃ a : A, below (f a) y

/-- Rocq: `Analysis.ProvableTI.below_stable`. -/
theorem below_stable : ∀ (L : Ordinal.{0}) (x : Nat), ¬¬below P L x → below P L x
  | ⟨_, _⟩, _, H => fun y hy hn => H (fun H' => H' y hy hn)

/-- Rocq: `Analysis.ProvableTI.below_mono`. -/
theorem below_mono : ∀ (L L' : Ordinal.{0}) (x : Nat), L ≤ L' → below P L x → below P L' x
  | ⟨A, f⟩, ⟨B, g⟩, _, hle, H => fun y hy hn => H y hy (fun ⟨a, ha⟩ => by
      obtain ⟨b, hb⟩ := lt_elim (le_elim hle a)
      exact hn ⟨b, below_mono (f a) (g b) y hb ha⟩)

/-- Rocq: `Analysis.ProvableTI.below_succ`. -/
theorem below_succ (L : Ordinal.{0}) (x : Nat) (H : ∀ y, P y x → below P L y) : below P (Ordinal.succ L) x :=
  fun y hy hn => hn ⟨PUnit.unit, H y hy⟩

/-- No infinite descending sequence starts below an ordinal.
Rocq: `Analysis.ProvableTI.below_no_descent`. -/
theorem below_no_descent : ∀ (L : Ordinal.{0}) (f : Nat → Nat), below P L (f 0) →
    (∀ i, P (f (i + 1)) (f i)) → False
  | ⟨_, g⟩, f, H, hd => H (f 1) (hd 0) (fun ⟨a, ha⟩ =>
      below_no_descent (g a) (fun i => f (i + 1)) ha (fun i => hd (i + 1)))

/-- With the excluded middle, `below` is the usual rank bound.
Rocq: `Analysis.ProvableTI.below_Acc_EM`. -/
theorem below_Acc_EM (EM : ExcludedMiddle) : ∀ (L : Ordinal.{0}) (x : Nat), below P L x → Acc P x
  | ⟨A, f⟩, x, H => Acc.intro x fun y hy =>
      (EM (∃ a : A, below P (f a) y)).elim (fun ⟨a, ha⟩ => below_Acc_EM EM (f a) y ha)
        (fun hn => (H y hy hn).elim)

/-- Rocq: `Analysis.ProvableTI.below_wf_ord_EM`. -/
theorem below_wf_ord_EM (EM : ExcludedMiddle) :
    ∀ (L : Ordinal.{0}) (x : Nat) (hx : Acc P x), below P L x → mkWfOrd P x hx ≤ L
  | ⟨A, f⟩, x, hx, H => by
    rw [mkWfOrd_unfold]
    refine le_intro fun ⟨y, hy⟩ => ?_
    rcases EM (∃ a : A, below P (f a) y) with ⟨a, ha⟩ | hn
    · exact lt_intro (y := ⟨A, f⟩) a (below_wf_ord_EM EM (f a) y _ ha)
    · exact (H y hy hn).elim

end Below

/-- Rocq: `Analysis.ProvableTI.below_ext`. -/
theorem below_ext (P P' : Nat → Nat → Prop) (hP : ∀ y x, P' y x → P y x) :
    ∀ (L : Ordinal.{0}) (x : Nat), below P L x → below P' L x
  | ⟨_, f⟩, x, H => fun y hy hn => H y (hP y x hy) (fun ⟨a, ha⟩ => hn ⟨a, below_ext P P' hP (f a) y ha⟩)

/-! ## A negative semantics for formulas with `X`

Disjunction and existence are read classically, so every formula is stable
when `X` is. -/

/-- Rocq: `Analysis.ProvableTI.nsat`. -/
def nsat (X : Nat → Prop) : (Nat → Nat) → Form → Prop
  | ρ, .eq s t => teval ρ s = teval ρ t
  | _, bot => False
  | ρ, conj A B => nsat X ρ A ∧ nsat X ρ B
  | ρ, disj A B => ¬(¬nsat X ρ A ∧ ¬nsat X ρ B)
  | ρ, imp A B => nsat X ρ A → nsat X ρ B
  | ρ, all A => ∀ x, nsat X (scons x ρ) A
  | ρ, ex A => ¬∀ x, ¬nsat X (scons x ρ) A
  | ρ, px t => X (teval ρ t)

/-- Rocq: `Analysis.ProvableTI.nsat_ext`. -/
theorem nsat_ext (X : Nat → Prop) : ∀ (A : Form) {ρ ρ' : Nat → Nat}, (∀ i, ρ i = ρ' i) →
    (nsat X ρ A ↔ nsat X ρ' A)
  | .eq s t, _, _, h => by
    show teval _ s = teval _ t ↔ teval _ s = teval _ t
    rw [teval_ext h s, teval_ext h t]
  | bot, _, _, _ => Iff.rfl
  | conj A B, _, _, h => ⟨fun ⟨a, b⟩ => ⟨(nsat_ext X A h).1 a, (nsat_ext X B h).1 b⟩,
      fun ⟨a, b⟩ => ⟨(nsat_ext X A h).2 a, (nsat_ext X B h).2 b⟩⟩
  | disj A B, _, _, h => ⟨fun H ⟨na, nb⟩ => H ⟨fun a => na ((nsat_ext X A h).1 a), fun b => nb ((nsat_ext X B h).1 b)⟩,
      fun H ⟨na, nb⟩ => H ⟨fun a => na ((nsat_ext X A h).2 a), fun b => nb ((nsat_ext X B h).2 b)⟩⟩
  | imp A B, _, _, h => ⟨fun f a => (nsat_ext X B h).1 (f ((nsat_ext X A h).2 a)),
      fun f a => (nsat_ext X B h).2 (f ((nsat_ext X A h).1 a))⟩
  | all A, _, _, h => ⟨fun f x => (nsat_ext X A (scons_ext h x)).1 (f x),
      fun f x => (nsat_ext X A (scons_ext h x)).2 (f x)⟩
  | ex A, _, _, h => ⟨fun H hn => H (fun x hx => hn x ((nsat_ext X A (scons_ext h x)).1 hx)),
      fun H hn => H (fun x hx => hn x ((nsat_ext X A (scons_ext h x)).2 hx))⟩
  | px t, _, _, h => by
    show X (teval _ t) ↔ X (teval _ t)
    rw [teval_ext h t]

/-- Rocq: `Analysis.ProvableTI.nsat_fsubst`. -/
theorem nsat_fsubst (X : Nat → Prop) : ∀ (A : Form) (ρ : Nat → Nat) (σ : Nat → ATerm),
    nsat X ρ (fsubst σ A) ↔ nsat X (fun i => teval ρ (σ i)) A
  | .eq s t, ρ, σ => by
    show teval ρ (asubst σ s) = teval ρ (asubst σ t) ↔ _
    rw [teval_asubst, teval_asubst]; exact Iff.rfl
  | bot, _, _ => Iff.rfl
  | conj A B, ρ, σ => ⟨fun ⟨a, b⟩ => ⟨(nsat_fsubst X A ρ σ).1 a, (nsat_fsubst X B ρ σ).1 b⟩,
      fun ⟨a, b⟩ => ⟨(nsat_fsubst X A ρ σ).2 a, (nsat_fsubst X B ρ σ).2 b⟩⟩
  | disj A B, ρ, σ =>
    ⟨fun H ⟨na, nb⟩ => H ⟨fun a => na ((nsat_fsubst X A ρ σ).1 a), fun b => nb ((nsat_fsubst X B ρ σ).1 b)⟩,
     fun H ⟨na, nb⟩ => H ⟨fun a => na ((nsat_fsubst X A ρ σ).2 a), fun b => nb ((nsat_fsubst X B ρ σ).2 b)⟩⟩
  | imp A B, ρ, σ => ⟨fun f a => (nsat_fsubst X B ρ σ).1 (f ((nsat_fsubst X A ρ σ).2 a)),
      fun f a => (nsat_fsubst X B ρ σ).2 (f ((nsat_fsubst X A ρ σ).1 a))⟩
  | all A, ρ, σ =>
    ⟨fun f x => (nsat_ext X A (up_env ρ σ x)).1 ((nsat_fsubst X A (scons x ρ) (up σ)).1 (f x)),
     fun f x => (nsat_fsubst X A (scons x ρ) (up σ)).2 ((nsat_ext X A (up_env ρ σ x)).2 (f x))⟩
  | ex A, ρ, σ =>
    ⟨fun H hn => H (fun x hx => hn x ((nsat_ext X A (up_env ρ σ x)).1 ((nsat_fsubst X A (scons x ρ) (up σ)).1 hx))),
     fun H hn => H (fun x hx => hn x ((nsat_fsubst X A (scons x ρ) (up σ)).2 ((nsat_ext X A (up_env ρ σ x)).2 hx)))⟩
  | px t, ρ, σ => by
    show X (teval ρ (asubst σ t)) ↔ _
    rw [teval_asubst]; exact Iff.rfl

/-- Rocq: `Analysis.ProvableTI.nsat_sub1_num`. -/
theorem nsat_sub1_num (X : Nat → Prop) (ρ : Nat → Nat) (A : Form) (i : Nat) :
    nsat X ρ (sub1 A (num i)) ↔ nsat X (scons i ρ) A := by
  have h := (nsat_fsubst X A ρ (inst1 (num i))).trans (nsat_ext X A (inst1_env ρ (num i)))
  rw [teval_num] at h
  exact h

/-- Rocq: `Analysis.ProvableTI.nsat_stable`. -/
theorem nsat_stable (X : Nat → Prop) (HX : ∀ n, ¬¬X n → X n) :
    ∀ (A : Form) (ρ : Nat → Nat), ¬¬nsat X ρ A → nsat X ρ A
  | .eq s t, ρ, H => by
    cases Nat.decEq (teval ρ s) (teval ρ t) with
    | isTrue e => exact e
    | isFalse ne => exact (H ne).elim
  | bot, _, H => H id
  | conj A B, ρ, H => ⟨nsat_stable X HX A ρ (fun hn => H (fun ⟨a, _⟩ => hn a)),
      nsat_stable X HX B ρ (fun hn => H (fun ⟨_, b⟩ => hn b))⟩
  | disj _ _, _, H => fun hn => H (fun h => h hn)
  | imp _ B, ρ, H => fun a => nsat_stable X HX B ρ (fun hn => H (fun f => hn (f a)))
  | all A, ρ, H => fun x => nsat_stable X HX A (scons x ρ) (fun hn => H (fun f => hn (f x)))
  | ex _, _, H => fun hn => H (fun h => h hn)
  | px _, _, H => HX _ H

/-- Rocq: `Analysis.ProvableTI.sat_dec_D`. -/
theorem sat_dec_D {A : Form} (ρ : Nat → Nat) (h : isD A = true) : sat ρ A ∨ ¬sat ρ A := by
  cases e : deval ρ A with
  | true => exact .inl ((deval_sat h ρ).1 e)
  | false => exact .inr ((deval_false ρ h).1 e)

/-- On bounded formulas the negative semantics is the usual one.
Rocq: `Analysis.ProvableTI.nsat_DP`. -/
theorem nsat_DP (X : Nat → Prop) {A : Form} (h : DP A) : ∀ ρ, nsat X ρ A ↔ sat ρ A := by
  induction h with
  | eq => intro _; exact Iff.rfl
  | bot => intro _; exact Iff.rfl
  | conj _ _ _ _ ihA ihB =>
    intro ρ
    exact ⟨fun ⟨a, b⟩ => ⟨(ihA ρ).1 a, (ihB ρ).1 b⟩, fun ⟨a, b⟩ => ⟨(ihA ρ).2 a, (ihB ρ).2 b⟩⟩
  | disj _ _ hA hB ihA ihB =>
    intro ρ
    refine ⟨fun H => ?_, fun H ⟨na, nb⟩ => H.elim (fun a => na ((ihA ρ).2 a)) (fun b => nb ((ihB ρ).2 b))⟩
    rcases sat_dec_D ρ (DP_isD hA) with a | na
    · exact .inl a
    · rcases sat_dec_D ρ (DP_isD hB) with b | nb
      · exact .inr b
      · exact (H ⟨fun a => na ((ihA ρ).1 a), fun b => nb ((ihB ρ).1 b)⟩).elim
  | imp _ _ _ _ ihA ihB =>
    intro ρ
    exact ⟨fun f a => (ihB ρ).1 (f ((ihA ρ).2 a)), fun f a => (ihB ρ).2 (f ((ihA ρ).1 a))⟩
  | ball v _ h0 _ _ ih =>
    intro ρ
    have HG : isD (ex (.eq (tplus (tv 1) (tv 0)) v)) = true := DP_isD (.bex _ _ rfl h0)
    refine ⟨fun H x ⟨d, hd⟩ => (ih (scons x ρ)).1 (H x (fun hn => hn d hd)), fun H x hx => (ih (scons x ρ)).2 (H x ?_)⟩
    rcases sat_dec_D (scons x ρ) HG with hs | hs
    · exact hs
    · exact (hx (fun d hd => hs ⟨d, hd⟩)).elim
  | bex u v hu hv =>
    intro ρ
    have HG : isD (ex (.eq (tplus u (tv 0)) v)) = true := DP_isD (.bex u v hu hv)
    refine ⟨fun H => ?_, fun ⟨d, hd⟩ hn => hn d hd⟩
    rcases sat_dec_D ρ HG with hs | hs
    · exact hs
    · exact (H (fun d hd => hs ⟨d, hd⟩)).elim

/-- Rocq: `Analysis.ProvableTI.nsat_D`. -/
theorem nsat_D (X : Nat → Prop) (A : Form) (ρ : Nat → Nat) (h : isD A = true) : nsat X ρ A ↔ sat ρ A :=
  nsat_DP X (isD_DP h) ρ

/-! ### Polarity of `X` -/

/-- Rocq: `Analysis.ProvableTI.xpol`. -/
def xpol : Bool → Form → Bool
  | _, .eq _ _ => true
  | _, bot => true
  | p, conj A B => xpol p A && xpol p B
  | p, disj A B => xpol p A && xpol p B
  | p, imp A B => xpol (!p) A && xpol p B
  | p, all A => xpol p A
  | p, ex A => xpol p A
  | p, px _ => p

/-- Rocq: `Analysis.ProvableTI.xpol_fsubst`. -/
theorem xpol_fsubst : ∀ (A : Form) (p : Bool) (σ : Nat → ATerm), xpol p (fsubst σ A) = xpol p A
  | .eq _ _, _, _ => rfl
  | bot, _, _ => rfl
  | conj A B, p, σ => congrArg₂ (· && ·) (xpol_fsubst A p σ) (xpol_fsubst B p σ)
  | disj A B, p, σ => congrArg₂ (· && ·) (xpol_fsubst A p σ) (xpol_fsubst B p σ)
  | imp A B, p, σ => congrArg₂ (· && ·) (xpol_fsubst A (!p) σ) (xpol_fsubst B p σ)
  | all A, p, σ => xpol_fsubst A p (up σ)
  | ex A, p, σ => xpol_fsubst A p (up σ)
  | px _, _, _ => rfl

/-- Rocq: `Analysis.ProvableTI.xpol_DP`. -/
theorem xpol_DP {A : Form} (h : DP A) : ∀ p, xpol p A = true := by
  induction h with
  | eq => intro _; rfl
  | bot => intro _; rfl
  | conj _ _ _ _ ih1 ih2 => intro p; show (xpol p _ && xpol p _) = true; rw [ih1, ih2]; rfl
  | disj _ _ _ _ ih1 ih2 => intro p; show (xpol p _ && xpol p _) = true; rw [ih1, ih2]; rfl
  | imp _ _ _ _ ih1 ih2 => intro p; show (xpol (!p) _ && xpol p _) = true; rw [ih1, ih2]; rfl
  | ball v B _ _ _ ih => intro p; show (xpol (!p) (ex (.eq (tplus (tv 1) (tv 0)) v)) && xpol p B) = true; rw [ih]; rfl
  | bex => intro _; rfl

/-- Rocq: `Analysis.ProvableTI.xpol_D`. -/
theorem xpol_D (p : Bool) (A : Form) (h : isD A = true) : xpol p A = true := xpol_DP (isD_DP h) p

/-- Formulas in which `X` is positive are monotone in `X`.
Rocq: `Analysis.ProvableTI.nsat_mono`. -/
theorem nsat_mono (X Y : Nat → Prop) (HXY : ∀ n, X n → Y n) : ∀ (A : Form) (p : Bool) (ρ : Nat → Nat),
    xpol p A = true → (p = true → nsat X ρ A → nsat Y ρ A) ∧ (p = false → nsat Y ρ A → nsat X ρ A)
  | .eq _ _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | bot, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | conj A B, p, ρ, hp =>
    have ⟨h1, h2⟩ := and_true_split hp
    have ⟨a1, a2⟩ := nsat_mono X Y HXY A p ρ h1
    have ⟨b1, b2⟩ := nsat_mono X Y HXY B p ρ h2
    ⟨fun e ⟨a, b⟩ => ⟨a1 e a, b1 e b⟩, fun e ⟨a, b⟩ => ⟨a2 e a, b2 e b⟩⟩
  | disj A B, p, ρ, hp =>
    have ⟨h1, h2⟩ := and_true_split hp
    have ⟨a1, a2⟩ := nsat_mono X Y HXY A p ρ h1
    have ⟨b1, b2⟩ := nsat_mono X Y HXY B p ρ h2
    ⟨fun e H ⟨na, nb⟩ => H ⟨fun a => na (a1 e a), fun b => nb (b1 e b)⟩,
     fun e H ⟨na, nb⟩ => H ⟨fun a => na (a2 e a), fun b => nb (b2 e b)⟩⟩
  | imp A B, p, ρ, hp =>
    have ⟨h1, h2⟩ := and_true_split hp
    have ⟨a1, a2⟩ := nsat_mono X Y HXY A (!p) ρ h1
    have ⟨b1, b2⟩ := nsat_mono X Y HXY B p ρ h2
    ⟨fun e f a => b1 e (f (a2 (by rw [e]; rfl) a)), fun e f a => b2 e (f (a1 (by rw [e]; rfl) a))⟩
  | all A, p, ρ, hp => ⟨fun e f x => (nsat_mono X Y HXY A p (scons x ρ) hp).1 e (f x),
      fun e f x => (nsat_mono X Y HXY A p (scons x ρ) hp).2 e (f x)⟩
  | ex A, p, ρ, hp => ⟨fun e H hn => H (fun x hx => hn x ((nsat_mono X Y HXY A p (scons x ρ) hp).1 e hx)),
      fun e H hn => H (fun x hx => hn x ((nsat_mono X Y HXY A p (scons x ρ) hp).2 e hx))⟩
  | px _, p, _, hp => ⟨fun _ h => HXY _ h,
      fun e _ => absurd ((show p = true from hp).symm.trans e) (fun h => Bool.noConfusion h)⟩

/-! ### Signed formulas -/

/-- Rocq: `Analysis.ProvableTI.spos`. -/
def Spos (s : SForm) : Prop := xpol s.1 s.2 = true

/-- Rocq: `Analysis.ProvableTI.ssem`. -/
def Ssem (X : Nat → Prop) : SForm → Prop
  | (true, A) => nsat X ρ0 A
  | (false, A) => ¬nsat X ρ0 A

/-- Rocq: `Analysis.ProvableTI.ssem_mono`. -/
theorem ssem_mono (X Y : Nat → Prop) (HXY : ∀ n, X n → Y n) : ∀ s : SForm, Spos s → Ssem X s → Ssem Y s
  | (true, A), hp, h => (nsat_mono X Y HXY A true ρ0 hp).1 rfl h
  | (false, A), hp, h => fun hy => h ((nsat_mono X Y HXY A false ρ0 hp).2 rfl hy)

/-- Rocq: `Analysis.ProvableTI.ssem_stable`. -/
theorem ssem_stable (X : Nat → Prop) (HX : ∀ n, ¬¬X n → X n) : ∀ s : SForm, ¬¬Ssem X s → Ssem X s
  | (true, A), H => nsat_stable X HX A ρ0 H
  | (false, _), H => fun a => H (fun hn => hn a)

/-- Rocq: `Analysis.ProvableTI.ssem_dax`. -/
theorem ssem_dax (X : Nat → Prop) : ∀ s : SForm, Dax s → Ssem X s
  | (true, A), ⟨hD, hv⟩ => (nsat_D X A ρ0 hD).2 ((deval_sat hD ρ0).1 hv)
  | (false, A), ⟨hD, hv⟩ => fun h => (deval_false ρ0 hD).1 hv ((nsat_D X A ρ0 hD).1 h)

/-- Rocq: `Analysis.ProvableTI.ssem_dfalse`. -/
theorem ssem_dfalse (X : Nat → Prop) : ∀ s : SForm, Dfalse s → ¬Ssem X s
  | (true, A), ⟨hD, hv⟩, h => (deval_false ρ0 hD).1 hv ((nsat_D X A ρ0 hD).1 h)
  | (false, A), ⟨hD, hv⟩, h => h ((nsat_D X A ρ0 hD).2 ((deval_sat hD ρ0).1 hv))

/-- Rocq: `Analysis.ProvableTI.spos_D`. -/
theorem spos_D : ∀ s : SForm, isD s.2 = true → Spos s
  | (b, A), h => xpol_D b A h

/-- Rocq: `Analysis.ProvableTI.ssem_conj`. -/
theorem ssem_conj (X : Nat → Prop) {s s1 s2 : SForm} (hk : kindof s = .conj s1 s2)
    (h1 : Ssem X s1) (h2 : Ssem X s2) : Ssem X s := by
  obtain ⟨b, A⟩ := s
  cases b <;> cases A <;> first
    | exact Kind.noConfusion hk
    | (cases hk; first | exact ⟨h1, h2⟩ | exact fun H => H ⟨h1, h2⟩ | exact fun f => h2 (f h1))

/-- Rocq: `Analysis.ProvableTI.ssem_disj`. -/
theorem ssem_disj (X : Nat → Prop) {s s1 s2 s' : SForm} (hk : kindof s = .disj s1 s2)
    (hsel : s' = s1 ∨ s' = s2) (h : Ssem X s') : Ssem X s := by
  obtain ⟨b, A⟩ := s
  cases b <;> cases A <;> first
    | exact Kind.noConfusion hk
    | (cases hk; rcases hsel with rfl | rfl <;> first
        | exact fun ⟨na, _⟩ => na h | exact fun ⟨_, nb⟩ => nb h
        | exact fun ⟨a, _⟩ => h a | exact fun ⟨_, b⟩ => h b
        | exact fun a => (h a).elim | exact fun _ => h)

/-- Rocq: `Analysis.ProvableTI.ssem_univ`. -/
theorem ssem_univ (X : Nat → Prop) {s : SForm} {b : Bool} {A : Form} (hk : kindof s = .univ b A)
    (hi : ∀ i, Ssem X (inst b A i)) : Ssem X s := by
  obtain ⟨b', A'⟩ := s
  cases b' <;> cases A' <;> first
    | exact Kind.noConfusion hk
    | (cases hk; first
        | exact fun x => (nsat_sub1_num X ρ0 _ x).1 (hi x)
        | exact fun H => H (fun x hx => hi x ((nsat_sub1_num X ρ0 _ x).2 hx)))

/-- Rocq: `Analysis.ProvableTI.ssem_exis`. -/
theorem ssem_exis (X : Nat → Prop) {s : SForm} {b : Bool} {A : Form} {m : Nat} (hk : kindof s = .exis b A)
    (h : Ssem X (inst b A m)) : Ssem X s := by
  obtain ⟨b', A'⟩ := s
  cases b' <;> cases A' <;> first
    | exact Kind.noConfusion hk
    | (cases hk; first
        | exact fun H => H m ((nsat_sub1_num X ρ0 _ m).1 h)
        | exact fun H => h ((nsat_sub1_num X ρ0 _ m).2 (H m)))

/-- Rocq: `Analysis.ProvableTI.spos_conj`. -/
theorem spos_conj {s s1 s2 : SForm} (hk : kindof s = .conj s1 s2) (hp : Spos s) : Spos s1 ∧ Spos s2 := by
  obtain ⟨b, A⟩ := s
  cases b <;> cases A <;> first | exact Kind.noConfusion hk | (cases hk; exact and_true_split hp)

/-- Rocq: `Analysis.ProvableTI.spos_disj`. -/
theorem spos_disj {s s1 s2 s' : SForm} (hk : kindof s = .disj s1 s2) (hsel : s' = s1 ∨ s' = s2)
    (hp : Spos s) : Spos s' := by
  obtain ⟨b, A⟩ := s
  cases b <;> cases A <;> first
    | exact Kind.noConfusion hk
    | (cases hk; have h := and_true_split hp; rcases hsel with rfl | rfl <;> first | exact h.1 | exact h.2)

/-- Rocq: `Analysis.ProvableTI.spos_inst`. -/
theorem spos_inst {s : SForm} {b : Bool} {A : Form} (i : Nat)
    (hk : kindof s = .univ b A ∨ kindof s = .exis b A) (hp : Spos s) : Spos (inst b A i) := by
  obtain ⟨b', A'⟩ := s
  rcases hk with hk | hk <;> cases b' <;> cases A' <;> first
    | exact Kind.noConfusion hk
    | (cases hk; exact (xpol_fsubst _ _ _).trans hp)

/-- Rocq: `Analysis.ProvableTI.not_spos_PX`. -/
theorem not_spos_PX (u : ATerm) : ¬Spos (false, px u) := fun h => Bool.noConfusion h

/-- Rocq: `Analysis.ProvableTI.D_not_PX`. -/
theorem D_not_PX (x : SForm) (b : Bool) (u : ATerm) (h : isD x.2 = true) : x ≠ (b, px u) := by
  intro e; subst e; exact Bool.noConfusion h

/-! ## The bounds -/

/-- Rocq: `Analysis.ProvableTI.Bd`. -/
def Bd (γ : Ordinal.{0}) (a : VForm) : Ordinal.{0} := γ + ω ^ sz a

/-- Rocq: `Analysis.ProvableTI.Bd_ge`. -/
theorem Bd_ge (γ : Ordinal.{0}) (a : VForm) : γ ≤ Bd γ a := le_add_right γ _

/-- Rocq: `Analysis.ProvableTI.Bd_le`. -/
theorem Bd_le (γ : Ordinal.{0}) {a b : VForm} (h : sz a ≤ sz b) : Bd γ a ≤ Bd γ b :=
  add_le_add (le_refl γ) (pow_le_pow_right ω h)

/-- Rocq: `Analysis.ProvableTI.olt_lt`. -/
theorem olt_lt {n : Nat} {b a : VForm} (h : Olt n b a) : sz b < sz a :=
  let ⟨_, hP, hr⟩ := h
  lt_of_le_of_lt (reach_le hr) (Pn_lt hP)

/-- Restarting at the successor of `Bd γ β` costs another `ω^β`, which still
fits below `ω^α`. Rocq: `Analysis.ProvableTI.Bd_step`. -/
theorem Bd_step (γ : Ordinal.{0}) {a b : VForm} (hab : sz a < sz b) :
    Bd (Ordinal.succ (Bd γ a)) a ≤ Bd γ b := by
  unfold Bd
  have he : (0 : Ordinal.{0}) < ω ^ sz a := pow_pos ω (sz a)
  have h1 : ω ^ sz a ≤ ω ^ sz a * ofNat 1 :=
    le_trans (zero_add _).ge (le_trans (add_le_add (mul_zero _).ge (le_refl _)) (mul_succ _ (ofNat 0)).ge)
  have h2 : ω ^ sz a + ω ^ sz a ≤ ω ^ sz a * ofNat 2 :=
    le_trans (add_le_add h1 (le_refl _)) (mul_succ _ (ofNat 1)).ge
  have h3 : ω ^ sz a + ω ^ sz a + ω ^ sz a ≤ ω ^ sz a * ofNat 3 :=
    le_trans (add_le_add h2 (le_refl _)) (mul_succ _ (ofNat 2)).ge
  have hs : Ordinal.succ (ω ^ sz a) ≤ ω ^ sz a + ω ^ sz a :=
    succ_least (lt_of_le_of_lt (add_zero _).ge (add_lt_add_left _ he))
  have hK : Ordinal.succ (ω ^ sz a) + ω ^ sz a ≤ ω ^ sz b :=
    le_trans (add_le_add hs (le_refl _)) (le_trans h3 (le_trans (mul_le_mul_left _ (le_of_lt (index_lt ω ⟨3⟩)))
      (le_trans (pow_succ (sz a) omega_gt0).ge (pow_le_pow_right ω (succ_least hab)))))
  exact le_trans (add_le_add (add_succ γ _).ge (le_refl _))
    (le_trans (add_assoc γ _ _).ge (add_le_add (le_refl γ) hK))

/-! ## The boundedness lemma -/

/-- Rocq: `Analysis.ProvableTI.B`. -/
def B (Q : Form) (L : Ordinal.{0}) : Nat → Prop := below (prec Q) L

/-- Rocq: `Analysis.ProvableTI.special`. -/
def Special (Q : Form) (s : SForm) : Prop := s = (false, Prog Q) ∨ ∃ a, s = inst false (ProgB Q) a

/-- Each formula of the sequent has `X` positive, or is a negated `X`-atom, or
comes from `¬Prog(X)`. Rocq: `Analysis.ProvableTI.cls`. -/
def Cls (Q : Form) (s : SForm) : Prop := Spos s ∨ Special Q s ∨ ∃ u, s = (false, px u)

/-- Rocq: `Analysis.ProvableTI.Qinst`. -/
def Qinst (Q : Form) (a : Nat) : Form := fsubst (up (inst1 (num a))) Q

/-- Rocq: `Analysis.ProvableTI.special_kind`. -/
theorem special_kind (Q : Form) {s : SForm} (h : Special Q s) :
    kindof s = .exis false (ProgB Q) ∨
    ∃ a, kindof s = .conj (true, all (imp (Qinst Q a) (px (tv 0)))) (false, px (num a)) := by
  rcases h with rfl | ⟨a, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨a, rfl⟩

theorem and_false_true {a : Bool} (h : (a && false) = true) : False := by
  cases a <;> exact Bool.noConfusion h

/-- Rocq: `Analysis.ProvableTI.special_not_pos`. -/
theorem special_not_pos (Q : Form) {s : SForm} (h : Special Q s) : ¬Spos s := by
  rcases h with rfl | ⟨a, rfl⟩
  · exact fun h => and_false_true (a := xpol true (all (imp Q (px (tv 0))))) h
  · exact fun h => and_false_true (a := xpol true (all (imp (Qinst Q a) (px (tv 0))))) h

/-- Rocq: `Analysis.ProvableTI.comp_sem`. -/
theorem comp_sem (Q : Form) (HQ : isD Q = true) (L : Ordinal.{0}) (a : Nat)
    (H : nsat (B Q L) ρ0 (all (imp (Qinst Q a) (px (tv 0))))) : ∀ y, prec Q y a → B Q L y := by
  intro y hy
  have E : ∀ i, scons y (scons a ρ0) i = teval (scons y ρ0) (up (inst1 (num a)) i)
    | 0 => rfl
    | 1 => ((teval_shift y ρ0 (num a)).trans (teval_num ρ0 a)).symm
    | _ + 2 => rfl
  exact H y ((nsat_D _ _ _ ((isD_fsubst_eq Q _).trans HQ)).2 ((sat_fsubst Q _ _).2 ((sat_ext Q E).1 hy)))

/-- Rocq: `Analysis.ProvableTI.comp_pos`. -/
theorem comp_pos (Q : Form) (HQ : isD Q = true) (a : Nat) : Spos (true, all (imp (Qinst Q a) (px (tv 0)))) := by
  show (xpol false (Qinst Q a) && true) = true
  rw [xpol_D false (Qinst Q a) ((isD_fsubst_eq Q _).trans HQ)]; rfl

/-- Rocq: `Analysis.ProvableTI.B_stable`. -/
theorem B_stable (Q : Form) (L : Ordinal.{0}) (n : Nat) : ¬¬B Q L n → B Q L n := below_stable _ L n

/-- Rocq: `Analysis.ProvableTI.B_mono`. -/
theorem B_mono (Q : Form) {L L' : Ordinal.{0}} (n : Nat) (h : L ≤ L') : B Q L n → B Q L' n :=
  below_mono _ L L' n h

/-- The positive formulas of a premise give the principal formula, when those
of the conclusion fail. Rocq: `Analysis.ProvableTI.extract`. -/
theorem extract (Q : Form) {L L' : Ordinal.{0}} {x : SForm} {Γ : List SForm} (hle : L ≤ L') (_hx : Spos x)
    (hpos : ∀ s, s ∈ Γ → Spos s → ¬Ssem (B Q L') s)
    (IH : (∀ s, s ∈ x :: Γ → Spos s → ¬Ssem (B Q L) s) → False) : Ssem (B Q L) x := by
  refine ssem_stable _ (B_stable Q L) x (fun hn => IH ?_)
  intro s hs hp
  cases hs with
  | head => exact hn
  | tail _ hs => exact fun h => hpos s hs hp (ssem_mono _ _ (fun m => B_mono Q m hle) s hp h)

/-- Rocq: `Analysis.ProvableTI.pos_lift`. -/
theorem pos_lift (Q : Form) {L L' : Ordinal.{0}} {Γ : List SForm} (hle : L ≤ L')
    (H : ∀ s, s ∈ Γ → Spos s → ¬Ssem (B Q L') s) : ∀ s, s ∈ Γ → Spos s → ¬Ssem (B Q L) s :=
  fun s hs hp h => H s hs hp (ssem_mono _ _ (fun m => B_mono Q m hle) s hp h)

theorem cls_cons_pos (Q : Form) {x : SForm} {Γ : List SForm} (hx : Spos x) (H : ∀ s, s ∈ Γ → Cls Q s) :
    ∀ s, s ∈ x :: Γ → Cls Q s := by
  intro s hs
  cases hs with
  | head => exact .inl hx
  | tail _ hs => exact H s hs

theorem neg_cons_pos {P : ATerm → Prop} {x : SForm} {Γ : List SForm} (hx : Spos x)
    (H : ∀ u, (false, px u) ∈ Γ → P u) : ∀ u, (false, px u) ∈ x :: Γ → P u := by
  intro u hu
  cases hu with
  | head => exact absurd hx (not_spos_PX u)
  | tail _ hu => exact H u hu

/-- Rocq: `Analysis.ProvableTI.od_TI_bound`. -/
theorem od_TI_bound (Q : Form) (HQ : isD Q = true) {n ρ : Nat} {α : VForm} {Γ : List SForm}
    (h : OD n ρ α Γ) : ρ ≤ 1 → (∀ s, s ∈ Γ → Cls Q s) →
    ∀ γ : Ordinal.{0}, (∀ u, (false, px u) ∈ Γ → B Q γ (teval ρ0 u)) →
    (∀ s, s ∈ Γ → Spos s → ¬Ssem (B Q (Bd γ α)) s) → False := by
  induction h with
  | ax n ρ α Γ s hs hax =>
    -- a true bounded formula
    intro _ _ γ _ hpos
    exact hpos s hs (spos_D s hax.1) (ssem_dax _ s hax)
  | xax n ρ α Γ u v hu hv huv =>
    -- `X t, ¬X t'`
    intro _ _ γ hneg hpos
    refine hpos _ hu rfl ?_
    show B Q (Bd γ α) (teval ρ0 u)
    rw [huv]; exact B_mono Q _ (Bd_ge γ α) (hneg v hv)
  | conj n ρ α β Γ s s1 s2 hs hk _ _ hlt ih1 ih2 =>
    intro hρ hcls γ hneg hpos
    have hle : Bd γ β ≤ Bd γ α := Bd_le γ (le_of_lt (olt_lt hlt))
    rcases hcls s hs with hp | hsp | ⟨w, rfl⟩
    · have ⟨hp1, hp2⟩ := spos_conj hk hp
      have H1 : Ssem (B Q (Bd γ β)) s1 :=
        extract Q hle hp1 hpos (ih1 hρ (cls_cons_pos Q hp1 hcls) γ (neg_cons_pos hp1 hneg))
      have H2 : Ssem (B Q (Bd γ β)) s2 :=
        extract Q hle hp2 hpos (ih2 hρ (cls_cons_pos Q hp2 hcls) γ (neg_cons_pos hp2 hneg))
      exact hpos s hs hp (ssem_mono _ _ (fun m => B_mono Q m hle) s hp (ssem_conj _ hk H1 H2))
    · rcases special_kind Q hsp with E | ⟨a, E⟩
      · rw [E] at hk; exact Kind.noConfusion hk
      · rw [E] at hk
        cases hk
        have H1 : Ssem (B Q (Bd γ β)) (true, all (imp (Qinst Q a) (px (tv 0)))) :=
          extract Q hle (comp_pos Q HQ a) hpos
            (ih1 hρ (cls_cons_pos Q (comp_pos Q HQ a) hcls) γ (neg_cons_pos (comp_pos Q HQ a) hneg))
        have Ha : B Q (Ordinal.succ (Bd γ β)) a := below_succ _ _ a (comp_sem Q HQ _ a H1)
        refine ih2 hρ ?_ (Ordinal.succ (Bd γ β)) ?_ ?_
        · intro x hx
          cases hx with
          | head => exact .inr (.inr ⟨num a, rfl⟩)
          | tail _ hx => exact hcls x hx
        · intro u hu
          cases hu with
          | head => show B Q _ (teval ρ0 (num a)); rw [teval_num]; exact Ha
          | tail _ hu =>
            exact B_mono Q _ (le_trans (Bd_ge γ β) (le_of_lt (succ_lt _))) (hneg u hu)
        · intro x hx hp
          cases hx with
          | head => exact absurd hp (not_spos_PX _)
          | tail _ hx => exact pos_lift Q (Bd_step γ (olt_lt hlt)) hpos x hx hp
    · rw [kind_PX] at hk; exact Kind.noConfusion hk
  | disj n ρ α β Γ s s1 s2 s' hs hk hsel _ hlt ih =>
    intro hρ hcls γ hneg hpos
    have hle : Bd γ β ≤ Bd γ α := Bd_le γ (le_of_lt (olt_lt hlt))
    rcases hcls s hs with hp | hsp | ⟨w, rfl⟩
    · have hp' := spos_disj hk hsel hp
      have H' : Ssem (B Q (Bd γ β)) s' :=
        extract Q hle hp' hpos (ih hρ (cls_cons_pos Q hp' hcls) γ (neg_cons_pos hp' hneg))
      exact hpos s hs hp (ssem_mono _ _ (fun m => B_mono Q m hle) s hp (ssem_disj _ hk hsel H'))
    · rcases special_kind Q hsp with E | ⟨a, E⟩ <;> (rw [E] at hk; exact Kind.noConfusion hk)
    · rw [kind_PX] at hk; exact Kind.noConfusion hk
  | univ n ρ α β Γ s b A hs hk _ _ hlt ih =>
    intro hρ hcls γ hneg hpos
    rcases hcls s hs with hp | hsp | ⟨w, rfl⟩
    · refine hpos s hs hp (ssem_univ _ hk fun i => ?_)
      have hle : Bd γ (β i) ≤ Bd γ α := Bd_le γ (le_of_lt (olt_lt (hlt i)))
      have hpi : Spos (inst b A i) := spos_inst i (.inl hk) hp
      exact ssem_mono _ _ (fun m => B_mono Q m hle) _ hpi
        (extract Q hle hpi hpos (ih i hρ (cls_cons_pos Q hpi hcls) γ (neg_cons_pos hpi hneg)))
    · rcases special_kind Q hsp with E | ⟨a, E⟩ <;> (rw [E] at hk; exact Kind.noConfusion hk)
    · rw [kind_PX] at hk; exact Kind.noConfusion hk
  | exis n ρ α β Γ s b A m hs hk _ _ hlt ih =>
    intro hρ hcls γ hneg hpos
    have hle : Bd γ β ≤ Bd γ α := Bd_le γ (le_of_lt (olt_lt hlt))
    rcases hcls s hs with hp | hsp | ⟨w, rfl⟩
    · have hpi : Spos (inst b A m) := spos_inst m (.inr hk) hp
      refine hpos s hs hp (ssem_exis (m := m) _ hk ?_)
      exact ssem_mono _ _ (fun m => B_mono Q m hle) _ hpi
        (extract Q hle hpi hpos (ih hρ (cls_cons_pos Q hpi hcls) γ (neg_cons_pos hpi hneg)))
    · rcases special_kind Q hsp with E | ⟨a, E⟩
      · rw [E] at hk
        cases hk
        have hsi : Special Q (inst false (ProgB Q) m) := .inr ⟨m, rfl⟩
        refine ih hρ ?_ γ ?_ ?_
        · intro x hx
          cases hx with
          | head => exact .inr (.inl hsi)
          | tail _ hx => exact hcls x hx
        · intro u hu
          cases hu with
          | tail _ hu => exact hneg u hu
        · intro x hx hp
          cases hx with
          | head => exact absurd hp (special_not_pos Q hsi)
          | tail _ hx => exact pos_lift Q hle hpos x hx hp
      · rw [E] at hk; exact Kind.noConfusion hk
    · rw [kind_PX] at hk; exact Kind.noConfusion hk
  | cut n ρ α β Γ s hr _ _ hlt ih1 ih2 =>
    -- a cut on a bounded formula
    intro hρ hcls γ hneg hpos
    have hle : Bd γ β ≤ Bd γ α := Bd_le γ (le_of_lt (olt_lt hlt))
    have hDs : isD s.2 = true := rank_0_D (Nat.le_zero.mp (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr hρ)))
    have hDn : isD (sneg s).2 = true := hDs
    cases dax_dec s hDs with
    | inl hax =>
      have hf : Dfalse (sneg s) := (dfalse_sneg (sneg s)).2 (by rw [sneg_sneg]; exact hax)
      refine ih2 hρ ?_ γ ?_ ?_
      · exact cls_cons_pos Q (spos_D _ hDn) hcls
      · intro u hu
        exact (rem_head _ _ _ hu).elim (fun e => absurd e.symm (D_not_PX _ false u hDn)) (hneg u)
      · intro x hx hp
        cases hx with
        | head => exact ssem_dfalse _ _ hf
        | tail _ hx => exact pos_lift Q hle hpos x hx hp
    | inr hf =>
      refine ih1 hρ ?_ γ ?_ ?_
      · exact cls_cons_pos Q (spos_D _ hDs) hcls
      · intro u hu
        exact (rem_head _ _ _ hu).elim (fun e => absurd e.symm (D_not_PX _ false u hDs)) (hneg u)
      · intro x hx hp
        cases hx with
        | head => exact ssem_dfalse _ _ hf
        | tail _ hx => exact pos_lift Q hle hpos x hx hp
  | up n m ρ α β γ' h Γ _ _ _ _ hlt ih =>
    -- raising the control
    intro hρ hcls γ hneg hpos
    refine ih hρ hcls γ hneg (pos_lift Q (Bd_le γ ?_) hpos)
    exact le_of_lt (lt_of_le_of_lt (reach_le (reach_prefix m β γ')) (olt_lt hlt))

/-! ## Provable transfinite induction -/

/-- Rocq: `Analysis.ProvableTI.sigma0`. -/
def sigma0 : Nat → Nat := fun _ => 0

/-- Rocq: `Analysis.ProvableTI.prec_R0`. -/
theorem prec_R0 (R : Form) (y x : Nat) : prec (fsubst (up (up (nsub sigma0))) R) y x ↔ prec R y x := by
  have E : ∀ i, teval (scons y (scons x ρ0)) (up (up (nsub sigma0)) i) = scons y (scons x ρ0) i
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  exact (sat_fsubst R _ _).trans (sat_ext R E)

/-- If PA proves transfinite induction along a bounded relation `≺`, then
`≺` has height below ε₀. Rocq: `Analysis.ProvableTI.PA_TI_bound`. -/
theorem PA_TI_bound (R : Form) (HR : isD R = true) (Hprov : PA [] (TI R)) :
    ∃ L : Ordinal.{0}, L < ε 0 ∧ ∀ x, below (prec R) L x := by
  have Hp : PA [Prog R] (all (px (tv 0))) :=
    .impE _ _ _ (prov_weaken Hprov _ (fun _ h => nomatch h)) hyp0
  obtain ⟨k, ρ, N, hN, hemb⟩ := embed Hp
  have HR0 : isD (fsubst (up (up (nsub sigma0))) R) = true := (isD_fsubst_eq R _).trans HR
  have Hd : OD N (ρ + 1) (W k) [(true, all (px (tv 0))), (false, Prog (fsubst (up (up (nsub sigma0))) R))] :=
    od_rank (hemb N sigma0 (Nat.le_refl N) (fun _ => Nat.lt_of_lt_of_le (Nat.succ_pos 2) hN)) (Nat.le_succ ρ)
  have Hd1 := od_elim_all ρ N _ _ Hd hN
  refine ⟨Bd 0 (otower ρ (W k)), ?_, fun x => ?_⟩
  · exact lt_of_le_of_lt (le_trans (zero_add _).le (VZ_eq _).ge) (below_ε₀ (V (otower ρ (W k)) Z))
  · refine below_ext _ _ (fun y z h => (prec_R0 R y z).2 h) _ x (below_stable _ _ x fun hn => ?_)
    refine od_TI_bound _ HR0 Hd1 (Nat.le_refl 1) ?_ 0 ?_ ?_
    · intro s hs
      cases hs with
      | head => exact .inl rfl
      | tail _ hs =>
        cases hs with
        | head => exact .inr (.inl (.inl rfl))
        | tail _ hs => exact nomatch hs
    · intro u hu
      cases hu with
      | tail _ hu =>
        cases hu with
        | tail _ hu => exact nomatch hu
    · intro s hs hp H
      cases hs with
      | head => exact hn (H x)
      | tail _ hs =>
        cases hs with
        | head => exact special_not_pos _ (.inl rfl) hp
        | tail _ hs => exact nomatch hs

/-- In particular there is no infinite descending sequence.
Rocq: `Analysis.ProvableTI.PA_TI_no_descent`. -/
theorem PA_TI_no_descent (R : Form) (HR : isD R = true) (Hprov : PA [] (TI R)) (f : Nat → Nat)
    (hd : ∀ i, prec R (f (i + 1)) (f i)) : False :=
  let ⟨L, _, HL⟩ := PA_TI_bound R HR Hprov
  below_no_descent _ L f (HL (f 0)) hd

/-- Classical corollary. With the excluded middle as a hypothesis: if PA proves
transfinite induction along `≺`, then `≺` is well-founded with order type below
ε₀. Rocq: `Analysis.ProvableTI.PA_TI_wf_EM`. -/
theorem PA_TI_wf_EM (EM : ExcludedMiddle) (R : Form) (HR : isD R = true) (Hprov : PA [] (TI R)) :
    ∃ Hwf : WellFounded (prec R), wfOrd (prec R) Hwf < ε 0 := by
  obtain ⟨L, HL, Hb⟩ := PA_TI_bound R HR Hprov
  have Hwf : WellFounded (prec R) := ⟨fun x => below_Acc_EM _ EM L x (Hb x)⟩
  refine ⟨Hwf, lt_of_le_of_lt (b := Ordinal.succ L) ?_ ?_⟩
  · exact le_intro fun x => lt_of_le_of_lt (below_wf_ord_EM _ EM L x _ (Hb x)) (succ_lt L)
  · have h0 : (0 : Ordinal.{0}) < ε 0 := lt_of_lt_of_le (pow_pos ω (ε 0)) (ε_fixpoint 0).ge
    have h1 : Ordinal.succ 0 < ε 0 :=
      lt_of_lt_of_le omega_gt1 (le_trans (pow_one' omega_gt0).ge
        (le_trans (pow_le_pow_right ω (succ_least h0)) (ε_fixpoint 0).ge))
    exact lt_of_le_of_lt (succ_least (lt_of_le_of_lt (add_zero L).ge (add_lt_add_left L (succ_lt 0))))
      (epsilon_additively_closed zero_complete L _ HL h1)

end ConstructiveOrdinals.ProvableTI
