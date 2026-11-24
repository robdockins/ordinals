import ConstructiveOrdinals.Analysis.HereditarySubstF
import ConstructiveOrdinals.Prelude.Index

/-!
# Hereditary substitution and normalization for Leivant's predicative System F

Port of `Ordinal/Analysis/HereditarySubstFNorm.v`.

Building on the ordinal type measure of `HereditarySubstF`, this file defines
hereditary substitution on the normal forms of predicative System F, proves
that it terminates by the ordinal measure `ω · tord U + size`, and that it
preserves typing; normalization and consistency follow.

Termination is unconditional: when a type abstraction meets a type argument,
the function checks decidably that the argument has the quantifier's kind
(`kind_of`), and otherwise returns its input. With the check, every recursive
call decreases the ordinal measure (`tord_inst` does the work); the typing
theorem shows that the check always succeeds on well-typed input.

Lean notes:

- Rocq proves the de Bruijn lemmas with `lia`. Here the variable cases go
  through the index functions `sv` and `svar` of `Prelude/Index`.
- Matches that Rocq writes with wildcards spell out every case, since a
  wildcard would make the definitions depend on `propext`.
-/

namespace ConstructiveOrdinals.HereditarySubstFNorm

open Ordinal HereditarySubstF Typ Index

theorem congrArg₂ {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') :
    f a b = f a' b' := ha ▸ hb ▸ rfl

theorem tshift_tvar (c Y : Nat) : tshift c (tvar Y) = tvar (sv c Y) := congrArg tvar (sv_eq c Y)

/-- Substitution into a variable, through `svar`. -/
def substVar (o : Option Nat) (T : Typ) : Typ :=
  match o with
  | none => T
  | some z => tvar z

theorem tsubst_tvar (Y X : Nat) (T : Typ) : tsubst (tvar Y) X T = substVar (svar X Y) T := by
  show (if Y = X then T else tvar (if Y < X then Y else Y - 1)) = _
  rw [svar_spec]
  by_cases h : Y = X
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; rfl

/-! ## Type-level de Bruijn lemmas -/

/-- Rocq: `Analysis.HereditarySubstFNorm.tshift_tshift`. -/
theorem tshift_tshift : ∀ (T : Typ) {X Y : Nat}, X ≤ Y → tshift X (tshift Y T) = tshift (Y + 1) (tshift X T)
  | tvar Z, X, Y, h => by
    rw [tshift_tvar, tshift_tvar, tshift_tvar, tshift_tvar, sv_sv Z h]
  | arrow A B, _, _, h => congrArg₂ arrow (tshift_tshift A h) (tshift_tshift B h)
  | all k U, _, _, h => congrArg (all k) (tshift_tshift U (Nat.succ_le_succ h))

/-- Rocq: `Analysis.HereditarySubstFNorm.tsubst_tshift`. -/
theorem tsubst_tshift : ∀ (T : Typ) (X : Nat) (U : Typ), tsubst (tshift X T) X U = T
  | tvar Z, X, U => by rw [tshift_tvar, tsubst_tvar, svar_sv]; rfl
  | arrow A B, X, U => congrArg₂ arrow (tsubst_tshift A X U) (tsubst_tshift B X U)
  | all k V, X, U => congrArg (all k) (tsubst_tshift V (X + 1) _)

/-- Shifting below the substituted variable. Rocq: `Analysis.HereditarySubstFNorm.tshift_tsubst_le`. -/
theorem tshift_tsubst_le : ∀ (T : Typ) {X Y : Nat} (U : Typ), X ≤ Y →
    tshift X (tsubst T Y U) = tsubst (tshift X T) (Y + 1) (tshift X U)
  | tvar Z, X, Y, U, h => by
    rw [tsubst_tvar, tshift_tvar, tsubst_tvar, svar_sv_le Z h]
    cases svar Y Z with
    | none => rfl
    | some z => show tshift X (tvar z) = _; rw [tshift_tvar]; rfl
  | arrow A B, _, _, U, h => congrArg₂ arrow (tshift_tsubst_le A U h) (tshift_tsubst_le B U h)
  | all k V, X, Y, U, h => by
    show all k (tshift (X + 1) (tsubst V (Y + 1) (tshift 0 U))) =
      all k (tsubst (tshift (X + 1) V) (Y + 2) (tshift 0 (tshift X U)))
    rw [tshift_tsubst_le V _ (Nat.succ_le_succ h), tshift_tshift U (Nat.zero_le X)]

/-- Shifting above the substituted variable. Rocq: `Analysis.HereditarySubstFNorm.tshift_tsubst_ge`. -/
theorem tshift_tsubst_ge : ∀ (T : Typ) {X Y : Nat} (U : Typ), Y ≤ X →
    tshift X (tsubst T Y U) = tsubst (tshift (X + 1) T) Y (tshift X U)
  | tvar Z, X, Y, U, h => by
    rw [tsubst_tvar, tshift_tvar, tsubst_tvar, svar_sv_ge Z h]
    cases svar Y Z with
    | none => rfl
    | some z => show tshift X (tvar z) = _; rw [tshift_tvar]; rfl
  | arrow A B, _, _, U, h => congrArg₂ arrow (tshift_tsubst_ge A U h) (tshift_tsubst_ge B U h)
  | all k V, X, Y, U, h => by
    show all k (tshift (X + 1) (tsubst V (Y + 1) (tshift 0 U))) =
      all k (tsubst (tshift (X + 2) V) (Y + 1) (tshift 0 (tshift X U)))
    rw [tshift_tsubst_ge V _ (Nat.succ_le_succ h), tshift_tshift U (Nat.zero_le X)]

/-- Rocq: `Analysis.HereditarySubstFNorm.tsubst_tsubst`. -/
theorem tsubst_tsubst : ∀ (T : Typ) {X Y : Nat} (U V : Typ), X ≤ Y →
    tsubst (tsubst T X U) Y V = tsubst (tsubst T (Y + 1) (tshift X V)) X (tsubst U Y V)
  | tvar Z, X, Y, U, V, h => by
    rw [tsubst_tvar Z X, tsubst_tvar Z (Y + 1)]
    cases e1 : svar X Z with
    | none =>
      have hZ := svar_none e1
      subst hZ
      rw [svar_lt (Nat.lt_succ_of_le h)]
      show _ = tsubst (tvar Z) Z _
      rw [tsubst_tvar, svar_self]; rfl
    | some z =>
      show tsubst (tvar z) Y V = _
      rw [tsubst_tvar z Y]
      cases e2 : svar Y z with
      | none =>
        have hz := svar_none e2
        subst hz
        have hZ := svar_ge e1 h
        subst hZ
        rw [show svar (z + 1) (z + 1) = none from svar_self _]
        exact (tsubst_tshift V X _).symm
      | some w =>
        obtain ⟨w', e3, e4⟩ := svar_comp h e1 e2
        rw [e3]
        show tvar w = tsubst (tvar w') X _
        rw [tsubst_tvar, e4]; rfl
  | arrow A B, _, _, U, V, h => congrArg₂ arrow (tsubst_tsubst A U V h) (tsubst_tsubst B U V h)
  | all k W, X, Y, U, V, h => by
    show all k (tsubst (tsubst W (X + 1) (tshift 0 U)) (Y + 1) (tshift 0 V)) =
      all k (tsubst (tsubst W (Y + 2) (tshift 0 (tshift X V))) (X + 1) (tshift 0 (tsubst U Y V)))
    rw [tsubst_tsubst W _ _ (Nat.succ_le_succ h), tshift_tshift V (Nat.zero_le X),
      tshift_tsubst_le U V (Nat.zero_le Y)]

/-! ## Kinding -/

theorem max_le' {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : Nat.max a b ≤ c := by
  show (if a ≤ b then b else a) ≤ c
  by_cases h : a ≤ b
  · rw [ite_eq_left h]; exact hb
  · rw [ite_eq_right h]; exact ha

theorem max_le_compat {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : Nat.max a b ≤ Nat.max c d :=
  max_le' (Nat.le_trans h1 (Nat.le_max_left _ _)) (Nat.le_trans h2 (Nat.le_max_right _ _))

theorem max_self (a : Nat) : Nat.max a a = a := ite_eq_left (Nat.le_refl a)

theorem max_eq_right {a b : Nat} (h : a ≤ b) : Nat.max a b = b := ite_eq_left h

/-- Rocq: `Analysis.HereditarySubstFNorm.kinding_cumul`. -/
theorem kinding_cumul {Δ : List Kind} {T : Typ} {k : Kind} (h : Kinding Δ T k) :
    ∀ {k'}, k ≤ k' → Kinding Δ T k' := by
  induction h with
  | var Γ X k k₀ hX hle => intro k'' hle'; exact .var _ _ _ _ hX (Nat.le_trans hle hle')
  | arrow Γ A B k k' _ _ ih1 ih2 =>
    intro k'' hle
    rw [← max_self k'']
    exact .arrow _ _ _ _ _ (ih1 (Nat.le_trans (Nat.le_max_left _ _) hle))
      (ih2 (Nat.le_trans (Nat.le_max_right _ _) hle))
  | all Γ k U k' _ ih =>
    intro k'' hle
    have h1 : k + 1 ≤ k'' := Nat.le_trans (Nat.le_max_left _ _) hle
    rw [← max_eq_right h1]
    exact .all _ _ _ _ (ih (Nat.le_trans (Nat.le_max_right _ _) hle))

/-- The least kind of a type, if any. Rocq: `Analysis.HereditarySubstFNorm.kind_of`. -/
def kindOf : List Kind → Typ → Option Kind
  | Δ, tvar X => List.nthError Δ X
  | Δ, arrow A B =>
    match kindOf Δ A, kindOf Δ B with
    | some k, some k' => some (Nat.max k k')
    | some _, none => none
    | none, _ => none
  | Δ, all k U =>
    match kindOf (k :: Δ) U with
    | some k' => some (Nat.max (k + 1) k')
    | none => none

/-- Rocq: `Analysis.HereditarySubstFNorm.kind_of_sound`. -/
theorem kindOf_sound : ∀ (T : Typ) (Δ : List Kind) (k : Kind), kindOf Δ T = some k → Kinding Δ T k
  | tvar X, Δ, k, h => .var _ _ _ _ h (Nat.le_refl k)
  | arrow A B, Δ, k, h => by
    have h' : (match kindOf Δ A, kindOf Δ B with
      | some k, some k' => some (Nat.max k k')
      | some _, none => none
      | none, _ => none) = some k := h
    cases eA : kindOf Δ A with
    | none => rw [eA] at h'; cases h'
    | some kA =>
      cases eB : kindOf Δ B with
      | none => rw [eA, eB] at h'; cases h'
      | some kB =>
        rw [eA, eB] at h'; cases h'
        exact .arrow _ _ _ _ _ (kindOf_sound A Δ kA eA) (kindOf_sound B Δ kB eB)
  | all k0 U, Δ, k, h => by
    have h' : (match kindOf (k0 :: Δ) U with
      | some k' => some (Nat.max (k0 + 1) k')
      | none => none) = some k := h
    cases eU : kindOf (k0 :: Δ) U with
    | none => rw [eU] at h'; cases h'
    | some kU =>
      rw [eU] at h'; cases h'
      exact .all _ _ _ _ (kindOf_sound U _ kU eU)

/-- Rocq: `Analysis.HereditarySubstFNorm.kind_of_complete`. -/
theorem kindOf_complete {Δ : List Kind} {T : Typ} {k : Kind} (h : Kinding Δ T k) :
    ∃ k0, kindOf Δ T = some k0 ∧ k0 ≤ k := by
  induction h with
  | var Γ X k k' hX hle => exact ⟨k, hX, hle⟩
  | arrow Γ A B k k' _ _ ih1 ih2 =>
    obtain ⟨k1, e1, h1⟩ := ih1
    obtain ⟨k2, e2, h2⟩ := ih2
    refine ⟨Nat.max k1 k2, ?_, max_le_compat h1 h2⟩
    show (match kindOf Γ A, kindOf Γ B with
      | some k, some k' => some (Nat.max k k')
      | some _, none => none
      | none, _ => none) = _
    rw [e1, e2]
  | all Γ k U k' _ ih =>
    obtain ⟨k1, e1, h1⟩ := ih
    refine ⟨Nat.max (k + 1) k1, ?_, max_le_compat (Nat.le_refl _) h1⟩
    show (match kindOf (k :: Γ) U with
      | some k' => some (Nat.max (k + 1) k')
      | none => none) = _
    rw [e1]

theorem nthError_sv {A : Type} : ∀ (Δ1 Δ2 : List A) (a : A) (X : Nat),
    List.nthError (Δ1 ++ a :: Δ2) (sv Δ1.length X) = List.nthError (Δ1 ++ Δ2) X
  | [], _, _, _ => rfl
  | _ :: _, _, _, 0 => rfl
  | _ :: Δ1, Δ2, a, X + 1 => nthError_sv Δ1 Δ2 a X

/-- Rocq: `Analysis.HereditarySubstFNorm.nth_error_insert`. -/
theorem nthError_insert {A : Type} (Δ1 Δ2 : List A) (a : A) (X : Nat) :
    List.nthError (Δ1 ++ a :: Δ2) (if X < Δ1.length then X else X + 1) = List.nthError (Δ1 ++ Δ2) X := by
  rw [sv_eq]; exact nthError_sv Δ1 Δ2 a X

theorem length_cons_app {A : Type} (a : A) (l1 l2 : List A) : (a :: l1 ++ l2) = a :: (l1 ++ l2) := rfl

/-- Rocq: `Analysis.HereditarySubstFNorm.kinding_weaken`. -/
theorem kinding_weaken {Δ : List Kind} {T : Typ} {k : Kind} (h : Kinding Δ T k) :
    ∀ (Δ1 Δ2 : List Kind) (k0 : Kind), Δ = Δ1 ++ Δ2 → Kinding (Δ1 ++ k0 :: Δ2) (tshift Δ1.length T) k := by
  induction h with
  | var Γ X k k' hX hle =>
    intro Δ1 Δ2 k0 E
    subst E
    rw [tshift_tvar]
    exact .var _ _ _ _ ((nthError_sv Δ1 Δ2 k0 X).trans hX) hle
  | arrow Γ A B k k' _ _ ih1 ih2 =>
    intro Δ1 Δ2 k0 E
    exact .arrow _ _ _ _ _ (ih1 Δ1 Δ2 k0 E) (ih2 Δ1 Δ2 k0 E)
  | all Γ k U k' _ ih =>
    intro Δ1 Δ2 k0 E
    subst E
    exact .all _ _ _ _ (ih (k :: Δ1) Δ2 k0 rfl)

theorem nthError_svar {A : Type} : ∀ (Δ1 Δ2 : List A) (a : A) {X z : Nat},
    svar Δ1.length X = some z → List.nthError (Δ1 ++ Δ2) z = List.nthError (Δ1 ++ a :: Δ2) X
  | [], _, _, 0, _, h => nomatch h
  | [], _, _, _ + 1, _, h => by cases h; rfl
  | _ :: _, _, _, 0, _, h => by cases h; rfl
  | _ :: Δ1, Δ2, a, X + 1, z, h => by
    obtain ⟨z0, h0, rfl⟩ := map_succ_some h
    exact nthError_svar Δ1 Δ2 a h0

/-- Rocq: `Analysis.HereditarySubstFNorm.nth_error_remove`. -/
theorem nthError_remove {A : Type} (Δ1 Δ2 : List A) (a : A) {X : Nat} (h : X ≠ Δ1.length) :
    List.nthError (Δ1 ++ Δ2) (if X < Δ1.length then X else X - 1) = List.nthError (Δ1 ++ a :: Δ2) X := by
  have e := svar_spec Δ1.length X
  rw [ite_eq_right h] at e
  exact nthError_svar Δ1 Δ2 a e

/-- Rocq: `Analysis.HereditarySubstFNorm.nth_error_at`. -/
theorem nthError_at {A : Type} : ∀ (Δ1 Δ2 : List A) (a : A), List.nthError (Δ1 ++ a :: Δ2) Δ1.length = some a
  | [], _, _ => rfl
  | _ :: Δ1, Δ2, a => nthError_at Δ1 Δ2 a

/-- Rocq: `Analysis.HereditarySubstFNorm.kinding_subst`. -/
theorem kinding_subst {Δ : List Kind} {T : Typ} {k' : Kind} (h : Kinding Δ T k') :
    ∀ (Δ1 Δ2 : List Kind) (k : Kind) (C : Typ), Δ = Δ1 ++ k :: Δ2 → Kinding (Δ1 ++ Δ2) C k →
      Kinding (Δ1 ++ Δ2) (tsubst T Δ1.length C) k' := by
  induction h with
  | var Γ X k₁ k₂ hX hle =>
    intro Δ1 Δ2 k0 C E hC
    subst E
    rw [tsubst_tvar]
    cases e : svar Δ1.length X with
    | none =>
      have hX' := svar_none e
      subst hX'
      rw [nthError_at] at hX
      cases hX
      exact kinding_cumul hC hle
    | some z => exact .var _ _ _ _ ((nthError_svar Δ1 Δ2 k0 e).trans hX) hle
  | arrow Γ A B k k'' _ _ ih1 ih2 =>
    intro Δ1 Δ2 k0 C E hC
    exact .arrow _ _ _ _ _ (ih1 Δ1 Δ2 k0 C E hC) (ih2 Δ1 Δ2 k0 C E hC)
  | all Γ k U k'' _ ih =>
    intro Δ1 Δ2 k0 C E hC
    subst E
    exact .all _ _ _ _ (ih (k :: Δ1) Δ2 k0 _ rfl (kinding_weaken hC [] (Δ1 ++ Δ2) k rfl))

/-! ## Normal forms and their typing -/

mutual
/-- Normal forms in spine form; type and term variables have separate de
Bruijn indices. Rocq: `Analysis.HereditarySubstFNorm.nf`. -/
inductive Nf : Type where
  | nlam : Typ → Nf → Nf
  | ntlam : Kind → Nf → Nf
  | nne : Nat → Spine → Nf
/-- Rocq: `Analysis.HereditarySubstFNorm.spine`. -/
inductive Spine : Type where
  | snil : Spine
  | sapp : Nf → Spine → Spine
  | stapp : Typ → Spine → Spine
end

open Nf Spine

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.nsize`. -/
def nsize : Nf → Nat
  | nlam _ t => nsize t + 1
  | ntlam _ t => nsize t + 1
  | nne _ sp => ssize sp + 1
/-- Rocq: `Analysis.HereditarySubstFNorm.ssize`. -/
def ssize : Spine → Nat
  | snil => 0
  | sapp t sp => nsize t + ssize sp + 1
  | stapp _ sp => ssize sp + 1
end

/-- Rocq: `Analysis.HereditarySubstFNorm.sp_app`. -/
def spApp : Spine → Spine → Spine
  | snil, sp2 => sp2
  | sapp t sp, sp2 => sapp t (spApp sp sp2)
  | stapp C sp, sp2 => stapp C (spApp sp sp2)

/-- Contexts interleave kinded type variables and typed term variables.
Rocq: `Analysis.HereditarySubstFNorm.entry`. -/
inductive Entry : Type where
  | EK : Kind → Entry
  | ET : Typ → Entry

open Entry

/-- Rocq: `Analysis.HereditarySubstFNorm.env`. -/
abbrev Env : Type := List Entry

/-- Rocq: `Analysis.HereditarySubstFNorm.kctx`. -/
def kctx : Env → List Kind
  | [] => []
  | EK k :: e => k :: kctx e
  | ET _ :: e => kctx e

/-- Rocq: `Analysis.HereditarySubstFNorm.get_var`. -/
def getVar : Env → Nat → Option Typ
  | [], _ => none
  | EK _ :: e, x => (getVar e x).map (tshift 0)
  | ET A :: _, 0 => some A
  | ET _ :: e, x + 1 => getVar e x

/-- Rocq: `Analysis.HereditarySubstFNorm.cntT`. -/
def cntT : Env → Nat
  | [] => 0
  | EK _ :: e => cntT e
  | ET _ :: e => cntT e + 1

/-- Rocq: `Analysis.HereditarySubstFNorm.kctx_app`. -/
theorem kctx_app : ∀ e1 e2 : Env, kctx (e1 ++ e2) = kctx e1 ++ kctx e2
  | [], _ => rfl
  | EK k :: e1, e2 => congrArg (k :: ·) (kctx_app e1 e2)
  | ET _ :: e1, e2 => kctx_app e1 e2

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.check`. -/
inductive Check : Env → Nf → Typ → Prop where
  | lam (e : Env) (A : Typ) (t : Nf) (B : Typ) : Check (ET A :: e) t B → Check e (nlam A t) (arrow A B)
  | tlam (e : Env) (k : Kind) (t : Nf) (B : Typ) : Check (EK k :: e) t B → Check e (ntlam k t) (all k B)
  | ne (e : Env) (x : Nat) (sp : Spine) (A T : Typ) : getVar e x = some A → SpineTy e A sp T →
      Check e (nne x sp) T
/-- Rocq: `Analysis.HereditarySubstFNorm.spine_ty`. -/
inductive SpineTy : Env → Typ → Spine → Typ → Prop where
  | nil (e : Env) (A : Typ) : SpineTy e A snil A
  | app (e : Env) (A B : Typ) (t : Nf) (sp : Spine) (T : Typ) :
      Check e t A → SpineTy e B sp T → SpineTy e (arrow A B) (sapp t sp) T
  | tapp (e : Env) (k : Kind) (B C : Typ) (sp : Spine) (T : Typ) :
      Kinding (kctx e) C k → SpineTy e (tsubst B 0 C) sp T → SpineTy e (all k B) (stapp C sp) T
end

/-- Rocq: `Analysis.HereditarySubstFNorm.spine_app`. -/
theorem spine_app : ∀ {e : Env} {A : Typ} {sp1 : Spine} {U : Typ}, SpineTy e A sp1 U →
    ∀ {sp2 : Spine} {T : Typ}, SpineTy e U sp2 T → SpineTy e A (spApp sp1 sp2) T
  | _, _, _, _, .nil _ _, _, _, h2 => h2
  | _, _, _, _, .app _ _ _ _ _ _ ht hsp, _, _, h2 => .app _ _ _ _ _ _ ht (spine_app hsp h2)
  | _, _, _, _, .tapp _ _ _ _ _ _ hk hsp, _, _, h2 => .tapp _ _ _ _ _ _ hk (spine_app hsp h2)

/-! ## Weakening by a term variable -/

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.shift_tm`. -/
def shiftTm (c : Nat) : Nf → Nf
  | nlam A t => nlam A (shiftTm (c + 1) t)
  | ntlam k t => ntlam k (shiftTm c t)
  | nne y sp => nne (if y < c then y else y + 1) (shiftSp c sp)
/-- Rocq: `Analysis.HereditarySubstFNorm.shift_sp`. -/
def shiftSp (c : Nat) : Spine → Spine
  | snil => snil
  | sapp t sp => sapp (shiftTm c t) (shiftSp c sp)
  | stapp C sp => stapp C (shiftSp c sp)
end

theorem getVar_sv : ∀ (e1 e2 : Env) (A : Typ) (y : Nat),
    getVar (e1 ++ ET A :: e2) (sv (cntT e1) y) = getVar (e1 ++ e2) y
  | [], _, _, _ => rfl
  | EK _ :: e1, e2, A, y => congrArg (Option.map (tshift 0)) (getVar_sv e1 e2 A y)
  | ET _ :: _, _, _, 0 => rfl
  | ET _ :: e1, e2, A, y + 1 => getVar_sv e1 e2 A y

/-- Rocq: `Analysis.HereditarySubstFNorm.get_var_insert`. -/
theorem getVar_insert (e1 e2 : Env) (A : Typ) (y : Nat) :
    getVar (e1 ++ ET A :: e2) (if y < cntT e1 then y else y + 1) = getVar (e1 ++ e2) y := by
  rw [sv_eq]; exact getVar_sv e1 e2 A y

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.weaken_tm`. -/
theorem weaken_tm : ∀ {e : Env} {t : Nf} {T : Typ}, Check e t T →
    ∀ (e1 e2 : Env) (A : Typ), e = e1 ++ e2 → Check (e1 ++ ET A :: e2) (shiftTm (cntT e1) t) T
  | _, _, _, .lam _ A t B h, e1, e2, A0, E => by
    subst E; exact .lam _ _ _ _ (weaken_tm h (ET A :: e1) e2 A0 rfl)
  | _, _, _, .tlam _ k t B h, e1, e2, A0, E => by
    subst E; exact .tlam _ _ _ _ (weaken_tm h (EK k :: e1) e2 A0 rfl)
  | _, _, _, .ne _ x sp A T hx hsp, e1, e2, A0, E => by
    subst E
    exact .ne _ _ _ _ _ ((getVar_insert e1 e2 A0 x).trans hx) (weaken_sp hsp e1 e2 A0 rfl)
/-- The spine part of `weaken_tm`. -/
theorem weaken_sp : ∀ {e : Env} {B : Typ} {sp : Spine} {T : Typ}, SpineTy e B sp T →
    ∀ (e1 e2 : Env) (A : Typ), e = e1 ++ e2 → SpineTy (e1 ++ ET A :: e2) B (shiftSp (cntT e1) sp) T
  | _, _, _, _, .nil _ _, _, _, _, _ => .nil _ _
  | _, _, _, _, .app _ _ _ _ _ _ ht hsp, e1, e2, A0, E =>
    .app _ _ _ _ _ _ (weaken_tm ht e1 e2 A0 E) (weaken_sp hsp e1 e2 A0 E)
  | _, _, _, _, .tapp _ _ _ _ _ _ hk hsp, e1, e2, A0, E => by
    subst E
    refine .tapp _ _ _ _ _ _ ?_ (weaken_sp hsp e1 e2 A0 rfl)
    rw [kctx_app] at hk ⊢
    exact hk
end

/-! ## Weakening by a type variable -/

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.tshift_tm`. -/
def tshiftTm (X : Nat) : Nf → Nf
  | nlam A t => nlam (tshift X A) (tshiftTm X t)
  | ntlam k t => ntlam k (tshiftTm (X + 1) t)
  | nne y sp => nne y (tshiftSp X sp)
/-- Rocq: `Analysis.HereditarySubstFNorm.tshift_sp`. -/
def tshiftSp (X : Nat) : Spine → Spine
  | snil => snil
  | sapp t sp => sapp (tshiftTm X t) (tshiftSp X sp)
  | stapp C sp => stapp (tshift X C) (tshiftSp X sp)
end

/-- Rocq: `Analysis.HereditarySubstFNorm.shift_env`. -/
def shiftEnv : Nat → Env → Env
  | _, [] => []
  | X, EK k :: e => EK k :: shiftEnv (X - 1) e
  | X, ET A :: e => ET (tshift X A) :: shiftEnv X e

/-- Rocq: `Analysis.HereditarySubstFNorm.kctx_shift_env`. -/
theorem kctx_shiftEnv : ∀ (e : Env) (X : Nat), kctx (shiftEnv X e) = kctx e
  | [], _ => rfl
  | EK k :: e, X => congrArg (k :: ·) (kctx_shiftEnv e (X - 1))
  | ET _ :: e, X => kctx_shiftEnv e X

theorem map_tshift (A : Typ) (n : Nat) : tshift 0 (tshift n A) = tshift (n + 1) (tshift 0 A) :=
  tshift_tshift A (Nat.zero_le n)

/-- Rocq: `Analysis.HereditarySubstFNorm.get_var_shift_env`. -/
theorem getVar_shiftEnv : ∀ (e1 e2 : Env) (k : Kind) (y : Nat),
    getVar (shiftEnv (kctx e1).length e1 ++ EK k :: e2) y =
      (getVar (e1 ++ e2) y).map (tshift (kctx e1).length)
  | [], e2, k, y => by
    show (getVar e2 y).map (tshift 0) = _
    rfl
  | EK k' :: e1, e2, k, y => by
    show (getVar (shiftEnv (kctx e1).length e1 ++ EK k :: e2) y).map (tshift 0) =
      ((getVar (e1 ++ e2) y).map (tshift 0)).map (tshift ((kctx e1).length + 1))
    rw [getVar_shiftEnv e1 e2 k y]
    cases getVar (e1 ++ e2) y with
    | none => rfl
    | some A => exact congrArg some (map_tshift A _)
  | ET _ :: _, _, _, 0 => rfl
  | ET _ :: e1, e2, k, y + 1 => getVar_shiftEnv e1 e2 k y

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.weaken_ty`. -/
theorem weaken_ty : ∀ {e : Env} {t : Nf} {T : Typ}, Check e t T →
    ∀ (e1 e2 : Env) (k : Kind), e = e1 ++ e2 →
      Check (shiftEnv (kctx e1).length e1 ++ EK k :: e2) (tshiftTm (kctx e1).length t)
        (tshift (kctx e1).length T)
  | _, _, _, .lam _ A t B h, e1, e2, k, E => by
    subst E; exact .lam _ _ _ _ (weaken_ty h (ET A :: e1) e2 k rfl)
  | _, _, _, .tlam _ k' t B h, e1, e2, k, E => by
    subst E; exact .tlam _ _ _ _ (weaken_ty h (EK k' :: e1) e2 k rfl)
  | _, _, _, .ne _ x sp A T hx hsp, e1, e2, k, E => by
    subst E
    refine .ne _ _ _ _ _ ?_ (weaken_sp_ty hsp e1 e2 k rfl)
    rw [getVar_shiftEnv, hx]; rfl
/-- The spine part of `weaken_ty`. -/
theorem weaken_sp_ty : ∀ {e : Env} {B : Typ} {sp : Spine} {T : Typ}, SpineTy e B sp T →
    ∀ (e1 e2 : Env) (k : Kind), e = e1 ++ e2 →
      SpineTy (shiftEnv (kctx e1).length e1 ++ EK k :: e2) (tshift (kctx e1).length B)
        (tshiftSp (kctx e1).length sp) (tshift (kctx e1).length T)
  | _, _, _, _, .nil _ _, _, _, _, _ => .nil _ _
  | _, _, _, _, .app _ _ _ _ _ _ ht hsp, e1, e2, k, E =>
    .app _ _ _ _ _ _ (weaken_ty ht e1 e2 k E) (weaken_sp_ty hsp e1 e2 k E)
  | _, _, _, _, .tapp _ k' B C sp T hk hsp, e1, e2, k, E => by
    subst E
    refine .tapp _ _ _ _ _ _ ?_ ?_
    · rw [kctx_app, kctx_shiftEnv]
      rw [kctx_app] at hk
      exact kinding_weaken hk (kctx e1) (kctx e2) k rfl
    · rw [← tshift_tsubst_ge B C (Nat.zero_le _)]
      exact weaken_sp_ty hsp e1 e2 k rfl
end

/-! ## Type substitution into normal forms -/

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.tsubst_tm`. -/
def tsubstTm : Nf → Nat → Typ → Nf
  | nlam A t, X, C => nlam (tsubst A X C) (tsubstTm t X C)
  | ntlam k t, X, C => ntlam k (tsubstTm t (X + 1) (tshift 0 C))
  | nne y sp, X, C => nne y (tsubstSp sp X C)
/-- Rocq: `Analysis.HereditarySubstFNorm.tsubst_sp`. -/
def tsubstSp : Spine → Nat → Typ → Spine
  | snil, _, _ => snil
  | sapp t sp, X, C => sapp (tsubstTm t X C) (tsubstSp sp X C)
  | stapp D sp, X, C => stapp (tsubst D X C) (tsubstSp sp X C)
end

/-- Rocq: `Analysis.HereditarySubstFNorm.env_subst`. -/
inductive EnvSubst : Nat → Typ → Env → Env → Prop where
  | here (e : Env) (k : Kind) (C : Typ) : Kinding (kctx e) C k → EnvSubst 0 C (EK k :: e) e
  | var (X : Nat) (C : Typ) (e e' : Env) (A : Typ) : EnvSubst X C e e' →
      EnvSubst X C (ET A :: e) (ET (tsubst A X C) :: e')
  | kind (X : Nat) (C : Typ) (e e' : Env) (k : Kind) : EnvSubst X C e e' →
      EnvSubst (X + 1) (tshift 0 C) (EK k :: e) (EK k :: e')

/-- Rocq: `Analysis.HereditarySubstFNorm.env_subst_get_var`. -/
theorem envSubst_getVar {X : Nat} {C : Typ} {e e' : Env} (h : EnvSubst X C e e') :
    ∀ y, getVar e' y = (getVar e y).map (fun A => tsubst A X C) := by
  induction h with
  | here e k C _ =>
    intro y
    show _ = ((getVar e y).map (tshift 0)).map _
    cases getVar e y with
    | none => rfl
    | some A => exact congrArg some (tsubst_tshift A 0 C).symm
  | var X C e e' A _ ih =>
    intro y
    cases y with
    | zero => rfl
    | succ y => exact ih y
  | kind X C e e' k _ ih =>
    intro y
    show (getVar e' y).map (tshift 0) = ((getVar e y).map (tshift 0)).map _
    rw [ih y]
    cases getVar e y with
    | none => rfl
    | some A => exact congrArg some (tshift_tsubst_le A C (Nat.zero_le X))

/-- Rocq: `Analysis.HereditarySubstFNorm.env_subst_kctx`. -/
theorem envSubst_kctx {X : Nat} {C : Typ} {e e' : Env} (h : EnvSubst X C e e') :
    ∃ Δ1 Δ2 k, kctx e = Δ1 ++ k :: Δ2 ∧ kctx e' = Δ1 ++ Δ2 ∧ Δ1.length = X ∧ Kinding (kctx e') C k := by
  induction h with
  | here e k C hC => exact ⟨[], kctx e, k, rfl, rfl, rfl, hC⟩
  | var X C e e' A _ ih => exact ih
  | kind X C e e' k _ ih =>
    obtain ⟨Δ1, Δ2, k0, E1, E2, L, HC⟩ := ih
    refine ⟨k :: Δ1, Δ2, k0, congrArg (k :: ·) E1, congrArg (k :: ·) E2, congrArg (· + 1) L, ?_⟩
    show Kinding (k :: kctx e') _ _
    rw [E2] at HC ⊢
    exact kinding_weaken HC [] (Δ1 ++ Δ2) k rfl

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.subst_ty`. -/
theorem subst_ty : ∀ {e : Env} {t : Nf} {T : Typ}, Check e t T →
    ∀ (X : Nat) (C : Typ) (e' : Env), EnvSubst X C e e' → Check e' (tsubstTm t X C) (tsubst T X C)
  | _, _, _, .lam _ A t B h, X, C, e', HS => .lam _ _ _ _ (subst_ty h X C _ (.var _ _ _ _ _ HS))
  | _, _, _, .tlam _ k t B h, X, C, e', HS => .tlam _ _ _ _ (subst_ty h _ _ _ (.kind _ _ _ _ _ HS))
  | _, _, _, .ne _ x sp A T hx hsp, X, C, e', HS => by
    refine .ne _ _ _ _ _ ?_ (subst_sp_ty hsp X C e' HS)
    rw [envSubst_getVar HS, hx]; rfl
/-- The spine part of `subst_ty`. -/
theorem subst_sp_ty : ∀ {e : Env} {B : Typ} {sp : Spine} {T : Typ}, SpineTy e B sp T →
    ∀ (X : Nat) (C : Typ) (e' : Env), EnvSubst X C e e' →
      SpineTy e' (tsubst B X C) (tsubstSp sp X C) (tsubst T X C)
  | _, _, _, _, .nil _ _, _, _, _, _ => .nil _ _
  | _, _, _, _, .app _ _ _ _ _ _ ht hsp, X, C, e', HS =>
    .app _ _ _ _ _ _ (subst_ty ht X C e' HS) (subst_sp_ty hsp X C e' HS)
  | _, _, _, _, .tapp _ k B D sp T hk hsp, X, C, e', HS => by
    refine .tapp _ _ _ _ _ _ ?_ ?_
    · obtain ⟨Δ1, Δ2, k1, E1, E2, L, HC⟩ := envSubst_kctx HS
      rw [E2, ← L]
      rw [E1] at hk
      exact kinding_subst hk Δ1 Δ2 k1 C rfl (E2 ▸ HC)
    · rw [← tsubst_tsubst B D C (Nat.zero_le X)]
      exact subst_sp_ty hsp X C e' HS
end

/-! ## The graph of hereditary substitution

`CH Δ U u x t` substitutes `u : U` for the term variable `x` in `t`; `CS`
does the same in a spine; `CA Δ U u sp` applies `u : U` to the spine `sp`.
`Δ` is the kind context, used to check the kind of a type argument before
reducing a type-application redex. -/

/-- Rocq: `Analysis.HereditarySubstFNorm.call`. -/
inductive Call : Type where
  | CH : List Kind → Typ → Nf → Nat → Nf → Call
  | CS : List Kind → Typ → Nf → Nat → Spine → Call
  | CA : List Kind → Typ → Nf → Spine → Call

/-- Rocq: `Analysis.HereditarySubstFNorm.res`. -/
inductive Res : Type where
  | rn : Nf → Res
  | rs : Spine → Res

open Call Res

/-- Rocq: `Analysis.HereditarySubstFNorm.unshift`. -/
def unshift (x y : Nat) : Nat := if y < x then y else y - 1

/-- The applications that are not redexes of the expected shape; on
well-typed input they never occur. Rocq: `Analysis.HereditarySubstFNorm.stuck`. -/
def Stuck (Δ : List Kind) (U : Typ) (u : Nf) (sp : Spine) : Prop :=
  match u, sp with
  | nlam _ _, sapp _ _ =>
    match U with
    | arrow _ _ => False
    | tvar _ => True
    | all _ _ => True
  | nlam _ _, stapp _ _ => True
  | ntlam _ _, sapp _ _ => True
  | ntlam _ _, stapp C _ =>
    match U with
    | all k _ => kindOf Δ C = none ∨ ∃ k0, kindOf Δ C = some k0 ∧ k < k0
    | tvar _ => True
    | arrow _ _ => True
  | nlam _ _, snil => False
  | ntlam _ _, snil => False
  | nne _ _, _ => False

/-- Rocq: `Analysis.HereditarySubstFNorm.HS`. -/
inductive HS : Call → Res → Prop where
  | hs_lam (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) (A : Typ) (t r : Nf) :
      HS (CH Δ U (shiftTm 0 u) (x + 1) t) (rn r) → HS (CH Δ U u x (nlam A t)) (rn (nlam A r))
  | hs_tlam (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) (k : Kind) (t r : Nf) :
      HS (CH (k :: Δ) (tshift 0 U) (tshiftTm 0 u) x t) (rn r) → HS (CH Δ U u x (ntlam k t)) (rn (ntlam k r))
  | hs_var (Δ : List Kind) (U : Typ) (u : Nf) (x y : Nat) (sp sp' : Spine) :
      x ≠ y → HS (CS Δ U u x sp) (rs sp') → HS (CH Δ U u x (nne y sp)) (rn (nne (unshift x y) sp'))
  | hs_head (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) (sp sp' : Spine) (r : Nf) :
      HS (CS Δ U u x sp) (rs sp') → HS (CA Δ U u sp') (rn r) → HS (CH Δ U u x (nne x sp)) (rn r)
  | hs_snil (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) : HS (CS Δ U u x snil) (rs snil)
  | hs_sapp (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) (t : Nf) (sp : Spine) (t' : Nf) (sp' : Spine) :
      HS (CH Δ U u x t) (rn t') → HS (CS Δ U u x sp) (rs sp') → HS (CS Δ U u x (sapp t sp)) (rs (sapp t' sp'))
  | hs_stapp (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) (C : Typ) (sp sp' : Spine) :
      HS (CS Δ U u x sp) (rs sp') → HS (CS Δ U u x (stapp C sp)) (rs (stapp C sp'))
  | ha_nil (Δ : List Kind) (U : Typ) (u : Nf) : HS (CA Δ U u snil) (rn u)
  | ha_ne (Δ : List Kind) (U : Typ) (y : Nat) (sp0 sp : Spine) :
      sp ≠ snil → HS (CA Δ U (nne y sp0) sp) (rn (nne y (spApp sp0 sp)))
  | ha_beta (Δ : List Kind) (A B A' : Typ) (b t : Nf) (sp : Spine) (r1 r : Nf) :
      HS (CH Δ A t 0 b) (rn r1) → HS (CA Δ B r1 sp) (rn r) → HS (CA Δ (arrow A B) (nlam A' b) (sapp t sp)) (rn r)
  | ha_tbeta (Δ : List Kind) (k : Kind) (B : Typ) (k' : Kind) (b : Nf) (C : Typ) (sp : Spine) (k0 : Kind)
      (r : Nf) : kindOf Δ C = some k0 → k0 ≤ k → HS (CA Δ (tsubst B 0 C) (tsubstTm b 0 C) sp) (rn r) →
      HS (CA Δ (all k B) (ntlam k' b) (stapp C sp)) (rn r)
  | ha_stuck (Δ : List Kind) (U : Typ) (u : Nf) (sp : Spine) : Stuck Δ U u sp → HS (CA Δ U u sp) (rn u)

/-- Rocq: `Analysis.HereditarySubstFNorm.HS_det`. -/
theorem HS_det {c : Call} {r1 : Res} (h : HS c r1) : ∀ {r2 : Res}, HS c r2 → r1 = r2 := by
  induction h with
  | hs_lam _ _ _ _ _ _ _ _ ih =>
    intro r2 h2; cases h2 with | hs_lam _ _ _ _ _ _ _ h' => cases ih h'; rfl
  | hs_tlam _ _ _ _ _ _ _ _ ih =>
    intro r2 h2; cases h2 with | hs_tlam _ _ _ _ _ _ _ h' => cases ih h'; rfl
  | hs_var _ _ _ _ _ _ _ hxy _ ih =>
    intro r2 h2; cases h2 with
    | hs_var _ _ _ _ _ _ _ _ h' => cases ih h'; rfl
    | hs_head => exact absurd rfl hxy
  | hs_head _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with
    | hs_var _ _ _ _ _ _ _ hxy => exact absurd rfl hxy
    | hs_head _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; exact ih2 h2'
  | hs_snil => intro r2 h2; cases h2; rfl
  | hs_sapp _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with | hs_sapp _ _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; cases ih2 h2'; rfl
  | hs_stapp _ _ _ _ _ _ _ _ ih =>
    intro r2 h2; cases h2 with | hs_stapp _ _ _ _ _ _ _ h' => cases ih h'; rfl
  | ha_nil =>
    intro r2 h2; cases h2 with
    | ha_nil => rfl
    | ha_ne _ _ _ _ _ hne => exact absurd rfl hne
    | ha_stuck _ _ _ _ hs => rfl
  | ha_ne _ _ _ _ _ hne =>
    intro r2 h2; cases h2 with
    | ha_nil => exact absurd rfl hne
    | ha_ne => rfl
    | ha_stuck _ _ _ _ hs => exact hs.elim
  | ha_beta _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with
    | ha_beta _ _ _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; exact ih2 h2'
    | ha_stuck _ _ _ _ hs => exact hs.elim
  | ha_tbeta _ _ _ _ _ _ _ k0 _ hk hle _ ih =>
    intro r2 h2; cases h2 with
    | ha_tbeta _ _ _ _ _ _ _ _ _ _ _ h' => exact ih h'
    | ha_stuck _ _ _ _ hs =>
      rcases hs with hs | ⟨k1, hs, hlt⟩
      · rw [hk] at hs; cases hs
      · rw [hk] at hs; cases hs
        exact absurd (Nat.lt_of_lt_of_le hlt hle) (Nat.lt_irrefl _)
  | ha_stuck _ _ _ _ hs =>
    intro r2 h2; cases h2 with
    | ha_nil => rfl
    | ha_ne => exact hs.elim
    | ha_beta => exact hs.elim
    | ha_tbeta _ _ _ _ _ _ _ _ _ hk hle _ =>
      rcases hs with hs | ⟨k1, hs, hlt⟩
      · rw [hk] at hs; cases hs
      · rw [hk] at hs; cases hs
        exact absurd (Nat.lt_of_lt_of_le hlt hle) (Nat.lt_irrefl _)
    | ha_stuck => rfl

/-- Rocq: `Analysis.HereditarySubstFNorm.res_ok`. -/
def ResOk : Call → Res → Prop
  | CS _ _ _ _ _, rs _ => True
  | CS _ _ _ _ _, rn _ => False
  | CH _ _ _ _ _, rn _ => True
  | CH _ _ _ _ _, rs _ => False
  | CA _ _ _ _, rn _ => True
  | CA _ _ _ _, rs _ => False

/-- Rocq: `Analysis.HereditarySubstFNorm.HS_res_ok`. -/
theorem HS_res_ok {c : Call} {r : Res} (h : HS c r) : ResOk c r := by
  cases h <;> trivial

/-! ## The ordinal measure and termination -/

/-- Rocq: `Analysis.HereditarySubstFNorm.hmeasure`. -/
def hmeasure : Call → Ordinal.{0}
  | CH _ U _ _ t => ω * tord U + ofNat (nsize t)
  | CS _ U _ _ sp => ω * tord U + ofNat (ssize sp)
  | CA _ U _ _ => ω * tord U

/-- Rocq: `Analysis.HereditarySubstFNorm.add_nat_lt'`. -/
theorem add_nat_lt' (a : Ordinal.{0}) {m n : Nat} (h : m < n) : a + ofNat m < a + ofNat n :=
  add_lt_add_left a (ofNat_increasing h)

/-- Rocq: `Analysis.HereditarySubstFNorm.below_head`. -/
theorem below_head (a : Ordinal.{0}) (n : Nat) : a < a + ofNat (n + 1) :=
  lt_of_le_of_lt (le_add_right a (ofNat 0)) (add_nat_lt' a (Nat.zero_lt_succ n))

/-- Rocq: `Analysis.HereditarySubstFNorm.below_major`. -/
theorem below_major {a a' : Ordinal.{0}} (d : Nat) (h : a' < a) : ω * a' + ofNat d < ω * a :=
  lt_of_lt_of_le (lex_lt_major 0 d h) (add_zero _).le

/-- Rocq: `Analysis.HereditarySubstFNorm.below_major'`. -/
theorem below_major' {a a' : Ordinal.{0}} (h : a' < a) : ω * a' < ω * a := mul_lt_mul_left omega_gt0 h

/-- Rocq: `Analysis.HereditarySubstFNorm.tord_shift_measure`. -/
theorem tord_shift_measure (U : Typ) (n : Nat) :
    ω * tord (tshift 0 U) + ofNat n ≈ ω * tord U + ofNat n :=
  add_congr (mul_congr (equiv_refl ω) (tord_tshift U 0)) (equiv_refl _)

theorem lt_succ_add_l (a b : Nat) : a < a + b + 1 := Nat.lt_succ_of_le (Nat.le_add_right _ _)
theorem lt_succ_add_r (a b : Nat) : b < a + b + 1 := Nat.lt_succ_of_le (Nat.le_add_left _ _)

/-- Rocq: `Analysis.HereditarySubstFNorm.hsub_total`. -/
def hsub_total : (c : Call) → { r // HS c r } :=
  (InvImage.wf hmeasure lt_wf).fix fun c IH =>
    match c with
    | CH Δ U u x (nlam A t) =>
      match IH (CH Δ U (shiftTm 0 u) (x + 1) t) (add_nat_lt' _ (Nat.lt_succ_self _)) with
      | ⟨rn r, h⟩ => ⟨rn (nlam A r), .hs_lam _ _ _ _ _ _ _ h⟩
      | ⟨rs _, h⟩ => (HS_res_ok h).elim
    | CH Δ U u x (ntlam k t) =>
      match IH (CH (k :: Δ) (tshift 0 U) (tshiftTm 0 u) x t)
          (lt_of_le_of_lt (tord_shift_measure U _).le (add_nat_lt' _ (Nat.lt_succ_self _))) with
      | ⟨rn r, h⟩ => ⟨rn (ntlam k r), .hs_tlam _ _ _ _ _ _ _ h⟩
      | ⟨rs _, h⟩ => (HS_res_ok h).elim
    | CH Δ U u x (nne y sp) =>
      match IH (CS Δ U u x sp) (add_nat_lt' _ (Nat.lt_succ_self _)) with
      | ⟨rn _, h⟩ => (HS_res_ok h).elim
      | ⟨rs sp', hsp⟩ =>
        if hxy : x = y then by
          subst hxy
          exact match IH (CA Δ U u sp') (below_head _ _) with
            | ⟨rn r, h⟩ => ⟨rn r, .hs_head _ _ _ _ _ _ _ hsp h⟩
            | ⟨rs _, h⟩ => (HS_res_ok h).elim
        else ⟨rn (nne (unshift x y) sp'), .hs_var _ _ _ _ _ _ _ hxy hsp⟩
    | CS _ _ _ _ snil => ⟨rs snil, .hs_snil _ _ _ _⟩
    | CS Δ U u x (sapp t sp) =>
      match IH (CH Δ U u x t) (add_nat_lt' _ (lt_succ_add_l _ _)),
          IH (CS Δ U u x sp) (add_nat_lt' _ (lt_succ_add_r _ _)) with
      | ⟨rn t', ht⟩, ⟨rs sp', hsp⟩ => ⟨rs (sapp t' sp'), .hs_sapp _ _ _ _ _ _ _ _ ht hsp⟩
      | ⟨rn _, _⟩, ⟨rn _, h⟩ => (HS_res_ok h).elim
      | ⟨rs _, h⟩, _ => (HS_res_ok h).elim
    | CS Δ U u x (stapp C sp) =>
      match IH (CS Δ U u x sp) (add_nat_lt' _ (Nat.lt_succ_self _)) with
      | ⟨rs sp', hsp⟩ => ⟨rs (stapp C sp'), .hs_stapp _ _ _ _ _ _ _ hsp⟩
      | ⟨rn _, h⟩ => (HS_res_ok h).elim
    | CA _ _ u snil => ⟨rn u, .ha_nil _ _ _⟩
    | CA Δ U (nlam A' b) (sapp t sp1) =>
      match U with
      | arrow A B =>
        match IH (CH Δ A t 0 b) (below_major _ (tord_arrow_l A B)) with
        | ⟨rs _, h⟩ => (HS_res_ok h).elim
        | ⟨rn r1, h1⟩ =>
          match IH (CA Δ B r1 sp1) (below_major' (tord_arrow_r A B)) with
          | ⟨rn r, h2⟩ => ⟨rn r, .ha_beta _ _ _ _ _ _ _ _ _ h1 h2⟩
          | ⟨rs _, h⟩ => (HS_res_ok h).elim
      | tvar _ => ⟨rn (nlam A' b), .ha_stuck _ _ _ _ trivial⟩
      | all _ _ => ⟨rn (nlam A' b), .ha_stuck _ _ _ _ trivial⟩
    | CA _ _ (nlam A' b) (stapp _ _) => ⟨rn (nlam A' b), .ha_stuck _ _ _ _ trivial⟩
    | CA _ _ (ntlam k' b) (sapp _ _) => ⟨rn (ntlam k' b), .ha_stuck _ _ _ _ trivial⟩
    | CA Δ U (ntlam k' b) (stapp C sp1) =>
      match U with
      | all k B =>
        match e : kindOf Δ C with
        | some k0 =>
          if hk : k0 ≤ k then
            match IH (CA Δ (tsubst B 0 C) (tsubstTm b 0 C) sp1)
                (below_major' (tord_inst (Γ := Δ) B (kinding_cumul (kindOf_sound C Δ k0 e) hk))) with
            | ⟨rn r, h2⟩ => ⟨rn r, .ha_tbeta _ _ _ _ _ _ _ _ _ e hk h2⟩
            | ⟨rs _, h⟩ => (HS_res_ok h).elim
          else ⟨rn (ntlam k' b), .ha_stuck _ _ _ _ (.inr ⟨k0, e, Nat.lt_of_not_le hk⟩)⟩
        | none => ⟨rn (ntlam k' b), .ha_stuck _ _ _ _ (.inl e)⟩
      | tvar _ => ⟨rn (ntlam k' b), .ha_stuck _ _ _ _ trivial⟩
      | arrow _ _ => ⟨rn (ntlam k' b), .ha_stuck _ _ _ _ trivial⟩
    | CA _ _ (nne y sp0) (sapp t sp1) =>
      ⟨rn (nne y (spApp sp0 (sapp t sp1))), .ha_ne _ _ _ _ _ (fun h => nomatch h)⟩
    | CA _ _ (nne y sp0) (stapp C sp1) =>
      ⟨rn (nne y (spApp sp0 (stapp C sp1))), .ha_ne _ _ _ _ _ (fun h => nomatch h)⟩

/-! ## Typing preservation -/

theorem getVar_svar : ∀ (e1 e2 : Env) (U0 : Typ) {y z : Nat},
    svar (cntT e1) y = some z → getVar (e1 ++ e2) z = getVar (e1 ++ ET U0 :: e2) y
  | [], _, _, 0, _, h => nomatch h
  | [], _, _, _ + 1, _, h => by cases h; rfl
  | EK _ :: e1, e2, U0, y, z, h => congrArg (Option.map (tshift 0)) (getVar_svar e1 e2 U0 h)
  | ET _ :: _, _, _, 0, _, h => by cases h; rfl
  | ET _ :: e1, e2, U0, y + 1, z, h => by
    obtain ⟨z0, h0, rfl⟩ := map_succ_some h
    exact getVar_svar e1 e2 U0 h0

/-- Removing the substituted variable from a context. Rocq: `Analysis.HereditarySubstFNorm.get_var_remove`. -/
theorem getVar_remove (e1 e2 : Env) (U0 : Typ) {x y : Nat} (hx : cntT e1 = x) (hxy : x ≠ y) :
    getVar (e1 ++ e2) (unshift x y) = getVar (e1 ++ ET U0 :: e2) y := by
  have e := svar_spec x y
  rw [ite_eq_right (fun h => hxy h.symm)] at e
  subst hx
  exact getVar_svar e1 e2 U0 e

/-- Rocq: `Analysis.HereditarySubstFNorm.post`. -/
def Post : Call → Res → Prop
  | CH Δ U u x t, rn r =>
    ∀ e1 e2 U0 T, Δ = kctx (e1 ++ ET U0 :: e2) → cntT e1 = x →
      getVar (e1 ++ ET U0 :: e2) x = some U → Check (e1 ++ e2) u U →
      Check (e1 ++ ET U0 :: e2) t T → Check (e1 ++ e2) r T
  | CS Δ U u x sp, rs sp' =>
    ∀ e1 e2 U0 A T, Δ = kctx (e1 ++ ET U0 :: e2) → cntT e1 = x →
      getVar (e1 ++ ET U0 :: e2) x = some U → Check (e1 ++ e2) u U →
      SpineTy (e1 ++ ET U0 :: e2) A sp T → SpineTy (e1 ++ e2) A sp' T
  | CA Δ U u sp, rn r => ∀ e T, Δ = kctx e → Check e u U → SpineTy e U sp T → Check e r T
  | CH _ _ _ _ _, rs _ => True
  | CS _ _ _ _ _, rn _ => True
  | CA _ _ _ _, rs _ => True

/-- Rocq: `Analysis.HereditarySubstFNorm.kctx_remove`. -/
theorem kctx_remove (e1 e2 : Env) (U0 : Typ) : kctx (e1 ++ ET U0 :: e2) = kctx (e1 ++ e2) := by
  rw [kctx_app, kctx_app]; rfl

/-- On well-typed input, the stuck applications do not occur. -/
theorem not_stuck {e : Env} {U : Typ} {u : Nf} {sp : Spine} {T : Typ} (hu : Check e u U)
    (hs : SpineTy e U sp T) (h : Stuck (kctx e) U u sp) : False := by
  cases hu with
  | lam _ A t B _ =>
    cases hs with
    | nil => exact h
    | app => exact h
  | tlam _ k t B _ =>
    cases hs with
    | nil => exact h
    | tapp _ _ _ C _ _ hk _ =>
      obtain ⟨k0, E, hk0⟩ := kindOf_complete hk
      rcases h with h | ⟨k1, h, hlt⟩
      · rw [E] at h; cases h
      · rw [E] at h; cases h
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hk0)
  | ne => exact h

/-- Rocq: `Analysis.HereditarySubstFNorm.HS_typed`. -/
theorem HS_typed {c : Call} {r : Res} (h : HS c r) : Post c r := by
  induction h with
  | hs_lam Δ U u x A t r _ ih =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | lam _ _ _ B hb =>
      exact .lam _ _ _ _ (ih (ET A :: e1) e2 U0 B HΔ (congrArg (· + 1) Hx) Hg
        (weaken_tm Hu [] (e1 ++ e2) A rfl) hb)
  | hs_tlam Δ U u x k t r _ ih =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | tlam _ _ _ B hb =>
      refine .tlam _ _ _ _ (ih (EK k :: e1) e2 U0 B (congrArg (k :: ·) HΔ) Hx ?_
        (weaken_ty Hu [] (e1 ++ e2) k rfl) hb)
      show (getVar (e1 ++ ET U0 :: e2) x).map (tshift 0) = _
      rw [Hg]; rfl
  | hs_var Δ U u x y sp sp' hxy _ ih =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | ne _ _ _ A _ hy hsp =>
      exact .ne _ _ _ _ _ ((getVar_remove e1 e2 U0 Hx hxy).trans hy) (ih e1 e2 U0 A T HΔ Hx Hg Hu hsp)
  | hs_head Δ U u x sp sp' r _ _ ih1 ih2 =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | ne _ _ _ A _ hy hsp =>
      rw [Hg] at hy; cases hy
      exact ih2 (e1 ++ e2) T (HΔ.trans (kctx_remove e1 e2 U0)) Hu (ih1 e1 e2 U0 U T HΔ Hx Hg Hu hsp)
  | hs_snil =>
    intro e1 e2 U0 A T _ _ _ _ Hs
    cases Hs; exact .nil _ _
  | hs_sapp Δ U u x t sp t' sp' _ _ ih1 ih2 =>
    intro e1 e2 U0 A T HΔ Hx Hg Hu Hs
    cases Hs with
    | app _ A' B _ _ _ ht hsp =>
      exact .app _ _ _ _ _ _ (ih1 e1 e2 U0 A' HΔ Hx Hg Hu ht) (ih2 e1 e2 U0 B T HΔ Hx Hg Hu hsp)
  | hs_stapp Δ U u x C sp sp' _ ih =>
    intro e1 e2 U0 A T HΔ Hx Hg Hu Hs
    cases Hs with
    | tapp _ k B _ _ _ hk hsp =>
      refine .tapp _ _ _ _ _ _ ?_ (ih e1 e2 U0 _ T HΔ Hx Hg Hu hsp)
      rw [← kctx_remove e1 e2 U0]; exact hk
  | ha_nil =>
    intro e T _ Hu Hs
    cases Hs; exact Hu
  | ha_ne Δ U y sp0 sp _ =>
    intro e T _ Hu Hs
    cases Hu with
    | ne _ _ _ A _ hy hsp0 => exact .ne _ _ _ _ _ hy (spine_app hsp0 Hs)
  | ha_beta Δ A B A' b t sp r1 r _ _ ih1 ih2 =>
    intro e T HΔ Hu Hs
    cases Hu with
    | lam _ _ _ _ hb =>
      cases Hs with
      | app _ _ _ _ _ _ ht hsp =>
        exact ih2 e T HΔ (ih1 [] e A B HΔ rfl rfl ht hb) hsp
  | ha_tbeta Δ k B k' b C sp k0 r _ _ _ ih =>
    intro e T HΔ Hu Hs
    cases Hu with
    | tlam _ _ _ _ hb =>
      cases Hs with
      | tapp _ _ _ _ _ _ hk hsp =>
        exact ih e T HΔ (subst_ty hb 0 C e (.here e k C hk)) hsp
  | ha_stuck Δ U u sp hs =>
    intro e T HΔ Hu Hs
    subst HΔ
    exact (not_stuck Hu Hs hs).elim

/-! ## The functions -/

/-- Rocq: `Analysis.HereditarySubstFNorm.hsub`. -/
def hsub (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) (t : Nf) : Nf :=
  match (hsub_total (CH Δ U u x t)).1 with
  | rn r => r
  | rs _ => t

/-- Rocq: `Analysis.HereditarySubstFNorm.happ`. -/
def happ (Δ : List Kind) (U : Typ) (u : Nf) (sp : Spine) : Nf :=
  match (hsub_total (CA Δ U u sp)).1 with
  | rn r => r
  | rs _ => u

theorem hsub_HS (Δ : List Kind) (U : Typ) (u : Nf) (x : Nat) (t : Nf) :
    HS (CH Δ U u x t) (rn (hsub Δ U u x t)) := by
  have h := (hsub_total (CH Δ U u x t)).2
  unfold hsub
  generalize (hsub_total (CH Δ U u x t)).1 = q at h ⊢
  cases q with
  | rn _ => exact h
  | rs _ => exact (HS_res_ok h).elim

theorem happ_HS (Δ : List Kind) (U : Typ) (u : Nf) (sp : Spine) : HS (CA Δ U u sp) (rn (happ Δ U u sp)) := by
  have h := (hsub_total (CA Δ U u sp)).2
  unfold happ
  generalize (hsub_total (CA Δ U u sp)).1 = q at h ⊢
  cases q with
  | rn _ => exact h
  | rs _ => exact (HS_res_ok h).elim

/-- Substituting `u : U` for the innermost variable preserves typing.
Rocq: `Analysis.HereditarySubstFNorm.hsub_typed`. -/
theorem hsub_typed {e : Env} {U : Typ} {u t : Nf} {T : Typ} (Ht : Check (ET U :: e) t T) (Hu : Check e u U) :
    Check e (hsub (kctx e) U u 0 t) T :=
  HS_typed (hsub_HS _ _ _ _ _) [] e U T rfl rfl rfl Hu Ht

/-- Applying `u : U` to a well-typed spine preserves typing.
Rocq: `Analysis.HereditarySubstFNorm.happ_typed`. -/
theorem happ_typed {e : Env} {U : Typ} {u : Nf} {sp : Spine} {T : Typ} (Hu : Check e u U)
    (Hs : SpineTy e U sp T) : Check e (happ (kctx e) U u sp) T :=
  HS_typed (happ_HS _ _ _ _) e T rfl Hu Hs

/-! ## Normalization and consistency -/

/-- Rocq: `Analysis.HereditarySubstFNorm.term`. -/
inductive Term : Type where
  | var : Nat → Term
  | abs : Typ → Term → Term
  | app : Term → Term → Term
  | tabs : Kind → Term → Term
  | tapp : Term → Typ → Term

open Term

/-- Rocq: `Analysis.HereditarySubstFNorm.typing`. -/
inductive Typing : Env → Term → Typ → Prop where
  | Var (e : Env) (x : Nat) (T : Typ) : getVar e x = some T → Typing e (var x) T
  | Abs (e : Env) (A : Typ) (t : Term) (B : Typ) : Typing (ET A :: e) t B → Typing e (abs A t) (arrow A B)
  | App (e : Env) (t1 t2 : Term) (A B : Typ) : Typing e t1 (arrow A B) → Typing e t2 A →
      Typing e (app t1 t2) B
  | Tabs (e : Env) (k : Kind) (t : Term) (B : Typ) : Typing (EK k :: e) t B → Typing e (tabs k t) (all k B)
  | Tapp (e : Env) (t : Term) (k : Kind) (B C : Typ) : Typing e t (all k B) → Kinding (kctx e) C k →
      Typing e (tapp t C) (tsubst B 0 C)

/-- Every well-typed term has a normal form of the same type.
Rocq: `Analysis.HereditarySubstFNorm.normalization`. -/
theorem normalization {e : Env} {t : Term} {T : Typ} (h : Typing e t T) : ∃ n, Check e n T := by
  induction h with
  | Var e x T hx => exact ⟨nne x snil, .ne _ _ _ _ _ hx (.nil _ _)⟩
  | Abs e A t B _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨nlam A n, .lam _ _ _ _ hn⟩
  | App e t1 t2 A B _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    exact ⟨_, happ_typed h1 (.app _ _ _ _ _ _ h2 (.nil _ _))⟩
  | Tabs e k t B _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨ntlam k n, .tlam _ _ _ _ hn⟩
  | Tapp e t k B C _ hk ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨_, happ_typed hn (.tapp _ _ _ _ _ _ hk (.nil _ _))⟩

/-- Consistency: the type `∀X:0. X` has no closed inhabitant.
Rocq: `Analysis.HereditarySubstFNorm.consistency`. -/
theorem consistency (t : Term) : ¬ Typing [] t (all 0 (tvar 0)) := fun Ht => by
  obtain ⟨n, hn⟩ := normalization Ht
  cases hn with
  | tlam _ _ _ _ hb =>
    cases hb with
    | ne _ _ _ _ _ hx _ => cases hx
  | ne _ _ _ _ _ hx _ => cases hx

/-! ## Reduction, and the correctness of hereditary substitution

Normal forms embed into raw terms (`emb`); hereditary substitution is correct
in that ordinary substitution followed by β-reduction reaches the same normal
form (`HS_red`). With it, every well-typed term reduces to a normal form of
the same type (`normalization_red`). -/

/-- Rocq: `Analysis.HereditarySubstFNorm.shift_term`. -/
def shiftTerm (c : Nat) : Term → Term
  | var y => var (if y < c then y else y + 1)
  | abs A t => abs A (shiftTerm (c + 1) t)
  | app t1 t2 => app (shiftTerm c t1) (shiftTerm c t2)
  | tabs k t => tabs k (shiftTerm c t)
  | tapp t C => tapp (shiftTerm c t) C

/-- Rocq: `Analysis.HereditarySubstFNorm.tshift_term`. -/
def tshiftTerm (X : Nat) : Term → Term
  | var y => var y
  | abs A t => abs (tshift X A) (tshiftTerm X t)
  | app t1 t2 => app (tshiftTerm X t1) (tshiftTerm X t2)
  | tabs k t => tabs k (tshiftTerm (X + 1) t)
  | tapp t C => tapp (tshiftTerm X t) (tshift X C)

/-- Rocq: `Analysis.HereditarySubstFNorm.tsubst_term`. -/
def tsubstTerm : Term → Nat → Typ → Term
  | var y, _, _ => var y
  | abs A t, X, C => abs (tsubst A X C) (tsubstTerm t X C)
  | app t1 t2, X, C => app (tsubstTerm t1 X C) (tsubstTerm t2 X C)
  | tabs k t, X, C => tabs k (tsubstTerm t (X + 1) (tshift 0 C))
  | tapp t D, X, C => tapp (tsubstTerm t X C) (tsubst D X C)

/-- `subst t x u` substitutes `u` for the term variable `x` in `t`.
Rocq: `Analysis.HereditarySubstFNorm.subst`. -/
def subst : Term → Nat → Term → Term
  | var y, x, u => if y = x then u else var (unshift x y)
  | abs A t, x, u => abs A (subst t (x + 1) (shiftTerm 0 u))
  | app t1 t2, x, u => app (subst t1 x u) (subst t2 x u)
  | tabs k t, x, u => tabs k (subst t x (tshiftTerm 0 u))
  | tapp t C, x, u => tapp (subst t x u) C

/-- Rocq: `Analysis.HereditarySubstFNorm.red1`. -/
inductive Red1 : Term → Term → Prop where
  | beta (A : Typ) (t u : Term) : Red1 (app (abs A t) u) (subst t 0 u)
  | tbeta (k : Kind) (t : Term) (C : Typ) : Red1 (tapp (tabs k t) C) (tsubstTerm t 0 C)
  | abs (A : Typ) (t t' : Term) : Red1 t t' → Red1 (abs A t) (abs A t')
  | app1 (t1 t1' t2 : Term) : Red1 t1 t1' → Red1 (app t1 t2) (app t1' t2)
  | app2 (t1 t2 t2' : Term) : Red1 t2 t2' → Red1 (app t1 t2) (app t1 t2')
  | tabs (k : Kind) (t t' : Term) : Red1 t t' → Red1 (tabs k t) (tabs k t')
  | tapp (t t' : Term) (C : Typ) : Red1 t t' → Red1 (tapp t C) (tapp t' C)

/-- Rocq: `Analysis.HereditarySubstFNorm.reds`. -/
inductive Reds : Term → Term → Prop where
  | refl (t : Term) : Reds t t
  | step (t t' t'' : Term) : Red1 t t' → Reds t' t'' → Reds t t''

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_trans`. -/
theorem reds_trans {t t' t'' : Term} (h : Reds t t') (h' : Reds t' t'') : Reds t t'' := by
  induction h with
  | refl => exact h'
  | step _ _ _ h1 _ ih => exact .step _ _ _ h1 (ih h')

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_one`. -/
theorem reds_one {t t' : Term} (h : Red1 t t') : Reds t t' := .step _ _ _ h (.refl _)

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_abs`. -/
theorem reds_abs (A : Typ) {t t' : Term} (h : Reds t t') : Reds (abs A t) (abs A t') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ h1 _ ih => exact .step _ _ _ (.abs _ _ _ h1) ih

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_tabs`. -/
theorem reds_tabs (k : Kind) {t t' : Term} (h : Reds t t') : Reds (tabs k t) (tabs k t') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ h1 _ ih => exact .step _ _ _ (.tabs _ _ _ h1) ih

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_tapp`. -/
theorem reds_tapp (C : Typ) {t t' : Term} (h : Reds t t') : Reds (tapp t C) (tapp t' C) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ h1 _ ih => exact .step _ _ _ (.tapp _ _ _ h1) ih

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_app1`. -/
theorem reds_app1 (u : Term) {t t' : Term} (h : Reds t t') : Reds (app t u) (app t' u) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ h1 _ ih => exact .step _ _ _ (.app1 _ _ _ h1) ih

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_app2`. -/
theorem reds_app2 (u : Term) {t t' : Term} (h : Reds t t') : Reds (app u t) (app u t') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ h1 _ ih => exact .step _ _ _ (.app2 _ _ _ h1) ih

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_app`. -/
theorem reds_app {t t' u u' : Term} (h1 : Reds t t') (h2 : Reds u u') : Reds (app t u) (app t' u') :=
  reds_trans (reds_app1 u h1) (reds_app2 t' h2)

/-! ### Embedding normal forms -/

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.emb`. -/
def emb : Nf → Term
  | nlam A t => abs A (emb t)
  | ntlam k t => tabs k (emb t)
  | nne y sp => embSp (var y) sp
/-- Rocq: `Analysis.HereditarySubstFNorm.emb_sp`. -/
def embSp (h : Term) : Spine → Term
  | snil => h
  | sapp t sp => embSp (app h (emb t)) sp
  | stapp C sp => embSp (tapp h C) sp
end

/-- Rocq: `Analysis.HereditarySubstFNorm.emb_sp_app`. -/
theorem embSp_app : ∀ (sp1 sp2 : Spine) (h : Term), embSp h (spApp sp1 sp2) = embSp (embSp h sp1) sp2
  | snil, _, _ => rfl
  | sapp _ sp, sp2, _ => embSp_app sp sp2 _
  | stapp _ sp, sp2, _ => embSp_app sp sp2 _

/-- Rocq: `Analysis.HereditarySubstFNorm.reds_emb_sp`. -/
theorem reds_embSp : ∀ (sp : Spine) {h h' : Term}, Reds h h' → Reds (embSp h sp) (embSp h' sp)
  | snil, _, _, H => H
  | sapp _ sp, _, _, H => reds_embSp sp (reds_app1 _ H)
  | stapp C sp, _, _, H => reds_embSp sp (reds_tapp C H)

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.shift_emb`. -/
theorem shift_emb : ∀ (t : Nf) (c : Nat), shiftTerm c (emb t) = emb (shiftTm c t)
  | nlam A t, c => congrArg (abs A) (shift_emb t (c + 1))
  | ntlam k t, c => congrArg (tabs k) (shift_emb t c)
  | nne y sp, c => shift_embSp sp c (var y)
/-- The spine part of `shift_emb`. -/
theorem shift_embSp : ∀ (sp : Spine) (c : Nat) (h : Term),
    shiftTerm c (embSp h sp) = embSp (shiftTerm c h) (shiftSp c sp)
  | snil, _, _ => rfl
  | sapp t sp, c, h => by
    show shiftTerm c (embSp (app h (emb t)) sp) = embSp (app (shiftTerm c h) (emb (shiftTm c t))) _
    rw [shift_embSp sp c, ← shift_emb t c]; rfl
  | stapp C sp, c, h => shift_embSp sp c (tapp h C)
end

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.tshift_emb`. -/
theorem tshift_emb : ∀ (t : Nf) (X : Nat), tshiftTerm X (emb t) = emb (tshiftTm X t)
  | nlam _ t, X => congrArg (abs _) (tshift_emb t X)
  | ntlam k t, X => congrArg (tabs k) (tshift_emb t (X + 1))
  | nne y sp, X => tshift_embSp sp X (var y)
/-- The spine part of `tshift_emb`. -/
theorem tshift_embSp : ∀ (sp : Spine) (X : Nat) (h : Term),
    tshiftTerm X (embSp h sp) = embSp (tshiftTerm X h) (tshiftSp X sp)
  | snil, _, _ => rfl
  | sapp t sp, X, h => by
    show tshiftTerm X (embSp (app h (emb t)) sp) = embSp (app (tshiftTerm X h) (emb (tshiftTm X t))) _
    rw [tshift_embSp sp X, ← tshift_emb t X]; rfl
  | stapp C sp, X, h => tshift_embSp sp X (tapp h C)
end

mutual
/-- Rocq: `Analysis.HereditarySubstFNorm.tsubst_emb`. -/
theorem tsubst_emb : ∀ (t : Nf) (X : Nat) (C : Typ), tsubstTerm (emb t) X C = emb (tsubstTm t X C)
  | nlam _ t, X, C => congrArg (abs _) (tsubst_emb t X C)
  | ntlam k t, X, _ => congrArg (tabs k) (tsubst_emb t (X + 1) _)
  | nne y sp, X, C => tsubst_embSp sp X C (var y)
/-- The spine part of `tsubst_emb`. -/
theorem tsubst_embSp : ∀ (sp : Spine) (X : Nat) (C : Typ) (h : Term),
    tsubstTerm (embSp h sp) X C = embSp (tsubstTerm h X C) (tsubstSp sp X C)
  | snil, _, _, _ => rfl
  | sapp t sp, X, C, h => by
    show tsubstTerm (embSp (app h (emb t)) sp) X C = embSp (app (tsubstTerm h X C) (emb (tsubstTm t X C))) _
    rw [tsubst_embSp sp X C, ← tsubst_emb t X C]; rfl
  | stapp D sp, X, C, h => tsubst_embSp sp X C (tapp h D)
end

/-- Substitution into an embedded spine, with the arguments substituted.
Rocq: `Analysis.HereditarySubstFNorm.emb_sps`. -/
def embSps (h : Term) : Spine → Nat → Term → Term
  | snil, _, _ => h
  | sapp t sp, x, u => embSps (app h (subst (emb t) x u)) sp x u
  | stapp C sp, x, u => embSps (tapp h C) sp x u

/-- Rocq: `Analysis.HereditarySubstFNorm.subst_emb_sp`. -/
theorem subst_embSp : ∀ (sp : Spine) (h : Term) (x : Nat) (u : Term),
    subst (embSp h sp) x u = embSps (subst h x u) sp x u
  | snil, _, _, _ => rfl
  | sapp _ sp, _, x, u => subst_embSp sp _ x u
  | stapp _ sp, _, x, u => subst_embSp sp _ x u

/-! ### Correctness -/

/-- Rocq: `Analysis.HereditarySubstFNorm.rpost`. -/
def RPost : Call → Res → Prop
  | CH Δ U u x t, rn r =>
    ∀ e1 e2 U0 T, Δ = kctx (e1 ++ ET U0 :: e2) → cntT e1 = x →
      getVar (e1 ++ ET U0 :: e2) x = some U → Check (e1 ++ e2) u U →
      Check (e1 ++ ET U0 :: e2) t T → Reds (subst (emb t) x (emb u)) (emb r)
  | CS Δ U u x sp, rs sp' =>
    ∀ e1 e2 U0 A T, Δ = kctx (e1 ++ ET U0 :: e2) → cntT e1 = x →
      getVar (e1 ++ ET U0 :: e2) x = some U → Check (e1 ++ e2) u U →
      SpineTy (e1 ++ ET U0 :: e2) A sp T →
      ∀ h h', Reds h h' → Reds (embSps h sp x (emb u)) (embSp h' sp')
  | CA Δ U u sp, rn r => ∀ e T, Δ = kctx e → Check e u U → SpineTy e U sp T → Reds (embSp (emb u) sp) (emb r)
  | CH _ _ _ _ _, rs _ => True
  | CS _ _ _ _ _, rn _ => True
  | CA _ _ _ _, rs _ => True

/-- Rocq: `Analysis.HereditarySubstFNorm.HS_red`. -/
theorem HS_red {c : Call} {r : Res} (h : HS c r) : RPost c r := by
  induction h with
  | hs_lam Δ U u x A t r _ ih =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | lam _ _ _ B hb =>
      refine reds_abs A ?_
      show Reds (subst (emb t) (x + 1) (shiftTerm 0 (emb u))) (emb r)
      rw [shift_emb]
      exact ih (ET A :: e1) e2 U0 B HΔ (congrArg (· + 1) Hx) Hg (weaken_tm Hu [] (e1 ++ e2) A rfl) hb
  | hs_tlam Δ U u x k t r _ ih =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | tlam _ _ _ B hb =>
      refine reds_tabs k ?_
      show Reds (subst (emb t) x (tshiftTerm 0 (emb u))) (emb r)
      rw [tshift_emb]
      refine ih (EK k :: e1) e2 U0 B (congrArg (k :: ·) HΔ) Hx ?_ (weaken_ty Hu [] (e1 ++ e2) k rfl) hb
      show (getVar (e1 ++ ET U0 :: e2) x).map (tshift 0) = _
      rw [Hg]; rfl
  | hs_var Δ U u x y sp sp' hxy _ ih =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | ne _ _ _ A _ hy hsp =>
      show Reds (subst (embSp (var y) sp) x (emb u)) (embSp (var (unshift x y)) sp')
      rw [subst_embSp]
      have e : subst (var y) x (emb u) = var (unshift x y) := ite_eq_right (fun h => hxy h.symm)
      rw [e]
      exact ih e1 e2 U0 A T HΔ Hx Hg Hu hsp _ _ (.refl _)
  | hs_head Δ U u x sp sp' r h1 _ ih1 ih2 =>
    intro e1 e2 U0 T HΔ Hx Hg Hu Ht
    cases Ht with
    | ne _ _ _ A _ hy hsp =>
      rw [Hg] at hy; cases hy
      show Reds (subst (embSp (var x) sp) x (emb u)) (emb r)
      rw [subst_embSp]
      have e : subst (var x) x (emb u) = emb u := ite_eq_left rfl
      rw [e]
      refine reds_trans (ih1 e1 e2 U0 U T HΔ Hx Hg Hu hsp _ _ (.refl _)) ?_
      exact ih2 (e1 ++ e2) T (HΔ.trans (kctx_remove e1 e2 U0)) Hu (HS_typed h1 e1 e2 U0 U T HΔ Hx Hg Hu hsp)
  | hs_snil => intro _ _ _ _ _ _ _ _ _ _ _ _ Hh; exact Hh
  | hs_sapp Δ U u x t sp t' sp' _ _ ih1 ih2 =>
    intro e1 e2 U0 A T HΔ Hx Hg Hu Hs h h' Hh
    cases Hs with
    | app _ A' B _ _ _ ht hsp =>
      exact ih2 e1 e2 U0 B T HΔ Hx Hg Hu hsp _ _ (reds_app Hh (ih1 e1 e2 U0 A' HΔ Hx Hg Hu ht))
  | hs_stapp Δ U u x C sp sp' _ ih =>
    intro e1 e2 U0 A T HΔ Hx Hg Hu Hs h h' Hh
    cases Hs with
    | tapp _ _ _ _ _ _ _ hsp => exact ih e1 e2 U0 _ T HΔ Hx Hg Hu hsp _ _ (reds_tapp C Hh)
  | ha_nil => intro _ _ _ _ _; exact .refl _
  | ha_ne Δ U y sp0 sp _ =>
    intro _ _ _ _ _
    show Reds (embSp (embSp (var y) sp0) sp) (embSp (var y) (spApp sp0 sp))
    rw [embSp_app]; exact .refl _
  | ha_beta Δ A B A' b t sp r1 r h1 _ ih1 ih2 =>
    intro e T HΔ Hu Hs
    cases Hu with
    | lam _ _ _ _ hb =>
      cases Hs with
      | app _ _ _ _ _ _ ht hsp =>
        show Reds (embSp (app (abs A (emb b)) (emb t)) sp) (emb r)
        refine reds_trans (reds_embSp sp (reds_one (.beta _ _ _))) ?_
        refine reds_trans (reds_embSp sp (ih1 [] e A _ HΔ rfl rfl ht hb)) ?_
        exact ih2 e T HΔ (HS_typed h1 [] e A _ HΔ rfl rfl ht hb) hsp
  | ha_tbeta Δ k B k' b C sp k0 r _ _ _ ih =>
    intro e T HΔ Hu Hs
    cases Hu with
    | tlam _ _ _ _ hb =>
      cases Hs with
      | tapp _ _ _ _ _ _ hk hsp =>
        show Reds (embSp (tapp (tabs k (emb b)) C) sp) (emb r)
        refine reds_trans (reds_embSp sp (reds_one (.tbeta _ _ _))) ?_
        rw [tsubst_emb]
        exact ih e T HΔ (subst_ty hb 0 C e (.here e k C hk)) hsp
  | ha_stuck Δ U u sp hs =>
    intro e T HΔ Hu Hs
    subst HΔ
    exact (not_stuck Hu Hs hs).elim

/-- Rocq: `Analysis.HereditarySubstFNorm.happ_red`. -/
theorem happ_red {e : Env} {U : Typ} {u : Nf} {sp : Spine} {T : Typ} (Hu : Check e u U)
    (Hs : SpineTy e U sp T) : Reds (embSp (emb u) sp) (emb (happ (kctx e) U u sp)) :=
  HS_red (happ_HS _ _ _ _) e T rfl Hu Hs

/-- Every well-typed term reduces to a normal form of the same type.
Rocq: `Analysis.HereditarySubstFNorm.normalization_red`. -/
theorem normalization_red {e : Env} {t : Term} {T : Typ} (h : Typing e t T) :
    ∃ n, Check e n T ∧ Reds t (emb n) := by
  induction h with
  | Var e x T hx => exact ⟨nne x snil, .ne _ _ _ _ _ hx (.nil _ _), .refl _⟩
  | Abs e A t B _ ih =>
    obtain ⟨n, hn, hr⟩ := ih
    exact ⟨nlam A n, .lam _ _ _ _ hn, reds_abs A hr⟩
  | App e t1 t2 A B _ _ ih1 ih2 =>
    obtain ⟨n1, h1, r1⟩ := ih1
    obtain ⟨n2, h2, r2⟩ := ih2
    have hs : SpineTy e (arrow A B) (sapp n2 snil) B := .app _ _ _ _ _ _ h2 (.nil _ _)
    exact ⟨_, happ_typed h1 hs, reds_trans (reds_app r1 r2) (happ_red h1 hs)⟩
  | Tabs e k t B _ ih =>
    obtain ⟨n, hn, hr⟩ := ih
    exact ⟨ntlam k n, .tlam _ _ _ _ hn, reds_tabs k hr⟩
  | Tapp e t k B C _ hk ih =>
    obtain ⟨n, hn, hr⟩ := ih
    have hs : SpineTy e (all k B) (stapp C snil) (tsubst B 0 C) := .tapp _ _ _ _ _ _ hk (.nil _ _)
    exact ⟨_, happ_typed hn hs, reds_trans (reds_tapp C hr) (happ_red hn hs)⟩

end ConstructiveOrdinals.HereditarySubstFNorm
