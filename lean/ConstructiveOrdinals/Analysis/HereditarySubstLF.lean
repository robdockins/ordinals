import ConstructiveOrdinals.Analysis.HereditarySubst

/-!
# Termination of hereditary substitution for LF

Port of `Ordinal/Analysis/HereditarySubstLF.v`.

In LF, types contain terms, so hereditary substitution goes into canonical
types and kinds as well as objects. It is indexed by the simple type `τ`
obtained by erasing the dependent type of the substituted object:
substitution does not change erasures (`erase_hsub_tp`), so the index stays
meaningful. The ordinal measure of `HereditarySubst` carries over unchanged,
and every call at index `τ` is again below `ω · (height τ + 1)`
(`lmeasure_bound`).

Lean notes:

- `lres_ok` compares the kind of result a call expects with the kind it got,
  through `lcallKind` and `lresKind` (values in the enumeration `LKind`); a
  match with a wildcard would make it depend on `propext`.
- Rocq's helpers `getn`, `gets`, `gett` and `getk` inside `lhsub_total` become
  direct matches on the recursive results.
-/

namespace ConstructiveOrdinals.HereditarySubstLF

open Ordinal HereditarySubst Ty

/-! ## Canonical LF syntax, with de Bruijn indices -/

/-- Rocq: `Analysis.HereditarySubstLF.head`. -/
inductive Head : Type where
  | hvar : Nat → Head
  | hcst : Nat → Head

open Head

mutual
/-- Objects: `lam M`, or a head applied to a spine. Rocq: `Analysis.HereditarySubstLF.tm`. -/
inductive Tm : Type where
  | tlam : Tm → Tm
  | tapp : Head → TSpine → Tm
/-- Rocq: `Analysis.HereditarySubstLF.tspine`. -/
inductive TSpine : Type where
  | tnil : TSpine
  | tcons : Tm → TSpine → TSpine
end

open Tm TSpine

/-- Types: a family constant applied to a spine, or `Πx:A.B`.
Rocq: `Analysis.HereditarySubstLF.tp`. -/
inductive Tp : Type where
  | atom : Nat → TSpine → Tp
  | pi : Tp → Tp → Tp

/-- Kinds: `type`, or `Πx:A.K`. Rocq: `Analysis.HereditarySubstLF.kd`. -/
inductive Kd : Type where
  | ktype : Kd
  | kpi : Tp → Kd → Kd

open Tp Kd

mutual
/-- Rocq: `Analysis.HereditarySubstLF.tsize`. -/
def tsize : Tm → Nat
  | tlam t => tsize t + 1
  | tapp _ sp => tsizeSp sp + 1
/-- Rocq: `Analysis.HereditarySubstLF.tsize_sp`. -/
def tsizeSp : TSpine → Nat
  | tnil => 0
  | tcons t sp => tsize t + tsizeSp sp + 1
end

/-- Rocq: `Analysis.HereditarySubstLF.psize`. -/
def psize : Tp → Nat
  | atom _ sp => tsizeSp sp + 1
  | pi A B => psize A + psize B + 1

/-- Rocq: `Analysis.HereditarySubstLF.ksize`. -/
def ksize : Kd → Nat
  | ktype => 0
  | kpi A K => psize A + ksize K + 1

/-- The simple-type erasure of a type. Rocq: `Analysis.HereditarySubstLF.erase`. -/
def erase : Tp → Ty
  | atom _ _ => base
  | pi A B => arr (erase A) (erase B)

mutual
/-- Rocq: `Analysis.HereditarySubstLF.tlift`. -/
def tlift (k : Nat) : Tm → Tm
  | tlam t => tlam (tlift (k + 1) t)
  | tapp (hvar y) sp => tapp (hvar (if y < k then y else y + 1)) (tliftSp k sp)
  | tapp (hcst c) sp => tapp (hcst c) (tliftSp k sp)
/-- Rocq: `Analysis.HereditarySubstLF.tlift_sp`. -/
def tliftSp (k : Nat) : TSpine → TSpine
  | tnil => tnil
  | tcons t sp => tcons (tlift k t) (tliftSp k sp)
end

/-! ## The graph of hereditary substitution -/

/-- Rocq: `Analysis.HereditarySubstLF.lcall`. -/
inductive LCall : Type where
  /-- into an object -/
  | LH : Ty → Tm → Nat → Tm → LCall
  /-- into a spine -/
  | LS : Ty → Tm → Nat → TSpine → LCall
  /-- into a type -/
  | LT : Ty → Tm → Nat → Tp → LCall
  /-- into a kind -/
  | LK : Ty → Tm → Nat → Kd → LCall
  /-- application -/
  | LA : Ty → Tm → TSpine → LCall

/-- Rocq: `Analysis.HereditarySubstLF.lres`. -/
inductive LRes : Type where
  | ln : Tm → LRes
  | ls : TSpine → LRes
  | lt : Tp → LRes
  | lk : Kd → LRes

open LCall

/-- Rocq: `Analysis.HereditarySubstLF.LHS`. -/
inductive LHS : LCall → LRes → Prop where
  | lh_lam (τ : Ty) (M : Tm) (x : Nat) (t r : Tm) :
      LHS (LH τ (tlift 0 M) (x + 1) t) (.ln r) → LHS (LH τ M x (tlam t)) (.ln (tlam r))
  | lh_cst (τ : Ty) (M : Tm) (x c : Nat) (sp sp' : TSpine) :
      LHS (LS τ M x sp) (.ls sp') → LHS (LH τ M x (tapp (hcst c) sp)) (.ln (tapp (hcst c) sp'))
  | lh_var (τ : Ty) (M : Tm) (x y : Nat) (sp sp' : TSpine) :
      x ≠ y → LHS (LS τ M x sp) (.ls sp') →
      LHS (LH τ M x (tapp (hvar y) sp)) (.ln (tapp (hvar (unshift x y)) sp'))
  | lh_head (τ : Ty) (M : Tm) (x : Nat) (sp sp' : TSpine) (r : Tm) :
      LHS (LS τ M x sp) (.ls sp') → LHS (LA τ M sp') (.ln r) → LHS (LH τ M x (tapp (hvar x) sp)) (.ln r)
  | ls_nil (τ : Ty) (M : Tm) (x : Nat) : LHS (LS τ M x tnil) (.ls tnil)
  | ls_cons (τ : Ty) (M : Tm) (x : Nat) (t : Tm) (sp : TSpine) (t' : Tm) (sp' : TSpine) :
      LHS (LH τ M x t) (.ln t') → LHS (LS τ M x sp) (.ls sp') →
      LHS (LS τ M x (tcons t sp)) (.ls (tcons t' sp'))
  | lt_atom (τ : Ty) (M : Tm) (x a : Nat) (sp sp' : TSpine) :
      LHS (LS τ M x sp) (.ls sp') → LHS (LCall.LT τ M x (atom a sp)) (.lt (atom a sp'))
  | lt_pi (τ : Ty) (M : Tm) (x : Nat) (A B A' B' : Tp) :
      LHS (LCall.LT τ M x A) (.lt A') → LHS (LCall.LT τ (tlift 0 M) (x + 1) B) (.lt B') →
      LHS (LCall.LT τ M x (pi A B)) (.lt (pi A' B'))
  | lk_type (τ : Ty) (M : Tm) (x : Nat) : LHS (LK τ M x ktype) (.lk ktype)
  | lk_pi (τ : Ty) (M : Tm) (x : Nat) (A : Tp) (K : Kd) (A' : Tp) (K' : Kd) :
      LHS (LCall.LT τ M x A) (.lt A') → LHS (LK τ (tlift 0 M) (x + 1) K) (.lk K') →
      LHS (LK τ M x (kpi A K)) (.lk (kpi A' K'))
  | la_nil (τ : Ty) (M : Tm) : LHS (LA τ M tnil) (.ln M)
  | la_beta (a b : Ty) (t N : Tm) (sp : TSpine) (r1 r : Tm) :
      LHS (LH a N 0 t) (.ln r1) → LHS (LA b r1 sp) (.ln r) → LHS (LA (arr a b) (tlam t) (tcons N sp)) (.ln r)
  | la_base (M N : Tm) (sp : TSpine) : LHS (LA base M (tcons N sp)) (.ln M)
  | la_app (a b : Ty) (h : Head) (sp0 : TSpine) (N : Tm) (sp : TSpine) :
      LHS (LA (arr a b) (tapp h sp0) (tcons N sp)) (.ln (tapp h sp0))

/-- Rocq: `Analysis.HereditarySubstLF.LHS_det`. -/
theorem LHS_det {c : LCall} {r1 : LRes} (h : LHS c r1) : ∀ {r2 : LRes}, LHS c r2 → r1 = r2 := by
  induction h with
  | lh_lam _ _ _ _ _ _ ih => intro r2 h2; cases h2 with | lh_lam _ _ _ _ _ h' => cases ih h'; rfl
  | lh_cst _ _ _ _ _ _ _ ih => intro r2 h2; cases h2 with | lh_cst _ _ _ _ _ _ h' => cases ih h'; rfl
  | lh_var _ _ _ _ _ _ hxy _ ih =>
    intro r2 h2; cases h2 with
    | lh_var _ _ _ _ _ _ _ h' => cases ih h'; rfl
    | lh_head => exact absurd rfl hxy
  | lh_head _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with
    | lh_var _ _ _ _ _ _ hxy => exact absurd rfl hxy
    | lh_head _ _ _ _ _ _ h1 h2' => cases ih1 h1; exact ih2 h2'
  | ls_nil => intro r2 h2; cases h2; rfl
  | ls_cons _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with | ls_cons _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; cases ih2 h2'; rfl
  | lt_atom _ _ _ _ _ _ _ ih => intro r2 h2; cases h2 with | lt_atom _ _ _ _ _ _ h' => cases ih h'; rfl
  | lt_pi _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with | lt_pi _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; cases ih2 h2'; rfl
  | lk_type => intro r2 h2; cases h2; rfl
  | lk_pi _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with | lk_pi _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; cases ih2 h2'; rfl
  | la_nil => intro r2 h2; cases h2; rfl
  | la_beta _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with | la_beta _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; exact ih2 h2'
  | la_base => intro r2 h2; cases h2; rfl
  | la_app => intro r2 h2; cases h2; rfl

/-- The four kinds of result. -/
inductive LKind : Type where
  | kn | ks | kt | kk

/-- The kind of result a call returns. -/
def lcallKind : LCall → LKind
  | LH _ _ _ _ => .kn
  | LA _ _ _ => .kn
  | LS _ _ _ _ => .ks
  | LCall.LT _ _ _ _ => .kt
  | LK _ _ _ _ => .kk

/-- The kind of a result. -/
def lresKind : LRes → LKind
  | .ln _ => .kn
  | .ls _ => .ks
  | .lt _ => .kt
  | .lk _ => .kk

/-- Rocq: `Analysis.HereditarySubstLF.lres_ok`. -/
def LResOk (c : LCall) (r : LRes) : Prop := lcallKind c = lresKind r

/-- Rocq: `Analysis.HereditarySubstLF.LHS_res_ok`. -/
theorem LHS_res_ok {c : LCall} {r : LRes} (h : LHS c r) : LResOk c r := by
  cases h <;> rfl

/-! ## The ordinal measure, as for simple types -/

/-- Rocq: `Analysis.HereditarySubstLF.lmeasure`. -/
def lmeasure : LCall → Ordinal.{0}
  | LH τ _ _ t => tyOrd τ + ofNat (tsize t)
  | LS τ _ _ sp => tyOrd τ + ofNat (tsizeSp sp)
  | LCall.LT τ _ _ A => tyOrd τ + ofNat (psize A)
  | LK τ _ _ K => tyOrd τ + ofNat (ksize K)
  | LA τ _ _ => tyOrd τ

/-- Rocq: `Analysis.HereditarySubstLF.lt_head_measure`. -/
theorem lt_head_measure (τ : Ty) {k : Nat} (hk : 0 < k) : tyOrd τ < tyOrd τ + ofNat k :=
  lt_of_le_of_lt (le_add_right (tyOrd τ) (ofNat 0)) (add_nat_lt _ hk)

theorem lt_succ_add_l (a b : Nat) : a < a + b + 1 := Nat.lt_succ_of_le (Nat.le_add_right _ _)
theorem lt_succ_add_r (a b : Nat) : b < a + b + 1 := Nat.lt_succ_of_le (Nat.le_add_left _ _)

/-! ## Termination: the graph is total -/

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_total`. -/
def lhsub_total : (c : LCall) → { r // LHS c r } :=
  (InvImage.wf lmeasure lt_wf).fix fun c IH =>
    match c with
    | LH τ M x (tlam t) =>
      match IH (LH τ (tlift 0 M) (x + 1) t) (add_nat_lt _ (Nat.lt_succ_self _)) with
      | ⟨.ln r, h⟩ => ⟨.ln (tlam r), .lh_lam _ _ _ _ _ h⟩
      | ⟨.ls _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LH τ M x (tapp (hvar y) sp) =>
      match IH (LS τ M x sp) (add_nat_lt _ (Nat.lt_succ_self _)) with
      | ⟨.ls sp', hsp⟩ =>
        if hxy : x = y then by
          subst hxy
          exact match IH (LA τ M sp') (lt_head_measure τ (Nat.zero_lt_succ _)) with
            | ⟨.ln r, h⟩ => ⟨.ln r, .lh_head _ _ _ _ _ _ hsp h⟩
            | ⟨.ls _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
            | ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
            | ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
        else ⟨.ln (tapp (hvar (unshift x y)) sp'), .lh_var _ _ _ _ _ _ hxy hsp⟩
      | ⟨.ln _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LH τ M x (tapp (hcst c) sp) =>
      match IH (LS τ M x sp) (add_nat_lt _ (Nat.lt_succ_self _)) with
      | ⟨.ls sp', hsp⟩ => ⟨.ln (tapp (hcst c) sp'), .lh_cst _ _ _ _ _ _ hsp⟩
      | ⟨.ln _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LS _ _ _ tnil => ⟨.ls tnil, .ls_nil _ _ _⟩
    | LS τ M x (tcons t sp) =>
      match IH (LH τ M x t) (add_nat_lt _ (lt_succ_add_l _ _)),
          IH (LS τ M x sp) (add_nat_lt _ (lt_succ_add_r _ _)) with
      | ⟨.ln t', ht⟩, ⟨.ls sp', hsp⟩ => ⟨.ls (tcons t' sp'), .ls_cons _ _ _ _ _ _ _ ht hsp⟩
      | ⟨.ln _, _⟩, ⟨.ln _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ln _, _⟩, ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ln _, _⟩, ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ls _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LCall.LT τ M x (atom a sp) =>
      match IH (LS τ M x sp) (add_nat_lt _ (Nat.lt_succ_self _)) with
      | ⟨.ls sp', hsp⟩ => ⟨.lt (atom a sp'), .lt_atom _ _ _ _ _ _ hsp⟩
      | ⟨.ln _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LCall.LT τ M x (pi A B) =>
      match IH (LCall.LT τ M x A) (add_nat_lt _ (lt_succ_add_l _ _)),
          IH (LCall.LT τ (tlift 0 M) (x + 1) B) (add_nat_lt _ (lt_succ_add_r _ _)) with
      | ⟨.lt A', hA⟩, ⟨.lt B', hB⟩ => ⟨.lt (pi A' B'), .lt_pi _ _ _ _ _ _ _ hA hB⟩
      | ⟨.lt _, _⟩, ⟨.ln _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, _⟩, ⟨.ls _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, _⟩, ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ln _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ls _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LK _ _ _ ktype => ⟨.lk ktype, .lk_type _ _ _⟩
    | LK τ M x (kpi A K) =>
      match IH (LCall.LT τ M x A) (add_nat_lt _ (lt_succ_add_l _ _)),
          IH (LK τ (tlift 0 M) (x + 1) K) (add_nat_lt _ (lt_succ_add_r _ _)) with
      | ⟨.lt A', hA⟩, ⟨.lk K', hK⟩ => ⟨.lk (kpi A' K'), .lk_pi _ _ _ _ _ _ _ hA hK⟩
      | ⟨.lt _, _⟩, ⟨.ln _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, _⟩, ⟨.ls _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, _⟩, ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ln _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ls _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩, _ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LA _ M tnil => ⟨.ln M, .la_nil _ _⟩
    | LA base M (tcons _ _) => ⟨.ln M, .la_base _ _ _⟩
    | LA (arr a b) (tlam t) (tcons N sp) =>
      match IH (LH a N 0 t) (tyOrd_dom a b _) with
      | ⟨.ln r1, h1⟩ =>
        match IH (LA b r1 sp) (tyOrd_cod a b) with
        | ⟨.ln r, h2⟩ => ⟨.ln r, .la_beta _ _ _ _ _ _ _ h1 h2⟩
        | ⟨.ls _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
        | ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
        | ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.ls _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lt _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
      | ⟨.lk _, h⟩ => absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)
    | LA (arr _ _) (tapp h sp0) (tcons _ _) => ⟨.ln (tapp h sp0), .la_app _ _ _ _ _ _⟩

/-! ## The functions and their equations -/

/-- Rocq: `Analysis.HereditarySubstLF.lhsub`. -/
def lhsub (τ : Ty) (M : Tm) (x : Nat) (t : Tm) : Tm :=
  match (lhsub_total (LH τ M x t)).1 with
  | .ln r => r
  | .ls _ => t
  | .lt _ => t
  | .lk _ => t

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_sp`. -/
def lhsubSp (τ : Ty) (M : Tm) (x : Nat) (sp : TSpine) : TSpine :=
  match (lhsub_total (LS τ M x sp)).1 with
  | .ls r => r
  | .ln _ => sp
  | .lt _ => sp
  | .lk _ => sp

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_tp`. -/
def lhsubTp (τ : Ty) (M : Tm) (x : Nat) (A : Tp) : Tp :=
  match (lhsub_total (LCall.LT τ M x A)).1 with
  | .lt r => r
  | .ln _ => A
  | .ls _ => A
  | .lk _ => A

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_kd`. -/
def lhsubKd (τ : Ty) (M : Tm) (x : Nat) (K : Kd) : Kd :=
  match (lhsub_total (LK τ M x K)).1 with
  | .lk r => r
  | .ln _ => K
  | .ls _ => K
  | .lt _ => K

/-- Rocq: `Analysis.HereditarySubstLF.lhapp`. -/
def lhapp (τ : Ty) (M : Tm) (sp : TSpine) : Tm :=
  match (lhsub_total (LA τ M sp)).1 with
  | .ln r => r
  | .ls _ => M
  | .lt _ => M
  | .lk _ => M

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_spec`. -/
theorem lhsub_spec {τ : Ty} {M : Tm} {x : Nat} {t r : Tm} (h : LHS (LH τ M x t) (.ln r)) :
    lhsub τ M x t = r := by
  unfold lhsub; rw [LHS_det (lhsub_total _).2 h]

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_sp_spec`. -/
theorem lhsubSp_spec {τ : Ty} {M : Tm} {x : Nat} {sp r : TSpine} (h : LHS (LS τ M x sp) (.ls r)) :
    lhsubSp τ M x sp = r := by
  unfold lhsubSp; rw [LHS_det (lhsub_total _).2 h]

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_tp_spec`. -/
theorem lhsubTp_spec {τ : Ty} {M : Tm} {x : Nat} {A r : Tp} (h : LHS (LCall.LT τ M x A) (.lt r)) :
    lhsubTp τ M x A = r := by
  unfold lhsubTp; rw [LHS_det (lhsub_total _).2 h]

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_kd_spec`. -/
theorem lhsubKd_spec {τ : Ty} {M : Tm} {x : Nat} {K r : Kd} (h : LHS (LK τ M x K) (.lk r)) :
    lhsubKd τ M x K = r := by
  unfold lhsubKd; rw [LHS_det (lhsub_total _).2 h]

/-- Rocq: `Analysis.HereditarySubstLF.lhapp_spec`. -/
theorem lhapp_spec {τ : Ty} {M : Tm} {sp : TSpine} {r : Tm} (h : LHS (LA τ M sp) (.ln r)) :
    lhapp τ M sp = r := by
  unfold lhapp; rw [LHS_det (lhsub_total _).2 h]

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_LHS`. -/
theorem lhsub_LHS (τ : Ty) (M : Tm) (x : Nat) (t : Tm) : LHS (LH τ M x t) (.ln (lhsub τ M x t)) := by
  have h := (lhsub_total (LH τ M x t)).2
  unfold lhsub
  generalize (lhsub_total (LH τ M x t)).1 = q at h ⊢
  cases q with
  | ln _ => exact h
  | _ => exact absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_sp_LHS`. -/
theorem lhsubSp_LHS (τ : Ty) (M : Tm) (x : Nat) (sp : TSpine) :
    LHS (LS τ M x sp) (.ls (lhsubSp τ M x sp)) := by
  have h := (lhsub_total (LS τ M x sp)).2
  unfold lhsubSp
  generalize (lhsub_total (LS τ M x sp)).1 = q at h ⊢
  cases q with
  | ls _ => exact h
  | _ => exact absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_tp_LHS`. -/
theorem lhsubTp_LHS (τ : Ty) (M : Tm) (x : Nat) (A : Tp) : LHS (LCall.LT τ M x A) (.lt (lhsubTp τ M x A)) := by
  have h := (lhsub_total (LCall.LT τ M x A)).2
  unfold lhsubTp
  generalize (lhsub_total (LCall.LT τ M x A)).1 = q at h ⊢
  cases q with
  | lt _ => exact h
  | _ => exact absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_kd_LHS`. -/
theorem lhsubKd_LHS (τ : Ty) (M : Tm) (x : Nat) (K : Kd) : LHS (LK τ M x K) (.lk (lhsubKd τ M x K)) := by
  have h := (lhsub_total (LK τ M x K)).2
  unfold lhsubKd
  generalize (lhsub_total (LK τ M x K)).1 = q at h ⊢
  cases q with
  | lk _ => exact h
  | _ => exact absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)

/-- Rocq: `Analysis.HereditarySubstLF.lhapp_LHS`. -/
theorem lhapp_LHS (τ : Ty) (M : Tm) (sp : TSpine) : LHS (LA τ M sp) (.ln (lhapp τ M sp)) := by
  have h := (lhsub_total (LA τ M sp)).2
  unfold lhapp
  generalize (lhsub_total (LA τ M sp)).1 = q at h ⊢
  cases q with
  | ln _ => exact h
  | _ => exact absurd (LHS_res_ok h) (fun e => LKind.noConfusion e)

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_lam`. -/
theorem lhsub_lam (τ : Ty) (M : Tm) (x : Nat) (t : Tm) :
    lhsub τ M x (tlam t) = tlam (lhsub τ (tlift 0 M) (x + 1) t) :=
  lhsub_spec (.lh_lam _ _ _ _ _ (lhsub_LHS _ _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_cst`. -/
theorem lhsub_cst (τ : Ty) (M : Tm) (x c : Nat) (sp : TSpine) :
    lhsub τ M x (tapp (hcst c) sp) = tapp (hcst c) (lhsubSp τ M x sp) :=
  lhsub_spec (.lh_cst _ _ _ _ _ _ (lhsubSp_LHS _ _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_var`. -/
theorem lhsub_var (τ : Ty) (M : Tm) {x y : Nat} (sp : TSpine) (h : x ≠ y) :
    lhsub τ M x (tapp (hvar y) sp) = tapp (hvar (unshift x y)) (lhsubSp τ M x sp) :=
  lhsub_spec (.lh_var _ _ _ _ _ _ h (lhsubSp_LHS _ _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_head`. -/
theorem lhsub_head (τ : Ty) (M : Tm) (x : Nat) (sp : TSpine) :
    lhsub τ M x (tapp (hvar x) sp) = lhapp τ M (lhsubSp τ M x sp) :=
  lhsub_spec (.lh_head _ _ _ _ _ _ (lhsubSp_LHS _ _ _ _) (lhapp_LHS _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_sp_nil`. -/
theorem lhsubSp_nil (τ : Ty) (M : Tm) (x : Nat) : lhsubSp τ M x tnil = tnil :=
  lhsubSp_spec (.ls_nil _ _ _)

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_sp_cons`. -/
theorem lhsubSp_cons (τ : Ty) (M : Tm) (x : Nat) (t : Tm) (sp : TSpine) :
    lhsubSp τ M x (tcons t sp) = tcons (lhsub τ M x t) (lhsubSp τ M x sp) :=
  lhsubSp_spec (.ls_cons _ _ _ _ _ _ _ (lhsub_LHS _ _ _ _) (lhsubSp_LHS _ _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_tp_atom`. -/
theorem lhsubTp_atom (τ : Ty) (M : Tm) (x a : Nat) (sp : TSpine) :
    lhsubTp τ M x (atom a sp) = atom a (lhsubSp τ M x sp) :=
  lhsubTp_spec (.lt_atom _ _ _ _ _ _ (lhsubSp_LHS _ _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_tp_pi`. -/
theorem lhsubTp_pi (τ : Ty) (M : Tm) (x : Nat) (A B : Tp) :
    lhsubTp τ M x (pi A B) = pi (lhsubTp τ M x A) (lhsubTp τ (tlift 0 M) (x + 1) B) :=
  lhsubTp_spec (.lt_pi _ _ _ _ _ _ _ (lhsubTp_LHS _ _ _ _) (lhsubTp_LHS _ _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_kd_type`. -/
theorem lhsubKd_type (τ : Ty) (M : Tm) (x : Nat) : lhsubKd τ M x ktype = ktype :=
  lhsubKd_spec (.lk_type _ _ _)

/-- Rocq: `Analysis.HereditarySubstLF.lhsub_kd_pi`. -/
theorem lhsubKd_pi (τ : Ty) (M : Tm) (x : Nat) (A : Tp) (K : Kd) :
    lhsubKd τ M x (kpi A K) = kpi (lhsubTp τ M x A) (lhsubKd τ (tlift 0 M) (x + 1) K) :=
  lhsubKd_spec (.lk_pi _ _ _ _ _ _ _ (lhsubTp_LHS _ _ _ _) (lhsubKd_LHS _ _ _ _))

/-- Rocq: `Analysis.HereditarySubstLF.lhapp_nil`. -/
theorem lhapp_nil (τ : Ty) (M : Tm) : lhapp τ M tnil = M := lhapp_spec (.la_nil _ _)

/-- Rocq: `Analysis.HereditarySubstLF.lhapp_beta`. -/
theorem lhapp_beta (a b : Ty) (t N : Tm) (sp : TSpine) :
    lhapp (arr a b) (tlam t) (tcons N sp) = lhapp b (lhsub a N 0 t) sp :=
  lhapp_spec (.la_beta _ _ _ _ _ _ _ (lhsub_LHS _ _ _ _) (lhapp_LHS _ _ _))

/-! ## Erasure is invariant

Substitution into a type does not change its simple-type erasure, which is
why the erasure, and not the dependent type, indexes the substitution. -/

/-- Rocq: `Analysis.HereditarySubstLF.erase_hsub_tp`. -/
theorem erase_hsub_tp : ∀ (A : Tp) (τ : Ty) (M : Tm) (x : Nat), erase (lhsubTp τ M x A) = erase A
  | atom a sp, τ, M, x => by rw [lhsubTp_atom]; rfl
  | pi A B, τ, M, x => by
    rw [lhsubTp_pi]
    show arr (erase _) (erase _) = arr (erase A) (erase B)
    rw [erase_hsub_tp A, erase_hsub_tp B]

/-! ## The measure is below `ω · (height + 1)` -/

/-- Rocq: `Analysis.HereditarySubstLF.lcall_ty`. -/
def lcallTy : LCall → Ty
  | LH τ _ _ _ => τ
  | LS τ _ _ _ => τ
  | LCall.LT τ _ _ _ => τ
  | LK τ _ _ _ => τ
  | LA τ _ _ => τ

/-- Rocq: `Analysis.HereditarySubstLF.lmeasure_bound`. -/
theorem lmeasure_bound (c : LCall) : lmeasure c < ω * ofNat (height (lcallTy c) + 1) := by
  have H : ∀ τ k, tyOrd τ + ofNat k < ω * ofNat (height τ + 1) := fun τ k =>
    lt_of_lt_of_le (add_lt_add_left _ (index_lt ω ⟨k⟩))
      (le_trans (add_le_add (tyOrd_eq τ).le (le_refl ω)) (mul_succ ω _).ge)
  match c with
  | LH τ _ _ _ => exact H τ _
  | LS τ _ _ _ => exact H τ _
  | LCall.LT τ _ _ _ => exact H τ _
  | LK τ _ _ _ => exact H τ _
  | LA τ _ _ => exact lt_of_le_of_lt (add_zero (tyOrd τ)).ge (H τ 0)

/-- Substituting `λz.z` (of erased type `base → base`) for `0` in the type
`c (0 · (d))` reduces the redex in its index.
Rocq example `lhsub_tp_example`. -/
theorem lhsubTp_example :
    lhsubTp (arr base base) (tlam (tapp (hvar 0) tnil)) 0
      (atom 7 (tcons (tapp (hvar 0) (tcons (tapp (hcst 3) tnil) tnil)) tnil))
      = atom 7 (tcons (tapp (hcst 3) tnil) tnil) := by
  rw [lhsubTp_atom, lhsubSp_cons, lhsubSp_nil, lhsub_head, lhsubSp_cons, lhsubSp_nil, lhsub_cst,
    lhsubSp_nil, lhapp_beta, lhsub_head, lhsubSp_nil, lhapp_nil, lhapp_nil]

end ConstructiveOrdinals.HereditarySubstLF
