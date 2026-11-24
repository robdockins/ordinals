/-!
# Peano and Heyting arithmetic, and the negative translation

Port of `Ordinal/Analysis/PeanoArith.v`.

First-order arithmetic with `0`, `S`, `+` and `·`, formulas built from
equations and atoms `X t` with `⊥`, `∧`, `∨`, `→`, `∀` and `∃`, and variables
as de Bruijn indices. `X` is a unary predicate variable with no axioms: the
theory is `PA(X)`, which proves its instances of the induction schema for
formulas mentioning `X`, and so can state transfinite induction `TI(≺, X)` as
a single sentence. The proof system is natural deduction with hypotheses in a list;
Peano arithmetic adds double-negation elimination to Heyting arithmetic.
The Gödel–Gentzen negative translation embeds Peano arithmetic in Heyting
arithmetic (`negative_translation`), so a proof of `⊥` in PA gives one in
HA (`PA_HA_consistency`).

Lean notes:

- Rocq's `incl` is spelled out as `∀ B, B ∈ Γ → B ∈ Γ'`.
- The abbreviations `PA` and `HA` are `Prov true` and `Prov false`.
-/

namespace ConstructiveOrdinals.PeanoArith

theorem congrArg₂ {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') :
    f a b = f a' b' := ha ▸ hb ▸ rfl

/-! ## Syntax -/

/-- Arithmetic terms. Rocq: `Analysis.PeanoArith.aterm`. -/
inductive ATerm : Type where
  | tv : Nat → ATerm
  | tz : ATerm
  | ts : ATerm → ATerm
  | tplus : ATerm → ATerm → ATerm
  | tmult : ATerm → ATerm → ATerm

/-- Formulas. Rocq: `Analysis.PeanoArith.form`. -/
inductive Form : Type where
  | eq : ATerm → ATerm → Form
  | bot : Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | imp : Form → Form → Form
  | all : Form → Form
  | ex : Form → Form
  /-- Rocq: `PX`. -/
  | px : ATerm → Form

open ATerm Form

/-- Rocq: `Analysis.PeanoArith.Neg`. -/
def Form.neg (A : Form) : Form := imp A bot

/-! ## Substitution -/

/-- Rocq: `Analysis.PeanoArith.asubst`. -/
def asubst (σ : Nat → ATerm) : ATerm → ATerm
  | tv i => σ i
  | tz => tz
  | ts t => ts (asubst σ t)
  | tplus s t => tplus (asubst σ s) (asubst σ t)
  | tmult s t => tmult (asubst σ s) (asubst σ t)

/-- Rocq: `Analysis.PeanoArith.shift_sub`. -/
def shiftSub : Nat → ATerm := fun i => tv (i + 1)

/-- Rocq: `Analysis.PeanoArith.up`. -/
def up (σ : Nat → ATerm) : Nat → ATerm
  | 0 => tv 0
  | i + 1 => asubst shiftSub (σ i)

/-- Rocq: `Analysis.PeanoArith.fsubst`. -/
def fsubst : (Nat → ATerm) → Form → Form
  | σ, eq s t => eq (asubst σ s) (asubst σ t)
  | _, bot => bot
  | σ, conj A B => conj (fsubst σ A) (fsubst σ B)
  | σ, disj A B => disj (fsubst σ A) (fsubst σ B)
  | σ, imp A B => imp (fsubst σ A) (fsubst σ B)
  | σ, all A => all (fsubst (up σ) A)
  | σ, ex A => ex (fsubst (up σ) A)
  | σ, px t => px (asubst σ t)
termination_by structural _ A => A

/-- Shifting past a new variable. Rocq: `Analysis.PeanoArith.fshift`. -/
def fshift (A : Form) : Form := fsubst shiftSub A

/-- Rocq: `Analysis.PeanoArith.inst1`. -/
def inst1 (t : ATerm) : Nat → ATerm
  | 0 => t
  | i + 1 => tv i

/-- Substituting for variable `0`. Rocq: `Analysis.PeanoArith.sub1`. -/
def sub1 (A : Form) (t : ATerm) : Form := fsubst (inst1 t) A

/-- Replacing variable `0` by its successor. Rocq: `Analysis.PeanoArith.suc_sub`. -/
def sucSub : Nat → ATerm
  | 0 => ts (tv 0)
  | i + 1 => tv (i + 1)

/-- Rocq: `Analysis.PeanoArith.asubst_ext`. -/
theorem asubst_ext {σ τ : Nat → ATerm} (h : ∀ i, σ i = τ i) : ∀ t, asubst σ t = asubst τ t
  | tv i => h i
  | tz => rfl
  | ts t => congrArg ts (asubst_ext h t)
  | tplus s t => congrArg₂ tplus (asubst_ext h s) (asubst_ext h t)
  | tmult s t => congrArg₂ tmult (asubst_ext h s) (asubst_ext h t)

/-- Rocq: `Analysis.PeanoArith.up_ext`. -/
theorem up_ext {σ τ : Nat → ATerm} (h : ∀ i, σ i = τ i) : ∀ i, up σ i = up τ i
  | 0 => rfl
  | i + 1 => congrArg (asubst shiftSub) (h i)

/-- Rocq: `Analysis.PeanoArith.fsubst_ext`. -/
theorem fsubst_ext : ∀ (A : Form) {σ τ : Nat → ATerm}, (∀ i, σ i = τ i) → fsubst σ A = fsubst τ A
  | eq s t, _, _, h => congrArg₂ eq (asubst_ext h s) (asubst_ext h t)
  | bot, _, _, _ => rfl
  | conj A B, _, _, h => congrArg₂ conj (fsubst_ext A h) (fsubst_ext B h)
  | disj A B, _, _, h => congrArg₂ disj (fsubst_ext A h) (fsubst_ext B h)
  | imp A B, _, _, h => congrArg₂ imp (fsubst_ext A h) (fsubst_ext B h)
  | all A, _, _, h => congrArg all (fsubst_ext A (up_ext h))
  | ex A, _, _, h => congrArg ex (fsubst_ext A (up_ext h))
  | px t, _, _, h => congrArg px (asubst_ext h t)

/-- Rocq: `Analysis.PeanoArith.asubst_comp`. -/
theorem asubst_comp (σ τ : Nat → ATerm) :
    ∀ t, asubst σ (asubst τ t) = asubst (fun i => asubst σ (τ i)) t
  | tv _ => rfl
  | tz => rfl
  | ts t => congrArg ts (asubst_comp σ τ t)
  | tplus s t => congrArg₂ tplus (asubst_comp σ τ s) (asubst_comp σ τ t)
  | tmult s t => congrArg₂ tmult (asubst_comp σ τ s) (asubst_comp σ τ t)

/-- Rocq: `Analysis.PeanoArith.asubst_id`. -/
theorem asubst_id : ∀ t, asubst tv t = t
  | tv _ => rfl
  | tz => rfl
  | ts t => congrArg ts (asubst_id t)
  | tplus s t => congrArg₂ tplus (asubst_id s) (asubst_id t)
  | tmult s t => congrArg₂ tmult (asubst_id s) (asubst_id t)

/-- Rocq: `Analysis.PeanoArith.up_comp`. -/
theorem up_comp (σ τ : Nat → ATerm) :
    ∀ i, asubst (up σ) (up τ i) = up (fun j => asubst σ (τ j)) i
  | 0 => rfl
  | i + 1 => by
    show asubst (up σ) (asubst shiftSub (τ i)) = asubst shiftSub (asubst σ (τ i))
    rw [asubst_comp, asubst_comp]
    rfl

/-- Rocq: `Analysis.PeanoArith.fsubst_comp`. -/
theorem fsubst_comp : ∀ (A : Form) (σ τ : Nat → ATerm),
    fsubst σ (fsubst τ A) = fsubst (fun i => asubst σ (τ i)) A
  | eq s t, σ, τ => congrArg₂ eq (asubst_comp σ τ s) (asubst_comp σ τ t)
  | bot, _, _ => rfl
  | conj A B, σ, τ => congrArg₂ conj (fsubst_comp A σ τ) (fsubst_comp B σ τ)
  | disj A B, σ, τ => congrArg₂ disj (fsubst_comp A σ τ) (fsubst_comp B σ τ)
  | imp A B, σ, τ => congrArg₂ imp (fsubst_comp A σ τ) (fsubst_comp B σ τ)
  | all A, σ, τ => congrArg all ((fsubst_comp A (up σ) (up τ)).trans (fsubst_ext A (up_comp σ τ)))
  | ex A, σ, τ => congrArg ex ((fsubst_comp A (up σ) (up τ)).trans (fsubst_ext A (up_comp σ τ)))
  | px t, σ, τ => congrArg px (asubst_comp σ τ t)

/-- Rocq: `Analysis.PeanoArith.fsubst_id`. -/
theorem fsubst_id : ∀ (A : Form) {σ : Nat → ATerm}, (∀ i, σ i = tv i) → fsubst σ A = A
  | eq s t, σ, h => by
    show eq (asubst σ s) (asubst σ t) = eq s t
    rw [asubst_ext h s, asubst_ext h t, asubst_id, asubst_id]
  | bot, _, _ => rfl
  | conj A B, _, h => congrArg₂ conj (fsubst_id A h) (fsubst_id B h)
  | disj A B, _, h => congrArg₂ disj (fsubst_id A h) (fsubst_id B h)
  | imp A B, _, h => congrArg₂ imp (fsubst_id A h) (fsubst_id B h)
  | all A, σ, h => congrArg all (fsubst_id A (σ := up σ) (fun
      | 0 => rfl
      | i + 1 => by show asubst shiftSub (σ i) = tv (i + 1); rw [h i]; rfl))
  | ex A, σ, h => congrArg ex (fsubst_id A (σ := up σ) (fun
      | 0 => rfl
      | i + 1 => by show asubst shiftSub (σ i) = tv (i + 1); rw [h i]; rfl))
  | px t, σ, h => by
    show px (asubst σ t) = px t
    rw [asubst_ext h t, asubst_id]

/-- Instantiating a shifted quantifier body with the new variable gives back
the body. Rocq: `Analysis.PeanoArith.sub1_up_shift`. -/
theorem sub1_up_shift (A : Form) : sub1 (fsubst (up shiftSub) A) (tv 0) = A := by
  unfold sub1
  rw [fsubst_comp]
  exact fsubst_id A (fun | 0 => rfl | _ + 1 => rfl)

/-- Rocq: `Analysis.PeanoArith.fshift_sub1`. -/
theorem fshift_sub1 (A : Form) (t : ATerm) :
    fshift (sub1 A t) = sub1 (fsubst (up shiftSub) A) (asubst shiftSub t) := by
  unfold fshift sub1
  rw [fsubst_comp, fsubst_comp]
  exact fsubst_ext A (fun | 0 => rfl | _ + 1 => rfl)

/-! ## Natural deduction

`Prov cl Γ A`: `A` is provable from the hypotheses `Γ`, classically if `cl`
is `true`. The induction rule has its premises in fixed contexts; with the
other rules it gives the induction axiom (`induction_axiom`). -/

/-- Rocq: `Analysis.PeanoArith.prov`. -/
inductive Prov (cl : Bool) : List Form → Form → Prop where
  | hyp (Γ : List Form) (A : Form) : A ∈ Γ → Prov cl Γ A
  | botE (Γ : List Form) (A : Form) : Prov cl Γ bot → Prov cl Γ A
  | dne (Γ : List Form) (A : Form) : cl = true → Prov cl Γ A.neg.neg → Prov cl Γ A
  | andI (Γ : List Form) (A B : Form) : Prov cl Γ A → Prov cl Γ B → Prov cl Γ (conj A B)
  | andE1 (Γ : List Form) (A B : Form) : Prov cl Γ (conj A B) → Prov cl Γ A
  | andE2 (Γ : List Form) (A B : Form) : Prov cl Γ (conj A B) → Prov cl Γ B
  | orI1 (Γ : List Form) (A B : Form) : Prov cl Γ A → Prov cl Γ (disj A B)
  | orI2 (Γ : List Form) (A B : Form) : Prov cl Γ B → Prov cl Γ (disj A B)
  | orE (Γ : List Form) (A B C : Form) : Prov cl Γ (disj A B) → Prov cl (A :: Γ) C →
      Prov cl (B :: Γ) C → Prov cl Γ C
  | impI (Γ : List Form) (A B : Form) : Prov cl (A :: Γ) B → Prov cl Γ (imp A B)
  | impE (Γ : List Form) (A B : Form) : Prov cl Γ (imp A B) → Prov cl Γ A → Prov cl Γ B
  | allI (Γ : List Form) (A : Form) : Prov cl (Γ.map fshift) A → Prov cl Γ (all A)
  | allE (Γ : List Form) (A : Form) (t : ATerm) : Prov cl Γ (all A) → Prov cl Γ (sub1 A t)
  | exI (Γ : List Form) (A : Form) (t : ATerm) : Prov cl Γ (sub1 A t) → Prov cl Γ (ex A)
  | exE (Γ : List Form) (A B : Form) : Prov cl Γ (ex A) →
      Prov cl (A :: Γ.map fshift) (fshift B) → Prov cl Γ B
  | refl (Γ : List Form) (t : ATerm) : Prov cl Γ (eq t t)
  | leib (Γ : List Form) (A : Form) (s t : ATerm) : Prov cl Γ (eq s t) →
      Prov cl Γ (sub1 A s) → Prov cl Γ (sub1 A t)
  | succNe (Γ : List Form) (t : ATerm) : Prov cl Γ (eq (ts t) tz).neg
  | succInj (Γ : List Form) (s t : ATerm) : Prov cl Γ (eq (ts s) (ts t)) → Prov cl Γ (eq s t)
  | plus0 (Γ : List Form) (t : ATerm) : Prov cl Γ (eq (tplus t tz) t)
  | plusS (Γ : List Form) (s t : ATerm) : Prov cl Γ (eq (tplus s (ts t)) (ts (tplus s t)))
  | mult0 (Γ : List Form) (t : ATerm) : Prov cl Γ (eq (tmult t tz) tz)
  | multS (Γ : List Form) (s t : ATerm) : Prov cl Γ (eq (tmult s (ts t)) (tplus (tmult s t) s))
  | ind (Γ : List Form) (A : Form) : Prov cl [] (sub1 A tz) → Prov cl [A] (fsubst sucSub A) →
      Prov cl Γ (all A)

/-- Peano arithmetic. -/
abbrev PA : List Form → Form → Prop := Prov true
/-- Heyting arithmetic. -/
abbrev HA : List Form → Form → Prop := Prov false

theorem mem_map_of_mem {α β : Type} (f : α → β) {a : α} : ∀ {l : List α}, a ∈ l → f a ∈ l.map f
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ h => .tail _ (mem_map_of_mem f h)

theorem exists_of_mem_map {α β : Type} {f : α → β} {b : β} :
    ∀ {l : List α}, b ∈ l.map f → ∃ a, a ∈ l ∧ f a = b
  | a :: _, .head _ => ⟨a, .head _, rfl⟩
  | _ :: _, .tail _ h =>
    let ⟨a, ha, e⟩ := exists_of_mem_map h
    ⟨a, .tail _ ha, e⟩

theorem incl_map {α β : Type} (f : α → β) {l l' : List α} (h : ∀ a, a ∈ l → a ∈ l') :
    ∀ b, b ∈ l.map f → b ∈ l'.map f := fun _ hb =>
  let ⟨_, ha, e⟩ := exists_of_mem_map hb
  e ▸ mem_map_of_mem f (h _ ha)

theorem incl_cons' {α : Type} {a : α} {l l' : List α} (h : ∀ b, b ∈ l → b ∈ l') :
    ∀ b, b ∈ a :: l → b ∈ a :: l'
  | _, .head _ => .head _
  | _, .tail _ hb => .tail _ (h _ hb)

/-- Rocq: `Analysis.PeanoArith.prov_weaken`. -/
theorem prov_weaken {cl : Bool} {Γ : List Form} {A : Form} (h : Prov cl Γ A) :
    ∀ Γ' : List Form, (∀ B, B ∈ Γ → B ∈ Γ') → Prov cl Γ' A := by
  induction h with
  | hyp Γ A hA => exact fun Γ' hi => .hyp _ _ (hi _ hA)
  | botE Γ A _ ih => exact fun Γ' hi => .botE _ _ (ih Γ' hi)
  | dne Γ A hc _ ih => exact fun Γ' hi => .dne _ _ hc (ih Γ' hi)
  | andI Γ A B _ _ ih1 ih2 => exact fun Γ' hi => .andI _ _ _ (ih1 Γ' hi) (ih2 Γ' hi)
  | andE1 Γ A B _ ih => exact fun Γ' hi => .andE1 _ _ B (ih Γ' hi)
  | andE2 Γ A B _ ih => exact fun Γ' hi => .andE2 _ A _ (ih Γ' hi)
  | orI1 Γ A B _ ih => exact fun Γ' hi => .orI1 _ _ _ (ih Γ' hi)
  | orI2 Γ A B _ ih => exact fun Γ' hi => .orI2 _ _ _ (ih Γ' hi)
  | orE Γ A B C _ _ _ ih1 ih2 ih3 =>
    exact fun Γ' hi => .orE _ A B _ (ih1 Γ' hi) (ih2 _ (incl_cons' hi)) (ih3 _ (incl_cons' hi))
  | impI Γ A B _ ih => exact fun Γ' hi => .impI _ _ _ (ih _ (incl_cons' hi))
  | impE Γ A B _ _ ih1 ih2 => exact fun Γ' hi => .impE _ A _ (ih1 Γ' hi) (ih2 Γ' hi)
  | allI Γ A _ ih => exact fun Γ' hi => .allI _ _ (ih _ (incl_map fshift hi))
  | allE Γ A t _ ih => exact fun Γ' hi => .allE _ _ t (ih Γ' hi)
  | exI Γ A t _ ih => exact fun Γ' hi => .exI _ _ t (ih Γ' hi)
  | exE Γ A B _ _ ih1 ih2 =>
    exact fun Γ' hi => .exE _ A _ (ih1 Γ' hi) (ih2 _ (incl_cons' (incl_map fshift hi)))
  | refl Γ t => exact fun Γ' _ => .refl _ t
  | leib Γ A s t _ _ ih1 ih2 => exact fun Γ' hi => .leib _ A s t (ih1 Γ' hi) (ih2 Γ' hi)
  | succNe Γ t => exact fun Γ' _ => .succNe _ t
  | succInj Γ s t _ ih => exact fun Γ' hi => .succInj _ _ _ (ih Γ' hi)
  | plus0 Γ t => exact fun Γ' _ => .plus0 _ t
  | plusS Γ s t => exact fun Γ' _ => .plusS _ s t
  | mult0 Γ t => exact fun Γ' _ => .mult0 _ t
  | multS Γ s t => exact fun Γ' _ => .multS _ s t
  | ind Γ A h0 h1 _ _ => exact fun Γ' _ => .ind _ _ h0 h1

/-- Rocq: `Analysis.PeanoArith.hyp0`. -/
theorem hyp0 {cl : Bool} {Γ : List Form} {A : Form} : Prov cl (A :: Γ) A := .hyp _ _ (.head _)

/-- Rocq: `Analysis.PeanoArith.hyp1`. -/
theorem hyp1 {cl : Bool} {Γ : List Form} {A B : Form} : Prov cl (B :: A :: Γ) A :=
  .hyp _ _ (.tail _ (.head _))

/-- Rocq: `Analysis.PeanoArith.hyp2`. -/
theorem hyp2 {cl : Bool} {Γ : List Form} {A B C : Form} : Prov cl (C :: B :: A :: Γ) A :=
  .hyp _ _ (.tail _ (.tail _ (.head _)))

/-- Rocq: `Analysis.PeanoArith.weak1`. -/
theorem weak1 {cl : Bool} {Γ : List Form} {A B : Form} (h : Prov cl Γ A) : Prov cl (B :: Γ) A :=
  prov_weaken h _ (fun _ hb => .tail _ hb)

/-- Rocq: `Analysis.PeanoArith.weak2`. -/
theorem weak2 {cl : Bool} {Γ : List Form} {A B C : Form} (h : Prov cl Γ A) :
    Prov cl (C :: B :: Γ) A :=
  prov_weaken h _ (fun _ hb => .tail _ (.tail _ hb))

/-- Rocq: `Analysis.PeanoArith.weak3`. -/
theorem weak3 {cl : Bool} {Γ : List Form} {A B C D : Form} (h : Prov cl Γ A) :
    Prov cl (D :: C :: B :: Γ) A :=
  prov_weaken h _ (fun _ hb => .tail _ (.tail _ (.tail _ hb)))

/-! ### Derivations are closed under substitution -/

/-- Rocq: `Analysis.PeanoArith.up_shift`. -/
theorem up_shift (σ : Nat → ATerm) (i : Nat) :
    asubst (up σ) (shiftSub i) = asubst shiftSub (σ i) := rfl

/-- Rocq: `Analysis.PeanoArith.fsubst_shift_comm`. -/
theorem fsubst_shift_comm (σ : Nat → ATerm) (A : Form) :
    fsubst (up σ) (fshift A) = fshift (fsubst σ A) := by
  unfold fshift
  rw [fsubst_comp, fsubst_comp]
  exact fsubst_ext A (fun _ => rfl)

/-- Rocq: `Analysis.PeanoArith.fsubst_sub1`. -/
theorem fsubst_sub1 (σ : Nat → ATerm) (A : Form) (t : ATerm) :
    fsubst σ (sub1 A t) = sub1 (fsubst (up σ) A) (asubst σ t) := by
  unfold sub1
  rw [fsubst_comp, fsubst_comp]
  refine fsubst_ext A (fun
    | 0 => rfl
    | i + 1 => ?_)
  show σ i = asubst (inst1 (asubst σ t)) (asubst shiftSub (σ i))
  rw [asubst_comp]
  exact ((asubst_ext (τ := tv) (fun _ => rfl) (σ i)).trans (asubst_id _)).symm

/-- Rocq: `Analysis.PeanoArith.fsubst_suc`. -/
theorem fsubst_suc (σ : Nat → ATerm) (A : Form) :
    fsubst (up σ) (fsubst sucSub A) = fsubst sucSub (fsubst (up σ) A) := by
  rw [fsubst_comp, fsubst_comp]
  refine fsubst_ext A (fun
    | 0 => rfl
    | i + 1 => ?_)
  show asubst shiftSub (σ i) = asubst sucSub (asubst shiftSub (σ i))
  rw [asubst_comp]
  exact asubst_ext (fun _ => rfl) _

theorem map_map {α β γ : Type} (f : α → β) (g : β → γ) :
    ∀ l : List α, (l.map f).map g = l.map (fun x => g (f x))
  | [] => rfl
  | a :: l => congrArg (g (f a) :: ·) (map_map f g l)

theorem map_ext {α β : Type} {f g : α → β} (h : ∀ a, f a = g a) : ∀ l : List α, l.map f = l.map g
  | [] => rfl
  | a :: l => congrArg₂ (· :: ·) (h a) (map_ext h l)

/-- Rocq: `Analysis.PeanoArith.prov_subst`. -/
theorem prov_subst {cl : Bool} {Γ : List Form} {A : Form} (h : Prov cl Γ A) :
    ∀ σ : Nat → ATerm, Prov cl (Γ.map (fsubst σ)) (fsubst σ A) := by
  induction h with
  | hyp Γ A hA => exact fun σ => .hyp _ _ (mem_map_of_mem _ hA)
  | botE Γ A _ ih => exact fun σ => .botE _ _ (ih σ)
  | dne Γ A hc _ ih => exact fun σ => .dne _ _ hc (ih σ)
  | andI Γ A B _ _ ih1 ih2 => exact fun σ => .andI _ _ _ (ih1 σ) (ih2 σ)
  | andE1 Γ A B _ ih => exact fun σ => .andE1 _ _ _ (ih σ)
  | andE2 Γ A B _ ih => exact fun σ => .andE2 _ _ _ (ih σ)
  | orI1 Γ A B _ ih => exact fun σ => .orI1 _ _ _ (ih σ)
  | orI2 Γ A B _ ih => exact fun σ => .orI2 _ _ _ (ih σ)
  | orE Γ A B C _ _ _ ih1 ih2 ih3 => exact fun σ => .orE _ _ _ _ (ih1 σ) (ih2 σ) (ih3 σ)
  | impI Γ A B _ ih => exact fun σ => .impI _ _ _ (ih σ)
  | impE Γ A B _ _ ih1 ih2 => exact fun σ => .impE _ _ _ (ih1 σ) (ih2 σ)
  | allI Γ A _ ih =>
    intro σ
    refine .allI _ _ ?_
    have h := ih (up σ)
    rw [map_map, map_ext (fun B => fsubst_shift_comm σ B), ← map_map] at h
    exact h
  | allE Γ A t _ ih =>
    intro σ
    rw [fsubst_sub1]
    exact .allE _ _ _ (ih σ)
  | exI Γ A t _ ih =>
    intro σ
    have h := ih σ
    rw [fsubst_sub1] at h
    exact .exI _ _ _ h
  | exE Γ A B _ _ ih1 ih2 =>
    intro σ
    have h := ih2 (up σ)
    rw [fsubst_shift_comm] at h
    show Prov cl _ _
    have e : (A :: Γ.map fshift).map (fsubst (up σ)) =
        fsubst (up σ) A :: (Γ.map (fsubst σ)).map fshift := by
      show fsubst (up σ) A :: _ = _
      rw [map_map, map_map, map_ext (fun B => fsubst_shift_comm σ B)]
    rw [e] at h
    exact .exE _ _ _ (ih1 σ) h
  | refl Γ t => exact fun σ => .refl _ _
  | leib Γ A s t _ _ ih1 ih2 =>
    intro σ
    rw [fsubst_sub1]
    have h := ih2 σ
    rw [fsubst_sub1] at h
    exact .leib _ _ _ _ (ih1 σ) h
  | succNe Γ t => exact fun σ => .succNe _ _
  | succInj Γ s t _ ih => exact fun σ => .succInj _ _ _ (ih σ)
  | plus0 Γ t => exact fun σ => .plus0 _ _
  | plusS Γ s t => exact fun σ => .plusS _ _ _
  | mult0 Γ t => exact fun σ => .mult0 _ _
  | multS Γ s t => exact fun σ => .multS _ _ _
  | ind Γ A _ _ ih0 ih1 =>
    intro σ
    refine .ind _ _ ?_ ?_
    · have h := ih0 σ
      rw [fsubst_sub1] at h
      exact h
    · have h := ih1 (up σ)
      rw [fsubst_suc] at h
      exact h

/-! ## The induction axiom -/

/-- Rocq: `Analysis.PeanoArith.induction_axiom`. -/
theorem induction_axiom (cl : Bool) (Γ : List Form) (A : Form) :
    Prov cl Γ (imp (sub1 A tz) (imp (all (imp A (fsubst sucSub A))) (all A))) := by
  -- Induction on `B := A(0) → ∀x (A x → A (S x)) → A`, with the first two
  -- shifted past the induction variable.
  let Hz := all (imp A (fsubst sucSub A))
  let B := imp (fshift (sub1 A tz)) (imp (fshift Hz) A)
  have E1 : ∀ σ : Nat → ATerm, (∀ i, σ (i + 1) = tv (i + 1)) →
      fsubst σ (fshift (sub1 A tz)) = fshift (sub1 A tz) := by
    intro σ hσ
    unfold fshift
    rw [fsubst_comp]
    exact fsubst_ext _ (fun i => hσ i)
  have E2 : ∀ σ : Nat → ATerm, (∀ i, σ (i + 1) = tv (i + 1)) → fsubst σ (fshift Hz) = fshift Hz := by
    intro σ hσ
    unfold fshift
    rw [fsubst_comp]
    exact fsubst_ext _ (fun i => hσ i)
  have E3 : ∀ X, fsubst (inst1 tz) (fshift X) = X := by
    intro X
    unfold fshift
    rw [fsubst_comp]
    exact fsubst_id X (fun _ => rfl)
  have HB : Prov cl [] (all B) := by
    refine .ind _ _ ?_ ?_
    · show Prov cl [] (imp (fsubst (inst1 tz) (fshift (sub1 A tz)))
        (imp (fsubst (inst1 tz) (fshift Hz)) (fsubst (inst1 tz) A)))
      rw [E3, E3]
      exact .impI _ _ _ (.impI _ _ _ hyp1)
    · show Prov cl [B] (imp (fsubst sucSub (fshift (sub1 A tz)))
        (imp (fsubst sucSub (fshift Hz)) (fsubst sucSub A)))
      rw [E1 sucSub (fun _ => rfl), E2 sucSub (fun _ => rfl)]
      refine .impI _ _ _ (.impI _ _ _ ?_)
      have HA0 : Prov cl [fshift Hz, fshift (sub1 A tz), B] A :=
        .impE _ _ _ (.impE _ _ _ hyp2 hyp1) hyp0
      have Hstep : Prov cl [fshift Hz, fshift (sub1 A tz), B]
          (sub1 (fsubst (up shiftSub) (imp A (fsubst sucSub A))) (tv 0)) :=
        .allE _ _ _ hyp0
      rw [sub1_up_shift] at Hstep
      exact .impE _ _ _ Hstep HA0
  refine .impI _ _ _ (.impI _ _ _ (.allI _ _ ?_))
  have Hi : Prov cl ((Hz :: sub1 A tz :: Γ).map fshift) (sub1 (fsubst (up shiftSub) B) (tv 0)) :=
    .allE _ _ _ (prov_weaken (prov_subst HB shiftSub) _ (fun _ h => nomatch h))
  rw [sub1_up_shift] at Hi
  exact .impE _ _ _ (.impE _ _ _ Hi (.hyp _ _ (.tail _ (.head _)))) (.hyp _ _ (.head _))

/-! ## The Gödel–Gentzen negative translation -/

/-- Rocq: `Analysis.PeanoArith.gg`. -/
def gg : Form → Form
  | eq s t => (eq s t).neg.neg
  | bot => bot
  | conj A B => conj (gg A) (gg B)
  | disj A B => (conj (gg A).neg (gg B).neg).neg
  | imp A B => imp (gg A) (gg B)
  | all A => all (gg A)
  | ex A => (all (gg A).neg).neg
  | px t => (px t).neg.neg

/-- Rocq: `Analysis.PeanoArith.gg_subst`. -/
theorem gg_subst : ∀ (A : Form) (σ : Nat → ATerm), gg (fsubst σ A) = fsubst σ (gg A)
  | eq _ _, _ => rfl
  | bot, _ => rfl
  | conj A B, σ => congrArg₂ conj (gg_subst A σ) (gg_subst B σ)
  | disj A B, σ => by
    show (conj (gg (fsubst σ A)).neg (gg (fsubst σ B)).neg).neg = _
    rw [gg_subst A σ, gg_subst B σ]; rfl
  | imp A B, σ => congrArg₂ imp (gg_subst A σ) (gg_subst B σ)
  | all A, σ => congrArg all (gg_subst A (up σ))
  | ex A, σ => by
    show (all (gg (fsubst (up σ) A)).neg).neg = _
    rw [gg_subst A (up σ)]; rfl
  | px _, _ => rfl

/-- Rocq: `Analysis.PeanoArith.gg_shift`. -/
theorem gg_shift (Γ : List Form) : (Γ.map fshift).map gg = (Γ.map gg).map fshift := by
  rw [map_map, map_map]
  exact map_ext (fun A => gg_subst A shiftSub) Γ

/-- Rocq: `Analysis.PeanoArith.dni`. -/
theorem dni {Γ : List Form} {A : Form} (h : HA Γ A) : HA Γ A.neg.neg :=
  .impI _ _ _ (.impE _ _ _ hyp0 (weak1 h))

/-- Rocq: `Analysis.PeanoArith.tneg`. -/
theorem tneg (Γ : List Form) (A : Form) : HA Γ (imp A.neg.neg.neg A.neg) :=
  .impI _ _ _ (.impI _ _ _ (.impE _ _ _ hyp1 (.impI _ _ _ (.impE _ _ _ hyp0 hyp1))))

/-- Translated formulas are stable under double negation.
Rocq: `Analysis.PeanoArith.gg_stable`. -/
theorem gg_stable : ∀ (A : Form) (Γ : List Form), HA Γ (imp (gg A).neg.neg (gg A))
  | eq s t, Γ => tneg Γ (eq s t).neg
  | bot, _ => .impI _ _ _ (.impE _ _ _ hyp0 (.impI _ _ _ hyp0))
  | conj A B, _ =>
    .impI _ _ _ (.andI _ _ _
      (.impE _ _ _ (gg_stable A _) (.impI _ _ _ (.impE _ _ _ hyp1
        (.impI _ _ _ (.impE _ _ _ hyp1 (.andE1 _ _ _ hyp0))))))
      (.impE _ _ _ (gg_stable B _) (.impI _ _ _ (.impE _ _ _ hyp1
        (.impI _ _ _ (.impE _ _ _ hyp1 (.andE2 _ _ _ hyp0)))))))
  | disj A B, Γ => tneg Γ _
  | imp A B, _ =>
    .impI _ _ _ (.impI _ _ _ (.impE _ _ _ (gg_stable B _)
      (.impI _ _ _ (.impE _ _ _ hyp2
        (.impI _ _ _ (.impE _ _ _ hyp1 (.impE _ _ _ hyp0 hyp2)))))))
  | all A, Γ => by
    refine .impI _ _ _ (.allI _ _ ?_)
    refine .impE _ _ _ (gg_stable A _) (.impI _ _ _ (.impE _ _ _ hyp1 ?_))
    refine .impI _ _ _ (.impE _ _ _ hyp1 ?_)
    have Hx : HA (all (fsubst (up shiftSub) (gg A)) :: (gg A).neg ::
        ((all (gg A)).neg.neg :: Γ).map fshift) (sub1 (fsubst (up shiftSub) (gg A)) (tv 0)) :=
      .allE _ _ _ hyp0
    rw [sub1_up_shift] at Hx
    exact Hx
  | ex A, Γ => tneg Γ _
  | px t, Γ => tneg Γ (px t).neg

/-- Rocq: `Analysis.PeanoArith.gg_dne`. -/
theorem gg_dne {Γ : List Form} {A : Form} (h : HA Γ (gg A).neg.neg) : HA Γ (gg A) :=
  .impE _ _ _ (gg_stable A Γ) h

theorem incl_swap {α : Type} {a b : α} {l : List α} : ∀ x, x ∈ a :: l → x ∈ a :: b :: l
  | _, .head _ => .head _
  | _, .tail _ h => .tail _ (.tail _ h)

/-- Rocq: `Analysis.PeanoArith.negative_translation`. -/
theorem negative_translation {Γ : List Form} {A : Form} (h : PA Γ A) : HA (Γ.map gg) (gg A) := by
  induction h with
  | hyp Γ A hA => exact .hyp _ _ (mem_map_of_mem _ hA)
  | botE Γ A _ ih => exact .botE _ _ ih
  | dne Γ A _ _ ih => exact gg_dne ih
  | andI Γ A B _ _ ih1 ih2 => exact .andI _ _ _ ih1 ih2
  | andE1 Γ A B _ ih => exact .andE1 _ _ _ ih
  | andE2 Γ A B _ ih => exact .andE2 _ _ _ ih
  | orI1 Γ A B _ ih => exact .impI _ _ _ (.impE _ _ _ (.andE1 _ _ _ hyp0) (weak1 ih))
  | orI2 Γ A B _ ih => exact .impI _ _ _ (.impE _ _ _ (.andE2 _ _ _ hyp0) (weak1 ih))
  | orE Γ A B C _ _ _ ih1 ih2 ih3 =>
    exact gg_dne (.impI _ _ _ (.impE _ _ _ (weak1 ih1) (.andI _ _ _
      (.impI _ _ _ (.impE _ _ _ hyp1 (prov_weaken ih2 _ incl_swap)))
      (.impI _ _ _ (.impE _ _ _ hyp1 (prov_weaken ih3 _ incl_swap))))))
  | impI Γ A B _ ih => exact .impI _ _ _ ih
  | impE Γ A B _ _ ih1 ih2 => exact .impE _ _ _ ih1 ih2
  | allI Γ A _ ih =>
    refine .allI _ _ ?_
    rw [← gg_shift]
    exact ih
  | allE Γ A t _ ih =>
    show HA _ (gg (fsubst _ A))
    rw [gg_subst]
    exact .allE _ _ _ ih
  | exI Γ A t _ ih =>
    have ih' : HA (Γ.map gg) (sub1 (gg A) t) := by
      unfold sub1; rw [← gg_subst]; exact ih
    exact .impI _ _ _ (.impE _ _ _ (.allE (Γ := _ :: _) (gg A).neg t hyp0) (weak1 ih'))
  | exE Γ A B _ _ ih1 ih2 =>
    have ih2' : HA (gg A :: (Γ.map gg).map fshift) (fshift (gg B)) := by
      rw [← gg_shift]; unfold fshift; rw [← gg_subst]; exact ih2
    refine gg_dne (.impI _ _ _ (.impE _ _ _ (weak1 ih1) (.allI _ _ ?_)))
    exact .impI _ _ _ (.impE _ _ _ hyp1 (prov_weaken ih2' _ incl_swap))
  | refl Γ t => exact dni (.refl _ _)
  | leib Γ A s t _ _ ih1 ih2 =>
    have ih2' : HA (Γ.map gg) (sub1 (gg A) s) := by
      unfold sub1; rw [← gg_subst]; exact ih2
    show HA _ (gg (fsubst _ A))
    refine gg_dne ?_
    rw [gg_subst]
    exact .impI _ _ _ (.impE _ _ _ (weak1 ih1) (.impI _ _ _ (.impE _ _ _ hyp1
      (.leib _ _ s t hyp0 (weak2 ih2')))))
  | succNe Γ t => exact .impI _ _ _ (.impE _ _ _ hyp0 (.succNe _ _))
  | succInj Γ s t _ ih =>
    exact .impI _ _ _ (.impE _ _ _ (weak1 ih) (.impI _ _ _ (.impE _ _ _ hyp1 (.succInj _ _ _ hyp0))))
  | plus0 Γ t => exact dni (.plus0 _ _)
  | plusS Γ s t => exact dni (.plusS _ _ _)
  | mult0 Γ t => exact dni (.mult0 _ _)
  | multS Γ s t => exact dni (.multS _ _ _)
  | ind Γ A _ _ ih0 ih1 =>
    refine .ind _ _ ?_ ?_
    · have h := ih0
      unfold sub1 at h; rw [gg_subst] at h; exact h
    · have h := ih1
      rw [gg_subst] at h; exact h

/-- Rocq: `Analysis.PeanoArith.PA_HA_consistency`. -/
theorem PA_HA_consistency (h : PA [] bot) : HA [] bot := negative_translation h

end ConstructiveOrdinals.PeanoArith
