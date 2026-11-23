import ConstructiveOrdinals.Bachmann.Defs

/-!
# Associativity of addition and the invariant `BFam`

Tree addition is not syntactically associative, but it is associative up to
the family-respecting order `bsub` in both directions, and hence up to `φ`.
This is needed to shift the step theorems to an arbitrary base: the components
of `β + (γ + δ)` must be compared with those of `(β + γ) + δ`.

Ported from the Rocq file `BachmannAssoc.v`.

Lean note: `badd_assoc_1` and `badd_assoc_2` destructure all three trees, so
both sides reduce and the matching of children is a direct case split; the
Rocq case lemmas (`badd_small_cases`, …) are ported as well.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-- Rocq: `BachmannAssoc.bsub_trans`. -/
theorem bsub_trans : ∀ {x y z : BOrd.{u}}, bsub x y → bsub y z → bsub x z
  | bnode _ g _ h, bnode _ _ _ _, bnode _ _ _ _, ⟨hxy1, hxy2⟩, ⟨hyz1, hyz2⟩ =>
    ⟨fun a => let ⟨b, hb⟩ := hxy1 a; let ⟨e, he⟩ := hyz1 b; ⟨e, bsub_trans (x := g a) hb he⟩,
     fun c => let ⟨d, hd⟩ := hxy2 c; let ⟨e, he⟩ := hyz2 d; ⟨e, fun ξ => bsub_trans (x := h c ξ) (hd ξ) (he ξ)⟩⟩

/-- Rocq: `BachmannAssoc.bsub_intro`. -/
theorem bsub_intro (x y : BOrd.{u}) (H1 : ∀ a, ∃ b, bsub (bsmallSz x a) (bsmallSz y b))
    (H2 : ∀ c, ∃ d, ∀ ξ, bsub (bbigSz x c ξ) (bbigSz y d ξ)) : bsub x y := by
  cases x; cases y; exact ⟨H1, H2⟩

/-- The children of `x + y`: those of `x`, and `x + (children of y)`.
Rocq: `BachmannAssoc.badd_small_cases`. -/
theorem badd_small_cases (x y : BOrd.{u}) (a : bsmall (badd x y)) :
    (∃ a', bsmallSz (badd x y) a = bsmallSz x a') ∨ (∃ b, bsmallSz (badd x y) a = badd x (bsmallSz y b)) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B k D l =>
  match a with
  | .inl a0 => exact .inl ⟨a0, rfl⟩
  | .inr b0 => exact .inr ⟨b0, rfl⟩

/-- Rocq: `BachmannAssoc.badd_big_cases`. -/
theorem badd_big_cases (x y : BOrd.{u}) (c : bbig (badd x y)) :
    (∃ c', ∀ ξ, bbigSz (badd x y) c ξ = bbigSz x c' ξ) ∨ (∃ d, ∀ ξ, bbigSz (badd x y) c ξ = badd x (bbigSz y d ξ)) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B k D l =>
  match c with
  | .inl c0 => exact .inl ⟨c0, fun _ => rfl⟩
  | .inr d0 => exact .inr ⟨d0, fun _ => rfl⟩

/-- Rocq: `BachmannAssoc.badd_small_l`. -/
theorem badd_small_l (x y : BOrd.{u}) (a' : bsmall x) : ∃ a, bsmallSz (badd x y) a = bsmallSz x a' := by
  cases x; cases y; exact ⟨.inl a', rfl⟩

/-- Rocq: `BachmannAssoc.badd_small_r`. -/
theorem badd_small_r (x y : BOrd.{u}) (b : bsmall y) : ∃ a, bsmallSz (badd x y) a = badd x (bsmallSz y b) := by
  cases x; cases y; exact ⟨.inr b, rfl⟩

/-- Rocq: `BachmannAssoc.badd_big_l`. -/
theorem badd_big_l (x y : BOrd.{u}) (c' : bbig x) : ∃ c, ∀ ξ, bbigSz (badd x y) c ξ = bbigSz x c' ξ := by
  cases x; cases y; exact ⟨.inl c', fun _ => rfl⟩

/-- Rocq: `BachmannAssoc.badd_big_r`. -/
theorem badd_big_r (x y : BOrd.{u}) (d : bbig y) : ∃ c, ∀ ξ, bbigSz (badd x y) c ξ = badd x (bbigSz y d ξ) := by
  cases x; cases y; exact ⟨.inr d, fun _ => rfl⟩

/-- Rocq: `BachmannAssoc.badd_assoc_1`. -/
theorem badd_assoc_1 (α β : BOrd.{u}) : ∀ γ, bsub (badd (badd α β) γ) (badd α (badd β γ)) := by
  cases α with
  | bnode A1 g1 C1 h1 =>
  cases β with
  | bnode B1 g2 D1 h2 =>
  intro γ
  induction γ with
  | bnode G g D h ihg ihh =>
  refine ⟨fun s => ?_, fun c => ?_⟩
  · match s with
    | .inl (.inl a) => exact ⟨.inl a, bsub_refl _⟩
    | .inl (.inr b) => exact ⟨.inr (.inl b), bsub_refl _⟩
    | .inr b => exact ⟨.inr (.inr b), ihg b⟩
  · match c with
    | .inl (.inl e) => exact ⟨.inl e, fun _ => bsub_refl _⟩
    | .inl (.inr e) => exact ⟨.inr (.inl e), fun _ => bsub_refl _⟩
    | .inr d => exact ⟨.inr (.inr d), fun ξ => ihh d ξ⟩

/-- Rocq: `BachmannAssoc.badd_assoc_2`. -/
theorem badd_assoc_2 (α β : BOrd.{u}) : ∀ γ, bsub (badd α (badd β γ)) (badd (badd α β) γ) := by
  cases α with
  | bnode A1 g1 C1 h1 =>
  cases β with
  | bnode B1 g2 D1 h2 =>
  intro γ
  induction γ with
  | bnode G g D h ihg ihh =>
  refine ⟨fun s => ?_, fun c => ?_⟩
  · match s with
    | .inl a => exact ⟨.inl (.inl a), bsub_refl _⟩
    | .inr (.inl b) => exact ⟨.inl (.inr b), bsub_refl _⟩
    | .inr (.inr b) => exact ⟨.inr b, ihg b⟩
  · match c with
    | .inl e => exact ⟨.inl (.inl e), fun _ => bsub_refl _⟩
    | .inr (.inl e) => exact ⟨.inl (.inr e), fun _ => bsub_refl _⟩
    | .inr (.inr d) => exact ⟨.inr d, fun ξ => ihh d ξ⟩

/-! ### Monotonicity of the arithmetic in the order `bsub` -/

/-- Rocq: `BachmannAssoc.bsub_badd_l`. -/
theorem bsub_badd_l (x x' : BOrd.{u}) (H : bsub x x') : ∀ y, bsub (badd x y) (badd x' y) := by
  intro y
  induction y with
  | bnode B g D h ihg ihh =>
  rw [badd_eq x (bnode B g D h), badd_eq x' (bnode B g D h)]
  exact bsub_blub _ _ _ _ H ⟨fun b => ⟨b, ihg b⟩, fun d => ⟨d, fun ξ => ihh d ξ⟩⟩

/-- Rocq: `BachmannAssoc.bsub_badd_r`. -/
theorem bsub_badd_r (x : BOrd.{u}) : ∀ y y', bsub y y' → bsub (badd x y) (badd x y') := by
  intro y
  induction y with
  | bnode B g D h ihg ihh =>
  intro y' H
  cases y' with
  | bnode B' g' D' h' =>
  rw [badd_eq x (bnode B g D h), badd_eq x (bnode B' g' D' h')]
  obtain ⟨H1, H2⟩ := H
  exact bsub_blub _ _ _ _ (bsub_refl _)
    ⟨fun b => let ⟨b', hb⟩ := H1 b; ⟨b', ihg b _ hb⟩, fun d => let ⟨d', hd⟩ := H2 d; ⟨d', fun ξ => ihh d ξ _ (hd ξ)⟩⟩

/-- Rocq: `BachmannAssoc.bsub_bmul_r`. -/
theorem bsub_bmul_r (x : BOrd.{u}) : ∀ y y', bsub y y' → bsub (bmul x y) (bmul x y') := by
  intro y
  induction y with
  | bnode B g D h ihg ihh =>
  intro y' H
  rw [bmul_eq x (bnode B g D h), bmul_eq x y']
  refine bsub_blub _ _ _ _ (bsub_bsup _ _ fun b => ?_) (bsub_intro _ _ (fun e => nomatch e) fun d => ?_)
  · obtain ⟨b', hb⟩ := bsub_small _ _ H b
    exact ⟨b', bsub_badd_l _ _ (ihg b _ hb) _⟩
  · obtain ⟨d', hd⟩ := bsub_big _ _ H d
    exact ⟨d', fun ξ => ihh d ξ _ (hd ξ)⟩

/-- Rocq: `BachmannAssoc.bsub_bmul_l`. -/
theorem bsub_bmul_l (x x' : BOrd.{u}) (H : bsub x x') : ∀ y, bsub (bmul x y) (bmul x' y) := by
  intro y
  induction y with
  | bnode B g D h ihg ihh =>
  rw [bmul_eq x (bnode B g D h), bmul_eq x' (bnode B g D h)]
  exact bsub_blub _ _ _ _ (bsub_bsup _ _ fun b => ⟨b, bsub_trans (bsub_badd_l _ _ (ihg b) _) (bsub_badd_r _ _ _ H)⟩)
    (bsub_intro _ _ (fun e => nomatch e) fun d => ⟨d, fun ξ => ihh d ξ⟩)

/-- Rocq: `BachmannAssoc.bsub_bexpΩ`. -/
theorem bsub_bexpΩ : ∀ y y' : BOrd.{u}, bsub y y' → bsub (bexpΩ y) (bexpΩ y') := by
  intro y
  induction y with
  | bnode B g D h ihg ihh =>
  intro y' H
  rw [bexpΩ_eq (bnode B g D h), bexpΩ_eq y']
  refine bsub_blub _ _ _ _ (bsub_refl _) (bsub_blub _ _ _ _ (bsub_bsup _ _ fun b => ?_)
    (bsub_intro _ _ (fun e => nomatch e) fun d => ?_))
  · obtain ⟨b', hb⟩ := bsub_small _ _ H b
    exact ⟨b', bsub_bmul_l _ _ (ihg b _ hb) _⟩
  · obtain ⟨d', hd⟩ := bsub_big _ _ H d
    exact ⟨d', fun ξ => ihh d ξ _ (hd ξ)⟩

/-- Rocq: `BachmannAssoc.bsub_embed`. -/
theorem bsub_embed : ∀ ξ ξ' : Ordinal.{u}, ξ ≤ ξ' → bsub (embed ξ) (embed ξ')
  | mk _ k, mk _ k', H =>
    ⟨fun a => let ⟨b, hb⟩ := le_subord H a; ⟨b, bsub_embed (k a) (k' b) hb⟩, fun e => nomatch e⟩

/-! ### The invariant `BFam`: every Ω-family is `bsub`-monotone -/

/-- Rocq: `BachmannAssoc.bfam`. -/
def BFam : BOrd.{u} → Prop
  | bnode _ g _ h => (∀ a, BFam (g a)) ∧ (∀ c ξ, BFam (h c ξ)) ∧ ∀ c ξ ξ', ξ ≤ ξ' → bsub (h c ξ) (h c ξ')

/-- Rocq: `BachmannAssoc.bfam_bmono`. -/
theorem bfam_bmono (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) : ∀ x : BOrd.{u}, BFam x → BMono f x
  | bnode _ g _ h, ⟨H1, H2, H3⟩ =>
    ⟨fun a => bfam_bmono f hf (g a) (H1 a), fun c ξ => bfam_bmono f hf (h c ξ) (H2 c ξ),
     fun c ξ ξ' H => bach_mono_index f hf _ _ (H3 c ξ ξ' H) (bfam_bmono f hf (h c ξ') (H2 c ξ')) 0⟩

/-- Rocq: `BachmannAssoc.bfam_small`. -/
theorem bfam_small (x : BOrd.{u}) (H : BFam x) : ∀ a, BFam (bsmallSz x a) := by
  cases x; exact H.1

/-- Rocq: `BachmannAssoc.bfam_big`. -/
theorem bfam_big (x : BOrd.{u}) (H : BFam x) : ∀ c ξ, BFam (bbigSz x c ξ) := by
  cases x; exact H.2.1

/-- Rocq: `BachmannAssoc.bfam_fam`. -/
theorem bfam_fam (x : BOrd.{u}) (H : BFam x) : ∀ c ξ ξ', ξ ≤ ξ' → bsub (bbigSz x c ξ) (bbigSz x c ξ') := by
  cases x; exact H.2.2

/-- Rocq: `BachmannAssoc.bfam_blub`. -/
theorem bfam_blub (x y : BOrd.{u}) (hx : BFam x) (hy : BFam y) : BFam (blub x y) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  obtain ⟨H1, H2, H3⟩ := hx
  obtain ⟨H1', H2', H3'⟩ := hy
  refine ⟨fun ab => ?_, fun cd ξ => ?_, fun cd => ?_⟩
  · match ab with
    | .inl a => exact H1 a
    | .inr b => exact H1' b
  · match cd with
    | .inl c => exact H2 c ξ
    | .inr d => exact H2' d ξ
  · match cd with
    | .inl c => exact H3 c
    | .inr d => exact H3' d

/-- Rocq: `BachmannAssoc.bfam_bsup`. -/
theorem bfam_bsup {I : Type u} (F : I → BOrd.{u}) (H : ∀ i, BFam (F i)) : BFam (bsup F) :=
  ⟨fun p => bfam_small _ (H p.1) p.2, fun p ξ => bfam_big _ (H p.1) p.2 ξ,
    fun p ξ ξ' hξ => bfam_fam _ (H p.1) p.2 ξ ξ' hξ⟩

/-- Rocq: `BachmannAssoc.bfam_bzero`. -/
theorem bfam_bzero : BFam bzero.{u} := ⟨fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e)⟩

/-- Rocq: `BachmannAssoc.bfam_bsucc`. -/
theorem bfam_bsucc (x : BOrd.{u}) (H : BFam x) : BFam (bsucc x) :=
  ⟨fun _ => H, fun e => (nomatch e), fun e => (nomatch e)⟩

/-- Rocq: `BachmannAssoc.bfam_embed`. -/
theorem bfam_embed : ∀ ξ : Ordinal.{u}, BFam (embed ξ)
  | mk _ k => ⟨fun a => bfam_embed (k a), fun e => (nomatch e), fun e => (nomatch e)⟩

/-- Rocq: `BachmannAssoc.bfam_Ω`. -/
theorem bfam_Ω : BFam bOmega.{u} :=
  ⟨fun e => (nomatch e), fun _ ξ => bfam_embed ξ, fun _ ξ ξ' H => bsub_embed ξ ξ' H⟩

/-- Rocq: `BachmannAssoc.bfam_badd`. -/
theorem bfam_badd (x y : BOrd.{u}) (hx : BFam x) : BFam y → BFam (badd x y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Hy1, Hy2, Hy3⟩ := hy
  rw [badd_eq x (bnode B g D h)]
  exact bfam_blub _ _ hx ⟨fun b => ihg b (Hy1 b), fun d ξ => ihh d ξ (Hy2 d ξ),
    fun d ξ ξ' H => bsub_badd_r _ _ _ (Hy3 d ξ ξ' H)⟩

/-- Rocq: `BachmannAssoc.bfam_bmul`. -/
theorem bfam_bmul (x y : BOrd.{u}) (hx : BFam x) : BFam y → BFam (bmul x y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Hy1, Hy2, Hy3⟩ := hy
  rw [bmul_eq x (bnode B g D h)]
  exact bfam_blub _ _ (bfam_bsup _ fun b => bfam_badd _ _ (ihg b (Hy1 b)) hx)
    ⟨fun e => (nomatch e), fun d ξ => ihh d ξ (Hy2 d ξ), fun d ξ ξ' H => bsub_bmul_r _ _ _ (Hy3 d ξ ξ' H)⟩

/-- Rocq: `BachmannAssoc.bfam_bexpΩ`. -/
theorem bfam_bexpΩ (y : BOrd.{u}) : BFam y → BFam (bexpΩ y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Hy1, Hy2, Hy3⟩ := hy
  rw [bexpΩ_eq (bnode B g D h)]
  exact bfam_blub _ _ (bfam_bsucc _ bfam_bzero) (bfam_blub _ _
    (bfam_bsup _ fun b => bfam_bmul _ _ (ihg b (Hy1 b)) bfam_Ω)
    ⟨fun e => (nomatch e), fun d ξ => ihh d ξ (Hy2 d ξ), fun d ξ ξ' H => bsub_bexpΩ _ _ (Hy3 d ξ ξ' H)⟩)

/-- Rocq: `BachmannAssoc.bfam_btower`. -/
theorem bfam_btower : ∀ n : Nat, BFam (btower.{u} n)
  | 0 => bfam_bsucc _ bfam_Ω
  | n + 1 => bfam_bexpΩ _ (bfam_btower n)

/-- Rocq: `BachmannAssoc.bfam_bεΩ1`. -/
theorem bfam_bεΩ1 : BFam bεΩ1.{u} := ⟨fun n => bfam_btower n.down, fun e => (nomatch e), fun e => (nomatch e)⟩

/-- Trees that are `bsub`-equivalent have the same `φ`. Rocq: `BachmannAssoc.bach_bsub_eq`. -/
theorem bach_bsub_eq (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (x y : BOrd.{u})
    (Hxy : bsub x y) (Hyx : bsub y x) (Hx : BFam x) (Hy : BFam y) (z : Ordinal.{u}) : bach f x z ≈ bach f y z :=
  equiv_intro (bach_mono_index f hf _ _ Hxy (bfam_bmono f hf y Hy) z)
    (bach_mono_index f hf _ _ Hyx (bfam_bmono f hf x Hx) z)

/-- Rocq: `BachmannAssoc.bach_badd_assoc`. -/
theorem bach_badd_assoc (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α β γ : BOrd.{u})
    (Hα : BFam α) (Hβ : BFam β) (Hγ : BFam γ) (z : Ordinal.{u}) :
    bach f (badd α (badd β γ)) z ≈ bach f (badd (badd α β) γ) z :=
  bach_bsub_eq f hf _ _ (badd_assoc_2 α β γ) (badd_assoc_1 α β γ)
    (bfam_badd _ _ Hα (bfam_badd _ _ Hβ Hγ)) (bfam_badd _ _ (bfam_badd _ _ Hα Hβ) Hγ) z

end Bachmann

end ConstructiveOrdinals
