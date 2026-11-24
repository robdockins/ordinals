import ConstructiveOrdinals.Schutte.ColumnFacts

/-!
# Bachmann's hierarchy, over Brouwer trees with two kinds of branching

Bachmann indexes his hierarchy of normal functions `φ_α` by ordinals `α` that
may exceed `Ω`, and he equips each limit `α` with a fundamental sequence of
length either `ω` or `Ω`. The two cases are treated differently: at a limit of
cofinality `ω` we take common fixpoints, just as in the Veblen hierarchy; but
at a limit of cofinality `Ω` we diagonalize, enumerating those `ξ` which are
fixpoints of the single function `ξ ↦ φ_{α[ξ]}(0)`.

Here we follow the uniform presentation of `Ordinal`: there is no separate
zero/successor/limit case analysis. A node of an index tree carries two kinds
of children:

- a family of "small" children `g : A → BOrd`, indexed by an arbitrary small
  type, which are strict predecessors of the node and are treated by the
  Veblen "intersect" rule; and
- a small-indexed collection of "Ω-families" `h : C → Ordinal → BOrd`, each of
  which is a fundamental sequence of length `Ω`, treated by Bachmann's
  "diagonalize" rule.

Branching over `Ordinal.{u}` plays the role of cofinality `Ω`. Note that `Ω`
need not be "the first uncountable ordinal" here; it is simply the type of
ordinals of the universe below, and its regularity comes from universe
stratification rather than from a choice principle.

Allowing both kinds of children in a single node (rather than having one
constructor for each kind) is what makes index trees closed under binary and
small suprema, and hence under the arithmetic operations, which are defined
just as for `Ordinal`.

Because `BOrd.{u}` branches over `Ordinal.{u}`, it lives in `Type (u+1)`; we
never attempt to embed `BOrd` back into `Ordinal`. The function `bach` is
defined by plain structural recursion.

## Layout of the development

- `Bachmann/Defs`: the trees, `bach`, the order `bsub`, the arithmetic, and the
  general step theorems (this file).
- `Bachmann/Assoc`: associativity of addition up to `φ`, and the invariant
  `BFam`.
- `Bachmann/Power`: `Ω^ζ·ξ` for arbitrary `ζ` as Schütte columns; the
  canonical trees.
- `Bachmann/Calibration`: `φ` against known hierarchies: `Γ₀`, Ackermann, the
  Small and Large Veblen Ordinals.
- `Bachmann/Cfe`: the enumerator of common fixpoints and the hierarchy `bphi`,
  normal by construction.
- `Bachmann/Normal`: `bphi` is normal on the canonical trees.
- `Bachmann/Agree`: Bachmann's `bach` agrees with `bphi` up to `ε_{Ω+1}`;
  certification of the Bachmann–Howard ordinal.
- `Bachmann/Facts`, `Bachmann/Enumeration`: semantic facts used by the
  notation system.
- `Notation/Bachmann/*`: the notation system (see `Notation/Bachmann/Notation`).

Ported from the Rocq file `BachmannDefs.v`.

Lean notes:

- Rocq's `blt` recurses on `match i with inl a => g a | inr (c, ξ) => h c ξ
  end`, which Lean's structural recursion does not accept; here the recursive
  calls sit inside the `match`. `blt_unfold` is still definitional; the
  unfolding of `ble` is `ble_unfold` (an `↔`) with `ble_intro`/`ble_elim`.
- The `Trans` instances and `beq_refl`/`beq_symm`/`beq_trans` below replace
  Rocq's instances. Rocq: `BachmannDefs.ble_preorder`,
  `BachmannDefs.blt_transitive`, `BachmannDefs.beq_equivalence`.
- Rocq's `False` and `unit` index types are `PEmpty` and `PUnit`; `nat` is
  `ULift Nat`.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal

/-- Index trees. Rocq: `BachmannDefs.BOrd`. -/
inductive BOrd : Type (u + 1) where
  | bnode (A : Type u) (g : A → BOrd) (C : Type u) (h : C → Ordinal.{u} → BOrd) : BOrd

open BOrd (bnode)

/-- Rocq: `BachmannDefs.bsmall`. -/
def bsmall : BOrd.{u} → Type u
  | bnode A _ _ _ => A

/-- Rocq: `BachmannDefs.bsmallSz`. -/
def bsmallSz : (x : BOrd.{u}) → bsmall x → BOrd.{u}
  | bnode _ g _ _ => g

/-- Rocq: `BachmannDefs.bbig`. -/
def bbig : BOrd.{u} → Type u
  | bnode _ _ C _ => C

/-- Rocq: `BachmannDefs.bbigSz`. -/
def bbigSz : (x : BOrd.{u}) → bbig x → Ordinal.{u} → BOrd.{u}
  | bnode _ _ _ h => h

/-! ## The ordering on index trees

A node denotes the strict supremum of all of its children, where each member
of an Ω-family counts as a child. The ordering is therefore the same game as
for `Ordinal`, with moves drawn from `A ⊕ C × Ordinal`. This is the ordering
of indices only; it makes no reference to `bach`. The two kinds of children are
distinguished only by how `bach` treats them. -/

/-- Rocq: `BachmannDefs.bidx`. -/
def bidx (x : BOrd.{u}) : Type (u + 1) := bsmall x ⊕ (bbig x × Ordinal.{u})

/-- Rocq: `BachmannDefs.bchild`. -/
def bchild (x : BOrd.{u}) : bidx x → BOrd.{u}
  | .inl a => bsmallSz x a
  | .inr p => bbigSz x p.1 p.2

/-- Rocq: `BachmannDefs.blt`. -/
def blt : BOrd.{u} → BOrd.{u} → Prop
  | bnode A g C h, y => ∃ j : bidx y, ∀ i : A ⊕ (C × Ordinal.{u}),
      match i with
      | .inl a => blt (g a) (bchild y j)
      | .inr p => blt (h p.1 p.2) (bchild y j)

/-- Rocq: `BachmannDefs.ble`. -/
def ble : BOrd.{u} → BOrd.{u} → Prop
  | bnode A g C h, y => ∀ i : A ⊕ (C × Ordinal.{u}),
      match i with
      | .inl a => blt (g a) y
      | .inr p => blt (h p.1 p.2) y

/-- Rocq: `BachmannDefs.beq`. -/
def beq (x y : BOrd.{u}) : Prop := ble x y ∧ ble y x

/-- Rocq: `BachmannDefs.blt_unfold`. -/
theorem blt_unfold (x y : BOrd.{u}) : blt x y = ∃ j : bidx y, ble x (bchild y j) := by
  cases x; rfl

/-- Rocq: `BachmannDefs.ble_unfold`. -/
theorem ble_unfold (x y : BOrd.{u}) : ble x y ↔ ∀ i : bidx x, blt (bchild x i) y := by
  cases x with
  | bnode A g C h =>
  exact ⟨fun H i => match i with
      | .inl a => H (.inl a)
      | .inr p => H (.inr p),
    fun H i => match i with
      | .inl a => H (.inl a)
      | .inr p => H (.inr p)⟩

theorem blt_intro {x y : BOrd.{u}} (j : bidx y) (h : ble x (bchild y j)) : blt x y :=
  (blt_unfold x y).symm ▸ ⟨j, h⟩

theorem blt_elim {x y : BOrd.{u}} (h : blt x y) : ∃ j : bidx y, ble x (bchild y j) :=
  blt_unfold x y ▸ h

theorem ble_intro {x y : BOrd.{u}} (h : ∀ i : bidx x, blt (bchild x i) y) : ble x y :=
  (ble_unfold x y).mpr h

theorem ble_elim {x y : BOrd.{u}} (h : ble x y) (i : bidx x) : blt (bchild x i) y :=
  (ble_unfold x y).mp h i

attribute [irreducible] blt ble

/-- Induction over the children of a node. Rocq: `BachmannDefs.BOrd_child_ind`. -/
theorem BOrd_child_ind {P : BOrd.{u} → Prop} (ind : ∀ x, (∀ i : bidx x, P (bchild x i)) → P x) :
    ∀ x, P x := by
  intro x
  induction x with
  | bnode A g C h ihg ihh =>
  exact ind _ fun i => match i with
    | .inl a => ihg a
    | .inr p => ihh p.1 p.2

/-- Rocq: `BachmannDefs.blt_le`. -/
theorem blt_le : ∀ b a : BOrd.{u}, blt a b → ble a b := by
  intro b
  induction b using BOrd_child_ind with
  | ind b ih =>
  intro a ha
  obtain ⟨j, hj⟩ := blt_elim ha
  exact ble_intro fun i => blt_intro j (ih j _ (ble_elim hj i))

/-- Rocq: `BachmannDefs.ble_refl`. -/
theorem ble_refl : ∀ x : BOrd.{u}, ble x x := by
  intro x
  induction x using BOrd_child_ind with
  | ind x ih => exact ble_intro fun i => blt_intro i (ih i)

/-- Rocq: `BachmannDefs.bindex_lt`. -/
theorem bindex_lt (x : BOrd.{u}) (i : bidx x) : blt (bchild x i) x := blt_intro i (ble_refl _)

/-- Rocq: `BachmannDefs.bindex_le`. -/
theorem bindex_le (x : BOrd.{u}) (i : bidx x) : ble (bchild x i) x := blt_le _ _ (bindex_lt x i)

/-- Rocq: `BachmannDefs.ble_trans`. -/
theorem ble_trans : ∀ {a b c : BOrd.{u}}, ble a b → ble b c → ble a c := by
  intro a
  induction a using BOrd_child_ind with
  | ind a ih =>
  intro b c hab hbc
  refine ble_intro fun ai => ?_
  obtain ⟨bi, h1⟩ := blt_elim (ble_elim hab ai)
  obtain ⟨ci, h2⟩ := blt_elim (ble_elim hbc bi)
  exact blt_intro ci (ih ai h1 h2)

/-- Rocq: `BachmannDefs.ble_lt_trans`. -/
theorem ble_lt_trans {a b c : BOrd.{u}} (hab : ble a b) (hbc : blt b c) : blt a c :=
  let ⟨ci, h⟩ := blt_elim hbc
  blt_intro ci (ble_trans hab h)

/-- Rocq: `BachmannDefs.blt_le_trans`. -/
theorem blt_le_trans {a b c : BOrd.{u}} (hab : blt a b) (hbc : ble b c) : blt a c :=
  let ⟨bi, h⟩ := blt_elim hab
  ble_lt_trans h (ble_elim hbc bi)

/-- Rocq: `BachmannDefs.blt_trans`. -/
theorem blt_trans {a b c : BOrd.{u}} (hab : blt a b) (hbc : blt b c) : blt a c :=
  blt_le_trans hab (blt_le _ _ hbc)

/-- Rocq: `BachmannDefs.blt_acc`. -/
theorem blt_acc : ∀ x y : BOrd.{u}, ble y x → Acc blt y := by
  intro x
  induction x using BOrd_child_ind with
  | ind x ih =>
  intro z hz
  refine Acc.intro _ fun y hy => ?_
  obtain ⟨i, hi⟩ := blt_elim (blt_le_trans hy hz)
  exact ih i y hi

/-- Rocq: `BachmannDefs.blt_wf`. -/
theorem blt_wf : WellFounded (blt : BOrd.{u} → BOrd.{u} → Prop) := ⟨fun a => blt_acc a a (ble_refl a)⟩

/-- Rocq: `BachmannDefs.blt_irreflexive`. -/
theorem blt_irreflexive (x : BOrd.{u}) : ¬ blt x x :=
  blt_wf.induction (C := fun x => ¬ blt x x) x fun x ih h => ih x h h

instance : @Trans BOrd.{u} BOrd.{u} BOrd.{u} ble ble ble := ⟨ble_trans⟩
instance : @Trans BOrd.{u} BOrd.{u} BOrd.{u} blt blt blt := ⟨blt_trans⟩
instance : @Trans BOrd.{u} BOrd.{u} BOrd.{u} ble blt blt := ⟨ble_lt_trans⟩
instance : @Trans BOrd.{u} BOrd.{u} BOrd.{u} blt ble blt := ⟨blt_le_trans⟩

theorem beq_refl (x : BOrd.{u}) : beq x x := ⟨ble_refl x, ble_refl x⟩

theorem beq_symm {x y : BOrd.{u}} (h : beq x y) : beq y x := ⟨h.2, h.1⟩

theorem beq_trans {x y z : BOrd.{u}} (h₁ : beq x y) (h₂ : beq y z) : beq x z :=
  ⟨ble_trans h₁.1 h₂.1, ble_trans h₂.2 h₁.2⟩

/-! ## The hierarchy -/

section bachmann

variable (f : Ordinal.{u} → Ordinal.{u})

/-- The inner recursion of `bach`, on the argument; `outerG` and `outerH` are
the recursive calls on the small children and on the Ω-families. -/
def bachInner {A C : Type u} (outerG : A → Ordinal.{u} → Ordinal.{u})
    (outerH : C → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk X k =>
    f (mk X k) ⊔ (sup fun a => fixOrd (outerG a) (mk X fun x => bachInner outerG outerH (k x))) ⊔
      sup fun c => fixOrd (fun ξ => outerH c ξ 0) (mk X fun x => bachInner outerG outerH (k x))

/-- Bachmann's hierarchy over `f`. Rocq: `BachmannDefs.bach`. -/
def bach : BOrd.{u} → Ordinal.{u} → Ordinal.{u}
  | bnode _ g _ h => bachInner f (fun a => bach (g a)) (fun c ξ => bach (h c ξ))

/-- Rocq: `BachmannDefs.bach_unroll`. -/
theorem bach_unroll (A : Type u) (g : A → BOrd.{u}) (C : Type u) (h : C → Ordinal.{u} → BOrd.{u})
    (y : Ordinal.{u}) :
    bach f (bnode A g C h) y =
      f y ⊔ (sup fun a => fixOrd (bach f (g a)) (lim fun x : y => bach f (bnode A g C h) (y x))) ⊔
        sup fun c => fixOrd (fun ξ => bach f (h c ξ) 0) (lim fun x : y => bach f (bnode A g C h) (y x)) := by
  cases y; rfl

/-- The first slice of the "canonical tree" invariant: along every Ω-family,
the diagonal `ξ ↦ φ_{α[ξ]}(0)` is monotone. This fails for arbitrary trees,
since `φ` is not monotone in its index. Rocq: `BachmannDefs.bmono`. -/
def BMono : BOrd.{u} → Prop
  | bnode _ g _ h =>
    (∀ a, BMono (g a)) ∧ (∀ c ξ, BMono (h c ξ)) ∧
      ∀ c ξ ξ', ξ ≤ ξ' → bach f (h c ξ) 0 ≤ bach f (h c ξ') 0

variable {f}

/-- Rocq: `BachmannDefs.bach_monotone`. -/
theorem bach_monotone (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ β : BOrd.{u}, BMono f β → ∀ y z, y ≤ z → bach f β y ≤ bach f β z
  | bnode A g C h, ⟨hm1, _, hm3⟩ => by
    intro y z
    induction z generalizing y with
    | mk Z k ihz =>
    intro hyz
    cases y with
    | mk Y m =>
    have hstart : lim (fun i : Y => bach f (bnode A g C h) (m i)) ≤
        lim (fun j : Z => bach f (bnode A g C h) (k j)) :=
      limit_least fun i =>
        let ⟨j, hj⟩ := le_subord hyz i
        lt_of_le_of_lt (ihz j (m i) hj) (limit_lt (fun j : Z => bach f (bnode A g C h) (k j)) j)
    rw [bach_unroll f A g C h (mk Y m), bach_unroll f A g C h (mk Z k)]
    exact lub_monotone (hf _ _ hyz) (lub_monotone
      (sup_monotone fun a => fixOrd_monotone (bach_monotone hf (g a) (hm1 a)) hstart)
      (sup_monotone fun c => fixOrd_monotone (fun x y h => hm3 c x y h) hstart))

end bachmann

attribute [irreducible] bach

/-! ## Index tree constructions -/

/-- Rocq: `BachmannDefs.bzero`. -/
def bzero : BOrd.{u} := bnode PEmpty PEmpty.elim PEmpty PEmpty.elim

/-- Rocq: `BachmannDefs.bsucc`. -/
def bsucc (x : BOrd.{u}) : BOrd.{u} := bnode PUnit (fun _ => x) PEmpty PEmpty.elim

/-- Rocq: `BachmannDefs.blub`. -/
def blub : BOrd.{u} → BOrd.{u} → BOrd.{u}
  | bnode A g C h, bnode B g' D h' =>
    bnode (A ⊕ B) (fun ab => match ab with
        | .inl a => g a
        | .inr b => g' b)
      (C ⊕ D) (fun cd => match cd with
        | .inl c => h c
        | .inr d => h' d)

/-- Rocq: `BachmannDefs.bsup`. -/
def bsup {I : Type u} (F : I → BOrd.{u}) : BOrd.{u} :=
  bnode (Σ i, bsmall (F i)) (fun p => bsmallSz (F p.1) p.2) (Σ i, bbig (F i)) (fun p => bbigSz (F p.1) p.2)

/-- A single Ω-family as a node. Rocq: `BachmannDefs.blimΩ`. -/
def blimΩ (g : Ordinal.{u} → BOrd.{u}) : BOrd.{u} := bnode PEmpty PEmpty.elim PUnit (fun _ => g)

/-- Ordinary ordinals embed as trees with only small branching. Rocq: `BachmannDefs.embed`. -/
def embed : Ordinal.{u} → BOrd.{u}
  | mk A g => bnode A (fun a => embed (g a)) PEmpty PEmpty.elim

/-- `Ω` is the node with a single Ω-family, `Ω[ξ] = ξ`. Rocq: `BachmannDefs.bOmega`. -/
def bOmega : BOrd.{u} := blimΩ embed

/-- The arithmetic operations follow addition, multiplication and
exponentiation of ordinals, with the additional rule that an Ω-family of the
right operand is mapped pointwise. This is where Bachmann's canonical
fundamental sequences come from: e.g., `(β + Ω)[ξ] = β + ξ`, `(β·Ω)[ξ] = β·ξ`
and `Ω^(β+1)[ξ] = Ω^β·ξ` arise from the definitions rather than being
stipulated. Rocq: `BachmannDefs.badd`. -/
def badd (x : BOrd.{u}) : BOrd.{u} → BOrd.{u}
  | bnode B g D h => blub x (bnode B (fun b => badd x (g b)) D (fun d ξ => badd x (h d ξ)))

/-- Rocq: `BachmannDefs.bmul`. -/
def bmul (x : BOrd.{u}) : BOrd.{u} → BOrd.{u}
  | bnode _ g D h =>
    blub (bsup fun b => badd (bmul x (g b)) x) (bnode PEmpty PEmpty.elim D fun d ξ => bmul x (h d ξ))

/-- Rocq: `BachmannDefs.bexpΩ`. -/
def bexpΩ : BOrd.{u} → BOrd.{u}
  | bnode _ g D h =>
    blub (bsucc bzero)
      (blub (bsup fun b => bmul (bexpΩ (g b)) bOmega) (bnode PEmpty PEmpty.elim D fun d ξ => bexpΩ (h d ξ)))

-- The canonical fundamental sequences hold by computation (Rocq examples `badd_Ω_fs`, `bmul_Ω_fs`,
-- `bexpΩ_succ_fs`).
example (A : Type u) (g : A → BOrd.{u}) (C : Type u) (h : C → Ordinal.{u} → BOrd.{u}) (ξ : Ordinal.{u}) :
    bbigSz (badd (bnode A g C h) bOmega) (.inr ⟨⟩) ξ = badd (bnode A g C h) (embed ξ) := rfl

example (x : BOrd.{u}) (ξ : Ordinal.{u}) : bbigSz (bmul x bOmega) (.inr ⟨⟩) ξ = bmul x (embed ξ) := by
  cases x; rfl

example (y : BOrd.{u}) (ξ : Ordinal.{u}) :
    bbigSz (bexpΩ (bsucc y)) (.inr (.inl ⟨⟨⟩, .inr ⟨⟩⟩)) ξ = bmul (bexpΩ y) (embed ξ) := rfl

/-- `ε_{Ω+1}`, with fundamental sequence `Ω+1, Ω^(Ω+1), Ω^Ω^(Ω+1), …`.
Rocq: `BachmannDefs.btower`. -/
def btower : Nat → BOrd.{u}
  | 0 => bsucc bOmega
  | n + 1 => bexpΩ (btower n)

/-- Rocq: `BachmannDefs.bεΩ1`. -/
def bεΩ1 : BOrd.{u} := bnode (ULift Nat) (fun n => btower n.down) PEmpty PEmpty.elim

/-- The Bachmann–Howard ordinal. Rocq: `BachmannDefs.BHO`. -/
def BHO : Ordinal.{u} := bach powOmega bεΩ1 0

/-! ## The constructions, with respect to the index ordering -/

/-- Rocq: `BachmannDefs.bzero_least`. -/
theorem bzero_least (x : BOrd.{u}) : ble bzero x :=
  ble_intro fun i => match i with
    | .inl e => nomatch e
    | .inr p => nomatch p.1

/-- Rocq: `BachmannDefs.bsucc_lt`. -/
theorem bsucc_lt (x : BOrd.{u}) : blt x (bsucc x) := bindex_lt (bsucc x) (.inl ⟨⟩)

/-- Rocq: `BachmannDefs.bsucc_least`. -/
theorem bsucc_least (x y : BOrd.{u}) (H : blt x y) : ble (bsucc x) y :=
  ble_intro fun i => match i with
    | .inl _ => H
    | .inr p => nomatch p.1

/-- Rocq: `BachmannDefs.blub_le1`. -/
theorem blub_le1 (x y : BOrd.{u}) : ble x (blub x y) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  exact ble_intro fun i => match i with
    | .inl a => blt_intro (.inl (.inl a)) (ble_refl _)
    | .inr p => blt_intro (.inr (.inl p.1, p.2)) (ble_refl _)

/-- Rocq: `BachmannDefs.blub_le2`. -/
theorem blub_le2 (x y : BOrd.{u}) : ble y (blub x y) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  exact ble_intro fun i => match i with
    | .inl b => blt_intro (.inl (.inr b)) (ble_refl _)
    | .inr p => blt_intro (.inr (.inr p.1, p.2)) (ble_refl _)

/-- Rocq: `BachmannDefs.blub_least`. -/
theorem blub_least (x y z : BOrd.{u}) (hx : ble x z) (hy : ble y z) : ble (blub x y) z := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  exact ble_intro fun i => match i with
    | .inl (.inl a) => ble_elim hx (.inl a)
    | .inl (.inr b) => ble_elim hy (.inl b)
    | .inr (.inl c, ξ) => ble_elim hx (.inr (c, ξ))
    | .inr (.inr d, ξ) => ble_elim hy (.inr (d, ξ))

/-- Rocq: `BachmannDefs.bsup_le`. -/
theorem bsup_le {I : Type u} (F : I → BOrd.{u}) (i : I) : ble (F i) (bsup F) :=
  ble_intro fun k => match k with
    | .inl a => blt_intro (x := bchild (F i) (.inl a)) (.inl ⟨i, a⟩) (ble_refl _)
    | .inr p => blt_intro (x := bchild (F i) (.inr p)) (.inr (⟨i, p.1⟩, p.2)) (ble_refl _)

/-- Rocq: `BachmannDefs.bsup_least`. -/
theorem bsup_least {I : Type u} (F : I → BOrd.{u}) (z : BOrd.{u}) (H : ∀ i, ble (F i) z) : ble (bsup F) z :=
  ble_intro fun k => match k with
    | .inl ⟨i, a⟩ => ble_elim (H i) (.inl a)
    | .inr (⟨i, c⟩, ξ) => ble_elim (H i) (.inr (c, ξ))

/-- `embed` is an order embedding. Rocq: `BachmannDefs.embed_order`. -/
theorem embed_order : ∀ x y : Ordinal.{u},
    (x ≤ y ↔ ble (embed x) (embed y)) ∧ (x < y ↔ blt (embed x) (embed y)) := by
  intro x
  induction x with
  | mk A f ih =>
  have Hle : ∀ y, mk A f ≤ y ↔ ble (embed (mk A f)) (embed y) := fun y =>
    ⟨fun H => ble_intro fun i => match i with
        | .inl a => ((ih a y).2.1 (le_elim H a))
        | .inr p => (nomatch p.1),
      fun H => le_intro fun a => (ih a y).2.2 (ble_elim H (.inl a))⟩
  intro y
  refine ⟨Hle y, ?_⟩
  cases y with
  | mk B g =>
  exact ⟨fun H => let ⟨b, hb⟩ := lt_elim H; blt_intro (.inl b) ((Hle (g b)).1 hb),
    fun H => let ⟨j, hj⟩ := blt_elim H
      match j, hj with
      | .inl b, hj => lt_intro b ((Hle (g b)).2 hj)
      | .inr p, _ => nomatch p.1⟩

/-- Rocq: `BachmannDefs.embed_le`. -/
theorem embed_le (x y : Ordinal.{u}) : x ≤ y ↔ ble (embed x) (embed y) := (embed_order x y).1

/-- Rocq: `BachmannDefs.embed_lt`. -/
theorem embed_lt (x y : Ordinal.{u}) : x < y ↔ blt (embed x) (embed y) := (embed_order x y).2

/-- `Ω` lies strictly above every embedded ordinal. Rocq: `BachmannDefs.embed_lt_Ω`. -/
theorem embed_lt_Ω (ξ : Ordinal.{u}) : blt (embed ξ) bOmega := bindex_lt bOmega (.inr (⟨⟩, ξ))

/-- Rocq: `BachmannDefs.Ω_not_le_embed`. -/
theorem Ω_not_le_embed (ξ : Ordinal.{u}) : ¬ ble bOmega (embed ξ) := fun H =>
  blt_irreflexive (embed ξ) (blt_le_trans (embed_lt_Ω ξ) H)

/-- `Ω` is the least index above every embedded ordinal. Rocq: `BachmannDefs.Ω_least`. -/
theorem Ω_least (z : BOrd.{u}) (H : ∀ ξ, blt (embed ξ) z) : ble bOmega z :=
  ble_intro fun i => match i with
    | .inl e => nomatch e
    | .inr (_, ξ) => H ξ

/-- Rocq: `BachmannDefs.badd_le_l`. -/
theorem badd_le_l (x y : BOrd.{u}) : ble x (badd x y) := by
  cases y; exact blub_le1 _ _

/-- Rocq: `BachmannDefs.badd_zero`. -/
theorem badd_zero (x : BOrd.{u}) : beq (badd x bzero) x :=
  ⟨blub_least _ _ _ (ble_refl x) (ble_intro fun i => match i with
      | .inl e => nomatch e
      | .inr p => nomatch p.1),
    badd_le_l _ _⟩

/-! ## Monotonicity of the arithmetic

Addition is monotone in both arguments, and strictly monotone in its right
argument, for arbitrary index trees. Multiplication and exponentiation are
more delicate, because they map Ω-families pointwise while treating small
children as successor steps. This is only sensible if every Ω-family behaves
like a fundamental sequence, i.e., has no largest member. For example, if `y'`
has a single Ω-family that is constant at `t`, then `y'` denotes `t+1` but
`bmul x y'` denotes only `x·t + 1`, which is below `bmul x (bsucc t)` whenever
`x > 1`. We therefore introduce the hereditary invariant `BUnb` stating that
every Ω-family is unbounded in itself. -/

/-- Rocq: `BachmannDefs.blub_le_iff`. -/
theorem blub_le_iff (x y z : BOrd.{u}) : ble (blub x y) z ↔ ble x z ∧ ble y z :=
  ⟨fun H => ⟨ble_trans (blub_le1 x y) H, ble_trans (blub_le2 x y) H⟩, fun H => blub_least _ _ _ H.1 H.2⟩

/-- Rocq: `BachmannDefs.bsup_le_iff`. -/
theorem bsup_le_iff {I : Type u} (F : I → BOrd.{u}) (z : BOrd.{u}) : ble (bsup F) z ↔ ∀ i, ble (F i) z :=
  ⟨fun H i => ble_trans (bsup_le F i) H, bsup_least F z⟩

/-- Rocq: `BachmannDefs.bsucc_le_iff`. -/
theorem bsucc_le_iff (x z : BOrd.{u}) : ble (bsucc x) z ↔ blt x z :=
  ⟨fun H => blt_le_trans (bsucc_lt x) H, bsucc_least x z⟩

/-! ### Addition -/

/-- Rocq: `BachmannDefs.baddR`. -/
def baddR (x y : BOrd.{u}) : BOrd.{u} :=
  bnode (bsmall y) (fun b => badd x (bsmallSz y b)) (bbig y) (fun d ξ => badd x (bbigSz y d ξ))

/-- Rocq: `BachmannDefs.badd_eq`. -/
theorem badd_eq (x y : BOrd.{u}) : badd x y = blub x (baddR x y) := by
  cases y; rfl

/-- Rocq: `BachmannDefs.baddR_child`. -/
theorem baddR_child (x y : BOrd.{u}) (i : bidx (baddR x y)) :
    bchild (baddR x y) i = badd x (bchild y i) := by
  cases i <;> rfl

/-- Rocq: `BachmannDefs.badd_le_iff`. -/
theorem badd_le_iff (x y z : BOrd.{u}) :
    ble (badd x y) z ↔ ble x z ∧ ∀ i : bidx y, blt (badd x (bchild y i)) z := by
  rw [badd_eq x y]
  refine ⟨fun H => ?_, fun H => ?_⟩
  · obtain ⟨h1, h2⟩ := (blub_le_iff _ _ _).mp H
    exact ⟨h1, fun i => by have := ble_elim h2 i; cases i <;> exact this⟩
  · exact blub_least _ _ _ H.1 (ble_intro fun i => by have := H.2 i; cases i <;> exact this)

/-- Rocq: `BachmannDefs.badd_child_lt`. -/
theorem badd_child_lt (x y : BOrd.{u}) (i : bidx y) : blt (badd x (bchild y i)) (badd x y) := by
  rw [badd_eq x y]
  have := bindex_lt (baddR x y) i
  exact blt_le_trans (by cases i <;> exact this) (blub_le2 _ _)

/-- Rocq: `BachmannDefs.badd_mono_r`. -/
theorem badd_mono_r (x : BOrd.{u}) : ∀ y y', ble y y' → ble (badd x y) (badd x y') := by
  intro y
  induction y using BOrd_child_ind with
  | ind y ih =>
  intro y' H
  refine (badd_le_iff _ _ _).mpr ⟨badd_le_l _ _, fun i => ?_⟩
  obtain ⟨j, hj⟩ := blt_elim (ble_elim H i)
  exact ble_lt_trans (ih i _ hj) (badd_child_lt _ _ _)

/-- Rocq: `BachmannDefs.badd_lt_r`. -/
theorem badd_lt_r (x y y' : BOrd.{u}) (H : blt y y') : blt (badd x y) (badd x y') :=
  let ⟨_, hj⟩ := blt_elim H
  ble_lt_trans (badd_mono_r x _ _ hj) (badd_child_lt _ _ _)

/-- Rocq: `BachmannDefs.badd_mono_l`. -/
theorem badd_mono_l (y : BOrd.{u}) : ∀ x x', ble x x' → ble (badd x y) (badd x' y) := by
  induction y using BOrd_child_ind with
  | ind y ih =>
  intro x x' H
  exact (badd_le_iff _ _ _).mpr ⟨ble_trans H (badd_le_l _ _), fun i =>
    ble_lt_trans (ih i x x' H) (badd_child_lt _ _ _)⟩

/-- Rocq: `BachmannDefs.badd_le_r`. -/
theorem badd_le_r (x : BOrd.{u}) : ∀ y : BOrd.{u}, ble y (badd x y) := by
  intro y
  induction y using BOrd_child_ind with
  | ind y ih => exact ble_intro fun i => ble_lt_trans (ih i) (badd_child_lt _ _ _)

/-- Rocq: `BachmannDefs.badd_lt_pos`. -/
theorem badd_lt_pos (z x : BOrd.{u}) (H : blt bzero x) : blt z (badd z x) :=
  let ⟨j, _⟩ := blt_elim H
  ble_lt_trans (badd_le_l _ _) (badd_child_lt z x j)

/-! ### Multiplication -/

/-- Rocq: `BachmannDefs.bmulS`. -/
def bmulS (x y : BOrd.{u}) : BOrd.{u} := bsup fun a : bsmall y => badd (bmul x (bsmallSz y a)) x

/-- Rocq: `BachmannDefs.bmulB`. -/
def bmulB (x y : BOrd.{u}) : BOrd.{u} :=
  bnode PEmpty PEmpty.elim (bbig y) (fun d ξ => bmul x (bbigSz y d ξ))

/-- Rocq: `BachmannDefs.bmul_eq`. -/
theorem bmul_eq (x y : BOrd.{u}) : bmul x y = blub (bmulS x y) (bmulB x y) := by
  cases y; rfl

/-- Rocq: `BachmannDefs.bmul_le_iff`. -/
theorem bmul_le_iff (x y z : BOrd.{u}) :
    ble (bmul x y) z ↔
      (∀ a, ble (badd (bmul x (bsmallSz y a)) x) z) ∧ (∀ d ξ, blt (bmul x (bbigSz y d ξ)) z) := by
  rw [bmul_eq x y]
  refine ⟨fun H => ?_, fun H => ?_⟩
  · obtain ⟨h1, h2⟩ := (blub_le_iff _ _ _).mp H
    exact ⟨(bsup_le_iff _ _).mp h1, fun d ξ => ble_elim h2 (.inr (d, ξ))⟩
  · refine blub_least _ _ _ ((bsup_le_iff _ _).mpr H.1) (ble_intro fun i => ?_)
    match i with
    | .inl e => exact nomatch e
    | .inr (d, ξ) => exact H.2 d ξ

/-- Rocq: `BachmannDefs.bmul_small_le`. -/
theorem bmul_small_le (x y : BOrd.{u}) (a : bsmall y) : ble (badd (bmul x (bsmallSz y a)) x) (bmul x y) := by
  rw [bmul_eq x y]
  exact ble_trans (bsup_le (fun a0 => badd (bmul x (bsmallSz y a0)) x) a) (blub_le1 _ _)

/-- Rocq: `BachmannDefs.bmul_big_lt`. -/
theorem bmul_big_lt (x y : BOrd.{u}) (d : bbig y) (ξ : Ordinal.{u}) : blt (bmul x (bbigSz y d ξ)) (bmul x y) := by
  rw [bmul_eq x y]
  exact blt_le_trans (bindex_lt (bmulB x y) (.inr (d, ξ))) (blub_le2 _ _)

/-- Rocq: `BachmannDefs.bmul_mono_l`. -/
theorem bmul_mono_l (y : BOrd.{u}) : ∀ x x', ble x x' → ble (bmul x y) (bmul x' y) := by
  induction y using BOrd_child_ind with
  | ind y ih =>
  intro x x' H
  refine (bmul_le_iff _ _ _).mpr ⟨fun a => ?_, fun d ξ => ?_⟩
  · exact ble_trans (ble_trans (badd_mono_l _ _ _ (ih (.inl a) x x' H)) (badd_mono_r _ _ _ H))
      (bmul_small_le _ _ _)
  · exact ble_lt_trans (ih (.inr (d, ξ)) x x' H) (bmul_big_lt _ _ _ _)

/-- Every Ω-family is unbounded in itself, hereditarily. Rocq: `BachmannDefs.bunb`. -/
def BUnb : BOrd.{u} → Prop
  | bnode _ g _ h => (∀ a, BUnb (g a)) ∧ (∀ c ξ, BUnb (h c ξ)) ∧ ∀ c ξ, ∃ ξ', blt (h c ξ) (h c ξ')

/-- Rocq: `BachmannDefs.bunb_child`. -/
theorem bunb_child (x : BOrd.{u}) (i : bidx x) (H : BUnb x) : BUnb (bchild x i) := by
  cases x with
  | bnode A g C h =>
  match i with
  | .inl a => exact H.1 a
  | .inr p => exact H.2.1 p.1 p.2

/-- Rocq: `BachmannDefs.bunb_fam`. -/
theorem bunb_fam (x : BOrd.{u}) (d : bbig x) (ξ : Ordinal.{u}) (H : BUnb x) :
    ∃ ξ', blt (bbigSz x d ξ) (bbigSz x d ξ') := by
  cases x with
  | bnode A g C h => exact H.2.2 d ξ

/-- Rocq: `BachmannDefs.bmul_mono_aux`. -/
theorem bmul_mono_aux (x : BOrd.{u}) (hx : blt bzero x) : ∀ t' : BOrd.{u}, BUnb t' → ∀ t,
    (blt t t' → ble (badd (bmul x t) x) (bmul x t')) ∧ (ble t t' → ble (bmul x t) (bmul x t')) := by
  intro t'
  induction t' using BOrd_child_ind with
  | ind t' ih =>
  intro hu
  have HK : ∀ t, blt t t' → ble (badd (bmul x t) x) (bmul x t') := fun t ht => by
    obtain ⟨j, hj⟩ := blt_elim ht
    match j, hj with
    | .inl a, hj =>
      exact ble_trans (badd_mono_l _ _ _ ((ih (.inl a) (bunb_child t' (.inl a) hu) t).2 hj)) (bmul_small_le x t' a)
    | .inr (d, ζ), hj =>
      obtain ⟨ζ', hζ⟩ := bunb_fam t' d ζ hu
      have ht' : blt t (bbigSz t' d ζ') := ble_lt_trans hj hζ
      exact ble_trans ((ih (.inr (d, ζ')) (bunb_child t' (.inr (d, ζ')) hu) t).1 ht')
        (blt_le _ _ (bmul_big_lt _ _ _ _))
  refine fun t => ⟨HK t, fun ht => (bmul_le_iff _ _ _).mpr ⟨fun a => HK _ (ble_elim ht (.inl a)), fun d ξ => ?_⟩⟩
  exact blt_le_trans (badd_lt_pos _ _ hx) (HK _ (ble_elim ht (.inr (d, ξ))))

/-- Rocq: `BachmannDefs.bmul_mono_r`. -/
theorem bmul_mono_r (x y y' : BOrd.{u}) (hx : blt bzero x) (hu : BUnb y') (H : ble y y') :
    ble (bmul x y) (bmul x y') :=
  (bmul_mono_aux x hx y' hu y).2 H

/-- Rocq: `BachmannDefs.bmul_lt_r`. -/
theorem bmul_lt_r (x y y' : BOrd.{u}) (hx : blt bzero x) (hu : BUnb y') (H : blt y y') :
    blt (bmul x y) (bmul x y') :=
  blt_le_trans (badd_lt_pos _ _ hx) ((bmul_mono_aux x hx y' hu y).1 H)

/-- `z < z·Ω`, without any hypotheses: `z ≤ z·1 < z·Ω`. Rocq: `BachmannDefs.bmul_Ω_gt`. -/
theorem bmul_Ω_gt (z : BOrd.{u}) : blt z (bmul z bOmega) :=
  ble_lt_trans (ble_trans (badd_le_r _ _) (bmul_small_le z (embed (succ 0)) ⟨⟩))
    (bmul_big_lt z bOmega ⟨⟩ (succ 0))

/-! ### Exponentiation -/

/-- Rocq: `BachmannDefs.bexpS`. -/
def bexpS (y : BOrd.{u}) : BOrd.{u} := bsup fun a : bsmall y => bmul (bexpΩ (bsmallSz y a)) bOmega

/-- Rocq: `BachmannDefs.bexpB`. -/
def bexpB (y : BOrd.{u}) : BOrd.{u} := bnode PEmpty PEmpty.elim (bbig y) (fun d ξ => bexpΩ (bbigSz y d ξ))

/-- Rocq: `BachmannDefs.bexpΩ_eq`. -/
theorem bexpΩ_eq (y : BOrd.{u}) : bexpΩ y = blub (bsucc bzero) (blub (bexpS y) (bexpB y)) := by
  cases y; rfl

/-- Rocq: `BachmannDefs.bexpΩ_le_iff`. -/
theorem bexpΩ_le_iff (y z : BOrd.{u}) :
    ble (bexpΩ y) z ↔
      blt bzero z ∧ (∀ a, ble (bmul (bexpΩ (bsmallSz y a)) bOmega) z) ∧ (∀ d ξ, blt (bexpΩ (bbigSz y d ξ)) z) := by
  rw [bexpΩ_eq y]
  refine ⟨fun H => ?_, fun H => ?_⟩
  · obtain ⟨h0, h12⟩ := (blub_le_iff _ _ _).mp H
    obtain ⟨h1, h2⟩ := (blub_le_iff _ _ _).mp h12
    exact ⟨(bsucc_le_iff _ _).mp h0, (bsup_le_iff _ _).mp h1, fun d ξ => ble_elim h2 (.inr (d, ξ))⟩
  · refine blub_least _ _ _ ((bsucc_le_iff _ _).mpr H.1)
      (blub_least _ _ _ ((bsup_le_iff _ _).mpr H.2.1) (ble_intro fun i => ?_))
    match i with
    | .inl e => exact nomatch e
    | .inr (d, ξ) => exact H.2.2 d ξ

/-- Rocq: `BachmannDefs.bexpΩ_pos`. -/
theorem bexpΩ_pos (y : BOrd.{u}) : blt bzero (bexpΩ y) := by
  rw [bexpΩ_eq y]
  exact blt_le_trans (bsucc_lt _) (blub_le1 _ _)

/-- Rocq: `BachmannDefs.bexpΩ_small_le`. -/
theorem bexpΩ_small_le (y : BOrd.{u}) (a : bsmall y) : ble (bmul (bexpΩ (bsmallSz y a)) bOmega) (bexpΩ y) := by
  rw [bexpΩ_eq y]
  exact ble_trans (ble_trans (bsup_le (fun a0 => bmul (bexpΩ (bsmallSz y a0)) bOmega) a) (blub_le1 _ _))
    (blub_le2 _ _)

/-- Rocq: `BachmannDefs.bexpΩ_big_lt`. -/
theorem bexpΩ_big_lt (y : BOrd.{u}) (d : bbig y) (ξ : Ordinal.{u}) : blt (bexpΩ (bbigSz y d ξ)) (bexpΩ y) := by
  rw [bexpΩ_eq y]
  exact blt_le_trans (blt_le_trans (bindex_lt (bexpB y) (.inr (d, ξ))) (blub_le2 _ _)) (blub_le2 _ _)

/-- Rocq: `BachmannDefs.bexpΩ_mono_aux`. -/
theorem bexpΩ_mono_aux : ∀ t' : BOrd.{u}, BUnb t' → ∀ t,
    (blt t t' → ble (bmul (bexpΩ t) bOmega) (bexpΩ t')) ∧ (ble t t' → ble (bexpΩ t) (bexpΩ t')) := by
  intro t'
  induction t' using BOrd_child_ind with
  | ind t' ih =>
  intro hu
  have HK : ∀ t, blt t t' → ble (bmul (bexpΩ t) bOmega) (bexpΩ t') := fun t ht => by
    obtain ⟨j, hj⟩ := blt_elim ht
    match j, hj with
    | .inl a, hj =>
      exact ble_trans (bmul_mono_l _ _ _ ((ih (.inl a) (bunb_child t' (.inl a) hu) t).2 hj)) (bexpΩ_small_le t' a)
    | .inr (d, ζ), hj =>
      obtain ⟨ζ', hζ⟩ := bunb_fam t' d ζ hu
      have ht' : blt t (bbigSz t' d ζ') := ble_lt_trans hj hζ
      exact ble_trans ((ih (.inr (d, ζ')) (bunb_child t' (.inr (d, ζ')) hu) t).1 ht')
        (blt_le _ _ (bexpΩ_big_lt _ _ _))
  refine fun t => ⟨HK t, fun ht => (bexpΩ_le_iff _ _).mpr ⟨bexpΩ_pos _, fun a => HK _ (ble_elim ht (.inl a)),
    fun d ξ => ?_⟩⟩
  exact blt_le_trans (bmul_Ω_gt _) (HK _ (ble_elim ht (.inr (d, ξ))))

/-- Rocq: `BachmannDefs.bexpΩ_mono`. -/
theorem bexpΩ_mono (y y' : BOrd.{u}) (hu : BUnb y') (H : ble y y') : ble (bexpΩ y) (bexpΩ y') :=
  (bexpΩ_mono_aux y' hu y).2 H

/-- Rocq: `BachmannDefs.bexpΩ_lt`. -/
theorem bexpΩ_lt (y y' : BOrd.{u}) (hu : BUnb y') (H : blt y y') : blt (bexpΩ y) (bexpΩ y') :=
  blt_le_trans (bmul_Ω_gt _) ((bexpΩ_mono_aux y' hu y).1 H)

/-! ### The invariant is satisfied by the canonical trees -/

/-- Rocq: `BachmannDefs.bunb_blub`. -/
theorem bunb_blub (x y : BOrd.{u}) (hx : BUnb x) (hy : BUnb y) : BUnb (blub x y) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  obtain ⟨H1, H2, H3⟩ := hx
  obtain ⟨H1', H2', H3'⟩ := hy
  refine ⟨fun ab => ?_, fun cd ξ => ?_, fun cd ξ => ?_⟩
  · match ab with
    | .inl a => exact H1 a
    | .inr b => exact H1' b
  · match cd with
    | .inl c => exact H2 c ξ
    | .inr d => exact H2' d ξ
  · match cd with
    | .inl c => exact H3 c ξ
    | .inr d => exact H3' d ξ

/-- Rocq: `BachmannDefs.bunb_bsup`. -/
theorem bunb_bsup {I : Type u} (F : I → BOrd.{u}) (H : ∀ i, BUnb (F i)) : BUnb (bsup F) :=
  ⟨fun p => bunb_child (F p.1) (.inl p.2) (H p.1), fun p ξ => bunb_child (F p.1) (.inr (p.2, ξ)) (H p.1),
    fun p ξ => bunb_fam (F p.1) p.2 ξ (H p.1)⟩

/-- Rocq: `BachmannDefs.bunb_bzero`. -/
theorem bunb_bzero : BUnb bzero.{u} :=
  ⟨fun e => (nomatch e), fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bunb_bsucc`. -/
theorem bunb_bsucc (x : BOrd.{u}) (H : BUnb x) : BUnb (bsucc x) :=
  ⟨fun _ => H, fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bunb_embed`. -/
theorem bunb_embed : ∀ ξ : Ordinal.{u}, BUnb (embed ξ)
  | mk _ f => ⟨fun a => bunb_embed (f a), fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bunb_Ω`. -/
theorem bunb_Ω : BUnb bOmega.{u} :=
  ⟨fun e => (nomatch e), fun _ ξ => bunb_embed ξ, fun _ ξ => ⟨succ ξ, (embed_lt _ _).mp (succ_lt ξ)⟩⟩

/-- Rocq: `BachmannDefs.bunb_badd`. -/
theorem bunb_badd (x y : BOrd.{u}) (hx : BUnb x) : BUnb y → BUnb (badd x y) := by
  induction y using BOrd_child_ind with
  | ind y ih =>
  intro hy
  rw [badd_eq x y]
  refine bunb_blub _ _ hx ⟨fun a => ih (.inl a) (bunb_child y (.inl a) hy),
    fun d ξ => ih (.inr (d, ξ)) (bunb_child y (.inr (d, ξ)) hy), fun d ξ => ?_⟩
  obtain ⟨ξ', hξ⟩ := bunb_fam y d ξ hy
  exact ⟨ξ', badd_lt_r _ _ _ hξ⟩

/-- Rocq: `BachmannDefs.bunb_bmul`. -/
theorem bunb_bmul (x y : BOrd.{u}) (hx0 : blt bzero x) (hx : BUnb x) : BUnb y → BUnb (bmul x y) := by
  induction y using BOrd_child_ind with
  | ind y ih =>
  intro hy
  rw [bmul_eq x y]
  refine bunb_blub _ _ (bunb_bsup _ fun a => bunb_badd _ _ (ih (.inl a) (bunb_child y (.inl a) hy)) hx)
    ⟨fun e => (nomatch e), fun d ξ => ih (.inr (d, ξ)) (bunb_child y (.inr (d, ξ)) hy), fun d ξ => ?_⟩
  obtain ⟨ξ', hξ⟩ := bunb_fam y d ξ hy
  exact ⟨ξ', bmul_lt_r _ _ _ hx0 (bunb_child y (.inr (d, ξ')) hy) hξ⟩

/-- Rocq: `BachmannDefs.bunb_bexpΩ`. -/
theorem bunb_bexpΩ (y : BOrd.{u}) : BUnb y → BUnb (bexpΩ y) := by
  induction y using BOrd_child_ind with
  | ind y ih =>
  intro hy
  rw [bexpΩ_eq y]
  refine bunb_blub _ _ (bunb_bsucc _ bunb_bzero) (bunb_blub _ _ (bunb_bsup _ fun a =>
    bunb_bmul _ _ (bexpΩ_pos _) (ih (.inl a) (bunb_child y (.inl a) hy)) bunb_Ω)
    ⟨fun e => (nomatch e), fun d ξ => ih (.inr (d, ξ)) (bunb_child y (.inr (d, ξ)) hy), fun d ξ => ?_⟩)
  obtain ⟨ξ', hξ⟩ := bunb_fam y d ξ hy
  exact ⟨ξ', bexpΩ_lt _ _ (bunb_child y (.inr (d, ξ')) hy) hξ⟩

/-- Rocq: `BachmannDefs.bunb_btower`. -/
theorem bunb_btower : ∀ n : Nat, BUnb (btower.{u} n)
  | 0 => bunb_bsucc _ bunb_Ω
  | n + 1 => bunb_bexpΩ _ (bunb_btower n)

/-- Rocq: `BachmannDefs.bunb_bεΩ1`. -/
theorem bunb_bεΩ1 : BUnb bεΩ1.{u} :=
  ⟨fun n => bunb_btower n.down, fun e => (nomatch e), fun e => nomatch e⟩

/-! ## Auxiliary facts about limits and fixpoints -/

/-- Rocq: `BachmannDefs.lim_eq_mor`. -/
theorem lim_eq_mor (A : Type u) (F G : A → Ordinal.{u}) (H : ∀ a, F a ≈ G a) : lim F ≈ lim G := lim_congr H

/-- Rocq: `BachmannDefs.lim_le_mor`. -/
theorem lim_le_mor (A : Type u) (F G : A → Ordinal.{u}) (H : ∀ a, F a ≤ G a) : lim F ≤ lim G := lim_monotone H

/-- Rocq: `BachmannDefs.lub_sup_False`. -/
theorem lub_sup_False (z : Ordinal.{u}) (F : PEmpty.{u + 1} → Ordinal.{u}) : z ⊔ sup F ≈ z :=
  equiv_intro (lub_least (le_refl _) (sup_least fun e => nomatch e)) (lub_le1 _ _)

/-- Rocq: `BachmannDefs.fixOrd_eq_func`. -/
theorem fixOrd_eq_func (F G : Ordinal.{u} → Ordinal.{u}) (a b : Ordinal.{u}) (HFG : ∀ x, F x ≈ G x)
    (HG : ∀ x y, x ≤ y → G x ≤ G y) (Hab : a ≈ b) : fixOrd F a ≈ fixOrd G b := by
  have Hiter : ∀ n, iterF F a n ≈ iterF G b n := by
    intro n
    induction n with
    | zero => exact Hab
    | succ n ih => exact equiv_trans (HFG _) (equiv_intro (HG _ _ ih.le) (HG _ _ ih.ge))
  exact sup_congr fun n => Hiter n.down

/-- Rocq: `BachmannDefs.fixOrd_eq_func_complete`. -/
theorem fixOrd_eq_func_complete (F G : Ordinal.{u} → Ordinal.{u}) (a b : Ordinal.{u})
    (HFG : ∀ x, Complete x → F x ≈ G x) (HF : ∀ x y, x ≤ y → F x ≤ F y) (HG : ∀ x y, x ≤ y → G x ≤ G y)
    (HGc : ∀ x, Complete x → Complete (G x)) (Hab : a ≈ b) (Hb : Complete b) : fixOrd F a ≈ fixOrd G b := by
  have _ := HG
  have Hiter : ∀ n, iterF F a n ≈ iterF G b n ∧ Complete (iterF G b n) := by
    intro n
    induction n with
    | zero => exact ⟨Hab, Hb⟩
    | succ n ih =>
      exact ⟨equiv_trans (equiv_intro (HF _ _ ih.1.le) (HF _ _ ih.1.ge)) (HFG _ ih.2), HGc _ ih.2⟩
  exact sup_congr fun n => (Hiter n.down).1

/-- Rocq: `BachmannDefs.bach_unroll'`. -/
theorem bach_unroll' (f : Ordinal.{u} → Ordinal.{u}) (x : BOrd.{u}) (y : Ordinal.{u}) :
    bach f x y =
      f y ⊔ (sup fun a : bsmall x => fixOrd (bach f (bsmallSz x a)) (lim fun j : y => bach f x (y j))) ⊔
        sup fun c : bbig x => fixOrd (fun ξ => bach f (bbigSz x c ξ) 0) (lim fun j : y => bach f x (y j)) := by
  cases x; exact bach_unroll f _ _ _ _ y

/-! ## Agreement with the Veblen hierarchy below `Ω` -/

/-- Rocq: `BachmannDefs.bach_embed`. -/
theorem bach_embed (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ β y : Ordinal.{u}, bach f (embed β) y ≈ veblen f β y := by
  intro β
  induction β with
  | mk A g ihβ =>
  intro y
  induction y with
  | mk Y k ihy =>
  show bach f (bnode A (fun a => embed (g a)) PEmpty PEmpty.elim) (mk Y k) ≈ _
  rw [bach_unroll, veblen_unroll]
  refine lub_congr (equiv_refl _) (equiv_trans (lub_sup_False _ _) (sup_congr fun a => ?_))
  exact fixOrd_eq_func _ _ _ _ (fun x => ihβ a x) (veblen_monotone hf _) (lim_eq_mor _ _ _ fun i => ihy i)

/-- Rocq: `BachmannDefs.bmono_embed`. -/
theorem bmono_embed (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ β : Ordinal.{u}, BMono f (embed β)
  | mk _ g => ⟨fun a => bmono_embed f hf (g a), fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bmono_Ω`. -/
theorem bmono_Ω (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) : BMono f bOmega :=
  ⟨fun e => (nomatch e), fun _ ξ => bmono_embed f hf ξ, fun _ ξ ξ' h =>
    le_trans (bach_embed f hf ξ 0).le (le_trans (veblen_monotone_first hf ξ' ξ 0 h) (bach_embed f hf ξ' 0).ge)⟩

/-- Rocq: `BachmannDefs.bmono_blub`. -/
theorem bmono_blub (f : Ordinal.{u} → Ordinal.{u}) (x y : BOrd.{u}) (hx : BMono f x) (hy : BMono f y) :
    BMono f (blub x y) := by
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

/-- Rocq: `BachmannDefs.bmono_badd_embed`. -/
theorem bmono_badd_embed (f : Ordinal.{u} → Ordinal.{u}) (α : BOrd.{u}) (hα : BMono f α) :
    ∀ ξ : Ordinal.{u}, BMono f (badd α (embed ξ))
  | mk X k => by
    rw [badd_eq α (embed (mk X k))]
    exact bmono_blub f _ _ hα ⟨fun b => bmono_badd_embed f α hα (k b), fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bach_embed0_mono`. -/
theorem bach_embed0_mono (x y : Ordinal.{u}) (H : x ≤ y) : bach powOmega (embed x) 0 ≤ bach powOmega (embed y) 0 :=
  le_trans (bach_embed _ (fun _ _ h => powOmega_monotone h) x 0).le
    (le_trans (veblen_monotone_first (fun _ _ h => powOmega_monotone h) y x 0 H)
      (bach_embed _ (fun _ _ h => powOmega_monotone h) y 0).ge)

/-! ## Monotonicity in the index, for the family-respecting order

`φ` is not monotone with respect to the index ordering `ble`: `Γ₀+1 < Ω`, but
`φ_{Γ₀+1}(0) > Γ₀ = φ_Ω(0)`. It is, however, monotone with respect to the
following stricter, structural order, which matches small children to small
children and Ω-families to Ω-families *pointwise*, at the same argument `ξ`.
This is the order under which Bachmann's fundamental sequences are "compared
as sequences". -/

/-- Rocq: `BachmannDefs.bsub`. -/
def bsub : BOrd.{u} → BOrd.{u} → Prop
  | bnode _ g _ h, bnode _ g' _ h' =>
    (∀ a, ∃ b, bsub (g a) (g' b)) ∧ (∀ c, ∃ d, ∀ ξ, bsub (h c ξ) (h' d ξ))

/-- Rocq: `BachmannDefs.bsub_refl`. -/
theorem bsub_refl : ∀ x : BOrd.{u}, bsub x x
  | bnode _ g _ h => ⟨fun a => ⟨a, bsub_refl (g a)⟩, fun c => ⟨c, fun ξ => bsub_refl (h c ξ)⟩⟩

/-- Rocq: `BachmannDefs.bsub_blub_l`. -/
theorem bsub_blub_l (x y : BOrd.{u}) : bsub x (blub x y) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  exact ⟨fun a => ⟨.inl a, bsub_refl _⟩, fun c => ⟨.inl c, fun _ => bsub_refl _⟩⟩

/-- Rocq: `BachmannDefs.bsub_blub_empty`. -/
theorem bsub_blub_empty (x y : BOrd.{u}) (HB : bsmall y → False) (HD : bbig y → False) : bsub (blub x y) x := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  refine ⟨fun ab => ?_, fun cd => ?_⟩
  · match ab with
    | .inl a => exact ⟨a, bsub_refl _⟩
    | .inr b => exact (HB b).elim
  · match cd with
    | .inl c => exact ⟨c, fun _ => bsub_refl _⟩
    | .inr d => exact (HD d).elim

/-- Rocq: `BachmannDefs.bach_mono_index`. -/
theorem bach_mono_index (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ x y : BOrd.{u}, bsub x y → BMono f y → ∀ z, bach f x z ≤ bach f y z
  | bnode A g C h, bnode B g' D h', ⟨hs1, hs2⟩, hy => by
    have hy' := hy
    obtain ⟨hm1, _, hm3⟩ := hy'
    intro z
    induction z with
    | mk Z k ihz =>
    have hstart : lim (fun j : Z => bach f (bnode A g C h) (k j)) ≤
        lim (fun j : Z => bach f (bnode B g' D h') (k j)) :=
      lim_le_mor _ _ _ fun j => ihz j
    rw [bach_unroll f A g C h (mk Z k), bach_unroll f B g' D h' (mk Z k)]
    refine lub_least (lub_le1 _ _) (le_trans ?_ (lub_le2 _ _))
    refine lub_least (sup_least fun a => ?_) (sup_least fun c => ?_)
    · obtain ⟨b, hb⟩ := hs1 a
      refine le_trans ?_ (le_trans (sup_le (fun b0 => fixOrd (bach f (g' b0))
        (lim fun j : Z => bach f (bnode B g' D h') (k j))) b) (lub_le1 _ _))
      exact le_trans (fixOrd_monotone_func (fun x => bach_mono_index f hf (g a) (g' b) hb (hm1 b) x)
          (bach_monotone hf _ (hm1 b)) _)
        (fixOrd_monotone (bach_monotone hf _ (hm1 b)) hstart)
    · obtain ⟨d, hd⟩ := hs2 c
      refine le_trans ?_ (le_trans (sup_le (fun d0 => fixOrd (fun ξ => bach f (h' d0 ξ) 0)
        (lim fun j : Z => bach f (bnode B g' D h') (k j))) d) (lub_le2 _ _))
      exact le_trans (fixOrd_monotone_func (fun ξ => bach_mono_index f hf (h c ξ) (h' d ξ) (hd ξ)
            (hy.2.1 d ξ) 0) (hm3 d) _)
        (fixOrd_monotone (hm3 d) hstart)

/-- Rocq: `BachmannDefs.bach_le_badd_embed`. -/
theorem bach_le_badd_embed (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α : BOrd.{u})
    (ξ : Ordinal.{u}) (hα : BMono f α) (y : Ordinal.{u}) : bach f α y ≤ bach f (badd α (embed ξ)) y := by
  refine bach_mono_index f hf _ _ ?_ (bmono_badd_embed f α hα ξ) y
  rw [badd_eq α (embed ξ)]
  exact bsub_blub_l _ _

/-! ## General step theorems

A node's value is `f y` joined with, for each of its components, the least
fixpoint above a common starting point of the function that component
contributes: `bach` of a small child, or the diagonal of an Ω-family. The
invariant `BRep f T G` records that `bach f T` agrees with a normal function
`G` on complete arguments, and that every component of `T` fixes the values of
`G`. The step theorems below propagate this invariant through the canonical
constructions. -/

/-- Rocq: `BachmannDefs.bcomp`. -/
def bcomp (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) : bsmall T ⊕ bbig T → Ordinal.{u} → Ordinal.{u}
  | .inl a => bach f (bsmallSz T a)
  | .inr c => fun ξ => bach f (bbigSz T c ξ) 0

/-- Rocq: `BachmannDefs.bach_comp_le`. -/
theorem bach_comp_le (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) (y : Ordinal.{u}) (k : bsmall T ⊕ bbig T) :
    fixOrd (bcomp f T k) (lim fun j : y => bach f T (y j)) ≤ bach f T y := by
  rw [bach_unroll' f T y]
  refine le_trans ?_ (lub_le2 _ _)
  match k with
  | .inl a =>
    exact le_trans (sup_le (fun a0 => fixOrd (bach f (bsmallSz T a0)) (lim fun j : y => bach f T (y j))) a)
      (lub_le1 _ _)
  | .inr c =>
    exact le_trans (sup_le (fun c0 => fixOrd (fun ξ => bach f (bbigSz T c0 ξ) 0)
      (lim fun j : y => bach f T (y j))) c) (lub_le2 _ _)

/-- Rocq: `BachmannDefs.bach_le_comp`. -/
theorem bach_le_comp (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) (y z : Ordinal.{u}) (H1 : f y ≤ z)
    (H2 : ∀ k, fixOrd (bcomp f T k) (lim fun j : y => bach f T (y j)) ≤ z) : bach f T y ≤ z := by
  rw [bach_unroll' f T y]
  exact lub_least H1 (lub_least (sup_least fun a => H2 (.inl a)) (sup_least fun c => H2 (.inr c)))

/-- Rocq: `BachmannDefs.f_le_bach`. -/
theorem f_le_bach (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) (y : Ordinal.{u}) : f y ≤ bach f T y := by
  rw [bach_unroll' f T y]
  exact lub_le1 _ _

/-- Rocq: `BachmannDefs.bmono_bcomp`. -/
theorem bmono_bcomp (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (T : BOrd.{u})
    (HT : BMono f T) : ∀ k x y, x ≤ y → bcomp f T k x ≤ bcomp f T k y := by
  cases T with
  | bnode A g C h =>
  intro k x y hxy
  match k with
  | .inl a => exact bach_monotone hf _ (HT.1 a) _ _ hxy
  | .inr c => exact HT.2.2 c x y hxy

/-- Rocq: `BachmannDefs.BRep`. -/
def BRep (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) (G : Ordinal.{u} → Ordinal.{u}) : Prop :=
  NormalFunction G ∧ (∀ y, Complete y → bach f T y ≈ G y) ∧ ∀ k y, Complete y → bcomp f T k (G y) ≤ G y

/-! ### The enumeration step

If one distinguished component agrees with a normal `G`, and every component
fixes the values of `enumFixpoints G`, then the node enumerates the fixpoints
of `G`. The successor and Ω-limit steps are instances. -/

/-- Rocq: `BachmannDefs.bach_enum_step`. -/
theorem bach_enum_step (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) (G : Ordinal.{u} → Ordinal.{u})
    (k0 : bsmall T ⊕ bbig T) (HG : NormalFunction G)
    (Hmono : ∀ k x y, x ≤ y → bcomp f T k x ≤ bcomp f T k y)
    (H0 : ∀ x, Complete x → bcomp f T k0 x ≈ G x) (Hf : ∀ x, Complete x → f x ≤ G x)
    (Hcl : ∀ k y, Complete y → bcomp f T k (enumFixpoints G y) ≤ enumFixpoints G y) :
    BRep f T (enumFixpoints G) := by
  have HE := enum_fixpoints_normal HG
  refine ⟨HE, ?_, Hcl⟩
  intro y
  induction y with
  | mk Y h ihy =>
  intro hyc
  have hhc : ∀ j, Complete (h j) := fun j => complete_subord hyc j
  have hs : lim (fun j : Y => bach f T (h j)) ≈ lim (fun j : Y => enumFixpoints G (h j)) :=
    lim_eq_mor _ _ _ fun j => ihy j (hhc j)
  have hsc : Complete (lim fun j : Y => enumFixpoints G (h j)) := lim_normal_complete (mk Y h) _ HE hyc
  refine equiv_intro ?_ ?_
  · refine bach_le_comp f T _ _ ?_ fun k => ?_
    · exact le_trans (Hf _ hyc) (le_trans (HG.monotone _ _ (normal_inflationary HE _ hyc))
        (Con.enum_are_fixpoints HG (mk Y h) hyc).ge)
    · refine fixOrd_least (Hmono k) _ _ (le_trans hs.le ?_) (Hcl k _ hyc)
      exact limit_least fun j => enumFixpoints_increasing HG.monotone (index_lt (mk Y h) j)
  · refine le_trans ?_ (bach_comp_le f T (mk Y h) k0)
    show fixOrd G (lim fun j : Y => enumFixpoints G (h j)) ≤ fixOrd (bcomp f T k0) (lim fun j : Y => bach f T (h j))
    exact (fixOrd_eq_func_complete (bcomp f T k0) G _ _ H0 (Hmono k0) HG.monotone HG.complete hs hsc).ge

/-! ### The Ω-limit step -/

/-- Rocq: `BachmannDefs.bach_Ωlim_step`. -/
theorem bach_Ωlim_step (f : Ordinal.{u} → Ordinal.{u}) (H : Ordinal.{u} → BOrd.{u}) (G : Ordinal.{u} → Ordinal.{u})
    (HG : NormalFunction G) (Hmono : ∀ ξ ξ', ξ ≤ ξ' → bach f (H ξ) 0 ≤ bach f (H ξ') 0)
    (HD : ∀ x, Complete x → bach f (H x) 0 ≈ G x) (Hf : ∀ x, Complete x → f x ≤ G x) :
    BRep f (blimΩ H) (enumFixpoints G) := by
  refine bach_enum_step f (blimΩ H) G (.inr ⟨⟩) HG ?_ (fun x hx => HD x hx) Hf ?_
  · intro k x y hxy
    match k with
    | .inl e => exact nomatch e
    | .inr _ => exact Hmono x y hxy
  · intro k y hy
    match k with
    | .inl e => exact nomatch e
    | .inr _ =>
      have hv : Complete (enumFixpoints G y) := (enum_fixpoints_normal HG).complete y hy
      exact le_trans (HD _ hv).le (Con.enum_are_fixpoints HG y hy).ge

/-! ### The successor step, for the canonical successor `α+1` -/

/-- Rocq: `BachmannDefs.bmono_badd_zero`. -/
theorem bmono_badd_zero (f : Ordinal.{u} → Ordinal.{u}) (α : BOrd.{u}) (H : BMono f α) : BMono f (badd α bzero) := by
  rw [badd_eq α bzero]
  exact bmono_blub f _ _ H ⟨fun e => (nomatch e), fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bmono_badd_one`. -/
theorem bmono_badd_one (f : Ordinal.{u} → Ordinal.{u}) (α : BOrd.{u}) (H : BMono f α) :
    BMono f (badd α (bsucc bzero)) := by
  rw [badd_eq α (bsucc bzero)]
  exact bmono_blub f _ _ H ⟨fun _ => bmono_badd_zero f α H, fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bach_badd_zero`. -/
theorem bach_badd_zero (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α : BOrd.{u})
    (hα : BMono f α) (y : Ordinal.{u}) : bach f (badd α bzero) y ≈ bach f α y := by
  refine equiv_intro (bach_mono_index f hf _ _ ?_ hα y) (bach_mono_index f hf _ _ ?_ (bmono_badd_zero f α hα) y)
  · rw [badd_eq α bzero]
    exact bsub_blub_empty _ _ (fun e => nomatch e) (fun e => nomatch e)
  · rw [badd_eq α bzero]
    exact bsub_blub_l _ _

/-- Rocq: `BachmannDefs.bach_succ_step`. -/
theorem bach_succ_step (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α : BOrd.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (hα : BMono f α) (HR : BRep f α G) :
    BRep f (badd α (bsucc bzero)) (enumFixpoints G) := by
  obtain ⟨HG, Hrep, Hcl⟩ := HR
  have Hα0 := bach_badd_zero f hf α hα
  have HT := bmono_badd_one f α hα
  cases α with
  | bnode A g C h =>
  refine bach_enum_step f (badd (bnode A g C h) (bsucc bzero)) G (.inl (.inr ⟨⟩)) HG (bmono_bcomp f hf _ HT)
    (fun x hx => equiv_trans (Hα0 x) (Hrep x hx))
    (fun x hx => le_trans (f_le_bach f _ x) (Hrep x hx).le) ?_
  intro k y hy
  have hv : Complete (enumFixpoints G y) := (enum_fixpoints_normal HG).complete y hy
  have hfix := Con.enum_are_fixpoints HG y hy
  match k with
  | .inl (.inl a) =>
    show bach f (g a) (enumFixpoints G y) ≤ enumFixpoints G y
    exact le_trans (bach_monotone hf _ (hα.1 a) _ _ hfix.le) (le_trans (Hcl (.inl a) _ hv) hfix.ge)
  | .inl (.inr _) =>
    show bach f (badd (bnode A g C h) bzero) (enumFixpoints G y) ≤ enumFixpoints G y
    exact le_trans (Hα0 _).le (le_trans (Hrep _ hv).le hfix.ge)
  | .inr (.inl c) =>
    show bach f (h c (enumFixpoints G y)) 0 ≤ enumFixpoints G y
    exact le_trans (hα.2.2 c _ _ hfix.le) (le_trans (Hcl (.inr c) _ hv) hfix.ge)
  | .inr (.inr e) => exact nomatch e

/-! ### The Veblen step

Adding an ordinary ordinal `ξ` to an index `α` builds the Veblen hierarchy
over `φ_α`: `φ_{α+ξ} = veblen φ_α ξ`. This single statement covers zero,
successor and (small) limit `ξ` uniformly, just as `veblen` does. The
components inherited from `α` fix every value of `veblen G ξ`, because such a
value is either a value of `G` (when `ξ` has no children) or a fixpoint of `G`
(when it does); completeness of `ξ` makes this case split constructive. -/

/-- Rocq: `BachmannDefs.veblen_value_cases`. -/
theorem veblen_value_cases (G : Ordinal.{u} → Ordinal.{u}) (HG : NormalFunction G) (ξ y : Ordinal.{u})
    (hξ : Complete ξ) (hy : Complete y) : veblen G ξ y ≈ G y ∨ veblen G ξ y ≈ G (veblen G ξ y) := by
  cases ξ with
  | mk X k =>
  have hξ' : Complete (mk X k) := hξ
  obtain ⟨_, hne, _⟩ := hξ
  match hne with
  | .inl ⟨x0⟩ =>
    refine .inr (equiv_intro (normal_inflationary HG _ (veblen_complete HG HG.complete _ hξ' y hy)) ?_)
    exact veblen_fixpoint_zero HG (lt_intro x0 (zero_least _)) hξ' hy
  | .inr hn =>
    refine .inl ?_
    rw [veblen_unroll]
    exact equiv_intro (lub_least (le_refl _) (sup_least fun i => (hn ⟨i⟩).elim)) (lub_le1 _ _)

/-- Rocq: `BachmannDefs.veblen_comp_closure`. -/
theorem veblen_comp_closure (f : Ordinal.{u} → Ordinal.{u}) (α : BOrd.{u}) (G : Ordinal.{u} → Ordinal.{u})
    (HR : BRep f α G) (Hmono : ∀ k x y, x ≤ y → bcomp f α k x ≤ bcomp f α k y) (ξ y : Ordinal.{u})
    (hξ : Complete ξ) (hy : Complete y) (k : bsmall α ⊕ bbig α) : bcomp f α k (veblen G ξ y) ≤ veblen G ξ y := by
  obtain ⟨HG, _, Hcl⟩ := HR
  have hvc : Complete (veblen G ξ y) := veblen_complete HG HG.complete _ hξ y hy
  match veblen_value_cases G HG ξ y hξ hy with
  | .inl H => exact le_trans (Hmono _ _ _ H.le) (le_trans (Hcl k y hy) H.ge)
  | .inr H => exact le_trans (Hmono _ _ _ H.le) (le_trans (Hcl k _ hvc) H.ge)

/-- Rocq: `BachmannDefs.bach_veblen_step`. -/
theorem bach_veblen_step (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α : BOrd.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (hα : BMono f α) (HR : BRep f α G) :
    ∀ ξ, Complete ξ → BRep f (badd α (embed ξ)) (veblen G ξ) := by
  have HR' := HR
  obtain ⟨HG, Hrep, _⟩ := HR'
  have hmα := bmono_bcomp f hf α hα
  cases α with
  | bnode A g C h =>
  intro ξ
  induction ξ with
  | mk X k ihk =>
  intro hξ
  have hkc : ∀ i, Complete (k i) := fun i => complete_subord hξ i
  have HT : BMono f (badd (bnode A g C h) (embed (mk X k))) := bmono_badd_embed f _ hα _
  have HV : NormalFunction (veblen G (mk X k)) := veblen_normal HG _ hξ
  have Hcomp : ∀ kk y, Complete y →
      bcomp f (badd (bnode A g C h) (embed (mk X k))) kk (veblen G (mk X k) y) ≤ veblen G (mk X k) y := by
    intro kk y hy
    have hvc : Complete (veblen G (mk X k) y) := HV.complete y hy
    match kk with
    | .inl (.inl a) =>
      show bcomp f (bnode A g C h) (.inl a) (veblen G (mk X k) y) ≤ veblen G (mk X k) y
      exact veblen_comp_closure f _ G HR hmα _ y hξ hy _
    | .inl (.inr i) =>
      show bach f (badd (bnode A g C h) (embed (k i))) (veblen G (mk X k) y) ≤ veblen G (mk X k) y
      exact le_trans ((ihk i (hkc i)).2.1 _ hvc).le
        (veblen_fixpoints HG (k i) (mk X k) y (hkc i) hξ hy (index_lt (mk X k) i)).le
    | .inr (.inl c) =>
      show bcomp f (bnode A g C h) (.inr c) (veblen G (mk X k) y) ≤ veblen G (mk X k) y
      exact veblen_comp_closure f _ G HR hmα _ y hξ hy _
    | .inr (.inr e) => exact nomatch e
  refine ⟨HV, ?_, Hcomp⟩
  intro y
  induction y with
  | mk Y hh ihy =>
  intro hyc
  have hhc : ∀ j, Complete (hh j) := fun j => complete_subord hyc j
  have hs : lim (fun j : Y => bach f (badd (bnode A g C h) (embed (mk X k))) (hh j)) ≈
      lim (fun j : Y => veblen G (mk X k) (hh j)) :=
    lim_eq_mor _ _ _ fun j => ihy j (hhc j)
  have hsc : Complete (lim fun j : Y => veblen G (mk X k) (hh j)) := lim_normal_complete (mk Y hh) _ HV hyc
  refine equiv_intro ?_ ?_
  · refine bach_le_comp f _ _ _ ?_ fun kk => ?_
    · refine le_trans (f_le_bach f (bnode A g C h) _) (le_trans (Hrep _ hyc).le ?_)
      rw [veblen_unroll]
      exact lub_le1 _ _
    · refine fixOrd_least (bmono_bcomp f hf _ HT kk) _ _ (le_trans hs.le ?_) (Hcomp kk _ hyc)
      exact limit_least fun j => veblen_increasing HG _ hξ _ _ hyc (index_lt (mk Y hh) j)
  · rw [veblen_unroll G (mk X k) (mk Y hh)]
    refine lub_least (le_trans (Hrep _ hyc).ge (bach_le_badd_embed f hf _ _ hα _)) (sup_least fun i => ?_)
    refine le_trans ?_ (bach_comp_le f (badd (bnode A g C h) (embed (mk X k))) (mk Y hh) (.inl (.inr i)))
    have HVi : NormalFunction (veblen G (k i)) := veblen_normal HG _ (hkc i)
    exact (fixOrd_eq_func_complete (bcomp f (badd (bnode A g C h) (embed (mk X k))) (.inl (.inr i)))
      (veblen G (k i)) _ _ (ihk i (hkc i)).2.1 (bmono_bcomp f hf _ HT (.inl (.inr i))) HVi.monotone HVi.complete
      hs hsc).ge

/-! ### The +Ω step

Adding `Ω` to an index `α` diagonalizes the Veblen hierarchy over `φ_α`: the
new Ω-family is `ξ ↦ α+ξ`, whose diagonal is `ξ ↦ φ_{α+ξ}(0) = veblen G ξ 0` by
the Veblen step. So `φ_{α+Ω}` enumerates the fixpoints of that diagonal,
generalizing `Γ` (the case `α = 0`). -/

/-- Rocq: `BachmannDefs.bsub_badd_embed`. -/
theorem bsub_badd_embed (α : BOrd.{u}) : ∀ ξ ξ' : Ordinal.{u}, ξ ≤ ξ' → bsub (badd α (embed ξ)) (badd α (embed ξ')) := by
  cases α with
  | bnode A g C h =>
  intro ξ
  induction ξ with
  | mk X k ihk =>
  intro ξ' H
  cases ξ' with
  | mk X' k' =>
  rw [badd_eq _ (embed (mk X k)), badd_eq _ (embed (mk X' k'))]
  refine ⟨fun ai => ?_, fun cd => ?_⟩
  · match ai with
    | .inl a => exact ⟨.inl a, bsub_refl _⟩
    | .inr i =>
      obtain ⟨j, hj⟩ := le_subord H i
      exact ⟨.inr j, ihk i (k' j) hj⟩
  · match cd with
    | .inl c => exact ⟨.inl c, fun _ => bsub_refl _⟩
    | .inr e => exact nomatch e

/-- Rocq: `BachmannDefs.badd_embed_diag_mono`. -/
theorem badd_embed_diag_mono (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α : BOrd.{u})
    (hα : BMono f α) (ξ ξ' : Ordinal.{u}) (H : ξ ≤ ξ') :
    bach f (badd α (embed ξ)) 0 ≤ bach f (badd α (embed ξ')) 0 :=
  bach_mono_index f hf _ _ (bsub_badd_embed α ξ ξ' H) (bmono_badd_embed f α hα ξ') 0

/-- Rocq: `BachmannDefs.bmono_badd_Ω`. -/
theorem bmono_badd_Ω (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α : BOrd.{u})
    (hα : BMono f α) : BMono f (badd α bOmega) := by
  rw [badd_eq α bOmega]
  exact bmono_blub f _ _ hα ⟨fun e => (nomatch e), fun _ ξ => bmono_badd_embed f α hα ξ,
    fun _ ξ ξ' H => badd_embed_diag_mono f hf α hα ξ ξ' H⟩

/-- Rocq: `BachmannDefs.bach_plusΩ_step`. -/
theorem bach_plusΩ_step (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (α : BOrd.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (hα : BMono f α) (HR : BRep f α G) :
    BRep f (badd α bOmega) (enumFixpoints fun ξ => veblen G ξ 0) := by
  have HR' := HR
  obtain ⟨HG, Hrep, _⟩ := HR'
  have HN : NormalFunction fun ξ => veblen G ξ 0 := veblen_first_normal HG
  have HT := bmono_badd_Ω f hf α hα
  have hmα := bmono_bcomp f hf α hα
  have Hplus : ∀ ξ, Complete ξ → BRep f (badd α (embed ξ)) (veblen G ξ) := bach_veblen_step f hf α G hα HR
  have Hcα := veblen_comp_closure f α G HR hmα
  cases α with
  | bnode A g C h =>
  refine bach_enum_step f (badd (bnode A g C h) bOmega) _ (.inr (.inr ⟨⟩)) HN (bmono_bcomp f hf _ HT) ?_ ?_ ?_
  · intro x hx
    show bach f (badd (bnode A g C h) (embed x)) 0 ≈ veblen G x 0
    exact (Hplus x hx).2.1 0 zero_complete
  · intro x hx
    refine le_trans (le_trans (f_le_bach f (bnode A g C h) x) (Hrep x hx).le) ?_
    exact le_trans (HG.monotone _ _ (add_zero x).ge) (veblen_fax HG x 0 hx zero_complete)
  · intro kk y hy
    have hv : Complete (enumFixpoints (fun ξ => veblen G ξ 0) y) := (enum_fixpoints_normal HN).complete y hy
    have hfix := Con.enum_are_fixpoints HN y hy
    match kk with
    | .inl (.inl a) =>
      show bcomp f (bnode A g C h) (.inl a) (enumFixpoints (fun ξ => veblen G ξ 0) y) ≤ _
      exact le_trans (hmα _ _ _ hfix.le) (le_trans (Hcα _ 0 hv zero_complete _) hfix.ge)
    | .inl (.inr e) => exact nomatch e
    | .inr (.inl c) =>
      show bcomp f (bnode A g C h) (.inr c) (enumFixpoints (fun ξ => veblen G ξ 0) y) ≤ _
      exact le_trans (hmα _ _ _ hfix.le) (le_trans (Hcα _ 0 hv zero_complete _) hfix.ge)
    | .inr (.inr _) =>
      show bach f (badd (bnode A g C h) (embed (enumFixpoints (fun ξ => veblen G ξ 0) y))) 0 ≤ _
      exact le_trans ((Hplus _ hv).2.1 0 zero_complete).le hfix.ge

/-! ### The base case: `φ_0 = f` -/

/-- Rocq: `BachmannDefs.bach_bzero`. -/
theorem bach_bzero (f : Ordinal.{u} → Ordinal.{u}) (y : Ordinal.{u}) : bach f bzero y ≈ f y := by
  rw [bach_unroll']
  exact equiv_intro (lub_least (le_refl _) (lub_least (sup_least fun e => nomatch e) (sup_least fun e => nomatch e)))
    (lub_le1 _ _)

/-- Rocq: `BachmannDefs.bmono_bzero`. -/
theorem bmono_bzero (f : Ordinal.{u} → Ordinal.{u}) : BMono f bzero :=
  ⟨fun e => (nomatch e), fun e => (nomatch e), fun e => nomatch e⟩

/-- Rocq: `BachmannDefs.bach_zero_rep`. -/
theorem bach_zero_rep (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) : BRep f bzero f :=
  ⟨hf, fun y _ => bach_bzero f y, fun k => match k with
    | .inl e => nomatch e
    | .inr e => nomatch e⟩

/-! ## Inversion and monotonicity of `bsub` for the constructions -/

/-- Rocq: `BachmannDefs.bsub_small`. -/
theorem bsub_small (x y : BOrd.{u}) (H : bsub x y) : ∀ a, ∃ b, bsub (bsmallSz x a) (bsmallSz y b) := by
  cases x; cases y; exact H.1

/-- Rocq: `BachmannDefs.bsub_big`. -/
theorem bsub_big (x y : BOrd.{u}) (H : bsub x y) : ∀ c, ∃ d, ∀ ξ, bsub (bbigSz x c ξ) (bbigSz y d ξ) := by
  cases x; cases y; exact H.2

/-- Rocq: `BachmannDefs.bsub_bsup`. -/
theorem bsub_bsup {I J : Type u} (F : I → BOrd.{u}) (F' : J → BOrd.{u}) (H : ∀ i, ∃ j, bsub (F i) (F' j)) :
    bsub (bsup F) (bsup F') :=
  ⟨fun p => let ⟨j, hj⟩ := H p.1; let ⟨b, hb⟩ := bsub_small _ _ hj p.2; ⟨⟨j, b⟩, hb⟩,
   fun p => let ⟨j, hj⟩ := H p.1; let ⟨d, hd⟩ := bsub_big _ _ hj p.2; ⟨⟨j, d⟩, hd⟩⟩

/-- Rocq: `BachmannDefs.bsub_blub`. -/
theorem bsub_blub (x x' y y' : BOrd.{u}) (hx : bsub x x') (hy : bsub y y') : bsub (blub x y) (blub x' y') := by
  cases x with
  | bnode A g C h =>
  cases x' with
  | bnode A' g' C' h' =>
  cases y with
  | bnode B k D l =>
  cases y' with
  | bnode B' k' D' l' =>
  obtain ⟨Hx1, Hx2⟩ := hx
  obtain ⟨Hy1, Hy2⟩ := hy
  refine ⟨fun ab => ?_, fun cd => ?_⟩
  · match ab with
    | .inl a => let ⟨a', ha⟩ := Hx1 a; exact ⟨.inl a', ha⟩
    | .inr b => let ⟨b', hb⟩ := Hy1 b; exact ⟨.inr b', hb⟩
  · match cd with
    | .inl c => let ⟨c', hc⟩ := Hx2 c; exact ⟨.inl c', hc⟩
    | .inr d => let ⟨d', hd⟩ := Hy2 d; exact ⟨.inr d', hd⟩

/-! ## Small constants -/

/-- Rocq: `BachmannDefs.S2`. -/
def S2 (f : Ordinal.{u} → Ordinal.{u}) (ξ : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} := schutteColumn f (succ 1) ξ

/-- Rocq: `BachmannDefs.complete_1`. -/
theorem complete_1 : Complete (1 : Ordinal.{u}) := succ_complete zero_complete

/-- Rocq: `BachmannDefs.complete_2`. -/
theorem complete_2 : Complete (succ 1 : Ordinal.{u}) := succ_complete complete_1

end Bachmann

end ConstructiveOrdinals
