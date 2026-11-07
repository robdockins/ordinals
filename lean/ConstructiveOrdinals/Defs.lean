import ConstructiveOrdinals.Tactic.OrdAuto

/-!
# Constructive type-theoretic ordinals

Port of `Ordinal/Defs.v`.

This development reconstructs enough of classical ordinal theory to be useful,
working entirely in constructive type theory.

The first goal is for these ordinals to give a practical proof technique, for
example to build termination measures for recursive programs and acyclicity
proofs for complicated data structures.

The second goal, which took most of the effort in the Rocq original, is to
climb the first part of the way into "Cantor's attic": the Veblen hierarchy,
the Feferman–Schütte ordinal Γ₀, and the small and large Veblen ordinals.
There are also ordinal notation systems up to ε₀, Γ₀, the Ackermann ordinals,
SVO and LVO. Unlike their semantic counterparts, the notation systems have a
decidable ordering and constructive Cantor normal forms. Because the semantic
ordinals are already constructive, the notation systems need no separate
syntactic well-foundedness proof; it follows from their denotations.

All definitions are constructive. Proofs use the excluded middle only where it
is needed, and then only as an explicit hypothesis, never as an axiom. Unlike
the Rocq version, this Lean port also avoids Lean's built-in axioms
(`propext`, `Quot.sound` and `Classical.choice`): every declaration should
report "does not depend on any axioms" under `#print axioms`.
-/

namespace ConstructiveOrdinals

universe u v

/-- Ordinals, represented as `Type`-indexed trees of potentially infinite
width but finite depth.

This lets us view ordinals both as objects of interest in their own right and
as canonical structures that give a distinguished way to measure the size of
values.

Because `Ordinal.{u}` abstracts over `Type u`, it lives in the strictly larger
universe `Type (u+1)`. This matches the set-theoretic idea that the proper
class of ordinals is too large to be a set: `Ordinal.{u}` can never be the
carrier of an `Ordinal.{u}`.

`Ordinal.Carrier` and `Ordinal.size` are coercions, so for `x : Ordinal` we
can write `i : x` for `i : x.Carrier` and `x i` for `x.size i`.

Rocq: `Defs.Ord` (constructor `ord`, fields `ordCarrier` and `ordSize`). -/
structure Ordinal : Type (u+1) where
  /-- Construct an ordinal as the limit of a family of ordinals. -/
  mk ::
  /-- The index type of the ordinal. Rocq: `ordCarrier`. -/
  Carrier : Type u
  /-- The ordinals below this one, indexed by the carrier. Rocq: `ordSize`. -/
  size : Carrier → Ordinal

namespace Ordinal

instance : CoeSort Ordinal.{u} (Type u) := ⟨Ordinal.Carrier⟩
instance : CoeFun Ordinal.{u} (fun x => x.Carrier → Ordinal.{u}) := ⟨Ordinal.size⟩

/-- Eta for ordinals. This is not definitional, because Lean (like Rocq) has
no definitional eta for recursive structures. -/
theorem mk_eta (x : Ordinal.{u}) : mk x.Carrier x.size = x := by
  cases x; rfl

end Ordinal

/-- Types with a distinguished ordinal measure.

This replaces Rocq's coercion `sz` together with the canonical structures that
let Rocq infer the ordinal from the type of a value. Every carrier type
`x.Carrier` gets an instance from `x.size`. Other types, such as `Nat`, get
instances where Rocq declared a canonical structure.

Rocq: `Defs.sz`. -/
class Sized (α : Type u) where
  /-- The ordinal measure of a value. Rocq: `sz`. -/
  sz : α → Ordinal.{u}

export Sized (sz)

instance (x : Ordinal.{u}) : Sized x.Carrier := ⟨x.size⟩

/-- `x ◃ y`: the measure of `x` is strictly smaller than that of `y`.
Rocq: `Defs` notation `x ◃ y`. -/
scoped notation:50 x:51 " ◃ " y:51 => sz x < sz y

/-- `x ⊴ y`: the measure of `x` is no larger than that of `y`.
Rocq: `Defs` notation `x ⊴ y`. -/
scoped notation:50 x:51 " ⊴ " y:51 => sz x ≤ sz y

namespace Ordinal

/-! ## Order relations

We define `<` and `≤` essentially by mutual recursion on the structure of
ordinals.

The quantifier structure of this definition describes a two-player game. Each
ordinal is a set of choices available to a player.

Think of `x < y` as a game state where it is our turn and we must choose in
`y`. If we choose `j : y`, play moves to `x ≤ y j`, where our opponent must
choose in `x`. If they choose `i : x`, play moves to `x i < y j`, and it is our
turn again. The game ends when a player has no choices left, which happens
after finitely many moves because ordinals are inductive. `x < y` and `x ≤ y`
are true exactly when the game has a winning strategy, and a constructive proof
exhibits one.

Two ordinals are equal, written `x ≈ y`, when `x ≤ y` and `y ≤ x`. This holds
exactly when `x` and `y` have winning strategies in the same situations:
`x ≈ y` iff `∀ a, a < x ↔ a < y`.
-/

/-- Strict order on ordinals. Rocq: `Defs.ord_lt`. -/
protected def Lt : Ordinal.{u} → Ordinal.{u} → Prop
  | mk _ f, mk _ g => ∃ b, ∀ a, Ordinal.Lt (f a) (g b)

/-- Non-strict order on ordinals. Rocq: `Defs.ord_le`. -/
protected def Le (x y : Ordinal.{u}) : Prop :=
  ∀ a, Ordinal.Lt (x a) y

/-- Ordinal equality: `≤` in both directions. Rocq: `Defs.ord_eq`. -/
protected def Equiv (x y : Ordinal.{u}) : Prop :=
  Ordinal.Le x y ∧ Ordinal.Le y x

instance : LT Ordinal.{u} := ⟨Ordinal.Lt⟩
instance : LE Ordinal.{u} := ⟨Ordinal.Le⟩
instance : HasEquiv Ordinal.{u} := ⟨Ordinal.Equiv⟩

/-- Characteristic equation for less-than. Rocq: `Defs.ord_lt_unfold`. -/
theorem lt_unfold (x y : Ordinal.{u}) : (x < y) = ∃ b : y, x ≤ y b := by
  cases x; cases y; rfl

/-- Characteristic equation for less-equal. Rocq: `Defs.ord_le_unfold`. -/
theorem le_unfold (x y : Ordinal.{u}) : (x ≤ y) = ∀ a : x, x a < y := rfl

/-- Unfolding `≈`. -/
theorem equiv_unfold (x y : Ordinal.{u}) : (x ≈ y) = (x ≤ y ∧ y ≤ x) := rfl

attribute [irreducible] Ordinal.Lt Ordinal.Le Ordinal.Equiv

theorem lt_intro {x y : Ordinal.{u}} (b : y) (h : x ≤ y b) : x < y :=
  (lt_unfold x y).symm ▸ ⟨b, h⟩

theorem lt_elim {x y : Ordinal.{u}} (h : x < y) : ∃ b : y, x ≤ y b :=
  lt_unfold x y ▸ h

theorem le_intro {x y : Ordinal.{u}} (h : ∀ a : x, x a < y) : x ≤ y :=
  (le_unfold x y).symm ▸ h

theorem le_elim {x y : Ordinal.{u}} (h : x ≤ y) : ∀ a : x, x a < y :=
  le_unfold x y ▸ h

theorem equiv_intro {x y : Ordinal.{u}} (h₁ : x ≤ y) (h₂ : y ≤ x) : x ≈ y :=
  (equiv_unfold x y).symm ▸ ⟨h₁, h₂⟩

theorem Equiv.le {x y : Ordinal.{u}} (h : x ≈ y) : x ≤ y :=
  (equiv_unfold x y ▸ h).1

theorem Equiv.ge {x y : Ordinal.{u}} (h : x ≈ y) : y ≤ x :=
  (equiv_unfold x y ▸ h).2

/-- Another way to unfold the definition of `≤`. Rocq: `Defs.ord_le_subord`. -/
theorem le_subord {x y : Ordinal.{u}} (h : x ≤ y) (i : x) : ∃ j : y, x i ≤ y j :=
  lt_elim (le_elim h i)

/-- Less-than implies less-equal. Rocq: `Defs.ord_lt_le`. -/
@[ord_hint]
theorem le_of_lt : ∀ {b a : Ordinal.{u}}, a < b → a ≤ b
  | mk _ g, a, h => by
    obtain ⟨b, hb⟩ := lt_elim h
    exact le_intro fun i => lt_intro b (le_of_lt (b := g b) (le_elim hb i))

/-- Less-equal is reflexive. Rocq: `Defs.ord_le_refl`. -/
@[ord_hint, refl]
theorem le_refl : ∀ x : Ordinal.{u}, x ≤ x
  | mk _ f => le_intro fun a => lt_intro a (le_refl (f a))

theorem le_rfl {x : Ordinal.{u}} : x ≤ x := le_refl x

/-- Rocq: `Defs.index_lt`. -/
@[ord_hint]
theorem index_lt (a : Ordinal.{u}) (i : a) : a i < a :=
  lt_intro i (le_refl _)

/-- Rocq: `Defs.index_le`. -/
@[ord_hint]
theorem index_le (a : Ordinal.{u}) (i : a) : a i ≤ a :=
  le_of_lt (index_lt a i)

/-- `≤` is transitive. Rocq: `Defs.ord_le_trans`. -/
theorem le_trans : ∀ {a b c : Ordinal.{u}}, a ≤ b → b ≤ c → a ≤ c
  | mk _ f, b, c, hab, hbc => by
    refine le_intro fun ai => ?_
    obtain ⟨bi, h₁⟩ := lt_elim (le_elim hab ai)
    obtain ⟨ci, h₂⟩ := lt_elim (le_elim hbc bi)
    exact lt_intro ci (le_trans (a := f ai) h₁ h₂)

/-- `≤` preserves `<` on the left. Rocq: `Defs.ord_le_lt_trans`. -/
theorem lt_of_le_of_lt {a b c : Ordinal.{u}} (hab : a ≤ b) (hbc : b < c) : a < c := by
  obtain ⟨ci, h⟩ := lt_elim hbc
  exact lt_intro ci (le_trans hab h)

/-- `≤` preserves `<` on the right. Rocq: `Defs.ord_lt_le_trans`. -/
theorem lt_of_lt_of_le {a b c : Ordinal.{u}} (hab : a < b) (hbc : b ≤ c) : a < c := by
  obtain ⟨bi, h⟩ := lt_elim hab
  exact lt_of_le_of_lt h (le_elim hbc bi)

/-- `<` is transitive. Rocq: `Defs.ord_lt_trans`. -/
theorem lt_trans {a b c : Ordinal.{u}} (hab : a < b) (hbc : b < c) : a < c :=
  lt_of_lt_of_le hab (le_of_lt hbc)

/-! ### Characterizations using only `<`

If we read `<` as set membership `∈`, then `≤` corresponds to the usual
definition of subset and `≈` to set equality. This makes the connection to the
von Neumann ordinals clearer.
-/

/-- Rocq: `Defs.ord_le_intro`. -/
theorem le_of_forall_lt {x y : Ordinal.{u}} (h : ∀ a, a < x → a < y) : x ≤ y :=
  le_intro fun a => h _ (index_lt x a)

/-- Rocq: `Defs.ord_le_elim`. -/
theorem lt_of_lt_of_le' {x y : Ordinal.{u}} (h : x ≤ y) : ∀ a, a < x → a < y :=
  fun _ ha => lt_of_lt_of_le ha h

/-- Rocq: `Defs.ord_le_equiv`. -/
theorem le_iff_forall_lt {x y : Ordinal.{u}} : x ≤ y ↔ ∀ a, a < x → a < y :=
  ⟨lt_of_lt_of_le', le_of_forall_lt⟩

/-- Rocq: `Defs.ord_eq_intro`. -/
theorem equiv_of_forall_lt_iff {x y : Ordinal.{u}} (h : ∀ a, a < x ↔ a < y) : x ≈ y :=
  equiv_intro (le_of_forall_lt fun a => (h a).1) (le_of_forall_lt fun a => (h a).2)

/-- Rocq: `Defs.ord_eq_elim`. -/
theorem forall_lt_iff_of_equiv {x y : Ordinal.{u}} (h : x ≈ y) : ∀ a, a < x ↔ a < y :=
  fun _ => ⟨fun ha => lt_of_lt_of_le ha h.le, fun ha => lt_of_lt_of_le ha h.ge⟩

/-- Rocq: `Defs.ord_eq_equiv`. -/
theorem equiv_iff_forall_lt_iff {x y : Ordinal.{u}} : x ≈ y ↔ ∀ a, a < x ↔ a < y :=
  ⟨forall_lt_iff_of_equiv, equiv_of_forall_lt_iff⟩

/-! ### Well-foundedness -/

/-- Rocq: `Defs.ord_lt_acc`. -/
theorem acc_of_le : ∀ (x y : Ordinal.{u}), y ≤ x → Acc (· < ·) y
  | mk _ f, z, hz => Acc.intro z fun y hy => by
    obtain ⟨b, hb⟩ := lt_elim (lt_of_lt_of_le hy hz)
    exact acc_of_le (f b) y hb

/-- The less-than ordering on ordinals is well-founded. Rocq: `Defs.ord_lt_wf`. -/
theorem lt_wf : WellFounded (α := Ordinal.{u}) (· < ·) :=
  ⟨fun a => acc_of_le a a (le_refl a)⟩

instance : WellFoundedRelation Ordinal.{u} := ⟨(· < ·), lt_wf⟩

/-- Well-founded recursion on ordinals; the workhorse for proving properties
of ordinals. Usable with `induction x using Ordinal.ltRec`.
Rocq: `Defs.ordinal_induction`. -/
@[elab_as_elim]
def ltRec {motive : Ordinal.{u} → Sort v}
    (ind : ∀ x, (∀ y, y < x → motive y) → motive x) (a : Ordinal.{u}) : motive a :=
  lt_wf.fix ind a

/-- Well-founded recursion on the elements of a type, measured by their size.
Rocq: `Defs.size_induction`. -/
@[elab_as_elim]
def sizeRec {α : Type u} [Sized α] {motive : α → Sort v}
    (ind : ∀ x, (∀ y : α, sz y < sz x → motive y) → motive x) (a : α) : motive a :=
  (InvImage.wf (sz (α := α)) lt_wf).fix ind a

/-- The less-than order is irreflexive, a simple corollary of
well-foundedness. Rocq: `Defs.ord_lt_irreflexive`. -/
theorem lt_irrefl (x : Ordinal.{u}) : ¬ x < x := by
  induction x using ltRec with
  | ind x ih => exact fun h => ih x h h

/-! ## Ordinal equality is an equivalence relation -/

/-- Rocq: `Defs.ord_eq_refl`. -/
@[refl]
theorem equiv_refl (x : Ordinal.{u}) : x ≈ x := equiv_intro (le_refl x) (le_refl x)

/-- Rocq: `Defs.ord_eq_trans`. -/
theorem equiv_trans {x y z : Ordinal.{u}} (h₁ : x ≈ y) (h₂ : y ≈ z) : x ≈ z :=
  equiv_intro (le_trans h₁.le h₂.le) (le_trans h₂.ge h₁.ge)

/-- Rocq: `Defs.ord_eq_sym`. -/
@[symm]
theorem equiv_symm {x y : Ordinal.{u}} (h : x ≈ y) : y ≈ x := equiv_intro h.ge h.le

theorem Equiv.refl (x : Ordinal.{u}) : x ≈ x := equiv_refl x
theorem Equiv.symm {x y : Ordinal.{u}} (h : x ≈ y) : y ≈ x := equiv_symm h
theorem Equiv.trans {x y z : Ordinal.{u}} (h₁ : x ≈ y) (h₂ : y ≈ z) : x ≈ z :=
  equiv_trans h₁ h₂

theorem equivalence : Equivalence (α := Ordinal.{u}) (· ≈ ·) :=
  ⟨equiv_refl, equiv_symm, equiv_trans⟩

/-! ### Relations for `calc` and rewriting

The `Trans` instances below support `calc` chains. Together with `le_of_lt`,
`Equiv.le`, `Equiv.ge` and the `ord_rw` tactic, they replace Rocq's setoid
rewriting setup.

Rocq: the relations `Defs.ord_le_rel`, `Defs.ord_lt_rel` and `Defs.ord_eq_rel`,
and the subrelation instances `Defs.ord_lt_le_subreleation`,
`Defs.ord_eq_le_subrelation` and `Defs.ord_eq_flip_le_subrelation`.
-/

instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨le_trans⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· ≤ ·) (· < ·) (· < ·) :=
  ⟨lt_of_le_of_lt⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· < ·) (· ≤ ·) (· < ·) :=
  ⟨lt_of_lt_of_le⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· < ·) (· < ·) (· < ·) := ⟨lt_trans⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· ≈ ·) (· ≈ ·) (· ≈ ·) := ⟨equiv_trans⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· ≈ ·) (· ≤ ·) (· ≤ ·) :=
  ⟨fun h₁ h₂ => le_trans h₁.le h₂⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· ≤ ·) (· ≈ ·) (· ≤ ·) :=
  ⟨fun h₁ h₂ => le_trans h₁ h₂.le⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· ≈ ·) (· < ·) (· < ·) :=
  ⟨fun h₁ h₂ => lt_of_le_of_lt h₁.le h₂⟩
instance : @Trans Ordinal.{u} Ordinal.{u} Ordinal.{u} (· < ·) (· ≈ ·) (· < ·) :=
  ⟨fun h₁ h₂ => lt_of_lt_of_le h₁ h₂.le⟩

/-- `<` is antitone in its first argument and monotone in its second.
Rocq: `Defs.ord_lt_mor` and `Defs.ord_lt_mor'`. -/
theorem lt_mono {a a' b b' : Ordinal.{u}} (ha : a' ≤ a) (hb : b ≤ b') (h : a < b) :
    a' < b' :=
  lt_of_le_of_lt ha (lt_of_lt_of_le h hb)

/-- Every increasing function is inflationary.
Rocq: `Defs.increasing_inflationary`. -/
theorem increasing_inflationary {f : Ordinal.{u} → Ordinal.{u}}
    (hinc : ∀ x y, x < y → f x < f y) (a : Ordinal.{u}) : a ≤ f a := by
  induction a using ltRec with
  | ind a ih => exact le_of_forall_lt fun z hz => lt_of_le_of_lt (ih z hz) (hinc z a hz)

/-! ## Zero, limit and successor ordinals

Classically, every ordinal falls into exactly one of these three classes.
Without the excluded middle we cannot prove that every ordinal is in one of
them, but we can show that the classes are mutually exclusive.
-/

/-- Rocq: `Defs.hasMaxElement`. -/
def HasMaxElement (A : Type u) (f : A → Ordinal.{u}) : Prop :=
  ∃ a, ∀ a', f a' ≤ f a

/-- Rocq: `Defs.ascendingSet`. -/
def AscendingSet (A : Type u) (f : A → Ordinal.{u}) : Prop :=
  ∀ a, ∃ a', f a < f a'

/-- Rocq: `Defs.zeroOrdinal`. -/
def IsZero (x : Ordinal.{u}) : Prop := ¬ Nonempty x.Carrier

/-- Rocq: `Defs.successorOrdinal`. -/
def IsSucc (x : Ordinal.{u}) : Prop := HasMaxElement x.Carrier x.size

/-- Rocq: `Defs.limitOrdinal`. -/
def IsLimit (x : Ordinal.{u}) : Prop := Nonempty x.Carrier ∧ AscendingSet x.Carrier x.size

/-- Rocq: `Defs.hasMax_ascending_contradiction`. -/
theorem hasMax_ascending_contradiction {A : Type u} {f : A → Ordinal.{u}}
    (hmax : HasMaxElement A f) (hasc : AscendingSet A f) : False := by
  obtain ⟨a, ha⟩ := hmax
  obtain ⟨a', ha'⟩ := hasc a
  exact lt_irrefl (f a') (lt_of_le_of_lt (ha a') ha')

/-- An ordinal cannot be both zero and a successor.
Rocq: `Defs.zero_not_successor`. -/
theorem zero_not_successor (x : Ordinal.{u}) (hz : IsZero x) (hs : IsSucc x) : False := by
  obtain ⟨a, _⟩ := hs
  exact hz ⟨a⟩

/-- An ordinal cannot be both zero and a limit. Rocq: `Defs.zero_not_limit`. -/
theorem zero_not_limit (x : Ordinal.{u}) (hz : IsZero x) (hl : IsLimit x) : False :=
  hz hl.1

/-- An ordinal cannot be both a successor and a limit.
Rocq: `Defs.successor_not_limit`. -/
theorem successor_not_limit (x : Ordinal.{u}) (hs : IsSucc x) (hl : IsLimit x) : False :=
  hasMax_ascending_contradiction hs hl.2

end Ordinal

/-! ## Auxiliary list predicates -/

/-- `P` holds of every element of a list. Rocq: `Defs.each`. -/
def Each {α : Type u} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ Each P xs

/-- Rocq: `Defs.each_implies`. -/
theorem Each.imp {α : Type u} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ {xs : List α}, Each P xs → Each Q xs
  | [], _ => trivial
  | _ :: _, ⟨hx, hxs⟩ => ⟨h _ hx, Each.imp h hxs⟩

/-- Rocq: `Defs.each_map`. -/
theorem Each.map_iff {α : Type u} {β : Type v} (P : β → Prop) (f : α → β) :
    ∀ xs : List α, Each P (xs.map f) ↔ Each (fun x => P (f x)) xs
  | [] => Iff.rfl
  | _ :: xs => and_congr Iff.rfl (Each.map_iff P f xs)

/-- Two lists are related elementwise by `R`. Rocq: `Defs.pairwise`. -/
inductive Forall₂ {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  /-- Rocq: `pairwise_nil`. -/
  | nil : Forall₂ R [] []
  /-- Rocq: `pairwise_cons`. -/
  | cons {x xs y ys} : R x y → Forall₂ R xs ys → Forall₂ R (x :: xs) (y :: ys)

/-- Rocq: `Defs.pairwise_length`. -/
theorem Forall₂.length_eq {α : Type u} {β : Type v} {R : α → β → Prop} :
    ∀ {xs ys}, Forall₂ R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg Nat.succ h.length_eq

/-- Rocq: `Defs.pairwise_le_refl`. -/
theorem Forall₂.le_refl : ∀ xs : List Ordinal.{u}, Forall₂ (· ≤ ·) xs xs
  | [] => .nil
  | x :: xs => .cons (Ordinal.le_refl x) (Forall₂.le_refl xs)

/-- Rocq: `Defs.pairwise_eq_refl`. -/
theorem Forall₂.equiv_refl : ∀ xs : List Ordinal.{u}, Forall₂ (· ≈ ·) xs xs
  | [] => .nil
  | x :: xs => .cons (Ordinal.equiv_refl x) (Forall₂.equiv_refl xs)

/-! ## Comparison results

Rocq's `ordering` (`LT`, `EQ`, `GT`) is Lean's `Ordering` (`lt`, `eq`, `gt`),
and Rocq's `ordering_swap` is `Ordering.swap`.

Rocq: `Defs.ordering`, `Defs.ordering_swap`.
-/

/-- Lexicographic combination of comparison results: `o` unless it is `eq`,
in which case `o'`. Rocq: `Defs.lexCompare`.

Core's `Ordering.then` is the same function, but its definition depends on
`propext`: a `match` with an overlapping wildcard pattern compiles to a proof
that uses it. Every case is therefore spelled out here. -/
def lexCompare : Ordering → Ordering → Ordering
  | .lt, _ => .lt
  | .eq, o' => o'
  | .gt, _ => .gt

/-- Swapping both arguments of a lexicographic comparison swaps the result. -/
theorem lexCompare_swap (o o' : Ordering) :
    (lexCompare o o').swap = lexCompare o.swap o'.swap := by
  cases o <;> rfl

/-- The relation between two ordinals that a comparison result claims.
Rocq: `Defs.ordering_correct`. -/
def OrderingCorrect : Ordering → Ordinal.{u} → Ordinal.{u} → Prop
  | .lt, a, b => a < b
  | .eq, a, b => a ≈ b
  | .gt, a, b => b < a

/-- Comparison of natural numbers by structural recursion, so that it
computes in the kernel. Rocq: `Defs.nat_compare`. -/
def natCompare : Nat → Nat → Ordering
  | 0, 0 => .eq
  | _ + 1, 0 => .gt
  | 0, _ + 1 => .lt
  | x + 1, y + 1 => natCompare x y

/-- Rocq: `Defs.nat_compare_correct`. -/
theorem natCompare_correct : ∀ x y : Nat,
    match natCompare x y with
    | .lt => x < y
    | .eq => x = y
    | .gt => y < x
  | 0, 0 => rfl
  | _ + 1, 0 => Nat.zero_lt_succ _
  | 0, _ + 1 => Nat.zero_lt_succ _
  | x + 1, y + 1 => by
    have ih := natCompare_correct x y
    show match natCompare x y with
      | .lt => x + 1 < y + 1
      | .eq => x + 1 = y + 1
      | .gt => y + 1 < x + 1
    revert ih
    cases natCompare x y with
    | lt => exact Nat.succ_lt_succ
    | eq => exact congrArg (· + 1)
    | gt => exact Nat.succ_lt_succ

/-- Rocq: `Defs.ordering_correct_eq_mor`. -/
theorem OrderingCorrect.congr {o : Ordering} {a a' b b' : Ordinal.{u}} (ha : a ≈ a')
    (hb : b ≈ b') (h : OrderingCorrect o a b) : OrderingCorrect o a' b' :=
  match o, h with
  | .lt, h => Ordinal.lt_of_le_of_lt ha.ge (Ordinal.lt_of_lt_of_le h hb.le)
  | .eq, h => Ordinal.equiv_trans (Ordinal.equiv_symm ha) (Ordinal.equiv_trans h hb)
  | .gt, h => Ordinal.lt_of_le_of_lt hb.ge (Ordinal.lt_of_lt_of_le h ha.le)

end ConstructiveOrdinals
