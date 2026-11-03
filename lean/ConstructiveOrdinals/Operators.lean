import ConstructiveOrdinals.Defs
import ConstructiveOrdinals.Prelude.Logic
import ConstructiveOrdinals.Prelude.Nat
import ConstructiveOrdinals.Tactic.OrdRewrite

/-!
# Basic ordinal operators

Port of `Ordinal/Operators.v`: zero, successor, limits, suprema, binary and
infinitary infima, ω, predecessor, and *complete* ordinals.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-! ## Definitions -/

/-- The zero ordinal, indexed by the empty type. This is the least ordinal.
Rocq: `Operators.zeroOrd`. -/
def zero : Ordinal.{u} := mk PEmpty PEmpty.elim

/-- The successor ordinal, indexed by the unit type. It is the smallest
ordinal strictly larger than its argument. Rocq: `Operators.succOrd`. -/
def succ (x : Ordinal.{u}) : Ordinal.{u} := mk PUnit fun _ => x

/-- The natural numbers inject into the ordinals in the obvious way.
Rocq: `Operators.natOrdSize`. -/
def ofNat : Nat → Ordinal.{u}
  | 0 => zero
  | n + 1 => succ (ofNat n)

/-- Numeric literals denote finite ordinals, as in Rocq's
`Number Notation Ord ... (via nat mapping [zeroOrd => O, succOrd => S])`. -/
instance (n : Nat) : OfNat Ordinal.{u} n := ⟨ofNat n⟩

/-- Limit ordinals, with the index type implicit. Rocq: `Operators.limOrd`. -/
def lim {A : Type u} (f : A → Ordinal.{u}) : Ordinal.{u} := mk A f

/-- The binary upper bound of two ordinals, indexed by the sum of their
index types. Rocq: `Operators.lubOrd`. -/
def lub (x y : Ordinal.{u}) : Ordinal.{u} :=
  mk (x.Carrier ⊕ y.Carrier) (Sum.elim x.size y.size)

/-- The supremum of a family of ordinals, indexed by a sigma type. This is the
least ordinal that is (non-strictly) above every ordinal in the range of `f`.
Rocq: `Operators.supOrd`. -/
def sup {A : Type u} (f : A → Ordinal.{u}) : Ordinal.{u} :=
  mk (Σ a, (f a).Carrier) fun p => f p.1 p.2

/-- The binary greatest lower bound of two ordinals. It is indexed by pairs:
it plays the games of both ordinals simultaneously. Rocq: `Operators.glbOrd`. -/
def glb : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | mk A f, mk B g => mk (A × B) fun p => glb (f p.1) (g p.2)

/-- `x ⊔ y`: binary least upper bound. -/
scoped infixr:68 " ⊔ " => Ordinal.lub
/-- `x ⊓ y`: binary greatest lower bound. -/
scoped infixr:69 " ⊓ " => Ordinal.glb

/-- The recursion behind `inf`. Its index set is essentially a dependent
function that chooses an element of each member of the range of `f`.
Rocq: `Operators.infOrd_loop`. -/
def infLoop : Ordinal.{u} → (A : Type u) → (A → Ordinal.{u}) → Ordinal.{u}
  | mk B g, A, f => mk (B × ∀ i, (f i).Carrier) fun jk => infLoop (g jk.1) A fun i => f i (jk.2 i)

/-- The greatest lower bound of a nonempty, possibly infinite, family of
ordinals. Nonemptiness is witnessed by a distinguished index `i`; induction
runs on `f i`.

Showing that this is the greatest lower bound requires a choice principle, to
turn a proof of `∀ x, ∃ y, …` into a function. If the order relations were
informative (in `Type` rather than `Prop`), no choice principle would be
needed. Rocq: `Operators.infOrd`. -/
def inf (A : Type u) (i : A) (f : A → Ordinal.{u}) : Ordinal.{u} := infLoop (f i) A f

/-- The limit of all the finite ordinals: ω, the smallest limit ordinal.
Rocq: `Operators.ω`. -/
def omega : Ordinal.{u} := mk (ULift Nat) fun n => ofNat n.down

/-- ω, the least limit ordinal. -/
scoped notation "ω" => Ordinal.omega

/-- The supremum of `f` applied to all the ordinals below `β`.
Rocq: `Operators.boundedSup`. -/
def boundedSup (β : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} :=
  sup fun i : β.Carrier => f (β i)

/-- The supremum of all the ordinals strictly below `x`. It is stationary on
limit ordinals (and zero) but undoes a successor. Rocq: `Operators.predOrd`. -/
def pred (x : Ordinal.{u}) : Ordinal.{u} := sup x.size

/-- A function on ordinals is strongly continuous if it preserves all nonempty
suprema. Rocq: `Operators.strongly_continuous`. -/
def StronglyContinuous (s : Ordinal.{u} → Ordinal.{u}) : Prop :=
  ∀ (A : Type u) (f : A → Ordinal.{u}) (_ : A), s (sup f) ≤ sup fun i => s (f i)

/-- A family is directed if any two members have a common upper bound in the
family. Rocq: `Operators.directed`. -/
def Directed (A : Type u) (f : A → Ordinal.{u}) : Prop :=
  ∀ a₁ a₂, ∃ a', f a₁ ≤ f a' ∧ f a₂ ≤ f a'

/-- A *complete* ordinal is directed, has a decidable inhabitedness question,
and has complete subordinals.

This technical property appears often in later proofs. Classically, every
ordinal is complete, as follows easily from totality of the order.
Rocq: `Operators.complete`. -/
def Complete : Ordinal.{u} → Prop
  | mk A f => Directed A f ∧ (Nonempty A ∨ ¬Nonempty A) ∧ ∀ a, Complete (f a)

/-! ## Unfolding lemmas -/

/-- Rocq: `Operators.zero_unfold`. -/
theorem zero_unfold : (0 : Ordinal.{u}) = mk PEmpty PEmpty.elim := rfl

/-- Rocq: `Operators.succ_unfold`. -/
theorem succ_unfold (x : Ordinal.{u}) : succ x = mk PUnit fun _ => x := rfl

theorem ofNat_zero : ofNat.{u} 0 = 0 := rfl
theorem ofNat_succ (n : Nat) : ofNat.{u} (n + 1) = succ (ofNat n) := rfl

/-- Rocq: `Operators.sup_unfold`. -/
theorem sup_unfold {A : Type u} (f : A → Ordinal.{u}) :
    sup f = mk (Σ a, (f a).Carrier) fun p => f p.1 p.2 := rfl

/-- Rocq: `Operators.limit_unfold`. -/
theorem limit_unfold {A : Type u} (f : A → Ordinal.{u}) : lim f = mk A f := rfl

/-- Rocq: `Operators.pred_unfold`. -/
theorem pred_unfold (x : Ordinal.{u}) : pred x = sup x.size := rfl

/-- Rocq: `Operators.glb_unfold`. -/
theorem glb_unfold (x y : Ordinal.{u}) :
    x ⊓ y = mk (x.Carrier × y.Carrier) fun i => x i.1 ⊓ y i.2 := by
  cases x; cases y; rfl

/-- Rocq: `Operators.lub_unfold`. -/
theorem lub_unfold (x y : Ordinal.{u}) :
    x ⊔ y = mk (x.Carrier ⊕ y.Carrier) (Sum.elim x.size y.size) := rfl

theorem complete_unfold (x : Ordinal.{u}) :
    Complete x = (Directed x.Carrier x.size ∧ (Nonempty x.Carrier ∨ ¬Nonempty x.Carrier) ∧
      ∀ a, Complete (x a)) := by
  cases x; rfl

theorem Complete.elim {x : Ordinal.{u}} (h : Complete x) :
    Directed x.Carrier x.size ∧ (Nonempty x.Carrier ∨ ¬Nonempty x.Carrier) ∧
      ∀ a, Complete (x a) :=
  complete_unfold x ▸ h

theorem Complete.intro {x : Ordinal.{u}} (h₁ : Directed x.Carrier x.size)
    (h₂ : Nonempty x.Carrier ∨ ¬Nonempty x.Carrier) (h₃ : ∀ a, Complete (x a)) :
    Complete x :=
  (complete_unfold x).symm ▸ ⟨h₁, h₂, h₃⟩

/-! ## Complete ordinals -/

/-- Rocq: `Operators.complete_subord`. -/
@[ord_hint]
theorem complete_subord {o : Ordinal.{u}} (h : Complete o) (i : o) : Complete (o i) :=
  h.elim.2.2 i

/-! ## Zero -/

/-- Zero is the least ordinal. Rocq: `Operators.zero_least`. -/
@[ord_hint]
theorem zero_least (o : Ordinal.{u}) : 0 ≤ o :=
  le_intro fun a => PEmpty.elim a

/-- No ordinal is strictly below zero. Rocq: `Operators.zero_lt`. -/
@[ord_hint]
theorem zero_lt (o : Ordinal.{u}) : ¬ o < 0 := fun h =>
  let ⟨b, _⟩ := lt_elim h
  PEmpty.elim b

/-- Rocq: `Operators.zero_complete`. -/
@[ord_hint]
theorem zero_complete : Complete (0 : Ordinal.{u}) :=
  Complete.intro (fun a => PEmpty.elim a) (Or.inr fun ⟨a⟩ => PEmpty.elim a)
    (fun a => PEmpty.elim a)

/-- Rocq: `Operators.complete_zeroDec`. -/
theorem complete_zeroDec {o : Ordinal.{u}} (h : Complete o) : o ≤ 0 ∨ 0 < o :=
  match h.elim.2.1 with
  | .inl ⟨a⟩ => .inr (lt_intro a (zero_least _))
  | .inr hn => .inl (le_intro fun a => (hn ⟨a⟩).elim)

/-- Rocq: `Operators.complete_directed`. -/
theorem complete_directed {o : Ordinal.{u}} (h : Complete o) :
    ∀ a₁ a₂, ∃ a', o a₁ ≤ o a' ∧ o a₂ ≤ o a' :=
  h.elim.1

/-- Rocq: `Operators.directed_monotone`. -/
theorem directed_monotone (a : Ordinal.{u}) (f : a.Carrier → Ordinal.{u})
    (hmono : ∀ x y : a.Carrier, sz x ≤ sz y → f x ≤ f y) (h : Complete a) :
    Directed a.Carrier f := fun a₁ a₂ =>
  let ⟨a', h₁, h₂⟩ := complete_directed h a₁ a₂
  ⟨a', hmono _ _ h₁, hmono _ _ h₂⟩

/-! ## Successor

`succ` is monotone for both `<` and `≤`, is strictly above its argument, and
is the smallest such ordinal.
-/

/-- Rocq: `Operators.succ_lt`. -/
@[ord_hint]
theorem succ_lt (o : Ordinal.{u}) : o < succ o := lt_intro PUnit.unit (le_refl o)

/-- Rocq: `Operators.succ_least`. -/
@[ord_hint]
theorem succ_least {x y : Ordinal.{u}} (h : x < y) : succ x ≤ y := le_intro fun _ => h

/-- Rocq: `Operators.succ_monotone` and `Operators.succOrd_le_mor`. -/
@[ord_hint, ord_mono]
theorem succ_monotone {a b : Ordinal.{u}} (h : a ≤ b) : succ a ≤ succ b :=
  succ_least (lt_of_le_of_lt h (succ_lt b))

/-- Rocq: `Operators.succ_increasing` and `Operators.succOrd_lt_mor`. -/
@[ord_hint]
theorem succ_increasing {a b : Ordinal.{u}} (h : a < b) : succ a < succ b :=
  lt_of_le_of_lt (succ_least h) (succ_lt b)

/-- Rocq: `Operators.succ_trans`. -/
@[ord_hint]
theorem succ_trans {x y : Ordinal.{u}} (h : x ≤ y) : x < succ y := lt_intro PUnit.unit h

/-- Rocq: `Operators.succ_trans'`. -/
@[ord_hint]
theorem succ_trans' {x y : Ordinal.{u}} (h : x ≤ y) : x ≤ succ y := le_of_lt (succ_trans h)

/-- Rocq: `Operators.succ_congruence` and `Operators.succOrd_eq_mor`. -/
@[ord_hint]
theorem succ_congruence {a b : Ordinal.{u}} (h : a ≈ b) : succ a ≈ succ b :=
  equiv_intro (succ_monotone h.le) (succ_monotone h.ge)

/-- Rocq: `Operators.succ_complete`. -/
@[ord_hint]
theorem succ_complete {o : Ordinal.{u}} (h : Complete o) : Complete (succ o) :=
  Complete.intro (fun _ _ => ⟨PUnit.unit, le_refl o, le_refl o⟩) (.inl ⟨PUnit.unit⟩) fun _ => h

/-- Rocq: `Operators.natOrdSize_complete`. -/
@[ord_hint]
theorem ofNat_complete : ∀ n : Nat, Complete (ofNat.{u} n)
  | 0 => zero_complete
  | n + 1 => succ_complete (ofNat_complete n)

/-! ## Supremum -/

/-- The supremum is (non-strictly) above every ordinal in the family.
Rocq: `Operators.sup_le`. -/
@[ord_hint]
theorem sup_le {A : Type u} (f : A → Ordinal.{u}) (a : A) : f a ≤ sup f :=
  le_intro fun b => lt_intro (show (sup f).Carrier from ⟨a, b⟩) (le_refl _)

/-- The supremum is the least upper bound. Rocq: `Operators.sup_least`. -/
theorem sup_least {A : Type u} {f : A → Ordinal.{u}} {z : Ordinal.{u}} (h : ∀ a, f a ≤ z) :
    sup f ≤ z :=
  le_intro fun p => le_elim (h p.1) p.2

/-- Rocq: `Operators.sup_lt`. -/
theorem sup_lt {x : Ordinal.{u}} {A : Type u} {f : A → Ordinal.{u}} (h : x < sup f) :
    ∃ a, x < f a :=
  let ⟨⟨a, q⟩, hq⟩ := lt_elim h
  ⟨a, lt_intro q hq⟩

/-- Rocq: `Operators.sup_ord_le_morphism`. -/
@[ord_mono]
theorem sup_monotone {A : Type u} {f g : A → Ordinal.{u}} (h : ∀ a, f a ≤ g a) :
    sup f ≤ sup g :=
  sup_least fun a => le_trans (h a) (sup_le g a)

/-- Rocq: `Operators.sup_ord_eq_morphism`. -/
theorem sup_congr {A : Type u} {f g : A → Ordinal.{u}} (h : ∀ a, f a ≈ g a) :
    sup f ≈ sup g :=
  equiv_intro (sup_monotone fun a => (h a).le) (sup_monotone fun a => (h a).ge)

/-! ## Limits -/

/-- The limit is strictly above every ordinal in the family.
Rocq: `Operators.limit_lt`. -/
@[ord_hint]
theorem limit_lt {A : Type u} (f : A → Ordinal.{u}) (i : A) : f i < lim f :=
  lt_intro (show (lim f).Carrier from i) (le_refl _)

/-- The limit is the least ordinal strictly above every member of the family.
Rocq: `Operators.limit_least`. -/
theorem limit_least {A : Type u} {f : A → Ordinal.{u}} {z : Ordinal.{u}} (h : ∀ i, f i < z) :
    lim f ≤ z :=
  le_intro h

/-! Supremum and limit are closely related. We always have
`sup f ≤ lim f ≤ succ (sup f)` and `lim f ≈ sup (succ ∘ f)`. When `f` is an
ascending family, `lim f ≈ sup f`; when it has a maximal element,
`lim f ≈ succ (sup f)`. -/

/-- Rocq: `Operators.sup_lim`. -/
theorem sup_lim {A : Type u} (f : A → Ordinal.{u}) : sup f ≤ lim f :=
  sup_least fun a => le_of_lt (limit_lt f a)

/-- Rocq: `Operators.lim_sup`. -/
theorem lim_sup {A : Type u} (f : A → Ordinal.{u}) : lim f ≤ succ (sup f) :=
  limit_least fun a => lt_of_le_of_lt (sup_le f a) (succ_lt _)

/-- Rocq: `Operators.sup_succ_lim`. -/
theorem sup_succ_lim {A : Type u} (f : A → Ordinal.{u}) :
    lim f ≈ sup fun a => succ (f a) := by
  refine equiv_intro (limit_least fun i => ?_) (sup_least fun a => succ_least (limit_lt f a))
  ord_rw [← sup_le (fun a => succ (f a)) i]
  exact succ_lt (f i)

/-- Rocq: `Operators.ascending_sup_lim`. -/
theorem ascending_sup_lim {A : Type u} {f : A → Ordinal.{u}} (hasc : AscendingSet A f) :
    lim f ≈ sup f :=
  equiv_intro
    (limit_least fun a =>
      let ⟨a', h⟩ := hasc a
      lt_of_lt_of_le h (sup_le f a'))
    (sup_lim f)

/-- Rocq: `Operators.succ_sup_lim`. -/
theorem succ_sup_lim {A : Type u} {f : A → Ordinal.{u}} (hmax : HasMaxElement A f) :
    lim f ≈ succ (sup f) :=
  equiv_intro (lim_sup f)
    (succ_least (let ⟨i, hi⟩ := hmax; lt_intro (show (lim f).Carrier from i) (sup_least hi)))

/-- Rocq: `Operators.lim_ord_le_morphism`. -/
@[ord_mono]
theorem lim_monotone {A : Type u} {f g : A → Ordinal.{u}} (h : ∀ a, f a ≤ g a) :
    lim f ≤ lim g :=
  limit_least fun a => lt_of_le_of_lt (h a) (limit_lt g a)

/-- Rocq: `Operators.lim_ord_eq_morphism`. -/
theorem lim_congr {A : Type u} {f g : A → Ordinal.{u}} (h : ∀ a, f a ≈ g a) :
    lim f ≈ lim g :=
  equiv_intro (lim_monotone fun a => (h a).le) (lim_monotone fun a => (h a).ge)

/-! ## Infima

`inf` computes the greatest lower bound of a nonempty family. The proof
requires `DependentFunctionalChoice`.

Classically, the infimum of a set of ordinals is always a member of the set,
since there are no infinite descending chains of ordinals.
-/

/-- Rocq: `Operators.inf_loop_lower_bound`. -/
theorem infLoop_lower_bound :
    ∀ (x : Ordinal.{u}) (A : Type u) (f : A → Ordinal.{u}),
      infLoop x A f ≤ x ∧ ∀ i, infLoop x A f ≤ f i
  | mk B g, A, f =>
    ⟨le_intro fun jk =>
        lt_intro (show (mk B g).Carrier from jk.1)
          (infLoop_lower_bound (g jk.1) A fun i => f i (jk.2 i)).1,
      fun i => le_intro fun jk =>
        lt_intro (jk.2 i) ((infLoop_lower_bound (g jk.1) A fun i => f i (jk.2 i)).2 i)⟩

/-- Rocq: `Operators.inf_loop_greatest`. -/
theorem infLoop_greatest (hc : DependentFunctionalChoice.{u}) :
    ∀ (x : Ordinal.{u}) (A : Type u) (f : A → Ordinal.{u}) (z : Ordinal.{u}),
      z ≤ x → (∀ i, z ≤ f i) → z ≤ infLoop x A f
  | mk B g, A, f, z, hzx, hzf => le_intro fun q => by
    obtain ⟨b, hb⟩ := lt_elim (le_elim hzx q)
    obtain ⟨k, hk⟩ := hc A (fun i => (f i).Carrier) (fun i j => z q ≤ f i j)
      fun i => lt_elim (le_elim (hzf i) q)
    exact lt_intro (show (infLoop (mk B g) A f).Carrier from (b, k))
      (infLoop_greatest hc (g b) A _ (z q) hb hk)

/-- Rocq: `Operators.inf_lower_bound`. -/
theorem inf_lower_bound (A : Type u) (i₀ : A) (f : A → Ordinal.{u}) (i : A) :
    inf A i₀ f ≤ f i :=
  (infLoop_lower_bound (f i₀) A f).2 i

/-- Rocq: `Operators.inf_greatest`. -/
theorem inf_greatest (hc : DependentFunctionalChoice.{u}) (A : Type u) (i₀ : A)
    (f : A → Ordinal.{u}) (z : Ordinal.{u}) (h : ∀ i, z ≤ f i) : z ≤ inf A i₀ f :=
  infLoop_greatest hc (f i₀) A f z (h i₀) h

/-! ## Bounded suprema -/

/-- For monotone `f`, `boundedSup β f` is an upper bound of `f x` for every
`x < β`. Rocq: `Operators.boundedSup_le`. -/
theorem boundedSup_le (β : Ordinal.{u}) {f : Ordinal.{u} → Ordinal.{u}}
    (hmono : ∀ x y, x ≤ y → f x ≤ f y) (x : Ordinal.{u}) (h : x < β) :
    f x ≤ boundedSup β f := by
  obtain ⟨b, hb⟩ := lt_elim h
  unfold boundedSup
  ord_rw [← sup_le (fun i : β.Carrier => f (β i)) b]
  exact hmono _ _ hb

/-- …and it is the least ordinal with this property.
Rocq: `Operators.boundedSup_least`. -/
theorem boundedSup_least (β : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (z : Ordinal.{u})
    (h : ∀ x, x < β → f x ≤ z) : boundedSup β f ≤ z :=
  sup_least fun i => h _ (index_lt β i)

/-! ## ω -/

/-- Rocq: `Operators.omega_limit`. -/
theorem omega_limit : IsLimit (ω : Ordinal.{u}) :=
  ⟨⟨⟨0⟩⟩, fun n => ⟨⟨n.down + 1⟩, succ_lt _⟩⟩

/-- ω is the smallest limit ordinal. Rocq: `Operators.omega_least`. -/
theorem omega_least {x : Ordinal.{u}} (h : IsLimit x) : ω ≤ x := by
  obtain ⟨⟨q⟩, hasc⟩ := h
  refine le_intro fun n => ?_
  show ofNat n.down < x
  induction n.down with
  | zero => exact lt_intro q (zero_least _)
  | succ n ih =>
    obtain ⟨r, hr⟩ := lt_elim ih
    obtain ⟨s, hs⟩ := hasc r
    exact lt_intro s (succ_least (lt_of_le_of_lt hr hs))

/-- Rocq: `Operators.natOrdSize_monotone`. -/
theorem ofNat_monotone {i j : Nat} (h : i ≤ j) : ofNat.{u} i ≤ ofNat j := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (le_of_lt (succ_lt _))

/-- Rocq: `Operators.natOrdSize_increasing`. -/
theorem ofNat_increasing {m n : Nat} (h : m < n) : ofNat.{u} m < ofNat n :=
  lt_of_lt_of_le (succ_lt (ofNat m)) (ofNat_monotone h)

/-- Rocq: `Operators.succ_cancel_le`. -/
theorem succ_cancel_le {x y : Ordinal.{u}} (h : succ x ≤ succ y) : x ≤ y :=
  (le_subord h PUnit.unit).elim fun _ h' => h'

/-- Rocq: `Operators.succ_cancel_eq`. -/
theorem succ_cancel_eq {x y : Ordinal.{u}} (h : succ x ≈ succ y) : x ≈ y :=
  equiv_intro (succ_cancel_le h.le) (succ_cancel_le h.ge)

/-- Rocq: `Operators.natOrdSize_unique`. -/
theorem ofNat_unique : ∀ m n : Nat, ofNat.{u} m ≈ ofNat n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, h => (zero_lt _ (le_elim h.ge PUnit.unit)).elim
  | _ + 1, 0, h => (zero_lt _ (le_elim h.le PUnit.unit)).elim
  | m + 1, n + 1, h => congrArg (· + 1) (ofNat_unique m n (succ_cancel_eq h))

/-- Rocq: `Operators.omega_complete`. -/
@[ord_hint]
theorem omega_complete : Complete (ω : Ordinal.{u}) :=
  Complete.intro
    (fun a₁ a₂ => ⟨⟨Nat.max a₁.down a₂.down⟩,
      ofNat_monotone (Nat.le_max_left _ _), ofNat_monotone (Nat.le_max_right _ _)⟩)
    (.inl ⟨⟨0⟩⟩) (fun n => ofNat_complete n.down)

/-- Rocq: `Operators.omega_gt0`. -/
@[ord_hint]
theorem omega_gt0 : (0 : Ordinal.{u}) < ω := index_lt ω ⟨0⟩

/-- Rocq: `Operators.omega_gt1`. -/
@[ord_hint]
theorem omega_gt1 : (1 : Ordinal.{u}) < ω := index_lt ω ⟨1⟩

/-! ## Zero, successor and limit ordinals, up to `≈` -/

/-- Any zero ordinal is equal to the distinguished `0`.
Rocq: `Operators.ord_isZero`. -/
theorem isZero_iff (z : Ordinal.{u}) : IsZero z ↔ z ≈ 0 :=
  ⟨fun h => equiv_intro (le_intro fun a => (h ⟨a⟩).elim) (zero_least z),
   fun h ⟨a⟩ => zero_lt _ (le_elim h.le a)⟩

/-- Any successor ordinal is equal to some application of `succ`.
Rocq: `Operators.ord_isSucc`. -/
theorem isSucc_iff (x : Ordinal.{u}) : IsSucc x ↔ ∃ o, x ≈ succ o :=
  ⟨fun ⟨a, ha⟩ => ⟨x a, equiv_intro (le_intro fun a' => lt_of_le_of_lt (ha a') (succ_lt _))
      (succ_least (index_lt x a))⟩,
   fun ⟨o, ho⟩ =>
    let ⟨a, ha⟩ := lt_elim (le_elim ho.ge PUnit.unit)
    ⟨a, fun a' => let ⟨_, hz⟩ := lt_elim (le_elim ho.le a'); le_trans hz ha⟩⟩

/-- Rocq: `Operators.ord_isLimit`. -/
theorem isLimit_iff (x : Ordinal.{u}) :
    IsLimit x ↔ 0 < x ∧ ∀ i, i < x → ∃ j, i < j ∧ j < x :=
  ⟨fun ⟨⟨a⟩, hasc⟩ => ⟨lt_intro a (zero_least _), fun _ hi =>
      let ⟨b, hb⟩ := lt_elim hi
      let ⟨b', hb'⟩ := hasc b
      ⟨x b', lt_of_le_of_lt hb hb', index_lt x b'⟩⟩,
   fun ⟨h₀, h⟩ => ⟨(lt_elim h₀).elim fun b _ => ⟨b⟩, fun a =>
      let ⟨_, hj₁, hj₂⟩ := h (x a) (index_lt x a)
      let ⟨k, hk⟩ := lt_elim hj₂
      ⟨k, lt_of_lt_of_le hj₁ hk⟩⟩⟩

/-- Rocq: `Operators.limit_boundedSup`. -/
theorem limit_boundedSup {β : Ordinal.{u}} (h : IsLimit β) : β ≈ boundedSup β fun a => a := by
  have e₁ : lim β.size = β := mk_eta β
  have e₂ : sup β.size = boundedSup β fun a => a := rfl
  have h' := ascending_sup_lim (f := β.size) h.2
  rw [e₁, e₂] at h'
  exact h'

/-- Rocq: `Operators.limit_boundedSup'`. -/
theorem limit_boundedSup' {β : Ordinal.{u}} (h₀ : 0 < β) (heq : β ≈ boundedSup β fun a => a) :
    IsLimit β :=
  ⟨(lt_elim h₀).elim fun b _ => ⟨b⟩, fun a =>
    let ⟨⟨x, o⟩, hle⟩ := lt_elim (le_elim heq.le a)
    ⟨x, lt_intro o hle⟩⟩

/-- Rocq: `Operators.zeroOrdinal_mor`. -/
theorem IsZero.congr {x y : Ordinal.{u}} (h : x ≈ y) (hx : IsZero x) : IsZero y :=
  (isZero_iff y).2 (equiv_trans (equiv_symm h) ((isZero_iff x).1 hx))

/-- Rocq: `Operators.succOrdinal_mor`. -/
theorem IsSucc.congr {x y : Ordinal.{u}} (h : x ≈ y) (hx : IsSucc x) : IsSucc y :=
  (isSucc_iff y).2 (let ⟨o, ho⟩ := (isSucc_iff x).1 hx; ⟨o, equiv_trans (equiv_symm h) ho⟩)

/-- Rocq: `Operators.limitOrdinal_mor`. -/
theorem IsLimit.congr {x y : Ordinal.{u}} (h : x ≈ y) (hx : IsLimit x) : IsLimit y :=
  let ⟨h₀, hl⟩ := (isLimit_iff x).1 hx
  (isLimit_iff y).2 ⟨lt_of_lt_of_le h₀ h.le, fun i hi =>
    let ⟨j, hj₁, hj₂⟩ := hl i (lt_of_lt_of_le hi h.ge)
    ⟨j, hj₁, lt_of_lt_of_le hj₂ h.le⟩⟩

/-! ## Predecessor -/

/-- `pred y` is above every ordinal strictly below `y`… Rocq: `Operators.pred_le`. -/
theorem pred_le {x y : Ordinal.{u}} (h : x < y) : x ≤ pred y := by
  obtain ⟨b, hb⟩ := lt_elim h
  ord_rw [hb]
  exact sup_le y.size b

/-- …and is the least such. Rocq: `Operators.pred_least`. -/
theorem pred_least {y z : Ordinal.{u}} (h : ∀ x, x < y → x ≤ z) : pred y ≤ z :=
  sup_least fun a => h _ (index_lt y a)

/-- Rocq: `Operators.pred_zero`. -/
theorem pred_zero : (0 : Ordinal.{u}) ≈ pred 0 :=
  equiv_intro (zero_least _) (pred_least fun x hx => (zero_lt x hx).elim)

/-- Rocq: `Operators.pred_successor`. -/
theorem pred_successor {x : Ordinal.{u}} (h : IsSucc x) : pred x < x :=
  let ⟨a, ha⟩ := h
  lt_intro a (sup_least ha)

/-- Rocq: `Operators.pred_limit`. -/
theorem pred_limit {x : Ordinal.{u}} (h : IsLimit x) : x ≈ pred x :=
  equiv_intro
    (le_intro fun a => by
      obtain ⟨a', ha'⟩ := h.2 a
      rw [pred_unfold]
      ord_rw [← sup_le x.size a']
      exact ha')
    (pred_least fun _ => le_of_lt)

/-- Rocq: `Operators.pred_succ`. -/
theorem pred_succ (x : Ordinal.{u}) : x ≈ pred (succ x) :=
  equiv_intro (pred_le (succ_lt x)) (pred_least fun _ hy => (lt_elim hy).elim fun _ h => h)

/-- Rocq: `Operators.succ_pred`. -/
theorem succ_pred (x : Ordinal.{u}) : x ≤ succ (pred x) :=
  le_intro fun a => lt_intro PUnit.unit (pred_le (index_lt x a))

/-- Rocq: `Operators.succ_pred'`. -/
theorem succ_pred' {x : Ordinal.{u}} (h : IsSucc x) : x ≈ succ (pred x) :=
  equiv_intro (succ_pred x) (succ_least (pred_successor h))

/-- Rocq: `Operators.pred_le_mor`. -/
@[ord_mono]
theorem pred_monotone {x y : Ordinal.{u}} (h : x ≤ y) : pred x ≤ pred y :=
  pred_least fun _ hz => pred_le (lt_of_lt_of_le hz h)

/-- Rocq: `Operators.pred_eq_mor`. -/
theorem pred_congr {x y : Ordinal.{u}} (h : x ≈ y) : pred x ≈ pred y :=
  equiv_intro (pred_monotone h.le) (pred_monotone h.ge)

/-! ## Greatest lower bounds -/

/-- Rocq: `Operators.glb_le1`. -/
theorem glb_le1 : ∀ x y : Ordinal.{u}, x ⊓ y ≤ x
  | mk A f, mk B g => le_intro fun p =>
    lt_intro (show (mk A f).Carrier from p.1) (glb_le1 (f p.1) (g p.2))

/-- Rocq: `Operators.glb_le2`. -/
theorem glb_le2 : ∀ y x : Ordinal.{u}, x ⊓ y ≤ y
  | mk B g, mk A f => le_intro fun p =>
    lt_intro (show (mk B g).Carrier from p.2) (glb_le2 (g p.2) (f p.1))

/-- `⊓` is the greatest lower bound. Rocq: `Operators.glb_greatest`. -/
theorem glb_greatest : ∀ z x y : Ordinal.{u}, z ≤ x → z ≤ y → z ≤ x ⊓ y
  | mk C h, mk A f, mk B g, hx, hy => le_intro fun c => by
    obtain ⟨a, ha⟩ := lt_elim (le_elim hx c)
    obtain ⟨b, hb⟩ := lt_elim (le_elim hy c)
    exact lt_intro (show (mk A f ⊓ mk B g).Carrier from (a, b)) (glb_greatest (h c) (f a) (g b) ha hb)

/-- Rocq: `Operators.glb_complete`. -/
theorem glb_complete : ∀ x y : Ordinal.{u}, Complete x → Complete y → Complete (x ⊓ y)
  | mk X f, mk Y g, hx, hy => by
    obtain ⟨hx₁, hx₂, hx₃⟩ := hx.elim
    obtain ⟨hy₁, hy₂, hy₃⟩ := hy.elim
    refine Complete.intro ?_ ?_ ?_
    · intro p₁ p₂
      obtain ⟨x', hx'₁, hx'₂⟩ := hx₁ p₁.1 p₂.1
      obtain ⟨y', hy'₁, hy'₂⟩ := hy₁ p₁.2 p₂.2
      exact ⟨(x', y'),
        glb_greatest _ _ _ (le_trans (glb_le1 _ _) hx'₁) (le_trans (glb_le2 _ _) hy'₁),
        glb_greatest _ _ _ (le_trans (glb_le1 _ _) hx'₂) (le_trans (glb_le2 _ _) hy'₂)⟩
    · match hx₂, hy₂ with
      | .inl ⟨x⟩, .inl ⟨y⟩ => exact .inl ⟨(x, y)⟩
      | .inl _, .inr hy₂ => exact .inr fun ⟨p⟩ => hy₂ ⟨p.2⟩
      | .inr hx₂, _ => exact .inr fun ⟨p⟩ => hx₂ ⟨p.1⟩
    · intro p
      exact glb_complete (f p.1) (g p.2) (hx₃ p.1) (hy₃ p.2)

/-- Rocq: `Operators.ord_glb_le_mor`. -/
@[ord_mono]
theorem glb_monotone {x x' y y' : Ordinal.{u}} (hx : x ≤ x') (hy : y ≤ y') : x ⊓ y ≤ x' ⊓ y' :=
  glb_greatest _ _ _ (le_trans (glb_le1 x y) hx) (le_trans (glb_le2 y x) hy)

/-- Rocq: `Operators.ord_glb_eq_mor`. -/
theorem glb_congr {x x' y y' : Ordinal.{u}} (hx : x ≈ x') (hy : y ≈ y') : x ⊓ y ≈ x' ⊓ y' :=
  equiv_intro (glb_monotone hx.le hy.le) (glb_monotone hx.ge hy.ge)

/-! ## Least upper bounds -/

/-- Rocq: `Operators.lub_le1`. -/
@[ord_hint]
theorem lub_le1 (x y : Ordinal.{u}) : x ≤ x ⊔ y :=
  le_intro fun a => lt_intro (show (x ⊔ y).Carrier from .inl a) (le_refl _)

/-- Rocq: `Operators.lub_le2`. -/
@[ord_hint]
theorem lub_le2 (x y : Ordinal.{u}) : y ≤ x ⊔ y :=
  le_intro fun a => lt_intro (show (x ⊔ y).Carrier from .inr a) (le_refl _)

/-- `⊔` is the least upper bound. Rocq: `Operators.lub_least`. -/
theorem lub_least {x y z : Ordinal.{u}} (hx : x ≤ z) (hy : y ≤ z) : x ⊔ y ≤ z :=
  le_intro fun
    | .inl a => le_elim hx a
    | .inr b => le_elim hy b

/-- Rocq: `Operators.lub_lt`. -/
theorem lub_lt {a b c : Ordinal.{u}} (h : a < b ⊔ c) : a < b ∨ a < c :=
  match lt_elim h with
  | ⟨.inl q, hq⟩ => .inl (lt_intro q hq)
  | ⟨.inr q, hq⟩ => .inr (lt_intro q hq)

/-- Rocq: `Operators.lub_le_comm`. -/
theorem lub_le_comm (x y : Ordinal.{u}) : x ⊔ y ≤ y ⊔ x :=
  lub_least (lub_le2 y x) (lub_le1 y x)

/-- Rocq: `Operators.lub_le_assoc1`. -/
theorem lub_le_assoc1 (x y z : Ordinal.{u}) : x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z :=
  lub_least (le_trans (lub_le1 x y) (lub_le1 _ z))
    (lub_least (le_trans (lub_le2 x y) (lub_le1 _ z)) (lub_le2 _ z))

/-- Rocq: `Operators.lub_le_assoc2`. -/
theorem lub_le_assoc2 (x y z : Ordinal.{u}) : (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z) :=
  lub_least (lub_least (lub_le1 x _) (le_trans (lub_le1 y z) (lub_le2 x _)))
    (le_trans (lub_le2 y z) (lub_le2 x _))

/-- Rocq: `Operators.lubOrd_monotone` and `Operators.ord_lub_le_mor`. -/
@[ord_mono]
theorem lub_monotone {a b c d : Ordinal.{u}} (hac : a ≤ c) (hbd : b ≤ d) : a ⊔ b ≤ c ⊔ d :=
  lub_least (le_trans hac (lub_le1 c d)) (le_trans hbd (lub_le2 c d))

/-- Rocq: `Operators.ord_lub_eq_mor`. -/
theorem lub_congr {a b c d : Ordinal.{u}} (hac : a ≈ c) (hbd : b ≈ d) : a ⊔ b ≈ c ⊔ d :=
  equiv_intro (lub_monotone hac.le hbd.le) (lub_monotone hac.ge hbd.ge)

/-- Rocq: `Operators.lub_binary_sup` (with `ULift Bool` for Rocq's `bool`). -/
theorem lub_binary_sup (a b : Ordinal.{u}) :
    a ⊔ b ≈ sup fun i : ULift.{u} Bool => cond i.down a b :=
  equiv_intro
    (lub_least (sup_le (fun i : ULift.{u} Bool => cond i.down a b) ⟨true⟩)
      (sup_le (fun i : ULift.{u} Bool => cond i.down a b) ⟨false⟩))
    (sup_least fun
      | ⟨true⟩ => lub_le1 a b
      | ⟨false⟩ => lub_le2 a b)

/-- Rocq: `Operators.lub_continuous`. -/
theorem lub_continuous {f : Ordinal.{u} → Ordinal.{u}} (a b : Ordinal.{u})
    (hmono : ∀ a b, a ≤ b → f a ≤ f b) (hcont : StronglyContinuous f) :
    f (a ⊔ b) ≈ f a ⊔ f b := by
  have h := lub_binary_sup a b
  refine equiv_trans (equiv_intro (hmono _ _ h.le) (hmono _ _ h.ge)) (equiv_intro ?_ ?_)
  · exact le_trans (hcont _ _ ⟨false⟩) (sup_least fun
      | ⟨true⟩ => lub_le1 _ _
      | ⟨false⟩ => lub_le2 _ _)
  · exact lub_least
      (hmono _ _ (sup_le (fun i : ULift.{u} Bool => cond i.down a b) ⟨true⟩))
      (hmono _ _ (sup_le (fun i : ULift.{u} Bool => cond i.down a b) ⟨false⟩))

/-- The lub of successors is at most the successor of the lub.
Rocq: `Operators.succ_lub`. -/
theorem succ_lub (x y : Ordinal.{u}) : succ x ⊔ succ y ≤ succ (x ⊔ y) :=
  lub_least (succ_monotone (lub_le1 x y)) (succ_monotone (lub_le2 x y))

/-- A family indexed by a sum, bounded by its left part. -/
private theorem lub_left_bound {x y : Ordinal.{u}} (hxy : y ≤ x) (a : (x ⊔ y).Carrier) :
    ∃ a₀ : x.Carrier, (x ⊔ y) a ≤ x a₀ :=
  match a with
  | .inl a => ⟨a, le_refl _⟩
  | .inr b => le_subord hxy b

private theorem lub_right_bound {x y : Ordinal.{u}} (hxy : x ≤ y) (a : (x ⊔ y).Carrier) :
    ∃ b₀ : y.Carrier, (x ⊔ y) a ≤ y b₀ :=
  match a with
  | .inl a => le_subord hxy a
  | .inr b => ⟨b, le_refl _⟩

/-- Rocq: `Operators.lub_complete1`. -/
theorem lub_complete1 {x y : Ordinal.{u}} (hxy : y ≤ x) (hx : Complete x) (hy : Complete y) :
    Complete (x ⊔ y) := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx.elim
  refine Complete.intro ?_ ?_ ?_
  · intro a₁ a₂
    obtain ⟨b₁, h₁⟩ := lub_left_bound hxy a₁
    obtain ⟨b₂, h₂⟩ := lub_left_bound hxy a₂
    obtain ⟨x', hx'₁, hx'₂⟩ := hx₁ b₁ b₂
    exact ⟨.inl x', le_trans h₁ hx'₁, le_trans h₂ hx'₂⟩
  · match hx₂ with
    | .inl ⟨a⟩ => exact .inl ⟨.inl a⟩
    | .inr hn => exact .inr fun ⟨a⟩ => (lub_left_bound hxy a).elim fun b _ => hn ⟨b⟩
  · intro a
    match a with
    | .inl a => exact hx₃ a
    | .inr b => exact complete_subord hy b

/-- Rocq: `Operators.lub_complete2`. -/
theorem lub_complete2 {x y : Ordinal.{u}} (hxy : x ≤ y) (hx : Complete x) (hy : Complete y) :
    Complete (x ⊔ y) := by
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy.elim
  refine Complete.intro ?_ ?_ ?_
  · intro a₁ a₂
    obtain ⟨b₁, h₁⟩ := lub_right_bound hxy a₁
    obtain ⟨b₂, h₂⟩ := lub_right_bound hxy a₂
    obtain ⟨y', hy'₁, hy'₂⟩ := hy₁ b₁ b₂
    exact ⟨.inr y', le_trans h₁ hy'₁, le_trans h₂ hy'₂⟩
  · match hy₂ with
    | .inl ⟨b⟩ => exact .inl ⟨.inr b⟩
    | .inr hn => exact .inr fun ⟨a⟩ => (lub_right_bound hxy a).elim fun b _ => hn ⟨b⟩
  · intro a
    match a with
    | .inl a => exact complete_subord hx a
    | .inr b => exact hy₃ b

/-- Rocq: `Operators.lim_complete`. -/
theorem lim_complete {A : Type u} {f : A → Ordinal.{u}} (h₁ : ∀ a, Complete (f a))
    (h₂ : Directed A f) (h₃ : Nonempty A ∨ ¬Nonempty A) : Complete (lim f) :=
  Complete.intro h₂ h₃ h₁

/-- Rocq: `Operators.sup_complete`. -/
theorem sup_complete {A : Type u} {f : A → Ordinal.{u}} (h₁ : ∀ a, Complete (f a))
    (h₂ : Directed A f) (h₃ : (∃ a, 0 < f a) ∨ ∀ a, f a ≤ 0) : Complete (sup f) := by
  refine Complete.intro ?_ ?_ ?_
  · intro p₁ p₂
    obtain ⟨a', ha₁, ha₂⟩ := h₂ p₁.1 p₂.1
    obtain ⟨q₁, hq₁⟩ := le_subord ha₁ p₁.2
    obtain ⟨q₂, hq₂⟩ := le_subord ha₂ p₂.2
    obtain ⟨q', hq'₁, hq'₂⟩ := complete_directed (h₁ a') q₁ q₂
    exact ⟨⟨a', q'⟩, le_trans hq₁ hq'₁, le_trans hq₂ hq'₂⟩
  · match h₃ with
    | .inl ⟨a, ha⟩ => exact .inl ((lt_elim ha).elim fun q _ => ⟨⟨a, q⟩⟩)
    | .inr h => exact .inr fun ⟨p⟩ => (le_subord (h p.1) p.2).elim fun b _ => PEmpty.elim b
  · intro p
    exact complete_subord (h₁ p.1) p.2

/-! ## Successor-unreachable ordinals -/

/-- Rocq: `Operators.succ_unreachable`. -/
def SuccUnreachable (x : Ordinal.{u}) : Prop := ∀ a, a < x → succ a < x

/-- Rocq: `Operators.succ_unreachable_eq_mor`. -/
theorem SuccUnreachable.congr {x y : Ordinal.{u}} (h : x ≈ y) (hx : SuccUnreachable x) :
    SuccUnreachable y := fun i hi =>
  lt_of_lt_of_le (hx i (lt_of_lt_of_le hi h.ge)) h.le

/-- Rocq: `Operators.zero_succ_unreachable`. -/
theorem zero_succ_unreachable : SuccUnreachable (0 : Ordinal.{u}) := fun a ha =>
  (zero_lt a ha).elim

/-- Rocq: `Operators.limit_unreachable`. -/
theorem limit_unreachable {y : Ordinal.{u}} (h : IsLimit y) : SuccUnreachable y := fun x hxy =>
  let ⟨_, hlim⟩ := (isLimit_iff y).1 h
  let ⟨q, hq₁, hq₂⟩ := hlim x hxy
  lt_of_le_of_lt (succ_least hq₁) hq₂

/-- Rocq: `Operators.unreachable_limit`. -/
theorem unreachable_limit {y : Ordinal.{u}} (h₀ : 0 < y) (hu : SuccUnreachable y) : IsLimit y :=
  (isLimit_iff y).2 ⟨h₀, fun i hi => ⟨succ i, succ_lt i, hu i hi⟩⟩

end Ordinal

end ConstructiveOrdinals
