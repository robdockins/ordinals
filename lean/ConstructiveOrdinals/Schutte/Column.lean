import ConstructiveOrdinals.Veblen.Facts

/-!
# Schütte columns

`schutteColumn f β α x` is a three-argument hierarchy that extends the
two-argument Veblen hierarchy by one more column of Schütte's Klammersymbole.
For `β = 0` it is `f (α + x)`. For larger `β`, its fixpoints are closed under
`schutteColumn (schutteColumn f β α') β' · 0` for `β' < β` and `α' < α`.

The Rocq definition nests three `fix`es (on `β`, `α` and `x`), and the inner
recursion on `α` supplies the base function of the outer recursive call. In
Lean the two inner recursions are separate functions, parameterised by the
outer recursive calls `outer b g = schutteColumn g (β b)`.
`schutte_column_unroll` gives the characteristic equation, and
`schutteColumn` is then made irreducible.

Ported from the Rocq file `SchutteColumn.v`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-- The innermost recursion of `schutteColumn`, on `x`. -/
def schutteColumnX (f : Ordinal.{u} → Ordinal.{u}) {B A : Type u}
    (outer : B → (Ordinal.{u} → Ordinal.{u}) → Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (α : Ordinal.{u}) (innerα : A → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk X fx => f (α + mk X fx) ⊔ sup fun b : B => sup fun a : A =>
      fixOrd (fun δ => outer b (innerα a) δ 0) (mk X fun i => schutteColumnX f outer α innerα (fx i))

/-- The middle recursion of `schutteColumn`, on `α`. -/
def schutteColumnα (f : Ordinal.{u} → Ordinal.{u}) {B : Type u}
    (outer : B → (Ordinal.{u} → Ordinal.{u}) → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) :
    Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | mk A fa => schutteColumnX f outer (mk A fa) fun a => schutteColumnα f outer (fa a)

/-- Rocq: `SchutteColumn.schutte_column`. -/
def schutteColumn : (Ordinal.{u} → Ordinal.{u}) → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | f, mk _ fb => schutteColumnα f fun b g => schutteColumn g (fb b)

/-- Rocq: `SchutteColumn.schutte_column_unroll`. -/
theorem schutte_column_unroll (f : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u}) :
    schutteColumn f β α x =
      f (α + x) ⊔ sup fun b : β => sup fun a : α =>
        fixOrd (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0)
          (lim fun i : x => schutteColumn f β α (x i)) := by
  cases β; cases α; cases x; rfl

attribute [irreducible] schutteColumn

/-- Rocq: `SchutteColumn.schutte_column0`. -/
theorem schutte_column0 (f : Ordinal.{u} → Ordinal.{u}) (α x : Ordinal.{u}) :
    schutteColumn f 0 α x ≈ f (α + x) := by
  rw [schutte_column_unroll]
  exact equiv_intro (lub_least (le_refl _) (sup_least fun e => PEmpty.elim e)) (lub_le1 _ _)

/-- Rocq: `SchutteColumn.proper_le_eq`. -/
theorem proper_le_eq (f : Ordinal.{u} → Ordinal.{u}) (h : ∀ x y, x ≤ y → f x ≤ f y) (x y : Ordinal.{u})
    (hxy : x ≈ y) : f x ≈ f y :=
  equiv_intro (h x y hxy.le) (h y x hxy.ge)

/-- Rocq: `SchutteColumn.schutte_column00`. -/
theorem schutte_column00 (f : Ordinal.{u} → Ordinal.{u}) (α : Ordinal.{u})
    (h : ∀ x y, x ≈ y → f x ≈ f y) : schutteColumn f 0 α 0 ≈ f α :=
  equiv_trans (schutte_column0 f α 0) (h _ _ (add_zero α))

/-- Rocq: `SchutteColumn.iter_f_monotone_func'`. -/
theorem iterF_monotone_func' {f g : Ordinal.{u} → Ordinal.{u}} (hfg : ∀ x, f x ≤ g x)
    (hf : ∀ x y, x ≤ y → f x ≤ f y) : ∀ (n : Nat) (x : Ordinal.{u}), iterF f x n ≤ iterF g x n
  | 0, _ => le_refl _
  | n + 1, x => le_trans (hf _ _ (iterF_monotone_func' hfg hf n x)) (hfg _)

/-- Rocq: `SchutteColumn.fixOrd_monotone_func'`. -/
theorem fixOrd_monotone_func' {f g : Ordinal.{u} → Ordinal.{u}} (hfg : ∀ x, f x ≤ g x)
    (hf : ∀ x y, x ≤ y → f x ≤ f y) (x : Ordinal.{u}) : fixOrd f x ≤ fixOrd g x :=
  sup_monotone fun n => iterF_monotone_func' hfg hf n.down x

/-- Rocq: `SchutteColumn.fixOrd_monotone_full`. -/
theorem fixOrd_monotone_full {f g : Ordinal.{u} → Ordinal.{u}} (hfg : ∀ x, f x ≤ g x)
    (hf : ∀ x y, x ≤ y → f x ≤ f y) {x y : Ordinal.{u}} (hxy : x ≤ y) : fixOrd f x ≤ fixOrd g y :=
  le_trans (fixOrd_monotone hf hxy) (fixOrd_monotone_func' hfg hf y)

/-- Rocq: `SchutteColumn.iter_f_monotone_func''`. -/
theorem iterF_monotone_func'' {f g : Ordinal.{u} → Ordinal.{u}} (hfg : ∀ x, Complete x → f x ≤ g x)
    (hg : ∀ x, Complete x → Complete (g x)) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ (n : Nat) (x : Ordinal.{u}), Complete x → iterF f x n ≤ iterF g x n
  | 0, _, _ => le_refl _
  | n + 1, x, hx =>
    le_trans (hf _ _ (iterF_monotone_func'' hfg hg hf n x hx)) (hfg _ (iterF_complete n x hx hg))

/-- Rocq: `SchutteColumn.fixOrd_monotone_func''`. -/
theorem fixOrd_monotone_func'' {f g : Ordinal.{u} → Ordinal.{u}} (hfg : ∀ x, Complete x → f x ≤ g x)
    (hg : ∀ x, Complete x → Complete (g x)) (hf : ∀ x y, x ≤ y → f x ≤ f y) (x : Ordinal.{u})
    (hx : Complete x) : fixOrd f x ≤ fixOrd g x :=
  sup_monotone fun n => iterF_monotone_func'' hfg hg hf n.down x hx

/-- Rocq: `SchutteColumn.fixOrd_monotone_full'`. -/
theorem fixOrd_monotone_full' {f g : Ordinal.{u} → Ordinal.{u}} (hfg : ∀ x, Complete x → f x ≤ g x)
    (hg : ∀ x, Complete x → Complete (g x)) (hf : ∀ x y, x ≤ y → f x ≤ f y) {x y : Ordinal.{u}}
    (hy : Complete y) (hxy : x ≤ y) : fixOrd f x ≤ fixOrd g y :=
  le_trans (fixOrd_monotone hf hxy) (fixOrd_monotone_func'' hfg hg hf y hy)

/-- Rocq: `SchutteColumn.schutte_column_monotone_αx`. -/
theorem schutte_column_monotone_αx (β : Ordinal.{u}) :
    ∀ (α : Ordinal.{u}) (f g : Ordinal.{u} → Ordinal.{u}),
      (∀ a b, a ≤ b → f a ≤ f b) → (∀ a b, a ≤ b → g a ≤ g b) → (∀ a, f a ≤ g a) →
      (∀ α' x, α' ≤ α → schutteColumn f β α' x ≤ schutteColumn g β α x) ∧
      (∀ x x', x ≤ x' → schutteColumn f β α x ≤ schutteColumn f β α x') := by
  induction β using ltRec with
  | ind β ihβ =>
  intro α
  induction α using ltRec with
  | ind α ihα =>
  intro f g hf hg hfg
  -- monotonicity of the inner function `δ ↦ schutteColumn h (β b) δ 0`
  have hinner : ∀ (b : β) (h : Ordinal.{u} → Ordinal.{u}), (∀ a b, a ≤ b → h a ≤ h b) →
      ∀ p p', p ≤ p' → schutteColumn h (β b) p 0 ≤ schutteColumn h (β b) p' 0 :=
    fun b h hh p p' hp => (ihβ (β b) (index_lt β b) p' h h hh hh (fun _ => le_refl _)).1 p 0 hp
  refine ⟨fun α' x => ?_, fun x => ?_⟩
  · induction x using ltRec with
    | ind x ihx =>
    intro hα
    rw [schutte_column_unroll f β α' x, schutte_column_unroll g β α x]
    refine lub_least (le_trans (hfg _) (le_trans (hg _ _ (add_le_add hα (le_refl x))) (lub_le1 _ _)))
      (sup_least fun b => sup_least fun a => ?_)
    obtain ⟨a', ha'⟩ := le_subord hα a
    have hlt : α' a < α := lt_of_lt_of_le (index_lt α' a) hα
    have hmF := (ihα (α' a) hlt f f hf hf (fun _ => le_refl _)).2
    have hmG := (ihα (α a') (index_lt α a') g g hg hg (fun _ => le_refl _)).2
    refine le_trans ?_ (le_trans (sup_le _ b) (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun a : α => fixOrd (fun δ => schutteColumn (schutteColumn g β (α a)) (β b) δ 0)
      (lim fun i : x => schutteColumn g β α (x i))) a')
    refine fixOrd_monotone_full (fun p => ?_) (hinner b _ hmF) (lim_monotone fun i => ihx (x i) (index_lt x i) hα)
    exact (ihβ (β b) (index_lt β b) p _ _ hmF hmG
      (fun z => (ihα (α a') (index_lt α a') f g hf hg hfg).1 (α' a) z ha')).1 p 0 (le_refl p)
  · induction x using ltRec with
    | ind x ihx =>
    intro x' hx
    rw [schutte_column_unroll f β α x, schutte_column_unroll f β α x']
    refine lub_least (le_trans (hf _ _ (add_le_add (le_refl α) hx)) (lub_le1 _ _))
      (sup_least fun b => sup_least fun a => ?_)
    refine le_trans ?_ (le_trans (sup_le _ b) (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun a : α => fixOrd (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0)
      (lim fun i : x' => schutteColumn f β α (x' i))) a)
    refine fixOrd_monotone (hinner b _ (ihα (α a) (index_lt α a) f f hf hf (fun _ => le_refl _)).2) ?_
    exact limit_least fun i =>
      let ⟨i', hi'⟩ := le_subord hx i
      lt_of_le_of_lt (ihx (x i) (index_lt x i) (x' i') hi')
        (limit_lt (fun i : x' => schutteColumn f β α (x' i)) i')

/-- Rocq: `SchutteColumn.schutte_column_monotone`. -/
theorem schutte_column_monotone (f : Ordinal.{u} → Ordinal.{u}) (β α x α' x' : Ordinal.{u})
    (hf : ∀ a b, a ≤ b → f a ≤ f b) (hα : α ≤ α') (hx : x ≤ x') :
    schutteColumn f β α x ≤ schutteColumn f β α' x' :=
  le_trans ((schutte_column_monotone_αx β α f f hf hf (fun _ => le_refl _)).2 x x' hx)
    ((schutte_column_monotone_αx β α' f f hf hf (fun _ => le_refl _)).1 α x' hα)

/-- Rocq: `SchutteColumn.schutte_column_monotone_func`. -/
theorem schutte_column_monotone_func (f g : Ordinal.{u} → Ordinal.{u}) (β α x α' x' : Ordinal.{u})
    (hf : ∀ a b, a ≤ b → f a ≤ f b) (hg : ∀ a b, a ≤ b → g a ≤ g b) (hfg : ∀ a, f a ≤ g a)
    (hα : α ≤ α') (hx : x ≤ x') : schutteColumn f β α x ≤ schutteColumn g β α' x' :=
  le_trans ((schutte_column_monotone_αx β α f f hf hf (fun _ => le_refl _)).2 x x' hx)
    ((schutte_column_monotone_αx β α' f g hf hg hfg).1 α x' hα)

/-- Rocq: `SchutteColumn.schutte_column_monotoneβ`. -/
theorem schutte_column_monotoneβ (β₁ : Ordinal.{u}) :
    ∀ (β₂ α x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}), (∀ a b, a ≤ b → f a ≤ f b) → β₁ ≤ β₂ →
      schutteColumn f β₁ α x ≤ schutteColumn f β₂ α x := by
  induction β₁ using ltRec with
  | ind β₁ ih =>
  intro β₂ α
  induction α using ltRec with
  | ind α ihα =>
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro f hf hβ
  rw [schutte_column_unroll f β₁ α x, schutte_column_unroll f β₂ α x]
  refine lub_least (lub_le1 _ _) (sup_least fun b₁ => sup_least fun a => ?_)
  obtain ⟨b₂, hb₂⟩ := le_subord hβ b₁
  have hm₁ : ∀ p q, p ≤ q → schutteColumn f β₁ (α a) p ≤ schutteColumn f β₁ (α a) q :=
    fun _ _ h => schutte_column_monotone f _ _ _ _ _ hf (le_refl _) h
  have hm₂ : ∀ p q, p ≤ q → schutteColumn f β₂ (α a) p ≤ schutteColumn f β₂ (α a) q :=
    fun _ _ h => schutte_column_monotone f _ _ _ _ _ hf (le_refl _) h
  refine le_trans ?_ (le_trans (sup_le _ b₂) (lub_le2 _ _))
  refine le_trans ?_ (sup_le (fun a : α => fixOrd (fun δ => schutteColumn (schutteColumn f β₂ (α a)) (β₂ b₂) δ 0)
    (lim fun i : x => schutteColumn f β₂ α (x i))) a)
  refine fixOrd_monotone_full (fun p => ?_)
    (fun p p' h => schutte_column_monotone _ _ _ _ _ _ hm₁ h (le_refl 0))
    (lim_monotone fun i => ihx (x i) (index_lt x i) f hf hβ)
  exact le_trans (schutte_column_monotone_func _ _ _ _ _ _ _ hm₁ hm₂
      (fun z => ihα (α a) (index_lt α a) z f hf hβ) (le_refl p) (le_refl 0))
    (ih (β₁ b₁) (index_lt β₁ b₁) (β₂ b₂) p 0 _ hm₂ hb₂)

/-- Rocq: `SchutteColumn.schutte_column_monotone_full`. -/
theorem schutte_column_monotone_full (f g : Ordinal.{u} → Ordinal.{u}) (β α x β' α' x' : Ordinal.{u})
    (hf : ∀ a b, a ≤ b → f a ≤ f b) (hg : ∀ a b, a ≤ b → g a ≤ g b) (hfg : ∀ a, f a ≤ g a)
    (hβ : β ≤ β') (hα : α ≤ α') (hx : x ≤ x') : schutteColumn f β α x ≤ schutteColumn g β' α' x' :=
  le_trans (schutte_column_monotoneβ β β' α x f hf hβ) (schutte_column_monotone_func f g β' α x α' x' hf hg hfg hα hx)

/-- Rocq: `SchutteColumn.schutte_column_le_f`. -/
theorem schutte_column_le_f (β α x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u})
    (_hf : ∀ a b, a ≤ b → f a ≤ f b) : f (α + x) ≤ schutteColumn f β α x := by
  rw [schutte_column_unroll]; exact lub_le1 _ _

/-- Rocq: `SchutteColumn.schutte_column_arg0`. -/
theorem schutte_column_arg0 (β x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ a b, a ≤ b → f a ≤ f b) : schutteColumn f β 0 x ≈ f x := by
  rw [schutte_column_unroll]
  exact equiv_intro (lub_least (hf _ _ (zero_add x).le) (sup_least fun _ => sup_least fun e => PEmpty.elim e))
    (le_trans (hf _ _ (zero_add x).ge) (lub_le1 _ _))

/-- Rocq: `SchutteColumn.supOrd_succ`. -/
theorem sup_succ (f : Ordinal.{u} → Ordinal.{u}) (α : Ordinal.{u}) :
    (sup fun x : (succ α).Carrier => f (succ α x)) ≈ f α :=
  equiv_intro (sup_least fun _ => le_refl _) (sup_le (fun x : (succ α).Carrier => f (succ α x)) PUnit.unit)

/-- Rocq: `SchutteColumn.schutte_column0_complete`. -/
theorem schutte_column0_complete (β α x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x, Complete x → Complete (f x)) (hβ : β ≤ 0) (hα : Complete α) (hx : Complete x) :
    Complete (schutteColumn f β α x) := by
  have hne : ∀ b : β, False := fun b => zero_lt _ (lt_of_lt_of_le (index_lt β b) hβ)
  rw [schutte_column_unroll]
  exact lub_complete1 (sup_least fun b => (hne b).elim) (hf _ (add_complete hα hx))
    (sup_complete (fun b => (hne b).elim) (fun b _ => (hne b).elim) (.inr fun b => (hne b).elim))

/-- Rocq: `SchutteColumn.schutte_column_nonzero`. -/
theorem schutte_column_nonzero (f : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u}) (hf : NormalFunction f) :
    0 < schutteColumn f β α x := by
  rw [schutte_column_unroll]; exact lt_of_lt_of_le (hf.nonzero _) (lub_le1 _ _)

/-- Addition on the left of a nonzero complete ordinal is normal.
Rocq: `SchutteColumn.normal_addOrd`. -/
theorem normal_addOrd (x : Ordinal.{u}) (hx : Complete x) (hx₀ : 0 < x) : NormalFunction (x + ·) where
  monotone _ _ h := add_le_add (le_refl x) h
  increasing _ _ _ h := add_lt_add_left x h
  continuous := by
    intro A f a₀ _ _
    show x + sup f ≤ sup fun i => x + f i
    rw [add_unfold]
    refine lub_least (le_trans (le_add_right x (f a₀)) (sup_le (fun i => x + f i) a₀)) ?_
    rw [sup_unfold f]
    exact sup_least fun ⟨i, j⟩ => le_trans (succ_least (add_lt_add_left x (index_lt (f i) j)))
      (sup_le (fun i => x + f i) i)
  complete _ h := add_complete hx h
  nonzero y := lt_of_lt_of_le hx₀ (le_add_right x y)

/-- Elimination for `z < schutteColumn f β α x`. Rocq: `SchutteColumn.schutte_column_ltE`. -/
theorem schutte_column_ltE {z : Ordinal.{u}} {f : Ordinal.{u} → Ordinal.{u}} {β α x : Ordinal.{u}}
    (h : z < schutteColumn f β α x) (R : Prop) (h₁ : z < f (α + x) → R)
    (h₂ : ∀ (b : β) (a : α), z < fixOrd (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0)
      (lim fun i : x => schutteColumn f β α (x i)) → R) : R := by
  rw [schutte_column_unroll] at h
  match lub_lt h with
  | .inl h => exact h₁ h
  | .inr h =>
    obtain ⟨b, h⟩ := sup_lt h
    obtain ⟨a, h⟩ := sup_lt h
    exact h₂ b a h

/-- Rocq: `SchutteColumn.schutte_column_increasing`. -/
theorem schutte_column_increasing (β α y x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hβ : Complete β) (hα : Complete α) (hy : Complete y) (hxy : x < y) :
    schutteColumn f β α x < schutteColumn f β α y := by
  have hbase : (∀ (b : β) (a : α), False) →
      schutteColumn f β α x < schutteColumn f β α y := fun hne => by
    refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (hf.increasing _ _ (add_complete hα hy) (add_lt_add_left α hxy))
      (schutte_column_le_f β α y f hf.monotone))
    rw [schutte_column_unroll]
    exact lub_least (le_refl _) (sup_least fun b => sup_least fun a => (hne b a).elim)
  match complete_zeroDec hβ, complete_zeroDec hα with
  | .inl hβ₀, _ => exact hbase fun b _ => zero_lt _ (lt_of_lt_of_le (index_lt β b) hβ₀)
  | _, .inl hα₀ => exact hbase fun _ a => zero_lt _ (lt_of_lt_of_le (index_lt α a) hα₀)
  | .inr hβ₀, .inr hα₀ =>
    obtain ⟨y', hy'⟩ := lt_elim hxy
    obtain ⟨b₀, _⟩ := lt_elim hβ₀
    obtain ⟨a₀, _⟩ := lt_elim hα₀
    refine lt_of_le_of_lt (schutte_column_monotone f β α x α (y y') hf.monotone (le_refl α) hy') ?_
    rw [schutte_column_unroll f β α y]
    refine lt_of_lt_of_le ?_ (le_trans (sup_le _ b₀) (lub_le2 _ _))
    refine lt_of_lt_of_le ?_ (sup_le (fun a : α => fixOrd (fun δ => schutteColumn (schutteColumn f β (α a)) (β b₀) δ 0)
      (lim fun i : y => schutteColumn f β α (y i))) a₀)
    exact lt_of_lt_of_le (limit_lt (fun i : y => schutteColumn f β α (y i)) y') (fixOrd_above _ _)

/-- Rocq: `SchutteColumn.schutte_column_inflationary1`. -/
theorem schutte_column_inflationary1 (β α x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x, Complete x → x ≤ f x) (hα : Complete α) (hx : Complete x) : α ≤ schutteColumn f β α x := by
  rw [schutte_column_unroll]
  exact le_trans (le_add_right α x) (le_trans (hf _ (add_complete hα hx)) (lub_le1 _ _))

/-- Rocq: `SchutteColumn.schutte_column_inflationary2`. -/
theorem schutte_column_inflationary2 (β α x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x, Complete x → x ≤ f x) (hα : Complete α) (hx : Complete x) : x ≤ schutteColumn f β α x := by
  rw [schutte_column_unroll]
  exact le_trans (le_add_left α x) (le_trans (hf _ (add_complete hα hx)) (lub_le1 _ _))


/-- The empty limit is below everything. -/
private theorem lim_zero_le {g : (0 : Ordinal.{u}).Carrier → Ordinal.{u}} (z : Ordinal.{u}) : lim g ≤ z :=
  limit_least fun e => PEmpty.elim e

private theorem lim_zero_complete {g : (0 : Ordinal.{u}).Carrier → Ordinal.{u}} : Complete (lim g) :=
  lim_complete (fun e => PEmpty.elim e) (fun e _ => PEmpty.elim e) (.inr fun ⟨e⟩ => PEmpty.elim e)

/-- `1 ≤ z + 0` for positive `z`. -/
private theorem one_le_add_zero {z : Ordinal.{u}} (h : 0 < z) : 1 ≤ z + 0 :=
  le_trans (succ_least h) (add_zero z).ge

section schutte_column_normal

variable (β : Ordinal.{u}) (hβ : Complete β)
  (hindβ1 : ∀ (f : Ordinal.{u} → Ordinal.{u}) (β' α : Ordinal.{u}), NormalFunction f → Complete β' → Complete α →
    β' < β → NormalFunction (schutteColumn f β' α))
  (hindβ2 : ∀ (f : Ordinal.{u} → Ordinal.{u}) (β' : Ordinal.{u}), NormalFunction f → Complete β' → β' < β →
    NormalFunction fun α => schutteColumn f β' α 0)
  (hindβ3 : ∀ (β' α b a x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}), β' < β → NormalFunction f → b < β' →
    a < α → Complete β' → Complete α → Complete b → Complete a → Complete x →
    schutteColumn (schutteColumn f β' a) b (schutteColumn f β' α x) 0 ≤ schutteColumn f β' α x)
  (α : Ordinal.{u}) (hα : Complete α)
  (hindα1 : ∀ (f : Ordinal.{u} → Ordinal.{u}) (α' : Ordinal.{u}), NormalFunction f → Complete α' → α' < α →
    NormalFunction (schutteColumn f β α'))

set_option hygiene false in
/-- The fixpoint in the unrolling of `schutteColumn f β α x`, for `b : β` and `a : α`. -/
local notation "Φ[" f ", " b ", " a ", " x "]" =>
  fixOrd (fun δδ => schutteColumn (schutteColumn f β (α a)) (β b) δδ 0)
    (lim fun ii : Ordinal.Carrier x => schutteColumn f β α (x ii))

set_option hygiene false in
local notation "L[" f ", " x "]" => lim fun ii : Ordinal.Carrier x => schutteColumn f β α (x ii)

set_option hygiene false in
local notation "S[" f ", " x "]" =>
  sup fun bb : Ordinal.Carrier β => sup fun aa : Ordinal.Carrier α => Φ[f, bb, aa, x]

include hβ hindβ1 hα hindα1

omit hβ hindβ1 in
private theorem normal_N {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) (a : α) :
    NormalFunction (schutteColumn f β (α a)) :=
  hindα1 f (α a) hf (complete_subord hα a) (index_lt α a)

omit hβ hindβ1 hα hindα1 in
private theorem G_mono {h : Ordinal.{u} → Ordinal.{u}} (hh : ∀ a b, a ≤ b → h a ≤ h b) (b' : Ordinal.{u}) :
    ∀ p q, p ≤ q → schutteColumn h b' p 0 ≤ schutteColumn h b' q 0 :=
  fun _ _ hpq => schutte_column_monotone h b' _ 0 _ 0 hh hpq (le_refl 0)

omit hα hindα1 in
private theorem G_complete {h : Ordinal.{u} → Ordinal.{u}} (hh : NormalFunction h) (b : β) :
    ∀ δ, Complete δ → Complete (schutteColumn h (β b) δ 0) :=
  fun δ hδ => (hindβ1 h (β b) δ hh (complete_subord hβ b) hδ (index_lt β b)).complete 0 zero_complete

omit hβ hindβ1 hα hindα1 in
private theorem G_infl {h : Ordinal.{u} → Ordinal.{u}} (hh : NormalFunction h) (b' : Ordinal.{u}) :
    ∀ δ, Complete δ → δ ≤ schutteColumn h b' δ 0 :=
  fun δ hδ => schutte_column_inflationary1 b' δ 0 h (normal_inflationary hh) hδ zero_complete

private theorem phi_complete {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {x : Ordinal.{u}}
    (hL : Complete L[f, x]) (b : β) (a : α) : Complete Φ[f, b, a, x] :=
  normal_fix_complete _ hL (G_infl (normal_N β α hα hindα1 hf a) _)
    (G_mono (normal_N β α hα hindα1 hf a).monotone _) (G_complete β hβ hindβ1 (normal_N β α hα hindα1 hf a) b)

omit hβ hindβ1 hα hindα1 in
private theorem phi_mono {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ a b, a ≤ b → f a ≤ f b) (x : Ordinal.{u})
    {b b' : β} {a a' : α} (hb : β b ≤ β b') (ha : α a ≤ α a') : Φ[f, b, a, x] ≤ Φ[f, b', a', x] :=
  fixOrd_monotone_func (fun δ => schutte_column_monotone_full _ _ _ δ 0 _ δ 0
      (fun _ _ h => schutte_column_monotone f β _ _ _ _ hf (le_refl _) h)
      (fun _ _ h => schutte_column_monotone f β _ _ _ _ hf (le_refl _) h)
      (fun z => schutte_column_monotone f β _ z _ z hf ha (le_refl z)) hb (le_refl δ) (le_refl 0))
    (G_mono (fun _ _ h => schutte_column_monotone f β _ _ _ _ hf (le_refl _) h) _) _

omit hβ hindβ1 in
private theorem phi_pos {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) (x : Ordinal.{u}) (b : β) (a : α) :
    0 < Φ[f, b, a, x] :=
  lt_of_lt_of_le (schutte_column_nonzero _ _ _ 0 (normal_N β α hα hindα1 hf a))
    (sup_le (fun n : ULift Nat => iterF (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0)
      L[f, x] n.down) ⟨1⟩)

private theorem sup_a_complete {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {x : Ordinal.{u}}
    (hL : Complete L[f, x]) (b : β) : Complete (sup fun a : α => Φ[f, b, a, x]) :=
  sup_complete (phi_complete β hβ hindβ1 α hα hindα1 hf hL b)
    (directed_monotone α _ (fun _ _ h => phi_mono β α hf.monotone x (le_refl _) h) hα)
    (match complete_zeroDec hα with
     | .inl h => .inr fun a => (zero_lt _ (lt_of_lt_of_le (index_lt α a) h)).elim
     | .inr h => let ⟨a, _⟩ := lt_elim h; .inl ⟨a, phi_pos β α hα hindα1 hf x b a⟩)

private theorem S_complete {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {x : Ordinal.{u}}
    (hL : Complete L[f, x]) : Complete S[f, x] :=
  sup_complete (sup_a_complete β hβ hindβ1 α hα hindα1 hf hL)
    (directed_monotone β _ (fun _ _ h => sup_monotone fun _ => phi_mono β α hf.monotone x h (le_refl _)) hβ)
    (match complete_zeroDec hβ, complete_zeroDec hα with
     | .inl h, _ => .inr fun b => (zero_lt _ (lt_of_lt_of_le (index_lt β b) h)).elim
     | _, .inl h => .inr fun _ => sup_least fun a => (zero_lt _ (lt_of_lt_of_le (index_lt α a) h)).elim
     | .inr hb, .inr ha =>
       let ⟨b, _⟩ := lt_elim hb
       let ⟨a, _⟩ := lt_elim ha
       .inl ⟨b, lt_of_lt_of_le (phi_pos β α hα hindα1 hf x b a)
         (sup_le (fun a : α => Φ[f, b, a, x]) a)⟩)

omit hβ hindβ1 hα hindα1 in
/-- `α + x ≤ L[f, x]` for positive `α` and `x`. -/
private theorem add_le_L {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {x : Ordinal.{u}} (hx : Complete x)
    (hα : Complete α) (hα₀ : 0 < α) (hx₀ : 0 < x) : α + x ≤ L[f, x] := by
  refine le_trans (normal_ord_decompose x (α + ·) hx hx₀ (normal_addOrd α hα hα₀)).le (sup_least fun j => ?_)
  refine le_trans (add_succ α (x j)).le (succ_least (lt_of_le_of_lt ?_
    (limit_lt (fun i : x => schutteColumn f β α (x i)) j)))
  exact le_trans (normal_inflationary hf _ (add_complete hα (complete_subord hx j)))
    (schutte_column_le_f β α (x j) f hf.monotone)

/-- Rocq: `SchutteColumn.veblen_gt0_column_complete`. -/
theorem veblen_gt0_column_complete :
    ∀ (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}), NormalFunction f → Complete x → 0 < β →
      (0 < α → f (α + x) ≤ S[f, x]) ∧ Complete (schutteColumn f β α x) := by
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro f hf hx hβ₀
  have hL : Complete L[f, x] :=
    lim_complete (fun i => (ihx (x i) (index_lt x i) f hf (complete_subord hx i) hβ₀).2)
      (directed_monotone x _ (fun _ _ h => schutte_column_monotone f β α _ α _ hf.monotone (le_refl α) h) hx)
      hx.elim.2.1
  have hS := S_complete β hβ hindβ1 α hα hindα1 hf hL
  obtain ⟨b, _⟩ := lt_elim hβ₀
  have hle : 0 < α → f (α + x) ≤ S[f, x] := by
    intro hα₀
    have hS_ge : ∀ a : α, ∀ z, z ≤ α a + (iterF (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0)
        L[f, x] 1 + 0) → f z ≤ S[f, x] := by
      intro a z hz
      refine le_trans (hf.monotone _ _ hz) ?_
      refine le_trans (schutte_column_le_f β (α a) _ f hf.monotone) ?_
      refine le_trans (schutte_column_le_f (β b) _ 0 _ (normal_N β α hα hindα1 hf a).monotone) ?_
      refine le_trans (sup_le (fun n : ULift Nat => iterF (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0)
        L[f, x] n.down) ⟨2⟩) ?_
      exact le_trans (sup_le (fun a : α => Φ[f, b, a, x]) a) (sup_le (fun b : β => sup fun a : α => Φ[f, b, a, x]) b)
    match complete_zeroDec hx with
    | .inl hx₀ =>
      refine le_trans (hf.monotone _ _ (le_trans (add_le_add (le_refl α) hx₀) (add_zero α).le)) ?_
      refine le_trans (normal_ord_decompose α f hα hα₀ hf).le (sup_least fun a => ?_)
      refine hS_ge a _ (le_trans (succ_le_add_one _) (add_le_add (le_refl _) (one_le_add_zero ?_)))
      exact schutte_column_nonzero _ _ _ 0 (normal_N β α hα hindα1 hf a)
    | .inr hx₀ =>
      obtain ⟨a, _⟩ := lt_elim hα₀
      refine le_trans ?_ (le_trans (sup_le (fun n : ULift Nat => iterF
        (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0) L[f, x] n.down) ⟨1⟩)
        (le_trans (sup_le (fun a : α => Φ[f, b, a, x]) a) (sup_le (fun b : β => sup fun a : α => Φ[f, b, a, x]) b)))
      refine le_trans (hf.monotone _ _ (le_trans (add_le_L β α hf hx hα hα₀ hx₀)
        (le_trans (add_zero _).ge (le_add_left (α a) _)))) ?_
      exact le_trans (schutte_column_le_f β (α a) _ f hf.monotone)
        (schutte_column_le_f (β b) _ 0 _ (normal_N β α hα hindα1 hf a).monotone)
  refine ⟨hle, ?_⟩
  rw [schutte_column_unroll]
  match complete_zeroDec hα with
  | .inl hα₀ =>
    exact lub_complete1 (sup_least fun _ => sup_least fun a => (zero_lt _ (lt_of_lt_of_le (index_lt α a) hα₀)).elim)
      (hf.complete _ (add_complete hα hx)) hS
  | .inr hα₀ => exact lub_complete2 (hle hα₀) (hf.complete _ (add_complete hα hx)) hS

/-- Rocq: `SchutteColumn.complete_lemma0`. -/
theorem complete_lemma0 (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (hx : Complete x) :
    Complete (schutteColumn f β α x) :=
  match complete_zeroDec hβ with
  | .inl h => schutte_column0_complete β α x f hf.complete h hα hx
  | .inr h => (veblen_gt0_column_complete β hβ hindβ1 α hα hindα1 x f hf hx h).2

/-- Rocq: `SchutteColumn.complete_lemma1`. -/
theorem complete_lemma1 (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (hx : Complete x) :
    Complete L[f, x] :=
  lim_complete (fun i => complete_lemma0 β hβ hindβ1 α hα hindα1 (x i) f hf (complete_subord hx i))
    (directed_monotone x _ (fun _ _ h => schutte_column_monotone f β α _ α _ hf.monotone (le_refl α) h) hx)
    hx.elim.2.1

/-- Rocq: `SchutteColumn.complete_lemma2`. -/
theorem complete_lemma2 (b : β) (a : α) (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hx : Complete x) : Complete Φ[f, b, a, x] :=
  phi_complete β hβ hindβ1 α hα hindα1 hf (complete_lemma1 β hβ hindβ1 α hα hindα1 x f hf hx) b a

/-- Rocq: `SchutteColumn.complete_lemma3`. -/
theorem complete_lemma3 (b : β) (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hx : Complete x) : Complete (sup fun a : α => Φ[f, b, a, x]) :=
  sup_a_complete β hβ hindβ1 α hα hindα1 hf (complete_lemma1 β hβ hindβ1 α hα hindα1 x f hf hx) b

/-- Rocq: `SchutteColumn.complete_lemma4`. -/
theorem complete_lemma4 (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (hx : Complete x) :
    Complete S[f, x] :=
  S_complete β hβ hindβ1 α hα hindα1 hf (complete_lemma1 β hβ hindβ1 α hα hindα1 x f hf hx)

omit hindβ1 in
include hindβ2 in
private theorem normal_G {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) (b : β) (a : α) :
    NormalFunction fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0 :=
  hindβ2 _ _ (normal_N β α hα hindα1 hf a) (complete_subord hβ b) (index_lt β b)

include hindβ2 in
/-- Rocq: `SchutteColumn.schutte_column_fixpoint1`. -/
theorem schutte_column_fixpoint1 (a x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hβ₀ : 0 < β) (ha : a < α) (hac : Complete a) (hx : Complete x) :
    f (a + schutteColumn f β α x) ≤ schutteColumn f β α x := by
  have hα₀ : 0 < α := lt_of_le_of_lt (zero_least a) ha
  have hL := complete_lemma1 β hβ hindβ1 α hα hindα1 x f hf hx
  have hcont : ∀ (A : Type u) (g : A → Ordinal.{u}) (_ : A), Directed A g → (∀ i, Complete (g i)) →
      f (a + sup g) ≤ sup fun i => f (a + g i) := fun A g a₀ hd hc =>
    le_trans (hf.monotone _ _ (add_continuous a A g a₀))
      (hf.continuous A (fun i => a + g i) a₀ (fun i j =>
        let ⟨k, h₁, h₂⟩ := hd i j
        ⟨k, add_le_add (le_refl a) h₁, add_le_add (le_refl a) h₂⟩) fun i => add_complete hac (hc i))
  obtain ⟨b₀, _⟩ := lt_elim hβ₀
  obtain ⟨a₂, ha₂⟩ := lt_elim ha
  have hYS : schutteColumn f β α x ≤ S[f, x] := by
    rw [schutte_column_unroll]
    exact lub_least ((veblen_gt0_column_complete β hβ hindβ1 α hα hindα1 x f hf hx hβ₀).1 hα₀) (le_refl _)
  refine le_trans (hf.monotone _ _ (add_le_add (le_refl a) hYS)) ?_
  refine le_trans (hcont β.Carrier _ b₀
    (directed_monotone β _ (fun _ _ h => sup_monotone fun _ => phi_mono β α hf.monotone x h (le_refl _)) hβ)
    (fun b => complete_lemma3 β hβ hindβ1 α hα hindα1 b x f hf hx)) (sup_least fun b' => ?_)
  refine le_trans (hcont α.Carrier _ a₂
    (directed_monotone α _ (fun _ _ h => phi_mono β α hf.monotone x (le_refl _) h) hα)
    (fun a => complete_lemma2 β hβ hindβ1 α hα hindα1 b' a x f hf hx)) (sup_least fun a' => ?_)
  obtain ⟨a₃, h₁, h₂⟩ := complete_directed hα a' a₂
  rw [schutte_column_unroll]
  refine le_trans ?_ (le_trans (sup_le _ b') (lub_le2 _ _))
  refine le_trans ?_ (sup_le (fun a : α => Φ[f, b', a, x]) a₃)
  refine le_trans ?_ (normal_prefixpoint (normal_G β hβ hindβ2 α hα hindα1 hf b' a₃) _ hL)
  refine le_trans ?_ (schutte_column_le_f (β b') _ 0 _ (normal_N β α hα hindα1 hf a₃).monotone)
  refine le_trans ?_ (schutte_column_le_f β (α a₃) _ f hf.monotone)
  exact hf.monotone _ _ (add_le_add (le_trans ha₂ h₂)
    (le_trans (phi_mono β α hf.monotone x (le_refl _) h₁) (add_zero _).ge))

include hindβ2 in
/-- `f (α a + (Φ + 0)) ≤ Φ`. -/
private theorem phi_ge_f {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {x : Ordinal.{u}} (hx : Complete x)
    (b : β) (a : α) : f (α a + (Φ[f, b, a, x] + 0)) ≤ Φ[f, b, a, x] :=
  le_trans (schutte_column_le_f β (α a) _ f hf.monotone)
    (le_trans (schutte_column_le_f (β b) _ 0 _ (normal_N β α hα hindα1 hf a).monotone)
      (normal_prefixpoint (normal_G β hβ hindβ2 α hα hindα1 hf b a) _
        (complete_lemma1 β hβ hindβ1 α hα hindα1 x f hf hx)))

include hindβ2 in
/-- Anything below `f (α + x)` is below one of the fixpoints `Φ`. -/
private theorem lt_phi_of_lt_f {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {x z : Ordinal.{u}}
    (hx : Complete x) (hα₀ : 0 < α) (hz : z < f (α + x)) (b : β) : ∃ a : α, z < Φ[f, b, a, x] := by
  match complete_zeroDec hx with
  | .inl hx₀ =>
    have hz' := lt_of_lt_of_le hz (le_trans (hf.monotone _ _ (le_trans (add_le_add (le_refl α) hx₀)
      (add_zero α).le)) (normal_ord_decompose α f hα hα₀ hf).le)
    obtain ⟨a, ha⟩ := sup_lt hz'
    exact ⟨a, lt_of_lt_of_le ha (le_trans (hf.monotone _ _ (le_trans (succ_le_add_one _)
      (add_le_add (le_refl _) (one_le_add_zero (phi_pos β α hα hindα1 hf x b a)))))
      (phi_ge_f β hβ hindβ1 hindβ2 α hα hindα1 hf hx b a))⟩
  | .inr hx₀ =>
    obtain ⟨a, _⟩ := lt_elim hα₀
    exact ⟨a, lt_of_lt_of_le hz (le_trans (hf.monotone _ _ (le_trans (add_le_L β α hf hx hα hα₀ hx₀)
      (le_trans (fixOrd_above _ _) (le_trans (add_zero _).ge (le_add_left (α a) _)))))
      (phi_ge_f β hβ hindβ1 hindβ2 α hα hindα1 hf hx b a))⟩

include hindβ2 hindβ3 in
/-- Rocq: `SchutteColumn.schutte_column_fixpoint'`. -/
theorem schutte_column_fixpoint' (a : Ordinal.{u}) :
    ∀ (b x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}), NormalFunction f → b < β → a < α →
      Complete b → Complete a → Complete x →
      schutteColumn (schutteColumn f β a) b (schutteColumn f β α x) 0 ≤ schutteColumn f β α x := by
  induction a using ltRec with
  | ind a iha =>
  intro b x f hf hb ha hbc hac hx
  have hβ₀ : 0 < β := lt_of_le_of_lt (zero_least b) hb
  have hα₀ : 0 < α := lt_of_le_of_lt (zero_least a) ha
  have hY := complete_lemma0 β hβ hindβ1 α hα hindα1 x f hf hx
  have hL := complete_lemma1 β hβ hindβ1 α hα hindα1 x f hf hx
  have hS := complete_lemma4 β hβ hindβ1 α hα hindα1 x f hf hx
  have hM : NormalFunction (schutteColumn f β a) := hindα1 f a hf hac ha
  have hSY : S[f, x] ≤ schutteColumn f β α x := by
    rw [schutte_column_unroll f β α x]; exact lub_le2 _ _
  obtain ⟨a₁, ha₁⟩ := lt_elim ha
  obtain ⟨b₁, hb₁⟩ := lt_elim hb
  rw [schutte_column_unroll (schutteColumn f β a) b (schutteColumn f β α x) 0]
  refine lub_least ?_ (sup_least fun b₂ => sup_least fun q => ?_)
  · -- `schutteColumn f β a (Y + 0) ≤ Y`
    refine le_trans (hM.monotone _ _ (add_zero _).le) ?_
    have common : ∀ z (b₃ : β) (a₃ : α), z < Φ[f, b₃, a₃, x] →
        schutteColumn f β a z < schutteColumn f β α x := by
      intro z b₃ a₃ h
      obtain ⟨a₄, h₁₄, h₃₄⟩ := complete_directed hα a₁ a₃
      refine lt_of_lt_of_le (hM.increasing _ _ (complete_lemma2 β hβ hindβ1 α hα hindα1 b₃ a₃ x f hf hx) h) ?_
      refine le_trans (schutte_column_monotone f β a _ (α a₄) _ hf.monotone (le_trans ha₁ h₁₄)
        (le_trans (phi_mono β α hf.monotone x (le_refl _) h₃₄) (add_zero _).ge)) ?_
      refine le_trans (schutte_column_le_f (β b₃) _ 0 _ (normal_N β α hα hindα1 hf a₄).monotone) ?_
      refine le_trans (normal_prefixpoint (normal_G β hβ hindβ2 α hα hindα1 hf b₃ a₄) _ hL) ?_
      exact le_trans (le_trans (sup_le (fun a : α => Φ[f, b₃, a, x]) a₄)
        (sup_le (fun b : β => sup fun a : α => Φ[f, b, a, x]) b₃)) hSY
    rw [schutte_column_unroll f β a]
    refine lub_least (schutte_column_fixpoint1 β hβ hindβ1 hindβ2 α hα hindα1 a x f hf hβ₀ ha hac hx)
      (sup_least fun b₂ => sup_least fun a₂ => ?_)
    refine fixOrd_least (G_mono (fun _ _ h => schutte_column_monotone f β _ _ _ _ hf.monotone (le_refl _) h) _) _ _
      (limit_least fun j => ?_)
      (iha (a a₂) (index_lt a a₂) (β b₂) x f hf (index_lt β b₂) (lt_trans (index_lt a a₂) ha)
        (complete_subord hβ b₂) (complete_subord hac a₂) hx)
    exact schutte_column_ltE (index_lt _ j) _
      (fun h => let ⟨a₀, h⟩ := lt_phi_of_lt_f β hβ hindβ1 hindβ2 α hα hindα1 hf hx hα₀ h b₁; common _ b₁ a₀ h)
      (fun b₃ a₃ h => common _ b₃ a₃ h)
  · -- the fixpoints of `δ ↦ schutteColumn (schutteColumn g b (Y q)) (b b₂) δ 0` stay below `Y`
    have hgq : NormalFunction (schutteColumn (schutteColumn f β a) b (schutteColumn f β α x q)) :=
      hindβ1 _ b _ hM hbc (complete_subord hY q) hb
    have hH : NormalFunction fun δ => schutteColumn (schutteColumn (schutteColumn f β a) b
        (schutteColumn f β α x q)) (b b₂) δ 0 :=
      hindβ2 _ (b b₂) hgq (complete_subord hbc b₂) (lt_trans (index_lt b b₂) hb)
    refine le_trans (normal_fix_least hH _ _ hS (lim_zero_le _) ?_) hSY
    refine le_trans (hH.continuous β.Carrier _ b₁
      (directed_monotone β _ (fun _ _ h => sup_monotone fun _ => phi_mono β α hf.monotone x h (le_refl _)) hβ)
      (fun b => complete_lemma3 β hβ hindβ1 α hα hindα1 b x f hf hx)) (sup_least fun b'' => ?_)
    refine le_trans (hH.continuous α.Carrier _ a₁
      (directed_monotone α _ (fun _ _ h => phi_mono β α hf.monotone x (le_refl _) h) hα)
      (fun a => complete_lemma2 β hβ hindβ1 α hα hindα1 b'' a x f hf hx)) (sup_least fun a'' => ?_)
    -- find indices above everything in sight with `Y q` below their fixpoint
    have hfind : ∀ (b₃ : β) (a₃ : α), schutteColumn f β α x q < Φ[f, b₃, a₃, x] →
        ∃ (bf : β) (af : α), b ≤ β bf ∧ a ≤ α af ∧ β b'' ≤ β bf ∧ α a'' ≤ α af ∧
          schutteColumn f β α x q < Φ[f, bf, af, x] := by
      intro b₃ a₃ h
      obtain ⟨b₄, h₁₄, h₃₄⟩ := complete_directed hβ b₁ b₃
      obtain ⟨bf, h₄f, h''f⟩ := complete_directed hβ b₄ b''
      obtain ⟨a₄, h₁₄', h₃₄'⟩ := complete_directed hα a₁ a₃
      obtain ⟨af, h₄f', h''f'⟩ := complete_directed hα a₄ a''
      exact ⟨bf, af, le_trans hb₁ (le_trans h₁₄ h₄f), le_trans ha₁ (le_trans h₁₄' h₄f'), h''f, h''f',
        lt_of_lt_of_le h (phi_mono β α hf.monotone x (le_trans h₃₄ h₄f) (le_trans h₃₄' h₄f'))⟩
    obtain ⟨bf, af, hbf, haf, hb'', ha'', hlt⟩ : ∃ (bf : β) (af : α), b ≤ β bf ∧ a ≤ α af ∧ β b'' ≤ β bf ∧
        α a'' ≤ α af ∧ schutteColumn f β α x q < Φ[f, bf, af, x] :=
      schutte_column_ltE (index_lt _ q) _
        (fun h => let ⟨a₀, h⟩ := lt_phi_of_lt_f β hβ hindβ1 hindβ2 α hα hindα1 hf hx hα₀ h b₁; hfind b₁ a₀ h)
        hfind
    have hN := normal_N β α hα hindα1 hf af
    have hGf := normal_G β hβ hindβ2 α hα hindα1 hf bf af
    have hΦf := complete_lemma2 β hβ hindβ1 α hα hindα1 bf af x f hf hx
    refine le_trans (schutte_column_monotone_func _ _ (b b₂) _ 0 _ 0
      (fun _ _ h => schutte_column_monotone _ b _ _ _ _ hM.monotone (le_refl _) h)
      (fun _ _ h => schutte_column_monotone _ (β bf) _ _ _ _ hN.monotone (le_refl _) h)
      (fun z => schutte_column_monotone_full _ _ b _ z (β bf) _ z hM.monotone hN.monotone
        (fun w => schutte_column_monotone f β a w (α af) w hf.monotone haf (le_refl w)) hbf (le_refl _) (le_refl z))
      (le_trans (phi_mono β α hf.monotone x hb'' ha'') (normal_inflationary hGf _ hΦf)) (le_refl 0)) ?_
    refine le_trans (hindβ3 (β bf) _ (b b₂) _ 0 _ (index_lt β bf) hN (lt_of_lt_of_le (index_lt b b₂) hbf) hlt
      (complete_subord hβ bf) hΦf (complete_subord hbc b₂) (complete_subord hY q) zero_complete) ?_
    refine le_trans (normal_prefixpoint hGf _ hL) ?_
    exact le_trans (sup_le (fun a : α => Φ[f, bf, a, x]) af) (sup_le (fun b : β => sup fun a : α => Φ[f, b, a, x]) bf)

include hindβ2 hindβ3 in
/-- Rocq: `SchutteColumn.schutte_column_continuous`. -/
theorem schutte_column_continuous (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ScottContinuous (schutteColumn f β α) := by
  intro A h a₀ hdir hcomp
  have hdir' : Directed A fun i => schutteColumn f β α (h i) := fun i j =>
    let ⟨k, h₁, h₂⟩ := hdir i j
    ⟨k, schutte_column_monotone f β α _ α _ hf.monotone (le_refl α) h₁,
      schutte_column_monotone f β α _ α _ hf.monotone (le_refl α) h₂⟩
  have hc' := fun i => complete_lemma0 β hβ hindβ1 α hα hindα1 (h i) f hf (hcomp i)
  have hT : Complete (sup fun i => schutteColumn f β α (h i)) :=
    sup_complete hc' hdir' (.inl ⟨a₀, schutte_column_nonzero f β α _ hf⟩)
  rw [schutte_column_unroll f β α (sup h)]
  refine lub_least ?_ (sup_least fun b => sup_least fun a => ?_)
  · match complete_zeroDec hα with
    | .inl hα₀ =>
      exact le_trans (hf.monotone _ _ (le_trans (add_le_add hα₀ (le_refl _)) (zero_add _).le))
        (le_trans (hf.continuous A h a₀ hdir hcomp) (sup_monotone fun i =>
          le_trans (hf.monotone _ _ (le_add_left α (h i))) (schutte_column_le_f β α (h i) f hf.monotone)))
    | .inr hα₀ =>
      exact le_trans ((compose_normal hf (normal_addOrd α hα hα₀)).continuous A h a₀ hdir hcomp)
        (sup_monotone fun i => schutte_column_le_f β α (h i) f hf.monotone)
  · have hG := normal_G β hβ hindβ2 α hα hindα1 hf b a
    refine normal_fix_least hG _ _ hT ?_ ?_
    · rw [sup_unfold h]
      exact limit_least fun ⟨i, j⟩ => lt_of_lt_of_le
        (schutte_column_increasing β α (h i) _ f hf hβ hα (hcomp i) (index_lt (h i) j))
        (sup_le (fun i => schutteColumn f β α (h i)) i)
    · exact le_trans (hG.continuous A _ a₀ hdir' hc') (sup_monotone fun i =>
        schutte_column_fixpoint' β hβ hindβ1 hindβ2 hindβ3 α hα hindα1 (α a) (β b) (h i) f hf
          (index_lt β b) (index_lt α a) (complete_subord hβ b) (complete_subord hα a) (hcomp i))

end schutte_column_normal

/-- Rocq: `SchutteColumn.schutte_column_normal_and_fixpoint`. -/
theorem schutte_column_normal_and_fixpoint (β : Ordinal.{u}) :
    Complete β →
      (∀ α : Ordinal.{u}, Complete α →
        (∀ f : Ordinal.{u} → Ordinal.{u}, NormalFunction f → NormalFunction (schutteColumn f β α)) ∧
        (∀ (f : Ordinal.{u} → Ordinal.{u}) (b a x : Ordinal.{u}), NormalFunction f → b < β → a < α →
          Complete b → Complete a → Complete x →
          schutteColumn (schutteColumn f β a) b (schutteColumn f β α x) 0 ≤ schutteColumn f β α x)) ∧
      (∀ f : Ordinal.{u} → Ordinal.{u}, NormalFunction f → NormalFunction fun δ => schutteColumn f β δ 0) := by
  induction β using ltRec with
  | ind β ihβ =>
  intro hβ
  have hindβ1 : ∀ (f : Ordinal.{u} → Ordinal.{u}) (β' α : Ordinal.{u}), NormalFunction f → Complete β' →
      Complete α → β' < β → NormalFunction (schutteColumn f β' α) :=
    fun f β' α hf hβ' hα h => ((ihβ β' h hβ').1 α hα).1 f hf
  have hindβ2 : ∀ (f : Ordinal.{u} → Ordinal.{u}) (β' : Ordinal.{u}), NormalFunction f → Complete β' → β' < β →
      NormalFunction fun α => schutteColumn f β' α 0 :=
    fun f β' hf hβ' h => (ihβ β' h hβ').2 f hf
  have hindβ3 : ∀ (β' α b a x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}), β' < β → NormalFunction f →
      b < β' → a < α → Complete β' → Complete α → Complete b → Complete a → Complete x →
      schutteColumn (schutteColumn f β' a) b (schutteColumn f β' α x) 0 ≤ schutteColumn f β' α x :=
    fun β' α b a x f h hf hb ha hβ' hα hbc hac hx => ((ihβ β' h hβ').1 α hα).2 f b a x hf hb ha hbc hac hx
  have main : ∀ α : Ordinal.{u}, Complete α →
      (∀ f : Ordinal.{u} → Ordinal.{u}, NormalFunction f → NormalFunction (schutteColumn f β α)) ∧
      (∀ (f : Ordinal.{u} → Ordinal.{u}) (b a x : Ordinal.{u}), NormalFunction f → b < β → a < α →
        Complete b → Complete a → Complete x →
        schutteColumn (schutteColumn f β a) b (schutteColumn f β α x) 0 ≤ schutteColumn f β α x) := by
    intro α
    induction α using ltRec with
    | ind α ihα =>
    intro hα
    have hindα1 : ∀ (f : Ordinal.{u} → Ordinal.{u}) (α' : Ordinal.{u}), NormalFunction f → Complete α' → α' < α →
        NormalFunction (schutteColumn f β α') :=
      fun f α' hf hα' h => (ihα α' h hα').1 f hf
    refine ⟨fun f hf => ?_, fun f b a x hf hb ha hbc hac hx =>
      schutte_column_fixpoint' β hβ hindβ1 hindβ2 hindβ3 α hα hindα1 a b x f hf hb ha hbc hac hx⟩
    exact {
      monotone := fun x y h => schutte_column_monotone f β α x α y hf.monotone (le_refl α) h
      increasing := fun x y hy h => schutte_column_increasing β α y x f hf hβ hα hy h
      continuous := schutte_column_continuous β hβ hindβ1 hindβ2 hindβ3 α hα hindα1 f hf
      complete := fun x hx => complete_lemma0 β hβ hindβ1 α hα hindα1 x f hf hx
      nonzero := fun x => schutte_column_nonzero f β α x hf }
  refine ⟨main, fun f hf => ?_⟩
  exact {
    monotone := fun x y h => schutte_column_monotone f β x 0 y 0 hf.monotone h (le_refl 0)
    increasing := by
      intro x y hy hxy
      match complete_zeroDec hβ with
      | .inl hβ₀ =>
        refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (hf.increasing x y hy hxy)
          (le_trans (hf.monotone _ _ (add_zero y).ge) (schutte_column_le_f β y 0 f hf.monotone)))
        rw [schutte_column_unroll]
        exact lub_least (hf.monotone _ _ (add_zero x).le)
          (sup_least fun b => (zero_lt _ (lt_of_lt_of_le (index_lt β b) hβ₀)).elim)
      | .inr hβ₀ =>
        obtain ⟨b₁, _⟩ := lt_elim hβ₀
        obtain ⟨y₁, hy₁⟩ := lt_elim hxy
        have hN := (main (y y₁) (complete_subord hy y₁)).1 f hf
        have hG := hindβ2 (schutteColumn f β (y y₁)) (β b₁) hN (complete_subord hβ b₁) (index_lt β b₁)
        have hL0 : Complete (lim fun i : (0 : Ordinal.{u}).Carrier => schutteColumn f β y ((0 : Ordinal.{u}) i)) :=
          lim_zero_complete
        have hGL := hG.complete _ hL0
        rw [schutte_column_unroll f β y 0]
        refine lt_of_lt_of_le ?_ (le_trans (sup_le _ b₁) (lub_le2 _ _))
        refine lt_of_lt_of_le ?_ (sup_le (fun a : y => fixOrd (fun δ => schutteColumn (schutteColumn f β (y a)) (β b₁) δ 0)
          (lim fun i : (0 : Ordinal.{u}).Carrier => schutteColumn f β y ((0 : Ordinal.{u}) i))) y₁)
        refine lt_of_lt_of_le ?_ (sup_le (fun n : ULift Nat => iterF (fun δ => schutteColumn (schutteColumn f β (y y₁)) (β b₁) δ 0)
          (lim fun i : (0 : Ordinal.{u}).Carrier => schutteColumn f β y ((0 : Ordinal.{u}) i)) n.down) ⟨2⟩)
        refine lt_of_le_of_lt (schutte_column_monotone f β x 0 (y y₁) 0 hf.monotone hy₁ (le_refl 0)) ?_
        refine lt_of_lt_of_le (hN.increasing 0 _ (add_complete hGL zero_complete)
          (lt_of_lt_of_le (schutte_column_nonzero _ _ _ 0 hN) (add_zero _).ge)) ?_
        exact schutte_column_le_f (β b₁) _ 0 _ hN.monotone
    continuous := by
      intro A g g₀ _ hgc
      show schutteColumn f β (sup g) 0 ≤ sup fun i => schutteColumn f β (g i) 0
      rw [schutte_column_unroll]
      refine lub_least ?_ (sup_least fun b₁ => ?_)
      · exact le_trans (hf.monotone _ _ (add_zero _).le) (le_trans (hf.continuous A g g₀ ‹_› hgc)
          (sup_monotone fun i => le_trans (hf.monotone _ _ (add_zero _).ge) (schutte_column_le_f β (g i) 0 f hf.monotone)))
      · rw [sup_unfold g]
        refine sup_least fun ⟨i, j⟩ => ?_
        refine le_trans ?_ (sup_le (fun i => schutteColumn f β (g i) 0) i)
        rw [schutte_column_unroll f β (g i) 0]
        refine le_trans ?_ (le_trans (sup_le _ b₁) (lub_le2 _ _))
        refine le_trans ?_ (sup_le (fun a : g i => fixOrd (fun δ => schutteColumn (schutteColumn f β (g i a)) (β b₁) δ 0)
          (lim fun x : (0 : Ordinal.{u}).Carrier => schutteColumn f β (g i) ((0 : Ordinal.{u}) x))) j)
        exact fixOrd_monotone (fun _ _ h => schutte_column_monotone _ _ _ 0 _ 0
          (fun _ _ h => schutte_column_monotone f β _ _ _ _ hf.monotone (le_refl _) h) h (le_refl 0)) (lim_zero_le _)
    complete := fun x hx => ((main x hx).1 f hf).complete 0 zero_complete
    nonzero := fun x => schutte_column_nonzero f β x 0 hf }

/-- Rocq: `SchutteColumn.schutte_column_normal`. -/
theorem schutte_column_normal (β α : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hβ : Complete β)
    (hα : Complete α) (hf : NormalFunction f) : NormalFunction (schutteColumn f β α) :=
  (((schutte_column_normal_and_fixpoint β hβ).1 α hα).1 f hf)

/-- Rocq: `SchutteColumn.schutte_column_normal_arg`. -/
theorem schutte_column_normal_arg (β : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hβ : Complete β)
    (hf : NormalFunction f) : NormalFunction fun α => schutteColumn f β α 0 :=
  (schutte_column_normal_and_fixpoint β hβ).2 f hf

/-- Rocq: `SchutteColumn.schutte_column_fixpoint`. -/
theorem schutte_column_fixpoint (β α x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (b a : Ordinal.{u})
    (hβ : Complete β) (hα : Complete α) (hf : NormalFunction f) (hb : b < β) (ha : a < α) (hbc : Complete b)
    (hac : Complete a) (hx : Complete x) :
    schutteColumn (schutteColumn f β a) b (schutteColumn f β α x) 0 ≤ schutteColumn f β α x :=
  ((schutte_column_normal_and_fixpoint β hβ).1 α hα).2 f b a x hf hb ha hbc hac hx

/-- Rocq: `SchutteColumn.schutte_column_gt0`. -/
theorem schutte_column_gt0 (β α : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) (hβ : Complete β)
    (hα : Complete α) (hx : Complete x) (hf : NormalFunction f) (hβ₀ : 0 < β) (hα₀ : 0 < α) :
    schutteColumn f β α x ≈
      sup fun b : β => sup fun a : α => fixOrd (fun δ => schutteColumn (schutteColumn f β (α a)) (β b) δ 0)
        (lim fun i : x => schutteColumn f β α (x i)) := by
  rw [schutte_column_unroll]
  exact equiv_intro (lub_least ((veblen_gt0_column_complete β hβ
      (fun f β' α hf hβ' hα _ => schutte_column_normal β' α f hβ' hα hf) α hα
      (fun f α' hf hα' _ => schutte_column_normal β α' f hβ hα' hf) x f hf hx hβ₀).1 hα₀) (le_refl _))
    (lub_le2 _ _)

/-- Rocq: `SchutteColumn.schutte_column_monotone_func'`. -/
theorem schutte_column_monotone_func' (β : Ordinal.{u}) :
    ∀ (α x : Ordinal.{u}) (f g : Ordinal.{u} → Ordinal.{u}), NormalFunction f → NormalFunction g →
      (∀ a, Complete a → f a ≤ g a) → Complete β → Complete α → Complete x →
      schutteColumn f β α x ≤ schutteColumn g β α x := by
  induction β using ltRec with
  | ind β ihβ =>
  intro α
  induction α using ltRec with
  | ind α ihα =>
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro f g hf hg hfg hβ hα hx
  have hY := (schutte_column_normal β α g hβ hα hg).complete x hx
  rw [schutte_column_unroll f β α x]
  refine lub_least (le_trans (hfg _ (add_complete hα hx)) (schutte_column_le_f β α x g hg.monotone))
    (sup_least fun b => sup_least fun a => ?_)
  have hβb := complete_subord hβ b
  have hαa := complete_subord hα a
  refine normal_fix_least (schutte_column_normal_arg (β b) _ hβb (schutte_column_normal β (α a) f hβ hαa hf))
    _ _ hY ?_ ?_
  · exact limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) f g hf hg hfg hβ hα (complete_subord hx i))
      (schutte_column_increasing β α x _ g hg hβ hα hx (index_lt x i))
  · exact le_trans (ihβ (β b) (index_lt β b) _ 0 _ _ (schutte_column_normal β (α a) f hβ hαa hf)
        (schutte_column_normal β (α a) g hβ hαa hg)
        (fun z hz => ihα (α a) (index_lt α a) z f g hf hg hfg hβ hαa hz) hβb hY zero_complete)
      (schutte_column_fixpoint β α x g (β b) (α a) hβ hα hg (index_lt β b) (index_lt α a) hβb hαa hx)

/-- Rocq: `SchutteColumn.schutte_column_normalβ`. -/
theorem schutte_column_normalβ (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    NormalFunction fun β => schutteColumn f β 1 0 where
  monotone x y h := schutte_column_monotoneβ x y 1 0 f hf.monotone h
  increasing := by
    intro x y hy hxy
    obtain ⟨i, hi⟩ := lt_elim hxy
    have hN := schutte_column_normal y 0 f hy zero_complete hf
    have hG := schutte_column_normal_arg (y i) _ (complete_subord hy i) hN
    have hL0 : Complete (lim fun j : (0 : Ordinal.{u}).Carrier => schutteColumn f y 1 ((0 : Ordinal.{u}) j)) :=
      lim_zero_complete
    have hG1 := hG.complete _ hL0
    have hG2 := hG.complete _ hG1
    rw [schutte_column_unroll f y 1 0]
    refine lt_of_lt_of_le ?_ (le_trans (sup_le _ i) (lub_le2 _ _))
    refine lt_of_lt_of_le ?_ (sup_le (fun a : (1 : Ordinal.{u}).Carrier => fixOrd
      (fun δ => schutteColumn (schutteColumn f y ((1 : Ordinal.{u}) a)) (y i) δ 0)
      (lim fun j : (0 : Ordinal.{u}).Carrier => schutteColumn f y 1 ((0 : Ordinal.{u}) j))) PUnit.unit)
    refine lt_of_lt_of_le ?_ (sup_le (fun n : ULift Nat => iterF (fun δ => schutteColumn (schutteColumn f y 0) (y i) δ 0)
      (lim fun j : (0 : Ordinal.{u}).Carrier => schutteColumn f y 1 ((0 : Ordinal.{u}) j)) n.down) ⟨3⟩)
    refine lt_of_le_of_lt (le_trans (schutte_column_monotoneβ x (y i) 1 0 f hf.monotone hi)
      (schutte_column_monotone_func f _ (y i) 1 0 1 0 hf.monotone hN.monotone
        (fun z => le_trans (hf.monotone _ _ (zero_add z).ge) (schutte_column_le_f y 0 z f hf.monotone))
        (le_refl 1) (le_refl 0))) ?_
    refine hG.increasing 1 _ hG2 ?_
    calc (1 : Ordinal.{u}) ≈ 1 + 0 := equiv_symm (add_zero 1)
      _ < 1 + schutteColumn (schutteColumn f y 0) (y i) _ 0 := add_lt_add_left 1 (schutte_column_nonzero _ _ _ 0 hN)
      _ ≤ _ := onePlus_least_normal hG _ hG1
  continuous := by
    intro A g a₀ _ _
    show schutteColumn f (sup g) 1 0 ≤ sup fun i => schutteColumn f (g i) 1 0
    rw [schutte_column_unroll]
    refine lub_least (le_trans (schutte_column_le_f (g a₀) 1 0 f hf.monotone)
      (sup_le (fun i => schutteColumn f (g i) 1 0) a₀)) ?_
    rw [sup_unfold g]
    refine sup_least fun ⟨i, j⟩ => sup_least fun _ => ?_
    refine le_trans ?_ (sup_le (fun i => schutteColumn f (g i) 1 0) i)
    rw [schutte_column_unroll f (g i) 1 0]
    refine le_trans ?_ (le_trans (sup_le _ j) (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun a : (1 : Ordinal.{u}).Carrier => fixOrd
      (fun δ => schutteColumn (schutteColumn f (g i) ((1 : Ordinal.{u}) a)) (g i j) δ 0)
      (lim fun k : (0 : Ordinal.{u}).Carrier => schutteColumn f (g i) 1 ((0 : Ordinal.{u}) k))) PUnit.unit)
    have hm : ∀ β : Ordinal.{u}, ∀ p q, p ≤ q → schutteColumn f β 0 p ≤ schutteColumn f β 0 q :=
      fun β _ _ h => schutte_column_monotone f β 0 _ 0 _ hf.monotone (le_refl 0) h
    exact fixOrd_monotone_full (fun δ => schutte_column_monotone_func _ _ (g i j) δ 0 δ 0 (hm _) (hm _)
        (fun z => le_trans (schutte_column_arg0 _ z f hf.monotone).le (schutte_column_arg0 _ z f hf.monotone).ge)
        (le_refl δ) (le_refl 0))
      (fun _ _ h => schutte_column_monotone _ _ _ 0 _ 0 (hm _) h (le_refl 0)) (lim_zero_le _)
  complete x hx := (schutte_column_normal x 1 f hx (succ_complete zero_complete) hf).complete 0 zero_complete
  nonzero x := schutte_column_nonzero f x 1 0 hf

/-- The E-numbers over `f`: the fixpoints of `β ↦ schutteColumn f β 1 0`.
Rocq: `SchutteColumn.E_number`. -/
def eNumber (f : Ordinal.{u} → Ordinal.{u}) (n : Ordinal.{u}) : Ordinal.{u} :=
  enumFixpoints (fun β => schutteColumn f β 1 0) n

/-- Rocq: `SchutteColumn.E_number_normal`. -/
theorem E_number_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) : NormalFunction (eNumber f) :=
  enum_fixpoints_normal (schutte_column_normalβ f hf)

end Ordinal

end ConstructiveOrdinals
