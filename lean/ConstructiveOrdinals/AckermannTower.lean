import ConstructiveOrdinals.Veblen.Facts

/-!
# The Ackermann tower

`ackermannTower f a` generalises the Veblen hierarchy by one more level of
diagonalisation. Its fixpoints are closed under `veblen (ackermannTower f a')`
for every `a' < a`. Iterating it finitely often from `x ↦ 1 + x` gives the
small Ackermann ordinal, and taking its first fixpoint gives the large
Ackermann ordinal.

As for `veblen`, the nested `fix` of the Rocq definition becomes the inner
function `ackermannTowerInner`, parameterised by the outer recursive calls.
`ackermann_tower_unroll` gives the characteristic equation, and
`ackermannTower` is then made irreducible.

Ported from the Rocq file `AckermannTower.v`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-- The inner recursion of `ackermannTower`, on the argument, given the outer
recursive calls `outer a' = ackermannTower f (a a')`. -/
def ackermannTowerInner (f : Ordinal.{u} → Ordinal.{u}) {A : Type u}
    (outer : A → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk X h => f (mk X h) ⊔
      sup fun a => fixOrd (fun d => veblen (outer a) d 0) (mk X fun x => ackermannTowerInner f outer (h x))

/-- Rocq: `AckermannTower.ackermann_tower`. -/
def ackermannTower (f : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | mk _ g => ackermannTowerInner f fun a => ackermannTower f (g a)

/-- Rocq: `AckermannTower.ackermann_tower_unroll`. -/
theorem ackermann_tower_unroll (f : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u}) :
    ackermannTower f a x =
      f x ⊔ sup fun a' : a =>
        fixOrd (fun d => veblen (ackermannTower f (a a')) d 0) (lim fun x' : x => ackermannTower f a (x x')) := by
  cases a; cases x; rfl

attribute [irreducible] ackermannTower

/-- The empty limit is below everything. -/
private theorem lim_zero_le {g : (0 : Ordinal.{u}).Carrier → Ordinal.{u}} (z : Ordinal.{u}) : lim g ≤ z :=
  limit_least fun e => PEmpty.elim e

/-- Rocq: `AckermannTower.ackermann_tower_monotone_x`. -/
theorem ackermann_tower_monotone_x (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ x y, x ≤ y → ackermannTower f a x ≤ ackermannTower f a y := by
  induction a using ltRec with
  | ind a iha =>
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro y hxy
  rw [ackermann_tower_unroll f a x, ackermann_tower_unroll f a y]
  refine lub_least (le_trans (hf x y hxy) (lub_le1 _ _))
    (le_trans (sup_monotone fun a' => ?_) (lub_le2 _ _))
  refine fixOrd_monotone (fun d d' h => veblen_monotone_first
    (iha (a a') (index_lt a a')) d' d 0 h) ?_
  exact limit_least fun i =>
    let ⟨j, hj⟩ := le_subord hxy i
    lt_of_le_of_lt (ihx (x i) (index_lt x i) (y j) hj)
      (limit_lt (fun y' : y => ackermannTower f a (y y')) j)

/-- Rocq: `AckermannTower.ackermann_tower_monotone_a`. -/
theorem ackermann_tower_monotone_a (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    ∀ b, a ≤ b → (∀ x y, x ≤ y → f x ≤ f y) → ∀ x, ackermannTower f a x ≤ ackermannTower f b x := by
  induction a using ltRec with
  | ind a iha =>
  intro b hab hf x
  induction x using ltRec with
  | ind x ihx =>
  rw [ackermann_tower_unroll f a x, ackermann_tower_unroll f b x]
  refine lub_least (lub_le1 _ _) (sup_least fun a' => ?_)
  obtain ⟨b', hb'⟩ := le_subord hab a'
  have hGb : ∀ d d', d ≤ d' → veblen (ackermannTower f (b b')) d 0 ≤ veblen (ackermannTower f (b b')) d' 0 :=
    fun d d' h => veblen_monotone_first (ackermann_tower_monotone_x f (b b') hf) d' d 0 h
  refine le_trans ?_ (le_trans (sup_le (fun b' : b => fixOrd (fun d => veblen (ackermannTower f (b b')) d 0)
    (lim fun x' : x => ackermannTower f b (x x'))) b') (lub_le2 _ _))
  exact le_trans
    (fixOrd_monotone_func (fun d => veblen_mono_func (ackermann_tower_monotone_x f (b b') hf)
      (iha (a a') (index_lt a a') (b b') hb' hf) d 0) hGb _)
    (fixOrd_monotone hGb (lim_monotone fun i => ihx (x i) (index_lt x i)))

/-- Rocq: `AckermannTower.ackermann_tower_monotone`. -/
theorem ackermann_tower_monotone (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y)
    (a b x y : Ordinal.{u}) (hab : a ≤ b) (hxy : x ≤ y) :
    ackermannTower f a x ≤ ackermannTower f b y :=
  le_trans (ackermann_tower_monotone_x f a hf x y hxy) (ackermann_tower_monotone_a f a b hab hf y)

/-- Rocq: `AckermannTower.ackermann_tower_increasing`. -/
theorem ackermann_tower_increasing (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (hf : NormalFunction f) (ha : Complete a) (x y : Ordinal.{u}) (hy : Complete y) (hxy : x < y) :
    ackermannTower f a x < ackermannTower f a y := by
  match complete_zeroDec ha with
  | .inl ha₀ =>
    refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (hf.increasing x y hy hxy) ?_)
    · rw [ackermann_tower_unroll]
      exact lub_least (le_refl _) (sup_least fun i =>
        (zero_lt _ (lt_of_lt_of_le (index_lt a i) ha₀)).elim)
    · rw [ackermann_tower_unroll]; exact lub_le1 _ _
  | .inr ha₀ =>
    obtain ⟨i, _⟩ := lt_elim ha₀
    obtain ⟨y', hy'⟩ := lt_elim hxy
    rw [ackermann_tower_unroll f a y]
    refine lt_of_lt_of_le ?_ (le_trans (sup_le _ i) (lub_le2 _ _))
    exact lt_of_lt_of_le (lt_of_le_of_lt (ackermann_tower_monotone_x f a hf.monotone x (y y') hy')
      (limit_lt (fun y' : y => ackermannTower f a (y y')) y')) (fixOrd_above _ _)

/-- Rocq: `AckermannTower.ackermann_tower_nonzero`. -/
theorem ackermann_tower_nonzero (f : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u}) (hf : NormalFunction f) :
    0 < ackermannTower f a x := by
  rw [ackermann_tower_unroll]
  exact lt_of_lt_of_le (hf.nonzero x) (lub_le1 _ _)

/-- Rocq: `AckermannTower.ackermann_tower_inflationary`. -/
theorem ackermann_tower_inflationary (f : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u})
    (hf : NormalFunction f) (hx : Complete x) : x ≤ ackermannTower f a x := by
  rw [ackermann_tower_unroll]
  exact le_trans (normal_inflationary hf x hx) (lub_le1 _ _)

section ackermann_tower

variable (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (a : Ordinal.{u}) (ha : Complete a)
  (hinduct : ∀ i, Complete i → i < a → NormalFunction (ackermannTower f i))
include hf hinduct

omit hinduct in
private theorem lim_tower_directed (i x : Ordinal.{u}) (hx : Complete x) :
    Directed x.Carrier fun x' => ackermannTower f i (x x') :=
  directed_monotone x _ (fun _ _ h => ackermann_tower_monotone_x f i hf.monotone _ _ h) hx

private theorem sub_normal {i : Ordinal.{u}} (hia : i ≤ a) (hi : Complete i) (i' : i) :
    NormalFunction (ackermannTower f (i i')) :=
  hinduct _ (complete_subord hi i') (lt_of_lt_of_le (index_lt i i') hia)

/-- The `fixOrd` in the unrolling of `ackermannTower f i x` is complete. -/
private theorem fix_tower_complete {i x : Ordinal.{u}} (hia : i ≤ a) (hi : Complete i) (i' : i)
    (hL : Complete (lim fun x' : x => ackermannTower f i (x x'))) :
    Complete (fixOrd (fun d => veblen (ackermannTower f (i i')) d 0) (lim fun x' : x => ackermannTower f i (x x'))) :=
  have hn := sub_normal f hf a hinduct hia hi i'
  normal_fix_complete _ hL (fun z hz => normal_inflationary (veblen_first_normal hn) z hz)
    (veblen_first_normal hn).monotone (veblen_first_normal hn).complete

/-- Rocq: `AckermannTower.ackermann_tower_complete_le`. -/
theorem ackermann_tower_complete_le :
    ∀ x i : Ordinal.{u}, i ≤ a → 0 < i → Complete i → Complete x →
      f x ≤ (sup fun i' : i => fixOrd (fun d => veblen (ackermannTower f (i i')) d 0)
        (lim fun x' : x => ackermannTower f i (x x'))) ∧
      Complete (ackermannTower f i x) := by
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro i hia hi0 hi hx
  have hL : Complete (lim fun x' : x => ackermannTower f i (x x')) :=
    lim_complete (fun x' => (ihx (x x') (index_lt x x') i hia hi0 hi (complete_subord hx x')).2)
      (lim_tower_directed f hf i x hx) hx.elim.2.1
  obtain ⟨i', _⟩ := lt_elim hi0
  have hn := sub_normal f hf a hinduct hia hi i'
  have hxL : x ≤ lim fun x' : x => ackermannTower f i (x x') :=
    le_intro fun x' => lt_of_le_of_lt (ackermann_tower_inflationary f i (x x') hf (complete_subord hx x'))
      (limit_lt (fun x' : x => ackermannTower f i (x x')) x')
  have hfx : f x ≤ sup fun i' : i => fixOrd (fun d => veblen (ackermannTower f (i i')) d 0)
      (lim fun x' : x => ackermannTower f i (x x')) := by
    refine le_trans (hf.monotone _ _ (le_trans hxL (add_zero _).ge)) ?_
    refine le_trans ?_ (sup_le (fun i' : i => fixOrd (fun d => veblen (ackermannTower f (i i')) d 0)
      (lim fun x' : x => ackermannTower f i (x x'))) i')
    refine le_trans ?_ (sup_le (fun n : ULift Nat => iterF (fun d => veblen (ackermannTower f (i i')) d 0)
      (lim fun x' : x => ackermannTower f i (x x')) n.down) ⟨1⟩)
    refine le_trans ?_ (veblen_fax hn _ 0 hL zero_complete)
    rw [ackermann_tower_unroll]
    exact lub_le1 _ _
  refine ⟨hfx, ?_⟩
  rw [ackermann_tower_unroll]
  refine lub_complete2 hfx (hf.complete x hx) (sup_complete (fun i' => fix_tower_complete f hf a hinduct hia hi i' hL)
    (directed_monotone i _ (fun p q h => fixOrd_monotone_func (fun d =>
      veblen_monotone_full (ackermann_tower_monotone_x f _ hf.monotone)
        (ackermann_tower_monotone_a f _ _ h hf.monotone) d 0 d 0 (le_refl d) (le_refl 0))
      (veblen_first_normal (sub_normal f hf a hinduct hia hi q)).monotone _) hi) (.inl ⟨i', ?_⟩))
  refine lt_of_lt_of_le (ackermann_tower_nonzero f _ 0 hf)
    (le_trans (f_le_veblen hn (lim fun x' : x => ackermannTower f i (x x')) 0) ?_)
  exact sup_le (fun n : ULift Nat => iterF (fun d => veblen (ackermannTower f (i i')) d 0)
    (lim fun x' : x => ackermannTower f i (x x')) n.down) ⟨1⟩

/-- Rocq: `AckermannTower.ackermann_tower_unroll_nonzero`. -/
theorem ackermann_tower_unroll_nonzero (x i : Ordinal.{u}) (hia : i ≤ a) (hi0 : 0 < i) (hi : Complete i)
    (hx : Complete x) :
    ackermannTower f i x ≈ sup fun i' : i => fixOrd (fun d => veblen (ackermannTower f (i i')) d 0)
      (lim fun x' : x => ackermannTower f i (x x')) := by
  rw [ackermann_tower_unroll]
  exact equiv_intro (lub_least (ackermann_tower_complete_le f hf a hinduct x i hia hi0 hi hx).1 (le_refl _))
    (lub_le2 _ _)

/-- Rocq: `AckermannTower.ackermann_tower_complete`. -/
theorem ackermann_tower_complete (x i : Ordinal.{u}) (hia : i ≤ a) (hi : Complete i) (hx : Complete x) :
    Complete (ackermannTower f i x) := by
  match complete_zeroDec hi with
  | .inl hi₀ =>
    have hne : ∀ i' : i, False := fun i' => zero_lt _ (lt_of_lt_of_le (index_lt i i') hi₀)
    rw [ackermann_tower_unroll]
    exact lub_complete1 (sup_least fun i' => (hne i').elim) (hf.complete x hx)
      (sup_complete (fun i' => (hne i').elim) (fun i' _ => (hne i').elim) (.inr fun i' => (hne i').elim))
  | .inr hi₀ => exact (ackermann_tower_complete_le f hf a hinduct x i hia hi₀ hi hx).2

private theorem lim_tower_complete {i x : Ordinal.{u}} (hia : i ≤ a) (hi : Complete i) (hx : Complete x) :
    Complete (lim fun x' : x => ackermannTower f i (x x')) :=
  lim_complete (fun x' => ackermann_tower_complete f hf a hinduct (x x') i hia hi (complete_subord hx x'))
    (lim_tower_directed f hf i x hx) hx.elim.2.1

/-- Rocq: `AckermannTower.ackermann_tower_fixpoint_aux`. -/
theorem ackermann_tower_fixpoint_aux (i i' x : Ordinal.{u}) (hia : i ≤ a) (hi'i : i' < i) (hi : Complete i)
    (hi' : Complete i') (hx : Complete x) :
    veblen (ackermannTower f i') (ackermannTower f i x) 0 ≤ ackermannTower f i x := by
  have hn' : NormalFunction (ackermannTower f i') := hinduct i' hi' (lt_of_lt_of_le hi'i hia)
  have hi0 : 0 < i := lt_of_le_of_lt (zero_least i') hi'i
  have hAc := ackermann_tower_complete f hf a hinduct x i hia hi hx
  have hL := lim_tower_complete f hf a hinduct hia hi hx
  have hq : ∀ q, Complete q → q < ackermannTower f i x →
      fixOrd (veblen (ackermannTower f i') q) 0 ≤ ackermannTower f i x := by
    intro q hqc hq
    obtain ⟨i'', hq⟩ := sup_lt (lt_of_lt_of_le hq
      (ackermann_tower_unroll_nonzero f hf a hinduct x i hia hi0 hi hx).le)
    obtain ⟨z, hz⟩ := lt_elim hi'i
    obtain ⟨t, hzt, hi''t⟩ := complete_directed hi z i''
    have hnz := sub_normal f hf a hinduct hia hi z
    have hnt := sub_normal f hf a hinduct hia hi t
    have hΦ := fix_tower_complete f hf a hinduct hia hi t hL
    refine le_trans (fixOrd_monotone_func (fun d => veblen_monotone_full hnz.monotone
      (ackermann_tower_monotone_a f i' _ hz hf.monotone) q d q d (le_refl q) (le_refl d))
      (veblen_monotone hnz.monotone q) 0) ?_
    rw [ackermann_tower_unroll]
    refine le_trans ?_ (le_trans (sup_le (fun i' : i => fixOrd (fun d => veblen (ackermannTower f (i i')) d 0)
      (lim fun x' : x => ackermannTower f i (x x'))) t) (lub_le2 _ _))
    refine normal_fix_least (veblen_normal hnz q hqc) 0 _ hΦ (zero_least _) ?_
    refine veblen_collapse hnz q _ _ hqc hΦ hΦ ?_ (le_refl _) ?_
    · exact lt_of_lt_of_le hq (fixOrd_monotone_func (fun d => veblen_monotone_full hnt.monotone
        (ackermann_tower_monotone_a f _ _ hi''t hf.monotone) d 0 d 0 (le_refl d) (le_refl 0))
        (veblen_first_normal hnt).monotone _)
    · exact le_trans (veblen_monotone_full hnt.monotone
          (ackermann_tower_monotone_a f _ _ hzt hf.monotone) _ 0 _ 0 (le_refl _) (le_refl 0))
        (normal_fixpoint (veblen_first_normal hnt) _ hL).ge
  refine le_trans (veblen_unroll_nonzero hn' _ 0 zero_complete (ackermann_tower_nonzero f i x hf)).le ?_
  exact sup_least fun q => le_trans (fixOrd_monotone (veblen_monotone hn'.monotone _) (lim_zero_le 0))
    (hq _ (complete_subord hAc q) (index_lt _ q))

/-- Rocq: `AckermannTower.ackermann_tower_continuous`. -/
theorem ackermann_tower_continuous (i : Ordinal.{u}) (hia : i ≤ a) (hi : Complete i) :
    ScottContinuous (ackermannTower f i) := by
  intro A g a₀ hdir hg
  have hdir' : Directed A fun z => ackermannTower f i (g z) := fun p q =>
    let ⟨k, h₁, h₂⟩ := hdir p q
    ⟨k, ackermann_tower_monotone_x f i hf.monotone _ _ h₁, ackermann_tower_monotone_x f i hf.monotone _ _ h₂⟩
  have hgc : ∀ z, Complete (ackermannTower f i (g z)) := fun z =>
    ackermann_tower_complete f hf a hinduct (g z) i hia hi (hg z)
  have hS : Complete (sup fun z => ackermannTower f i (g z)) :=
    sup_complete hgc hdir' (.inl ⟨a₀, ackermann_tower_nonzero f i _ hf⟩)
  rw [ackermann_tower_unroll]
  refine lub_least (le_trans (hf.continuous A g a₀ hdir hg) (sup_monotone fun z => ?_)) (sup_least fun i' => ?_)
  · rw [ackermann_tower_unroll]; exact lub_le1 _ _
  · have hn := sub_normal f hf a hinduct hia hi i'
    refine normal_fix_least (veblen_first_normal hn) _ _ hS ?_ ?_
    · rw [sup_unfold g]
      exact limit_least fun ⟨z, q⟩ => lt_of_lt_of_le
        (ackermann_tower_increasing f i hf hi _ _ (hg z) (index_lt (g z) q))
        (sup_le (fun z => ackermannTower f i (g z)) z)
    · refine le_trans ((veblen_first_normal hn).continuous A _ a₀ hdir' hgc) (sup_monotone fun z => ?_)
      exact ackermann_tower_fixpoint_aux f hf a hinduct i (i i') (g z) hia (index_lt i i') hi
        (complete_subord hi i') (hg z)

end ackermann_tower

/-- Rocq: `AckermannTower.ackermann_tower_normal`. -/
theorem ackermann_tower_normal (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    NormalFunction f → Complete a → NormalFunction (ackermannTower f a) := by
  induction a using ltRec with
  | ind a iha =>
  intro hf ha
  have hinduct : ∀ i, Complete i → i < a → NormalFunction (ackermannTower f i) :=
    fun i hi h => iha i h hf hi
  exact {
    monotone := ackermann_tower_monotone_x f a hf.monotone
    increasing := fun x y hy h => ackermann_tower_increasing f a hf ha x y hy h
    continuous := ackermann_tower_continuous f hf a hinduct a (le_refl a) ha
    complete := fun x hx => ackermann_tower_complete f hf a hinduct x a (le_refl a) ha hx
    nonzero := fun x => ackermann_tower_nonzero f a x hf }

/-- Rocq: `AckermannTower.ackermann_tower_fixpoint`. -/
theorem ackermann_tower_fixpoint (f : Ordinal.{u} → Ordinal.{u}) (a a' x : Ordinal.{u}) (hf : NormalFunction f)
    (ha : Complete a) (ha' : Complete a') (hx : Complete x) (h : a' < a) :
    veblen (ackermannTower f a') (ackermannTower f a x) 0 ≤ ackermannTower f a x :=
  ackermann_tower_fixpoint_aux f hf a (fun i hi _ => ackermann_tower_normal f i hf hi) a a' x (le_refl a) h
    ha ha' hx

/-- Rocq: `AckermannTower.ackermann_tower_normal_first`. -/
theorem ackermann_tower_normal_first (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    NormalFunction fun a => ackermannTower f a 0 where
  monotone x y h := ackermann_tower_monotone f hf.monotone x y 0 0 h (le_refl 0)
  increasing x y hy hxy := by
    obtain ⟨i, hi⟩ := lt_elim hxy
    have hg := ackermann_tower_normal f (y i) hf (complete_subord hy i)
    have hG0 : Complete (veblen (ackermannTower f (y i)) 0 0) :=
      veblen_complete hg hg.complete 0 zero_complete 0 zero_complete
    calc ackermannTower f x 0
        ≤ ackermannTower f (y i) 0 := ackermann_tower_monotone f hf.monotone _ _ 0 0 hi (le_refl 0)
      _ < ackermannTower f (y i) (veblen (ackermannTower f (y i)) 0 0 + 0) :=
          ackermann_tower_increasing f _ hf (complete_subord hy i) _ _ (add_complete hG0 zero_complete)
            (lt_of_lt_of_le (veblen_nonzero hg 0 0) (add_zero _).ge)
      _ ≤ veblen (ackermannTower f (y i)) (veblen (ackermannTower f (y i)) 0 0) 0 :=
          veblen_fax hg _ 0 hG0 zero_complete
      _ ≤ fixOrd (fun d => veblen (ackermannTower f (y i)) d 0) 0 :=
          sup_le (fun n : ULift Nat => iterF (fun d => veblen (ackermannTower f (y i)) d 0) 0 n.down) ⟨2⟩
      _ ≤ fixOrd (fun d => veblen (ackermannTower f (y i)) d 0)
            (lim fun x' : (0 : Ordinal.{u}) => ackermannTower f y ((0 : Ordinal.{u}) x')) :=
          fixOrd_monotone (veblen_first_normal hg).monotone (zero_least _)
      _ ≤ ackermannTower f y 0 := by
          rw [ackermann_tower_unroll f y 0]
          exact le_trans (sup_le (fun i : y => fixOrd (fun d => veblen (ackermannTower f (y i)) d 0)
            (lim fun x' : (0 : Ordinal.{u}) => ackermannTower f y ((0 : Ordinal.{u}) x'))) i) (lub_le2 _ _)
  continuous := by
    intro A g a₀ _ hgc
    show ackermannTower f (sup g) 0 ≤ sup fun z => ackermannTower f (g z) 0
    rw [ackermann_tower_unroll]
    refine lub_least (le_trans ?_ (sup_le (fun z => ackermannTower f (g z) 0) a₀)) (sup_least ?_)
    · rw [ackermann_tower_unroll]; exact lub_le1 _ _
    · rw [sup_unfold g]
      intro ⟨z, q⟩
      refine le_trans ?_ (sup_le (fun z => ackermannTower f (g z) 0) z)
      rw [ackermann_tower_unroll f (g z) 0]
      refine le_trans ?_ (le_trans (sup_le (fun q : g z => fixOrd (fun d => veblen (ackermannTower f (g z q)) d 0)
        (lim fun x' : (0 : Ordinal.{u}) => ackermannTower f (g z) ((0 : Ordinal.{u}) x'))) q) (lub_le2 _ _))
      exact fixOrd_monotone (veblen_first_normal (ackermann_tower_normal f _ hf
        (complete_subord (hgc z) q))).monotone (lim_zero_le _)
  complete a ha := (ackermann_tower_normal f a hf ha).complete 0 zero_complete
  nonzero a := ackermann_tower_nonzero f a 0 hf

/-- Rocq: `AckermannTower.ackermann_tower_monotone_func`. -/
theorem ackermann_tower_monotone_func (f g : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    ∀ x, NormalFunction f → NormalFunction g → Complete a → Complete x →
      (∀ x, Complete x → f x ≤ g x) → ackermannTower f a x ≤ ackermannTower g a x := by
  induction a using ltRec with
  | ind a iha =>
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro hf hg ha hx hfg
  have hY := (ackermann_tower_normal g a hg ha).complete x hx
  rw [ackermann_tower_unroll f a x]
  refine lub_least (le_trans (hfg x hx) (by rw [ackermann_tower_unroll]; exact lub_le1 _ _))
    (sup_least fun a' => ?_)
  have hna := complete_subord ha a'
  refine normal_fix_least (veblen_first_normal (ackermann_tower_normal f _ hf hna)) _ _ hY ?_ ?_
  · exact limit_least fun i => lt_of_le_of_lt
      (ihx (x i) (index_lt x i) hf hg ha (complete_subord hx i) hfg)
      (ackermann_tower_increasing g a hg ha _ _ hx (index_lt x i))
  · exact le_trans (veblen_monotone_func (ackermann_tower_normal f _ hf hna) (ackermann_tower_normal g _ hg hna)
      (fun z hz => iha (a a') (index_lt a a') z hf hg hna hz hfg) _ 0 hY zero_complete)
      (ackermann_tower_fixpoint g a (a a') x hg ha hna hx (index_lt a a'))

/-- Rocq: `AckermannTower.ackermann_tower_fax`. -/
theorem ackermann_tower_fax (f : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u}) (hf : NormalFunction f)
    (ha : Complete a) (hx : Complete x) : f (a + x) ≤ ackermannTower f a x := by
  match complete_zeroDec ha with
  | .inl ha₀ =>
    refine le_trans (hf.monotone _ _ (le_trans (add_le_add ha₀ (le_refl x)) (zero_add x).le)) ?_
    rw [ackermann_tower_unroll]; exact lub_le1 _ _
  | .inr ha₀ =>
    have hAc := (ackermann_tower_normal f a hf ha).complete x hx
    have hax : a + x ≤ ackermannTower f a x := by
      clear hAc
      induction x using ltRec with
      | ind x ihx =>
      rw [add_unfold]
      refine lub_least ?_ (sup_least fun i => succ_least (lt_of_le_of_lt
        (ihx (x i) (index_lt x i) (complete_subord hx i))
        (ackermann_tower_increasing f a hf ha _ _ hx (index_lt x i))))
      exact le_trans (normal_inflationary (ackermann_tower_normal_first f hf) a ha)
        (ackermann_tower_monotone f hf.monotone a a 0 x (le_refl a) (zero_least x))
    refine le_trans ?_ (ackermann_tower_fixpoint f a 0 x hf ha zero_complete hx ha₀)
    refine le_trans ?_ (veblen_fax (ackermann_tower_normal f 0 hf zero_complete) _ 0 hAc zero_complete)
    rw [ackermann_tower_unroll f 0]
    exact le_trans (hf.monotone _ _ (le_trans hax (add_zero _).ge)) (lub_le1 _ _)

/-- Rocq: `AckermannTower.ackermann_tower_zero`. -/
theorem ackermann_tower_zero (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) : ackermannTower f 0 x ≈ f x := by
  rw [ackermann_tower_unroll]
  exact equiv_intro (lub_least (le_refl _) (sup_least fun e => PEmpty.elim e)) (lub_le1 _ _)

/-- Rocq: `AckermannTower.ackermann_tower_succ`. -/
theorem ackermann_tower_succ (f : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u}) (hf : NormalFunction f)
    (ha : Complete a) (hx : Complete x) :
    ackermannTower f (succ a) x ≈ enumFixpoints (fun i => veblen (ackermannTower f a) i 0) x := by
  have hn := ackermann_tower_normal f a hf ha
  have hF := veblen_first_normal hn
  have hE := enum_fixpoints_normal hF
  have hsa := succ_complete ha
  have hns := ackermann_tower_normal f (succ a) hf hsa
  induction x using ltRec with
  | ind x ihx =>
  refine equiv_intro ?_ ?_
  · refine le_trans (ackermann_tower_unroll_nonzero f hf (succ a)
      (fun i hi _ => ackermann_tower_normal f i hf hi) x (succ a) (le_refl _) (succ_trans (zero_least a))
      hsa hx).le (sup_least fun _ => ?_)
    refine normal_fix_least hF _ _ (hE.complete x hx) ?_ (Con.enum_are_fixpoints hF x hx).ge
    exact limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) (complete_subord hx i)).le
      (hE.increasing _ _ hx (index_lt x i))
  · exact enum_least' hF x _ hx (hns.complete x hx)
      (ackermann_tower_fixpoint f (succ a) a x hf hsa ha hx (succ_lt a))
      fun x' hx' h => lt_of_le_of_lt (ihx x' h hx').ge (hns.increasing _ _ hx h)

/-- Rocq: `AckermannTower.ackermann_tower_add_closed`. -/
theorem ackermann_tower_add_closed (f : Ordinal.{u} → Ordinal.{u}) (α x p q : Ordinal.{u})
    (hf : NormalFunction f) (hα : Complete α) (hx : Complete x) (hα₀ : 0 < α)
    (hp : p < ackermannTower f α x) (hq : q < ackermannTower f α x) : p + q < ackermannTower f α x := by
  have hAc := (ackermann_tower_normal f α hf hα).complete x hx
  have h0 := ackermann_tower_normal f 0 hf zero_complete
  have hpow : ω ^ ackermannTower f α x ≤ ackermannTower f α x :=
    le_trans (add_zero _).ge (le_trans (veblen_onePlus _ hAc 0 zero_complete).ge
      (le_trans (veblen_monotone_func onePlus_normal h0 (fun z hz => onePlus_least_normal h0 z hz) _ 0 hAc
        zero_complete) (ackermann_tower_fixpoint f α 0 x hf hα zero_complete hx hα₀)))
  have hinf : ackermannTower f α x ≤ ω ^ ackermannTower f α x :=
    le_trans (normal_inflationary (veblen_first_normal onePlus_normal) _ hAc)
      (le_trans (veblen_onePlus _ hAc 0 zero_complete).le (add_zero _).le)
  exact lt_of_lt_of_le (powOmega_additively_closed hAc p q (lt_of_lt_of_le hp hinf) (lt_of_lt_of_le hq hinf)) hpow

/-! ## Finite towers and the Ackermann ordinals -/

/-- Rocq: `AckermannTower.ackermann_tower_fin`. -/
def ackermannTowerFin (f : Ordinal.{u} → Ordinal.{u}) : Nat → Ordinal.{u} → Ordinal.{u}
  | 0 => f
  | n + 1 => enumFixpoints fun x => veblen (ackermannTowerFin f n) x 0

/-- Rocq: `AckermannTower.ackermann_tower_fin_normal`. -/
theorem ackermann_tower_fin_normal (a : Nat) :
    ∀ f : Ordinal.{u} → Ordinal.{u}, NormalFunction f → NormalFunction (ackermannTowerFin f a) := by
  induction a with
  | zero => intro f hf; exact hf
  | succ a ih => intro f hf; exact enum_fixpoints_normal (veblen_first_normal (ih f hf))

/-- Rocq: `AckermannTower.ackermann_tower_fin_monotone_S`. -/
theorem ackermann_tower_fin_monotone_S (f : Ordinal.{u} → Ordinal.{u}) (n : Nat) (x : Ordinal.{u})
    (hf : NormalFunction f) (hx : Complete x) : ackermannTowerFin f n x ≤ ackermannTowerFin f (n + 1) x := by
  have hn := ackermann_tower_fin_normal n f hf
  have hE := ackermann_tower_fin_normal (n + 1) f hf
  have hEc := hE.complete x hx
  refine le_trans ?_ (Con.enum_are_fixpoints (veblen_first_normal hn) x hx).ge
  refine le_trans ?_ (veblen_fax hn _ 0 hEc zero_complete)
  exact hn.monotone _ _ (le_trans (normal_inflationary hE x hx) (add_zero _).ge)

/-- Rocq: `AckermannTower.ackermann_tower_fin_monotone1`. -/
theorem ackermann_tower_fin_monotone1 (f : Ordinal.{u} → Ordinal.{u}) (m n : Nat) (x : Ordinal.{u})
    (hf : NormalFunction f) (hmn : m ≤ n) (hx : Complete x) :
    ackermannTowerFin f m x ≤ ackermannTowerFin f n x := by
  induction hmn with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (ackermann_tower_fin_monotone_S f _ x hf hx)

/-- Rocq: `AckermannTower.ackermann_tower_fin_monotone`. -/
theorem ackermann_tower_fin_monotone (f : Ordinal.{u} → Ordinal.{u}) (m n : Nat) (x y : Ordinal.{u})
    (hf : NormalFunction f) (hmn : m ≤ n) (hxy : x ≤ y) (hx : Complete x) :
    ackermannTowerFin f m x ≤ ackermannTowerFin f n y :=
  le_trans (ackermann_tower_fin_monotone1 f m n x hf hmn hx) ((ackermann_tower_fin_normal n f hf).monotone x y hxy)

/-- Rocq: `AckermannTower.ackermann_tower_fin_eq`. -/
theorem ackermann_tower_fin_eq (a : Nat) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}), NormalFunction f → Complete x →
      ackermannTowerFin f a x ≈ ackermannTower f (ofNat a) x := by
  induction a with
  | zero => intro f x _ _; exact equiv_symm (ackermann_tower_zero f x)
  | succ a ih =>
    intro f x hf hx
    have hn₁ := ackermann_tower_fin_normal a f hf
    have hn₂ := ackermann_tower_normal f (ofNat a) hf (ofNat_complete a)
    refine equiv_trans ?_ (equiv_symm (ackermann_tower_succ f (ofNat a) x hf (ofNat_complete a) hx))
    exact equiv_intro
      (Con.enum_fixpoints_func_mono (veblen_first_normal hn₁) (veblen_first_normal hn₂)
        (fun z hz => veblen_monotone_func hn₁ hn₂ (fun w hw => (ih f w hf hw).le) z 0 hz zero_complete) x hx)
      (Con.enum_fixpoints_func_mono (veblen_first_normal hn₂) (veblen_first_normal hn₁)
        (fun z hz => veblen_monotone_func hn₂ hn₁ (fun w hw => (ih f w hf hw).ge) z 0 hz zero_complete) x hx)

/-- Rocq: `AckermannTower.ackermann_tower_fin_fixpoints`. -/
theorem ackermann_tower_fin_fixpoints (n : Nat) (f : Ordinal.{u} → Ordinal.{u}) (m : Nat) (x : Ordinal.{u})
    (hf : NormalFunction f) (hmn : m < n) (hx : Complete x) :
    veblen (ackermannTowerFin f m) (ackermannTowerFin f n x) 0 ≤ ackermannTowerFin f n x := by
  match n, hmn with
  | n + 1, hmn =>
    have hm := ackermann_tower_fin_normal m f hf
    have hn := ackermann_tower_fin_normal n f hf
    have hEc := (ackermann_tower_fin_normal (n + 1) f hf).complete x hx
    exact le_trans (veblen_monotone_func hm hn (fun z hz => ackermann_tower_fin_monotone f m n z z hf
        (Nat.le_of_lt_succ hmn) (le_refl z) hz) _ 0 hEc zero_complete)
      (Con.enum_are_fixpoints (veblen_first_normal hn) x hx).ge

/-- The small Ackermann ordinal. Rocq: `AckermannTower.SmallAckermannOrdinal`. -/
def SmallAckermannOrdinal : Ordinal.{u} :=
  sup fun n : (ω : Ordinal.{u}).Carrier => ackermannTowerFin (fun y => 1 + y) n.down 0

/-- The large Ackermann ordinal. Rocq: `AckermannTower.LargeAckermannOrdinal`. -/
def LargeAckermannOrdinal : Ordinal.{u} := fixOrd (fun x => ackermannTower (fun y => 1 + y) x 0) 0

/-- Rocq: `AckermannTower.ackermann_tower_base_le`. -/
theorem ackermann_tower_base_le (a : Ordinal.{u}) :
    ∀ x, Complete a → Complete x → ackermannTower powOmega a x ≤ ackermannTower (fun y => 1 + y) (1 + a) x := by
  induction a using ltRec with
  | ind a iha =>
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro ha hx
  have h1a := onePlus_complete ha
  have hn1 := ackermann_tower_normal _ (1 + a) onePlus_normal h1a
  have hY := hn1.complete x hx
  rw [ackermann_tower_unroll powOmega a x]
  refine lub_least ?_ (sup_least fun a' => ?_)
  · have h0 := ackermann_tower_normal _ 0 onePlus_normal zero_complete
    refine le_trans ?_ (ackermann_tower_fixpoint _ (1 + a) 0 x onePlus_normal h1a zero_complete hx
      (onePlus_nonzero a))
    refine le_trans ?_ (veblen_monotone_func onePlus_normal h0 (fun z hz => onePlus_least_normal h0 z hz) _ 0
      hY zero_complete)
    exact le_trans (pow_le_pow_right ω (normal_inflationary hn1 x hx))
      (le_trans (add_zero _).ge (veblen_onePlus _ hY 0 zero_complete).ge)
  · have hna := complete_subord ha a'
    have hω := ackermann_tower_normal powOmega _ powOmega_normal hna
    have h1a' := onePlus_complete hna
    refine normal_fix_least (veblen_first_normal hω) _ _ hY ?_ ?_
    · exact limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) ha (complete_subord hx i))
        (ackermann_tower_increasing _ (1 + a) onePlus_normal h1a _ _ hx (index_lt x i))
    · exact le_trans (veblen_monotone_func hω (ackermann_tower_normal _ _ onePlus_normal h1a')
          (fun z hz => iha (a a') (index_lt a a') z hna hz) _ 0 hY zero_complete)
        (ackermann_tower_fixpoint _ (1 + a) (1 + a a') x onePlus_normal h1a h1a' hx
          (add_lt_add_left 1 (index_lt a a')))

/-- Rocq: `AckermannTower.ackermann_tower_fix_limit`. -/
theorem ackermann_tower_fix_limit (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) (hf : NormalFunction f)
    (hx : Complete x) : IsLimit (fixOrd (fun x => ackermannTower f x 0) x) := by
  have hN := ackermann_tower_normal_first f hf
  have hΦ : Complete (fixOrd (fun x => ackermannTower f x 0) x) :=
    normal_fix_complete x hx (normal_inflationary hN) hN.monotone hN.complete
  have hfix := normal_fixpoint hN x hx
  have hΦ₀ : 0 < fixOrd (fun x => ackermannTower f x 0) x :=
    lt_of_lt_of_le (ackermann_tower_nonzero f _ 0 hf) hfix.ge
  refine additively_closed_limit ?_ fun p q hp hq => ?_
  · calc (1 : Ordinal.{u}) ≈ 1 + 0 := equiv_symm (add_zero 1)
      _ ≤ f 0 := onePlus_least_normal hf 0 zero_complete
      _ < f (fixOrd (fun x => ackermannTower f x 0) x + 0) :=
          hf.increasing _ _ (add_complete hΦ zero_complete) (lt_of_lt_of_le hΦ₀ (add_zero _).ge)
      _ ≤ ackermannTower f (fixOrd (fun x => ackermannTower f x 0) x) 0 :=
          ackermann_tower_fax f _ 0 hf hΦ zero_complete
      _ ≤ fixOrd (fun x => ackermannTower f x 0) x := hfix.ge
  · exact lt_of_lt_of_le (ackermann_tower_add_closed f _ 0 p q hf hΦ zero_complete hΦ₀
      (lt_of_lt_of_le hp hfix.le) (lt_of_lt_of_le hq hfix.le)) hfix.ge

/-- Rocq: `AckermannTower.LargeAckermannOrdinal_limit`. -/
theorem LargeAckermannOrdinal_limit : IsLimit (LargeAckermannOrdinal.{u}) :=
  ackermann_tower_fix_limit _ 0 onePlus_normal zero_complete

/-- Rocq: `AckermannTower.ackermann_tower_base_eq`. -/
theorem ackermann_tower_base_eq (a : Ordinal.{u}) :
    ∀ x, Complete a → Complete x → 1 + a ≤ a →
      ackermannTower (fun y => 1 + y) a x ≈ ackermannTower powOmega a x := by
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro ha hx h1a
  have hn1 := ackermann_tower_normal _ a onePlus_normal ha
  have hY := hn1.complete x hx
  refine equiv_intro (ackermann_tower_monotone_func _ _ a x onePlus_normal powOmega_normal ha hx
    (fun z hz => onePlus_least_normal powOmega_normal z hz)) ?_
  rw [ackermann_tower_unroll powOmega a x]
  refine lub_least ?_ (sup_least fun a' => ?_)
  · refine le_trans (show powOmega x ≤ ackermannTower powOmega 0 x by
      rw [ackermann_tower_unroll powOmega 0 x]; exact lub_le1 _ _) ?_
    exact le_trans (ackermann_tower_base_le 0 x zero_complete hx)
      (ackermann_tower_monotone _ onePlus_normal.monotone _ _ x x
        (le_trans (add_le_add (le_refl 1) (zero_least a)) h1a) (le_refl x))
  · have hna := complete_subord ha a'
    have hω := ackermann_tower_normal powOmega _ powOmega_normal hna
    have h1a' := onePlus_complete hna
    refine normal_fix_least (veblen_first_normal hω) _ _ hY ?_ ?_
    · exact limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) ha (complete_subord hx i) h1a).ge
        (ackermann_tower_increasing _ a onePlus_normal ha _ _ hx (index_lt x i))
    · exact le_trans (veblen_monotone_func hω (ackermann_tower_normal _ _ onePlus_normal h1a')
          (fun z hz => ackermann_tower_base_le (a a') z hna hz) _ 0 hY zero_complete)
        (ackermann_tower_fixpoint _ a (1 + a a') x onePlus_normal ha h1a' hx
          (lt_of_lt_of_le (add_lt_add_left 1 (index_lt a a')) h1a))

/-- Rocq: `AckermannTower.SmallAckermannOrdinal_alt`. -/
theorem SmallAckermannOrdinal_alt :
    SmallAckermannOrdinal.{u} ≈ ackermannTower (fun y => 1 + y) ω 0 := by
  refine equiv_intro (sup_least fun i => ?_) ?_
  · exact le_trans (ackermann_tower_fin_eq i.down _ 0 onePlus_normal zero_complete).le
      (ackermann_tower_monotone _ onePlus_normal.monotone _ _ 0 0 (le_of_lt (index_lt ω i)) (le_refl 0))
  · rw [ackermann_tower_unroll]
    refine lub_least ?_ (sup_least fun i => ?_)
    · have h0 : (0 : Ordinal.{u}) < SmallAckermannOrdinal :=
        lt_of_lt_of_le ((ackermann_tower_fin_normal 0 _ onePlus_normal).nonzero 0)
          (sup_le (fun n : (ω : Ordinal.{u}).Carrier => ackermannTowerFin (fun y => 1 + y) n.down 0) ⟨0⟩)
      exact le_trans (add_zero 1).le (succ_least h0)
    · have hni := ackermann_tower_normal _ (ofNat i.down) onePlus_normal (ofNat_complete _)
      have hY := (ackermann_tower_normal _ (ofNat (i.down + 1)) onePlus_normal (ofNat_complete _)).complete 0
        zero_complete
      refine le_trans ?_ (le_trans (ackermann_tower_fin_eq (i.down + 1) _ 0 onePlus_normal zero_complete).ge
        (sup_le (fun n : (ω : Ordinal.{u}).Carrier => ackermannTowerFin (fun y => 1 + y) n.down 0) ⟨i.down + 1⟩))
      exact normal_fix_least (veblen_first_normal hni) _ _ hY (lim_zero_le _)
        (ackermann_tower_fixpoint _ (ofNat (i.down + 1)) (ofNat i.down) 0 onePlus_normal (ofNat_complete _)
          (ofNat_complete _) zero_complete (succ_lt _))

/-- Rocq: `AckermannTower.SmallAckermannOrdinal_alt2`. -/
theorem SmallAckermannOrdinal_alt2 : SmallAckermannOrdinal.{u} ≈ ackermannTower powOmega ω 0 :=
  equiv_trans SmallAckermannOrdinal_alt (ackermann_tower_base_eq ω 0 omega_complete zero_complete
    (additively_closed_collapse additively_closed_omega omega_gt1))

/-- Rocq: `AckermannTower.LargeAckermannOrdinal_alt`. -/
theorem LargeAckermannOrdinal_alt :
    LargeAckermannOrdinal.{u} ≈ fixOrd (fun x => ackermannTower powOmega x 0) 0 := by
  have h1 := ackermann_tower_normal_first _ onePlus_normal
  have hω := ackermann_tower_normal_first _ powOmega_normal
  have hΦ1 : Complete (fixOrd (fun x => ackermannTower (fun y => 1 + y) x 0) (0 : Ordinal.{u})) :=
    normal_fix_complete 0 zero_complete (normal_inflationary h1) h1.monotone h1.complete
  have hΦω : Complete (fixOrd (fun x => ackermannTower powOmega x 0) (0 : Ordinal.{u})) :=
    normal_fix_complete 0 zero_complete (normal_inflationary hω) hω.monotone hω.complete
  have hf1 := normal_fixpoint h1 0 zero_complete
  have hfω := normal_fixpoint hω 0 zero_complete
  refine equiv_intro (normal_fix_least h1 0 _ hΦω (zero_least _) ?_)
    (normal_fix_least hω 0 _ hΦ1 (zero_least _) ?_)
  · exact le_trans (ackermann_tower_base_eq _ 0 hΦω zero_complete
      (le_trans (onePlus_least_normal hω _ hΦω) hfω.ge)).le hfω.ge
  · exact le_trans (ackermann_tower_base_eq _ 0 hΦ1 zero_complete
      (le_trans (onePlus_least_normal h1 _ hΦ1) hf1.ge)).ge hf1.ge

end Ordinal

end ConstructiveOrdinals
