import ConstructiveOrdinals.NaturalArith
import ConstructiveOrdinals.Classical
import ConstructiveOrdinals.Prelude.List

/-!
# The natural (Hessenberg) product, constructively

Port of `Ordinal/NaturalProduct.v`.

Classically, the natural product `a ⊗ b` is the maximal order type of the
product partial order `a × b` (de Jongh and Parikh), which is also the rank of
the tree of bad sequences in `a × b`. `nmul` is defined by playing that game
directly: a position is a down-closed region of the plane, given as a finite
union of rectangles; a move picks a point of the region and deletes the upward
cone above it.

The cone is removed from each rectangle using the (constructive) binary glb,
so no decisions about whether the point lies inside a rectangle are needed:

    (x × y) \ ↑p  =  ((x ⊓ px) × y)  ∪  (x × (y ⊓ py)).

Termination is by structural recursion on an explicit fuel ordinal; the fuel
is bounded by the "one-sided" recursion `gbound` (the incorrect natural
product of `NaturalArith`), which makes it provably sufficient, and the result
is independent of the fuel.

## Guide to the results

Constructive (no axioms):
- `nmul_comm`, `nmul_monotone`, `nmul_increasing1`, `nmul_increasing2`,
  `nmul_zero`, `nmul_one`;
- `nmul_succ_upper`: `a ⊗ (b+1) ≤ a ⊗ b ♯ a`;
- `covers_rk`: the upper half of distributivity, given any split of `b ♯ c`
  into two strictly increasing pieces;
- the game machinery: fuel independence (`nmul_fuel`), the fuel-free rank
  `rk`, subadditivity (`rk_app_le`) and the chain lemma (`rk_chain`);
- on a universe `Q` with a decidable order: superdistributivity
  (`nmul_distrib_lower_Q`) and subdistributivity given a split at the points
  of `Q` (`covers_rk_Q`).

Classical (the excluded middle as an explicit hypothesis):
- `nmul_succ_classical`: `a ⊗ (b+1) ≈ a ⊗ b ♯ a`;
- `nmul_distrib`: `a ⊗ (b ♯ c) ≈ a ⊗ b ♯ a ⊗ c`;
- `nmul_exp`: `ω^α ⊗ ω^β ≈ ω^(α ♯ β)`;
- `nmul_is_hessenberg`: on Cantor normal forms, `a ⊗ b` is the natural sum of
  `ω^(αi ♯ βj)` over all pairs of terms, i.e. `nmul` is Hessenberg's natural
  product.

Reverse results:
- `succ_lower_WEM`: the lower half of the successor law, for all ordinals,
  implies the weak excluded middle; hence so does the lower half of
  distributivity (`distrib_lower_WEM`);
- `succ_lower_complete_WEM`, `distrib_lower_complete_WEM`: the same, even
  restricted to complete ordinals;
- `split_WEM`: a total split of `b ♯ c`, as used by `covers_rk`, implies the
  weak excluded middle;
- `row_lower_EM`: the lower half of the row lemma over an arbitrary region
  implies the excluded middle.

Lean notes:
- The product is `NaturalProduct.nmul`, written `a ⊗ b` only in docstrings:
  `⊗` is not declared as notation, to avoid confusion with
  `Ordinal.IncorrectNmul`.
- Rocq's `cut` is a `flat_map`; here it is the same list built by direct
  recursion, so that its membership lemmas are axiom-free.
- The game lives in the namespace `ConstructiveOrdinals.NaturalProduct`, as
  its names (`cut`, `rk`, `Region`, …) are too generic for `Ordinal`.
-/

namespace ConstructiveOrdinals.NaturalProduct

open Ordinal

universe u

/-- A position: a finite union of rectangles. Rocq: `NaturalProduct.region`. -/
abbrev Region := List (Ordinal.{u} × Ordinal.{u})

/-- Moves: choose a rectangle and a child in each coordinate.
Rocq: `NaturalProduct.mv`. -/
def Mv : Region.{u} → Type u
  | [] => PEmpty
  | r :: D => (r.1.Carrier × r.2.Carrier) ⊕ Mv D

/-- The point played by a move. Rocq: `NaturalProduct.mvpt`. -/
def mvpt : (D : Region.{u}) → Mv D → Ordinal.{u} × Ordinal.{u}
  | [], m => PEmpty.elim m
  | r :: _, .inl cd => (r.1 cd.1, r.2 cd.2)
  | _ :: D, .inr m => mvpt D m

/-- Delete the upward cone above `p` from every rectangle.
Rocq: `NaturalProduct.cut`. -/
def cut (p : Ordinal.{u} × Ordinal.{u}) : Region.{u} → Region.{u}
  | [] => []
  | r :: D => (r.1 ⊓ p.1, r.2) :: (r.1, r.2 ⊓ p.2) :: cut p D

/-- The rank of a position, by recursion on an explicit fuel ordinal.
Rocq: `NaturalProduct.grank`. -/
def grank : Ordinal.{u} → Region.{u} → Ordinal.{u}
  | mk F h, D => mk (F × Mv D) fun km => grank (h km.1) (cut (mvpt D km.2) D)

/-- The inner `fix` of Rocq's `gbound`, on the second argument; `outer` is
the outer recursive call. -/
def gboundInner {A : Type u} (outer : A → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk B g => mk (A × B) fun ab => outer ab.1 (mk B g) ♯ gboundInner outer (g ab.2)

/-- The fuel bound: the "one-sided" recursion (essentially the incorrect
natural product). It overestimates the natural product, which is exactly what
fuel needs; see `grank_le_measure`. Rocq: `NaturalProduct.gbound`. -/
def gbound : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | mk _ f => gboundInner fun a => gbound (f a)

/-- The natural product. Rocq: `NaturalProduct.nmulOrd`. -/
def nmul (a b : Ordinal.{u}) : Ordinal.{u} := grank (succ (gbound a b)) [(a, b)]

/-! ## Moves and points -/

/-- Rocq: `NaturalProduct.mv_intro`. -/
theorem mv_intro : ∀ (D : Region.{u}) (r : Ordinal.{u} × Ordinal.{u}), r ∈ D →
    ∀ (c : r.1.Carrier) (d : r.2.Carrier), ∃ m : Mv D, mvpt D m = (r.1 c, r.2 d)
  | _ :: _, _, .head _, c, d => ⟨.inl (c, d), rfl⟩
  | _ :: D, r, .tail _ h, c, d =>
    let ⟨m, hm⟩ := mv_intro D r h c d
    ⟨.inr m, hm⟩

/-- Rocq: `NaturalProduct.mv_elim`. -/
theorem mv_elim : ∀ (D : Region.{u}) (m : Mv D), ∃ r, r ∈ D ∧
    ∃ (c : r.1.Carrier) (d : r.2.Carrier), mvpt D m = (r.1 c, r.2 d)
  | [], m => PEmpty.elim m
  | r :: _, .inl (c, d) => ⟨r, .head _, c, d, rfl⟩
  | _ :: D, .inr m =>
    let ⟨r, hr, c, d, h⟩ := mv_elim D m
    ⟨r, .tail _ hr, c, d, h⟩

/-! ## Region inclusion

A rectangle of `D` is either empty (one side `≤ 0`) or is dominated
componentwise by some rectangle of `E`. -/

/-- Rocq: `NaturalProduct.rle`. -/
def Rle (r s : Ordinal.{u} × Ordinal.{u}) : Prop := r.1 ≤ s.1 ∧ r.2 ≤ s.2

/-- Rocq: `NaturalProduct.rsub`. -/
def Rsub (D E : Region.{u}) : Prop :=
  ∀ r, r ∈ D → (r.1 ≤ 0 ∨ r.2 ≤ 0) ∨ ∃ s, s ∈ E ∧ Rle r s

/-- Rocq: `NaturalProduct.rsub_refl`. -/
theorem rsub_refl (D : Region.{u}) : Rsub D D := fun r hr =>
  .inr ⟨r, hr, le_refl _, le_refl _⟩

/-- Rocq: `NaturalProduct.rsub_trans`. -/
theorem rsub_trans {D E F : Region.{u}} (hDE : Rsub D E) (hEF : Rsub E F) : Rsub D F := fun r hr =>
  match hDE r hr with
  | .inl hz => .inl hz
  | .inr ⟨s, hs, h₁, h₂⟩ =>
    match hEF s hs with
    | .inl (.inl hz) => .inl (.inl (le_trans h₁ hz))
    | .inl (.inr hz) => .inl (.inr (le_trans h₂ hz))
    | .inr ⟨t, ht, h₃, h₄⟩ => .inr ⟨t, ht, le_trans h₁ h₃, le_trans h₂ h₄⟩

/-- The rectangles of `cut p D`. -/
theorem mem_cut {p : Ordinal.{u} × Ordinal.{u}} :
    ∀ {D : Region.{u}} {r}, r ∈ cut p D →
      ∃ r₀, r₀ ∈ D ∧ (r = (r₀.1 ⊓ p.1, r₀.2) ∨ r = (r₀.1, r₀.2 ⊓ p.2))
  | r₀ :: _, _, .head _ => ⟨r₀, .head _, .inl rfl⟩
  | r₀ :: _, _, .tail _ (.head _) => ⟨r₀, .head _, .inr rfl⟩
  | _ :: _, _, .tail _ (.tail _ h) =>
    let ⟨r₁, hr₁, he⟩ := mem_cut h
    ⟨r₁, .tail _ hr₁, he⟩

theorem mem_cut_left {p : Ordinal.{u} × Ordinal.{u}} :
    ∀ {D : Region.{u}} {r₀}, r₀ ∈ D → (r₀.1 ⊓ p.1, r₀.2) ∈ cut p D
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ h => .tail _ (.tail _ (mem_cut_left h))

theorem mem_cut_right {p : Ordinal.{u} × Ordinal.{u}} :
    ∀ {D : Region.{u}} {r₀}, r₀ ∈ D → (r₀.1, r₀.2 ⊓ p.2) ∈ cut p D
  | _ :: _, _, .head _ => .tail _ (.head _)
  | _ :: _, _, .tail _ h => .tail _ (.tail _ (mem_cut_right h))

/-- Rocq: `NaturalProduct.cut_mono`. -/
theorem cut_mono {p p' : Ordinal.{u} × Ordinal.{u}} {D E : Region.{u}} (hp : Rle p p')
    (hDE : Rsub D E) : Rsub (cut p D) (cut p' E) := fun r hr => by
  obtain ⟨r₀, hr₀, he⟩ := mem_cut hr
  rcases he with rfl | rfl
  · match hDE r₀ hr₀ with
    | .inl (.inl hz) => exact .inl (.inl (le_trans (glb_le1 _ _) hz))
    | .inl (.inr hz) => exact .inl (.inr hz)
    | .inr ⟨s, hs, h₁, h₂⟩ =>
      exact .inr ⟨(s.1 ⊓ p'.1, s.2), mem_cut_left hs,
        glb_greatest _ _ _ (le_trans (glb_le1 _ _) h₁) (le_trans (glb_le2 _ _) hp.1), h₂⟩
  · match hDE r₀ hr₀ with
    | .inl (.inl hz) => exact .inl (.inl hz)
    | .inl (.inr hz) => exact .inl (.inr (le_trans (glb_le1 _ _) hz))
    | .inr ⟨s, hs, h₁, h₂⟩ =>
      exact .inr ⟨(s.1, s.2 ⊓ p'.2), mem_cut_right hs, h₁,
        glb_greatest _ _ _ (le_trans (glb_le1 _ _) h₂) (le_trans (glb_le2 _ _) hp.2)⟩

/-! ## Monotonicity in fuel and in the region (constructive) -/

/-- Rocq: `NaturalProduct.grank_unfold_lt`. -/
theorem grank_unfold_lt : ∀ (β : Ordinal.{u}) (D : Region.{u}) (k : β) (m : Mv D),
    grank (β k) (cut (mvpt D m) D) < grank β D
  | mk _ _, _, k, m => lt_intro (show (grank (mk _ _) _).Carrier from (k, m)) (le_refl _)

/-- Rocq: `NaturalProduct.grank_mono`. -/
theorem grank_mono : ∀ (β β' : Ordinal.{u}) (D E : Region.{u}),
    β ≤ β' → Rsub D E → grank β D ≤ grank β' E
  | mk F h, β', D, E, hβ, hDE => le_intro fun ⟨k, m⟩ => by
    obtain ⟨k', hk'⟩ := lt_elim (le_elim hβ k)
    obtain ⟨r, hr, c, d, hm⟩ := mv_elim D m
    match hDE r hr with
    | .inl (.inl hz) => exact (zero_lt _ (lt_of_lt_of_le (index_lt r.1 c) hz)).elim
    | .inl (.inr hz) => exact (zero_lt _ (lt_of_lt_of_le (index_lt r.2 d) hz)).elim
    | .inr ⟨s, hs, h₁, h₂⟩ =>
      obtain ⟨c', hc⟩ := lt_elim (lt_of_lt_of_le (index_lt r.1 c) h₁)
      obtain ⟨d', hd⟩ := lt_elim (lt_of_lt_of_le (index_lt r.2 d) h₂)
      obtain ⟨m', hm'⟩ := mv_intro E s hs c' d'
      have hp : Rle (mvpt D m) (mvpt E m') := by rw [hm, hm']; exact ⟨hc, hd⟩
      exact lt_of_le_of_lt (grank_mono (h k) (β' k') _ _ hk' (cut_mono hp hDE))
        (grank_unfold_lt β' E k' m')

/-- Rocq: `NaturalProduct.grank_le_fuel`. -/
theorem grank_le_fuel : ∀ (β : Ordinal.{u}) (D : Region.{u}), grank β D ≤ β
  | mk F h, _ => le_intro fun km =>
    lt_intro (show (mk F h).Carrier from km.1) (grank_le_fuel (h km.1) _)

/-- A region with no moves has rank zero. Rocq: `NaturalProduct.grank_nomoves`. -/
theorem grank_nomoves : ∀ (β : Ordinal.{u}) (D : Region.{u}), (Mv D → False) → grank β D ≈ 0
  | mk _ _, _, h => equiv_intro (le_intro fun km => (h km.2).elim) (zero_least _)

/-! ## List facts, proved without `propext` -/

private theorem mem_append_cases {α : Type u} {a : α} :
    ∀ {l₁ l₂ : List α}, a ∈ l₁ ++ l₂ → a ∈ l₁ ∨ a ∈ l₂
  | [], _, h => .inr h
  | _ :: _, _, .head _ => .inl (.head _)
  | _ :: _, _, .tail _ h =>
    match mem_append_cases h with
    | .inl h => .inl (.tail _ h)
    | .inr h => .inr h

private theorem mem_split {α : Type u} {a : α} :
    ∀ {l : List α}, a ∈ l → ∃ l₁ l₂, l = l₁ ++ a :: l₂
  | _ :: l, .head _ => ⟨[], l, rfl⟩
  | b :: _, .tail _ h =>
    let ⟨l₁, l₂, he⟩ := mem_split h
    ⟨b :: l₁, l₂, congrArg (b :: ·) he⟩

private theorem mem_map_of_mem {α β : Type u} (f : α → β) {a : α} :
    ∀ {l : List α}, a ∈ l → f a ∈ l.map f
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ h => .tail _ (mem_map_of_mem f h)

private theorem exists_of_mem_map {α β : Type u} {f : α → β} {b : β} :
    ∀ {l : List α}, b ∈ l.map f → ∃ a, a ∈ l ∧ f a = b
  | a :: _, .head _ => ⟨a, .head _, rfl⟩
  | _ :: _, .tail _ h =>
    let ⟨a, ha, he⟩ := exists_of_mem_map h
    ⟨a, .tail _ ha, he⟩

/-! ## Fuel independence

Once the fuel is sufficient (`grank β D < β`), adding more fuel changes
nothing. This is fully constructive. -/

/-- Rocq: `NaturalProduct.grank_stable`. -/
theorem grank_stable : ∀ (β' β : Ordinal.{u}) (D : Region.{u}),
    grank β D < β → grank β' D ≤ grank β D
  | mk F' h', mk F h, D, hs => le_intro fun km => by
    obtain ⟨k, hk⟩ := lt_elim hs
    exact lt_of_le_of_lt (grank_stable (h' km.1) (h k) (cut (mvpt D km.2) D)
        (lt_of_lt_of_le (grank_unfold_lt (mk F h) D k km.2) hk))
      (grank_unfold_lt (mk F h) D k km.2)

/-- Rocq: `NaturalProduct.grank_stable_eq`. -/
theorem grank_stable_eq (β β' : Ordinal.{u}) (D : Region.{u}) (hs : grank β D < β) (hle : β ≤ β') :
    grank β' D ≈ grank β D :=
  equiv_intro (grank_stable β' β D hs) (grank_mono β β' D D hle (rsub_refl D))

/-- Any fuel at least as large as the value already computed is enough.
Rocq: `NaturalProduct.grank_value_fuel`. -/
theorem grank_value_fuel : ∀ (γ β : Ordinal.{u}) (D : Region.{u}),
    grank β D ≤ γ → grank β D ≤ grank γ D
  | mk G j, mk F h, D, H => le_intro fun km => by
    have hv : grank (h km.1) (cut (mvpt D km.2) D) < mk G j :=
      lt_of_lt_of_le (grank_unfold_lt (mk F h) D km.1 km.2) H
    obtain ⟨jj, hjj⟩ := lt_elim hv
    exact lt_of_le_of_lt (grank_value_fuel (j jj) (h km.1) _ hjj) (grank_unfold_lt (mk G j) D jj km.2)

/-! ## A constructive bound on the rank -/

/-- Rocq: `NaturalProduct.gbound_unfold`. -/
theorem gbound_unfold (x y : Ordinal.{u}) :
    gbound x y = mk (x.Carrier × y.Carrier) fun ab => gbound (x ab.1) y ♯ gbound x (y ab.2) := by
  cases x; cases y; rfl

/-- Rocq: `NaturalProduct.gbound_monotone`. -/
theorem gbound_monotone (x : Ordinal.{u}) :
    ∀ x' y y' : Ordinal.{u}, x ≤ x' → y ≤ y' → gbound x y ≤ gbound x' y' := by
  induction x using ltRec with
  | ind x ihx =>
    intro x' y
    induction y using ltRec generalizing x' with
    | ind y ihy =>
      intro y' hx hy
      rw [gbound_unfold x y, gbound_unfold x' y']
      exact le_intro fun ab => by
        obtain ⟨a', ha'⟩ := lt_elim (le_elim hx ab.1)
        obtain ⟨b', hb'⟩ := lt_elim (le_elim hy ab.2)
        exact lt_intro (show (mk (x'.Carrier × y'.Carrier) fun ab =>
            gbound (x' ab.1) y' ♯ gbound x' (y' ab.2)).Carrier from (a', b'))
          (nadd_le_nadd (ihx (x ab.1) (index_lt x ab.1) (x' a') y y' ha' hy)
            (ihy (y ab.2) (index_lt y ab.2) x' (y' b') hx hb'))

/-- The natural sum of the bounds of the rectangles.
Rocq: `NaturalProduct.gmeasure`. -/
def gmeasure : Region.{u} → Ordinal.{u}
  | [] => 0
  | r :: D => gbound r.1 r.2 ♯ gmeasure D

/-- Rocq: `NaturalProduct.gmeasure_app`. -/
theorem gmeasure_app : ∀ l₁ l₂ : Region.{u}, gmeasure (l₁ ++ l₂) ≈ gmeasure l₁ ♯ gmeasure l₂
  | [], _ => equiv_symm (nadd_zero_l _)
  | _ :: l₁, l₂ => equiv_trans (nadd_congr (equiv_refl _) (gmeasure_app l₁ l₂)) (nadd_assoc _ _ _)

/-- Rocq: `NaturalProduct.cut_piece_le`. -/
theorem cut_piece_le (p r₁ r₀ : Ordinal.{u} × Ordinal.{u})
    (h : r₀ ∈ [(r₁.1 ⊓ p.1, r₁.2), (r₁.1, r₁.2 ⊓ p.2)]) : Rle r₀ r₁ := by
  cases h with
  | head => exact ⟨glb_le1 _ _, le_refl _⟩
  | tail _ h =>
    cases h with
    | head => exact ⟨le_refl _, glb_le1 _ _⟩
    | tail _ h => nomatch h

private theorem piece_mem {p r₁ r₀ : Ordinal.{u} × Ordinal.{u}}
    (h : r₀ = (r₁.1 ⊓ p.1, r₁.2) ∨ r₀ = (r₁.1, r₁.2 ⊓ p.2)) :
    r₀ ∈ [(r₁.1 ⊓ p.1, r₁.2), (r₁.1, r₁.2 ⊓ p.2)] := by
  rcases h with rfl | rfl
  · exact .head _
  · exact .tail _ (.head _)

/-- Rocq: `NaturalProduct.cut_split`. -/
theorem cut_split (D : Region.{u}) (m : Mv D) :
    ∃ D', Rsub (cut (mvpt D m) D) D' ∧ gmeasure D' < gmeasure D := by
  obtain ⟨r, hr, c, d, hm⟩ := mv_elim D m
  rw [hm]
  obtain ⟨l₁, l₂, hD⟩ := mem_split hr
  refine ⟨l₁ ++ (r.1 ⊓ r.1 c, r.2) :: (r.1, r.2 ⊓ r.2 d) :: l₂, fun r₀ hr₀ => ?_, ?_⟩
  · obtain ⟨r₁, hr₁, he⟩ := mem_cut hr₀
    rw [hD] at hr₁
    rcases mem_append_cases hr₁ with h₁ | h₂
    · exact .inr ⟨r₁, List.mem_append_left _ h₁, cut_piece_le _ _ _ (piece_mem he)⟩
    · cases h₂ with
      | head =>
        refine .inr ⟨r₀, List.mem_append_right l₁ ?_, le_refl _, le_refl _⟩
        rcases he with rfl | rfl
        · exact .head _
        · exact .tail _ (.head _)
      | tail _ h₂ =>
        exact .inr ⟨r₁, List.mem_append_right l₁ (.tail _ (.tail _ h₂)),
          cut_piece_le _ _ _ (piece_mem he)⟩
  · rw [hD]
    have hchild : gbound (r.1 ⊓ r.1 c) r.2 ♯ gbound r.1 (r.2 ⊓ r.2 d) < gbound r.1 r.2 := by
      rw [gbound_unfold r.1 r.2]
      exact lt_intro (show (mk (r.1.Carrier × r.2.Carrier) fun ab =>
          gbound (r.1 ab.1) r.2 ♯ gbound r.1 (r.2 ab.2)).Carrier from (c, d))
        (nadd_le_nadd (gbound_monotone _ _ _ _ (glb_le2 _ _) (le_refl _))
          (gbound_monotone _ _ _ _ (le_refl _) (glb_le2 _ _)))
    exact lt_of_le_of_lt (gmeasure_app l₁ (_ :: _ :: l₂)).le (lt_of_lt_of_le
      (nadd_increasing2 _ (lt_of_le_of_lt (nadd_assoc _ _ _).le (nadd_increasing1 _ hchild)))
      (gmeasure_app l₁ (r :: l₂)).ge)

/-- The key estimate: cutting at a point of rectangle `r` is dominated by
splitting `r` alone into its two pieces, which strictly lowers the natural sum
of `gbound`s over the rectangles. Rocq: `NaturalProduct.grank_le_measure`. -/
theorem grank_le_measure : ∀ (β : Ordinal.{u}) (D : Region.{u}), grank β D ≤ gmeasure D
  | mk F h, D => le_intro fun km => by
    obtain ⟨D', hD', hlt⟩ := cut_split D km.2
    exact lt_of_le_of_lt (grank_mono (h km.1) (h km.1) _ _ (le_refl _) hD')
      (lt_of_le_of_lt (grank_le_measure (h km.1) D') hlt)

/-- Rocq: `NaturalProduct.grank_cut_lt_measure`. -/
theorem grank_cut_lt_measure (β : Ordinal.{u}) (D : Region.{u}) (m : Mv D) :
    grank β (cut (mvpt D m) D) < gmeasure D :=
  let ⟨D', hD', hlt⟩ := cut_split D m
  lt_of_le_of_lt (grank_mono β β _ _ (le_refl _) hD') (lt_of_le_of_lt (grank_le_measure β D') hlt)

/-- Rocq: `NaturalProduct.nmulOrd_sufficient`. -/
theorem nmul_sufficient (a b : Ordinal.{u}) :
    grank (succ (gbound a b)) [(a, b)] < succ (gbound a b) :=
  succ_trans (le_trans (grank_le_measure _ _) (nadd_zero_r _).le)

/-- The definition does not depend on the choice of fuel, so long as it
exceeds the bound. Rocq: `NaturalProduct.nmulOrd_fuel`. -/
theorem nmul_fuel (a b β : Ordinal.{u}) (hβ : gbound a b < β) : nmul a b ≈ grank β [(a, b)] :=
  equiv_symm (grank_stable_eq _ _ _ (nmul_sufficient a b) (succ_least hβ))

/-- Rocq: `NaturalProduct.nmulOrd_le_gbound`. -/
theorem nmul_le_gbound (a b : Ordinal.{u}) : nmul a b ≤ gbound a b :=
  le_trans (grank_le_measure _ _) (nadd_zero_r _).le

/-! ## Commutativity -/

/-- Rocq: `NaturalProduct.rswap`. -/
def rswap (r : Ordinal.{u} × Ordinal.{u}) : Ordinal.{u} × Ordinal.{u} := (r.2, r.1)

/-- Rocq: `NaturalProduct.swapR`. -/
def swapR (D : Region.{u}) : Region.{u} := D.map rswap

/-- Rocq: `NaturalProduct.cut_swap`. -/
theorem cut_swap (p : Ordinal.{u} × Ordinal.{u}) (D : Region.{u}) :
    Rsub (cut p (swapR D)) (swapR (cut (rswap p) D)) := fun r hr => by
  obtain ⟨r₀, hr₀, he⟩ := mem_cut hr
  obtain ⟨r₁, hr₁, rfl⟩ := exists_of_mem_map hr₀
  refine .inr ⟨r, ?_, le_refl _, le_refl _⟩
  rcases he with rfl | rfl
  · exact mem_map_of_mem rswap (mem_cut_right (p := rswap p) hr₁)
  · exact mem_map_of_mem rswap (mem_cut_left (p := rswap p) hr₁)

/-- Rocq: `NaturalProduct.grank_swap_le`. -/
theorem grank_swap_le : ∀ (β : Ordinal.{u}) (D : Region.{u}), grank β (swapR D) ≤ grank β D
  | mk F h, D => le_intro fun km => by
    obtain ⟨r, hr, c, d, hm⟩ := mv_elim _ km.2
    obtain ⟨r₀, hin, rfl⟩ := exists_of_mem_map hr
    obtain ⟨m', hm'⟩ := mv_intro D r₀ hin d c
    refine lt_of_le_of_lt ?_ (grank_unfold_lt (mk F h) D km.1 m')
    refine le_trans (grank_mono (h km.1) (h km.1) _ _ (le_refl _) (cut_swap _ _)) ?_
    refine le_trans (grank_swap_le (h km.1) _) ?_
    rw [hm, hm']
    exact le_refl _

/-- Rocq: `NaturalProduct.swapR_swapR`. -/
theorem swapR_swapR : ∀ D : Region.{u}, swapR (swapR D) = D
  | [] => rfl
  | r :: D => congrArg (r :: ·) (swapR_swapR D)

/-- Rocq: `NaturalProduct.grank_swap`. -/
theorem grank_swap (β : Ordinal.{u}) (D : Region.{u}) : grank β (swapR D) ≈ grank β D := by
  refine equiv_intro (grank_swap_le β D) ?_
  have h := grank_swap_le β (swapR D)
  rw [swapR_swapR] at h
  exact h

/-- Rocq: `NaturalProduct.nmulOrd_comm`. -/
theorem nmul_comm (a b : Ordinal.{u}) : nmul a b ≈ nmul b a :=
  let β := succ (gbound a b ⊔ gbound b a)
  equiv_trans (nmul_fuel a b β (succ_trans (lub_le1 _ _)))
    (equiv_trans (equiv_symm (grank_swap β [(a, b)]))
      (equiv_symm (nmul_fuel b a β (succ_trans (lub_le2 _ _)))))

/-! ## Monotonicity -/

/-- Rocq: `NaturalProduct.nmulOrd_monotone` and `NaturalProduct.nmulOrd_le_mor`. -/
@[ord_mono]
theorem nmul_monotone {a b a' b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') : nmul a b ≤ nmul a' b' :=
  le_trans (nmul_fuel a b (succ (gbound a' b')) (succ_trans (gbound_monotone _ _ _ _ ha hb))).le
    (grank_mono _ _ _ _ (le_refl _) fun r hr => by
      cases hr with
      | head => exact .inr ⟨(a', b'), .head _, ha, hb⟩
      | tail _ h => nomatch h)

/-- Rocq: `NaturalProduct.nmulOrd_increasing1`. -/
theorem nmul_increasing1 {a a' b : Ordinal.{u}} (ha : a < a') (hb : 0 < b) : nmul a b < nmul a' b := by
  obtain ⟨c', hc'⟩ := lt_elim ha
  obtain ⟨d, _⟩ := lt_elim hb
  refine lt_of_le_of_lt (le_trans (grank_value_fuel (gbound a' b) (succ (gbound a b)) [(a, b)]
      (le_trans (nmul_le_gbound a b) (gbound_monotone _ _ _ _ (le_of_lt ha) (le_refl _))))
    (grank_mono _ _ [(a, b)] (cut (mvpt [(a', b)] (.inl (c', d))) [(a', b)]) (le_refl _) ?_))
    (grank_unfold_lt (succ (gbound a' b)) [(a', b)] PUnit.unit (.inl (c', d)))
  intro r hr
  cases hr with
  | head => exact .inr ⟨(a' ⊓ a' c', b), .head _, glb_greatest _ _ _ (le_of_lt ha) hc', le_refl _⟩
  | tail _ h => nomatch h

/-- Rocq: `NaturalProduct.nmulOrd_increasing2`. -/
theorem nmul_increasing2 {a b b' : Ordinal.{u}} (hb : b < b') (ha : 0 < a) : nmul a b < nmul a b' :=
  lt_of_le_of_lt (nmul_comm a b).le (lt_of_lt_of_le (nmul_increasing1 hb ha) (nmul_comm b' a).le)

/-! ## Zero and one -/

/-- Rocq: `NaturalProduct.nmulOrd_zero`. -/
theorem nmul_zero (a : Ordinal.{u}) : nmul a 0 ≈ 0 :=
  grank_nomoves _ _ fun m =>
    match m with
    | .inl ⟨_, e⟩ => PEmpty.elim e
    | .inr e => PEmpty.elim e

/-- One rectangle of height one behaves exactly like its width, as long as the
fuel is large enough. Rocq: `NaturalProduct.grank_one_upper`. -/
theorem grank_one_upper : ∀ (β x : Ordinal.{u}), grank β [(x, 1)] ≤ x
  | mk F h, x => le_intro fun km => by
    match km with
    | (k, .inl (c, _)) =>
      refine lt_of_le_of_lt (grank_mono (h k) (h k) _ [(x c, 1)] (le_refl _) fun r hr => ?_)
        (lt_of_le_of_lt (grank_one_upper (h k) (x c)) (index_lt x c))
      cases hr with
      | head => exact .inr ⟨(x c, 1), .head _, glb_le2 _ _, le_refl _⟩
      | tail _ h =>
        cases h with
        | head => exact .inl (.inr (glb_le2 _ _))
        | tail _ h => nomatch h
    | (_, .inr e) => exact PEmpty.elim e

/-- Rocq: `NaturalProduct.grank_one_lower`. -/
theorem grank_one_lower : ∀ (β x : Ordinal.{u}), x ≤ β → x ≤ grank β [(x, 1)]
  | mk F h, x, hx => le_intro fun c => by
    obtain ⟨k, hk⟩ := lt_elim (le_elim hx c)
    refine lt_of_le_of_lt (grank_one_lower (h k) (x c) hk) (lt_of_le_of_lt
      (grank_mono (h k) (h k) [(x c, 1)] (cut (mvpt [(x, 1)] (.inl (c, PUnit.unit))) [(x, 1)])
        (le_refl _) fun r hr => ?_)
      (grank_unfold_lt (mk F h) [(x, 1)] k (.inl (c, PUnit.unit))))
    cases hr with
    | head => exact .inr ⟨(x ⊓ x c, 1), .head _,
        glb_greatest _ _ _ (le_of_lt (index_lt x c)) (le_refl _), le_refl _⟩
    | tail _ h => nomatch h

/-- Rocq: `NaturalProduct.gbound_one`. -/
theorem gbound_one : ∀ a : Ordinal.{u}, a ≤ gbound a 1
  | mk A f => le_intro fun c => by
    rw [gbound_unfold]
    exact lt_intro (show (mk ((mk A f).Carrier × (1 : Ordinal.{u}).Carrier) fun ab =>
        gbound ((mk A f) ab.1) 1 ♯ gbound (mk A f) ((1 : Ordinal.{u}) ab.2)).Carrier from (c, PUnit.unit))
      (le_trans (gbound_one (f c)) (nadd_le1 _ _))

/-- Rocq: `NaturalProduct.nmulOrd_one`. -/
theorem nmul_one (a : Ordinal.{u}) : nmul a 1 ≈ a :=
  equiv_intro (grank_one_upper _ a) (grank_one_lower _ a (le_of_lt (succ_trans (gbound_one a))))

/-! ## The successor law, upper half

Consider a rectangle `w × (b+1)` laid over a region `D` that covers `w × b`
and has height at most `b`. Moves in the top row are moves in `w`; moves in
`D` only shrink the top row. Hence the rank is at most `rank D ♯ w`. -/

/-- Rocq: `NaturalProduct.rsub_nil`. -/
theorem rsub_nil (E : Region.{u}) : Rsub [] E := fun _ h => nomatch h

/-- Rocq: `NaturalProduct.rsub_cons`. -/
theorem rsub_cons {r : Ordinal.{u} × Ordinal.{u}} {D E : Region.{u}} (h₁ : Rsub [r] E)
    (h₂ : Rsub D E) : Rsub (r :: D) E := fun r₀ hr₀ => by
  cases hr₀ with
  | head => exact h₁ r (.head _)
  | tail _ h => exact h₂ r₀ h

/-- Rocq: `NaturalProduct.rsub_in`. -/
theorem rsub_in {r s : Ordinal.{u} × Ordinal.{u}} {E : Region.{u}} (hs : s ∈ E) (hrs : Rle r s) :
    Rsub [r] E := fun r₀ hr₀ => by
  cases hr₀ with
  | head => exact .inr ⟨s, hs, hrs⟩
  | tail _ h => nomatch h

/-- Rocq: `NaturalProduct.rsub_cons_r`. -/
theorem rsub_cons_r {s : Ordinal.{u} × Ordinal.{u}} {D E : Region.{u}} (h : Rsub D E) :
    Rsub D (s :: E) := fun r hr =>
  match h r hr with
  | .inl hz => .inl hz
  | .inr ⟨s', hs', hrs⟩ => .inr ⟨s', .tail _ hs', hrs⟩

/-- Rocq: `NaturalProduct.rsub_single_trans`. -/
theorem rsub_single_trans {r s : Ordinal.{u} × Ordinal.{u}} {E : Region.{u}} (h : Rle r s)
    (hs : Rsub [s] E) : Rsub [r] E :=
  rsub_trans (rsub_in (.head _) h) hs

/-- Rocq: `NaturalProduct.cut_sub`. -/
theorem cut_sub (p : Ordinal.{u} × Ordinal.{u}) (D : Region.{u}) : Rsub (cut p D) D := fun _ hr =>
  let ⟨r₁, hr₁, he⟩ := mem_cut hr
  .inr ⟨r₁, hr₁, cut_piece_le _ _ _ (piece_mem he)⟩

/-- Rocq: `NaturalProduct.grank_row_upper`. -/
theorem grank_row_upper : ∀ (β : Ordinal.{u}) (D : Region.{u}) (w b : Ordinal.{u}),
    Rsub [(w, b)] D → (∀ r, r ∈ D → r.2 ≤ b) → grank β ((w, succ b) :: D) ≤ grank β D ♯ w
  | mk F h, D, w, b, hw, hh => le_intro fun km => by
    match km with
    | (k, .inl (c, _)) =>
      -- a move in the top row
      refine lt_of_le_of_lt (grank_mono (h k) (h k) _ ((w c, succ b) :: D) (le_refl _)
        (rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
          (rsub_cons (rsub_cons_r (rsub_single_trans (s := (w, b)) ⟨le_refl _, glb_le2 _ _⟩ hw))
            (rsub_cons_r (cut_sub _ D))))) ?_
      refine lt_of_le_of_lt (grank_row_upper (h k) D (w c) b
        (rsub_single_trans (s := (w, b)) ⟨le_of_lt (index_lt w c), le_refl _⟩ hw) hh) ?_
      exact lt_of_le_of_lt (nadd_le_nadd (grank_mono (h k) (mk F h) D D
          (le_of_lt (index_lt (mk F h) k)) (rsub_refl D)) (le_refl _))
        (nadd_increasing2 _ (index_lt w c))
    | (k, .inr m) =>
      -- a move in `D`
      have hpy : (mvpt D m).2 ≤ b := by
        obtain ⟨r, hr, c, d, hm⟩ := mv_elim D m
        rw [hm]
        exact le_trans (le_of_lt (index_lt r.2 d)) (hh r hr)
      have hcut : Rsub (cut (mvpt D m) [(w, b)]) (cut (mvpt D m) D) :=
        cut_mono ⟨le_refl _, le_refl _⟩ hw
      refine lt_of_le_of_lt (grank_mono (h k) (h k) _ ((w ⊓ (mvpt D m).1, succ b) :: cut (mvpt D m) D)
        (le_refl _) (rsub_cons (rsub_in (.head _) ⟨le_refl _, le_refl _⟩)
          (rsub_cons (rsub_cons_r (rsub_single_trans (s := (w, b ⊓ (mvpt D m).2))
              ⟨le_refl _, glb_greatest _ _ _ (le_trans (glb_le2 _ _) hpy) (glb_le2 _ _)⟩
              (rsub_trans (rsub_in (.tail _ (.head _)) ⟨le_refl _, le_refl _⟩) hcut)))
            (rsub_cons_r (rsub_refl _))))) ?_
      refine lt_of_le_of_lt (grank_row_upper (h k) (cut (mvpt D m) D) (w ⊓ (mvpt D m).1) b
        (rsub_trans (rsub_in (.head _) ⟨le_refl _, le_refl _⟩) hcut)
        (fun r hr => let ⟨r₁, hr₁, he⟩ := mem_cut hr
          le_trans (cut_piece_le _ _ _ (piece_mem he)).2 (hh r₁ hr₁))) ?_
      exact lt_of_le_of_lt (nadd_le_nadd (le_refl _) (glb_le1 _ _))
        (nadd_increasing1 _ (grank_unfold_lt (mk F h) D k m))

/-- Rocq: `NaturalProduct.nmulOrd_succ_upper`. -/
theorem nmul_succ_upper (a b : Ordinal.{u}) : nmul a (succ b) ≤ nmul a b ♯ a :=
  let β := succ (gbound a (succ b) ⊔ gbound a b)
  le_trans (nmul_fuel a (succ b) β (succ_trans (lub_le1 _ _))).le
    (le_trans (grank_mono β β [(a, succ b)] [(a, succ b), (a, b)] (le_refl _)
      (rsub_cons (rsub_in (.head _) ⟨le_refl _, le_refl _⟩) (rsub_nil _)))
      (le_trans (grank_row_upper β [(a, b)] a b (rsub_refl _) fun r hr => by
          cases hr with
          | head => exact le_refl _
          | tail _ h => nomatch h)
        (nadd_le_nadd (nmul_fuel a b β (succ_trans (lub_le2 _ _))).ge (le_refl _))))

/-! ## Fuel-free rank

With the fuel fixed just above `gmeasure D`, `grank` no longer depends on
fuel, and behaves like the true rank of the game. -/

/-- Rocq: `NaturalProduct.rk`. -/
def rk (D : Region.{u}) : Ordinal.{u} := grank (succ (gmeasure D)) D

/-- Rocq: `NaturalProduct.rk_sufficient`. -/
theorem rk_sufficient (D : Region.{u}) : rk D < succ (gmeasure D) :=
  succ_trans (grank_le_measure _ D)

/-- Rocq: `NaturalProduct.grank_le_rk`. -/
theorem grank_le_rk (β : Ordinal.{u}) (D : Region.{u}) : grank β D ≤ rk D :=
  grank_stable β _ D (rk_sufficient D)

/-- Rocq: `NaturalProduct.rk_le_grank`. -/
theorem rk_le_grank (β : Ordinal.{u}) (D : Region.{u}) (h : rk D ≤ β) : rk D ≤ grank β D :=
  grank_value_fuel β _ D h

/-- Rocq: `NaturalProduct.rk_mono`. -/
theorem rk_mono {D E : Region.{u}} (h : Rsub D E) : rk D ≤ rk E :=
  le_trans (grank_mono _ _ D E (le_refl _) h) (grank_le_rk _ E)

/-- Rocq: `NaturalProduct.rk_move_lt`. -/
theorem rk_move_lt (D : Region.{u}) (m : Mv D) : rk (cut (mvpt D m) D) < rk D :=
  lt_of_le_of_lt (rk_le_grank (gmeasure D) _ (le_of_lt (grank_cut_lt_measure _ D m)))
    (grank_unfold_lt (succ (gmeasure D)) D PUnit.unit m)

/-- Rocq: `NaturalProduct.rk_lt_elim`. -/
theorem rk_lt_elim (D : Region.{u}) (i : Ordinal.{u}) (h : i < rk D) :
    ∃ m : Mv D, i ≤ rk (cut (mvpt D m) D) := by
  obtain ⟨km, hm⟩ := lt_elim h
  exact ⟨km.2, le_trans hm (grank_le_rk _ _)⟩

/-- Rocq: `NaturalProduct.nmul_rk`. -/
theorem nmul_rk (a b : Ordinal.{u}) : nmul a b ≈ rk [(a, b)] :=
  nmul_fuel a b _ (succ_trans (nadd_le1 _ _))

/-! ## More region lemmas -/

/-- Rocq: `NaturalProduct.cut_cons`. -/
theorem cut_cons (p r : Ordinal.{u} × Ordinal.{u}) (D : Region.{u}) :
    cut p (r :: D) = (r.1 ⊓ p.1, r.2) :: (r.1, r.2 ⊓ p.2) :: cut p D := rfl

/-- Rocq: `NaturalProduct.cut_cut_sub`. -/
theorem cut_cut_sub (u v t : Ordinal.{u}) (q : Ordinal.{u} × Ordinal.{u}) (D : Region.{u})
    (hut : u ≤ t) (huq : u ≤ q.1) (hvq : v ≤ q.2) : Rsub (cut (u, v) D) (cut q (cut (t, v) D)) :=
  fun _ hr => by
    obtain ⟨r₁, hr₁, he⟩ := mem_cut hr
    rcases he with rfl | rfl
    · exact .inr ⟨((r₁.1 ⊓ t) ⊓ q.1, r₁.2), mem_cut_left (mem_cut_left (p := (t, v)) hr₁),
        glb_greatest _ _ _ (glb_greatest _ _ _ (glb_le1 _ _) (le_trans (glb_le2 _ _) hut))
          (le_trans (glb_le2 _ _) huq), le_refl _⟩
    · exact .inr ⟨(r₁.1, (r₁.2 ⊓ v) ⊓ q.2), mem_cut_right (mem_cut_right (p := (t, v)) hr₁),
        le_refl _, glb_greatest _ _ _ (le_refl _) (le_trans (glb_le2 _ _) hvq)⟩

/-- Rocq: `NaturalProduct.rsub_row_cut`. -/
theorem rsub_row_cut (w b : Ordinal.{u}) (q : Ordinal.{u} × Ordinal.{u}) (D : Region.{u})
    (hwq : w ≤ q.1) (hw : Rsub [(w, b)] D) : Rsub [(w, b)] (cut q D) :=
  rsub_trans (rsub_in (s := (w ⊓ q.1, b)) (.head _) ⟨glb_greatest _ _ _ (le_refl _) hwq, le_refl _⟩)
    (cut_mono ⟨le_refl _, le_refl _⟩ hw)

/-- Rocq: `NaturalProduct.cut_heights`. -/
theorem cut_heights (b : Ordinal.{u}) (q : Ordinal.{u} × Ordinal.{u}) (D : Region.{u})
    (hh : ∀ r, r ∈ D → r.2 ≤ b) : ∀ r, r ∈ cut q D → r.2 ≤ b := fun _ hr =>
  let ⟨r₁, hr₁, he⟩ := mem_cut hr
  le_trans (cut_piece_le _ _ _ (piece_mem he)).2 (hh r₁ hr₁)

/-- Rocq: `NaturalProduct.cut_high`. -/
theorem cut_high (q : Ordinal.{u} × Ordinal.{u}) (D : Region.{u}) (h : ∀ r, r ∈ D → r.2 ≤ q.2) :
    Rsub D (cut q D) := fun r hr =>
  .inr ⟨(r.1, r.2 ⊓ q.2), mem_cut_right hr, le_refl _, glb_greatest _ _ _ (le_refl _) (h r hr)⟩

/-- Rocq: `NaturalProduct.move_height`. -/
theorem move_height (D : Region.{u}) (b : Ordinal.{u}) (m : Mv D) (hh : ∀ r, r ∈ D → r.2 ≤ b) :
    (mvpt D m).2 < b := by
  obtain ⟨r, hr, c, d, hm⟩ := mv_elim D m
  rw [hm]
  exact lt_of_lt_of_le (index_lt r.2 d) (hh r hr)

/-- Rocq: `NaturalProduct.row_move_lower`. -/
theorem row_move_lower (w b : Ordinal.{u}) (D : Region.{u}) (c : w) (hh : ∀ r, r ∈ D → r.2 ≤ b) :
    rk ((w c, succ b) :: D) < rk ((w, succ b) :: D) :=
  lt_of_le_of_lt (rk_mono (E := cut (mvpt ((w, succ b) :: D) (Sum.inl (c, PUnit.unit))) ((w, succ b) :: D))
      (rsub_cons (rsub_in (s := (w ⊓ w c, succ b)) (.head _)
          ⟨glb_greatest _ _ _ (le_of_lt (index_lt w c)) (le_refl _), le_refl _⟩)
        (rsub_cons_r (rsub_cons_r (cut_high (w c, b) D hh)))))
    (rk_move_lt ((w, succ b) :: D) (Sum.inl (c, PUnit.unit)))

/-! ## The chain lemma

Inside the cone above `(px, py)`, play the points `(u, py)` for decreasing `u`
first: this shows that removing that cone costs at least the (ordinal-sum)
length of the chain from `px` to `w`. -/

/-- Rocq: `NaturalProduct.rk_chain`. -/
theorem rk_chain (w b : Ordinal.{u}) (D : Region.{u}) (px py : Ordinal.{u})
    (hw : Rsub [(w, b)] D) (hpy : py < b) :
    ∀ e t : Ordinal.{u}, px + e ≤ t → t ≤ w → rk (cut (px, py) D) + e ≤ rk (cut (t, py) D)
  | mk E f, t, ht, htw => by
    rw [add_unfold]
    refine lub_least (rk_mono (cut_mono ⟨le_trans (le_add_right _ _) ht, le_refl _⟩ (rsub_refl D)))
      (sup_least fun i => succ_least ?_)
    have hut : px + f i < t := lt_of_lt_of_le (add_lt_add_left px (index_lt (mk E f) i)) ht
    match hw (w, b) (.head _) with
    | .inl (.inl hz) => exact (zero_lt _ (lt_of_lt_of_le hut (le_trans htw hz))).elim
    | .inl (.inr hz) => exact (zero_lt _ (lt_of_lt_of_le hpy hz)).elim
    | .inr ⟨s, hs, hs₁, hs₂⟩ =>
      have hux : px + f i < s.1 ⊓ t := lt_of_lt_of_le (succ_lt _)
        (glb_greatest _ _ _ (succ_least (lt_of_lt_of_le hut (le_trans htw hs₁))) (succ_least hut))
      obtain ⟨c, hc⟩ := lt_elim hux
      obtain ⟨d, hd⟩ := lt_elim (lt_of_lt_of_le hpy hs₂)
      obtain ⟨m, hm⟩ := mv_intro _ _ (mem_cut_left (p := (t, py)) hs) c d
      refine lt_of_le_of_lt (rk_chain w b D px py hw hpy (f i) (px + f i) (le_refl _)
        (le_of_lt (lt_of_lt_of_le hut htw))) (lt_of_le_of_lt (rk_mono ?_) (rk_move_lt _ m))
      rw [hm]
      exact cut_cut_sub _ _ _ _ D (le_of_lt hut) hc hd

/-! ## The successor law, lower half (classical)

The one arithmetic fact needed is stated separately: if `x` exceeds `x''` by
at least the chain `y ↦ w` (in the sense of ordinal sum), then `x'' ♯ w` is
already reached by `x ♯ w'` for some `w' < w`. For successor `w` this is
trivial; for limit `w` it is an absorption property of Cantor normal forms. -/

/-- Rocq: `NaturalProduct.absorb_prop`. -/
def AbsorbProp : Prop :=
  ∀ w y x x'' : Ordinal.{u}, y < w → x'' < x → (∀ e, y + e ≤ w → x'' + e ≤ x) →
    ∃ w', w' < w ∧ x'' ♯ w ≤ x ♯ w'

/-- Rocq: `NaturalProduct.rk_row_lower`. -/
theorem rk_row_lower (em : ExcludedMiddle) (abs : AbsorbProp.{u}) (w : Ordinal.{u}) :
    ∀ (D : Region.{u}) (b : Ordinal.{u}), Rsub [(w, b)] D → (∀ r, r ∈ D → r.2 ≤ b) →
      rk D ♯ w ≤ rk ((w, succ b) :: D) := by
  induction w using ltRec with
  | ind w ihw =>
    suffices H : ∀ (o : Ordinal.{u}) (D : Region.{u}) (b : Ordinal.{u}), rk D ≤ o →
        Rsub [(w, b)] D → (∀ r, r ∈ D → r.2 ≤ b) → rk D ♯ w ≤ rk ((w, succ b) :: D) from
      fun D b hw hh => H (rk D) D b (le_refl _) hw hh
    intro o
    induction o using ltRec with
    | ind o iho =>
      intro D b ho hw hh
      have htop : ∀ c : w, rk D ♯ w c < rk ((w, succ b) :: D) := fun c =>
        lt_of_le_of_lt (ihw (w c) (index_lt w c) D b
          (rsub_single_trans (s := (w, b)) ⟨le_of_lt (index_lt w c), le_refl _⟩ hw) hh)
          (row_move_lower w b D c hh)
      refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
      · obtain ⟨m, hm⟩ := rk_lt_elim D i hi
        have hqy := move_height D b m hh
        match order_total em w (mvpt D m).1 with
        | .inl hwq =>
          -- a move at `q` does not disturb the top row
          refine lt_of_le_of_lt (nadd_le_nadd hm (le_refl _)) (lt_of_le_of_lt
            (iho (rk (cut (mvpt D m) D)) (lt_of_lt_of_le (rk_move_lt D m) ho) (cut (mvpt D m) D) b
              (le_refl _) (rsub_row_cut w b _ D hwq hw) (cut_heights b _ D hh)) ?_)
          exact lt_of_le_of_lt (rk_mono (E := cut (mvpt ((w, succ b) :: D) (Sum.inr m)) ((w, succ b) :: D))
              (rsub_cons (rsub_in (s := (w ⊓ (mvpt D m).1, succ b)) (.head _)
                ⟨glb_greatest _ _ _ (le_refl _) hwq, le_refl _⟩) (rsub_cons_r (rsub_cons_r (rsub_refl _)))))
            (rk_move_lt ((w, succ b) :: D) (Sum.inr m))
        | .inr hqw =>
          -- `q` lies under the top row: answer with a top-row move
          have hchain : ∀ e, (mvpt D m).1 + e ≤ w → rk (cut (mvpt D m) D) + e ≤ rk D := fun e he =>
            le_trans (rk_chain w b D (mvpt D m).1 (mvpt D m).2 hw hqy e w he (le_refl w))
              (rk_mono (cut_sub _ D))
          obtain ⟨w', hw', habs⟩ := abs w (mvpt D m).1 (rk D) (rk (cut (mvpt D m) D)) hqw
            (rk_move_lt D m) hchain
          obtain ⟨c, hc⟩ := lt_elim hw'
          exact lt_of_le_of_lt (le_trans (nadd_le_nadd hm (le_refl _))
            (le_trans habs (nadd_le_nadd (le_refl _) hc))) (htop c)
      · obtain ⟨c, hc⟩ := lt_elim hj
        exact lt_of_le_of_lt (nadd_le_nadd (le_refl _) hc) (htop c)

/-- Rocq: `NaturalProduct.nmulOrd_succ_lower`. -/
theorem nmul_succ_lower (em : ExcludedMiddle) (abs : AbsorbProp.{u}) (a b : Ordinal.{u}) :
    nmul a b ♯ a ≤ nmul a (succ b) :=
  le_trans (nadd_le_nadd (nmul_rk a b).le (le_refl a))
    (le_trans (rk_row_lower em abs a [(a, b)] b (rsub_refl _) fun r hr => by
        cases hr with
        | head => exact le_refl _
        | tail _ h => nomatch h)
      (le_trans (rk_mono (rsub_cons (rsub_in (s := (a, succ b)) (.head _) ⟨le_refl _, le_refl _⟩)
          (rsub_in (s := (a, succ b)) (.head _) ⟨le_refl _, le_of_lt (succ_lt b)⟩)))
        (nmul_rk a (succ b)).ge))

/-- Rocq: `NaturalProduct.nmulOrd_succ`. -/
theorem nmul_succ (em : ExcludedMiddle) (abs : AbsorbProp.{u}) (a b : Ordinal.{u}) :
    nmul a (succ b) ≈ nmul a b ♯ a :=
  equiv_intro (nmul_succ_upper a b) (nmul_succ_lower em abs a b)

/-! ## The absorption fact (classical, via Cantor normal forms)

Let `ω^δ` be the last Cantor term of `w`, so `w = w0 + ω^δ` with every exponent
of `w0` at least `δ`. Split `x'' = H + L` with every exponent of `H` at least
`δ` and `L < ω^δ`. Then `w' := w0 + L` works. -/

section absorb

variable (em : ExcludedMiddle)
include em

/-- Rocq: `NaturalProduct.cpl` (a section `Let`). -/
private theorem cpl (x : Ordinal.{u}) : Complete x := ord_complete em x

/-- Rocq: `NaturalProduct.each_complete`. -/
theorem each_complete : ∀ xs : List Ordinal.{u}, Each Complete xs
  | [] => trivial
  | x :: xs => ⟨cpl em x, each_complete xs⟩

/-- Rocq: `NaturalProduct.omega_exp_closed`. -/
theorem omega_exp_closed (δ : Ordinal.{u}) : AdditivelyClosed (ω ^ δ) :=
  powOmega_additively_closed (cpl em δ)

/-- Anything below `w0 + ω^δ` is absorbed by adding `ω^δ`.
Rocq: `NaturalProduct.below_add_last`. -/
theorem below_add_last (δ : Ordinal.{u}) : ∀ pre : List Ordinal.{u}, (∀ a, a ∈ pre → δ ≤ a) →
    ∀ z, z < cantorDenote pre + ω ^ δ → z + ω ^ δ ≤ cantorDenote pre + ω ^ δ
  | [], _, z, hz =>
    le_trans (additively_closed_collapse (omega_exp_closed em δ) (lt_of_lt_of_le hz (zero_add _).le))
      (zero_add _).ge
  | a :: pre, hpre, z, hz => by
    have hz' : z < ω ^ a + (cantorDenote pre + ω ^ δ) := lt_of_lt_of_le hz (add_assoc _ _ _).ge
    refine le_trans ?_ (add_assoc _ _ _).le
    match add_lt hz' with
    | .inl hza =>
      refine le_trans ?_ (le_add_right _ _)
      match order_total em a δ with
      | .inl had =>
        exact le_trans (additively_closed_collapse (omega_exp_closed em δ)
            (lt_of_lt_of_le hza (pow_le_pow_right ω had)))
          (pow_le_pow_right ω (hpre a (.head _)))
      | .inr hda => exact le_of_lt (omega_exp_closed em a z _ hza (pow_lt_pow_right omega_gt1 hda))
    | .inr ⟨i, hi⟩ =>
      exact le_trans (add_le_add hi (le_refl _)) (le_trans (add_assoc _ _ _).ge
        (add_le_add (le_refl _) (below_add_last δ pre (fun b hb => hpre b (.tail _ hb)) _ (index_lt _ i))))

/-- Rocq: `NaturalProduct.cantor_split`. -/
theorem cantor_split (δ : Ordinal.{u}) : ∀ (ls : List Ordinal.{u}) (x : Ordinal.{u}),
    CantorSequence x ls → ∃ pre suf, ls = pre ++ suf ∧
      (∀ a, a ∈ pre → δ ≤ a) ∧ (∀ a, a ∈ suf → a < δ)
  | [], _, _ => ⟨[], [], rfl, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | a :: ls, _, ⟨_, hls⟩ => by
    match order_total em δ a with
    | .inl hda =>
      obtain ⟨pre, suf, heq, hpre, hsuf⟩ := cantor_split δ ls a hls
      refine ⟨a :: pre, suf, congrArg (a :: ·) heq, fun b hb => ?_, hsuf⟩
      cases hb with
      | head => exact hda
      | tail _ h => exact hpre b h
    | .inr had =>
      refine ⟨[], a :: ls, rfl, (fun _ h => nomatch h), fun b hb => ?_⟩
      cases hb with
      | head => exact had
      | tail _ h => exact lt_of_le_of_lt (cantor_sequence_le1 ls a hls b h) had

/-- Rocq: `NaturalProduct.cantor_below`. -/
theorem cantor_below (δ : Ordinal.{u}) : ∀ suf : List Ordinal.{u}, (∀ a, a ∈ suf → a < δ) →
    cantorDenote suf < ω ^ δ
  | [], _ => pow_pos ω δ
  | a :: suf, h => omega_exp_closed em δ _ _ (pow_lt_pow_right omega_gt1 (h a (.head _)))
      (cantor_below δ suf fun b hb => h b (.tail _ hb))

/-- Rocq: `NaturalProduct.decompose_at`. -/
theorem decompose_at (δ x : Ordinal.{u}) : ∃ H L, x ≈ H + L ∧ L < ω ^ δ ∧
    ∀ q, q ≤ ω ^ δ → H ♯ q ≤ H + q := by
  obtain ⟨ls, hls, hx⟩ := cantor_decomposition em x
  obtain ⟨pre, suf, rfl, hpre, hsuf⟩ := cantor_split em δ ls x hls
  exact ⟨cantorDenote pre, cantorDenote suf, equiv_trans (equiv_symm hx) (cantor_denote_app pre suf),
    cantor_below em δ suf hsuf, fun q hq => cantor_denote_nadd_add em pre δ (each_complete em pre) hpre q hq⟩

/-- Rocq: `NaturalProduct.last_term`. -/
theorem last_term (w : Ordinal.{u}) (hw : 0 < w) :
    ∃ pre δ, w ≈ cantorDenote pre + ω ^ δ ∧ ∀ a, a ∈ pre → δ ≤ a := by
  obtain ⟨ls, hls, hx⟩ := cantor_decomposition em w
  induction ls using List.rev_ind with
  | hnil => exact (lt_irrefl 0 (lt_of_lt_of_le hw hx.ge)).elim
  | hsnoc δ pre _ =>
    exact ⟨pre, δ, equiv_trans (equiv_symm hx) (equiv_trans (cantor_denote_app pre [δ])
        (add_congr (equiv_refl _) (add_zero _))),
      fun b hb => cantor_sequence_le pre w [δ] hls b δ hb (.head _)⟩

end absorb

/-- Rocq: `NaturalProduct.nadd_swap4`. -/
theorem nadd_swap4 (a b c d : Ordinal.{u}) : (a ♯ b) ♯ (c ♯ d) ≈ (a ♯ d) ♯ (c ♯ b) :=
  equiv_trans (equiv_symm (nadd_assoc _ _ _)) (equiv_trans
    (nadd_congr (equiv_refl a) (equiv_trans (nadd_assoc b c d) (equiv_trans (nadd_comm _ _)
      (nadd_congr (equiv_refl d) (nadd_comm b c))))) (nadd_assoc _ _ _))

/-- Rocq: `NaturalProduct.absorb`. -/
theorem absorb (em : ExcludedMiddle) : AbsorbProp.{u} := by
  intro w y x x'' hyw _ hchain
  obtain ⟨pre, δ, hw, hpre⟩ := last_term em w (lt_of_le_of_lt (zero_least y) hyw)
  obtain ⟨H, L, hx'', hL, hD⟩ := decompose_at em δ x''
  have hDw0 : ∀ q, q ≤ ω ^ δ → cantorDenote pre ♯ q ≤ cantorDenote pre + q := fun q hq =>
    cantor_denote_nadd_add em pre δ (each_complete em pre) hpre q hq
  have hA1 : y + ω ^ δ ≤ w :=
    le_trans (below_add_last em δ pre hpre y (lt_of_lt_of_le hyw hw.le)) hw.ge
  have hxx : H + ω ^ δ ≤ x :=
    le_trans (add_le_add (le_trans (le_add_right H L) hx''.ge) (le_refl _)) (hchain _ hA1)
  refine ⟨cantorDenote pre + L, lt_of_lt_of_le (add_lt_add_left _ hL) hw.ge, ?_⟩
  exact le_trans (nadd_le_nadd (le_trans hx''.le (add_nadd_le H L))
      (le_trans hw.le (add_nadd_le _ _)))
    (le_trans (nadd_swap4 _ _ _ _).le (le_trans (nadd_le_nadd (hD _ (le_refl _)) (hDw0 L (le_of_lt hL)))
      (nadd_le_nadd hxx (le_refl _))))

/-- Classically, `a ⊗ (b + 1) ≈ a ⊗ b ♯ a`.
Rocq: `NaturalProduct.nmulOrd_succ_classical`. -/
theorem nmul_succ_classical (em : ExcludedMiddle) (a b : Ordinal.{u}) :
    nmul a (succ b) ≈ nmul a b ♯ a :=
  nmul_succ em (absorb em) a b

/-! # Distributivity -/

/-! ## Region sums

`rsum R1 R2` stacks the height profiles of `R1` and `R2` column by column,
using natural sum. The game on `a × (b ♯ c)` is the game on
`rsum [(a,b)] [(a,c)]`, and a move at height `b' ♯ c` corresponds to a move at
height `b'` in the first component.

Only the lower bound `rk R1 ♯ rk R2 ≤ rk (rsum R1 R2)` holds in general. For
`R1 = 1 × ω` and `R2 = ω × 1` (each padded with a zero-height rectangle of
width `ω`), `rsum` is a column of height `ω+1` over a row of length `ω`, of rank
`ω·2+1 > ω ♯ ω`. This region does arise in the `ω × (ω+1)` game, after the move
`(1,1)`. -/

/-- Rocq: `NaturalProduct.rsum` (a `flat_map`; here the same list by recursion). -/
def rsum : Region.{u} → Region.{u} → Region.{u}
  | [], _ => []
  | r₁ :: R₁, R₂ => R₂.map (fun r₂ => (r₁.1 ⊓ r₂.1, r₁.2 ♯ r₂.2)) ++ rsum R₁ R₂

/-- Rocq: `NaturalProduct.in_rsum`. -/
theorem in_rsum (r : Ordinal.{u} × Ordinal.{u}) : ∀ R₁ R₂ : Region.{u}, r ∈ rsum R₁ R₂ ↔
    ∃ r₁ r₂, r₁ ∈ R₁ ∧ r₂ ∈ R₂ ∧ r = (r₁.1 ⊓ r₂.1, r₁.2 ♯ r₂.2)
  | [], _ => ⟨(fun h => nomatch h), fun ⟨_, _, h, _⟩ => nomatch h⟩
  | r₁ :: R₁, R₂ => by
    refine ⟨fun h => ?_, fun ⟨a, b, ha, hb, he⟩ => ?_⟩
    · rcases mem_append_cases h with h | h
      · obtain ⟨r₂, hr₂, he⟩ := exists_of_mem_map h
        exact ⟨r₁, r₂, .head _, hr₂, he.symm⟩
      · obtain ⟨a, b, ha, hb, he⟩ := (in_rsum r R₁ R₂).1 h
        exact ⟨a, b, .tail _ ha, hb, he⟩
    · cases ha with
      | head => rw [he]; exact List.mem_append_left _ (mem_map_of_mem _ hb)
      | tail _ ha => exact List.mem_append_right _ ((in_rsum r R₁ R₂).2 ⟨a, b, ha, hb, he⟩)

/-- Rocq: `NaturalProduct.rsum_comm`. -/
theorem rsum_comm (R₁ R₂ : Region.{u}) : Rsub (rsum R₁ R₂) (rsum R₂ R₁) := fun r hr =>
  let ⟨r₁, r₂, h₁, h₂, he⟩ := (in_rsum r R₁ R₂).1 hr
  .inr ⟨(r₂.1 ⊓ r₁.1, r₂.2 ♯ r₁.2), (in_rsum _ R₂ R₁).2 ⟨r₂, r₁, h₂, h₁, rfl⟩, by
    rw [he]; exact ⟨glb_greatest _ _ _ (glb_le2 _ _) (glb_le1 _ _), (nadd_comm _ _).le⟩⟩

/-- Every column below `W` is covered, and nothing is wider than `W`.
Rocq: `NaturalProduct.wide`. -/
def Wide (W : Ordinal.{u}) (R : Region.{u}) : Prop :=
  (∃ s, s ∈ R ∧ W ≤ s.1) ∧ ∀ r, r ∈ R → r.1 ≤ W

/-- Rocq: `NaturalProduct.wide_cut`. -/
theorem wide_cut (W : Ordinal.{u}) (q : Ordinal.{u} × Ordinal.{u}) (R : Region.{u}) (h : Wide W R) :
    Wide W (cut q R) :=
  ⟨let ⟨s, hs, hWs⟩ := h.1; ⟨(s.1, s.2 ⊓ q.2), mem_cut_right hs, hWs⟩,
   fun _ hr => let ⟨r₁, hr₁, he⟩ := mem_cut hr
     le_trans (cut_piece_le _ _ _ (piece_mem he)).1 (h.2 r₁ hr₁)⟩

/-- Rocq: `NaturalProduct.list_max`. -/
theorem list_max (em : ExcludedMiddle) (P : Ordinal.{u} × Ordinal.{u} → Prop) :
    ∀ l : Region.{u}, (∃ s, s ∈ l ∧ P s) →
      ∃ s, s ∈ l ∧ P s ∧ ∀ s', s' ∈ l → P s' → s'.2 ≤ s.2
  | [], ⟨_, h, _⟩ => nomatch h
  | a :: l, hex => by
    match em (∃ s, s ∈ l ∧ P s) with
    | .inl hl =>
      obtain ⟨s, hs, hps, hmax⟩ := list_max em P l hl
      match em (P a) with
      | .inl hpa =>
        match order_total em a.2 s.2 with
        | .inl has =>
          refine ⟨s, .tail _ hs, hps, fun s' hs' hps' => ?_⟩
          cases hs' with
          | head => exact has
          | tail _ h => exact hmax s' h hps'
        | .inr hsa =>
          refine ⟨a, .head _, hpa, fun s' hs' hps' => ?_⟩
          cases hs' with
          | head => exact le_refl _
          | tail _ h => exact le_of_lt (lt_of_le_of_lt (hmax s' h hps') hsa)
      | .inr hpa =>
        refine ⟨s, .tail _ hs, hps, fun s' hs' hps' => ?_⟩
        cases hs' with
        | head => exact (hpa hps').elim
        | tail _ h => exact hmax s' h hps'
    | .inr hl =>
      obtain ⟨s, hs, hps⟩ := hex
      cases hs with
      | head =>
        refine ⟨a, .head _, hps, fun s' hs' hps' => ?_⟩
        cases hs' with
        | head => exact le_refl _
        | tail _ h => exact (hl ⟨s', h, hps'⟩).elim
      | tail _ h => exact (hl ⟨s, h, hps⟩).elim

/-! ## Superdistributivity (classical) -/

/-- Answer a move `q` in the first component by the point `(qx, qy ♯ Y2)`,
where `Y2` is the tallest rectangle of the second component covering column
`qx`. Rocq: `NaturalProduct.rsum_step`. -/
theorem rsum_step (em : ExcludedMiddle) (W : Ordinal.{u}) (R₁ R₂ : Region.{u}) (m : Mv R₁)
    (hw₁ : Wide W R₁) (hw₂ : Wide W R₂)
    (ih : rk (cut (mvpt R₁ m) R₁) ♯ rk R₂ ≤ rk (rsum (cut (mvpt R₁ m) R₁) R₂)) :
    rk (cut (mvpt R₁ m) R₁) ♯ rk R₂ < rk (rsum R₁ R₂) := by
  obtain ⟨r₁, hr₁, c, d, hm⟩ := mv_elim R₁ m
  have hq₁ : (mvpt R₁ m).1 < r₁.1 := by rw [hm]; exact index_lt r₁.1 c
  have hq₂ : (mvpt R₁ m).2 < r₁.2 := by rw [hm]; exact index_lt r₁.2 d
  have hcov : ∃ s, s ∈ R₂ ∧ (mvpt R₁ m).1 < s.1 :=
    let ⟨⟨s, hs, hWs⟩, _⟩ := hw₂
    ⟨s, hs, lt_of_lt_of_le hq₁ (le_trans (hw₁.2 r₁ hr₁) hWs)⟩
  obtain ⟨s₂, hs₂, hqs₂, hmax⟩ := list_max em (fun s => (mvpt R₁ m).1 < s.1) R₂ hcov
  -- the answering point
  obtain ⟨cg, hcg⟩ := lt_elim (show (mvpt R₁ m).1 < r₁.1 ⊓ s₂.1 from
    lt_of_lt_of_le (succ_lt _) (glb_greatest _ _ _ (succ_least hq₁) (succ_least hqs₂)))
  obtain ⟨dg, hdg⟩ := lt_elim (nadd_increasing1 s₂.2 hq₂)
  obtain ⟨m', hm'⟩ := mv_intro _ _ ((in_rsum _ R₁ R₂).2 ⟨r₁, s₂, hr₁, hs₂, rfl⟩) cg dg
  have hqp : (mvpt R₁ m).1 ≤ (mvpt (rsum R₁ R₂) m').1 := by rw [hm']; exact hcg
  have hqp₂ : (mvpt R₁ m).2 ♯ s₂.2 ≤ (mvpt (rsum R₁ R₂) m').2 := by rw [hm']; exact hdg
  refine lt_of_le_of_lt ih (lt_of_le_of_lt (rk_mono fun r hr => ?_) (rk_move_lt _ m'))
  obtain ⟨r₁', r₂, h₁, h₂, rfl⟩ := (in_rsum _ _ _).1 hr
  obtain ⟨r₀, hr₀, hpiece⟩ := mem_cut h₁
  have hsrc : (r₀.1 ⊓ r₂.1, r₀.2 ♯ r₂.2) ∈ rsum R₁ R₂ := (in_rsum _ _ _).2 ⟨r₀, r₂, hr₀, h₂, rfl⟩
  rcases hpiece with rfl | rfl
  · -- left piece
    exact .inr ⟨((r₀.1 ⊓ r₂.1) ⊓ (mvpt (rsum R₁ R₂) m').1, r₀.2 ♯ r₂.2), mem_cut_left hsrc,
      glb_greatest _ _ _ (glb_greatest _ _ _ (le_trans (glb_le1 _ _) (glb_le1 _ _)) (glb_le2 _ _))
        (le_trans (glb_le1 _ _) (le_trans (glb_le2 _ _) hqp)), le_refl _⟩
  · -- lower piece
    match order_total em r₂.1 (mvpt R₁ m).1 with
    | .inl hr₂q =>
      exact .inr ⟨((r₀.1 ⊓ r₂.1) ⊓ (mvpt (rsum R₁ R₂) m').1, r₀.2 ♯ r₂.2), mem_cut_left hsrc,
        glb_greatest _ _ _ (le_refl _) (le_trans (glb_le2 _ _) (le_trans hr₂q hqp)),
        nadd_le_nadd (glb_le1 _ _) (le_refl _)⟩
    | .inr hqr₂ =>
      exact .inr ⟨(r₀.1 ⊓ r₂.1, (r₀.2 ♯ r₂.2) ⊓ (mvpt (rsum R₁ R₂) m').2), mem_cut_right hsrc,
        le_refl _, glb_greatest _ _ _ (nadd_le_nadd (glb_le1 _ _) (le_refl _))
          (le_trans (nadd_le_nadd (glb_le2 _ _) (hmax r₂ h₂ hqr₂)) hqp₂)⟩

/-- Rocq: `NaturalProduct.rsum_lower`. -/
theorem rsum_lower (em : ExcludedMiddle) (W : Ordinal.{u}) (R₁ R₂ : Region.{u})
    (hw₁ : Wide W R₁) (hw₂ : Wide W R₂) : rk R₁ ♯ rk R₂ ≤ rk (rsum R₁ R₂) := by
  suffices H : ∀ (o : Ordinal.{u}) (R₁ R₂ : Region.{u}), rk R₁ ♯ rk R₂ ≤ o → Wide W R₁ → Wide W R₂ →
      rk R₁ ♯ rk R₂ ≤ rk (rsum R₁ R₂) from H _ R₁ R₂ (le_refl _) hw₁ hw₂
  intro o
  induction o using ltRec with
  | ind o iho =>
    intro R₁ R₂ ho hw₁ hw₂
    refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
    · obtain ⟨m, hm⟩ := rk_lt_elim R₁ i hi
      exact lt_of_le_of_lt (nadd_le_nadd hm (le_refl _)) (rsum_step em W R₁ R₂ m hw₁ hw₂
        (iho _ (lt_of_lt_of_le (nadd_increasing1 _ (rk_move_lt R₁ m)) ho) _ _ (le_refl _)
          (wide_cut _ _ _ hw₁) hw₂))
    · obtain ⟨m, hm⟩ := rk_lt_elim R₂ j hj
      have ih' : rk (cut (mvpt R₂ m) R₂) ♯ rk R₁ ≤ rk (rsum (cut (mvpt R₂ m) R₂) R₁) :=
        le_trans (nadd_comm _ _).le (le_trans (iho _ (lt_of_lt_of_le (nadd_increasing2 _ (rk_move_lt R₂ m)) ho)
          R₁ _ (le_refl _) hw₁ (wide_cut _ _ _ hw₂)) (rk_mono (rsum_comm _ _)))
      exact lt_of_le_of_lt (le_trans (nadd_le_nadd (le_refl _) hm) (nadd_comm _ _).le)
        (lt_of_lt_of_le (rsum_step em W R₂ R₁ m hw₂ hw₁ ih') (rk_mono (rsum_comm R₂ R₁)))

private theorem pad_bound (a y : Ordinal.{u}) :
    ∀ r, r ∈ [(a, y), (a, 0)] → r.1 ≤ a ∧ r.2 ≤ y := fun r hr => by
  cases hr with
  | head => exact ⟨le_refl _, le_refl _⟩
  | tail _ h =>
    cases h with
    | head => exact ⟨le_refl _, zero_least _⟩
    | tail _ h => nomatch h

/-- Classical superdistributivity. Rocq: `NaturalProduct.nmulOrd_distrib_lower`. -/
theorem nmul_distrib_lower (em : ExcludedMiddle) (a b c : Ordinal.{u}) :
    nmul a b ♯ nmul a c ≤ nmul a (b ♯ c) := by
  have hW : ∀ y, Wide a [(a, y), (a, 0)] := fun y =>
    ⟨⟨(a, y), .head _, le_refl _⟩, fun r hr => (pad_bound a y r hr).1⟩
  refine le_trans (nadd_le_nadd (nmul_rk a b).le (nmul_rk a c).le) (le_trans (nadd_le_nadd
    (rk_mono (rsub_in (s := (a, b)) (E := [(a, b), (a, 0)]) (.head _) ⟨le_refl _, le_refl _⟩))
    (rk_mono (rsub_in (s := (a, c)) (E := [(a, c), (a, 0)]) (.head _) ⟨le_refl _, le_refl _⟩)))
    (le_trans (rsum_lower em a _ _ (hW b) (hW c)) (le_trans (rk_mono ?_) (nmul_rk a (b ♯ c)).ge)))
  intro r hr
  obtain ⟨r₁, r₂, h₁, h₂, rfl⟩ := (in_rsum _ _ _).1 hr
  exact .inr ⟨(a, b ♯ c), .head _, le_trans (glb_le1 _ _) (pad_bound a b r₁ h₁).1,
    nadd_le_nadd (pad_bound a b r₁ h₁).2 (pad_bound a c r₂ h₂).2⟩

/-! ## Splitting the chain `b ♯ c` (classical)

Interleaving the Cantor normal forms of `b` and `c` writes `b ♯ c` as an
ordinal sum of blocks `ω^z`, each tagged with the side it came from. Every
`v < b ♯ c` then gets a side and a position on that side; positions are
strictly increasing within each side and bounded by `b` (resp. `c`). This is
the order-preserving bijection `b ⊔ c → b ♯ c`, presented as a relation. -/

/-- Rocq: `NaturalProduct.left_subtract`. -/
theorem left_subtract (em : ExcludedMiddle) {x v : Ordinal.{u}} (h : x ≤ v) : ∃ e, v ≈ x + e := by
  obtain ⟨e, he, hleast⟩ := ord_well_ordered em (fun e => v ≤ x + e) v (le_add_left x v)
  refine ⟨e, equiv_intro he ?_⟩
  match order_total em (x + e) v with
  | .inl h' => exact h'
  | .inr hlt =>
    match add_lt hlt with
    | .inl h₁ => exact (lt_irrefl x (lt_of_le_of_lt h h₁)).elim
    | .inr ⟨i, hi⟩ => exact (lt_irrefl (e i) (lt_of_lt_of_le (index_lt e i) (hleast (e i) hi))).elim

/-- Rocq: `NaturalProduct.add_cancel_lt`. -/
theorem add_cancel_lt (em : ExcludedMiddle) {x y z : Ordinal.{u}} (h : x + y < x + z) : y < z :=
  match order_total em z y with
  | .inl hzy => (lt_irrefl _ (lt_of_lt_of_le h (add_le_add (le_refl x) hzy))).elim
  | .inr hyz => hyz

/-- Rocq: `NaturalProduct.tden`. -/
def tden (tl : List (Bool × Ordinal.{u})) : Ordinal.{u} := cantorDenote (tl.map Prod.snd)

/-- Rocq: `NaturalProduct.sden`. -/
def sden (s : Bool) (tl : List (Bool × Ordinal.{u})) : Ordinal.{u} :=
  cantorDenote ((tl.filter fun e => e.1 == s).map Prod.snd)

/-- Rocq: `NaturalProduct.splitR`. -/
def SplitR : List (Bool × Ordinal.{u}) → Ordinal.{u} → Bool → Ordinal.{u} → Prop
  | [], _, _, _ => False
  | (t, z) :: tl', v, s, p =>
    (v < ω ^ z ∧ s = t ∧ p ≈ v) ∨
    (ω ^ z ≤ v ∧ ∃ v' p', v ≈ ω ^ z + v' ∧ SplitR tl' v' s p' ∧
      p ≈ cond (s == t) (ω ^ z + p') p')

/-- Rocq: `NaturalProduct.splitR_total`. -/
theorem splitR_total (em : ExcludedMiddle) :
    ∀ (tl : List (Bool × Ordinal.{u})) (v : Ordinal.{u}), v < tden tl → ∃ s p, SplitR tl v s p
  | [], v, hv => (zero_lt v hv).elim
  | (t, z) :: tl, v, hv =>
    match order_total em (ω ^ z) v with
    | .inl hzv =>
      let ⟨v', hv'⟩ := left_subtract em hzv
      let ⟨s, p', hsp⟩ := splitR_total em tl v' (add_cancel_lt em (lt_of_le_of_lt hv'.ge hv))
      ⟨s, cond (s == t) (ω ^ z + p') p', .inr ⟨hzv, v', p', hv', hsp, equiv_refl _⟩⟩
    | .inr hvz => ⟨t, v, .inl ⟨hvz, rfl, equiv_refl _⟩⟩

/-- Rocq: `NaturalProduct.splitR_bound`. -/
theorem splitR_bound : ∀ (tl : List (Bool × Ordinal.{u})) (v : Ordinal.{u}) (s : Bool) (p : Ordinal.{u}),
    SplitR tl v s p → p < sden s tl
  | [], _, _, _, h => h.elim
  | (t, z) :: tl, v, s, p, .inl ⟨hv, hs, hp⟩ => by
    subst hs
    cases s
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le hv (le_add_right _ _))
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le hv (le_add_right _ _))
  | (t, z) :: tl, _, s, p, .inr ⟨_, v', p', _, hsp, hp⟩ => by
    have hb := splitR_bound tl v' s p' hsp
    cases t <;> cases s
    · exact lt_of_le_of_lt hp.le (add_lt_add_left _ hb)
    · exact lt_of_le_of_lt hp.le hb
    · exact lt_of_le_of_lt hp.le hb
    · exact lt_of_le_of_lt hp.le (add_lt_add_left _ hb)

/-- Rocq: `NaturalProduct.splitR_mono`. -/
theorem splitR_mono (em : ExcludedMiddle) :
    ∀ (tl : List (Bool × Ordinal.{u})) (v w : Ordinal.{u}) (s : Bool) (p q : Ordinal.{u}),
      SplitR tl v s p → SplitR tl w s q → v < w → p < q
  | [], _, _, _, _, _, h, _, _ => h.elim
  | (_, _) :: _, _, _, _, _, _, .inl ⟨_, _, hp⟩, .inl ⟨_, _, hq⟩, hvw =>
    lt_of_le_of_lt hp.le (lt_of_lt_of_le hvw hq.ge)
  | (t, z) :: _, _, _, s, _, _, .inl ⟨hvz, hs, hp⟩, .inr ⟨_, _, _, _, _, hq⟩, _ => by
    subst hs
    cases s
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le hvz (le_trans (le_add_right _ _) hq.ge))
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le hvz (le_trans (le_add_right _ _) hq.ge))
  | (_, _) :: _, v, _, _, _, _, .inr ⟨hzv, _⟩, .inl ⟨hwz, _⟩, hvw =>
    (lt_irrefl v (lt_of_lt_of_le (lt_trans hvw hwz) hzv)).elim
  | (t, z) :: tl, _, _, s, _, _, .inr ⟨_, v', p', hv', hsp, hp⟩, .inr ⟨_, w', q', hw', hsq, hq⟩, hvw => by
    have hpq := splitR_mono em tl v' w' s p' q' hsp hsq
      (add_cancel_lt em (lt_of_le_of_lt hv'.ge (lt_of_lt_of_le hvw hw'.le)))
    cases t <;> cases s
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le (add_lt_add_left _ hpq) hq.ge)
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le hpq hq.ge)
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le hpq hq.ge)
    · exact lt_of_le_of_lt hp.le (lt_of_lt_of_le (add_lt_add_left _ hpq) hq.ge)

/-- Rocq: `NaturalProduct.merge_tags`. -/
theorem merge_tags {xs ys zs : List Ordinal.{u}} (h : MergeLists xs ys zs) :
    ∃ tl : List (Bool × Ordinal.{u}), tl.map Prod.snd = zs ∧
      (tl.filter fun e => e.1 == true).map Prod.snd = xs ∧
      (tl.filter fun e => e.1 == false).map Prod.snd = ys := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | left x _ ih =>
    obtain ⟨tl, h₁, h₂, h₃⟩ := ih
    exact ⟨(true, x) :: tl, congrArg (x :: ·) h₁, congrArg (x :: ·) h₂, h₃⟩
  | right y _ ih =>
    obtain ⟨tl, h₁, h₂, h₃⟩ := ih
    exact ⟨(false, y) :: tl, congrArg (y :: ·) h₁, h₂, congrArg (y :: ·) h₃⟩

/-- Rocq: `NaturalProduct.cantor_sequence_weaken`. -/
theorem cantor_sequence_weaken (l : List Ordinal.{u}) {x x' : Ordinal.{u}} (h : x ≤ x')
    (hl : CantorSequence x l) : CantorSequence x' l :=
  CantorSequence.mono h hl

/-- Rocq: `NaturalProduct.merge_nil_l`. -/
theorem merge_nil_l : ∀ ys : List Ordinal.{u}, MergeLists [] ys ys
  | [] => .nil
  | y :: ys => .right y (merge_nil_l ys)

/-- Rocq: `NaturalProduct.merge_nil_r`. -/
theorem merge_nil_r : ∀ xs : List Ordinal.{u}, MergeLists xs [] xs
  | [] => .nil
  | x :: xs => .left x (merge_nil_r xs)

/-- Rocq: `NaturalProduct.merge_exists`. -/
theorem merge_exists (em : ExcludedMiddle) (xs : List Ordinal.{u}) :
    ∀ (ys : List Ordinal.{u}) (x y : Ordinal.{u}), CantorSequence x xs → CantorSequence y ys →
      ∃ zs, MergeLists xs ys zs ∧ CantorSequence (x ⊔ y) zs := by
  induction xs with
  | nil => exact fun ys x y _ hys => ⟨ys, merge_nil_l ys, CantorSequence.mono (lub_le2 x y) hys⟩
  | cons a xs ihx =>
    intro ys
    induction ys with
    | nil => exact fun x y hxs _ => ⟨a :: xs, merge_nil_r _, CantorSequence.mono (lub_le1 x y) hxs⟩
    | cons b ys ihy =>
      intro x y ⟨hxa, hxs⟩ ⟨hyb, hys⟩
      match order_total em b a with
      | .inl hba =>
        obtain ⟨zs, hm, hzs⟩ := ihx (b :: ys) a b hxs ⟨le_refl b, hys⟩
        exact ⟨a :: zs, .left a hm, le_trans hxa (lub_le1 x y),
          CantorSequence.mono (lub_least (le_refl a) hba) hzs⟩
      | .inr hab =>
        obtain ⟨zs, hm, hzs⟩ := ihy a b ⟨le_refl a, hxs⟩ hys
        exact ⟨b :: zs, .right b hm, le_trans hyb (lub_le2 x y),
          CantorSequence.mono (lub_least (le_of_lt hab) (le_refl b)) hzs⟩

/-- The split, packaged. Rocq: `NaturalProduct.nadd_split`. -/
theorem nadd_split (em : ExcludedMiddle) (b c : Ordinal.{u}) :
    ∃ Sp : Ordinal.{u} → Bool → Ordinal.{u} → Prop,
      (∀ v, v < b ♯ c → ∃ s p, Sp v s p) ∧
      (∀ v p, Sp v true p → p < b) ∧
      (∀ v p, Sp v false p → p < c) ∧
      (∀ v w s p q, Sp v s p → Sp w s q → v < w → p < q) := by
  obtain ⟨xs, hxs, hb⟩ := cantor_decomposition em b
  obtain ⟨ys, hys, hc⟩ := cantor_decomposition em c
  obtain ⟨zs, hm, hzs⟩ := merge_exists em xs ys b c hxs hys
  have hbc := nadd_cantor_sequences em hm b c (b ⊔ c) hxs hys hzs
  obtain ⟨tl, h₁, h₂, h₃⟩ := merge_tags hm
  refine ⟨SplitR tl, fun v hv => splitR_total em tl v ?_, fun v p h => ?_, fun v p h => ?_,
    splitR_mono em tl⟩
  · show v < cantorDenote (tl.map Prod.snd)
    rw [h₁]
    exact lt_of_lt_of_le hv (le_trans (nadd_le_nadd hb.ge hc.ge) hbc.le)
  · have hb' : p < cantorDenote ((tl.filter fun e => e.1 == true).map Prod.snd) :=
      splitR_bound tl v true p h
    rw [h₂] at hb'
    exact lt_of_lt_of_le hb' hb.le
  · have hc' : p < cantorDenote ((tl.filter fun e => e.1 == false).map Prod.snd) :=
      splitR_bound tl v false p h
    rw [h₃] at hc'
    exact lt_of_lt_of_le hc' hc.le

/-! ## Subdistributivity via the split

Map each point `(u, v)` of the `a × (b ♯ c)` game to `(u, pos v)` on the side
of `v`. This map reflects the order, so the game embeds in the sum of the
`a × b` and `a × c` games. Coverage is tracked semantically: every point of the
left region, sent to its side, lies in the corresponding right region. -/

/-- The point `(u, v)` lies under some rectangle of `R`. Rocq: `NaturalProduct.sem`. -/
def Sem (R : Region.{u}) (u v : Ordinal.{u}) : Prop := ∃ r, r ∈ R ∧ u < r.1 ∧ v < r.2

/-- Rocq: `NaturalProduct.glb_lt`. -/
theorem glb_lt {a x y : Ordinal.{u}} (hx : a < x) (hy : a < y) : a < x ⊓ y :=
  lt_of_lt_of_le (succ_lt a) (glb_greatest _ _ _ (succ_least hx) (succ_least hy))

/-- Rocq: `NaturalProduct.sem_cut_elim`. -/
theorem sem_cut_elim (p : Ordinal.{u} × Ordinal.{u}) (D : Region.{u}) (u v : Ordinal.{u})
    (h : Sem (cut p D) u v) : Sem D u v ∧ (u < p.1 ∨ v < p.2) := by
  obtain ⟨r, hr, hu, hv⟩ := h
  obtain ⟨r₀, hr₀, he⟩ := mem_cut hr
  rcases he with rfl | rfl
  · exact ⟨⟨r₀, hr₀, lt_of_lt_of_le hu (glb_le1 _ _), hv⟩, .inl (lt_of_lt_of_le hu (glb_le2 _ _))⟩
  · exact ⟨⟨r₀, hr₀, hu, lt_of_lt_of_le hv (glb_le1 _ _)⟩, .inr (lt_of_lt_of_le hv (glb_le2 _ _))⟩

/-- Rocq: `NaturalProduct.sem_cut_intro`. -/
theorem sem_cut_intro (q : Ordinal.{u} × Ordinal.{u}) (R : Region.{u}) (u y : Ordinal.{u})
    (h : Sem R u y) (hor : u < q.1 ∨ y < q.2) : Sem (cut q R) u y :=
  let ⟨r, hr, hu, hy⟩ := h
  match hor with
  | .inl hq => ⟨(r.1 ⊓ q.1, r.2), mem_cut_left hr, glb_lt hu hq, hy⟩
  | .inr hq => ⟨(r.1, r.2 ⊓ q.2), mem_cut_right hr, hu, glb_lt hy hq⟩

/-- Rocq: `NaturalProduct.sem_move`. -/
theorem sem_move (D : Region.{u}) (m : Mv D) : Sem D (mvpt D m).1 (mvpt D m).2 := by
  obtain ⟨r, hr, c, d, hm⟩ := mv_elim D m
  rw [hm]
  exact ⟨r, hr, index_lt _ c, index_lt _ d⟩

/-- Rocq: `NaturalProduct.sem_to_move`. -/
theorem sem_to_move (R : Region.{u}) (u y : Ordinal.{u}) (h : Sem R u y) :
    ∃ m : Mv R, u ≤ (mvpt R m).1 ∧ y ≤ (mvpt R m).2 := by
  obtain ⟨r, hr, hu, hy⟩ := h
  obtain ⟨c, hc⟩ := lt_elim hu
  obtain ⟨d, hd⟩ := lt_elim hy
  obtain ⟨m, hm⟩ := mv_intro R r hr c d
  refine ⟨m, ?_, ?_⟩ <;> rw [hm]
  · exact hc
  · exact hd

/-- Rocq: `NaturalProduct.side`. -/
def side (s : Bool) (R₁ R₂ : Region.{u}) : Region.{u} := cond s R₁ R₂

/-- Rocq: `NaturalProduct.covers`. -/
def Covers (T : Ordinal.{u}) (Sp : Ordinal.{u} → Bool → Ordinal.{u} → Prop) (D R₁ R₂ : Region.{u}) :
    Prop :=
  ∀ u v, Sem D u v → v < T ∧ ∀ s p, Sp v s p → Sem (side s R₁ R₂) u p

/-- The upper half of distributivity, given any split of the chain into two
strictly increasing pieces. Rocq: `NaturalProduct.covers_rk`. -/
theorem covers_rk (T : Ordinal.{u}) (Sp : Ordinal.{u} → Bool → Ordinal.{u} → Prop)
    (Sp_total : ∀ v, v < T → ∃ s p, Sp v s p)
    (Sp_mono : ∀ v w s p q, Sp v s p → Sp w s q → v < w → p < q) :
    ∀ D R₁ R₂ : Region.{u}, Covers T Sp D R₁ R₂ → rk D ≤ rk R₁ ♯ rk R₂ := by
  suffices H : ∀ (o : Ordinal.{u}) (D R₁ R₂ : Region.{u}), rk D ≤ o → Covers T Sp D R₁ R₂ →
      rk D ≤ rk R₁ ♯ rk R₂ from fun D R₁ R₂ => H _ D R₁ R₂ (le_refl _)
  intro o
  induction o using ltRec with
  | ind o iho =>
    intro D R₁ R₂ ho hcov
    refine le_intro fun a => ?_
    obtain ⟨m, hm⟩ := rk_lt_elim D _ (index_lt (rk D) a)
    obtain ⟨hT, hside⟩ := hcov _ _ (sem_move D m)
    obtain ⟨s, π, hπ⟩ := Sp_total _ hT
    have hrk : rk (cut (mvpt D m) D) < o := lt_of_lt_of_le (rk_move_lt D m) ho
    refine lt_of_le_of_lt hm ?_
    cases s with
    | true =>
      obtain ⟨m', hq₁, hq₂⟩ := sem_to_move R₁ _ _ (hside true π hπ)
      refine lt_of_le_of_lt (iho _ hrk _ (cut (mvpt R₁ m') R₁) R₂ (le_refl _) fun u v huv => ?_)
        (nadd_increasing1 _ (rk_move_lt R₁ m'))
      obtain ⟨hD, hor⟩ := sem_cut_elim _ D u v huv
      obtain ⟨hTv, hsidev⟩ := hcov u v hD
      refine ⟨hTv, fun s' p' hs' => ?_⟩
      have hsem := hsidev s' p' hs'
      cases s' with
      | false => exact hsem
      | true =>
        refine sem_cut_intro _ R₁ u p' hsem ?_
        match hor with
        | .inl hu => exact .inl (lt_of_lt_of_le hu hq₁)
        | .inr hv => exact .inr (lt_of_lt_of_le (Sp_mono v _ true p' π hs' hπ hv) hq₂)
    | false =>
      obtain ⟨m', hq₁, hq₂⟩ := sem_to_move R₂ _ _ (hside false π hπ)
      refine lt_of_le_of_lt (iho _ hrk _ R₁ (cut (mvpt R₂ m') R₂) (le_refl _) fun u v huv => ?_)
        (nadd_increasing2 _ (rk_move_lt R₂ m'))
      obtain ⟨hD, hor⟩ := sem_cut_elim _ D u v huv
      obtain ⟨hTv, hsidev⟩ := hcov u v hD
      refine ⟨hTv, fun s' p' hs' => ?_⟩
      have hsem := hsidev s' p' hs'
      cases s' with
      | true => exact hsem
      | false =>
        refine sem_cut_intro _ R₂ u p' hsem ?_
        match hor with
        | .inl hu => exact .inl (lt_of_lt_of_le hu hq₁)
        | .inr hv => exact .inr (lt_of_lt_of_le (Sp_mono v _ false p' π hs' hπ hv) hq₂)

/-- Classical subdistributivity. Rocq: `NaturalProduct.nmulOrd_distrib_upper`. -/
theorem nmul_distrib_upper (em : ExcludedMiddle) (a b c : Ordinal.{u}) :
    nmul a (b ♯ c) ≤ nmul a b ♯ nmul a c := by
  obtain ⟨Sp, htot, hb, hc, hmono⟩ := nadd_split em b c
  refine le_trans (nmul_rk a (b ♯ c)).le (le_trans (covers_rk (b ♯ c) Sp htot hmono
    [(a, b ♯ c)] [(a, b)] [(a, c)] fun u v ⟨r, hr, hu, hv⟩ => ?_)
    (nadd_le_nadd (nmul_rk a b).ge (nmul_rk a c).ge))
  cases hr with
  | head =>
    refine ⟨hv, fun s p hsp => ?_⟩
    cases s with
    | true => exact ⟨(a, b), .head _, hu, hb v p hsp⟩
    | false => exact ⟨(a, c), .head _, hu, hc v p hsp⟩
  | tail _ h => nomatch h

/-- Classically, the natural product distributes over the natural sum.
Rocq: `NaturalProduct.nmulOrd_distrib`. -/
theorem nmul_distrib (em : ExcludedMiddle) (a b c : Ordinal.{u}) :
    nmul a (b ♯ c) ≈ nmul a b ♯ nmul a c :=
  equiv_intro (nmul_distrib_upper em a b c) (nmul_distrib_lower em a b c)

/-! # The exponent law: `ω^α ⊗ ω^β ≈ ω^(α ♯ β)` -/

/-- Rocq: `NaturalProduct.nmulOrd_eq_mor`. -/
theorem nmul_congr {x y a b : Ordinal.{u}} (hxy : x ≈ y) (hab : a ≈ b) : nmul x a ≈ nmul y b :=
  equiv_intro (nmul_monotone hxy.le hab.le) (nmul_monotone hxy.ge hab.ge)

/-- Subadditivity: a move in a union is a move in one of the parts, and only
shrinks the other. Rocq: `NaturalProduct.rsub_app`. -/
theorem rsub_app {A A' B B' : Region.{u}} (hA : Rsub A A') (hB : Rsub B B') : Rsub (A ++ B) (A' ++ B') :=
  fun r hr =>
    match mem_append_cases hr with
    | .inl h =>
      match hA r h with
      | .inl hz => .inl hz
      | .inr ⟨s, hs, hrs⟩ => .inr ⟨s, List.mem_append_left _ hs, hrs⟩
    | .inr h =>
      match hB r h with
      | .inl hz => .inl hz
      | .inr ⟨s, hs, hrs⟩ => .inr ⟨s, List.mem_append_right _ hs, hrs⟩

theorem cut_append (p : Ordinal.{u} × Ordinal.{u}) :
    ∀ R₁ R₂ : Region.{u}, cut p (R₁ ++ R₂) = cut p R₁ ++ cut p R₂
  | [], _ => rfl
  | r :: R₁, R₂ => congrArg (fun l => (r.1 ⊓ p.1, r.2) :: (r.1, r.2 ⊓ p.2) :: l) (cut_append p R₁ R₂)

/-- Rocq: `NaturalProduct.rk_app_le`. -/
theorem rk_app_le (R₁ R₂ : Region.{u}) : rk (R₁ ++ R₂) ≤ rk R₁ ♯ rk R₂ := by
  suffices H : ∀ (o : Ordinal.{u}) (R₁ R₂ : Region.{u}), rk R₁ ♯ rk R₂ ≤ o →
      rk (R₁ ++ R₂) ≤ rk R₁ ♯ rk R₂ from H _ R₁ R₂ (le_refl _)
  intro o
  induction o using ltRec with
  | ind o iho =>
    intro R₁ R₂ ho
    refine le_intro fun a => ?_
    obtain ⟨m, hm⟩ := rk_lt_elim _ _ (index_lt (rk (R₁ ++ R₂)) a)
    refine lt_of_le_of_lt hm ?_
    obtain ⟨r, hr, c, d, hp⟩ := mv_elim _ m
    rw [cut_append]
    rcases mem_append_cases hr with hr | hr
    · obtain ⟨m₁, hm₁⟩ := mv_intro R₁ r hr c d
      rw [hp.trans hm₁.symm]
      exact lt_of_le_of_lt (le_trans (rk_mono (rsub_app (rsub_refl _) (cut_sub _ R₂)))
          (iho _ (lt_of_lt_of_le (nadd_increasing1 _ (rk_move_lt R₁ m₁)) ho) _ _ (le_refl _)))
        (nadd_increasing1 _ (rk_move_lt R₁ m₁))
    · obtain ⟨m₂, hm₂⟩ := mv_intro R₂ r hr c d
      rw [hp.trans hm₂.symm]
      exact lt_of_le_of_lt (le_trans (rk_mono (rsub_app (cut_sub _ R₁) (rsub_refl _)))
          (iho _ (lt_of_lt_of_le (nadd_increasing2 _ (rk_move_lt R₂ m₂)) ho) _ _ (le_refl _)))
        (nadd_increasing2 _ (rk_move_lt R₂ m₂))

/-- Finite natural multiples. Rocq: `NaturalProduct.nrep`. -/
def nrep : Nat → Ordinal.{u} → Ordinal.{u}
  | 0, _ => 0
  | k + 1, x => nrep k x ♯ x

/-- Rocq: `NaturalProduct.nrep_mono` and `NaturalProduct.nrep_le_mor`. -/
theorem nrep_mono : ∀ (k : Nat) {x y : Ordinal.{u}}, x ≤ y → nrep k x ≤ nrep k y
  | 0, _, _, _ => le_refl _
  | k + 1, _, _, h => nadd_le_nadd (nrep_mono k h) h

/-- Rocq: `NaturalProduct.nrep_eq_mor`. -/
theorem nrep_congr (k : Nat) {x y : Ordinal.{u}} (h : x ≈ y) : nrep k x ≈ nrep k y :=
  equiv_intro (nrep_mono k h.le) (nrep_mono k h.ge)

/-- Rocq: `NaturalProduct.mul_nat_le_nrep`. -/
theorem mul_nat_le_nrep (x : Ordinal.{u}) : ∀ k : Nat, x * ofNat k ≤ nrep k x
  | 0 => (mul_zero x).le
  | k + 1 => le_trans (mul_succ _ _).le (le_trans (add_nadd_le _ _) (nadd_le_nadd (mul_nat_le_nrep x k) (le_refl _)))

/-- Rocq: `NaturalProduct.nrep_below`. -/
theorem nrep_below (em : ExcludedMiddle) {γ δ : Ordinal.{u}} (h : γ < δ) : ∀ k : Nat, nrep k (ω ^ γ) < ω ^ δ
  | 0 => pow_pos ω δ
  | k + 1 => nadd_closed em δ _ _ (ord_complete em δ) (nrep_below em h k) (pow_lt_pow_right omega_gt1 h)

/-- Rocq: `NaturalProduct.nmul_nrep_l`. -/
theorem nmul_nrep_l (em : ExcludedMiddle) : ∀ (k : Nat) (x y : Ordinal.{u}), nmul (nrep k x) y ≈ nrep k (nmul x y)
  | 0, _, y => equiv_trans (nmul_comm 0 y) (nmul_zero y)
  | k + 1, x, y =>
    equiv_trans (nmul_comm _ y) (equiv_trans (nmul_distrib em y (nrep k x) x)
      (nadd_congr (equiv_trans (nmul_comm y _) (nmul_nrep_l em k x y)) (nmul_comm y x)))

/-- Rocq: `NaturalProduct.exp_below`. -/
theorem exp_below (u α : Ordinal.{u}) (h : u < ω ^ α) :
    u < 1 ∨ ∃ (i : α) (k : Nat), u ≤ nrep k (ω ^ α i) := by
  rw [pow_unfold] at h
  match lub_lt h with
  | .inl h₁ => exact .inl h₁
  | .inr h₂ =>
    obtain ⟨i, hi⟩ := sup_lt h₂
    rw [mul_unfold] at hi
    obtain ⟨⟨n⟩, hn⟩ := sup_lt hi
    exact .inr ⟨i, n + 1, le_trans (le_of_lt (lt_of_lt_of_le hn (mul_succ _ _).ge))
      (mul_nat_le_nrep _ (n + 1))⟩

/-- Rocq: `NaturalProduct.below_one`. -/
theorem below_one (u : Ordinal.{u}) (h : u < 1) : u ≤ 0 :=
  (lt_elim h).elim fun _ h => h

/-- One side of the upper bound, shared by both coordinates.
Rocq: `NaturalProduct.exp_upper_part`. -/
theorem exp_upper_part (em : ExcludedMiddle) (α β u : Ordinal.{u})
    (ih : ∀ i : α, nmul (ω ^ α i) (ω ^ β) ≤ ω ^ (α i ♯ β)) (hu : u < ω ^ α) :
    nmul u (ω ^ β) < ω ^ (α ♯ β) :=
  match exp_below u α hu with
  | .inl h₁ => lt_of_le_of_lt (nmul_monotone (below_one u h₁) (le_refl _))
      (lt_of_le_of_lt (le_trans (nmul_comm _ _).le (nmul_zero _).le) (pow_pos ω _))
  | .inr ⟨i, k, hk⟩ => lt_of_le_of_lt (nmul_monotone hk (le_refl _))
      (lt_of_le_of_lt (nmul_nrep_l em k _ _).le (lt_of_le_of_lt (nrep_mono k (ih i))
        (nrep_below em (nadd_increasing1 β (index_lt α i)) k)))

/-- Rocq: `NaturalProduct.nmulOrd_exp_upper`. -/
theorem nmul_exp_upper (em : ExcludedMiddle) (α : Ordinal.{u}) :
    ∀ β : Ordinal.{u}, nmul (ω ^ α) (ω ^ β) ≤ ω ^ (α ♯ β) := by
  induction α using ltRec with
  | ind α iha =>
    intro β
    induction β using ltRec with
    | ind β ihb =>
      refine le_trans (nmul_rk _ _).le (le_intro fun a => ?_)
      obtain ⟨m, hm⟩ := rk_lt_elim _ _ (index_lt (rk [(ω ^ α, ω ^ β)]) a)
      refine lt_of_le_of_lt hm ?_
      obtain ⟨r, hr, c, d, hp⟩ := mv_elim _ m
      cases hr with
      | tail _ h => nomatch h
      | head =>
        have hpx : (mvpt _ m).1 < ω ^ α := by rw [hp]; exact index_lt _ c
        have hpy : (mvpt _ m).2 < ω ^ β := by rw [hp]; exact index_lt _ d
        refine lt_of_le_of_lt (rk_mono (E := [((mvpt _ m).1, ω ^ β)] ++ [(ω ^ α, (mvpt _ m).2)])
          fun r hr => ?_) (lt_of_le_of_lt (rk_app_le _ _) (lt_of_le_of_lt
            (nadd_le_nadd (nmul_rk _ _).ge (nmul_rk _ _).ge) ?_))
        · cases hr with
          | head => exact .inr ⟨((mvpt _ m).1, ω ^ β), .head _, glb_le2 _ _, le_refl _⟩
          | tail _ h =>
            cases h with
            | head => exact .inr ⟨(ω ^ α, (mvpt _ m).2), .tail _ (.head _), le_refl _, glb_le2 _ _⟩
            | tail _ h => nomatch h
        · refine nadd_closed em _ _ _ (ord_complete em _)
            (exp_upper_part em α β _ (fun i => iha (α i) (index_lt α i) β) hpx) ?_
          refine lt_of_le_of_lt (nmul_comm _ _).le (lt_of_lt_of_le
            (exp_upper_part em β α _ (fun j => le_trans (nmul_comm _ _).le (le_trans
              (ihb (β j) (index_lt β j)) (pow_le_pow_right ω (nadd_comm _ _).le))) hpy)
            (pow_le_pow_right ω (nadd_comm _ _).le))

/-- Rocq: `NaturalProduct.nmulOrd_exp_lower`. -/
theorem nmul_exp_lower (em : ExcludedMiddle) (α : Ordinal.{u}) :
    ∀ β : Ordinal.{u}, ω ^ (α ♯ β) ≤ nmul (ω ^ α) (ω ^ β) := by
  induction α using ltRec with
  | ind α iha =>
    intro β
    induction β using ltRec with
    | ind β ihb =>
      rw [nadd_unfold α β, pow_unfold]
      refine lub_least (le_trans (nmul_one 1).ge (nmul_monotone (succ_least (pow_pos _ _))
        (succ_least (pow_pos _ _)))) (sup_least fun i => ?_)
      rw [mul_unfold]
      refine sup_least fun ⟨n⟩ => le_trans (mul_succ _ _).ge (le_trans (mul_nat_le_nrep _ (n + 1)) ?_)
      match i with
      | .inl a =>
        exact le_trans (nrep_mono (n + 1) (iha (α a) (index_lt α a) β))
          (le_trans (nmul_nrep_l em (n + 1) _ _).ge
            (nmul_monotone (le_of_lt (nrep_below em (index_lt α a) (n + 1))) (le_refl _)))
      | .inr b =>
        exact le_trans (nrep_mono (n + 1) (ihb (β b) (index_lt β b)))
          (le_trans (nrep_mono (n + 1) (nmul_comm _ _).le) (le_trans (nmul_nrep_l em (n + 1) _ _).ge
            (le_trans (nmul_comm _ _).le
              (nmul_monotone (le_refl _) (le_of_lt (nrep_below em (index_lt β b) (n + 1)))))))

/-- Classically, `ω^α ⊗ ω^β ≈ ω^(α ♯ β)`. Rocq: `NaturalProduct.nmulOrd_exp`. -/
theorem nmul_exp (em : ExcludedMiddle) (α β : Ordinal.{u}) : nmul (ω ^ α) (ω ^ β) ≈ ω ^ (α ♯ β) :=
  equiv_intro (nmul_exp_upper em α β) (nmul_exp_lower em α β)

/-! # Identification with Hessenberg's natural product

Classically, writing `a = ω^α1 + ... + ω^αm` and `b = ω^β1 + ... + ω^βn` in
Cantor normal form, Hessenberg's product is the natural sum of the terms
`ω^(αi ♯ βj)` over all pairs `i, j`. `nmul` satisfies exactly this formula. It
follows from distributivity and the exponent law alone; the general form below
needs no ordering on the lists. -/

/-- All pairwise natural sums of exponents. Rocq: `NaturalProduct.cnf_prod`
(a `flat_map`; here the same list by recursion). -/
def cnfProd : List Ordinal.{u} → List Ordinal.{u} → List Ordinal.{u}
  | [], _ => []
  | a :: xs, ys => ys.map (fun b => a ♯ b) ++ cnfProd xs ys

/-- Rocq: `NaturalProduct.nmul_exp_nadd`. -/
theorem nmul_exp_nadd (em : ExcludedMiddle) (a : Ordinal.{u}) : ∀ ys : List Ordinal.{u},
    nmul (ω ^ a) (cantorDenoteNadd ys) ≈ cantorDenoteNadd (ys.map fun b => a ♯ b)
  | [] => nmul_zero _
  | b :: ys => equiv_trans (nmul_distrib em _ _ _) (nadd_congr (nmul_exp em a b) (nmul_exp_nadd em a ys))

/-- Natural sums of ω-powers multiply term by term.
Rocq: `NaturalProduct.nmulOrd_nadd_powers`. -/
theorem nmul_nadd_powers (em : ExcludedMiddle) : ∀ xs ys : List Ordinal.{u},
    nmul (cantorDenoteNadd xs) (cantorDenoteNadd ys) ≈ cantorDenoteNadd (cnfProd xs ys)
  | [], _ => equiv_trans (nmul_comm _ _) (nmul_zero _)
  | a :: xs, ys =>
    equiv_trans (nmul_comm _ _) (equiv_trans (nmul_distrib em _ _ _) (equiv_trans
      (nadd_congr (equiv_trans (nmul_comm _ _) (nmul_exp_nadd em a ys))
        (equiv_trans (nmul_comm _ _) (nmul_nadd_powers em xs ys)))
      (equiv_symm (cantor_denote_nadd_app _ _))))

/-- The formula on Cantor normal forms. Rocq: `NaturalProduct.nmulOrd_cantor`. -/
theorem nmul_cantor (em : ExcludedMiddle) (xs ys : List Ordinal.{u}) (x y : Ordinal.{u})
    (hxs : CantorSequence x xs) (hys : CantorSequence y ys) :
    nmul (cantorDenote xs) (cantorDenote ys) ≈ cantorDenoteNadd (cnfProd xs ys) :=
  equiv_trans (nmul_congr (cantor_denote_nadd_eq em xs x (each_complete em xs) hxs)
      (cantor_denote_nadd_eq em ys y (each_complete em ys) hys))
    (nmul_nadd_powers em xs ys)

/-- `nmul` is Hessenberg's natural product. Rocq: `NaturalProduct.nmulOrd_is_hessenberg`. -/
theorem nmul_is_hessenberg (em : ExcludedMiddle) (a b : Ordinal.{u}) :
    ∃ xs ys, CantorSequence a xs ∧ cantorDenote xs ≈ a ∧ CantorSequence b ys ∧
      cantorDenote ys ≈ b ∧ nmul a b ≈ cantorDenoteNadd (cnfProd xs ys) := by
  obtain ⟨xs, hxs, ha⟩ := cantor_decomposition em a
  obtain ⟨ys, hys, hb⟩ := cantor_decomposition em b
  exact ⟨xs, ys, hxs, ha, hys, hb,
    equiv_trans (nmul_congr (equiv_symm ha) (equiv_symm hb)) (nmul_cantor em xs ys a b hxs hys)⟩

/-! # Superdistributivity on a decidable universe

Superdistributivity, `a ⊗ b ♯ a ⊗ c ≤ a ⊗ (b ♯ c)`, implies the weak excluded
middle in general (`distrib_lower_WEM`), but its proof (`rsum_step`) uses the
excluded middle only to compare corners of rectangles with coordinates of
moves. Those comparisons are decidable when every ordinal in sight lies in a
universe `Q` with a decidable order, closed under the operations that build
positions: `Q` is closed under `≈`, `♯` and `0`, and the trees are
hereditarily in `Q` (`QH`). For a notation system with interpolants, the
notations provide such a universe (`Notation/CantorProduct.lean`).

Each declaration takes exactly the section hypotheses that Rocq's section
closing gives it. -/

section decidable_universe

variable (Q : Ordinal.{u} → Prop) (Q_eq : ∀ x y, x ≈ y → Q x → Q y)
  (Q_dec : ∀ x y, Q x → Q y → x < y ∨ y ≤ x) (Q_zero : Q 0)
  (Q_nadd : ∀ x y, Q x → Q y → Q (x ♯ y))

/-- Hereditary membership: all descendants lie in `Q`. Rocq: `NaturalProduct.HQ`. -/
def HQ : Ordinal.{u} → Prop
  | mk _ g => ∀ a, Q (g a) ∧ HQ (g a)

/-- `x` and all its descendants lie in `Q`. Rocq: `NaturalProduct.QH`. -/
def QH (x : Ordinal.{u}) : Prop := Q x ∧ HQ Q x

/-- Rocq: `NaturalProduct.QH_child`. -/
theorem QH_child : ∀ (x : Ordinal.{u}) (i : x), QH Q x → QH Q (x i)
  | mk _ _, i, h => h.2 i

include Q_zero in
/-- Rocq: `NaturalProduct.QH_zero`. -/
theorem QH_zero : QH Q 0 := ⟨Q_zero, fun a => PEmpty.elim a⟩

include Q_eq Q_dec in
/-- Rocq: `NaturalProduct.Q_glb`. -/
theorem Q_glb {x y : Ordinal.{u}} (hx : Q x) (hy : Q y) : Q (x ⊓ y) :=
  match Q_dec x y hx hy with
  | .inl h => Q_eq x _ (equiv_intro (glb_greatest _ _ _ (le_refl _) (le_of_lt h)) (glb_le1 _ _)) hx
  | .inr h => Q_eq y _ (equiv_intro (glb_greatest _ _ _ h (le_refl _)) (glb_le2 _ _)) hy

include Q_eq Q_dec in
/-- Rocq: `NaturalProduct.QH_glb`. -/
theorem QH_glb : ∀ x y : Ordinal.{u}, QH Q x → QH Q y → QH Q (x ⊓ y)
  | mk A f, mk B g, hx, hy => ⟨Q_glb Q Q_eq Q_dec hx.1 hy.1, by
      rw [glb_unfold]
      exact fun ab => QH_glb (f ab.1) (g ab.2) (hx.2 ab.1) (hy.2 ab.2)⟩

/-- Rocq: `NaturalProduct.HQ_lub`. -/
theorem HQ_lub {x y : Ordinal.{u}} (hx : HQ Q x) (hy : HQ Q y) : HQ Q (x ⊔ y) := by
  cases x; cases y
  exact fun i => match i with
    | .inl a => hx a
    | .inr b => hy b

include Q_nadd in
/-- Rocq: `NaturalProduct.QH_nadd`. -/
theorem QH_nadd (x : Ordinal.{u}) : ∀ y : Ordinal.{u}, QH Q x → QH Q y → QH Q (x ♯ y) := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      intro hx hy
      refine ⟨Q_nadd _ _ hx.1 hy.1, ?_⟩
      rw [nadd_unfold]
      exact HQ_lub Q (fun a => ihx (x a) (index_lt x a) y (QH_child Q x a hx) hy)
        (fun b => ihy (y b) (index_lt y b) hx (QH_child Q y b hy))

include Q_zero Q_nadd in
/-- Rocq: `NaturalProduct.QH_nrep`. -/
theorem QH_nrep (x : Ordinal.{u}) (hx : QH Q x) : ∀ k : Nat, QH Q (nrep k x)
  | 0 => QH_zero Q Q_zero
  | k + 1 => QH_nadd Q Q_nadd _ _ (QH_nrep x hx k) hx

/-- Regions whose corners are hereditarily in `Q`. Rocq: `NaturalProduct.QR`. -/
def QR (R : Region.{u}) : Prop := ∀ r, r ∈ R → QH Q r.1 ∧ QH Q r.2

/-- Rocq: `NaturalProduct.QR_move`. -/
theorem QR_move (R : Region.{u}) (m : Mv R) (h : QR Q R) : QH Q (mvpt R m).1 ∧ QH Q (mvpt R m).2 := by
  obtain ⟨r, hr, c, d, hm⟩ := mv_elim R m
  rw [hm]
  exact ⟨QH_child Q _ c (h r hr).1, QH_child Q _ d (h r hr).2⟩

include Q_eq Q_dec in
/-- Rocq: `NaturalProduct.QR_cut`. -/
theorem QR_cut (p : Ordinal.{u} × Ordinal.{u}) (R : Region.{u}) (hp₁ : QH Q p.1) (hp₂ : QH Q p.2)
    (h : QR Q R) : QR Q (cut p R) := fun _ hr => by
  obtain ⟨r₁, hr₁, he⟩ := mem_cut hr
  rcases he with rfl | rfl
  · exact ⟨QH_glb Q Q_eq Q_dec _ _ (h r₁ hr₁).1 hp₁, (h r₁ hr₁).2⟩
  · exact ⟨(h r₁ hr₁).1, QH_glb Q Q_eq Q_dec _ _ (h r₁ hr₁).2 hp₂⟩

include Q_eq Q_dec Q_nadd in
/-- Rocq: `NaturalProduct.QR_rsum`. -/
theorem QR_rsum (R₁ R₂ : Region.{u}) (h₁ : QR Q R₁) (h₂ : QR Q R₂) : QR Q (rsum R₁ R₂) := fun r hr => by
  obtain ⟨r₁, r₂, hr₁, hr₂, rfl⟩ := (in_rsum r R₁ R₂).1 hr
  exact ⟨QH_glb Q Q_eq Q_dec _ _ (h₁ r₁ hr₁).1 (h₂ r₂ hr₂).1, QH_nadd Q Q_nadd _ _ (h₁ r₁ hr₁).2 (h₂ r₂ hr₂).2⟩

/-- Rocq: `NaturalProduct.exists_dec`. -/
theorem exists_dec (Pr : Ordinal.{u} × Ordinal.{u} → Prop) : ∀ l : Region.{u},
    (∀ s, s ∈ l → Pr s ∨ ¬Pr s) → (∃ s, s ∈ l ∧ Pr s) ∨ ¬(∃ s, s ∈ l ∧ Pr s)
  | [], _ => .inr fun ⟨_, h, _⟩ => nomatch h
  | a :: l, hd =>
    match hd a (.head _) with
    | .inl ha => .inl ⟨a, .head _, ha⟩
    | .inr ha =>
      match exists_dec Pr l (fun s hs => hd s (.tail _ hs)) with
      | .inl ⟨s, hs, hps⟩ => .inl ⟨s, .tail _ hs, hps⟩
      | .inr hl => .inr fun ⟨s, hs, hps⟩ => by
          cases hs with
          | head => exact ha hps
          | tail _ h => exact hl ⟨s, h, hps⟩

include Q_dec in
/-- Rocq: `NaturalProduct.list_max_Q`. -/
theorem list_max_Q (Pr : Ordinal.{u} × Ordinal.{u} → Prop) : ∀ l : Region.{u},
    (∀ s, s ∈ l → (Pr s ∨ ¬Pr s) ∧ Q s.2) → (∃ s, s ∈ l ∧ Pr s) →
      ∃ s, s ∈ l ∧ Pr s ∧ ∀ s', s' ∈ l → Pr s' → s'.2 ≤ s.2
  | [], _, ⟨_, h, _⟩ => nomatch h
  | a :: l, hd, hex => by
    match exists_dec Pr l (fun s hs => (hd s (.tail _ hs)).1) with
    | .inl hl =>
      obtain ⟨s, hs, hps, hmax⟩ := list_max_Q Pr l (fun s hs => hd s (.tail _ hs)) hl
      match hd a (.head _) with
      | ⟨.inl hpa, hqa⟩ =>
        match Q_dec s.2 a.2 (hd s (.tail _ hs)).2 hqa with
        | .inl hsa =>
          refine ⟨a, .head _, hpa, fun s' hs' hps' => ?_⟩
          cases hs' with
          | head => exact le_refl _
          | tail _ h => exact le_of_lt (lt_of_le_of_lt (hmax s' h hps') hsa)
        | .inr has =>
          refine ⟨s, .tail _ hs, hps, fun s' hs' hps' => ?_⟩
          cases hs' with
          | head => exact has
          | tail _ h => exact hmax s' h hps'
      | ⟨.inr hpa, _⟩ =>
        refine ⟨s, .tail _ hs, hps, fun s' hs' hps' => ?_⟩
        cases hs' with
        | head => exact (hpa hps').elim
        | tail _ h => exact hmax s' h hps'
    | .inr hl =>
      obtain ⟨s, hs, hps⟩ := hex
      cases hs with
      | head =>
        refine ⟨a, .head _, hps, fun s' hs' hps' => ?_⟩
        cases hs' with
        | head => exact le_refl _
        | tail _ h => exact (hl ⟨s', h, hps'⟩).elim
      | tail _ h => exact (hl ⟨s, h, hps⟩).elim

include Q_dec in
/-- Rocq: `NaturalProduct.rsum_step_Q`. -/
theorem rsum_step_Q (W : Ordinal.{u}) (R₁ R₂ : Region.{u}) (m : Mv R₁) (hq₁ : QR Q R₁) (hq₂ : QR Q R₂)
    (hw₁ : Wide W R₁) (hw₂ : Wide W R₂)
    (ih : rk (cut (mvpt R₁ m) R₁) ♯ rk R₂ ≤ rk (rsum (cut (mvpt R₁ m) R₁) R₂)) :
    rk (cut (mvpt R₁ m) R₁) ♯ rk R₂ < rk (rsum R₁ R₂) := by
  have hqx := (QR_move Q R₁ m hq₁).1.1
  obtain ⟨r₁, hr₁, c, d, hm⟩ := mv_elim R₁ m
  have hq₁' : (mvpt R₁ m).1 < r₁.1 := by rw [hm]; exact index_lt r₁.1 c
  have hq₂' : (mvpt R₁ m).2 < r₁.2 := by rw [hm]; exact index_lt r₁.2 d
  have hcov : ∃ s, s ∈ R₂ ∧ (mvpt R₁ m).1 < s.1 :=
    let ⟨⟨s, hs, hWs⟩, _⟩ := hw₂
    ⟨s, hs, lt_of_lt_of_le hq₁' (le_trans (hw₁.2 r₁ hr₁) hWs)⟩
  have hdec : ∀ s, s ∈ R₂ → ((mvpt R₁ m).1 < s.1 ∨ ¬(mvpt R₁ m).1 < s.1) ∧ Q s.2 := fun s hs =>
    ⟨match Q_dec _ _ hqx (hq₂ s hs).1.1 with
      | .inl h => .inl h
      | .inr h => .inr fun h' => lt_irrefl _ (lt_of_lt_of_le h' h),
     (hq₂ s hs).2.1⟩
  obtain ⟨s₂, hs₂, hqs₂, hmax⟩ := list_max_Q Q Q_dec (fun s => (mvpt R₁ m).1 < s.1) R₂ hdec hcov
  obtain ⟨cg, hcg⟩ := lt_elim (show (mvpt R₁ m).1 < r₁.1 ⊓ s₂.1 from
    lt_of_lt_of_le (succ_lt _) (glb_greatest _ _ _ (succ_least hq₁') (succ_least hqs₂)))
  obtain ⟨dg, hdg⟩ := lt_elim (nadd_increasing1 s₂.2 hq₂')
  obtain ⟨m', hm'⟩ := mv_intro _ _ ((in_rsum _ R₁ R₂).2 ⟨r₁, s₂, hr₁, hs₂, rfl⟩) cg dg
  have hqp : (mvpt R₁ m).1 ≤ (mvpt (rsum R₁ R₂) m').1 := by rw [hm']; exact hcg
  have hqp₂ : (mvpt R₁ m).2 ♯ s₂.2 ≤ (mvpt (rsum R₁ R₂) m').2 := by rw [hm']; exact hdg
  refine lt_of_le_of_lt ih (lt_of_le_of_lt (rk_mono fun r hr => ?_) (rk_move_lt _ m'))
  obtain ⟨r₁', r₂, h₁, h₂, rfl⟩ := (in_rsum _ _ _).1 hr
  obtain ⟨r₀, hr₀, hpiece⟩ := mem_cut h₁
  have hsrc : (r₀.1 ⊓ r₂.1, r₀.2 ♯ r₂.2) ∈ rsum R₁ R₂ := (in_rsum _ _ _).2 ⟨r₀, r₂, hr₀, h₂, rfl⟩
  rcases hpiece with rfl | rfl
  · exact .inr ⟨((r₀.1 ⊓ r₂.1) ⊓ (mvpt (rsum R₁ R₂) m').1, r₀.2 ♯ r₂.2), mem_cut_left hsrc,
      glb_greatest _ _ _ (glb_greatest _ _ _ (le_trans (glb_le1 _ _) (glb_le1 _ _)) (glb_le2 _ _))
        (le_trans (glb_le1 _ _) (le_trans (glb_le2 _ _) hqp)), le_refl _⟩
  · match Q_dec _ _ hqx (hq₂ r₂ h₂).1.1 with
    | .inl hqr₂ =>
      exact .inr ⟨(r₀.1 ⊓ r₂.1, (r₀.2 ♯ r₂.2) ⊓ (mvpt (rsum R₁ R₂) m').2), mem_cut_right hsrc,
        le_refl _, glb_greatest _ _ _ (nadd_le_nadd (glb_le1 _ _) (le_refl _))
          (le_trans (nadd_le_nadd (glb_le2 _ _) (hmax r₂ h₂ hqr₂)) hqp₂)⟩
    | .inr hr₂q =>
      exact .inr ⟨((r₀.1 ⊓ r₂.1) ⊓ (mvpt (rsum R₁ R₂) m').1, r₀.2 ♯ r₂.2), mem_cut_left hsrc,
        glb_greatest _ _ _ (le_refl _) (le_trans (glb_le2 _ _) (le_trans hr₂q hqp)),
        nadd_le_nadd (glb_le1 _ _) (le_refl _)⟩

include Q_eq Q_dec in
/-- Rocq: `NaturalProduct.rsum_lower_Q`. -/
theorem rsum_lower_Q (W : Ordinal.{u}) (R₁ R₂ : Region.{u}) (hq₁ : QR Q R₁) (hq₂ : QR Q R₂)
    (hw₁ : Wide W R₁) (hw₂ : Wide W R₂) : rk R₁ ♯ rk R₂ ≤ rk (rsum R₁ R₂) := by
  suffices H : ∀ (o : Ordinal.{u}) (R₁ R₂ : Region.{u}), rk R₁ ♯ rk R₂ ≤ o → QR Q R₁ → QR Q R₂ →
      Wide W R₁ → Wide W R₂ → rk R₁ ♯ rk R₂ ≤ rk (rsum R₁ R₂) from
    H _ R₁ R₂ (le_refl _) hq₁ hq₂ hw₁ hw₂
  intro o
  induction o using ltRec with
  | ind o iho =>
    intro R₁ R₂ ho hq₁ hq₂ hw₁ hw₂
    refine nadd_least3 (fun i hi => ?_) (fun j hj => ?_)
    · obtain ⟨m, hm⟩ := rk_lt_elim R₁ i hi
      obtain ⟨hm₁, hm₂⟩ := QR_move Q R₁ m hq₁
      exact lt_of_le_of_lt (nadd_le_nadd hm (le_refl _)) (rsum_step_Q Q Q_dec W R₁ R₂ m hq₁ hq₂ hw₁ hw₂
        (iho _ (lt_of_lt_of_le (nadd_increasing1 _ (rk_move_lt R₁ m)) ho) _ _ (le_refl _)
          (QR_cut Q Q_eq Q_dec _ _ hm₁ hm₂ hq₁) hq₂ (wide_cut _ _ _ hw₁) hw₂))
    · obtain ⟨m, hm⟩ := rk_lt_elim R₂ j hj
      obtain ⟨hm₁, hm₂⟩ := QR_move Q R₂ m hq₂
      have ih' : rk (cut (mvpt R₂ m) R₂) ♯ rk R₁ ≤ rk (rsum (cut (mvpt R₂ m) R₂) R₁) :=
        le_trans (nadd_comm _ _).le (le_trans (iho _ (lt_of_lt_of_le (nadd_increasing2 _ (rk_move_lt R₂ m)) ho)
          R₁ _ (le_refl _) hq₁ (QR_cut Q Q_eq Q_dec _ _ hm₁ hm₂ hq₂) hw₁ (wide_cut _ _ _ hw₂))
          (rk_mono (rsum_comm _ _)))
      exact lt_of_le_of_lt (le_trans (nadd_le_nadd (le_refl _) hm) (nadd_comm _ _).le)
        (lt_of_lt_of_le (rsum_step_Q Q Q_dec W R₂ R₁ m hq₂ hq₁ hw₂ hw₁ ih') (rk_mono (rsum_comm R₂ R₁)))

include Q_eq Q_dec Q_zero in
/-- Superdistributivity on a decidable universe, constructively.
Rocq: `NaturalProduct.nmulOrd_distrib_lower_Q`. -/
theorem nmul_distrib_lower_Q (a b c : Ordinal.{u}) (ha : QH Q a) (hb : QH Q b) (hc : QH Q c) :
    nmul a b ♯ nmul a c ≤ nmul a (b ♯ c) := by
  have hW : ∀ y, Wide a [(a, y), (a, 0)] := fun y =>
    ⟨⟨(a, y), .head _, le_refl _⟩, fun r hr => (pad_bound a y r hr).1⟩
  have hQR : ∀ y, QH Q y → QR Q [(a, y), (a, 0)] := fun y hy r hr => by
    cases hr with
    | head => exact ⟨ha, hy⟩
    | tail _ h =>
      cases h with
      | head => exact ⟨ha, QH_zero Q Q_zero⟩
      | tail _ h => nomatch h
  refine le_trans (nadd_le_nadd (nmul_rk a b).le (nmul_rk a c).le) (le_trans (nadd_le_nadd
    (rk_mono (rsub_in (s := (a, b)) (E := [(a, b), (a, 0)]) (.head _) ⟨le_refl _, le_refl _⟩))
    (rk_mono (rsub_in (s := (a, c)) (E := [(a, c), (a, 0)]) (.head _) ⟨le_refl _, le_refl _⟩)))
    (le_trans (rsum_lower_Q Q Q_eq Q_dec a _ _ (hQR b hb) (hQR c hc) (hW b) (hW c))
      (le_trans (rk_mono ?_) (nmul_rk a (b ♯ c)).ge)))
  intro r hr
  obtain ⟨r₁, r₂, h₁, h₂, rfl⟩ := (in_rsum _ _ _).1 hr
  exact .inr ⟨(a, b ♯ c), .head _, le_trans (glb_le1 _ _) (pad_bound a b r₁ h₁).1,
    nadd_le_nadd (pad_bound a b r₁ h₁).2 (pad_bound a c r₂ h₂).2⟩

include Q_eq Q_dec Q_zero Q_nadd in
/-- Rocq: `NaturalProduct.nmul_nrep_lower_Q`. -/
theorem nmul_nrep_lower_Q (x y : Ordinal.{u}) (hx : QH Q x) (hy : QH Q y) :
    ∀ k : Nat, nrep k (nmul x y) ≤ nmul (nrep k x) y
  | 0 => zero_least _
  | k + 1 =>
    le_trans (nadd_le_nadd (nmul_nrep_lower_Q x y hx hy k) (le_refl _))
      (le_trans (nadd_le_nadd (nmul_comm _ _).le (nmul_comm _ _).le)
        (le_trans (nmul_distrib_lower_Q Q Q_eq Q_dec Q_zero y (nrep k x) x hy
          (QH_nrep Q Q_zero Q_nadd x hx k) hx) (nmul_comm _ _).le))

/-! Subdistributivity on the universe: `covers_rk`, with the split needed only
at points of the universe. -/

/-- Rocq: `NaturalProduct.covers_Q`. -/
def CoversQ (T : Ordinal.{u}) (Sp : Ordinal.{u} → Bool → Ordinal.{u} → Prop) (D R₁ R₂ : Region.{u}) :
    Prop :=
  ∀ u v, Sem D u v → Q v → v < T ∧ ∀ s p, Sp v s p → Sem (side s R₁ R₂) u p

include Q_eq Q_dec in
/-- Rocq: `NaturalProduct.covers_rk_Q`. -/
theorem covers_rk_Q (T : Ordinal.{u}) (Sp : Ordinal.{u} → Bool → Ordinal.{u} → Prop)
    (Sp_total : ∀ v, Q v → v < T → ∃ s p, Sp v s p)
    (Sp_mono : ∀ v w s p q, Q v → Q w → Sp v s p → Sp w s q → v < w → p < q) :
    ∀ D R₁ R₂ : Region.{u}, QR Q D → CoversQ Q T Sp D R₁ R₂ → rk D ≤ rk R₁ ♯ rk R₂ := by
  suffices H : ∀ (o : Ordinal.{u}) (D R₁ R₂ : Region.{u}), rk D ≤ o → QR Q D →
      CoversQ Q T Sp D R₁ R₂ → rk D ≤ rk R₁ ♯ rk R₂ from fun D R₁ R₂ => H _ D R₁ R₂ (le_refl _)
  intro o
  induction o using ltRec with
  | ind o iho =>
    intro D R₁ R₂ ho hQD hcov
    refine le_intro fun a => ?_
    obtain ⟨m, hm⟩ := rk_lt_elim D _ (index_lt (rk D) a)
    obtain ⟨hp₁, hp₂⟩ := QR_move Q D m hQD
    obtain ⟨hT, hside⟩ := hcov _ _ (sem_move D m) hp₂.1
    obtain ⟨s, π, hπ⟩ := Sp_total _ hp₂.1 hT
    have hrk : rk (cut (mvpt D m) D) < o := lt_of_lt_of_le (rk_move_lt D m) ho
    have hQc := QR_cut Q Q_eq Q_dec _ D hp₁ hp₂ hQD
    refine lt_of_le_of_lt hm ?_
    cases s with
    | true =>
      obtain ⟨m', hq₁, hq₂⟩ := sem_to_move R₁ _ _ (hside true π hπ)
      refine lt_of_le_of_lt (iho _ hrk _ (cut (mvpt R₁ m') R₁) R₂ (le_refl _) hQc fun u v huv hQv => ?_)
        (nadd_increasing1 _ (rk_move_lt R₁ m'))
      obtain ⟨hD, hor⟩ := sem_cut_elim _ D u v huv
      obtain ⟨hTv, hsidev⟩ := hcov u v hD hQv
      refine ⟨hTv, fun s' p' hs' => ?_⟩
      have hsem := hsidev s' p' hs'
      cases s' with
      | false => exact hsem
      | true =>
        refine sem_cut_intro _ R₁ u p' hsem ?_
        match hor with
        | .inl hu => exact .inl (lt_of_lt_of_le hu hq₁)
        | .inr hv => exact .inr (lt_of_lt_of_le (Sp_mono v _ true p' π hQv hp₂.1 hs' hπ hv) hq₂)
    | false =>
      obtain ⟨m', hq₁, hq₂⟩ := sem_to_move R₂ _ _ (hside false π hπ)
      refine lt_of_le_of_lt (iho _ hrk _ R₁ (cut (mvpt R₂ m') R₂) (le_refl _) hQc fun u v huv hQv => ?_)
        (nadd_increasing2 _ (rk_move_lt R₂ m'))
      obtain ⟨hD, hor⟩ := sem_cut_elim _ D u v huv
      obtain ⟨hTv, hsidev⟩ := hcov u v hD hQv
      refine ⟨hTv, fun s' p' hs' => ?_⟩
      have hsem := hsidev s' p' hs'
      cases s' with
      | true => exact hsem
      | false =>
        refine sem_cut_intro _ R₂ u p' hsem ?_
        match hor with
        | .inl hu => exact .inl (lt_of_lt_of_le hu hq₁)
        | .inr hv => exact .inr (lt_of_lt_of_le (Sp_mono v _ false p' π hQv hp₂.1 hs' hπ hv) hq₂)

end decidable_universe

/-! ## Toward a constructive split

### A split on all ordinals is not constructive

`covers_rk` needs only a split of `b ♯ c`; the excluded middle enters only
through `nadd_split`. But a split in exactly the form of `nadd_split`, total on
every ordinal below `b ♯ c` with a boolean side, already implies the weak
excluded middle. Take `b = c = 1`: all positions are below 1, so two comparable
heights never share a side, and the side of the height `e` (which is 0, or 1 if
`P`) decides `¬P ∨ ¬¬P`. So any constructive version must weaken the
interface, e.g. require totality only on heights that actually occur as
moves. -/

/-- Rocq: `NaturalProduct.split_spec`. -/
def SplitSpec (b c : Ordinal.{u}) (Sp : Ordinal.{u} → Bool → Ordinal.{u} → Prop) : Prop :=
  (∀ v, v < b ♯ c → ∃ s p, Sp v s p) ∧
  (∀ v p, Sp v true p → p < b) ∧
  (∀ v p, Sp v false p → p < c) ∧
  (∀ v w s p q, Sp v s p → Sp w s q → v < w → p < q)

private theorem bool_cases (a b c : Bool) (h : b ≠ c) : a = b ∨ a = c := by
  cases a <;> cases b <;> cases c <;> first | exact .inl rfl | exact .inr rfl | exact (h rfl).elim

/-- Rocq: `NaturalProduct.split_WEM`. -/
theorem split_WEM (H : ∀ b c : Ordinal.{u}, ∃ Sp, SplitSpec b c Sp) : WeakExcludedMiddle :=
  fun P => by
  obtain ⟨Sp, Htot, Hb, Hc, Hm⟩ := H 1 1
  have H12 : (1 : Ordinal.{u}) < 1 ♯ 1 :=
    lt_of_le_of_lt (nadd_zero_r 1).ge (nadd_increasing2 1 (succ_lt 0))
  have Hpos : ∀ v s p, Sp v s p → p ≤ 0 := fun v s p h => below_one p (by
    cases s with
    | true => exact Hb v p h
    | false => exact Hc v p h)
  have Hsame : ∀ v w s p q, Sp v s p → Sp w s q → v < w → False := fun v w s p q hv hw hvw =>
    zero_lt p (lt_of_lt_of_le (Hm v w s p q hv hw hvw) (Hpos w s q hw))
  let e : Ordinal.{u} := mk (ULift (PLift P)) fun _ => 0
  have He : e ≤ 1 := le_intro fun _ => succ_lt 0
  obtain ⟨s0, p0, H0⟩ := Htot 0 (lt_of_le_of_lt (zero_least 1) H12)
  obtain ⟨s1, p1, H1⟩ := Htot 1 H12
  obtain ⟨se, pe, He'⟩ := Htot e (lt_of_le_of_lt He H12)
  have H01 : s0 ≠ s1 := fun heq => Hsame 0 1 s0 p0 p1 H0 (heq ▸ H1) (succ_lt 0)
  rcases bool_cases se s0 s1 H01 with h | h
  · -- same side as 0: `P` is refuted
    exact .inr fun hp => Hsame 0 e s0 p0 pe H0 (h ▸ He')
      (lt_intro (show e.Carrier from ⟨⟨hp⟩⟩) (le_refl 0))
  · -- the side of 1: `¬P` is refuted
    refine .inl fun hnp => ?_
    have he0 : e < 1 := lt_of_le_of_lt (le_intro fun ⟨⟨hp⟩⟩ => (hnp hp).elim) (succ_lt 0)
    exact Hsame e 1 s1 pe p1 (h ▸ He') H1 he0

/-! ### The general row lemma implies the excluded middle

`rk_row_lower` places a row of width `w` over an arbitrary region `D` covering
`w × b`. In that generality its statement already implies the excluded middle.
Take `w = 1 ⊔ sup_P ω` (ω if `P`, 1 otherwise), `d = 1 + w`, and `D = d × 1`.
The natural-sum child `1 ♯ w` of `rk D ♯ w` must be reached by some move:
- a top-row move into a `P`-indexed child of `w` proves `P`;
- the top-row move into the child 0 of `w`, or any move inside `D`, reaches
  only `d` or a finite rank, which refutes `P`.

So a constructive proof of the successor law cannot go through the row lemma
for arbitrary `D`; at most it can use it for full rectangles. -/

/-- Rocq: `NaturalProduct.rk_row_upper`. -/
theorem rk_row_upper (w b : Ordinal.{u}) (D : Region.{u}) (hw : Rsub [(w, b)] D)
    (hh : ∀ r, r ∈ D → r.2 ≤ b) : rk ((w, succ b) :: D) ≤ rk D ♯ w :=
  le_trans (grank_row_upper _ D w b hw hh) (nadd_le_nadd (grank_le_rk _ D) (le_refl w))

/-- Rocq: `NaturalProduct.nat_nadd`. -/
theorem nat_nadd (n : Nat) : ∀ m : Nat, ofNat.{u} n ♯ ofNat m ≈ ofNat (n + m)
  | 0 => nadd_zero_r _
  | m + 1 => equiv_trans (nadd_succ2 _ _) (succ_congruence (nat_nadd n m))

/-- Rocq: `NaturalProduct.below_omega_double`. -/
theorem below_omega_double (x : Ordinal.{u}) (h : x < ω) : x ♯ x < ω := by
  obtain ⟨⟨n⟩, hn⟩ := lt_elim h
  exact lt_of_le_of_lt (le_trans (nadd_le_nadd hn hn) (nat_nadd n n).le) (index_lt ω ⟨n + n⟩)

private theorem rsub_empty {r : Ordinal.{u} × Ordinal.{u}} {E : Region.{u}} (h : r.2 ≤ 0) :
    Rsub [r] E := fun r₀ hr₀ => by
  cases hr₀ with
  | head => exact .inl (.inr h)
  | tail _ h' => nomatch h'

private theorem single_heights (x y : Ordinal.{u}) : ∀ r, r ∈ [(x, y)] → r.2 ≤ y := fun _ hr => by
  cases hr with
  | head => exact le_refl _
  | tail _ h => nomatch h

/-- Rocq: `NaturalProduct.row_lower_EM`. -/
theorem row_lower_EM
    (RL : ∀ (w : Ordinal.{u}) (D : Region.{u}) (b : Ordinal.{u}), Rsub [(w, b)] D →
      (∀ r, r ∈ D → r.2 ≤ b) → rk D ♯ w ≤ rk ((w, succ b) :: D)) :
    ExcludedMiddle := fun P => by
  let s : Ordinal.{u} := sup fun _ : ULift (PLift P) => ω
  let w : Ordinal.{u} := 1 ⊔ s
  let d : Ordinal.{u} := 1 + w
  have Hs : s ≤ ω := sup_least fun _ => le_refl ω
  have Hw1 : 1 ≤ w := lub_le1 _ _
  have Hwω : w ≤ ω := lub_least (le_of_lt omega_gt1) Hs
  have Hdω : d ≤ ω := le_trans (add_le_add (le_refl 1) Hwω)
    (additively_closed_collapse additively_closed_omega omega_gt1)
  have Hd1 : 1 < d := lt_of_le_of_lt (add_zero 1).ge
    (add_lt_add_left 1 (lt_of_lt_of_le (succ_lt 0) Hw1))
  have Hwd : w ≤ d := le_add_left 1 w
  -- under `P`, `1 ♯ w` exceeds ω
  have Hbig : P → ω < 1 ♯ w := fun p =>
    lt_of_lt_of_le (lt_of_le_of_lt (nadd_zero_r ω).ge (nadd_increasing2 ω (succ_lt 0)))
      (le_trans (nadd_comm ω 1).le
        (nadd_le_nadd (le_refl 1) (le_trans (sup_le (fun _ : ULift (PLift P) => ω) ⟨⟨p⟩⟩) (lub_le2 1 s))))
  let D : Region.{u} := [(d, 1)]
  have HrkD : rk D ≈ d := equiv_trans (equiv_symm (nmul_rk d 1)) (nmul_one d)
  have Hz : 1 ♯ w < rk ((w, succ 1) :: D) :=
    lt_of_lt_of_le (lt_of_lt_of_le (nadd_increasing1 w Hd1) (nadd_le_nadd HrkD.ge (le_refl w)))
      (RL w D 1 (rsub_in (.head _) ⟨Hwd, le_refl 1⟩) (single_heights d 1))
  obtain ⟨m, Hm⟩ := rk_lt_elim _ _ Hz
  rcases m with ⟨c, t⟩ | ⟨k, t⟩ | m
  · -- a top-row move to width `w c`
    have hs : Rsub [(w ⊓ w c, succ 1), (w, succ 1 ⊓ 1), (d ⊓ w c, 1), (d, 1 ⊓ 1)]
        ((w c, succ 1) :: D) :=
      rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
        (rsub_cons (rsub_in (.tail _ (.head _)) ⟨Hwd, glb_le2 _ _⟩) (rsub_cons_r (cut_sub (w c, 1) D)))
    have Hup : 1 ♯ w ≤ d ♯ w c :=
      le_trans Hm (le_trans (rk_mono hs)
        (le_trans (rk_row_upper (w c) 1 D (rsub_in (.head _) ⟨le_trans (index_le w c) Hwd, le_refl 1⟩)
          (single_heights d 1)) (nadd_le_nadd HrkD.le (le_refl _))))
    rcases c with u | ⟨⟨⟨p⟩⟩, _⟩
    · -- the child 0 of `w`: refutes `P`
      exact .inr fun p => lt_irrefl ω (lt_of_lt_of_le (Hbig p)
        (le_trans Hup (le_trans (nadd_zero_r d).le Hdω)))
    · -- a `P`-indexed child
      exact .inl p
  · -- a move inside `D`: everything left is finite
    refine .inr fun p => ?_
    let dk := d k
    have hs : Rsub [(w ⊓ dk, succ 1), (w, succ 1 ⊓ 0), (d ⊓ dk, 1), (d, 1 ⊓ 0)] [(dk, succ 1)] :=
      rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
        (rsub_cons (rsub_empty (glb_le2 _ _))
          (rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_of_lt (succ_lt 1)⟩)
            (rsub_cons (rsub_empty (glb_le2 _ _)) (rsub_nil _))))
    have Hup : 1 ♯ w ≤ dk ♯ dk :=
      le_trans Hm (le_trans (rk_mono hs) (le_trans (nmul_rk dk (succ 1)).ge
        (le_trans (nmul_succ_upper dk 1) (nadd_le_nadd (nmul_one dk).le (le_refl dk)))))
    have Hdk : dk < ω := lt_of_lt_of_le (index_lt d k) Hdω
    exact lt_irrefl ω (lt_of_lt_of_le (Hbig p) (le_trans Hup (le_of_lt (below_omega_double dk Hdk))))
  · exact (m : PEmpty).elim

/-! ### The successor law implies the weak excluded middle

Found by a search in a two-world Kripke model (`P` undecided, then true). Let
`c₁` have, if `P`, the child ω (so it is 0, or ω+1 if `P`), let
`c₂ = succ e` (1, or 2 if `P`), and let `a` have exactly the two children `c₁`
and `c₂`. These children are not directed: which of them is larger depends on
`P`. In `a ♯ a ≤ a ⊗ 2`, the natural-sum child `c₁ ♯ a` must be matched by a
top-row move into `c₁` or `c₂`:
- into `c₂` reaches at most `a ♯ c₂`, which refutes `P`;
- into `c₁`: then `c₁ ♯ c₂` must be matched by a move inside `c₁ × 2` (which
  needs a proof of `P`), at `(c₁, 0)` (reaching `c₁ ♯ c₁`, which refutes
  `¬P`), or at `(c₂, 0)` (reaching `c₂ ♯ (c₁ ⊓ c₂)`, which refutes `P`).

So the lower half of the successor law, for all ordinals, is not
constructive. Completeness does not rescue it either; see
`succ_lower_complete_WEM` below. -/

/-- Rocq: `NaturalProduct.rk_one`. -/
theorem rk_one (x : Ordinal.{u}) : rk [(x, 1)] ≈ x :=
  equiv_trans (equiv_symm (nmul_rk x 1)) (nmul_one x)

/-- Rocq: `NaturalProduct.rk_two`. -/
theorem rk_two (x : Ordinal.{u}) : rk [(x, succ 1)] ≤ x ♯ x :=
  le_trans (nmul_rk x (succ 1)).ge
    (le_trans (nmul_succ_upper x 1) (nadd_le_nadd (nmul_one x).le (le_refl x)))

/-- Rocq: `NaturalProduct.succ_one_glb_child`. -/
theorem succ_one_glb_child (y : (succ 1 ⊓ 1 : Ordinal.{u}).Carrier) :
    (succ 1 ⊓ 1 : Ordinal.{u}) y ≤ 0 :=
  glb_le2 0 1

/-- Rocq: `NaturalProduct.succ_lower_WEM`. -/
theorem succ_lower_WEM (SL : ∀ a b : Ordinal.{u}, nmul a b ♯ a ≤ nmul a (succ b)) :
    WeakExcludedMiddle := fun P => by
  let c1 : Ordinal.{u} := mk (ULift (PLift P)) fun _ => ω
  let e : Ordinal.{u} := mk (ULift (PLift P)) fun _ => 0
  let c2 : Ordinal.{u} := succ e
  let a : Ordinal.{u} := mk (ULift Bool) fun b => cond b.down c1 c2
  have Hc1P : P → ω < c1 := fun p => lt_intro (show c1.Carrier from ⟨⟨p⟩⟩) (le_refl ω)
  have Hc1nP : ¬P → c1 ≤ 0 := fun np => le_intro fun ⟨⟨p⟩⟩ => (np p).elim
  have Hc2small : c2 < ω :=
    lt_of_le_of_lt (succ_monotone (le_intro fun _ => succ_lt 0 : e ≤ 1)) (index_lt ω ⟨2⟩)
  have Hc2pos : 0 < c2 := succ_trans (zero_least e)
  have Hc1a : c1 < a := index_lt a ⟨true⟩
  have Hc2a : c2 < a := index_lt a ⟨false⟩
  -- `c₁ ≤ c₂` refutes `P`; `c₂ ≤ c₁` refutes `¬P`
  have HnotP : c1 ≤ c2 → ¬P := fun h p =>
    lt_irrefl ω (lt_trans (lt_of_lt_of_le (Hc1P p) h) Hc2small)
  have HnotnotP : c2 ≤ c1 → ¬¬P := fun h np =>
    lt_irrefl 0 (lt_of_lt_of_le Hc2pos (le_trans h (Hc1nP np)))
  have HA : a ♯ a ≤ rk [(a, succ 1)] :=
    le_trans (nadd_le_nadd (nmul_one a).ge (le_refl a)) (le_trans (SL a 1) (nmul_rk a (succ 1)).le)
  have Hz1 : c1 ♯ a < rk [(a, succ 1)] := lt_of_lt_of_le (nadd_increasing1 a Hc1a) HA
  obtain ⟨m, Hm⟩ := rk_lt_elim _ _ Hz1
  rcases m with ⟨⟨x⟩, t⟩ | m
  · cases x with
    | false =>
      -- top-row answer into `c₂`: reaches only `a ♯ c₂`
      refine .inr (HnotP (nadd_cancel_le (z := a) ?_))
      have hs : Rsub [(a ⊓ c2, succ 1), (a, succ 1 ⊓ 1)] ((c2, succ 1) :: [(a, 1)]) :=
        rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
          (rsub_cons (rsub_in (.tail _ (.head _)) ⟨le_refl _, glb_le2 _ _⟩) (rsub_nil _))
      exact le_trans Hm (le_trans (rk_mono hs)
        (le_trans (rk_row_upper c2 1 [(a, 1)] (rsub_in (.head _) ⟨le_of_lt Hc2a, le_refl 1⟩)
            (single_heights a 1))
          (le_trans (nadd_le_nadd (rk_one a).le (le_refl c2)) (nadd_comm a c2).le)))
    | true =>
      -- top-row answer into `c₁`
      let R1 : Region.{u} := [(a ⊓ c1, succ 1), (a, succ 1 ⊓ 1)]
      have Hz2 : c1 ♯ c2 < rk R1 := lt_of_lt_of_le (nadd_increasing2 c1 Hc2a) Hm
      obtain ⟨m2, Hm2⟩ := rk_lt_elim R1 _ Hz2
      rcases m2 with ⟨⟨_, ⟨p⟩⟩, _⟩ | ⟨⟨x2⟩, y2⟩ | m2
      · -- a move inside `c₁ × 2` carries a proof of `P`
        exact .inl fun np => np p.down
      · let v := (succ 1 ⊓ 1 : Ordinal.{u}) y2
        have Hv : v ≤ 0 := succ_one_glb_child y2
        cases x2 with
        | true =>
          -- at `(c₁, 0)`: reaches only `c₁ ♯ c₁`
          refine .inl (HnotnotP (nadd_cancel_le (z := c1) ?_))
          have hs : Rsub [((a ⊓ c1) ⊓ c1, succ 1), (a ⊓ c1, succ 1 ⊓ v), (a ⊓ c1, succ 1 ⊓ 1),
              (a, (succ 1 ⊓ 1) ⊓ v)] [(c1, succ 1)] :=
            rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
              (rsub_cons (rsub_empty (le_trans (glb_le2 _ _) Hv))
                (rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, glb_le1 _ _⟩)
                  (rsub_cons (rsub_empty (le_trans (glb_le2 _ _) Hv)) (rsub_nil _))))
          exact le_trans (nadd_comm c2 c1).le (le_trans Hm2 (le_trans (rk_mono hs) (rk_two c1)))
        | false =>
          -- at `(c₂, 0)`: reaches only `c₂ ♯ (c₁ ⊓ c₂)`
          refine .inr (HnotP (le_trans (nadd_cancel_le (z := c2) ?_) (glb_le2 c2 c1)))
          have hs : Rsub [((a ⊓ c1) ⊓ c2, succ 1), (a ⊓ c1, succ 1 ⊓ v), (a ⊓ c2, succ 1 ⊓ 1),
              (a, (succ 1 ⊓ 1) ⊓ v)] ((c1 ⊓ c2, succ 1) :: [(c2, 1)]) :=
            rsub_cons (rsub_in (.head _)
                ⟨glb_greatest _ _ _ (le_trans (glb_le1 _ _) (glb_le2 _ _)) (glb_le2 _ _), le_refl _⟩)
              (rsub_cons (rsub_empty (le_trans (glb_le2 _ _) Hv))
                (rsub_cons (rsub_in (.tail _ (.head _)) ⟨glb_le2 _ _, glb_le2 _ _⟩)
                  (rsub_cons (rsub_empty (le_trans (glb_le2 _ _) Hv)) (rsub_nil _))))
          exact le_trans Hm2 (le_trans (rk_mono hs)
            (le_trans (rk_row_upper (c1 ⊓ c2) 1 [(c2, 1)] (rsub_in (.head _) ⟨glb_le2 _ _, le_refl 1⟩)
                (single_heights c2 1))
              (le_trans (nadd_le_nadd (rk_one c2).le (le_refl _)) (nadd_comm _ _).le)))
      · exact (m2 : PEmpty).elim
  · exact (m : PEmpty).elim

/-! ### Completeness does not help

The witness above has non-directed children. This one is complete: let `c n`
have the children `n` and, if `P`, `ω` (so `c n` is `n+1`, or `ω+1` if `P`),
and let `a` be the limit of the increasing sequence `c 0, c 1, …`. The `c n`
are directed, and so is `a`. In `a ♯ a ≤ a ⊗ 2`, the opponent plays three
moves:
- `c 0 ♯ a`, answered by a top-row move into some `c n`;
- `c 0 ♯ c (n+1)`, from the column just beyond that answer. The answer either
  shrinks the top row to `n` (reaching only `a ♯ n`, which refutes `P`) or
  plays at `(c j, 0)` in the bottom row, which also cuts the top row, leaving
  `c n × 2 ∪ c j × 1`;
- `c 0 ♯ (n+1)`. The answer must now shrink the top row to `n` (reaching
  `c 0 ♯ n` under `P`, one move short) or the bottom row to `j` (reaching a
  finite rank, which refutes `P`).

Each answer is either a move into a `P`-indexed child, proving `P`, or refutes
`P`. The opponent wins because the answer's column must be chosen before the
opponent's: a strategy for the successor law has to commit to one column of
the top row, while the matching natural-sum move can use any column. -/

/-- Rocq: `NaturalProduct.succ_lower_complete_WEM`. -/
theorem succ_lower_complete_WEM
    (SL : ∀ a b : Ordinal.{u}, Complete a → Complete b → nmul a b ♯ a ≤ nmul a (succ b)) :
    WeakExcludedMiddle := fun P => by
  let c : Nat → Ordinal.{u} := fun n =>
    mk (ULift.{u} (Option (PLift P))) fun o => o.down.elim (ofNat n) fun _ => ω
  let a : Ordinal.{u} := mk (ULift Nat) fun n => c n.down
  have Hca : ∀ n, c n < a := fun n => index_lt a ⟨n⟩
  have Hnc : ∀ n, ofNat n < c n := fun n => index_lt (c n) ⟨none⟩
  have HcP : P → ∀ i j, c i ≤ c j := fun p i j => le_intro fun ⟨o⟩ => by
    cases o with
    | some q => exact index_lt (c j) ⟨some q⟩
    | none => exact lt_trans (index_lt ω ⟨i⟩) (index_lt (c j) ⟨some ⟨p⟩⟩)
  have HwP : P → ∀ i, ω < c i := fun p i => index_lt (c i) ⟨some ⟨p⟩⟩
  have Hmono : ∀ i j, i ≤ j → c i ≤ c j := fun i j hij => le_intro fun ⟨o⟩ => by
    cases o with
    | some q => exact index_lt (c j) ⟨some q⟩
    | none => exact lt_of_le_of_lt (ofNat_monotone hij) (Hnc j)
  have Hcomp : Complete a := by
    refine Complete.intro ?_ (.inl ⟨⟨0⟩⟩) ?_
    · rintro ⟨i⟩ ⟨j⟩
      exact ⟨⟨Nat.max i j⟩, Hmono _ _ (Nat.le_max_left _ _), Hmono _ _ (Nat.le_max_right _ _)⟩
    · rintro ⟨n⟩
      show Complete (c n)
      refine Complete.intro ?_ (.inl ⟨⟨none⟩⟩) ?_
      · rintro ⟨o₁⟩ ⟨o₂⟩
        cases o₁ with
        | some p =>
          cases o₂ with
          | some _ => exact ⟨⟨some p⟩, le_refl _, le_refl _⟩
          | none => exact ⟨⟨some p⟩, le_refl _, le_of_lt (index_lt ω ⟨n⟩)⟩
        | none =>
          cases o₂ with
          | some q => exact ⟨⟨some q⟩, le_of_lt (index_lt ω ⟨n⟩), le_refl _⟩
          | none => exact ⟨⟨none⟩, le_refl _, le_refl _⟩
      · rintro ⟨o⟩
        cases o with
        | some _ => exact omega_complete
        | none => exact ofNat_complete n
  have HA : a ♯ a ≤ rk [(a, succ 1)] :=
    le_trans (nadd_le_nadd (nmul_one a).ge (le_refl a))
      (le_trans (SL a 1 Hcomp (succ_complete zero_complete)) (nmul_rk a (succ 1)).le)
  -- finite ranks refute `P`
  have HfinP : ∀ x, x < ω → c 0 ≤ x → ¬P := fun x hx h p =>
    lt_irrefl ω (lt_trans (lt_of_lt_of_le (HwP p 0) h) hx)
  -- the opponent plays `c 0` in the first copy of `a`
  have Hz1 : c 0 ♯ a < rk [(a, succ 1)] := lt_of_lt_of_le (nadd_increasing1 a (Hca 0)) HA
  obtain ⟨n, Hm⟩ : ∃ n, c 0 ♯ a ≤ rk (cut (c n, 1) [(a, succ 1)]) := by
    obtain ⟨m, Hm⟩ := rk_lt_elim _ _ Hz1
    rcases m with ⟨⟨n⟩, _⟩ | m
    · exact ⟨n, Hm⟩
    · exact (m : PEmpty).elim
  let R1 : Region.{u} := [(c n, succ 1), (a, 1)]
  have HR1 : rk (cut (c n, 1) [(a, succ 1)]) ≤ rk R1 :=
    rk_mono (rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
      (rsub_cons (rsub_in (.tail _ (.head _)) ⟨le_refl _, glb_le2 _ _⟩) (rsub_nil _)))
  -- then `c (n+1)` in the second copy, beyond the answer's column
  have Hz2 : c 0 ♯ c (n + 1) < rk R1 :=
    lt_of_lt_of_le (nadd_increasing2 (c 0) (Hca (n + 1))) (le_trans Hm HR1)
  obtain ⟨m2, Hm2⟩ := rk_lt_elim R1 _ Hz2
  rcases m2 with ⟨⟨o⟩, _⟩ | ⟨⟨j⟩, _⟩ | m2
  · cases o with
    | some p =>
      -- a move into a `P`-indexed child proves `P`
      exact .inl fun np => np p.down
    | none =>
      -- the top row shrinks to `n`: reaches only `a ♯ n`
      refine .inr fun p => ?_
      have hs : Rsub [(c n ⊓ ofNat n, succ 1), (c n, succ 1 ⊓ 1), (a ⊓ ofNat n, 1), (a, 1 ⊓ 1)]
          ((ofNat n, succ 1) :: [(a, 1)]) :=
        rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
          (rsub_cons (rsub_in (.tail _ (.head _)) ⟨le_of_lt (Hca n), glb_le2 _ _⟩)
            (rsub_cons (rsub_in (.tail _ (.head _)) ⟨glb_le1 _ _, le_refl _⟩)
              (rsub_cons (rsub_in (.tail _ (.head _)) ⟨le_refl _, glb_le1 _ _⟩) (rsub_nil _))))
      have H : c 0 ♯ c (n + 1) ≤ a ♯ ofNat n :=
        le_trans Hm2 (le_trans (rk_mono hs)
          (le_trans (rk_row_upper (ofNat n) 1 [(a, 1)]
              (rsub_in (.head _) ⟨le_of_lt (lt_trans (Hnc n) (Hca n)), le_refl 1⟩)
              (single_heights a 1))
            (nadd_le_nadd (rk_one a).le (le_refl _))))
      -- under `P`, `a ≤ c (n+1) + 1`, so `c 0 ≤ n + 1 < ω`
      have Ha : a ≤ succ (c (n + 1)) := le_intro fun ⟨i⟩ =>
        lt_of_le_of_lt (HcP p i (n + 1)) (succ_lt _)
      refine HfinP (ofNat (n + 1)) (index_lt ω ⟨n + 1⟩) (nadd_cancel_le (z := c (n + 1)) ?_) p
      exact le_trans H (le_trans (nadd_le_nadd Ha (le_refl _))
        (le_trans (nadd_succ _ _).le (le_trans (succ_monotone (nadd_comm _ _).le) (nadd_succ _ _).ge)))
  · -- an answer at `(c j, 0)` in the bottom row cuts the top row too
    let R2 : Region.{u} := [(c n, succ 1), (c j, 1)]
    have HR2 : rk [(c n ⊓ c j, succ 1), (c n, succ 1 ⊓ 0), (a ⊓ c j, 1), (a, 1 ⊓ 0)] ≤ rk R2 :=
      rk_mono (rsub_cons (rsub_in (.head _) ⟨glb_le1 _ _, le_refl _⟩)
        (rsub_cons (rsub_empty (glb_le2 _ _))
          (rsub_cons (rsub_in (.tail _ (.head _)) ⟨glb_le2 _ _, le_refl _⟩)
            (rsub_cons (rsub_empty (glb_le2 _ _)) (rsub_nil _)))))
    -- the opponent descends to `n+1` inside `c (n+1)`
    have Hz3 : c 0 ♯ ofNat (n + 1) < rk R2 :=
      lt_of_lt_of_le (nadd_increasing2 (c 0) (Hnc (n + 1))) (le_trans Hm2 HR2)
    obtain ⟨m3, Hm3⟩ := rk_lt_elim R2 _ Hz3
    rcases m3 with ⟨⟨o⟩, _⟩ | ⟨⟨o⟩, _⟩ | m3
    · cases o with
      | some p => exact .inl fun np => np p.down
      | none =>
        -- top row to `n`: reaches only `c 0 ♯ n`, under `P`
        refine .inr fun p => lt_irrefl (ofNat n) (lt_of_lt_of_le (succ_lt _)
          (nadd_cancel_le (z := c 0) ?_))
        have hs : Rsub [(c n ⊓ ofNat n, succ 1), (c n, succ 1 ⊓ 1), (c j ⊓ ofNat n, 1), (c j, 1 ⊓ 1)]
            ((ofNat n, succ 1) :: [(c 0, 1)]) :=
          rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
            (rsub_cons (rsub_in (.tail _ (.head _)) ⟨HcP p n 0, glb_le2 _ _⟩)
              (rsub_cons (rsub_in (.tail _ (.head _)) ⟨le_trans (glb_le1 _ _) (HcP p j 0), le_refl _⟩)
                (rsub_cons (rsub_in (.tail _ (.head _)) ⟨HcP p j 0, glb_le1 _ _⟩) (rsub_nil _))))
        exact le_trans (nadd_comm _ _).le (le_trans Hm3 (le_trans (rk_mono hs)
          (le_trans (rk_row_upper (ofNat n) 1 [(c 0, 1)]
              (rsub_in (.head _) ⟨le_of_lt (lt_of_lt_of_le (Hnc n) (HcP p n 0)), le_refl 1⟩)
              (single_heights (c 0) 1))
            (le_trans (nadd_le_nadd (rk_one _).le (le_refl _)) (nadd_comm _ _).le))))
    · cases o with
      | some p => exact .inl fun np => np p.down
      | none =>
        -- bottom row to `j`: everything left is finite
        have hs : Rsub [(c n ⊓ ofNat j, succ 1), (c n, succ 1 ⊓ 0), (c j ⊓ ofNat j, 1), (c j, 1 ⊓ 0)]
            [(ofNat j, succ 1)] :=
          rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
            (rsub_cons (rsub_empty (glb_le2 _ _))
              (rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_of_lt (succ_lt 1)⟩)
                (rsub_cons (rsub_empty (glb_le2 _ _)) (rsub_nil _))))
        exact .inr (HfinP (ofNat j ♯ ofNat j) (below_omega_double _ (index_lt ω ⟨j⟩))
          (le_trans (nadd_le1 (c 0) (ofNat (n + 1)))
            (le_trans Hm3 (le_trans (rk_mono hs) (rk_two _)))))
    · exact (m3 : PEmpty).elim
  · exact (m2 : PEmpty).elim

/-- Superdistributivity contains the successor law (take `c = 1`).
Rocq: `NaturalProduct.distrib_lower_WEM`. -/
theorem distrib_lower_WEM
    (H : ∀ a b c : Ordinal.{u}, nmul a b ♯ nmul a c ≤ nmul a (b ♯ c)) : WeakExcludedMiddle :=
  succ_lower_WEM fun a b => le_trans (nadd_le_nadd (le_refl _) (nmul_one a).ge)
    (le_trans (H a b 1) (nmul_monotone (le_refl a)
      (le_trans (nadd_succ2 b 0).le (succ_monotone (nadd_zero_r b).le))))

/-- Rocq: `NaturalProduct.distrib_lower_complete_WEM`. -/
theorem distrib_lower_complete_WEM
    (H : ∀ a b c : Ordinal.{u}, Complete a → Complete b → Complete c →
      nmul a b ♯ nmul a c ≤ nmul a (b ♯ c)) : WeakExcludedMiddle :=
  succ_lower_complete_WEM fun a b ha hb => le_trans (nadd_le_nadd (le_refl _) (nmul_one a).ge)
    (le_trans (H a b 1 ha hb (succ_complete zero_complete)) (nmul_monotone (le_refl a)
      (le_trans (nadd_succ2 b 0).le (succ_monotone (nadd_zero_r b).le))))

end ConstructiveOrdinals.NaturalProduct
