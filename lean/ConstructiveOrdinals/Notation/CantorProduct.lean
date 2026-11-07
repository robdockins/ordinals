import ConstructiveOrdinals.NaturalProduct
import ConstructiveOrdinals.Notation.Interpolants
import ConstructiveOrdinals.Notation.CantorDecomposition

/-!
# The natural product on Cantor normal forms

Port of `Ordinal/Notation/CantorProduct.v`.

The semantic natural product `NaturalProduct.nmul` satisfies distributivity
and the successor law only classically; their lower halves imply the weak
excluded middle, even for complete ordinals. Here we compute instead. For a
notation system with a Cantor decomposition, the standard algorithm multiplies
normal forms term by term: the product of `ω^α₁ + ⋯ + ω^αₘ` and
`ω^β₁ + ⋯ + ω^βₙ` is the sorted list of all `ω^(αᵢ ♯ βⱼ)`.

- The algorithm denotes the natural sum of the pairwise terms
  (`cantor_nmul_correct`), constructively.
- On notations, it satisfies the usual laws constructively: commutativity,
  associativity, distributivity over the natural sum, unit and zero, the
  exponent law and the successor law. These rest on the uniqueness of Cantor
  normal forms (`cantor_nadd_unique`), which the decidable comparison of
  notations makes constructive.
- Given interpolants, it reflects `nmul` constructively
  (`cantor_nmul_reflects`), so the semantic product does satisfy all these
  laws on notations. Interpolants are needed only at epsilon notations
  (`cantor_nmul_reflects_epsilons`). With the excluded middle, interpolants
  are not needed (`cantor_nmul_reflects_EM`).

The constructive reflection works because, on trees whose children are
hereditarily notations, every comparison that the classical proofs decide
with the excluded middle is a comparison of notations (`NaturalProduct`,
section `decidable_universe`); interpolants make the denoted trees equivalent
to such trees.

We write `V xs` for the natural sum of the ω-powers of a list of exponents.

Lean notes:
- Rocq's `Permutation` is core `List.Perm`; the few facts needed about it are
  proved here, to keep them axiom-free.
- Rocq's local abbreviations `V` and `prod_equiv` are the abbreviations `V`
  and `ProdEquiv`.
- `V_cnf_assoc` is proved on values rather than through `Forall2`, with the
  helpers `V_list_map_app`, `V_map_assoc` and `V_cnf_map_l`.
- The canonical tree `Trec` recurses on an accessibility proof, as
  `Interpolants.HasInterpolantsRec` does.
-/

namespace ConstructiveOrdinals.CantorProduct

open Ordinal NaturalProduct CantorDecomposition Interpolants

universe u v

/-- The natural sum of the ω-powers of a list of exponents. Rocq's local
abbreviation `V` for `NaturalArith.cantor_denote_nadd`. -/
abbrev V (xs : List Ordinal.{u}) : Ordinal.{u} := Ordinal.cantorDenoteNadd xs

/-! ## Permutations -/

private theorem perm_refl {α : Type u} : ∀ l : List α, l.Perm l
  | [] => .nil
  | x :: l => .cons x (perm_refl l)

private theorem perm_middle {α : Type u} (a : α) : ∀ l₁ l₂ : List α,
    (a :: (l₁ ++ l₂)).Perm (l₁ ++ a :: l₂)
  | [], _ => perm_refl _
  | b :: l₁, l₂ => .trans (.swap b a _) (.cons b (perm_middle a l₁ l₂))

private theorem perm_map {α : Type u} {β : Type v} (g : α → β) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (l₁.map g).Perm (l₂.map g) := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons _ ih
  | swap x y l => exact .swap _ _ _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-! ## The algebra of pairwise products of exponent lists -/

/-- Rocq: `Notation.CantorProduct.nadd_middle_swap`. -/
theorem nadd_middle_swap (p q r s : Ordinal.{u}) : (p ♯ q) ♯ (r ♯ s) ≈ (p ♯ r) ♯ (q ♯ s) :=
  equiv_trans (equiv_symm (nadd_assoc _ _ _))
    (equiv_trans (nadd_congr (equiv_refl p) (nadd_left_comm q r s)) (nadd_assoc _ _ _))

/-- Rocq: `Notation.CantorProduct.V_app`. -/
theorem V_app (xs ys : List Ordinal.{u}) : V (xs ++ ys) ≈ V xs ♯ V ys :=
  cantor_denote_nadd_app xs ys

/-- Rocq: `Notation.CantorProduct.V_perm`. -/
theorem V_perm (xs ys : List Ordinal.{u}) (h : xs.Perm ys) : V xs ≈ V ys := by
  induction h with
  | nil => exact equiv_refl _
  | cons x _ ih => exact nadd_congr (equiv_refl _) ih
  | swap x y l => exact nadd_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact equiv_trans ih₁ ih₂

/-- Rocq: `Notation.CantorProduct.V_eq2`. -/
theorem V_eq2 (xs ys : List Ordinal.{u}) (h : Forall₂ (· ≈ ·) xs ys) : V xs ≈ V ys := by
  induction h with
  | nil => exact equiv_refl _
  | cons hxy _ ih => exact nadd_congr (pow_congr (equiv_refl ω) hxy) ih

/-- Rocq: `Notation.CantorProduct.Forall2_map_eq`. -/
theorem Forall2_map_eq (g h : Ordinal.{u} → Ordinal.{u}) (H : ∀ z, g z ≈ h z) :
    ∀ zs : List Ordinal.{u}, Forall₂ (· ≈ ·) (zs.map g) (zs.map h)
  | [] => .nil
  | z :: zs => .cons (H z) (Forall2_map_eq g h H zs)

/-- Rocq: `Notation.CantorProduct.V_cnf_nil_r`. -/
theorem V_cnf_nil_r : ∀ xs : List Ordinal.{u}, V (cnfProd xs []) ≈ 0
  | [] => equiv_refl _
  | _ :: xs => V_cnf_nil_r xs

/-- Rocq: `Notation.CantorProduct.V_cnf_cons_l`. -/
theorem V_cnf_cons_l (a : Ordinal.{u}) (xs ys : List Ordinal.{u}) :
    V (cnfProd (a :: xs) ys) ≈ V (ys.map fun b => a ♯ b) ♯ V (cnfProd xs ys) :=
  V_app _ _

/-- Rocq: `Notation.CantorProduct.V_cnf_cons_r`. -/
theorem V_cnf_cons_r : ∀ (xs : List Ordinal.{u}) (b : Ordinal.{u}) (ys : List Ordinal.{u}),
    V (cnfProd xs (b :: ys)) ≈ V (xs.map fun a => a ♯ b) ♯ V (cnfProd xs ys)
  | [], _, _ => equiv_symm (nadd_zero_l 0)
  | a :: xs, b, ys =>
    equiv_trans (V_cnf_cons_l a xs (b :: ys))
      (equiv_trans (nadd_congr (equiv_refl _) (V_cnf_cons_r xs b ys))
        (equiv_trans (nadd_middle_swap _ _ _ _) (nadd_congr (equiv_refl _) (equiv_symm (V_app _ _)))))

/-- Rocq: `Notation.CantorProduct.V_cnf_comm`. -/
theorem V_cnf_comm : ∀ xs ys : List Ordinal.{u}, V (cnfProd xs ys) ≈ V (cnfProd ys xs)
  | [], ys => equiv_symm (V_cnf_nil_r ys)
  | a :: xs, ys =>
    equiv_trans (V_cnf_cons_l a xs ys)
      (equiv_trans (nadd_congr (V_eq2 _ _ (Forall2_map_eq _ _ (fun z => nadd_comm a z) ys))
          (V_cnf_comm xs ys))
        (equiv_symm (V_cnf_cons_r ys a xs)))

/-- Rocq: `Notation.CantorProduct.V_cnf_app_r`. -/
theorem V_cnf_app_r (xs : List Ordinal.{u}) : ∀ ys zs : List Ordinal.{u},
    V (cnfProd xs (ys ++ zs)) ≈ V (cnfProd xs ys) ♯ V (cnfProd xs zs)
  | [], _ => equiv_symm (equiv_trans (nadd_congr (V_cnf_nil_r xs) (equiv_refl _)) (nadd_zero_l _))
  | b :: ys, zs =>
    equiv_trans (V_cnf_cons_r xs b (ys ++ zs))
      (equiv_trans (nadd_congr (equiv_refl _) (V_cnf_app_r xs ys zs))
        (equiv_trans (nadd_assoc _ _ _) (nadd_congr (equiv_symm (V_cnf_cons_r xs b ys)) (equiv_refl _))))

/-- Rocq: `Notation.CantorProduct.V_cnf_app_l`. -/
theorem V_cnf_app_l (xs ys zs : List Ordinal.{u}) :
    V (cnfProd (xs ++ ys) zs) ≈ V (cnfProd xs zs) ♯ V (cnfProd ys zs) :=
  equiv_trans (V_cnf_comm _ zs) (equiv_trans (V_cnf_app_r zs xs ys)
    (nadd_congr (V_cnf_comm zs xs) (V_cnf_comm zs ys)))

/-- Two exponent lists are interchangeable in products. Rocq's local
abbreviation `prod_equiv`. -/
abbrev ProdEquiv (L₁ L₂ : List Ordinal.{u}) : Prop :=
  ∀ ws : List Ordinal.{u}, V (cnfProd ws L₁) ≈ V (cnfProd ws L₂)

/-- Rocq: `Notation.CantorProduct.prod_equiv_refl`. -/
theorem prod_equiv_refl (L : List Ordinal.{u}) : ProdEquiv L L := fun _ => equiv_refl _

/-- Rocq: `Notation.CantorProduct.prod_equiv_sym`. -/
theorem prod_equiv_sym (L₁ L₂ : List Ordinal.{u}) (h : ProdEquiv L₁ L₂) : ProdEquiv L₂ L₁ :=
  fun ws => equiv_symm (h ws)

/-- Rocq: `Notation.CantorProduct.prod_equiv_trans`. -/
theorem prod_equiv_trans (L₁ L₂ L₃ : List Ordinal.{u}) (h₁ : ProdEquiv L₁ L₂)
    (h₂ : ProdEquiv L₂ L₃) : ProdEquiv L₁ L₃ :=
  fun ws => equiv_trans (h₁ ws) (h₂ ws)

/-- Rocq: `Notation.CantorProduct.prod_equiv_eq2`. -/
theorem prod_equiv_eq2 (L₁ L₂ : List Ordinal.{u}) (h : Forall₂ (· ≈ ·) L₁ L₂) :
    ProdEquiv L₁ L₂ := by
  induction h with
  | nil => exact fun _ => equiv_refl _
  | @cons x xs y ys hxy _ ih =>
    exact fun ws => equiv_trans (V_cnf_cons_r ws x xs)
      (equiv_trans (nadd_congr (V_eq2 _ _ (Forall2_map_eq _ _ (fun a => nadd_congr (equiv_refl a) hxy) ws))
        (ih ws)) (equiv_symm (V_cnf_cons_r ws y ys)))

/-- Rocq: `Notation.CantorProduct.prod_equiv_perm`. -/
theorem prod_equiv_perm (L₁ L₂ : List Ordinal.{u}) (h : L₁.Perm L₂) : ProdEquiv L₁ L₂ := by
  induction h with
  | nil => exact fun _ => equiv_refl _
  | @cons x l₁ l₂ _ ih =>
    exact fun ws => equiv_trans (V_cnf_cons_r ws x l₁)
      (equiv_trans (nadd_congr (equiv_refl _) (ih ws)) (equiv_symm (V_cnf_cons_r ws x l₂)))
  | swap x y l =>
    exact fun ws => equiv_trans (V_cnf_cons_r ws y (x :: l))
      (equiv_trans (nadd_congr (equiv_refl _) (V_cnf_cons_r ws x l))
        (equiv_trans (nadd_left_comm _ _ _) (equiv_symm (equiv_trans (V_cnf_cons_r ws x (y :: l))
          (nadd_congr (equiv_refl _) (V_cnf_cons_r ws y l))))))
  | trans _ _ ih₁ ih₂ => exact fun ws => equiv_trans (ih₁ ws) (ih₂ ws)

/-- Rocq: `Notation.CantorProduct.prod_equiv_l`. -/
theorem prod_equiv_l (L₁ L₂ ws : List Ordinal.{u}) (h : ProdEquiv L₁ L₂) :
    V (cnfProd L₁ ws) ≈ V (cnfProd L₂ ws) :=
  equiv_trans (V_cnf_comm _ ws) (equiv_trans (h ws) (V_cnf_comm ws _))

private theorem V_zero_map : ∀ L : List Ordinal.{u}, V (L.map fun b => 0 ♯ b) ≈ V L
  | [] => equiv_refl _
  | x :: L => nadd_congr (pow_congr (equiv_refl ω) (nadd_zero_l x)) (V_zero_map L)

/-- Rocq: `Notation.CantorProduct.prod_equiv_V`. -/
theorem prod_equiv_V (L₁ L₂ : List Ordinal.{u}) (h : ProdEquiv L₁ L₂) : V L₁ ≈ V L₂ :=
  have h0 : ∀ L : List Ordinal.{u}, V (cnfProd [0] L) ≈ V L := fun L =>
    equiv_trans (V_app _ _) (equiv_trans (nadd_zero_r _) (V_zero_map L))
  equiv_trans (equiv_symm (h0 L₁)) (equiv_trans (h [0]) (h0 L₂))

/-- Rocq: `Notation.CantorProduct.cnf_prod_single`. -/
theorem cnf_prod_single (a b : Ordinal.{u}) : V (cnfProd [a] [b]) ≈ ω ^ (a ♯ b) :=
  nadd_zero_r _

private theorem V_list_map_app (g : Ordinal.{u} → Ordinal.{u}) : ∀ l₁ l₂ : List Ordinal.{u},
    V ((l₁ ++ l₂).map g) ≈ V (l₁.map g) ♯ V (l₂.map g)
  | [], _ => equiv_symm (nadd_zero_l _)
  | _ :: l₁, l₂ => equiv_trans (nadd_congr (equiv_refl _) (V_list_map_app g l₁ l₂)) (nadd_assoc _ _ _)

private theorem V_map_assoc (a b : Ordinal.{u}) : ∀ zs : List Ordinal.{u},
    V (zs.map fun c => (a ♯ b) ♯ c) ≈ V ((zs.map fun c => b ♯ c).map fun c => a ♯ c)
  | [] => equiv_refl _
  | z :: zs => nadd_congr (pow_congr (equiv_refl ω) (equiv_symm (nadd_assoc a b z))) (V_map_assoc a b zs)

private theorem V_cnf_map_l (a : Ordinal.{u}) : ∀ ys zs : List Ordinal.{u},
    V (cnfProd (ys.map fun b => a ♯ b) zs) ≈ V ((cnfProd ys zs).map fun c => a ♯ c)
  | [], _ => equiv_refl _
  | b :: ys, zs =>
    equiv_trans (V_cnf_cons_l _ _ zs)
      (equiv_trans (nadd_congr (V_map_assoc a b zs) (V_cnf_map_l a ys zs)) (equiv_symm (V_list_map_app _ _ _)))

/-- Rocq: `Notation.CantorProduct.V_cnf_assoc`. -/
theorem V_cnf_assoc : ∀ xs ys zs : List Ordinal.{u},
    V (cnfProd (cnfProd xs ys) zs) ≈ V (cnfProd xs (cnfProd ys zs))
  | [], _, _ => equiv_refl _
  | a :: xs, ys, zs =>
    equiv_trans (V_cnf_app_l _ _ zs)
      (equiv_trans (nadd_congr (V_cnf_map_l a ys zs) (V_cnf_assoc xs ys zs))
        (equiv_symm (V_cnf_cons_l a xs (cnfProd ys zs))))

/-! ## Uniqueness of Cantor normal forms, and the algorithm -/

private theorem list_map_app {α : Type u} {β : Type v} (g : α → β) : ∀ l₁ l₂ : List α,
    (l₁ ++ l₂).map g = l₁.map g ++ l₂.map g
  | [], _ => rfl
  | x :: l₁, l₂ => congrArg (g x :: ·) (list_map_app g l₁ l₂)

private theorem forall2_app {α β : Type u} {R : α → β → Prop} {a c : List α} {b d : List β}
    (h₁ : Forall₂ R a b) (h₂ : Forall₂ R c d) : Forall₂ R (a ++ c) (b ++ d) := by
  induction h₁ with
  | nil => exact h₂
  | cons hxy _ ih => exact .cons hxy ih

section cantor_product

variable {A : Type} {f : A → Ordinal.{0}} {P : A → Prop} (X : HasCantorDecomposition f P)

include X in
/-- Rocq: `Notation.CantorProduct.V_map_complete`. -/
theorem V_map_complete : ∀ a, Complete (f a) := X.complete

/-- Rocq: `Notation.CantorProduct.ordered_head_le`. -/
theorem ordered_head_le (f : A → Ordinal.{0}) : ∀ (xs : List A) (x : A),
    CantorOrdered f (x :: xs) → ∀ z, z ∈ x :: xs → f z ≤ f x
  | [], _, _, _, .head _ => le_refl _
  | [], _, _, _, .tail _ h => nomatch h
  | _ :: _, _, _, _, .head _ => le_refl _
  | _ :: ys, _, ⟨hxy, hord⟩, z, .tail _ h => le_trans (ordered_head_le f ys _ hord z h) hxy

/-- Rocq: `Notation.CantorProduct.V_below_power`. -/
theorem V_below_power (f : A → Ordinal.{0}) : ∀ (xs : List A) (e d : Ordinal.{0}),
    (∀ z, z ∈ xs → f z ≤ e) → e < d → Complete d → V (xs.map f) < ω ^ d
  | [], _, d, _, _, _ => pow_pos ω d
  | x :: xs, e, d, hxs, hed, hd =>
    nadd_closed_con d _ _ hd (pow_lt_pow_right omega_gt1 (lt_of_le_of_lt (hxs x (.head _)) hed))
      (V_below_power f xs e d (fun z h => hxs z (.tail _ h)) hed hd)

include X in
/-- Two normal forms with the same value agree term by term. The comparison
of the leading exponents is decided by the notation system; a strictly smaller
leading exponent bounds the whole sum below the other's leading power, by
closure under natural sum. Rocq: `Notation.CantorProduct.cantor_nadd_unique`. -/
theorem cantor_nadd_unique : ∀ xs ys : List A, Each P xs → Each P ys →
    CantorOrdered f xs → CantorOrdered f ys → V (xs.map f) ≈ V (ys.map f) →
    Forall₂ (· ≈ ·) (xs.map f) (ys.map f)
  | [], [], _, _, _, _, _ => .nil
  | [], y :: _, _, _, _, _, heq =>
    (lt_irrefl 0 (lt_of_lt_of_le (pow_pos ω (f y)) (le_trans (nadd_le1 _ _) heq.ge))).elim
  | x :: _, [], _, _, _, _, heq =>
    (lt_irrefl 0 (lt_of_lt_of_le (pow_pos ω (f x)) (le_trans (nadd_le1 _ _) heq.le))).elim
  | x :: xs, y :: ys, ⟨hx, hxs⟩, ⟨hy, hys⟩, hox, hoy, heq => by
    have Hlt : ∀ u us v vs, CantorOrdered f (u :: us) → f u < f v →
        ¬ V ((u :: us).map f) ≈ V ((v :: vs).map f) := fun u us v _ hou huv h =>
      lt_irrefl (ω ^ f v) (lt_of_le_of_lt (le_trans (nadd_le1 _ _) h.ge)
        (V_below_power f (u :: us) (f u) (f v) (ordered_head_le f us u hou) huv (X.complete v)))
    have hc := X.compare_correct x y hx hy
    revert hc
    cases X.compare x y with
    | lt => exact fun hc => (Hlt x xs y ys hox hc heq).elim
    | gt => exact fun hc => (Hlt y ys x xs hoy hc (equiv_symm heq)).elim
    | eq =>
      intro hc
      have heq' : ω ^ f y ♯ V (xs.map f) ≈ ω ^ f y ♯ V (ys.map f) :=
        equiv_trans (nadd_congr (pow_congr (equiv_refl ω) (equiv_symm hc)) (equiv_refl _)) heq
      exact .cons hc (cantor_nadd_unique xs ys hxs hys hox.2 hoy.2 (equiv_intro
        (nadd_cancel_le (z := ω ^ f y) (le_trans (nadd_comm _ _).le (le_trans heq'.le (nadd_comm _ _).le)))
        (nadd_cancel_le (z := ω ^ f y) (le_trans (nadd_comm _ _).le (le_trans heq'.ge (nadd_comm _ _).le)))))

include X in
/-- Rocq: `Notation.CantorProduct.denote_V`. -/
theorem denote_V (l : List A) (h₁ : Each P l) (h₂ : CantorOrdered f l) :
    CantorDecomposition.cantorDenote f l ≈ V (l.map f) := by
  have h := cantor_denote_nadd_eq X l h₁ h₂
  rw [CantorDecomposition.cantor_denote_nadd_map] at h
  exact h

/-- Rocq: `Notation.CantorProduct.dec_value`. -/
theorem dec_value (x : A) (hx : P x) : f x ≈ V ((X.decompose x).map f) :=
  let ⟨h₁, h₂, h₃⟩ := X.decompose_correct x hx
  equiv_trans h₃ (denote_V X _ h₁ h₂)

/-- Rocq: `Notation.CantorProduct.dec_equiv`. -/
theorem dec_equiv (x : A) (L : List A) (hx : P x) (hL : Each P L) (hoL : CantorOrdered f L)
    (H : f x ≈ V (L.map f)) : ProdEquiv ((X.decompose x).map f) (L.map f) :=
  let ⟨h₁, h₂, _⟩ := X.decompose_correct x hx
  prod_equiv_eq2 _ _ (cantor_nadd_unique X _ _ h₁ hL h₂ hoL (equiv_trans (equiv_symm (dec_value X x hx)) H))

private theorem naddInner_perm (x : A) (xs : List A)
    (ih : ∀ ys, (cantorNaddList X xs ys).Perm (xs ++ ys)) :
    ∀ ys, (cantorNaddInner X x xs (cantorNaddList X xs) ys).Perm (x :: xs ++ ys)
  | [] => by
    show (x :: xs).Perm (x :: (xs ++ []))
    rw [List.append_nil]
  | y :: ys => by
    show (match X.compare x y with
      | .lt => y :: cantorNaddInner X x xs (cantorNaddList X xs) ys
      | .eq => x :: cantorNaddList X xs (y :: ys)
      | .gt => x :: cantorNaddList X xs (y :: ys)).Perm (x :: xs ++ y :: ys)
    cases X.compare x y with
    | lt => exact .trans (.cons y (naddInner_perm x xs ih ys)) (perm_middle y (x :: xs) ys)
    | eq => exact .cons x (ih (y :: ys))
    | gt => exact .cons x (ih (y :: ys))

/-- Rocq: `Notation.CantorProduct.nadd_list_perm`. -/
theorem nadd_list_perm : ∀ xs ys : List A, (cantorNaddList X xs ys).Perm (xs ++ ys)
  | [], ys => perm_refl ys
  | x :: xs, ys => naddInner_perm X x xs (nadd_list_perm xs) ys

/-- Insertion sort by repeated merging. Rocq: `Notation.CantorProduct.cantor_sort`. -/
def cantorSort (l : List A) : List A :=
  l.foldr (fun e acc => cantorNaddList X [e] acc) []

/-- Rocq: `Notation.CantorProduct.cantor_sort_correct`. -/
theorem cantor_sort_correct : ∀ l : List A, Each P l →
    Each P (cantorSort X l) ∧ CantorOrdered f (cantorSort X l) ∧ (cantorSort X l).Perm l
  | [], _ => ⟨trivial, trivial, .nil⟩
  | e :: l, ⟨he, hl⟩ =>
    let ⟨h₁, h₂, h₃⟩ := cantor_sort_correct l hl
    let ⟨h₄, h₅, _⟩ := cantor_nadd_list_correct X [e] (cantorSort X l) ⟨he, trivial⟩ h₁
      ⟨trivial, trivial⟩ h₂
    ⟨h₄, h₅, .trans (nadd_list_perm X [e] _) (.cons e h₃)⟩

/-- All pairwise natural sums. Rocq: `Notation.CantorProduct.cantor_pairs` (a
`flat_map`; here the same list by recursion). -/
def cantorPairs : List A → List A → List A
  | [], _ => []
  | x :: xs, ys => ys.map (fun y => cantorNadd X x y) ++ cantorPairs xs ys

private theorem pairs_row (x : A) (hx : P x) : ∀ ys : List A, Each P ys →
    Each P (ys.map fun y => cantorNadd X x y) ∧
      Forall₂ (· ≈ ·) ((ys.map fun y => cantorNadd X x y).map f) ((ys.map f).map fun b => f x ♯ b)
  | [], _ => ⟨trivial, .nil⟩
  | y :: ys, ⟨hy, hys⟩ =>
    let ⟨c₁, c₂⟩ := cantor_nadd_correct X x y hx hy
    let ⟨r₁, r₂⟩ := pairs_row x hx ys hys
    ⟨⟨c₁, r₁⟩, .cons c₂ r₂⟩

/-- Rocq: `Notation.CantorProduct.cantor_pairs_correct`. -/
theorem cantor_pairs_correct : ∀ xs ys : List A, Each P xs → Each P ys →
    Each P (cantorPairs X xs ys) ∧
      Forall₂ (· ≈ ·) ((cantorPairs X xs ys).map f) (cnfProd (xs.map f) (ys.map f))
  | [], _, _, _ => ⟨trivial, .nil⟩
  | x :: xs, ys, ⟨hx, hxs⟩, hys => by
    obtain ⟨h₁, h₂⟩ := cantor_pairs_correct xs ys hxs hys
    obtain ⟨r₁, r₂⟩ := pairs_row X x hx ys hys
    refine ⟨(CantorDecomposition.each_app P _ _).2 ⟨r₁, h₁⟩, ?_⟩
    show Forall₂ _ ((ys.map (fun y => cantorNadd X x y) ++ cantorPairs X xs ys).map f) _
    rw [list_map_app]
    exact forall2_app r₂ h₂

/-- The natural product of notations. Rocq: `Notation.CantorProduct.cantor_nmul`. -/
def cantorNmul (x y : A) : A :=
  X.recompose (cantorSort X (cantorPairs X (X.decompose x) (X.decompose y)))

/-- Rocq: `Notation.CantorProduct.cantor_nmul_terms`. -/
theorem cantor_nmul_terms (x y : A) (hx : P x) (hy : P y) :
    ∃ L, Each P L ∧ CantorOrdered f L ∧ P (cantorNmul X x y) ∧ f (cantorNmul X x y) ≈ V (L.map f) ∧
      ProdEquiv (L.map f) (cnfProd ((X.decompose x).map f) ((X.decompose y).map f)) := by
  obtain ⟨hx₁, _, _⟩ := X.decompose_correct x hx
  obtain ⟨hy₁, _, _⟩ := X.decompose_correct y hy
  obtain ⟨hp₁, hp₂⟩ := cantor_pairs_correct X _ _ hx₁ hy₁
  obtain ⟨hs₁, hs₂, hs₃⟩ := cantor_sort_correct X _ hp₁
  obtain ⟨hr₁, hr₂⟩ := X.recompose_correct _ hs₁ hs₂
  exact ⟨_, hs₁, hs₂, hr₁, equiv_trans (equiv_symm hr₂) (denote_V X _ hs₁ hs₂),
    prod_equiv_trans _ _ _ (prod_equiv_perm _ _ (perm_map f hs₃)) (prod_equiv_eq2 _ _ hp₂)⟩

/-- The algorithm computes the natural sum of the pairwise terms.
Rocq: `Notation.CantorProduct.cantor_nmul_correct`. -/
theorem cantor_nmul_correct (x y : A) (hx : P x) (hy : P y) :
    P (cantorNmul X x y) ∧
      f (cantorNmul X x y) ≈ V (cnfProd ((X.decompose x).map f) ((X.decompose y).map f)) :=
  let ⟨_, _, _, h₃, h₄, h₅⟩ := cantor_nmul_terms X x y hx hy
  ⟨h₃, equiv_trans h₄ (prod_equiv_V _ _ h₅)⟩

/-- Rocq: `Notation.CantorProduct.cantor_nmul_dec`. -/
theorem cantor_nmul_dec (x y : A) (hx : P x) (hy : P y) :
    ProdEquiv ((X.decompose (cantorNmul X x y)).map f)
      (cnfProd ((X.decompose x).map f) ((X.decompose y).map f)) :=
  let ⟨L, h₁, h₂, h₃, h₄, h₅⟩ := cantor_nmul_terms X x y hx hy
  prod_equiv_trans _ _ _ (dec_equiv X _ L h₃ h₁ h₂ h₄) h₅

/-- Rocq: `Notation.CantorProduct.dec_proper`. -/
theorem dec_proper (x y : A) (hx : P x) (hy : P y) (h : f x ≈ f y) :
    ProdEquiv ((X.decompose x).map f) ((X.decompose y).map f) :=
  let ⟨hy₁, hy₂, _⟩ := X.decompose_correct y hy
  dec_equiv X x _ hx hy₁ hy₂ (equiv_trans h (dec_value X y hy))

/-! ## The laws, constructively -/

/-- Rocq: `Notation.CantorProduct.cantor_nmul_proper`. -/
theorem cantor_nmul_proper (x x' y y' : A) (hx : P x) (hx' : P x') (hy : P y) (hy' : P y')
    (hxx : f x ≈ f x') (hyy : f y ≈ f y') : f (cantorNmul X x y) ≈ f (cantorNmul X x' y') :=
  equiv_trans (cantor_nmul_correct X x y hx hy).2
    (equiv_trans (equiv_trans (dec_proper X y y' hy hy' hyy _)
        (prod_equiv_l _ _ _ (dec_proper X x x' hx hx' hxx)))
      (equiv_symm (cantor_nmul_correct X x' y' hx' hy').2))

/-- Rocq: `Notation.CantorProduct.cantor_nmul_comm`. -/
theorem cantor_nmul_comm (x y : A) (hx : P x) (hy : P y) :
    f (cantorNmul X x y) ≈ f (cantorNmul X y x) :=
  equiv_trans (cantor_nmul_correct X x y hx hy).2
    (equiv_trans (V_cnf_comm _ _) (equiv_symm (cantor_nmul_correct X y x hy hx).2))

/-- Rocq: `Notation.CantorProduct.cantor_nmul_assoc`. -/
theorem cantor_nmul_assoc (x y z : A) (hx : P x) (hy : P y) (hz : P z) :
    f (cantorNmul X (cantorNmul X x y) z) ≈ f (cantorNmul X x (cantorNmul X y z)) :=
  let hxy := (cantor_nmul_correct X x y hx hy).1
  let hyz := (cantor_nmul_correct X y z hy hz).1
  equiv_trans (cantor_nmul_correct X _ z hxy hz).2
    (equiv_trans (prod_equiv_l _ _ _ (cantor_nmul_dec X x y hx hy))
      (equiv_trans (V_cnf_assoc _ _ _)
        (equiv_trans (equiv_symm (cantor_nmul_dec X y z hy hz _))
          (equiv_symm (cantor_nmul_correct X x _ hx hyz).2))))

/-- Rocq: `Notation.CantorProduct.cantor_nmul_nadd_r`. -/
theorem cantor_nmul_nadd_r (x y z : A) (hx : P x) (hy : P y) (hz : P z) :
    f (cantorNmul X x (cantorNadd X y z)) ≈
      f (cantorNadd X (cantorNmul X x y) (cantorNmul X x z)) := by
  obtain ⟨Hyz, Hyz'⟩ := cantor_nadd_correct X y z hy hz
  obtain ⟨Hxy, Hxy'⟩ := cantor_nmul_correct X x y hx hy
  obtain ⟨Hxz, Hxz'⟩ := cantor_nmul_correct X x z hx hz
  obtain ⟨hy₁, hy₂, _⟩ := X.decompose_correct y hy
  obtain ⟨hz₁, hz₂, _⟩ := X.decompose_correct z hz
  obtain ⟨hm₁, hm₂, hm₃⟩ := cantor_nadd_list_correct X _ _ hy₁ hz₁ hy₂ hz₂
  rw [CantorDecomposition.cantor_denote_nadd_map, CantorDecomposition.cantor_denote_nadd_map,
    CantorDecomposition.cantor_denote_nadd_map] at hm₃
  have hdec : f (cantorNadd X y z) ≈ V ((cantorNaddList X (X.decompose y) (X.decompose z)).map f) :=
    equiv_trans Hyz' (equiv_trans (nadd_congr (dec_value X y hy) (dec_value X z hz)) (equiv_symm hm₃))
  have hperm := prod_equiv_perm _ _ (perm_map f (nadd_list_perm X (X.decompose y) (X.decompose z)))
    ((X.decompose x).map f)
  rw [list_map_app] at hperm
  exact equiv_trans (cantor_nmul_correct X x _ hx Hyz).2
    (equiv_trans (dec_equiv X _ _ Hyz hm₁ hm₂ hdec _)
      (equiv_trans hperm (equiv_trans (V_cnf_app_r _ _ _)
        (equiv_trans (nadd_congr (equiv_symm Hxy') (equiv_symm Hxz'))
          (equiv_symm (cantor_nadd_correct X _ _ Hxy Hxz).2)))))

/-- Rocq: `Notation.CantorProduct.cantor_nmul_nadd_l`. -/
theorem cantor_nmul_nadd_l (x y z : A) (hx : P x) (hy : P y) (hz : P z) :
    f (cantorNmul X (cantorNadd X x y) z) ≈
      f (cantorNadd X (cantorNmul X x z) (cantorNmul X y z)) :=
  let hxy := (cantor_nadd_correct X x y hx hy).1
  let hxz := (cantor_nmul_correct X x z hx hz).1
  let hyz := (cantor_nmul_correct X y z hy hz).1
  let hzx := (cantor_nmul_correct X z x hz hx).1
  let hzy := (cantor_nmul_correct X z y hz hy).1
  equiv_trans (cantor_nmul_comm X _ z hxy hz)
    (equiv_trans (cantor_nmul_nadd_r X z x y hz hx hy)
      (equiv_trans (cantor_nadd_correct X _ _ hzx hzy).2
        (equiv_trans (nadd_congr (cantor_nmul_comm X z x hz hx) (cantor_nmul_comm X z y hz hy))
          (equiv_symm (cantor_nadd_correct X _ _ hxz hyz).2))))

/-- Rocq: `Notation.CantorProduct.cantor_nmul_zero`. -/
theorem cantor_nmul_zero (x : A) (hx : P x) : f (cantorNmul X x (cantorZero X)) ≈ 0 :=
  let ⟨Hz₁, Hz₂⟩ := cantor_zero_reflects X
  equiv_trans (cantor_nmul_correct X x _ hx Hz₂).2
    (equiv_trans (dec_equiv X (cantorZero X) [] Hz₂ trivial trivial (equiv_symm Hz₁) _)
      (V_cnf_nil_r _))

private theorem V_map_zero_r {c : Ordinal.{0}} (hc : c ≈ 0) :
    ∀ L : List Ordinal.{0}, V (L.map fun a => a ♯ c) ≈ V L
  | [] => equiv_refl _
  | x :: L => nadd_congr (pow_congr (equiv_refl ω)
      (equiv_trans (nadd_congr (equiv_refl x) hc) (nadd_zero_r x))) (V_map_zero_r hc L)

/-- Rocq: `Notation.CantorProduct.cantor_nmul_one`. -/
theorem cantor_nmul_one (x : A) (hx : P x) : f (cantorNmul X x (cantorNat X 1)) ≈ f x :=
  let ⟨H₁, H₂⟩ := cantor_nat_correct X 1
  let ⟨Hz₁, Hz₂⟩ := cantor_zero_reflects X
  have hone : f (cantorNat X 1) ≈ V ([cantorZero X].map f) :=
    equiv_trans H₁ (equiv_symm (equiv_trans (nadd_zero_r _)
      (equiv_trans (pow_congr (equiv_refl ω) (equiv_symm Hz₁)) (pow_zero ω))))
  equiv_trans (cantor_nmul_correct X x _ hx H₂).2
    (equiv_trans (dec_equiv X _ [cantorZero X] H₂ ⟨Hz₂, trivial⟩ ⟨trivial, trivial⟩ hone _)
      (equiv_trans (V_cnf_cons_r _ _ _)
        (equiv_trans (nadd_congr (equiv_refl _) (V_cnf_nil_r _))
          (equiv_trans (nadd_zero_r _)
            (equiv_trans (V_map_zero_r (equiv_symm Hz₁) _) (equiv_symm (dec_value X x hx)))))))

private theorem single_value (a : A) (ha : P a) :
    P (X.recompose [a]) ∧ f (X.recompose [a]) ≈ V ([a].map f) :=
  let ⟨h₁, h₂⟩ := X.recompose_correct [a] ⟨ha, trivial⟩ ⟨trivial, trivial⟩
  ⟨h₁, equiv_trans (equiv_symm h₂) (equiv_trans (add_zero _) (equiv_symm (nadd_zero_r _)))⟩

/-- The exponent law, for single powers `ω ^ a`.
Rocq: `Notation.CantorProduct.cantor_nmul_exp`. -/
theorem cantor_nmul_exp (a b : A) (ha : P a) (hb : P b) :
    f (cantorNmul X (X.recompose [a]) (X.recompose [b])) ≈ f (X.recompose [cantorNadd X a b]) :=
  let ⟨Hab, Hab'⟩ := cantor_nadd_correct X a b ha hb
  let ⟨Ha₁, Ha₂⟩ := single_value X a ha
  let ⟨Hb₁, Hb₂⟩ := single_value X b hb
  let ⟨_, Hc₂⟩ := single_value X _ Hab
  equiv_trans (cantor_nmul_correct X _ _ Ha₁ Hb₁).2
    (equiv_trans (prod_equiv_l _ _ _ (dec_equiv X _ [a] Ha₁ ⟨ha, trivial⟩ ⟨trivial, trivial⟩ Ha₂))
      (equiv_trans (dec_equiv X _ [b] Hb₁ ⟨hb, trivial⟩ ⟨trivial, trivial⟩ Hb₂ _)
        (equiv_trans (cnf_prod_single _ _)
          (equiv_trans (pow_congr (equiv_refl ω) (equiv_symm Hab'))
            (equiv_trans (equiv_symm (nadd_zero_r _)) (equiv_symm Hc₂))))))

/-- The successor law: `x ⊗ (y+1) = x ⊗ y ♯ x`.
Rocq: `Notation.CantorProduct.cantor_nmul_succ`. -/
theorem cantor_nmul_succ (x y : A) (hx : P x) (hy : P y) :
    f (cantorNmul X x (cantorSucc X y)) ≈ f (cantorNadd X (cantorNmul X x y) x) :=
  let ⟨Hs₁, Hs₂⟩ := cantor_succ_reflects X (f y) y ⟨equiv_refl _, hy⟩
  let ⟨H₁, H₂⟩ := cantor_nat_correct X 1
  let ⟨Hy₁, Hy₁'⟩ := cantor_nadd_correct X y _ hy H₂
  let Hxy := (cantor_nmul_correct X x y hx hy).1
  let Hx₁ := (cantor_nmul_correct X x _ hx H₂).1
  have hsucc : f (cantorSucc X y) ≈ f (cantorNadd X y (cantorNat X 1)) :=
    equiv_trans (equiv_symm Hs₁) (equiv_symm (equiv_trans Hy₁' (equiv_trans
      (nadd_congr (equiv_refl _) H₁) (equiv_trans (nadd_succ2 _ _) (succ_congruence (nadd_zero_r _))))))
  equiv_trans (cantor_nmul_proper X x x _ _ hx hx Hs₂ Hy₁ (equiv_refl _) hsucc)
    (equiv_trans (cantor_nmul_nadd_r X x y _ hx hy H₂)
      (equiv_trans (cantor_nadd_correct X _ _ Hxy Hx₁).2
        (equiv_trans (nadd_congr (equiv_refl _) (cantor_nmul_one X x hx))
          (equiv_symm (cantor_nadd_correct X _ _ Hxy hx).2))))

/-! ## Reflection of the semantic product, classically -/

include X in
/-- Rocq: `Notation.CantorProduct.cantor_ordered_sequence`. -/
theorem cantor_ordered_sequence : ∀ L : List A, Each P L → CantorOrdered f L →
    ∃ b, CantorSequence b (L.map f)
  | [], _, _ => ⟨0, trivial⟩
  | x :: L, hL, ho => ⟨f x, le_refl _, cantor_sequence_dec_weaken _ _ (cantor_ordered_dec X L x hL ho)⟩

/-- Rocq: `Notation.CantorProduct.cantor_nmul_reflects_EM`. -/
theorem cantor_nmul_reflects_EM (em : ExcludedMiddle) :
    Reflects A f P (.ord ==> .ord ==> .ord) nmul (cantorNmul X) := by
  intro u x ⟨hu, hx⟩ v y ⟨hv, hy⟩
  obtain ⟨H₁, H₂⟩ := cantor_nmul_correct X x y hx hy
  obtain ⟨hx₁, hx₂, hx₃⟩ := X.decompose_correct x hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := X.decompose_correct y hy
  obtain ⟨bx, hbx⟩ := cantor_ordered_sequence X _ hx₁ hx₂
  obtain ⟨b₂, hby⟩ := cantor_ordered_sequence X _ hy₁ hy₂
  rw [CantorDecomposition.cantor_denote_map] at hx₃ hy₃
  exact ⟨equiv_trans (nmul_congr (equiv_trans hu hx₃) (equiv_trans hv hy₃))
    (equiv_trans (nmul_cantor em _ _ bx b₂ hbx hby) (equiv_symm H₂)), H₁⟩

end cantor_product

/-! ## The lower half of the reflection, constructively

Given interpolants, a notation's value is equivalent to the tree `Tn z` whose
children are exactly the notations below it, recursively. On such trees every
corner and every move of the product game is a notation, so the comparisons
in the proof of superdistributivity are decided by the notation system
(`nmul_distrib_lower_Q`). The exponent law's lower bound then follows by
induction, using interpolants to bound children by notations and closure under
natural sum; assembling the pairwise terms gives
`f (cantorNmul X x y) ≤ nmul (f x) (f y)`. -/

/-- Rocq: `Notation.CantorProduct.nadd_lt_elim`. -/
theorem nadd_lt_elim (z x y : Ordinal.{u}) (h : z < x ♯ y) :
    (∃ i, z ≤ x i ♯ y) ∨ (∃ j, z ≤ x ♯ y j) := by
  rw [nadd_unfold] at h
  match lub_lt h with
  | .inl h => obtain ⟨i, hi⟩ := lt_elim h; exact .inl ⟨i, hi⟩
  | .inr h => obtain ⟨j, hj⟩ := lt_elim h; exact .inr ⟨j, hj⟩

/-- The ordinals with a notation. Rocq: `Notation.CantorProduct.Qn`. -/
def Qn {A : Type} (f : A → Ordinal.{0}) (P : A → Prop) (z : Ordinal.{0}) : Prop :=
  ∃ a, P a ∧ z ≈ f a

/-- Hereditarily notations. Rocq: `Notation.CantorProduct.QHn`. -/
abbrev QHn {A : Type} (f : A → Ordinal.{0}) (P : A → Prop) (x : Ordinal.{0}) : Prop :=
  QH (Qn f P) x

/-- The canonical tree of notations below `z`. Rocq: `Notation.CantorProduct.Trec`. -/
noncomputable def Trec {A : Type} (f : A → Ordinal.{0}) (P : A → Prop) {z : Ordinal.{0}}
    (h : Acc (· < ·) z) : Ordinal.{0} :=
  Acc.rec (motive := fun _ _ => Ordinal.{0})
    (fun z _ ih => mk {b : A // P b ∧ f b < z} fun bh => ih (f bh.1) bh.2.2) h

/-- Rocq: `Notation.CantorProduct.Tn`. -/
noncomputable def Tn {A : Type} (f : A → Ordinal.{0}) (P : A → Prop) (z : Ordinal.{0}) : Ordinal.{0} :=
  Trec f P (lt_wf.apply z)

section cantor_product_lower

variable {A : Type} {f : A → Ordinal.{0}} {P : A → Prop} (X : HasCantorDecomposition f P)
  (Hinterp : HasAllInterpolants f P)

/-- Rocq: `Notation.CantorProduct.Qn_eq`. -/
theorem Qn_eq (x y : Ordinal.{0}) (h : x ≈ y) (hx : Qn f P x) : Qn f P y :=
  let ⟨a, ha, hxa⟩ := hx
  ⟨a, ha, equiv_trans (equiv_symm h) hxa⟩

include X in
/-- Rocq: `Notation.CantorProduct.Qn_dec`. -/
theorem Qn_dec (x y : Ordinal.{0}) (hx : Qn f P x) (hy : Qn f P y) : x < y ∨ y ≤ x := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  have hc := X.compare_correct a b ha hb
  revert hc
  cases X.compare a b with
  | lt => exact fun hc => .inl (lt_of_le_of_lt hxa.le (lt_of_lt_of_le hc hyb.ge))
  | eq => exact fun hc => .inr (le_trans hyb.le (le_trans hc.ge hxa.ge))
  | gt => exact fun hc => .inr (le_of_lt (lt_of_le_of_lt hyb.le (lt_of_lt_of_le hc hxa.ge)))

include X in
/-- Rocq: `Notation.CantorProduct.Qn_zero`. -/
theorem Qn_zero : Qn f P 0 :=
  let ⟨h₁, h₂⟩ := cantor_zero_reflects X
  ⟨cantorZero X, h₂, h₁⟩

include X in
/-- Rocq: `Notation.CantorProduct.Qn_nadd`. -/
theorem Qn_nadd (x y : Ordinal.{0}) (hx : Qn f P x) (hy : Qn f P y) : Qn f P (x ♯ y) :=
  let ⟨a, ha, hxa⟩ := hx
  let ⟨b, hb, hyb⟩ := hy
  let ⟨h₁, h₂⟩ := cantor_nadd_correct X a b ha hb
  ⟨cantorNadd X a b, h₁, equiv_trans (nadd_congr hxa hyb) (equiv_symm h₂)⟩

include X in
/-- Rocq: `Notation.CantorProduct.QHn_nadd`. -/
theorem QHn_nadd (x y : Ordinal.{0}) (hx : QHn f P x) (hy : QHn f P y) : QHn f P (x ♯ y) :=
  QH_nadd (Qn f P) (Qn_nadd X) x y hx hy

include X in
/-- Rocq: `Notation.CantorProduct.QHn_zero`. -/
theorem QHn_zero : QHn f P 0 := QH_zero (Qn f P) (Qn_zero X)

/-- Rocq: `Notation.CantorProduct.Trec_le`. -/
theorem Trec_le (z : Ordinal.{0}) (H : Acc (· < ·) z) : Trec f P H ≤ z := by
  induction z using ltRec with
  | ind z ih =>
    cases H with
    | intro _ h =>
      exact le_intro fun (bh : {b : A // P b ∧ f b < z}) =>
        lt_of_le_of_lt (ih _ bh.2.2 (h _ bh.2.2)) bh.2.2

/-- Rocq: `Notation.CantorProduct.Trec_ge`. -/
theorem Trec_ge (z : Ordinal.{0}) (H : Acc (· < ·) z) (hz : HasInterpolants f P z) :
    z ≤ Trec f P H := by
  induction z using ltRec with
  | ind z ih =>
    cases H with
    | intro _ h =>
      refine le_intro fun i => ?_
      obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold z).1 hz (z i) (index_lt z i)
      exact lt_intro (show (Trec f P (Acc.intro z h)).Carrier from ⟨y, hy₁, hy₃⟩)
        (le_trans hy₂ (ih (f y) hy₃ (h _ hy₃) hy₄))

include Hinterp in
/-- Rocq: `Notation.CantorProduct.Trec_eq`. -/
theorem Trec_eq (z : Ordinal.{0}) (H : Acc (· < ·) z) (a : A) (ha : P a) (hz : z ≈ f a) :
    Trec f P H ≈ z :=
  equiv_intro (Trec_le z H) (Trec_ge z H ((has_interpolants_eq_mor hz).2 (Hinterp a ha)))

include Hinterp in
/-- Rocq: `Notation.CantorProduct.Trec_HQ`. -/
theorem Trec_HQ (z : Ordinal.{0}) (H : Acc (· < ·) z) : HQ (Qn f P) (Trec f P H) := by
  induction z using ltRec with
  | ind z ih =>
    cases H with
    | intro _ h =>
      show ∀ bh : {b : A // P b ∧ f b < z}, _
      intro bh
      exact ⟨⟨bh.1, bh.2.1, Trec_eq Hinterp _ _ bh.1 bh.2.1 (equiv_refl _)⟩, ih _ bh.2.2 _⟩

include Hinterp in
/-- Rocq: `Notation.CantorProduct.Tn_QH`. -/
theorem Tn_QH (a : A) (ha : P a) : QHn f P (Tn f P (f a)) :=
  ⟨⟨a, ha, Trec_eq Hinterp _ _ a ha (equiv_refl _)⟩, Trec_HQ Hinterp _ _⟩

include Hinterp in
/-- Rocq: `Notation.CantorProduct.Tn_eq`. -/
theorem Tn_eq (a : A) (ha : P a) : Tn f P (f a) ≈ f a :=
  Trec_eq Hinterp _ _ a ha (equiv_refl _)

/-- The tree of the power `ω ^ a`. Rocq: `Notation.CantorProduct.En`. -/
noncomputable def En (a : A) : Ordinal.{0} := Tn f P (f (X.recompose [a]))

include Hinterp in
/-- Rocq: `Notation.CantorProduct.En_props`. -/
theorem En_props (a : A) (ha : P a) : QHn f P (En X a) ∧ En X a ≈ ω ^ f a :=
  let ⟨h₁, h₂⟩ := X.recompose_correct [a] ⟨ha, trivial⟩ ⟨trivial, trivial⟩
  ⟨Tn_QH Hinterp _ h₁, equiv_trans (Tn_eq Hinterp _ h₁) (equiv_trans (equiv_symm h₂) (add_zero _))⟩

include X in
/-- Rocq: `Notation.CantorProduct.nrep_power_below`. -/
theorem nrep_power_below (k : Nat) (a a' : A) (_ha : P a) (h : f a' < f a) :
    nrep k (ω ^ f a') < ω ^ f a := by
  induction k with
  | zero => exact pow_pos ω _
  | succ k ih =>
    exact nadd_closed_con (f a) _ _ (X.complete a) ih (pow_lt_pow_right omega_gt1 h)

include Hinterp in
/-- Rocq: `Notation.CantorProduct.exp_lower_n`. -/
theorem exp_lower_n (a₀ b₀ : A) (ha₀ : P a₀) (hb₀ : P b₀) :
    ω ^ (f a₀ ♯ f b₀) ≤ nmul (En X a₀) (En X b₀) := by
  suffices H : ∀ o a b, P a → P b → f a ♯ f b ≤ o → ω ^ (f a ♯ f b) ≤ nmul (En X a) (En X b) from
    H _ a₀ b₀ ha₀ hb₀ (le_refl _)
  intro o
  induction o using ltRec with
  | ind o IH =>
  intro a b ha hb ho
  obtain ⟨HEa, HEa'⟩ := En_props X Hinterp a ha
  obtain ⟨HEb, HEb'⟩ := En_props X Hinterp b hb
  have Hnrep := nmul_nrep_lower_Q (Qn f P) Qn_eq (Qn_dec X) (Qn_zero X) (Qn_nadd X)
  rw [pow_unfold]
  refine lub_least ?_ (sup_least fun i => ?_)
  · exact le_trans (nmul_one 1).ge (nmul_monotone (succ_least (lt_of_lt_of_le (pow_pos ω _) HEa'.ge))
      (succ_least (lt_of_lt_of_le (pow_pos ω _) HEb'.ge)))
  rw [mul_unfold]
  refine sup_least fun n => le_trans (mul_succ _ _).ge (le_trans (mul_nat_le_nrep _ (n.down + 1)) ?_)
  generalize n.down + 1 = k
  match nadd_lt_elim _ _ _ (index_lt (f a ♯ f b) i) with
  | .inl ⟨j, hj⟩ =>
    obtain ⟨a₁, Ha₁, Ha₁le, Ha₁lt, _⟩ := (has_interpolants_unfold _).1 (Hinterp a ha) (f a j) (index_lt _ j)
    obtain ⟨HE₁, HE₁eq⟩ := En_props X Hinterp a₁ Ha₁
    have Hlt : f a₁ ♯ f b < o := lt_of_lt_of_le (nadd_increasing1 _ Ha₁lt) ho
    exact le_trans (nrep_mono k (pow_le_pow_right ω (le_trans hj (nadd_le_nadd Ha₁le (le_refl _)))))
      (le_trans (nrep_mono k (IH _ Hlt a₁ b Ha₁ hb (le_refl _)))
        (le_trans (Hnrep _ _ HE₁ HEb k) (nmul_monotone (le_of_lt (lt_of_lt_of_le
          (lt_of_le_of_lt (nrep_mono k HE₁eq.le) (nrep_power_below X k a a₁ ha Ha₁lt)) HEa'.ge))
          (le_refl _))))
  | .inr ⟨j, hj⟩ =>
    obtain ⟨b₁, Hb₁, Hb₁le, Hb₁lt, _⟩ := (has_interpolants_unfold _).1 (Hinterp b hb) (f b j) (index_lt _ j)
    obtain ⟨HE₁, HE₁eq⟩ := En_props X Hinterp b₁ Hb₁
    have Hlt : f a ♯ f b₁ < o := lt_of_lt_of_le (nadd_increasing2 _ Hb₁lt) ho
    exact le_trans (nrep_mono k (pow_le_pow_right ω (le_trans hj (nadd_le_nadd (le_refl _) Hb₁le))))
      (le_trans (nrep_mono k (le_trans (IH _ Hlt a b₁ ha Hb₁ (le_refl _)) (nmul_comm _ _).le))
        (le_trans (Hnrep _ _ HE₁ HEa k) (le_trans (nmul_monotone (le_of_lt (lt_of_lt_of_le
          (lt_of_le_of_lt (nrep_mono k HE₁eq.le) (nrep_power_below X k b b₁ hb Hb₁lt)) HEb'.ge))
          (le_refl _)) (nmul_comm _ _).le)))

/-- Rocq: `Notation.CantorProduct.VE`. -/
noncomputable def VE : List A → Ordinal.{0}
  | [] => 0
  | x :: xs => En X x ♯ VE xs

include Hinterp in
/-- Rocq: `Notation.CantorProduct.VE_props`. -/
theorem VE_props : ∀ xs : List A, Each P xs → QHn f P (VE X xs) ∧ VE X xs ≈ V (xs.map f)
  | [], _ => ⟨QHn_zero X, equiv_refl _⟩
  | x :: xs, ⟨hx, hxs⟩ =>
    let ⟨h₁, h₂⟩ := VE_props xs hxs
    let ⟨h₃, h₄⟩ := En_props X Hinterp x hx
    ⟨QHn_nadd X _ _ h₃ h₁, nadd_congr h₄ h₂⟩

include Hinterp in
private theorem pairs_row_lower (x : A) (hx : P x) : ∀ ys : List A, Each P ys →
    V ((ys.map f).map fun b => f x ♯ b) ≤ nmul (En X x) (VE X ys)
  | [], _ => zero_least _
  | y :: ys, ⟨hy, hys⟩ =>
    le_trans (nadd_le_nadd (exp_lower_n X Hinterp x y hx hy) (pairs_row_lower x hx ys hys))
      (nmul_distrib_lower_Q (Qn f P) Qn_eq (Qn_dec X) (Qn_zero X) _ _ _ (En_props X Hinterp x hx).1
        (En_props X Hinterp y hy).1 (VE_props X Hinterp ys hys).1)

include Hinterp in
/-- Rocq: `Notation.CantorProduct.pairs_lower`. -/
theorem pairs_lower : ∀ xs ys : List A, Each P xs → Each P ys →
    V (cnfProd (xs.map f) (ys.map f)) ≤ nmul (VE X xs) (VE X ys)
  | [], _, _, _ => zero_least _
  | x :: xs, ys, ⟨hx, hxs⟩, hys =>
    le_trans (V_cnf_cons_l _ _ _).le
      (le_trans (nadd_le_nadd (pairs_row_lower X Hinterp x hx ys hys) (pairs_lower xs ys hxs hys))
        (le_trans (nadd_le_nadd (nmul_comm _ _).le (nmul_comm _ _).le)
          (le_trans (nmul_distrib_lower_Q (Qn f P) Qn_eq (Qn_dec X) (Qn_zero X) _ _ _
              (VE_props X Hinterp ys hys).1 (En_props X Hinterp x hx).1 (VE_props X Hinterp xs hxs).1)
            (nmul_comm _ _).le)))

include Hinterp in
/-- The algorithm's value is a lower bound for the semantic product.
Rocq: `Notation.CantorProduct.cantor_nmul_lower`. -/
theorem cantor_nmul_lower (x y : A) (hx : P x) (hy : P y) :
    f (cantorNmul X x y) ≤ nmul (f x) (f y) :=
  let hx₁ := (X.decompose_correct x hx).1
  let hy₁ := (X.decompose_correct y hy).1
  le_trans (cantor_nmul_correct X x y hx hy).2.le
    (le_trans (pairs_lower X Hinterp _ _ hx₁ hy₁)
      (nmul_monotone (le_trans (VE_props X Hinterp _ hx₁).2.le (dec_value X x hx).ge)
        (le_trans (VE_props X Hinterp _ hy₁).2.le (dec_value X y hy).ge)))

end cantor_product_lower


/-! ## The upper half

Subdistributivity over a Cantor normal form `ω^e + c` uses the split of the
chain that sends `v < ω^e` to the left and `ω^e + p` to the right; reading `p`
off the normal form of `v` is where the notation system is needed. The
exponent law's upper bound then follows by subadditivity and closure, by
induction. -/

/-- Rocq: `Notation.CantorProduct.add_cancel_lt_con`. -/
theorem add_cancel_lt_con (x y z : Ordinal.{u}) (h : x + y < x + z) : y < z :=
  match add_lt h with
  | .inl h₁ => (lt_irrefl x (lt_of_le_of_lt (le_add_right x y) h₁)).elim
  | .inr ⟨j, hj⟩ => lt_of_le_of_lt (add_cancel_le x x y (z j) hj (le_refl x)) (index_lt z j)

/-- Rocq: `Notation.CantorProduct.ordered_tail`. -/
theorem ordered_tail {A : Type} {f : A → Ordinal.{0}} (l : List A) (x : A)
    (h : CantorOrdered f (x :: l)) : CantorOrdered f l :=
  h.2

/-- Rocq: `Notation.CantorProduct.each_in`. -/
theorem each_in {A : Type} {P : A → Prop} : ∀ (l : List A) (t : A), Each P l → t ∈ l → P t
  | _ :: _, _, ⟨h, _⟩, .head _ => h
  | _ :: l, t, ⟨_, hl⟩, .tail _ h => each_in l t hl h

section cantor_product_upper

variable {A : Type} {f : A → Ordinal.{0}} {P : A → Prop} (X : HasCantorDecomposition f P)
  (Hinterp : HasAllInterpolants f P)

/-- Rocq: `Notation.CantorProduct.rec_value`. -/
theorem rec_value (l : List A) (h₁ : Each P l) (h₂ : CantorOrdered f l) :
    P (X.recompose l) ∧ f (X.recompose l) ≈ CantorDecomposition.cantorDenote f l :=
  let ⟨a, b⟩ := X.recompose_correct l h₁ h₂
  ⟨a, equiv_symm b⟩

include X in
/-- Subtracting a leading power from a notation.
Rocq: `Notation.CantorProduct.head_sub`. -/
theorem head_sub (e : A) (rest : List A) (w : A) (he : P e) (hrest : Each P rest)
    (hord : CantorOrdered f (e :: rest)) (hw : P w) (hle : ω ^ f e ≤ f w)
    (hlt : f w < ω ^ f e + CantorDecomposition.cantorDenote f rest) :
    ∃ p, Qn f P p ∧ f w ≈ ω ^ f e + p ∧ p < CantorDecomposition.cantorDenote f rest := by
  obtain ⟨hw₁, hw₂, hw₃⟩ := X.decompose_correct w hw
  generalize X.decompose w = dl at hw₁ hw₂ hw₃
  cases dl with
  | nil => exact (lt_irrefl 0 (lt_of_lt_of_le (pow_pos ω _) (le_trans hle hw₃.le))).elim
  | cons d ds =>
    obtain ⟨hd, hds⟩ := hw₁
    have hc := X.compare_correct d e hd he
    revert hc
    cases X.compare d e with
    | lt =>
      intro hc
      exact (lt_irrefl (f w) (lt_of_le_of_lt (equiv_trans hw₃ (denote_V X (d :: ds) ⟨hd, hds⟩ hw₂)).le
        (lt_of_lt_of_le (V_below_power f (d :: ds) (f d) (f e) (ordered_head_le f ds d hw₂) hc
          (X.complete e)) hle))).elim
    | eq =>
      intro hc
      obtain ⟨h₁, h₂⟩ := rec_value X ds hds hw₂.2
      have hfw : f w ≈ ω ^ f e + CantorDecomposition.cantorDenote f ds :=
        equiv_trans hw₃ (add_congr (pow_congr (equiv_refl ω) hc) (equiv_refl _))
      exact ⟨_, ⟨X.recompose ds, h₁, equiv_symm h₂⟩, hfw,
        add_cancel_lt_con _ _ _ (lt_of_le_of_lt hfw.ge hlt)⟩
    | gt =>
      intro hc
      exact (lt_irrefl (f w) (lt_trans hlt (lt_of_le_of_lt (denote_V X (e :: rest) ⟨he, hrest⟩ hord).le
        (lt_of_lt_of_le (V_below_power f (e :: rest) (f e) (f d) (ordered_head_le f rest e hord) hc
          (X.complete d)) (le_trans (nadd_le1 _ _) (equiv_trans hw₃ (denote_V X (d :: ds) ⟨hd, hds⟩ hw₂)).ge))))).elim

include Hinterp in
/-- Rocq: `Notation.CantorProduct.head_split_upper`. -/
theorem head_split_upper (a : Ordinal.{0}) (e : A) (rest : List A) (ha : QHn f P a) (he : P e)
    (hrest : Each P rest) (hord : CantorOrdered f (e :: rest)) :
    nmul a (Tn f P (f (X.recompose (e :: rest)))) ≤
      nmul a (En X e) ♯ nmul a (Tn f P (f (X.recompose rest))) := by
  obtain ⟨HPl, Hl⟩ := rec_value X (e :: rest) ⟨he, hrest⟩ hord
  obtain ⟨HPr, Hr⟩ := rec_value X _ hrest hord.2
  obtain ⟨_, HEe'⟩ := En_props X Hinterp e he
  let E := ω ^ f e
  let c := CantorDecomposition.cantorDenote f rest
  let T0 := Tn f P (f (X.recompose (e :: rest)))
  have HT0 : T0 ≈ E + c := equiv_trans (Tn_eq Hinterp _ HPl) Hl
  have HTr : Tn f P (f (X.recompose rest)) ≈ c := equiv_trans (Tn_eq Hinterp _ HPr) Hr
  have HQE : Qn f P E := ⟨X.recompose [e], (single_value X e he).1,
    equiv_symm (equiv_trans (single_value X e he).2 (nadd_zero_r _))⟩
  let Sp : Ordinal.{0} → Bool → Ordinal.{0} → Prop := fun v s p =>
    cond s (v < E ∧ p ≈ v) (E ≤ v ∧ v ≈ E + p)
  have Sp_total : ∀ v, Qn f P v → v < T0 → ∃ s p, Sp v s p := fun v hQv hvT =>
    match Qn_dec X v E hQv HQE with
    | .inl h => ⟨true, v, h, equiv_refl v⟩
    | .inr h =>
      let ⟨w, hw, hvw⟩ := hQv
      let ⟨p, _, hp₁, _⟩ := head_sub X e rest w he hrest hord hw (le_trans h hvw.le)
        (lt_of_le_of_lt hvw.ge (lt_of_lt_of_le hvT HT0.le))
      ⟨false, p, h, equiv_trans hvw hp₁⟩
  have Sp_mono : ∀ v w s p q, Qn f P v → Qn f P w → Sp v s p → Sp w s q → v < w → p < q := by
    intro v w s p q _ _ h₁ h₂ hvw
    cases s with
    | true => exact lt_of_le_of_lt h₁.2.le (lt_of_lt_of_le hvw h₂.2.ge)
    | false => exact add_cancel_lt_con E p q (lt_of_le_of_lt h₁.2.ge (lt_of_lt_of_le hvw h₂.2.le))
  have hQD : QR (Qn f P) [(a, T0)] := fun r hr => by
    cases hr with
    | head => exact ⟨ha, Tn_QH Hinterp _ HPl⟩
    | tail _ h => nomatch h
  have hcov : CoversQ (Qn f P) T0 Sp [(a, T0)] [(a, En X e)] [(a, Tn f P (f (X.recompose rest)))] := by
    intro u v hs _
    obtain ⟨r, hr, hu, hv⟩ := hs
    cases hr with
    | tail _ h => nomatch h
    | head =>
      refine ⟨hv, fun s p hsp => ?_⟩
      cases s with
      | true => exact ⟨(a, En X e), .head _, hu, lt_of_le_of_lt hsp.2.le (lt_of_lt_of_le hsp.1 HEe'.ge)⟩
      | false =>
        exact ⟨(a, Tn f P (f (X.recompose rest))), .head _, hu, lt_of_lt_of_le
          (add_cancel_lt_con E _ _ (lt_of_le_of_lt hsp.2.ge (lt_of_lt_of_le hv HT0.le))) HTr.ge⟩
  exact le_trans (nmul_rk a T0).le
    (le_trans (covers_rk_Q (Qn f P) Qn_eq (Qn_dec X) T0 Sp Sp_total Sp_mono _ _ _ hQD hcov)
      (nadd_le_nadd (nmul_rk _ _).ge (nmul_rk _ _).ge))

/-- Rocq: `Notation.CantorProduct.VS`. -/
noncomputable def VS (a : Ordinal.{0}) : List A → Ordinal.{0}
  | [] => 0
  | t :: l => nmul a (En X t) ♯ VS a l

include Hinterp in
/-- Rocq: `Notation.CantorProduct.list_split_upper`. -/
theorem list_split_upper (a : Ordinal.{0}) : ∀ l : List A, QHn f P a → Each P l →
    CantorOrdered f l → nmul a (Tn f P (f (X.recompose l))) ≤ VS X a l
  | [], _, _, _ =>
    let ⟨H₁, H₂⟩ := rec_value X [] trivial trivial
    le_trans (nmul_monotone (le_refl a) (le_trans (Tn_eq Hinterp _ H₁).le H₂.le)) (nmul_zero a).le
  | t :: l, ha, ⟨ht, hl⟩, hord =>
    le_trans (head_split_upper X Hinterp a t l ha ht hl hord)
      (nadd_le_nadd (le_refl _) (list_split_upper a l ha hl hord.2))

/-- Rocq: `Notation.CantorProduct.below_power_dec`. -/
theorem below_power_dec (a₁ a : A) (ha₁ : P a₁) (ha : P a) (h : f a₁ < ω ^ f a) :
    ∀ t, t ∈ X.decompose a₁ → f t < f a := by
  obtain ⟨H₁, H₂, H₃⟩ := X.decompose_correct a₁ ha₁
  generalize X.decompose a₁ = dl at H₁ H₂ H₃ ⊢
  cases dl with
  | nil => exact fun _ ht => nomatch ht
  | cons d ds =>
    intro t ht
    obtain ⟨hd₁, hds⟩ := H₁
    have hbig : ∀ (_ : f a ≤ f d), False := fun hle =>
      lt_irrefl (f a₁) (lt_of_lt_of_le h (le_trans (pow_le_pow_right ω hle)
        (le_trans (nadd_le1 _ _) (equiv_trans H₃ (denote_V X (d :: ds) ⟨hd₁, hds⟩ H₂)).ge)))
    refine lt_of_le_of_lt (ordered_head_le f ds d H₂ t ht) ?_
    have hc := X.compare_correct d a hd₁ ha
    revert hc
    cases X.compare d a with
    | lt => exact id
    | eq => exact fun hc => (hbig hc.ge).elim
    | gt => exact fun hc => (hbig (le_of_lt hc)).elim

include X in
/-- Rocq: `Notation.CantorProduct.sum_below_power`. -/
theorem sum_below_power (a b : A) (l : List A) (ha : P a) (hb : P b) (hl : Each P l)
    (hlt : ∀ t, t ∈ l → f t < f a) : V ((l.map f).map fun s => f b ♯ s) < ω ^ (f a ♯ f b) := by
  obtain ⟨_, Hab'⟩ := cantor_nadd_correct X a b ha hb
  refine lt_of_lt_of_le ?_ (pow_le_pow_right ω Hab'.le)
  induction l with
  | nil => exact pow_pos ω _
  | cons t l ih =>
    obtain ⟨_, hl⟩ := hl
    exact nadd_closed_con _ _ _ (X.complete _) (pow_lt_pow_right omega_gt1 (lt_of_lt_of_le
        (lt_of_le_of_lt (nadd_comm _ _).le (nadd_increasing1 (f b) (hlt t (.head _)))) Hab'.ge))
      (ih hl fun t h => hlt t (.tail _ h))

/-- Rocq: `Notation.CantorProduct.VS_upper`. -/
theorem VS_upper (b : A) (l : List A) (_hb : P b) (hl : Each P l)
    (H : ∀ t, t ∈ l → nmul (En X b) (En X t) ≤ ω ^ (f b ♯ f t)) :
    VS X (En X b) l ≤ V ((l.map f).map fun s => f b ♯ s) := by
  induction l with
  | nil => exact le_refl _
  | cons t l ih =>
    exact nadd_le_nadd (H t (.head _)) (ih hl.2 fun t h => H t (.tail _ h))

include Hinterp in
/-- Rocq: `Notation.CantorProduct.exp_upper_n`. -/
theorem exp_upper_n (a₀ b₀ : A) (ha₀ : P a₀) (hb₀ : P b₀) :
    nmul (En X a₀) (En X b₀) ≤ ω ^ (f a₀ ♯ f b₀) := by
  suffices H : ∀ o a b, P a → P b → f a ♯ f b ≤ o → nmul (En X a) (En X b) ≤ ω ^ (f a ♯ f b) from
    H _ a₀ b₀ ha₀ hb₀ (le_refl _)
  intro o
  induction o using ltRec with
  | ind o IH =>
  intro a b ha hb ho
  obtain ⟨HEa, _⟩ := En_props X Hinterp a ha
  obtain ⟨HEb, _⟩ := En_props X Hinterp b hb
  -- bounds for one side, by the induction hypothesis
  have Hside : ∀ a b u, P a → P b → f a ♯ f b ≤ o → QHn f P u → u < En X a →
      nmul (En X b) u < ω ^ (f a ♯ f b) := by
    intro a' b' u ha' hb' ho' hu hlt
    obtain ⟨a₁, Ha₁, Hua₁⟩ := hu.1
    have Hlt₁ : f a₁ < ω ^ f a' :=
      lt_of_le_of_lt Hua₁.ge (lt_of_lt_of_le hlt (En_props X Hinterp a' ha').2.le)
    obtain ⟨Hd₁, Hd₂, Hd₃⟩ := X.decompose_correct a₁ Ha₁
    obtain ⟨HPr, Hr⟩ := rec_value X _ Hd₁ Hd₂
    have Hu' : u ≈ Tn f P (f (X.recompose (X.decompose a₁))) :=
      equiv_trans Hua₁ (equiv_trans Hd₃ (equiv_symm (equiv_trans (Tn_eq Hinterp _ HPr) Hr)))
    refine lt_of_le_of_lt (nmul_monotone (le_refl _) Hu'.le) (lt_of_le_of_lt
      (list_split_upper X Hinterp _ _ (En_props X Hinterp b' hb').1 Hd₁ Hd₂) (lt_of_le_of_lt
        (VS_upper X b' _ hb' Hd₁ fun t ht => IH (f b' ♯ f t) (lt_of_lt_of_le (lt_of_lt_of_le
            (nadd_increasing2 (f b') (below_power_dec X a₁ a' Ha₁ ha' Hlt₁ t ht)) (nadd_comm _ _).le) ho')
          b' t hb' (each_in _ _ Hd₁ ht) (le_refl _))
        (sum_below_power X a' b' _ ha' hb' Hd₁ (below_power_dec X a₁ a' Ha₁ ha' Hlt₁))))
  obtain ⟨_, Hab'⟩ := cantor_nadd_correct X a b ha hb
  refine le_trans (nmul_rk _ _).le (le_intro fun i => ?_)
  obtain ⟨m, hm⟩ := rk_lt_elim _ _ (index_lt (rk [(En X a, En X b)]) i)
  rcases m with ⟨c, d⟩ | m
  · have hs : Rsub [(En X a ⊓ En X a c, En X b), (En X a, En X b ⊓ En X b d)]
        ([(En X a c, En X b)] ++ [(En X a, En X b d)]) :=
      rsub_cons (rsub_in (.head _) ⟨glb_le2 _ _, le_refl _⟩)
        (rsub_cons (rsub_in (.tail _ (.head _)) ⟨le_refl _, glb_le2 _ _⟩) (rsub_nil _))
    have hx : nmul (En X a c) (En X b) < ω ^ f (cantorNadd X a b) :=
      lt_of_le_of_lt (nmul_comm _ _).le (lt_of_lt_of_le
        (Hside a b _ ha hb ho (QH_child _ _ c HEa) (index_lt _ c)) (pow_le_pow_right ω Hab'.ge))
    have hy : nmul (En X a) (En X b d) < ω ^ f (cantorNadd X a b) :=
      lt_of_lt_of_le (Hside b a _ hb ha (le_trans (nadd_comm _ _).le ho) (QH_child _ _ d HEb)
        (index_lt _ d)) (pow_le_pow_right ω (le_trans (nadd_comm _ _).le Hab'.ge))
    exact lt_of_le_of_lt hm (lt_of_le_of_lt (rk_mono hs) (lt_of_le_of_lt (rk_app_le _ _)
      (lt_of_le_of_lt (nadd_le_nadd (nmul_rk _ _).ge (nmul_rk _ _).ge)
        (lt_of_lt_of_le (nadd_closed_con _ _ _ (X.complete _) hx hy) (pow_le_pow_right ω Hab'.le)))))
  · exact (m : PEmpty).elim

include Hinterp in
/-- The semantic product is at most the algorithm's value.
Rocq: `Notation.CantorProduct.cantor_nmul_upper`. -/
theorem cantor_nmul_upper (x y : A) (hx : P x) (hy : P y) :
    nmul (f x) (f y) ≤ f (cantorNmul X x y) := by
  obtain ⟨Hx₁, Hx₂, Hx₃⟩ := X.decompose_correct x hx
  obtain ⟨Hy₁, Hy₂, Hy₃⟩ := X.decompose_correct y hy
  obtain ⟨HPx, Hrx⟩ := rec_value X _ Hx₁ Hx₂
  obtain ⟨HPy, Hry⟩ := rec_value X _ Hy₁ Hy₂
  have Hy' : f y ≈ Tn f P (f (X.recompose (X.decompose y))) :=
    equiv_trans Hy₃ (equiv_symm (equiv_trans (Tn_eq Hinterp _ HPy) Hry))
  have Hx' : Tn f P (f x) ≈ Tn f P (f (X.recompose (X.decompose x))) :=
    equiv_trans (Tn_eq Hinterp x hx)
      (equiv_trans Hx₃ (equiv_symm (equiv_trans (Tn_eq Hinterp _ HPx) Hrx)))
  have claim : ∀ l : List A, Each P l → VS X (Tn f P (f x)) l ≤
      V (cnfProd (l.map f) ((X.decompose x).map f)) := by
    intro l hl
    induction l with
    | nil => exact le_refl _
    | cons t l ih =>
      obtain ⟨ht, hl⟩ := hl
      refine le_trans (nadd_le_nadd ?_ (ih hl)) (V_cnf_cons_l _ _ _).ge
      exact le_trans (nmul_comm _ _).le (le_trans (nmul_monotone (le_refl _) Hx'.le)
        (le_trans (list_split_upper X Hinterp _ _ (En_props X Hinterp t ht).1 Hx₁ Hx₂)
          (VS_upper X t _ ht Hx₁ fun s hs => exp_upper_n X Hinterp t s ht (each_in _ _ Hx₁ hs))))
  exact le_trans (nmul_monotone (Tn_eq Hinterp x hx).ge Hy'.le)
    (le_trans (list_split_upper X Hinterp _ _ (Tn_QH Hinterp x hx) Hy₁ Hy₂)
      (le_trans (claim _ Hy₁) (le_trans (V_cnf_comm _ _).le (cantor_nmul_correct X x y hx hy).2.ge)))

include Hinterp in
/-- Together: the algorithm reflects the semantic natural product.
Rocq: `Notation.CantorProduct.cantor_nmul_reflects`. -/
theorem cantor_nmul_reflects : Reflects A f P (.ord ==> .ord ==> .ord) nmul (cantorNmul X) := by
  intro u x ⟨hu, hx⟩ v y ⟨hv, hy⟩
  exact ⟨equiv_trans (nmul_congr hu hv) (equiv_intro (cantor_nmul_upper X Hinterp x y hx hy)
    (cantor_nmul_lower X Hinterp x y hx hy)), (cantor_nmul_correct X x y hx hy).1⟩

end cantor_product_upper

/-! ## Interpolants are needed only at epsilon numbers

A notation that is not an epsilon number (`f x ≈ ω ^ f x`) has a normal form
whose exponents all denote strictly smaller ordinals, and interpolants are
preserved by `ω ^ ·` and `+`. So interpolants at the epsilon notations give
interpolants everywhere, and the reflection of the natural product needs
nothing more. -/

/-- Rocq: `Notation.CantorProduct.le_expOmega`. -/
theorem le_powOmega : ∀ x : Ordinal.{u}, x ≤ ω ^ x
  | mk B g => le_intro fun b =>
    lt_of_le_of_lt (le_powOmega (g b)) (pow_lt_pow_right omega_gt1 (index_lt (mk B g) b))

section epsilon_interpolants

variable {A : Type} {f : A → Ordinal.{0}} {P : A → Prop} (X : HasCantorDecomposition f P)

/-- Rocq: `Notation.CantorProduct.repeat_props`. -/
theorem repeat_props (e : A) (n : Nat) (he : P e) :
    Each P (List.replicate n e) ∧ CantorOrdered f (List.replicate n e) := by
  induction n with
  | zero => exact ⟨trivial, trivial⟩
  | succ n ih =>
    refine ⟨⟨he, ih.1⟩, ?_, ih.2⟩
    cases n with
    | zero => exact trivial
    | succ _ => exact le_refl _

/-- Rocq: `Notation.CantorProduct.denote_repeat`. -/
theorem denote_repeat (f : A → Ordinal.{0}) (e : A) (n : Nat) :
    CantorDecomposition.cantorDenote f (List.replicate (n + 1) e) ≈ ω ^ f e * ofNat (n + 1) := by
  induction n with
  | zero => exact equiv_trans (add_zero _) (equiv_symm (mul_one _))
  | succ n ih =>
    exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (equiv_trans
      (mul_congr (equiv_refl _) (ofNat_add (n + 1) 1))
      (equiv_trans (mul_add _ _ _) (add_congr (mul_one _) (equiv_refl _)))))

/-- Rocq: `Notation.CantorProduct.interp_zero`. -/
theorem interp_zero : HasInterpolants f P 0 :=
  (has_interpolants_unfold 0).2 fun i hi => (zero_lt i hi).elim

include X in
/-- Rocq: `Notation.CantorProduct.interp_power`. -/
theorem interp_power (e : A) (_he : P e)
    (IH : ∀ y, P y → f y < ω ^ f e → HasInterpolants f P (f y))
    (hie : HasInterpolants f P (f e)) : HasInterpolants f P (ω ^ f e) := by
  refine (has_interpolants_unfold _).2 fun i hi => ?_
  rw [pow_unfold] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨Hz₁, Hz₂⟩ := cantor_zero_reflects X
    have Hfz : f (cantorZero X) < ω ^ f e := lt_of_le_of_lt Hz₁.ge (pow_pos ω _)
    obtain ⟨_, hi⟩ := lt_elim hi
    exact ⟨cantorZero X, Hz₂, le_trans hi Hz₁.le, Hfz, IH _ Hz₂ Hfz⟩
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    rw [mul_unfold] at hi
    obtain ⟨n, hi⟩ := sup_lt hi
    obtain ⟨e', He', He'₁, He'₂, _⟩ := (has_interpolants_unfold _).1 hie (f e j) (index_lt _ j)
    obtain ⟨Hr₁, Hr₂⟩ := repeat_props e' (n.down + 1) He'
    obtain ⟨Hy, Hfy⟩ := X.recompose_correct _ Hr₁ Hr₂
    have Hfy' : f (X.recompose (List.replicate (n.down + 1) e')) ≈ ω ^ f e' * ofNat (n.down + 1) :=
      equiv_trans (equiv_symm Hfy) (denote_repeat f e' n.down)
    have Hylt : f (X.recompose (List.replicate (n.down + 1) e')) < ω ^ f e :=
      lt_of_le_of_lt Hfy'.le (mul_nat_below_power (X.complete e) He'₂ _)
    exact ⟨_, Hy, le_of_lt (lt_of_lt_of_le hi (le_trans (mul_succ _ _).ge
      (le_trans (mul_le_mul_right _ (pow_le_pow_right ω He'₁)) Hfy'.ge))), Hylt, IH _ Hy Hylt⟩

include X in
/-- Rocq: `Notation.CantorProduct.interp_denote`. -/
theorem interp_denote : ∀ l : List A, Each P l →
    (∀ t, t ∈ l → HasInterpolants f P (ω ^ f t)) →
    HasInterpolants f P (CantorDecomposition.cantorDenote f l)
  | [], _, _ => interp_zero
  | t :: l, ⟨htp, hl⟩, ht =>
    let ⟨Hp₁, Hp₂⟩ := X.recompose_correct [t] ⟨htp, trivial⟩ ⟨trivial, trivial⟩
    have Hp : f (X.recompose [t]) ≈ ω ^ f t := equiv_trans (equiv_symm Hp₂) (add_zero _)
    (has_interpolants_eq_mor (add_congr Hp (equiv_refl _))).1
      (has_interpolants_add (cantorAdd X) (cantor_add_reflects X) _ _ Hp₁
        ((has_interpolants_eq_mor Hp).2 (ht t (.head _)))
        (interp_denote l hl fun t h => ht t (.tail _ h)))

include X in
/-- Rocq: `Notation.CantorProduct.interpolants_from_epsilons`. -/
theorem interpolants_from_epsilons
    (Heps : ∀ x, P x → f x ≈ ω ^ f x → HasInterpolants f P (f x)) : HasAllInterpolants f P := by
  intro x₀ hx₀
  suffices H : ∀ o x, P x → f x ≤ o → HasInterpolants f P (f x) from H _ x₀ hx₀ (le_refl _)
  intro o
  induction o using ltRec with
  | ind o IH =>
  intro x hx ho
  obtain ⟨Hd₁, Hd₂, Hd₃⟩ := X.decompose_correct x hx
  generalize X.decompose x = dl at Hd₁ Hd₂ Hd₃
  cases dl with
  | nil => exact (has_interpolants_eq_mor Hd₃).2 interp_zero
  | cons d ds =>
    have Hdx' : ω ^ f d ≤ f x := le_trans (le_add_right _ _) Hd₃.ge
    have hc := X.compare_correct d x Hd₁.1 hx
    revert hc
    cases X.compare d x with
    | lt =>
      -- not an epsilon number: every exponent is smaller
      intro hc
      have Hsmall : ∀ y, P y → f y < f x → HasInterpolants f P (f y) := fun y hy hlt =>
        IH (f y) (lt_of_lt_of_le hlt ho) y hy (le_refl _)
      refine (has_interpolants_eq_mor Hd₃).2 (interp_denote X (d :: ds) Hd₁ fun t ht => ?_)
      have Htd : f t ≤ f d := ordered_head_le f ds d Hd₂ t ht
      have HPt : P t := each_in _ _ Hd₁ ht
      exact interp_power X t HPt
        (fun y hy hlt => Hsmall y hy (lt_of_lt_of_le hlt (le_trans (pow_le_pow_right ω Htd) Hdx')))
        (Hsmall t HPt (lt_of_le_of_lt Htd hc))
    | eq =>
      -- an epsilon number
      exact fun hc => Heps x hx (equiv_intro (le_powOmega _) (le_trans (pow_le_pow_right ω hc.ge) Hdx'))
    | gt =>
      exact fun hc => (lt_irrefl (f x) (lt_of_lt_of_le hc (le_trans (le_powOmega _) Hdx'))).elim

/-- Hence the natural product reflects as soon as the epsilon notations have
interpolants. Rocq: `Notation.CantorProduct.cantor_nmul_reflects_epsilons`. -/
theorem cantor_nmul_reflects_epsilons
    (H : ∀ x, P x → f x ≈ ω ^ f x → HasInterpolants f P (f x)) :
    Reflects A f P (.ord ==> .ord ==> .ord) nmul (cantorNmul X) :=
  cantor_nmul_reflects X (interpolants_from_epsilons X H)

/-- In particular, unconditionally for a system without epsilon notations.
Rocq: `Notation.CantorProduct.cantor_nmul_reflects_no_epsilons`. -/
theorem cantor_nmul_reflects_no_epsilons (H : ∀ x, P x → ¬ f x ≈ ω ^ f x) :
    Reflects A f P (.ord ==> .ord ==> .ord) nmul (cantorNmul X) :=
  cantor_nmul_reflects_epsilons X fun x hx heq => (H x hx heq).elim

end epsilon_interpolants

/-! ## Remarks

Every notation system of this development has interpolants, so its natural
product reflects `nmul` constructively (see `VF_reflects_nmul` in each
notation file).

Interpolants matter only at epsilon notations (`interpolants_from_epsilons`);
a system without them needs no hypothesis at all
(`cantor_nmul_reflects_no_epsilons`). Whether they can be dropped at epsilon
notations is open:

- An epsilon notation is where a system can depend on an undecided
  proposition. For instance, a system with one free atom `ε`, denoting
  `e = sup_n ω^ω^…^b` with `b` equal to `1`, or `ε₀ + 1` if `P`, has decidable
  comparisons (`e` is `ε₀`, or `ε₁` if `P`) but no interpolants at `ε`.
- At such an `e`, the classical strategy for superdistributivity must compare
  a child of `e` (whose value depends on `P`) with a deeper descendant (whose
  value does not): choosing the tallest rectangle covering a column. This is
  the kind of choice that yields the reverse results elsewhere, so a
  counterexample to reflection, if there is one, would be a game of
  transfinite height played at such an atom. The Kripke instances checked so
  far (`tools/kripke/pdep_widths.py`) have finite heights and are all
  forced. -/

end ConstructiveOrdinals.CantorProduct
