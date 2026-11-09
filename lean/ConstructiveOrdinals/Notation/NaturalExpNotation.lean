import ConstructiveOrdinals.NaturalExp
import ConstructiveOrdinals.Notation.CantorProduct
import ConstructiveOrdinals.Notation.SchutteMatrix

/-!
# No natural exponentiation on notation systems, constructively

Port of `Ordinal/Notation/NaturalExpNotation.v`.

`NaturalExp` shows, with excluded middle, that no operation on the ordinals
satisfies the laws of a natural exponentiation, and that excluded middle is
needed only for the `e`-free ratio lemma `no_log23_ratio`. Here we prove the
ratio lemma constructively for ordinals denoted by a notation system with a
Cantor decomposition and interpolants (`no_log23_ratio_notation`). Hence no
operation on such a notation system satisfies the laws, restricted to its
notations (`natural_exp_impossible_notation`), constructively. This covers the
notation systems of the development, up to the large Veblen ordinal.

Each use of excluded middle in the classical proof has a constructive
substitute on notations:
- Cantor normal forms come from the decomposition of the notation system
  (`dec_head`, `lead_exists_Q`);
- comparisons of exponents are decided by its comparison (`Qn_dec`);
- powers of `ω` with complete exponents are closed under natural sums
  constructively (`nadd_closed_con`);
- the leading exponent of a natural product of notations is read off the
  term-by-term product of their normal forms (`has_deg_mul_Q`), which reflects
  `nmul` given interpolants (`cantor_nmul_reflects`).

Lean notes:
- Rocq's `take_eq` and `take_eq_spec` (splitting off the leading run of equal
  exponents) are replaced by the existential lemma `split_leading`, and a few
  list facts are proved locally to avoid the axioms of core's list lemmas.
-/

namespace ConstructiveOrdinals.NaturalExpNotation

open Ordinal NaturalProduct NaturalExp CantorDecomposition CantorProduct Interpolants

universe u v

/-! ## List helpers -/

private theorem mem_map_inv {α : Type u} {β : Type v} {g : α → β} {b : β} :
    ∀ {l : List α}, b ∈ l.map g → ∃ a, a ∈ l ∧ g a = b
  | [], h => nomatch h
  | a :: l, h => by
    cases h with
    | head => exact ⟨a, .head _, rfl⟩
    | tail _ h =>
      obtain ⟨a', ha', e⟩ := mem_map_inv h
      exact ⟨a', .tail _ ha', e⟩

private theorem mem_append_inv {α : Type u} {x : α} :
    ∀ {l₁ l₂ : List α}, x ∈ l₁ ++ l₂ → x ∈ l₁ ∨ x ∈ l₂
  | [], _, h => .inr h
  | _ :: _, _, h => by
    cases h with
    | head => exact .inl (.head _)
    | tail _ h => exact (mem_append_inv h).elim (fun h => .inl (.tail _ h)) .inr

private theorem length_map' {α : Type u} {β : Type v} (g : α → β) : ∀ l : List α, (l.map g).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (length_map' g l)

private theorem map_append' {α : Type u} {β : Type v} (g : α → β) :
    ∀ l₁ l₂ : List α, (l₁ ++ l₂).map g = l₁.map g ++ l₂.map g
  | [], _ => rfl
  | a :: l₁, l₂ => congrArg (g a :: ·) (map_append' g l₁ l₂)

private theorem mem_cnfProd : ∀ (xs ys : List Ordinal.{0}) (z : Ordinal.{0}),
    z ∈ cnfProd xs ys → ∃ a b, a ∈ xs ∧ b ∈ ys ∧ a ♯ b = z
  | [], _, _, h => nomatch h
  | a :: xs, ys, z, h =>
    match mem_append_inv h with
    | .inl h₁ =>
      let ⟨b, hb, e⟩ := mem_map_inv h₁
      ⟨a, b, .head _, hb, e⟩
    | .inr h₂ =>
      let ⟨a', b, ha, hb, e⟩ := mem_cnfProd xs ys z h₂
      ⟨a', b, .tail _ ha, hb, e⟩

/-! ## Leading exponents of natural sums of powers, constructively -/

/-- Rocq: `Notation.NaturalExpNotation.V_ge_member`. -/
theorem V_ge_member (z : Ordinal.{0}) : ∀ zs : List Ordinal.{0}, z ∈ zs → ω ^ z ≤ V zs
  | [], h => nomatch h
  | _ :: zs, h => by
    cases h with
    | head => exact le_trans (nadd_zero_r _).ge (nadd_le_nadd (le_refl _) (zero_least _))
    | tail _ h =>
      exact le_trans (V_ge_member z zs h)
        (le_trans (nadd_zero_l _).ge (nadd_le_nadd (zero_least _) (le_refl _)))

/-- Rocq: `Notation.NaturalExpNotation.V_le_nrep`. -/
theorem V_le_nrep (z0 : Ordinal.{0}) : ∀ zs : List Ordinal.{0},
    (∀ z, z ∈ zs → z ≤ z0) → V zs ≤ nrep zs.length (ω ^ z0)
  | [], _ => le_refl _
  | a :: zs, h =>
    le_trans (nadd_comm _ _).le
      (nadd_le_nadd (V_le_nrep z0 zs fun z hz => h z (.tail _ hz))
        (pow_le_pow_right ω (h a (.head _))))

/-- Rocq: `Notation.NaturalExpNotation.has_deg_V`. -/
theorem has_deg_V (z0 : Ordinal.{0}) (zs : List Ordinal.{0}) (hin : z0 ∈ zs)
    (hle : ∀ z, z ∈ zs → z ≤ z0) : HasDeg z0 (V zs) :=
  ⟨V_ge_member z0 zs hin, zs.length + 1,
    lt_of_le_of_lt (V_le_nrep z0 zs hle) (nrep_lt_succ _ _ (pow_pos ω z0))⟩

/-- Rocq: `Notation.NaturalExpNotation.nrep_below_con`. -/
theorem nrep_below_con (k : Nat) (d : Ordinal.{0}) (hd : Complete d) :
    nrep k (ω ^ d) < ω ^ succ d := by
  induction k with
  | zero => exact pow_pos ω _
  | succ k ih =>
    exact nadd_closed_con (succ d) _ _ (succ_complete hd) ih (pow_lt_pow_right omega_gt1 (succ_lt d))

/-- Rocq: `Notation.NaturalExpNotation.nrep_lt_closed_con`. -/
theorem nrep_lt_closed_con (k : Nat) (g r : Ordinal.{0}) (hg : Complete g) (hr : r < ω ^ g) :
    nrep k r < ω ^ g := by
  induction k with
  | zero => exact pow_pos ω _
  | succ k ih => exact nadd_closed_con g _ _ hg ih hr

/-- Rocq: `Notation.NaturalExpNotation.lead_nrep_con`. -/
theorem lead_nrep_con (γ : Ordinal.{0}) (c : Nat) (d : Ordinal.{0}) (k : Nat) (hγ : Complete γ)
    (h : HasLead γ c d) : HasLead γ ((k + 1) * c) (nrep (k + 1) d) :=
  let ⟨hc, r, hr, hd⟩ := h
  ⟨Nat.mul_le_mul (Nat.le_add_left 1 k) hc, nrep (k + 1) r, nrep_lt_closed_con _ γ r hγ hr,
    equiv_trans (nrep_congr _ hd)
      (equiv_trans (nrep_nadd _ _ _) (nadd_congr (nrep_nrep _ _ _) (equiv_refl _)))⟩

/-! ## Notations -/

section notations

variable {A : Type} {f : A → Ordinal.{0}} {P : A → Prop}

/-- Rocq: `Notation.NaturalExpNotation.Q_f`. -/
theorem Q_f (a : A) (ha : P a) : Qn f P (f a) := ⟨a, ha, equiv_refl _⟩

/-- Rocq: `Notation.NaturalExpNotation.Qn_nmul`. -/
theorem Qn_nmul (X : HasCantorDecomposition f P) (Hinterp : HasAllInterpolants f P)
    (x y : Ordinal.{0}) (hx : Qn f P x) (hy : Qn f P y) : Qn f P (nmul x y) :=
  let ⟨a, ha, ex⟩ := hx
  let ⟨b, hb, ey⟩ := hy
  let r := cantor_nmul_reflects X Hinterp x a ⟨ex, ha⟩ y b ⟨ey, hb⟩
  ⟨cantorNmul X a b, r.2, r.1⟩

/-- Rocq: `Notation.NaturalExpNotation.Qn_nat`. -/
theorem Qn_nat (X : HasCantorDecomposition f P) (n : Nat) : Qn f P (ofNat n) :=
  ⟨cantorNat X n, (cantor_nat_correct X n).2, equiv_symm (cantor_nat_correct X n).1⟩

/-- Rocq: `Notation.NaturalExpNotation.Qn_omega`. -/
theorem Qn_omega (X : HasCantorDecomposition f P) : Qn f P ω := by
  have h1 := cantor_nat_correct X 1
  have h2 := X.recompose_correct [cantorNat X 1] ⟨h1.2, trivial⟩ ⟨trivial, trivial⟩
  refine ⟨X.recompose [cantorNat X 1], h2.1, ?_⟩
  exact equiv_symm (equiv_trans (equiv_symm h2.2) (equiv_trans (add_zero _)
    (equiv_trans (pow_congr (equiv_refl ω) h1.1) (pow_one' omega_gt0))))

/-- Rocq: `Notation.NaturalExpNotation.Qn_nrep`. -/
theorem Qn_nrep (X : HasCantorDecomposition f P) (k : Nat) (x : Ordinal.{0}) (hx : Qn f P x) :
    Qn f P (nrep k x) := by
  induction k with
  | zero => exact Qn_zero X
  | succ k ih => exact Qn_nadd X _ _ ih hx

/-- Leading exponents of notation-denoted ordinals are compared by the
notation system. Rocq: `Notation.NaturalExpNotation.has_deg_le_Q`. -/
theorem has_deg_le_Q (X : HasCantorDecomposition f P) (δ δ' x x' : Ordinal.{0})
    (hq : Qn f P δ) (hq' : Qn f P δ') (hd : HasDeg δ x) (hd' : HasDeg δ' x') (h : x ≤ x') :
    δ ≤ δ' := by
  obtain ⟨a, ha, ea⟩ := hq
  obtain ⟨b, hb, eb⟩ := hq'
  have hd := has_deg_eq_exp _ _ _ ea hd
  have hd' := has_deg_eq_exp _ _ _ eb hd'
  obtain ⟨n, hn⟩ := hd'.2
  refine le_trans ea.le (le_trans ?_ eb.ge)
  rcases Qn_dec X (f b) (f a) (Q_f b hb) (Q_f a ha) with hlt | hle
  · exact absurd (lt_of_le_of_lt hd.1 (lt_of_le_of_lt h (lt_of_lt_of_le hn (le_of_lt
      (lt_of_lt_of_le (nrep_below_con n (f b) (X.complete b))
        (pow_le_pow_right ω (succ_least hlt))))))) (lt_irrefl _)
  · exact hle

/-- The head of the Cantor decomposition is the leading exponent.
Rocq: `Notation.NaturalExpNotation.dec_head`. -/
theorem dec_head (X : HasCantorDecomposition f P) (x : A) (hx : P x) (hpos : 0 < f x) :
    ∃ d ds, X.decompose x = d :: ds ∧ P d ∧ HasDeg (f d) (f x) ∧
      ∀ z, z ∈ d :: ds → f z ≤ f d := by
  obtain ⟨hP, ho, he⟩ := X.decompose_correct x hx
  have hv := dec_value X x hx
  obtain ⟨l, hE⟩ : ∃ l, X.decompose x = l := ⟨_, rfl⟩
  rw [hE] at hP ho he hv
  cases l with
  | nil => exact absurd (lt_of_lt_of_le hpos he.le) (lt_irrefl _)
  | cons d ds =>
    refine ⟨d, ds, hE, hP.1, has_deg_eq _ _ _ (equiv_symm hv) (has_deg_V _ _ (.head _) ?_),
      ordered_head_le f ds d ho⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_map_inv hz
    exact ordered_head_le f ds d ho y hy

/-- Rocq: `Notation.NaturalExpNotation.pos_of_deg`. -/
theorem pos_of_deg (δ z : Ordinal.{0}) (h : HasDeg δ z) : 0 < z :=
  lt_of_lt_of_le (pow_pos ω δ) h.1

/-- The leading exponent of a natural product of notations, from the
term-by-term product of their normal forms.
Rocq: `Notation.NaturalExpNotation.has_deg_mul_Q`. -/
theorem has_deg_mul_Q (X : HasCantorDecomposition f P) (Hinterp : HasAllInterpolants f P)
    (x y : A) (hx : P x) (hy : P y) (px : 0 < f x) (py : 0 < f y) :
    ∃ dx dy, P dx ∧ P dy ∧ HasDeg (f dx) (f x) ∧ HasDeg (f dy) (f y) ∧
      HasDeg (f dx ♯ f dy) (nmul (f x) (f y)) := by
  obtain ⟨d, ds, Ex, hd, hdx, hbx⟩ := dec_head X x hx px
  obtain ⟨e, es, Ey, he, hdy, hby⟩ := dec_head X y hy py
  have hc := (cantor_nmul_correct X x y hx hy).2
  rw [Ex, Ey] at hc
  have hr := (cantor_nmul_reflects X Hinterp (f x) x ⟨equiv_refl _, hx⟩ (f y) y
    ⟨equiv_refl _, hy⟩).1
  refine ⟨d, e, hd, he, hdx, hdy, has_deg_eq _ _ _ (equiv_symm (equiv_trans hr hc))
    (has_deg_V _ _ (.head _) ?_)⟩
  intro z hz
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_cnfProd _ _ z hz
  obtain ⟨a', ha', rfl⟩ := mem_map_inv ha
  obtain ⟨b', hb', rfl⟩ := mem_map_inv hb
  exact nadd_le_nadd (hbx a' ha') (hby b' hb')

/-- The leading exponent of a natural power of a notation.
Rocq: `Notation.NaturalExpNotation.npow_deg_Q`. -/
theorem npow_deg_Q (X : HasCantorDecomposition f P) (Hinterp : HasAllInterpolants f P)
    (k : Nat) (x : A) (δ : Ordinal.{0}) (hx : P x) (hq : Qn f P δ) (hδ : HasDeg δ (f x)) :
    ∃ y, P y ∧ npow (k + 1) (f x) ≈ f y ∧ HasDeg (nrep (k + 1) δ) (f y) := by
  induction k with
  | zero => exact ⟨x, hx, npow_one _, has_deg_eq_exp _ _ _ (equiv_symm (nrep_one δ)) hδ⟩
  | succ k ih =>
    obtain ⟨y, hy, ey, hdy⟩ := ih
    obtain ⟨dy, dx, pdy, pdx, hdy', hdx', hm⟩ :=
      has_deg_mul_Q X Hinterp y x hy hx (pos_of_deg _ _ hdy) (pos_of_deg _ _ hδ)
    have hr := cantor_nmul_reflects X Hinterp (f y) y ⟨equiv_refl _, hy⟩ (f x) x
      ⟨equiv_refl _, hx⟩
    refine ⟨cantorNmul X y x, hr.2, equiv_trans (nmul_congr ey (equiv_refl _)) hr.1, ?_⟩
    refine has_deg_eq _ _ _ hr.1 (has_deg_eq_exp _ _ _ (nadd_congr ?_ ?_) hm)
    · exact equiv_intro
        (has_deg_le_Q X _ _ (f y) (f y) (Q_f dy pdy) (Qn_nrep X _ δ hq) hdy' hdy (le_refl _))
        (has_deg_le_Q X _ _ (f y) (f y) (Qn_nrep X _ δ hq) (Q_f dy pdy) hdy hdy' (le_refl _))
    · exact equiv_intro
        (has_deg_le_Q X _ _ (f x) (f x) (Q_f dx pdx) hq hdx' hδ (le_refl _))
        (has_deg_le_Q X _ _ (f x) (f x) hq (Q_f dx pdx) hδ hdx' (le_refl _))

/-- Rocq: `Notation.NaturalExpNotation.ordered_app_r`. -/
theorem ordered_app_r : ∀ (p s : List A), CantorOrdered f (p ++ s) → CantorOrdered f s
  | [], _, h => h
  | a :: p, s, h => ordered_app_r p s (ordered_tail (p ++ s) a h)

/-- Splitting off the leading run of exponents equal to the head. Replaces
Rocq's `take_eq` and `take_eq_spec`. -/
theorem split_leading (X : HasCantorDecomposition f P) (g : A) (hg : P g) :
    ∀ l : List A, Each P l → CantorOrdered f l → (∀ z, z ∈ l → f z ≤ f g) →
      ∃ pre suf, l = pre ++ suf ∧ (∀ z, z ∈ pre → f z ≈ f g) ∧ (∀ z, z ∈ suf → f z < f g)
  | [], _, _, _ => by
    refine ⟨[], [], rfl, ?_, ?_⟩ <;> intro z h <;> cases h
  | z :: l, hP, ho, hb => by
    have hc := X.compare_correct g z hg hP.1
    revert hc
    cases X.compare g z with
    | lt => exact fun hc => absurd (lt_of_lt_of_le hc (hb z (.head _))) (lt_irrefl _)
    | eq =>
      intro hc
      obtain ⟨pre, suf, he, h1, h2⟩ :=
        split_leading X g hg l hP.2 (ordered_tail l z ho) fun w hw => hb w (.tail _ hw)
      refine ⟨z :: pre, suf, congrArg (z :: ·) he, ?_, h2⟩
      intro w hw
      cases hw with
      | head => exact equiv_symm hc
      | tail _ hw => exact h1 w hw
    | gt =>
      intro hc
      refine ⟨[], z :: l, rfl, ?_, fun w hw => lt_of_le_of_lt (ordered_head_le f l z ho w hw) hc⟩
      intro w h
      cases h

/-- The leading coefficient of a notation-denoted ordinal.
Rocq: `Notation.NaturalExpNotation.lead_exists_Q`. -/
theorem lead_exists_Q (X : HasCantorDecomposition f P) (d : A) (hd : P d) (hpos : 0 < f d) :
    ∃ g c, P g ∧ HasLead (f g) c (f d) := by
  obtain ⟨hP, ho, _⟩ := X.decompose_correct d hd
  have hv := dec_value X d hd
  obtain ⟨g, ds, E, hg, _, hb⟩ := dec_head X d hd hpos
  rw [E] at hP ho hv
  obtain ⟨pre, suf, hl, hpre, hsuf⟩ := split_leading X g hg (g :: ds) hP ho hb
  refine ⟨g, pre.length, hg, ?_, V (suf.map f), ?_, ?_⟩
  · cases pre with
    | nil =>
      have hy : g ∈ suf := by
        have h0 : g ∈ g :: ds := .head _
        rw [hl] at h0
        exact h0
      exact absurd (hsuf g hy) (lt_irrefl _)
    | cons _ _ => exact Nat.succ_pos _
  · cases suf with
    | nil => exact pow_pos ω _
    | cons s rest =>
      have hord : CantorOrdered f (s :: rest) := ordered_app_r pre _ (by rw [← hl]; exact ho)
      exact V_below_power f (s :: rest) (f s) (f g) (ordered_head_le f rest s hord)
        (hsuf s (.head _)) (X.complete g)
  · rw [hl, map_append'] at hv
    refine equiv_trans hv (equiv_trans (V_app _ _) (nadd_congr ?_ (equiv_refl _)))
    have h := cantor_nadd_all_eq (f g) (pre.map f) fun a ha => by
      obtain ⟨z, hz, rfl⟩ := mem_map_inv ha
      exact hpre z hz
    rw [length_map'] at h
    exact h

/-! ## The ratio lemma for notations -/

/-- Rocq: `Notation.NaturalExpNotation.no_log23_ratio_notation`. -/
theorem no_log23_ratio_notation (X : HasCantorDecomposition f P)
    (Hinterp : HasAllInterpolants f P) (x y : A) (hx : P x) (hy : P y) :
    ¬ Log23Ratio (f x) (f y) := by
  intro ⟨HX, Hup, Hdown⟩
  have HXY : f x ≤ f y :=
    le_trans (npow_one (f x)).ge (le_trans (Hup 0 0 (Nat.le_succ 2)) (npow_one (f y)).le)
  have Px : 0 < f x := lt_of_lt_of_le omega_gt0 HX
  have Py : 0 < f y := lt_of_lt_of_le Px HXY
  obtain ⟨d2, _, _, Hd2, Hδ2, _⟩ := dec_head X x hx Px
  obtain ⟨d3, _, _, Hd3, Hδ3, _⟩ := dec_head X y hy Py
  have Hmono : ∀ a k : Nat, 2 ^ (a + 1) ≤ 3 ^ (k + 1) →
      nrep (a + 1) (f d2) ≤ nrep (k + 1) (f d3) := fun a k h => by
    obtain ⟨z2, _, Ez2, Hz2⟩ := npow_deg_Q X Hinterp a x (f d2) hx (Q_f d2 Hd2) Hδ2
    obtain ⟨z3, _, Ez3, Hz3⟩ := npow_deg_Q X Hinterp k y (f d3) hy (Q_f d3 Hd3) Hδ3
    exact has_deg_le_Q X _ _ (f z2) (f z3) (Qn_nrep X _ _ (Q_f d2 Hd2))
      (Qn_nrep X _ _ (Q_f d3 Hd3)) Hz2 Hz3 (le_trans Ez2.ge (le_trans (Hup a k h) Ez3.le))
  have Hmono' : ∀ a k : Nat, 3 ^ (k + 1) ≤ 2 ^ (a + 1) →
      nrep (k + 1) (f d3) ≤ nrep (a + 1) (f d2) := fun a k h => by
    obtain ⟨z2, _, Ez2, Hz2⟩ := npow_deg_Q X Hinterp a x (f d2) hx (Q_f d2 Hd2) Hδ2
    obtain ⟨z3, _, Ez3, Hz3⟩ := npow_deg_Q X Hinterp k y (f d3) hy (Q_f d3 Hd3) Hδ3
    exact has_deg_le_Q X _ _ (f z3) (f z2) (Qn_nrep X _ _ (Q_f d3 Hd3))
      (Qn_nrep X _ _ (Q_f d2 Hd2)) Hz3 Hz2 (le_trans Ez3.ge (le_trans (Hdown a k h) Ez2.le))
  -- `D₂ > 0`, since `f x ≥ ω`.
  have Hδ2pos : 0 < f d2 := by
    rcases Qn_dec X 0 (f d2) (Qn_zero X) (Q_f d2 Hd2) with hp | hz
    · exact hp
    · obtain ⟨n, hn⟩ := Hδ2.2
      have hn1 : nrep n (1 : Ordinal.{0}) ≈ ofNat n := by
        have h := nrep_nat.{0} n 1
        rw [Nat.mul_one] at h
        exact h
      exact absurd (lt_of_le_of_lt HX (lt_of_lt_of_le hn (le_trans
        (nrep_mono n (le_trans (pow_le_pow_right ω hz) (pow_zero ω).le))
        (le_trans hn1.le (le_of_lt (index_lt ω ⟨n⟩)))))) (lt_irrefl _)
  have Hδ23 : f d2 ≤ f d3 := has_deg_le_Q X _ _ _ _ (Q_f d2 Hd2) (Q_f d3 Hd3) Hδ2 Hδ3 HXY
  obtain ⟨g2, c2, Hg2, Hl2⟩ := lead_exists_Q X d2 Hd2 Hδ2pos
  obtain ⟨g3, c3, Hg3, Hl3⟩ := lead_exists_Q X d3 Hd3 (lt_of_lt_of_le Hδ2pos Hδ23)
  have Cg2 : Complete (f g2) := X.complete g2
  have Cg3 : Complete (f g3) := X.complete g3
  -- `D₂` and `D₃` have the same leading exponent.
  have Hγ23 : f g2 ≤ f g3 :=
    has_deg_le_Q X _ _ _ _ (Q_f g2 Hg2) (Q_f g3 Hg3) (lead_deg _ _ _ Hl2) (lead_deg _ _ _ Hl3) Hδ23
  have Hγ32 : f g3 ≤ f g2 :=
    has_deg_le_Q X _ _ _ _ (Q_f g3 Hg3) (Q_f g2 Hg2) (lead_deg _ _ _ Hl3)
      (lead_deg _ _ _ (lead_nrep_con _ _ _ 1 Cg2 Hl2))
      (le_trans (nrep_one (f d3)).ge (Hmono' 1 0 (by decide)))
  refine nat_no_ratio c2 c3 Hl2.1 Hl3.1 ?_ ?_
  · intro a k ha hk h
    match a, k, ha, hk, h with
    | a + 1, k + 1, _, _, h =>
      exact lead_le _ _ _ _ _ _ (lead_nrep_con _ _ _ a Cg2 Hl2) (lead_nrep_con _ _ _ k Cg3 Hl3)
        (Hmono a k h) Hγ32
  · intro a k ha hk h
    match a, k, ha, hk, h with
    | a + 1, k + 1, _, _, h =>
      exact lead_le _ _ _ _ _ _ (lead_nrep_con _ _ _ k Cg3 Hl3) (lead_nrep_con _ _ _ a Cg2 Hl2)
        (Hmono' a k h) Hγ23

/-! ## No natural exponentiation on notations -/

/-- An operation on the notations: it maps notation-denoted ordinals to
notation-denoted ordinals. The rest of `ExpDomain` holds for any such notation
system. Rocq: `Notation.NaturalExpNotation.exp_domain_notation`. -/
theorem exp_domain_notation (X : HasCantorDecomposition f P) (Hinterp : HasAllInterpolants f P)
    (e : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (he : ∀ a b, Qn f P a → Qn f P b → Qn f P (e a b)) : ExpDomain (Qn f P) e :=
  ⟨Qn_nat X, Qn_omega X, Qn_nadd X, Qn_nmul X Hinterp, he⟩

/-- Constructively, no operation on the notations satisfies the laws of a
natural exponentiation, restricted to the notations.
Rocq: `Notation.NaturalExpNotation.natural_exp_impossible_notation`. -/
theorem natural_exp_impossible_notation (X : HasCantorDecomposition f P)
    (Hinterp : HasAllInterpolants f P) :
    ¬ ∃ e : Ordinal.{0} → Ordinal.{0} → Ordinal.{0},
      (∀ a b, Qn f P a → Qn f P b → Qn f P (e a b)) ∧ NaturalExpLawsOn (Qn f P) e := by
  intro ⟨e, hQ, he⟩
  have R := laws_log23_ratio_on (Qn f P) e (exp_domain_notation X Hinterp e hQ) he
  obtain ⟨x, hx, ex⟩ := hQ _ _ (Qn_nat X 2) (Qn_omega X)
  obtain ⟨y, hy, ey⟩ := hQ _ _ (Qn_nat X 3) (Qn_omega X)
  exact no_log23_ratio_notation X Hinterp x y hx hy (log23_ratio_eq _ _ _ _ ex ey R)

end notations

/-- For example, on the Schütte matrices, whose normal forms reach the large
Veblen ordinal. Rocq's `let Q := …` is unfolded.
Rocq: `Notation.NaturalExpNotation.natural_exp_impossible_schutte_matrix`. -/
theorem natural_exp_impossible_schutte_matrix :
    ¬ ∃ e : Ordinal.{0} → Ordinal.{0} → Ordinal.{0},
      (∀ a b, Qn SchutteMatrixNotation.VForm.denote SchutteMatrixNotation.VForm.IsNormal a →
        Qn SchutteMatrixNotation.VForm.denote SchutteMatrixNotation.VForm.IsNormal b →
        Qn SchutteMatrixNotation.VForm.denote SchutteMatrixNotation.VForm.IsNormal (e a b)) ∧
      NaturalExpLawsOn (Qn SchutteMatrixNotation.VForm.denote SchutteMatrixNotation.VForm.IsNormal) e :=
  natural_exp_impossible_notation SchutteMatrixNotation.VForm.hasCantorDecomposition
    SchutteMatrixNotation.VForm.schutte_matrix_has_all_interpolants

end ConstructiveOrdinals.NaturalExpNotation
