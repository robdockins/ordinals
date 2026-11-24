import ConstructiveOrdinals.Bachmann.Agree

/-!
# Semantic facts about Bachmann's hierarchy, for notation systems

Prerequisites for the notation system in `Notation/Bachmann/Notation`: small
identities between canonical trees, up to `bsub` in both directions (`φ`
depends on the tree, not only on the order type of the index), and
calibrations of `bphi` at the base `1+x`.

Ported from the Rocq file `BachmannFacts.v`. Its local `schutte_matrix_app`
is `Ordinal.schutte_matrix_app` of `Schutte/ColumnFacts`.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-! ## Trees with no components -/

/-- Rocq: `BachmannFacts.bphi_bzero`. -/
theorem bphi_bzero (f : Ordinal.{u} → Ordinal.{u}) (_hf : NormalFunction f) (y : Ordinal.{u}) : bphi f bzero y ≈ f y := by
  refine equiv_intro ?_ (bphi_ge_f f _ y)
  show cfe f (PEmpty ⊕ PEmpty) (bphi_fam f PEmpty.elim PEmpty.elim) y ≤ f y
  rw [cfe_unroll]
  exact sup_least fun o => match o with
    | some (.inl e, _) => nomatch e
    | some (.inr e, _) => nomatch e
    | none => le_refl _

/-! ## Identities between canonical trees, up to `bsub` -/

/-- Rocq: `BachmannFacts.bequiv`. -/
def BEquiv (x y : BOrd.{u}) : Prop := bsub x y ∧ bsub y x

/-- Rocq: `BachmannFacts.bequiv_refl`. -/
theorem bequiv_refl (x : BOrd.{u}) : BEquiv x x := ⟨bsub_refl x, bsub_refl x⟩

/-- Rocq: `BachmannFacts.bequiv_sym`. -/
theorem bequiv_sym {x y : BOrd.{u}} (H : BEquiv x y) : BEquiv y x := ⟨H.2, H.1⟩

/-- Rocq: `BachmannFacts.bequiv_trans`. -/
theorem bequiv_trans {x y z : BOrd.{u}} (H1 : BEquiv x y) (H2 : BEquiv y z) : BEquiv x z :=
  ⟨bsub_trans H1.1 H2.1, bsub_trans H2.2 H1.2⟩

/-- Rocq: `BachmannFacts.bequiv_embed`. -/
theorem bequiv_embed (ξ ξ' : Ordinal.{u}) (H : ξ ≈ ξ') : BEquiv (embed ξ) (embed ξ') :=
  ⟨bsub_embed _ _ H.le, bsub_embed _ _ H.ge⟩

/-- Rocq: `BachmannFacts.bequiv_badd`. -/
theorem bequiv_badd (x x' y y' : BOrd.{u}) (Hx : BEquiv x x') (Hy : BEquiv y y') : BEquiv (badd x y) (badd x' y') :=
  ⟨bsub_trans (bsub_badd_l _ _ Hx.1 _) (bsub_badd_r _ _ _ Hy.1), bsub_trans (bsub_badd_l _ _ Hx.2 _) (bsub_badd_r _ _ _ Hy.2)⟩

/-- Rocq: `BachmannFacts.bequiv_bmul`. -/
theorem bequiv_bmul (x x' y y' : BOrd.{u}) (Hx : BEquiv x x') (Hy : BEquiv y y') : BEquiv (bmul x y) (bmul x' y') :=
  ⟨bsub_trans (bsub_bmul_l _ _ Hx.1 _) (bsub_bmul_r _ _ _ Hy.1), bsub_trans (bsub_bmul_l _ _ Hx.2 _) (bsub_bmul_r _ _ _ Hy.2)⟩

/-- Rocq: `BachmannFacts.bequiv_bexpΩ`. -/
theorem bequiv_bexpΩ (x x' : BOrd.{u}) (H : BEquiv x x') : BEquiv (bexpΩ x) (bexpΩ x') :=
  ⟨bsub_bexpΩ _ _ H.1, bsub_bexpΩ _ _ H.2⟩

/-- `0 + x` is `x`. Rocq: `BachmannFacts.bequiv_badd_zero_l`. -/
theorem bequiv_badd_zero_l (x : BOrd.{u}) : BEquiv (badd bzero x) x :=
  bsub_badd_empty_l bzero (fun e => (nomatch e)) (fun e => (nomatch e)) x

/-- `x + 0` is `x`. Rocq: `BachmannFacts.bequiv_badd_zero_r`. -/
theorem bequiv_badd_zero_r (x : BOrd.{u}) : BEquiv (badd x bzero) x := by
  cases x with
  | bnode A g C h =>
  refine ⟨⟨fun s => ?_, fun c => ?_⟩, ⟨fun a => ⟨.inl a, bsub_refl _⟩, fun c => ⟨.inl c, fun _ => bsub_refl _⟩⟩⟩
  · match s with
    | .inl a => exact ⟨a, bsub_refl _⟩
    | .inr e => exact nomatch e
  · match c with
    | .inl c => exact ⟨c, fun _ => bsub_refl _⟩
    | .inr e => exact nomatch e

/-- `Ω^0 = 1` has the single small child 0 and no families.
Rocq: `BachmannFacts.bexpΩ_bzero_small`. -/
theorem bexpΩ_bzero_small (t : bsmall (bexpΩ bzero.{u})) : bsmallSz (bexpΩ bzero) t = bzero :=
  match t with
  | .inl _ => rfl
  | .inr (.inl ⟨e, _⟩) => nomatch e
  | .inr (.inr e) => nomatch e

/-- Rocq: `BachmannFacts.bexpΩ_bzero_big`. -/
theorem bexpΩ_bzero_big (t : bbig (bexpΩ bzero.{u})) : False :=
  match t with
  | .inl e => nomatch e
  | .inr (.inl ⟨e, _⟩) => nomatch e
  | .inr (.inr e) => nomatch e

/-- Rocq: `BachmannFacts.embed_big`. -/
theorem embed_big (ξ : Ordinal.{u}) (c : bbig (embed ξ)) : False := by
  cases ξ; exact nomatch c

private theorem embed_small_bsub (o : Ordinal.{u}) (j : bsmall (embed o)) : bsub (bsmallSz (embed o) j) (embed o) := by
  cases o with
  | mk Y m => exact bsub_embed _ _ (le_of_lt (index_lt (mk Y m) j))

/-- `Ω^0·ξ` is `ξ`. Rocq: `BachmannFacts.bequiv_one_mul`. -/
theorem bequiv_one_mul (ξ : Ordinal.{u}) : BEquiv (bmul (bexpΩ bzero) (embed ξ)) (embed ξ) := by
  induction ξ with
  | mk X k ih =>
  refine ⟨bsub_intro _ _ (fun s => ?_) (fun c => ?_), bsub_intro _ _ (fun x => ?_) (fun e => (nomatch e))⟩
  · match s with
    | .inl ⟨x, s⟩ =>
      refine ⟨x, ?_⟩
      show bsub (bsmallSz (badd (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero)) s) (embed (k x))
      match badd_small_cases (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero) s with
      | .inl ⟨a', E⟩ =>
        rw [E]
        obtain ⟨j, hj⟩ := bsub_small _ _ (ih x).1 a'
        exact bsub_trans hj (embed_small_bsub _ j)
      | .inr ⟨b, E⟩ =>
        rw [E, bexpΩ_bzero_small]
        exact bsub_trans (bequiv_badd_zero_r _).1 (ih x).1
    | .inr e => exact nomatch e
  · match c with
    | .inl ⟨x, c⟩ =>
      match badd_big_cases (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero) c with
      | .inl ⟨c', _⟩ =>
        obtain ⟨d, _⟩ := bsub_big _ _ (ih x).1 c'
        exact (embed_big _ d).elim
      | .inr ⟨d, _⟩ => exact (bexpΩ_bzero_big d).elim
    | .inr e => exact nomatch e
  · obtain ⟨t0, Ht0⟩ := bexpΩ_small_zero bzero.{u}
    obtain ⟨s, Hs⟩ := badd_small_r (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero) t0
    obtain ⟨t, Ht⟩ := bmul_small_r (bexpΩ bzero) (embed (mk X k)) x s
    refine ⟨t, ?_⟩
    rw [Ht]
    show bsub (embed (k x)) (bsmallSz (badd (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero)) s)
    rw [Hs, Ht0]
    exact bsub_trans (ih x).2 (bequiv_badd_zero_r _).2

/-! ## Transferring representations along `BEquiv` -/

/-- Rocq: `BachmannFacts.BRep_bequiv`. -/
theorem BRep_bequiv (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (T T' : BOrd.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (H : BEquiv T T') (HT : BFam T) (HT' : BFam T') (HR : BRep f T G) : BRep f T' G :=
  BRep_bsub_equiv f hf T T' G H.1 H.2 HT HT' HR

/-! ## The base `1+x` -/

/-- Below `Ω`, with base `1+x`, `φ_α(y) = ω^α + y`. Rocq: `BachmannFacts.bphi_onePlus_embed`. -/
theorem bphi_onePlus_embed (α y : Ordinal.{u}) (hα : Complete α) (hy : Complete y) :
    bphi (fun x => 1 + x) (embed α) y ≈ ω ^ α + y :=
  equiv_trans (bphi_embed _ onePlus_normal α hα y hy) (veblen_onePlus α hα y hy)

/-- A node with a component has values that are fixpoints of `1+x`, i.e.,
infinite. Rocq: `BachmannFacts.bphi_onePlus_absorb`. -/
theorem bphi_onePlus_absorb (T : BOrd.{u}) (y : Ordinal.{u}) (HT : BGood (fun x => 1 + x) T)
    (Hi : Nonempty (bsmall T ⊕ bbig T)) (hy : Complete y) :
    1 + bphi (fun x => 1 + x) T y ≈ bphi (fun x => 1 + x) T y :=
  equiv_intro (bphi_fix_base' onePlus_normal T y HT Hi hy) (le_add_left _ _)

/-! ## z-relative strict reachability

`zlt z x y`: `x` lies strictly below a tree `D` that is reachable from `y`
through small children and family members at arguments at most `z`. If `z` is
a common fixpoint of `y`'s components, then `φ_x` fixes `z`. -/

/-- Rocq: `BachmannFacts.zlt`. -/
def zlt (z : Ordinal.{u}) (x y : BOrd.{u}) : Prop := ∃ D, bslt x D ∧ bleZ z D y

/-- Rocq: `BachmannFacts.zlt_bslt`. -/
theorem zlt_bslt (z : Ordinal.{u}) (x y : BOrd.{u}) (H : bslt x y) : zlt z x y := ⟨y, H, .sub _ (bsub_refl _)⟩

/-- Rocq: `BachmannFacts.zlt_mono_r`. -/
theorem zlt_mono_r (z : Ordinal.{u}) (x y y' : BOrd.{u}) (H : zlt z x y) (Hy : bsub y y') : zlt z x y' :=
  let ⟨D, h1, h2⟩ := H
  ⟨D, h1, bleZ_mono_r _ _ _ _ h2 Hy⟩

/-- Rocq: `BachmannFacts.zlt_mono_l`. -/
theorem zlt_mono_l (z : Ordinal.{u}) (x x' y : BOrd.{u}) (Hx : bsub x' x) (H : zlt z x y) : zlt z x' y :=
  let ⟨D, h1, h2⟩ := H
  ⟨D, bslt_bsub_l _ _ _ Hx h1, h2⟩

/-- Rocq: `BachmannFacts.zlt_shift`. -/
theorem zlt_shift (z : Ordinal.{u}) (w x y : BOrd.{u}) (H : zlt z x y) : zlt z (badd w x) (badd w y) :=
  let ⟨D, h1, h2⟩ := H
  ⟨badd w D, bslt_badd_r _ _ _ h1, bleZ_shift _ _ _ _ h2⟩

/-- Rocq: `BachmannFacts.zlt_big`. -/
theorem zlt_big (z : Ordinal.{u}) (x y : BOrd.{u}) (t : bbig y) (ξ : Ordinal.{u}) (H : zlt z x (bbigSz y t ξ))
    (Hξ : ξ ≤ z) : zlt z x y :=
  let ⟨D, h1, h2⟩ := H
  ⟨D, h1, .big _ t ξ Hξ h2⟩

/-- Rocq: `BachmannFacts.zlt_nest`. -/
theorem zlt_nest (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (z : Ordinal.{u}) (x y : BOrd.{u})
    (H : zlt z x y) (Hg : BGood f y) (Hfam : BFam y) (Hz : Complete z) (Hfix : BFix f y z) : bphi f x z ≤ z :=
  let ⟨D, h1, h2⟩ := H
  bleZ_nest f hf z D y x h2 h1 y (bsub_refl y) Hg Hfam Hz Hfix

/-! ## Indices below `Ω^Ω`

An index below `Ω^Ω` is a list of pairs `(ζ, c)` standing for
`Ω^{ζ₁}·c₁ + … + Ω^{ζₙ}·cₙ` with small `ζ` and `c`. -/

/-- Rocq: `BachmannFacts.oterm`. -/
def oterm (p : Ordinal.{u} × Ordinal.{u}) : BOrd.{u} := bmul (bexpΩ (embed p.1)) (embed p.2)

/-- Rocq: `BachmannFacts.osum`. -/
def osum : List (Ordinal.{u} × Ordinal.{u}) → BOrd.{u}
  | [] => bzero
  | p :: l => badd (oterm p) (osum l)

/-- Rocq: `BachmannFacts.ofold`. -/
def ofold (acc : BOrd.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) : BOrd.{u} :=
  List.foldl (fun acc p => badd acc (oterm p)) acc l

/-- Rocq: `BachmannFacts.bequiv_badd_assoc`. -/
theorem bequiv_badd_assoc (a b c : BOrd.{u}) : BEquiv (badd (badd a b) c) (badd a (badd b c)) :=
  ⟨badd_assoc_1 a b c, badd_assoc_2 a b c⟩

/-- Rocq: `BachmannFacts.ofold_osum`. -/
theorem ofold_osum : ∀ (l : List (Ordinal.{u} × Ordinal.{u})) (acc : BOrd.{u}), BEquiv (ofold acc l) (badd acc (osum l))
  | [], acc => bequiv_sym (bequiv_badd_zero_r acc)
  | p :: l, acc => bequiv_trans (ofold_osum l (badd acc (oterm p))) (bequiv_badd_assoc _ _ _)

/-- Exponents strictly decreasing and bounded by `ζ`; coefficients positive.
Rocq: `BachmannFacts.odesc`. -/
def ODesc (ζ : Ordinal.{u}) : List (Ordinal.{u} × Ordinal.{u}) → Prop
  | [] => True
  | p :: l => p.1 < ζ ∧ 0 < p.2 ∧ ODesc p.1 l

/-- Rocq: `BachmannFacts.onormal`. -/
def ONormal : List (Ordinal.{u} × Ordinal.{u}) → Prop
  | [] => True
  | p :: l => 0 < p.2 ∧ ODesc p.1 l

/-- Rocq: `BachmannFacts.odesc_onormal`. -/
theorem odesc_onormal (ζ : Ordinal.{u}) : ∀ l, ODesc ζ l → ONormal l
  | [], _ => trivial
  | _ :: _, H => ⟨H.2.1, H.2.2⟩

/-- Rocq: `BachmannFacts.ocoef_lt`. -/
def OCoefLt (z : Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) : Prop := Each (fun p => p.2 < z) l

/-- Rocq: `BachmannFacts.oinf`. -/
def OInf (z : Ordinal.{u}) : Prop := ∀ n : Nat, ofNat n ≤ z

/-- Rocq: `BachmannFacts.oterm_pos`. -/
theorem oterm_pos (e c : Ordinal.{u}) (Hc : 0 < c) : bpos (oterm (e, c)) :=
  bslt_bsub_r _ _ _ (bpos_bexpΩ _) (bsub_P_Pz _ c Hc)

/-- `P·c + P` lies below `P·(c+1)`. Rocq: `BachmannFacts.bsub_mul_succ`. -/
theorem bsub_mul_succ (P : BOrd.{u}) (c : Ordinal.{u}) : bsub (badd (bmul P (embed c)) P) (bmul P (embed (succ c))) :=
  bsub_bmul_step P (embed (succ c)) ⟨⟩

/-- A sum with exponents below `ζ`, and coefficients below `z`, is
z-reachably below `Ω^ζ`. Rocq: `BachmannFacts.osum_below`. -/
theorem osum_below : ∀ (l : List (Ordinal.{u} × Ordinal.{u})) (ζ z : Ordinal.{u}), ODesc ζ l → OCoefLt z l →
    zlt z (osum l) (bexpΩ (embed ζ))
  | [], _, z, _, _ => zlt_bslt z _ _ (bpos_bexpΩ _)
  | (e, c) :: l, ζ, z, ⟨he, _, hd⟩, ⟨hcz, hc⟩ => by
    cases ζ with
    | mk Z k =>
    obtain ⟨j, hj⟩ := lt_elim he
    obtain ⟨t, ht⟩ := bexpΩ_fam_s (embed (mk Z k)) j
    refine zlt_big z _ _ t (succ c) ?_ (succ_least hcz)
    rw [ht]
    exact zlt_mono_r _ _ _ _ (zlt_mono_r _ _ _ _ (zlt_shift z _ _ _ (osum_below l e z hd hc)) (bsub_mul_succ _ c))
      (bsub_bmul_l _ _ (bsub_bexpΩ _ _ (bsub_embed _ _ hj)) _)

/-- Lexicographic order on Ω-Cantor normal forms below `Ω^Ω`.
Rocq: `BachmannFacts.olt`. -/
inductive olt : List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → Prop
  /-- Rocq: `BachmannFacts.olt_nil`. -/
  | nil (p : Ordinal.{u} × Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) : olt [] (p :: l)
  /-- Rocq: `BachmannFacts.olt_exp`. -/
  | exp (e c : Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) (e' c' : Ordinal.{u})
      (l' : List (Ordinal.{u} × Ordinal.{u})) : e < e' → olt ((e, c) :: l) ((e', c') :: l')
  /-- Rocq: `BachmannFacts.olt_coef`. -/
  | coef (e c : Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) (e' c' : Ordinal.{u})
      (l' : List (Ordinal.{u} × Ordinal.{u})) : e ≈ e' → c < c' → olt ((e, c) :: l) ((e', c') :: l')
  /-- Rocq: `BachmannFacts.olt_tail`. -/
  | tail (e c : Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) (e' c' : Ordinal.{u})
      (l' : List (Ordinal.{u} × Ordinal.{u})) : e ≈ e' → c ≈ c' → olt l l' → olt ((e, c) :: l) ((e', c') :: l')

/-- Rocq: `BachmannFacts.osum_pos`. -/
theorem osum_pos (p : Ordinal.{u} × Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) (H : 0 < p.2) :
    bpos (osum (p :: l)) :=
  bslt_bsub_r _ _ _ (oterm_pos p.1 p.2 H) (bsub_le_badd _ _)

/-- Rocq: `BachmannFacts.bsub_oterm`. -/
theorem bsub_oterm (e c e' c' : Ordinal.{u}) (He : e ≤ e') (Hc : c ≤ c') : bsub (oterm (e, c)) (oterm (e', c')) :=
  bsub_trans (bsub_bmul_l _ _ (bsub_bexpΩ _ _ (bsub_embed _ _ He)) _) (bsub_bmul_r _ _ _ (bsub_embed _ _ Hc))

/-! ## Semantic consequences -/

/-- Values of a node with a component are common fixpoints of `f` and the
node's components. Rocq: `BachmannFacts.bfix_value_full`. -/
theorem bfix_value_full (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (y : BOrd.{u}) (w : Ordinal.{u})
    (Hy : BGood f y) (Hi : Nonempty (bsmall y ⊕ bbig y)) (Hw : Complete w) : BFix f y (bphi f y w) :=
  ⟨bphi_fix_base' hf y w Hy Hi Hw, fun a => bphi_fix_small' hf y a w Hy Hw, fun c => bphi_fix_big' hf y c w Hy Hw⟩

/-- If `x` is z-reachably below `y` at a value `z` of `φ_y`, then `z` is a
fixpoint of `φ_x`. Rocq: `BachmannFacts.zlt_value`. -/
theorem zlt_value (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (x y : BOrd.{u}) (w : Ordinal.{u})
    (H : zlt (bphi f y w) x y) (Hg : BGood f y) (Hfam : BFam y) (Hi : Nonempty (bsmall y ⊕ bbig y))
    (Hw : Complete w) : bphi f x (bphi f y w) ≤ bphi f y w :=
  zlt_nest f hf _ x y H Hg Hfam (bphi_complete hf y w Hg Hw) (bfix_value_full f hf y w Hg Hi Hw)

/-- `φ` depends only on the tree up to `BEquiv`. Rocq: `BachmannFacts.bphi_bequiv`. -/
theorem bphi_bequiv (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (T T' : BOrd.{u})
    (y : Ordinal.{u}) (H : BEquiv T T') (HT : BFam T) (HT' : BFam T') : bphi f T y ≈ bphi f T' y :=
  equiv_intro ((bphi_mono_index f hf T' HT').2 _ H.1 y) ((bphi_mono_index f hf T HT).2 _ H.2 y)

/-- Entrywise equal indices. Rocq: `BachmannFacts.oeq`. -/
inductive oeq : List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → Prop
  /-- Rocq: `BachmannFacts.oeq_nil`. -/
  | nil : oeq [] []
  /-- Rocq: `BachmannFacts.oeq_cons`. -/
  | cons (e c : Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u})) (e' c' : Ordinal.{u})
      (l' : List (Ordinal.{u} × Ordinal.{u})) : e ≈ e' → c ≈ c' → oeq l l' → oeq ((e, c) :: l) ((e', c') :: l')

/-- Rocq: `BachmannFacts.bfam_oterm`. -/
theorem bfam_oterm (p : Ordinal.{u} × Ordinal.{u}) : BFam (oterm p) :=
  bfam_bmul _ _ (bfam_bexpΩ _ (bfam_embed _)) (bfam_embed _)

/-- Rocq: `BachmannFacts.bfam_osum`. -/
theorem bfam_osum : ∀ l : List (Ordinal.{u} × Ordinal.{u}), BFam (osum l)
  | [] => bfam_bzero
  | p :: l => bfam_badd _ _ (bfam_oterm p) (bfam_osum l)

/-- Rocq: `BachmannFacts.bfam_ofold`. -/
theorem bfam_ofold : ∀ (l : List (Ordinal.{u} × Ordinal.{u})) (acc : BOrd.{u}), BFam acc → BFam (ofold acc l)
  | [], _, H => H
  | p :: l, acc, H => bfam_ofold l (badd acc (oterm p)) (bfam_badd _ _ H (bfam_oterm p))

/-! ## Indices below `Ω^Ω` and Klammersymbols

Adding the summand `Ω^ζ·c` to an index adds the column `(1+ζ, c)` to the
Klammersymbol it represents (`bach_bexpΩ_rep`). -/

/-- Rocq: `BachmannFacts.ocols`. -/
def ocols (l : List (Ordinal.{u} × Ordinal.{u})) : List (Ordinal.{u} × Ordinal.{u}) := l.map fun p => (1 + p.1, p.2)

/-- Rocq: `BachmannFacts.ofold_rep`. -/
theorem ofold_rep (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ (l : List (Ordinal.{u} × Ordinal.{u})) (acc : BOrd.{u}) (G : Ordinal.{u} → Ordinal.{u}), BFam acc →
      BRep f acc G → Each (fun p => Complete p.1 ∧ Complete p.2) l → BRep f (ofold acc l) (schutteMatrix G (ocols l))
  | [], _, _, _, HR, _ => HR
  | (e, c) :: l, acc, G, Hacc, HR, ⟨⟨He, Hc⟩, Hl⟩ =>
    ofold_rep f hf l (badd acc (oterm (e, c))) (schutteColumn G (1 + e) c) (bfam_badd _ _ Hacc (bfam_oterm _))
      (bach_bexpΩ_rep f hf e He acc G Hacc HR c Hc) Hl

/-- Entrywise equal Klammersymbols. Rocq: `BachmannFacts.meq`. -/
inductive meq : List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → Prop
  /-- Rocq: `BachmannFacts.meq_nil`. -/
  | nil : meq [] []
  /-- Rocq: `BachmannFacts.meq_cons`. -/
  | cons (b a : Ordinal.{u}) (m : List (Ordinal.{u} × Ordinal.{u})) (b' a' : Ordinal.{u})
      (m' : List (Ordinal.{u} × Ordinal.{u})) : b ≈ b' → a ≈ a' → meq m m' → meq ((b, a) :: m) ((b', a') :: m')

/-- Entrywise equal Klammersymbols denote the same function.
Rocq: `BachmannFacts.schutte_matrix_meq`. -/
theorem schutte_matrix_meq (m m' : List (Ordinal.{u} × Ordinal.{u})) (H : meq m m') :
    ∀ f : Ordinal.{u} → Ordinal.{u}, (∀ x y, x ≤ y → f x ≤ f y) → ∀ x, schutteMatrix f m x ≈ schutteMatrix f m' x := by
  induction H with
  | nil => exact fun _ _ x => equiv_refl _
  | cons b a m b' a' m' Hb Ha _ ih =>
    intro f hf x
    have hcol : ∀ x y, x ≤ y → schutteColumn f b a x ≤ schutteColumn f b a y := fun x y h =>
      schutte_column_monotone f b a x a y hf (le_refl a) h
    have hcol' : ∀ x y, x ≤ y → schutteColumn f b' a' x ≤ schutteColumn f b' a' y := fun x y h =>
      schutte_column_monotone f b' a' x a' y hf (le_refl a') h
    refine equiv_trans (ih _ hcol x) (equiv_intro ?_ ?_)
    · exact schutte_matrix_monotone_func m' _ _ x hcol hcol'
        (fun y => schutte_column_monotone_full f f b a y b' a' y hf hf (fun _ => le_refl _) Hb.le Ha.le (le_refl y))
    · exact schutte_matrix_monotone_func m' _ _ x hcol' hcol
        (fun y => schutte_column_monotone_full f f b' a' y b a y hf hf (fun _ => le_refl _) Hb.ge Ha.ge (le_refl y))

/-! ## Reachability through exponents -/

/-- Rocq: `BachmannFacts.zlt_bleZ`. -/
theorem zlt_bleZ (z : Ordinal.{u}) (x y w : BOrd.{u}) (H : zlt z x y) (Hw : bleZ z y w) : zlt z x w :=
  let ⟨D, h1, h2⟩ := H
  ⟨D, h1, bleZ_trans _ _ _ _ h2 Hw⟩

/-- If `a` is z-reachably below `b`, then `Ω^a·z` is z-reachable from `Ω^b`.
Rocq: `BachmannFacts.zlt_exp`. -/
theorem zlt_exp (z : Ordinal.{u}) (a b : BOrd.{u}) (H : zlt z a b) (Hz : OInf z) :
    bleZ z (bmul (bexpΩ a) (embed z)) (bexpΩ b) :=
  let ⟨D, h1, h2⟩ := H
  bleZ_trans _ _ _ _ (bleZ_exp_lt a D h1 z Hz) (bleZ_exp z _ _ Hz h2)

/-- A value of a node with a component is infinite. Rocq: `BachmannFacts.bphi_value_inf`. -/
theorem bphi_value_inf (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (y : BOrd.{u}) (w : Ordinal.{u})
    (_ : ∀ x, x ≤ f x) (H1 : ∀ x, Complete x → 1 + x ≤ f x) (Hg : BGood f y) (Hi : Nonempty (bsmall y ⊕ bbig y))
    (Hw : Complete w) : OInf (bphi f y w) := fun n =>
  fix_onePlus_finite (fun x => 1 + x) onePlus_normal _ (bphi_complete hf y w Hg Hw)
    (le_trans (H1 _ (bphi_complete hf y w Hg Hw)) (bphi_fix_base' hf y w Hg Hi Hw)) n

/-! ## Dominance through strict contexts

A context is a tree with an ordinal hole that is canonical at complete
arguments and strictly increasing in the structural order `bslt`. Along a
context, `ξ ↦ φ_{C ξ}(0)` is strictly increasing, hence at least `ξ`. Contexts
are built from `embed` by adding on the left, multiplying by a positive tree on
the left, and exponentiating; together with `bsub`-monotonicity this places
every coefficient of an index below `φ_T(0)`. -/

/-- Rocq: `BachmannFacts.bctx`. -/
def BCtx (C : Ordinal.{u} → BOrd.{u}) : Prop :=
  (∀ ξ, Complete ξ → BCd (C ξ)) ∧ ∀ ξ ξ', Complete ξ' → ξ < ξ' → bslt (C ξ) (C ξ')

/-- Rocq: `BachmannFacts.bctx_dom`. -/
theorem bctx_dom (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (C : Ordinal.{u} → BOrd.{u}) (HC : BCtx C) :
    ∀ ξ, Complete ξ → ξ ≤ bphi f (C ξ) 0 := by
  intro ξ
  induction ξ with
  | mk X g ih =>
  intro hc
  have hg := bcanon_good f hf _ (HC.1 _ hc).1 (HC.1 _ hc).2
  exact le_intro fun j => lt_of_le_of_lt (ih j (complete_subord hc j))
    (bphi_strict f hf _ _ (HC.2 _ _ hc (index_lt (mk X g) j)) hg.2 hg.1)

/-- Rocq: `BachmannFacts.bslt_embed`. -/
theorem bslt_embed (ξ ξ' : Ordinal.{u}) (H : ξ < ξ') : bslt (embed ξ) (embed ξ') := by
  cases ξ' with
  | mk X k =>
  obtain ⟨j, hj⟩ := lt_elim H
  exact .small (embed (mk X k)) j (bsub_embed ξ (k j) hj)

/-- Rocq: `BachmannFacts.bctx_embed`. -/
theorem bctx_embed : BCtx embed.{u} := ⟨bcd_embed, fun ξ ξ' _ h => bslt_embed ξ ξ' h⟩

/-- Rocq: `BachmannFacts.bctx_add`. -/
theorem bctx_add (A : BOrd.{u}) (C : Ordinal.{u} → BOrd.{u}) (HA : BCd A) (HC : BCtx C) : BCtx fun ξ => badd A (C ξ) :=
  ⟨fun ξ hξ => bcd_badd _ _ HA (HC.1 ξ hξ), fun ξ ξ' hc hlt => bslt_badd_r _ _ _ (HC.2 ξ ξ' hc hlt)⟩

/-- Rocq: `BachmannFacts.bctx_mul`. -/
theorem bctx_mul (P : BOrd.{u}) (C : Ordinal.{u} → BOrd.{u}) (HP : BCd P) (Hp : bpos P) (HC : BCtx C) :
    BCtx fun ξ => bmul P (C ξ) :=
  ⟨fun ξ hξ => bcd_bmul _ _ HP Hp (HC.1 ξ hξ), fun ξ ξ' hc hlt => bslt_bmul_r _ Hp _ _ (HC.2 ξ ξ' hc hlt)⟩

/-- Rocq: `BachmannFacts.bctx_exp`. -/
theorem bctx_exp (C : Ordinal.{u} → BOrd.{u}) (HC : BCtx C) : BCtx fun ξ => bexpΩ (C ξ) :=
  ⟨fun ξ hξ => bcd_bexpΩ _ (HC.1 ξ hξ), fun ξ ξ' hc hlt => bslt_bexpΩ _ _ (HC.2 ξ ξ' hc hlt)⟩

/-! ## The children of `Ω^e·γ` -/

/-- Rocq: `BachmannFacts.bexpΩ_small_all`. -/
theorem bexpΩ_small_all (y : BOrd.{u}) (t : bsmall (bexpΩ y)) : bsmallSz (bexpΩ y) t = bzero := by
  cases y with
  | bnode B g D h =>
  match t with
  | .inl _ => rfl
  | .inr (.inl ⟨_, .inl ⟨e, _⟩⟩) => exact nomatch e
  | .inr (.inl ⟨_, .inr e⟩) => exact nomatch e
  | .inr (.inr e) => exact nomatch e

/-- Rocq: `BachmannFacts.bexpΩ_big_cases`. -/
theorem bexpΩ_big_cases (y : BOrd.{u}) (k : bbig (bexpΩ y)) :
    (∃ q, ∀ ξ, bbigSz (bexpΩ y) k ξ = bmul (bexpΩ (bsmallSz y q)) (embed ξ)) ∨
      (∃ d, ∀ ξ, bbigSz (bexpΩ y) k ξ = bexpΩ (bbigSz y d ξ)) := by
  cases y with
  | bnode B g D h =>
  match k with
  | .inl e => exact nomatch e
  | .inr (.inl ⟨_, .inl ⟨e, _⟩⟩) => exact nomatch e
  | .inr (.inl ⟨b, .inr _⟩) => exact .inl ⟨b, fun _ => rfl⟩
  | .inr (.inr d) => exact .inr ⟨d, fun _ => rfl⟩

/-- The children of `E·γ₀` are `E·γ + K`, for `γ < γ₀` and `K` a child of `E`.
Rocq: `BachmannFacts.mul_small_form`. -/
theorem mul_small_form (E : BOrd.{u}) : ∀ (γ0 : Ordinal.{u}) (a : bsmall (bmul E (embed γ0))),
    ∃ γ, γ < γ0 ∧ ∃ k, bsmallSz (bmul E (embed γ0)) a = badd (bmul E (embed γ)) (bsmallSz E k) := by
  intro γ0
  induction γ0 with
  | mk G g ih =>
  intro a
  match a with
  | .inl ⟨j, s⟩ =>
    show ∃ γ, γ < mk G g ∧ ∃ k, bsmallSz (badd (bmul E (embed (g j))) E) s = badd (bmul E (embed γ)) (bsmallSz E k)
    match badd_small_cases (bmul E (embed (g j))) E s with
    | .inl ⟨a', Ea⟩ =>
      obtain ⟨γ, hγ, k, hk⟩ := ih j a'
      exact ⟨γ, lt_trans hγ (index_lt (mk G g) j), k, by rw [Ea]; exact hk⟩
    | .inr ⟨k, Ek⟩ => exact ⟨g j, index_lt (mk G g) j, k, Ek⟩
  | .inr e => exact nomatch e

/-- Rocq: `BachmannFacts.mul_big_form`. -/
theorem mul_big_form (E : BOrd.{u}) : ∀ (γ0 : Ordinal.{u}) (d : bbig (bmul E (embed γ0))),
    ∃ γ, γ < γ0 ∧ ∃ k, ∀ ξ, bbigSz (bmul E (embed γ0)) d ξ = badd (bmul E (embed γ)) (bbigSz E k ξ) := by
  intro γ0
  induction γ0 with
  | mk G g ih =>
  intro d
  match d with
  | .inl ⟨j, s⟩ =>
    show ∃ γ, γ < mk G g ∧ ∃ k, ∀ ξ, bbigSz (badd (bmul E (embed (g j))) E) s ξ = badd (bmul E (embed γ)) (bbigSz E k ξ)
    match badd_big_cases (bmul E (embed (g j))) E s with
    | .inl ⟨a', Ea⟩ =>
      obtain ⟨γ, hγ, k, hk⟩ := ih j a'
      exact ⟨γ, lt_trans hγ (index_lt (mk G g) j), k, fun ξ => by rw [Ea]; exact hk ξ⟩
    | .inr ⟨k, Ek⟩ => exact ⟨g j, index_lt (mk G g) j, k, Ek⟩
  | .inr e => exact nomatch e

/-- Rocq: `BachmannFacts.mul_small_back`. -/
theorem mul_small_back (E : BOrd.{u}) (γ0 : Ordinal.{u}) (j : γ0) (k : bsmall E) :
    ∃ a, bsmallSz (bmul E (embed γ0)) a = badd (bmul E (embed (γ0 j))) (bsmallSz E k) := by
  cases γ0 with
  | mk G g =>
  obtain ⟨s, Hs⟩ := badd_small_r (bmul E (embed (g j))) E k
  obtain ⟨t, Ht⟩ := bmul_small_r E (embed (mk G g)) j s
  exact ⟨t, by rw [Ht]; exact Hs⟩

/-- Rocq: `BachmannFacts.mul_big_back`. -/
theorem mul_big_back (E : BOrd.{u}) (γ0 : Ordinal.{u}) (j : γ0) (k : bbig E) :
    ∃ d, ∀ ξ, bbigSz (bmul E (embed γ0)) d ξ = badd (bmul E (embed (γ0 j))) (bbigSz E k ξ) := by
  cases γ0 with
  | mk G g =>
  obtain ⟨s, Hs⟩ := badd_big_r (bmul E (embed (g j))) E k
  obtain ⟨t, Ht⟩ := bmul_big_r E (embed (mk G g)) j s
  exact ⟨t, fun ξ => by rw [Ht]; exact Hs ξ⟩

/-- Rocq: `BachmannFacts.bsub_mul_zero`. -/
theorem bsub_mul_zero (x : BOrd.{u}) : bsub (bmul x (embed 0)) bzero :=
  bsub_intro _ _ (fun s => match s with
      | .inl ⟨e, _⟩ => nomatch e
      | .inr e => nomatch e)
    (fun c => match c with
      | .inl ⟨e, _⟩ => nomatch e
      | .inr e => nomatch e)

end Bachmann

end ConstructiveOrdinals
