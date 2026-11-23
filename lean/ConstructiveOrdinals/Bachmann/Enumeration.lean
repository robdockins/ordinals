import ConstructiveOrdinals.Bachmann.Facts
import ConstructiveOrdinals.Schutte.Absorb

/-!
# The enumerator: interpolation, change of base, merges, shifted enumerations

Facts about `cfe` and `bphi` used by the notation system: every value lies
below a word of components, enumerators for different bases are comparable,
equal exponents merge, and an enumeration cut off above a threshold is a
shifted enumeration.

Ported from the Rocq file `BachmannEnumeration.v`.

Lean notes:

- Each lemma of a Rocq section takes the section variables and hypotheses
  that its proof uses as explicit arguments.
- The section-local definitions of `cfe_offset` (the two fixpoint predicates
  and the two inhabitation decisions) are unfolded in the statements.
  Rocq: `BachmannEnumeration.fixI`, `BachmannEnumeration.fixJ`,
  `BachmannEnumeration.decI`, `BachmannEnumeration.decJ`.
- `btower_small` is a definition (Rocq's `Defined`), built from
  `bexpΩ_small_one`.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-! ## Interpolation for the common-fixpoint enumerator

Everything below a value `cfe y` lies below `f y`, or below a finite
composition of `f` and the components ("a word") applied either to 0 or to the
successor of an earlier value `cfe (y j)`. The starting points lie below
`cfe y`, and in the second case there is a component, so `cfe y` is a fixpoint
of `f` and of every component; hence the whole composition stays below
`cfe y`. This is the semantic half of interpolation for notations built on
`bphi`. -/

/-- The value of a word of components. Rocq: `BachmannEnumeration.wev`. -/
def wev (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) :
    List (Option I) → Ordinal.{u} → Ordinal.{u}
  | [], x => x
  | none :: w, x => f (wev f I F w x)
  | some i :: w, x => F i (wev f I F w x)

/-- Rocq: `BachmannEnumeration.wev_monotone`. -/
theorem wev_monotone (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ (w : List (Option I)) (x y : Ordinal.{u}), x ≤ y → wev f I F w x ≤ wev f I F w y
  | [], _, _, h => h
  | none :: w, _, _, h => hf.monotone _ _ (wev_monotone f hf I F HF w _ _ h)
  | some i :: w, _, _, h => (HF i).monotone _ _ (wev_monotone f hf I F HF w _ _ h)

/-- Rocq: `BachmannEnumeration.wev_complete`. -/
theorem wev_complete (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ (w : List (Option I)) (x : Ordinal.{u}), Complete x → Complete (wev f I F w x)
  | [], _, h => h
  | none :: w, _, h => hf.complete _ (wev_complete f hf I F HF w _ h)
  | some i :: w, _, h => (HF i).complete _ (wev_complete f hf I F HF w _ h)

/-- Rocq: `BachmannEnumeration.wev_continuous`. -/
theorem wev_continuous (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ w : List (Option I), ScottContinuous (wev f I F w)
  | [] => fun _ _ _ _ _ => le_refl _
  | o :: w => fun A g a0 hdir hc => by
    have hdir' : Directed A fun a => wev f I F w (g a) := fun a1 a2 =>
      let ⟨a', h1, h2⟩ := hdir a1 a2
      ⟨a', wev_monotone f hf I F HF w _ _ h1, wev_monotone f hf I F HF w _ _ h2⟩
    have hc' : ∀ a, Complete (wev f I F w (g a)) := fun a => wev_complete f hf I F HF w _ (hc a)
    match o with
    | some i =>
      exact le_trans ((HF i).monotone _ _ (wev_continuous f hf I F HF w A g a0 hdir hc))
        ((HF i).continuous A _ a0 hdir' hc')
    | none =>
      exact le_trans (hf.monotone _ _ (wev_continuous f hf I F HF w A g a0 hdir hc)) (hf.continuous A _ a0 hdir' hc')

/-- Rocq: `BachmannEnumeration.wev_app`. -/
theorem wev_app (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) :
    ∀ (w1 w2 : List (Option I)) (x : Ordinal.{u}), wev f I F (w1 ++ w2) x = wev f I F w1 (wev f I F w2 x)
  | [], _, _ => rfl
  | none :: w1, w2, x => congrArg f (wev_app f I F w1 w2 x)
  | some i :: w1, w2, x => congrArg (F i) (wev_app f I F w1 w2 x)

/-- Rocq: `BachmannEnumeration.word`. -/
def word {I : Type u} (p : I × List I) : List (Option I) := some p.1 :: (p.2.map some ++ [none])

/-- Rocq: `BachmannEnumeration.wev_comps`. -/
theorem wev_comps (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) :
    ∀ (L : List I) (x : Ordinal.{u}), wev f I F (L.map some ++ [none]) x = comps f I F L x
  | [], _ => rfl
  | i :: L, x => congrArg (F i) (wev_comps f I F L x)

/-- Rocq: `BachmannEnumeration.wev_word`. -/
theorem wev_word (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) (p : I × List I)
    (x : Ordinal.{u}) : wev f I F (word p) x = c1 f I F p x :=
  congrArg (F p.1) (wev_comps f I F p.2 x)

/-- Rocq: `BachmannEnumeration.iterw`. -/
def iterw {I : Type u} (p : I × List I) : Nat → List (Option I)
  | 0 => []
  | k + 1 => word p ++ iterw p k

/-- Rocq: `BachmannEnumeration.wev_iterw`. -/
theorem wev_iterw (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) (p : I × List I) :
    ∀ (k : Nat) (x : Ordinal.{u}), wev f I F (iterw p k) x = iterF (c1 f I F p) x k
  | 0, _ => rfl
  | k + 1, x => by
    show wev f I F (word p ++ iterw p k) x = c1 f I F p (iterF (c1 f I F p) x k)
    rw [wev_app, wev_iterw f I F p k x, wev_word]

/-- Rocq: `BachmannEnumeration.cstart`. -/
def cstart (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) (y : Ordinal.{u}) :
    Option y → Ordinal.{u}
  | none => 0
  | some j => succ (cfe f I F (y j))

/-- Rocq: `BachmannEnumeration.cfe_interp`. -/
theorem cfe_interp (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (y i : Ordinal.{u}) (hy : Complete y)
    (hi : i < cfe f I F y) :
    i < f y ∨ (Nonempty I ∧ ∃ (o : Option y) (w : List (Option I)),
      i < wev f I F w (cstart f I F y o) ∧ cstart f I F y o ≤ cfe f I F y) := by
  rw [cfe_unroll f I F y] at hi
  obtain ⟨o, ho⟩ := sup_lt hi
  match o, ho with
  | none, ho => exact .inl ho
  | some p, ho =>
    refine .inr ⟨⟨p.1⟩, ?_⟩
    have Hsc : (lim fun j : y => cfe f I F (y j)) ≤ cfe f I F y :=
      le_trans (fixOrd_above _ _) (cfe_ge_term f I F y (some p))
    obtain ⟨k, hk⟩ := sup_lt (show i < fixOrd (c1 f I F p) (lim fun j : y => cfe f I F (y j)) from ho)
    have hk : i < wev f I F (iterw p k.down) (lim fun j : y => cfe f I F (y j)) := by
      rw [wev_iterw]; exact hk
    cases y with
    | mk Y h =>
    obtain ⟨hdir, _, hc⟩ := hy
    have Hdir' : Directed (Option Y) (cstart f I F (mk Y h)) := fun o1 o2 =>
      match o1, o2 with
      | some j1, some j2 =>
        let ⟨j3, h1, h2⟩ := hdir j1 j2
        ⟨some j3, succ_monotone (cfe_monotone f hf I F HF _ _ h1), succ_monotone (cfe_monotone f hf I F HF _ _ h2)⟩
      | some j1, none => ⟨some j1, le_refl _, zero_least _⟩
      | none, some j2 => ⟨some j2, zero_least _, le_refl _⟩
      | none, none => ⟨none, le_refl _, le_refl _⟩
    have Hcs : ∀ o, Complete (cstart f I F (mk Y h) o) := fun o =>
      match o with
      | some j => succ_complete (cfe_complete f hf I F HF _ (hc j))
      | none => zero_complete
    have Hs : (lim fun j : Y => cfe f I F (h j)) ≤ sup (cstart f I F (mk Y h)) :=
      limit_least fun j => lt_of_lt_of_le (succ_lt _) (sup_le (cstart f I F (mk Y h)) (some j))
    have Hk' : i < sup fun o => wev f I F (iterw p k.down) (cstart f I F (mk Y h) o) :=
      lt_of_lt_of_le hk (le_trans (wev_monotone f hf I F HF _ _ _ Hs)
        (wev_continuous f hf I F HF (iterw p k.down) _ _ none Hdir' Hcs))
    obtain ⟨o, ho⟩ := sup_lt Hk'
    refine ⟨o, iterw p k.down, ho, ?_⟩
    match o with
    | some j => exact succ_least (lt_of_lt_of_le (limit_lt (fun j : Y => cfe f I F (h j)) j) Hsc)
    | none => exact zero_least _

/-- The same, for `bphi`: the components of a node are those of `bphi_fam`.
Rocq: `BachmannEnumeration.bphi_interp`. -/
theorem bphi_interp (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (X : BOrd.{u}) (y i : Ordinal.{u})
    (HX : BGood f X) (hy : Complete y) (hi : i < bphi f X y) :
    i < f y ∨ (Nonempty (bsmall X ⊕ bbig X) ∧ ∃ (o : Option y) (w : List (Option (bsmall X ⊕ bbig X))),
      i < wev f _ (bphi_fam f (bsmallSz X) (bbigSz X)) w
          (match o with
           | none => 0
           | some j => succ (bphi f X (y j))) ∧
        (match o with
         | none => 0
         | some j => succ (bphi f X (y j))) ≤ bphi f X y) := by
  cases X with
  | bnode A g C h =>
  match cfe_interp f hf (A ⊕ C) (bphi_fam f g h) (bphi_fam_normal' hf A g C h HX) y i hy hi with
  | .inl H => exact .inl H
  | .inr ⟨hn, o, w, h1, h2⟩ =>
    refine .inr ⟨hn, o, w, ?_, ?_⟩
    · cases o <;> exact h1
    · cases o <;> exact h2

/-- Structural inclusion implies the index order. Rocq: `BachmannEnumeration.bsub_ble`. -/
theorem bsub_ble : ∀ x y : BOrd.{u}, bsub x y → ble x y
  | bnode _ g _ h, bnode _ g' _ h', ⟨H1, H2⟩ =>
    ble_intro fun i => match i with
      | .inl a => let ⟨b, hb⟩ := H1 a; blt_intro (.inl b) (bsub_ble (g a) (g' b) hb)
      | .inr (c, ξ) => let ⟨d, hd⟩ := H2 c; blt_intro (.inr (d, ξ)) (bsub_ble (h c ξ) (h' d ξ) (hd ξ))

/-- Rocq: `BachmannEnumeration.bsub_child_blt`. -/
theorem bsub_child_blt (x y : BOrd.{u}) (i : bidx y) (H : bsub x (bchild y i)) : blt x y :=
  ble_lt_trans (bsub_ble _ _ H) (bindex_lt y i)

/-! ## Changing the base: comparing two enumerators

`cfe f I F` lies below `cfe f' J F'` when `f` is dominated pointwise by `f'`
or by a component of the second family, and every component of the first
family by one of the second. -/

/-- Rocq: `BachmannEnumeration.cfe_dom_base`. -/
theorem cfe_dom_base (f f' : Ordinal.{u} → Ordinal.{u}) (hf' : NormalFunction f') (J : Type u)
    (F' : J → Ordinal.{u} → Ordinal.{u}) (HF' : ∀ j, NormalFunction (F' j))
    (H0 : ∀ x, Complete x → f x ≤ f' x ∨ ∃ j, f x ≤ F' j x) (y : Ordinal.{u}) (hy : Complete y) :
    f y ≤ cfe f' J F' y :=
  match H0 y hy with
  | .inl H => le_trans H (cfe_ge_f f' J F' y)
  | .inr ⟨j, H⟩ => le_trans H (le_trans ((HF' j).monotone _ _ (cfe_inflationary f' hf' J F' y hy))
      (cfe_fix_F f' hf' J F' HF' j y hy))

/-- Rocq: `BachmannEnumeration.cfe_dom`. -/
theorem cfe_dom (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (f' : Ordinal.{u} → Ordinal.{u})
    (hf' : NormalFunction f') (J : Type u) (F' : J → Ordinal.{u} → Ordinal.{u}) (HF' : ∀ j, NormalFunction (F' j))
    (H0 : ∀ x, Complete x → f x ≤ f' x ∨ ∃ j, f x ≤ F' j x)
    (H1 : ∀ i, ∃ j, ∀ x, Complete x → F i x ≤ F' j x) (HJ : Nonempty J ∨ ¬ Nonempty I) :
    ∀ y, Complete y → cfe f I F y ≤ cfe f' J F' y := by
  match HJ with
  | .inl ⟨j0⟩ =>
    intro y
    induction y with
    | mk Y h ih =>
    intro hy
    have Hz := cfe_complete f' hf' J F' HF' _ hy
    have Hfz := cfe_fix_f f' hf' J F' HF' j0 _ hy
    refine cfe_least f hf I F HF _ _ (cfe_dom_base f f' hf' J F' HF' H0 _ hy)
      (limit_least fun a => lt_of_le_of_lt (ih a (complete_subord hy a))
        (cfe_increasing f' hf' J F' HF' (.inl ⟨j0⟩) _ _ hy (index_lt (mk Y h) a))) fun i => ?_
    obtain ⟨j, hj⟩ := H1 i
    refine ⟨le_trans (hj _ Hz) (cfe_fix_F f' hf' J F' HF' j _ hy), ?_⟩
    match H0 _ Hz with
    | .inl H => exact le_trans H Hfz
    | .inr ⟨j', H⟩ => exact le_trans H (cfe_fix_F f' hf' J F' HF' j' _ hy)
  | .inr hnI =>
    intro y hy
    rw [cfe_unroll f I F y]
    exact sup_least fun o => match o with
      | some p => (hnI ⟨p.1⟩).elim
      | none => cfe_dom_base f f' hf' J F' HF' H0 y hy

/-- Rocq: `BachmannEnumeration.bphi_unfold`. -/
theorem bphi_unfold (f : Ordinal.{u} → Ordinal.{u}) (X : BOrd.{u}) :
    bphi f X = cfe f (bsmall X ⊕ bbig X) (bphi_fam f (bsmallSz X) (bbigSz X)) := by
  cases X; rfl

/-- Rocq: `BachmannEnumeration.bphi_fam_normal''`. -/
theorem bphi_fam_normal'' (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (X : BOrd.{u}) (HX : BGood f X) :
    ∀ k, NormalFunction (bphi_fam f (bsmallSz X) (bbigSz X) k) := by
  cases X with
  | bnode A g C h => exact bphi_fam_normal' hf A g C h HX

/-- Rocq: `BachmannEnumeration.bcd_good`. -/
theorem bcd_good (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (T : BOrd.{u}) (H : BCd T) : BGood f T :=
  (bcanon_good f hf T H.1 H.2).2

/-- `φ^{ω^x}_T` lies below `φ^{1+x}_{Ω+T}`: the Ω-family of `Ω+T` supplies
`ξ ↦ ω^ξ`, and the other children of `Ω+T` are `Ω + (children of T)`.
Rocq: `BachmannEnumeration.bphi_powOmega_shift`. -/
theorem bphi_powOmega_shift : ∀ T : BOrd.{u}, BCd T → ∀ y, Complete y →
    bphi powOmega T y ≤ bphi (fun x => 1 + x) (badd bOmega T) y
  | bnode A g C h, HT, y, hy => by
    have HG1 := bcd_good _ powOmega_normal _ HT
    have HG2 := bcd_good _ onePlus_normal _ (bcd_badd _ _ bcd_Ω HT)
    refine cfe_dom powOmega powOmega_normal _ _ (bphi_fam_normal' powOmega_normal A g C h HG1) (fun x => 1 + x)
      onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ HG2) ?_ ?_ (.inl ⟨.inr (.inl ⟨⟩)⟩) y hy
    · intro x hx
      refine .inr ⟨.inr (.inl ⟨⟩), ?_⟩
      show ω ^ x ≤ bphi (fun x => 1 + x) (embed x) 0
      exact le_trans (le_add_right _ 0) (bphi_onePlus_embed x 0 hx zero_complete).ge
    · intro k
      match k with
      | .inl a =>
        exact ⟨.inl (.inr a), fun x hx => bphi_powOmega_shift (g a) (bcd_small (bnode A g C h) a HT) x hx⟩
      | .inr c =>
        exact ⟨.inr (.inr c), fun x hx =>
          bphi_powOmega_shift (h c x) (bcd_big (bnode A g C h) c x HT hx) 0 zero_complete⟩

/-- `φ^{1+x}_T` lies below `φ^{ω^x}_T`. Rocq: `BachmannEnumeration.bphi_base_mono`. -/
theorem bphi_base_mono : ∀ T : BOrd.{u}, BCd T → ∀ y, Complete y →
    bphi (fun x => 1 + x) T y ≤ bphi powOmega T y
  | bnode A g C h, HT, y, hy => by
    have HG1 := bcd_good _ onePlus_normal _ HT
    have HG2 := bcd_good _ powOmega_normal _ HT
    refine cfe_dom (fun x => 1 + x) onePlus_normal _ _ (bphi_fam_normal' onePlus_normal A g C h HG1) powOmega
      powOmega_normal _ _ (bphi_fam_normal' powOmega_normal A g C h HG2)
      (fun x hx => .inl (onePlus_least_normal powOmega_normal x hx)) (fun k => ?_) ?_ y hy
    · match k with
      | .inl a => exact ⟨.inl a, fun x hx => bphi_base_mono (g a) (bcd_small (bnode A g C h) a HT) x hx⟩
      | .inr c => exact ⟨.inr c, fun x hx => bphi_base_mono (h c x) (bcd_big (bnode A g C h) c x HT hx) 0 zero_complete⟩
    · match HT.2.1 with
      | .inl H => exact .inl H
      | .inr H => exact .inr H

/-- Rocq: `BachmannEnumeration.Ω_le_bexp`. -/
theorem Ω_le_bexp (Y : BOrd.{u}) (a : bsmall Y) : bsub bOmega (bexpΩ Y) :=
  bsub_intro _ _ (fun e => (nomatch e)) fun _ =>
    let ⟨t, ht⟩ := bexpΩ_fam_s Y a
    ⟨t, fun ξ => by rw [ht]; exact embed_le_mul _ ξ (bexpΩ_small_zero _)⟩

/-- The small child `0` of `Ω^y`, as a definition. -/
def bexpΩ_small_one : (y : BOrd.{u}) → bsmall (bexpΩ y)
  | bnode _ _ _ _ => .inl ⟨⟩

/-- Rocq: `BachmannEnumeration.btower_small`. -/
def btower_small : (n : Nat) → bsmall (btower.{u} n)
  | 0 => ⟨⟩
  | n + 1 => bexpΩ_small_one (btower n)

/-- `Ω + tower n` lies z-reachably below `tower (n+2)`. Rocq: `BachmannEnumeration.zlt_Ω_tower`. -/
theorem zlt_Ω_tower (n : Nat) (z : Ordinal.{u}) (Hz : OInf z) : zlt z (badd bOmega (btower n)) (btower (n + 2)) := by
  obtain ⟨D, H1, H2⟩ := tower_rel n z Hz
  have Hl : zlt z (btower n) (btower (n + 1)) := ⟨D, H1, H2⟩
  refine zlt_bleZ z _ (bmul (btower (n + 1)) (embed z)) _ ?_ (zlt_exp z _ _ Hl Hz)
  refine zlt_mono_r _ _ _ _ (zlt_shift z bOmega _ _ Hl) ?_
  refine bsub_trans (bsub_badd_l _ _ (Ω_le_bexp (btower n) (btower_small n)) _) ?_
  refine bsub_trans (bsub_badd_l _ _ (bsub_bmul_one (btower (n + 1))).2 _) ?_
  exact bsub_trans (bsub_mul_succ _ 1) (bsub_bmul_r _ _ _ (bsub_embed _ _ (Hz 2)))

/-! ## Merging equal exponents

Improper indices with equal adjacent exponents normalize up to `BEquiv`: sums
of embedded ordinals are embeddings of sums, and multiplication distributes
over addition on the left. -/

/-- The children of `a + b` are those of `a`, and `a + (children of b)`.
Rocq: `BachmannEnumeration.bequiv_embed_add`. -/
theorem bequiv_embed_add : ∀ b a : Ordinal.{u}, BEquiv (embed (a + b)) (badd (embed a) (embed b)) := by
  intro b
  induction b with
  | mk B k ih =>
  intro a
  cases a with
  | mk A g =>
  refine ⟨⟨fun s => ?_, fun e => (nomatch e)⟩, ⟨fun s => ?_, fun c => ?_⟩⟩
  · match s with
    | .inl x => exact ⟨.inl x, bsub_refl _⟩
    | .inr ⟨i, _⟩ => exact ⟨.inr i, (ih i (mk A g)).1⟩
  · match s with
    | .inl x => exact ⟨.inl x, bsub_refl _⟩
    | .inr i => exact ⟨.inr ⟨i, ⟨⟩⟩, (ih i (mk A g)).2⟩
  · match c with
    | .inl e => exact nomatch e
    | .inr e => exact nomatch e

/-- Rocq: `BachmannEnumeration.bsub_badd_intro`. -/
theorem bsub_badd_intro (A B Z : BOrd.{u}) (H1 : bsub A Z)
    (H2 : ∀ b, ∃ t, bsub (badd A (bsmallSz B b)) (bsmallSz Z t))
    (H3 : ∀ d, ∃ t, ∀ ξ, bsub (badd A (bbigSz B d ξ)) (bbigSz Z t ξ)) : bsub (badd A B) Z := by
  refine bsub_intro _ _ (fun a => ?_) (fun c => ?_)
  · match badd_small_cases A B a with
    | .inl ⟨a', E⟩ => rw [E]; exact bsub_small _ _ H1 a'
    | .inr ⟨b, E⟩ => rw [E]; exact H2 b
  · match badd_big_cases A B c with
    | .inl ⟨c', E⟩ =>
      obtain ⟨t, ht⟩ := bsub_big _ _ H1 c'
      exact ⟨t, fun ξ => by rw [E]; exact ht ξ⟩
    | .inr ⟨d, E⟩ =>
      obtain ⟨t, ht⟩ := H3 d
      exact ⟨t, fun ξ => by rw [E]; exact ht ξ⟩

/-- Rocq: `BachmannEnumeration.bmul_small_cases`. -/
theorem bmul_small_cases (P Y : BOrd.{u}) (t : bsmall (bmul P Y)) :
    ∃ q s, bsmallSz (bmul P Y) t = bsmallSz (badd (bmul P (bsmallSz Y q)) P) s := by
  cases Y with
  | bnode B g D h =>
  match t with
  | .inl ⟨q, s⟩ => exact ⟨q, s, rfl⟩
  | .inr e => exact nomatch e

/-- Rocq: `BachmannEnumeration.bmul_big_cases`. -/
theorem bmul_big_cases (P Y : BOrd.{u}) (t : bbig (bmul P Y)) :
    (∃ q s, ∀ ξ, bbigSz (bmul P Y) t ξ = bbigSz (badd (bmul P (bsmallSz Y q)) P) s ξ) ∨
      (∃ d, ∀ ξ, bbigSz (bmul P Y) t ξ = bmul P (bbigSz Y d ξ)) := by
  cases Y with
  | bnode B g D h =>
  match t with
  | .inl ⟨q, s⟩ => exact .inl ⟨q, s, fun _ => rfl⟩
  | .inr d => exact .inr ⟨d, fun _ => rfl⟩

/-- Rocq: `BachmannEnumeration.bsub_bmul_intro`. -/
theorem bsub_bmul_intro (P Y Z : BOrd.{u}) (H1 : ∀ q, bsub (badd (bmul P (bsmallSz Y q)) P) Z)
    (H2 : ∀ d, ∃ t, ∀ ξ, bsub (bmul P (bbigSz Y d ξ)) (bbigSz Z t ξ)) : bsub (bmul P Y) Z := by
  refine bsub_intro _ _ (fun a => ?_) (fun c => ?_)
  · obtain ⟨q, s, E⟩ := bmul_small_cases P Y a
    rw [E]
    exact bsub_small _ _ (H1 q) s
  · match bmul_big_cases P Y c with
    | .inl ⟨q, s, E⟩ =>
      obtain ⟨t, ht⟩ := bsub_big _ _ (H1 q) s
      exact ⟨t, fun ξ => by rw [E]; exact ht ξ⟩
    | .inr ⟨d, E⟩ =>
      obtain ⟨t, ht⟩ := H2 d
      exact ⟨t, fun ξ => by rw [E]; exact ht ξ⟩

/-- Rocq: `BachmannEnumeration.bmul_small_via`. -/
theorem bmul_small_via (P Y : BOrd.{u}) (q : bsmall Y) (W : BOrd.{u}) (E : bsmallSz Y q = W) :
    ∀ s : bsmall (badd (bmul P W) P), ∃ t, bsmallSz (bmul P Y) t = bsmallSz (badd (bmul P W) P) s := by
  subst E
  exact bmul_small_r P Y q

/-- Rocq: `BachmannEnumeration.bmul_big_via`. -/
theorem bmul_big_via (P Y : BOrd.{u}) (q : bsmall Y) (W : BOrd.{u}) (E : bsmallSz Y q = W) :
    ∀ s : bbig (badd (bmul P W) P), ∃ t, ∀ ξ, bbigSz (bmul P Y) t ξ = bbigSz (badd (bmul P W) P) s ξ := by
  subst E
  exact bmul_big_r P Y q

/-- Left distributivity, up to `BEquiv`. Rocq: `BachmannEnumeration.bequiv_bmul_badd`. -/
theorem bequiv_bmul_badd (P x : BOrd.{u}) : ∀ y, BEquiv (bmul P (badd x y)) (badd (bmul P x) (bmul P y)) := by
  intro y
  induction y with
  | bnode B g D h ihg ihh =>
  refine ⟨bsub_bmul_intro _ _ _ (fun q => ?_) (fun d => ?_), bsub_badd_intro _ _ _ ?_ (fun k => ?_) (fun k => ?_)⟩
  · match badd_small_cases x (bnode B g D h) q with
    | .inl ⟨a, E⟩ =>
      rw [E]
      exact bsub_trans (bsub_bmul_step P x a) (bsub_le_badd _ _)
    | .inr ⟨b, E⟩ =>
      rw [E]
      exact bsub_trans (bsub_badd_l _ _ (ihg b).1 P) (bsub_trans (bequiv_badd_assoc _ _ _).1
        (bsub_badd_r _ _ _ (bsub_bmul_step P (bnode B g D h) b)))
  · match badd_big_cases x (bnode B g D h) d with
    | .inl ⟨c, E⟩ =>
      obtain ⟨t1, E1⟩ := bmul_big_fam P x c
      obtain ⟨t, E2⟩ := badd_big_l (bmul P x) (bmul P (bnode B g D h)) t1
      exact ⟨t, fun ξ => by rw [E, E2, E1]; exact bsub_refl _⟩
    | .inr ⟨d', E⟩ =>
      obtain ⟨t1, E1⟩ := bmul_big_fam P (bnode B g D h) d'
      obtain ⟨t, E2⟩ := badd_big_r (bmul P x) (bmul P (bnode B g D h)) t1
      exact ⟨t, fun ξ => by rw [E, E2, E1]; exact (ihh d' ξ).1⟩
  · exact bsub_bmul_r _ _ _ (bsub_le_badd _ _)
  · obtain ⟨q, s, E⟩ := bmul_small_cases P (bnode B g D h) k
    rw [E]
    have H : bsub (badd (bmul P x) (badd (bmul P (g q)) P)) (badd (bmul P (badd x (g q))) P) :=
      bsub_trans (bequiv_badd_assoc _ _ _).2 (bsub_badd_l _ _ (ihg q).2 P)
    obtain ⟨s1, E1⟩ := badd_small_r (bmul P x) (badd (bmul P (g q)) P) s
    obtain ⟨s2, H2⟩ := bsub_small _ _ H s1
    obtain ⟨q', Eq⟩ := badd_small_r x (bnode B g D h) q
    obtain ⟨t, Et⟩ := bmul_small_via P _ q' _ Eq s2
    refine ⟨t, ?_⟩
    rw [Et]
    rw [E1] at H2
    exact H2
  · match bmul_big_cases P (bnode B g D h) k with
    | .inl ⟨q, s, E⟩ =>
      have H : bsub (badd (bmul P x) (badd (bmul P (g q)) P)) (badd (bmul P (badd x (g q))) P) :=
        bsub_trans (bequiv_badd_assoc _ _ _).2 (bsub_badd_l _ _ (ihg q).2 P)
      obtain ⟨s1, E1⟩ := badd_big_r (bmul P x) (badd (bmul P (g q)) P) s
      obtain ⟨s2, H2⟩ := bsub_big _ _ H s1
      obtain ⟨q', Eq⟩ := badd_small_r x (bnode B g D h) q
      obtain ⟨t, Et⟩ := bmul_big_via P _ q' _ Eq s2
      refine ⟨t, fun ξ => ?_⟩
      rw [Et, E]
      have H2ξ := H2 ξ
      rw [E1] at H2ξ
      exact H2ξ
    | .inr ⟨d, E⟩ =>
      obtain ⟨d', Ed⟩ := badd_big_r x (bnode B g D h) d
      obtain ⟨t, Et⟩ := bmul_big_fam P (badd x (bnode B g D h)) d'
      exact ⟨t, fun ξ => by rw [Et, E, Ed]; exact (ihh d ξ).2⟩

/-- Equal exponents merge: `Ω^e·c + (Ω^e·c' + r) ≈ Ω^e·(c+c') + r`.
Rocq: `BachmannEnumeration.bequiv_merge`. -/
theorem bequiv_merge (E : BOrd.{u}) (c c' : Ordinal.{u}) (r : BOrd.{u}) :
    BEquiv (badd (bmul E (embed c)) (badd (bmul E (embed c')) r)) (badd (bmul E (embed (c + c'))) r) :=
  bequiv_trans (bequiv_sym (bequiv_badd_assoc _ _ _))
    (bequiv_badd _ _ _ _ (bequiv_trans (bequiv_sym (bequiv_bmul_badd E _ _))
      (bequiv_bmul _ _ _ _ (bequiv_refl _) (bequiv_sym (bequiv_embed_add c' c)))) (bequiv_refl r))

/-! ## Shifted enumerations -/

/-- Rocq: `BachmannEnumeration.addOrd_lt_cases`. -/
theorem addOrd_lt_cases (t y a : Ordinal.{u}) (H : a < t + y) : a < t ∨ ∃ j : y, a ≤ t + y j := add_lt_cases' H

/-! ## Enumerating a class cut off above a threshold

If the common fixpoints of `(f, F)` are exactly those of `(f, G)` that lie in
an upward-closed region `U`, and the region contains all values of the first
enumerator, then the first enumerator is the second shifted by the least
argument `t` landing in `U`. The shift needs the fixpoints of `(f, G)` to be
additively principal. -/

/-- Rocq: `BachmannEnumeration.fixJ_value`. -/
theorem fixJ_value (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (J : Type u)
    (G : J → Ordinal.{u} → Ordinal.{u}) (HG : ∀ j, NormalFunction (G j)) (j0 : J) (x : Ordinal.{u})
    (hx : Complete x) : f (cfe f J G x) ≤ cfe f J G x ∧ ∀ j, G j (cfe f J G x) ≤ cfe f J G x :=
  ⟨cfe_fix_f f hf J G HG j0 x hx, fun j => cfe_fix_F f hf J G HG j x hx⟩

/-- Rocq: `BachmannEnumeration.fixI_value`. -/
theorem fixI_value (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (i0 : I) (x : Ordinal.{u})
    (hx : Complete x) : f (cfe f I F x) ≤ cfe f I F x ∧ ∀ i, F i (cfe f I F x) ≤ cfe f I F x :=
  ⟨cfe_fix_f f hf I F HF i0 x hx, fun i => cfe_fix_F f hf I F HF i x hx⟩

/-- Rocq: `BachmannEnumeration.cfe_offset`. -/
theorem cfe_offset (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I J : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (G : J → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i))
    (HG : ∀ j, NormalFunction (G j)) (i0 : I) (j0 : J) (U : Ordinal.{u} → Prop) (HU : ∀ a b, a ≤ b → U a → U b)
    (H1 : ∀ z, Complete z → (f z ≤ z ∧ ∀ i, F i z ≤ z) → (f z ≤ z ∧ ∀ j, G j z ≤ z))
    (H2 : ∀ z, Complete z → (f z ≤ z ∧ ∀ j, G j z ≤ z) → U z → (f z ≤ z ∧ ∀ i, F i z ≤ z))
    (H3 : ∀ y, Complete y → U (cfe f I F y))
    (Hp : ∀ z, Complete z → (f z ≤ z ∧ ∀ j, G j z ≤ z) → ∀ a, a < z → a + z ≤ z)
    (t : Ordinal.{u}) (Ht0 : Complete t) (Ht1 : U (cfe f J G t))
    (Ht2 : ∀ z, Complete z → (f z ≤ z ∧ ∀ j, G j z ≤ z) → U z → cfe f J G t ≤ z) (Ht3 : t < cfe f J G t) :
    ∀ y, Complete y → cfe f I F y ≈ cfe f J G (t + y) := by
  intro y
  induction y using ltRec with
  | ind y ih =>
  intro hy
  have hty := add_complete Ht0 hy
  refine equiv_intro ?_ ?_
  · refine cfe_least f hf I F HF _ _ (le_trans (hf.monotone _ _ (le_add_left t y)) (cfe_ge_f f J G _))
      (limit_least fun j => lt_of_le_of_lt (ih (y j) (index_lt y j) (complete_subord hy j)).le
        (cfe_increasing f hf J G HG (.inl ⟨j0⟩) _ _ hty (add_lt_add_left t (index_lt y j)))) fun i => ?_
    obtain ⟨Hf1, Hf2⟩ := H2 _ (cfe_complete f hf J G HG _ hty) (fixJ_value f hf J G HG j0 _ hty)
      (HU _ _ (cfe_monotone f hf J G HG _ _ (le_add_right t y)) Ht1)
    exact ⟨Hf2 i, Hf1⟩
  · have hz := cfe_complete f hf I F HF y hy
    have HzI := fixI_value f hf I F HF i0 y hy
    have HzJ := H1 _ hz HzI
    have Htz := Ht2 _ hz HzJ (H3 y hy)
    refine cfe_least f hf J G HG _ _ ?_ (limit_least fun k => ?_) fun j => ⟨HzJ.2 j, HzJ.1⟩
    · exact le_trans (hf.monotone _ _ (le_trans (add_le_add (le_refl t) (cfe_inflationary f hf I F y hy))
        (Hp _ hz HzJ t (lt_of_lt_of_le Ht3 Htz)))) HzI.1
    · have hk := index_lt (t + y) k
      match add_lt_cases' hk with
      | .inl hk1 => exact lt_of_lt_of_le (cfe_increasing f hf J G HG (.inl ⟨j0⟩) _ _ Ht0 hk1) Htz
      | .inr ⟨j, hk1⟩ =>
        exact lt_of_le_of_lt (cfe_monotone f hf J G HG _ _ hk1)
          (lt_of_le_of_lt (ih (y j) (index_lt y j) (complete_subord hy j)).ge
            (cfe_increasing f hf I F HF (.inl ⟨i0⟩) _ _ hy (index_lt y j)))

/-- The least value of `φ_T` at a successor lies below every common fixpoint
above the previous value. Rocq: `BachmannEnumeration.bphi_succ_le`. -/
theorem bphi_succ_le (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (T : BOrd.{u}) (z a : Ordinal.{u})
    (HT : BGood f T) (_Hz : Complete z) (Hfix : BFix f T z) (Ha : Complete a) (Hlt : bphi f T a < z) :
    bphi f T (succ a) ≤ z := by
  cases T with
  | bnode A g C h =>
  obtain ⟨H1, H2, H3⟩ := Hfix
  exact cfe_least f hf _ _ (bphi_fam_normal' hf A g C h HT) _ z
    (le_trans (hf.monotone _ _ (succ_least (lt_of_le_of_lt (normal_inflationary (bphi_normal hf _ HT) a Ha) Hlt))) H1)
    (limit_least fun _ => Hlt) fun k => match k with
      | .inl a => ⟨H2 a, H1⟩
      | .inr c => ⟨H3 c, H1⟩

/-- Rocq: `BachmannEnumeration.bsmall_mul_embed_inh`. -/
theorem bsmall_mul_embed_inh (y : BOrd.{u}) (x : Ordinal.{u}) (H : 0 < x) : Nonempty (bsmall (bmul (bexpΩ y) (embed x))) := by
  cases x with
  | mk X g =>
  obtain ⟨q, _⟩ := lt_elim H
  obtain ⟨t0, _⟩ := bexpΩ_small_zero y
  obtain ⟨s, _⟩ := badd_small_r (bmul (bexpΩ y) (embed (g q))) (bexpΩ y) t0
  obtain ⟨t, _⟩ := bmul_small_r (bexpΩ y) (embed (mk X g)) q s
  exact ⟨t⟩

/-- Rocq: `BachmannEnumeration.zlt_embed_Ω`. -/
theorem zlt_embed_Ω (z a : Ordinal.{u}) (Ha : a < z) : zlt z (embed a) bOmega :=
  ⟨embed (succ a), bslt_embed _ _ (succ_lt a), .big bOmega ⟨⟩ (succ a) (succ_least Ha) (.sub _ (bsub_refl _))⟩

end Bachmann

end ConstructiveOrdinals
