import ConstructiveOrdinals.Bachmann.Power

/-!
# The enumerator of common fixpoints, and the hierarchy `bphi`

Parts (A) and (B) of the direct proof of normality; the rest is in
`Bachmann/Normal` and `Bachmann/Agree`.

Ported from the Rocq file `BachmannCfe.v`.

Lean notes:

- Each lemma takes as explicit arguments the section variables and hypotheses
  that its Rocq proof uses, in the Rocq order.
- Rocq's section-local `Hfm` (monotonicity of `f`) is `hf.monotone`.
  Rocq: `BachmannCfe.Hfm`.
- `cfe` is defined through `cfe_term` and `bphi` through `Sum.elim`, so that
  `cfe_unroll` and the unfolding of `bphi` into `cfe` over `bphi_fam` are
  definitional, as in Rocq.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-! ## (A) Enumerating the common fixpoints of a family of normal functions -/

/-- Finite compositions `F_{i_1} ∘ … ∘ F_{i_n} ∘ f`. Rocq: `BachmannCfe.comps`. -/
def comps (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) :
    List I → Ordinal.{u} → Ordinal.{u}
  | [] => f
  | i :: L => fun x => F i (comps f I F L x)

/-- Rocq: `BachmannCfe.comps_normal`. -/
theorem comps_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ L, NormalFunction (comps f I F L)
  | [] => hf
  | i :: L => compose_normal (f := F i) (g := comps f I F L) (HF i) (comps_normal f hf I F HF L)

/-- Rocq: `BachmannCfe.comps_complete`. -/
theorem comps_complete (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (L : List I) :
    ∀ x, Complete x → Complete (comps f I F L x) :=
  (comps_normal f hf I F HF L).complete

/-- The case `L1 = []` of `comps_app_le_l`, by recursion on `L2`. -/
theorem comps_ge_f (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ (L2 : List I) (x : Ordinal.{u}), Complete x → f x ≤ comps f I F L2 x
  | [], _, _ => le_refl _
  | j :: L2, x, hx =>
    le_trans (comps_ge_f f hf I F HF L2 x hx) (normal_inflationary (HF j) _ (comps_complete f hf I F HF L2 x hx))

/-- Rocq: `BachmannCfe.comps_app_le_l`. -/
theorem comps_app_le_l (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ (L1 L2 : List I) (x : Ordinal.{u}), Complete x → comps f I F L1 x ≤ comps f I F (L1 ++ L2) x
  | [], L2, x, hx => comps_ge_f f hf I F HF L2 x hx
  | i :: L1, L2, x, hx => (HF i).monotone _ _ (comps_app_le_l f hf I F HF L1 L2 x hx)

/-- Rocq: `BachmannCfe.comps_app_le_r`. -/
theorem comps_app_le_r (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ (L1 L2 : List I) (x : Ordinal.{u}), Complete x → comps f I F L2 x ≤ comps f I F (L1 ++ L2) x
  | [], _, _, _ => le_refl _
  | i :: L1, L2, x, hx =>
    le_trans (comps_app_le_r f hf I F HF L1 L2 x hx)
      (normal_inflationary (HF i) _ (comps_complete f hf I F HF _ x hx))

/-- Every composition fixes a point that `f` and all the `F_i` fix.
Rocq: `BachmannCfe.comps_closed`. -/
theorem comps_closed (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (HF : ∀ i, NormalFunction (F i)) (z : Ordinal.{u}) (H1 : f z ≤ z) (H2 : ∀ i, F i z ≤ z) :
    ∀ L, comps f I F L z ≤ z
  | [] => H1
  | i :: L => le_trans ((HF i).monotone _ _ (comps_closed f I F HF z H1 H2 L)) (H2 i)

/-! ## Monotonicity of the enumerator in its family -/

/-- Rocq: `BachmannCfe.comps_monotone_gen`. -/
theorem comps_monotone_gen (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x y, x ≤ y → f x ≤ f y) (HF : ∀ i x y, x ≤ y → F i x ≤ F i y) :
    ∀ (L : List I) (x y : Ordinal.{u}), x ≤ y → comps f I F L x ≤ comps f I F L y
  | [], _, _, h => hf _ _ h
  | i :: L, _, _, h => HF i _ _ (comps_monotone_gen f I F hf HF L _ _ h)

/-- Rocq: `BachmannCfe.comps_mono_family`. -/
theorem comps_mono_family (f : Ordinal.{u} → Ordinal.{u}) (I J : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (F' : J → Ordinal.{u} → Ordinal.{u}) (HF' : ∀ j x y, x ≤ y → F' j x ≤ F' j y)
    (Hfam : ∀ i, ∃ j, ∀ x, F i x ≤ F' j x) : ∀ L : List I, ∃ L' : List J, ∀ x, comps f I F L x ≤ comps f J F' L' x
  | [] => ⟨[], fun _ => le_refl _⟩
  | i :: L =>
    let ⟨L', hL'⟩ := comps_mono_family f I J F F' HF' Hfam L
    let ⟨j, hj⟩ := Hfam i
    ⟨j :: L', fun x => le_trans (hj _) (HF' j _ _ (hL' x))⟩

/-! ## The enumerator -/

/-- A nonempty composition: `F_i` after the composition `L` (which ends with
`f`). Rocq: `BachmannCfe.c1`. -/
def c1 (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) (p : I × List I) :
    Ordinal.{u} → Ordinal.{u} :=
  fun x => F p.1 (comps f I F p.2 x)

/-- Rocq: `BachmannCfe.c1_normal`. -/
theorem c1_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (p : I × List I) :
    NormalFunction (c1 f I F p) :=
  compose_normal (f := F p.1) (g := comps f I F p.2) (HF p.1) (comps_normal f hf I F HF p.2)

/-- Rocq: `BachmannCfe.c1_ge_f`. -/
theorem c1_ge_f (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (p : I × List I) (x : Ordinal.{u})
    (hx : Complete x) : f x ≤ c1 f I F p x :=
  le_trans (comps_app_le_l f hf I F HF [] p.2 x hx)
    (normal_inflationary (HF p.1) _ (comps_complete f hf I F HF p.2 x hx))

/-- Rocq: `BachmannCfe.c1_fix_f`. -/
theorem c1_fix_f (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (p : I × List I) (z : Ordinal.{u})
    (hz : Complete z) (H : c1 f I F p z ≤ z) : f z ≤ z :=
  le_trans (c1_ge_f f hf I F HF p z hz) H

/-- Rocq: `BachmannCfe.c1_fix_F`. -/
theorem c1_fix_F (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (p : I × List I) (z : Ordinal.{u})
    (hz : Complete z) (H : c1 f I F p z ≤ z) : F p.1 z ≤ z :=
  le_trans ((HF p.1).monotone _ _ (normal_inflationary (comps_normal f hf I F HF p.2) z hz)) H

/-- The terms whose supremum is a value of `cfe`. Rocq: `BachmannCfe.cfe_term`. -/
def cfe_term (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (y s : Ordinal.{u}) : Option (I × List I) → Ordinal.{u}
  | none => f y
  | some p => fixOrd (c1 f I F p) s

/-- The enumerator of the common fixpoints of `f` and the `F_i`.
Rocq: `BachmannCfe.cfe`. -/
def cfe (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u}) :
    Ordinal.{u} → Ordinal.{u}
  | mk Y h => sup (cfe_term f I F (mk Y h) (mk Y fun j => cfe f I F (h j)))

/-- Rocq: `BachmannCfe.cfe_unroll`. -/
theorem cfe_unroll (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (y : Ordinal.{u}) : cfe f I F y = sup (cfe_term f I F y (lim fun j : y => cfe f I F (y j))) := by
  cases y; rfl

attribute [irreducible] cfe

section cfe

variable (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u})

/-- Rocq: `BachmannCfe.cfe_ge_term`. -/
theorem cfe_ge_term (y : Ordinal.{u}) (o : Option (I × List I)) :
    cfe_term f I F y (lim fun j : y => cfe f I F (y j)) o ≤ cfe f I F y := by
  rw [cfe_unroll f I F y]
  exact sup_le _ o

/-- Rocq: `BachmannCfe.cfe_ge_f`. -/
theorem cfe_ge_f (y : Ordinal.{u}) : f y ≤ cfe f I F y := cfe_ge_term f I F y none

end cfe

/-- Rocq: `BachmannCfe.cfe_monotone`. -/
theorem cfe_monotone (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ x y : Ordinal.{u}, x ≤ y → cfe f I F x ≤ cfe f I F y := by
  intro x y
  induction y generalizing x with
  | mk Y h ihy =>
  intro hxy
  cases x with
  | mk X g =>
  rw [cfe_unroll f I F (mk X g)]
  refine sup_least fun o => ?_
  match o with
  | some p =>
    refine le_trans ?_ (cfe_ge_term f I F (mk Y h) (some p))
    exact fixOrd_monotone (c1_normal f hf I F HF p).monotone (limit_least fun i =>
      let ⟨j, hj⟩ := le_subord hxy i
      lt_of_le_of_lt (ihy j (g i) hj) (limit_lt (fun j : Y => cfe f I F (h j)) j))
  | none => exact le_trans (hf.monotone _ _ hxy) (cfe_ge_f f I F (mk Y h))

/-- Rocq: `BachmannCfe.cfe_inflationary`. -/
theorem cfe_inflationary (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (y : Ordinal.{u}) (hy : Complete y) : y ≤ cfe f I F y :=
  le_trans (normal_inflationary hf y hy) (cfe_ge_f f I F y)

/-- Rocq: `BachmannCfe.cfe_start_ge`. -/
theorem cfe_start_ge (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (y : Ordinal.{u}) (hc : ∀ j, Complete (y j)) :
    y ≤ lim fun j : y => cfe f I F (y j) := by
  cases y with
  | mk Y h => exact lim_le_mor _ _ _ fun j => cfe_inflationary f hf I F _ (hc j)

/-- The terms at a node, with a complete start above `y`, are directed.
Rocq: `BachmannCfe.cfe_dir`. -/
theorem cfe_dir (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (y s : Ordinal.{u})
    (hs : Complete s) (hys : y ≤ s) : Directed _ (cfe_term f I F y s) := by
  have HfP : ∀ p, f y ≤ fixOrd (c1 f I F p) s := fun p =>
    le_trans (hf.monotone _ _ hys) (le_trans (c1_ge_f f hf I F HF p s hs)
      (sup_le (fun n : ULift.{u} Nat => iterF (c1 f I F p) s n.down) ⟨1⟩))
  intro o1 o2
  match o1, o2 with
  | some (i1, L1), some (i2, L2) =>
    refine ⟨some (i1, L1 ++ i2 :: L2), ?_, ?_⟩
    · exact fixOrd_monotone_func'' (fun x hx => (HF i1).monotone _ _ (comps_app_le_l f hf I F HF L1 (i2 :: L2) x hx))
        (c1_normal f hf I F HF (i1, L1 ++ i2 :: L2)).complete (c1_normal f hf I F HF (i1, L1)).monotone s hs
    · exact fixOrd_monotone_func'' (fun x hx => le_trans (comps_app_le_r f hf I F HF L1 (i2 :: L2) x hx)
          (normal_inflationary (HF i1) _ (comps_complete f hf I F HF _ x hx)))
        (c1_normal f hf I F HF (i1, L1 ++ i2 :: L2)).complete (c1_normal f hf I F HF (i2, L2)).monotone s hs
  | some (i1, L1), none => exact ⟨some (i1, L1), le_refl _, HfP _⟩
  | none, some (i2, L2) => exact ⟨some (i2, L2), HfP _, le_refl _⟩
  | none, none => exact ⟨none, le_refl _, le_refl _⟩

/-- Rocq: `BachmannCfe.cfe_term_complete`. -/
theorem cfe_term_complete (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (y s : Ordinal.{u})
    (o : Option (I × List I)) (hy : Complete y) (hs : Complete s) : Complete (cfe_term f I F y s o) :=
  match o with
  | some p =>
    normal_fix_complete _ hs (normal_inflationary (c1_normal f hf I F HF p)) (c1_normal f hf I F HF p).monotone
      (c1_normal f hf I F HF p).complete
  | none => hf.complete y hy

/-- Rocq: `BachmannCfe.cfe_complete_start`. -/
theorem cfe_complete_start (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) :
    ∀ y : Ordinal.{u}, Complete y → Complete (cfe f I F y) ∧ Complete (lim fun j : y => cfe f I F (y j)) := by
  intro y
  induction y with
  | mk Y h ih =>
  intro hyc
  have hyc' := hyc
  obtain ⟨hdir, hinh, hhc⟩ := hyc'
  have Hs : Complete (lim fun j : Y => cfe f I F (h j)) :=
    lim_complete (fun j => (ih j (hhc j)).1)
      (fun j1 j2 => let ⟨j', h1, h2⟩ := hdir j1 j2
        ⟨j', cfe_monotone f hf I F HF _ _ h1, cfe_monotone f hf I F HF _ _ h2⟩) hinh
  refine ⟨?_, Hs⟩
  rw [cfe_unroll]
  exact sup_complete (fun o => cfe_term_complete f hf I F HF _ _ o hyc Hs)
    (cfe_dir f hf I F HF _ _ Hs (cfe_start_ge f hf I F (mk Y h) hhc)) (.inl ⟨none, hf.nonzero _⟩)

/-- Rocq: `BachmannCfe.cfe_complete`. -/
theorem cfe_complete (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (y : Ordinal.{u}) (hy : Complete y) :
    Complete (cfe f I F y) :=
  (cfe_complete_start f hf I F HF y hy).1

/-- Rocq: `BachmannCfe.cfe_nonzero`. -/
theorem cfe_nonzero (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (y : Ordinal.{u}) : 0 < cfe f I F y :=
  lt_of_lt_of_le (hf.nonzero y) (cfe_ge_f f I F y)

/-- Least fixpoints of the compositions are fixed by `f` and by the `F_i`.
Rocq: `BachmannCfe.c1_fixOrd_fix`. -/
theorem c1_fixOrd_fix (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (p : I × List I) (s : Ordinal.{u})
    (hs : Complete s) : c1 f I F p (fixOrd (c1 f I F p) s) ≤ fixOrd (c1 f I F p) s :=
  (normal_fixpoint (c1_normal f hf I F HF p) s hs).ge

/-- Rocq: `BachmannCfe.cfe_fix_F`. -/
theorem cfe_fix_F (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (i : I) (y : Ordinal.{u})
    (hy : Complete y) : F i (cfe f I F y) ≤ cfe f I F y := by
  obtain ⟨_, Hs⟩ := cfe_complete_start f hf I F HF y hy
  have Hys := cfe_start_ge f hf I F y (complete_subord hy)
  rw [cfe_unroll f I F y]
  refine le_trans ((HF i).continuous _ _ none (cfe_dir f hf I F HF y _ Hs Hys)
    (fun o => cfe_term_complete f hf I F HF y _ o hy Hs)) (sup_least fun o => ?_)
  match o with
  | some (j, L) =>
    have Hle : fixOrd (c1 f I F (j, L)) (lim fun j0 : y => cfe f I F (y j0)) ≤
        fixOrd (c1 f I F (i, j :: L)) (lim fun j0 : y => cfe f I F (y j0)) :=
      fixOrd_monotone_func'' (fun x hx => normal_inflationary (HF i) _ ((HF j).complete _ (comps_complete f hf I F HF L x hx)))
        (c1_normal f hf I F HF (i, j :: L)).complete (c1_normal f hf I F HF (j, L)).monotone _ Hs
    exact le_trans ((HF i).monotone _ _ Hle)
      (le_trans (c1_fix_F f hf I F HF (i, j :: L) _ (cfe_term_complete f hf I F HF y _ (some (i, j :: L)) hy Hs)
          (c1_fixOrd_fix f hf I F HF (i, j :: L) _ Hs))
        (sup_le (cfe_term f I F y _) (some (i, j :: L))))
  | none =>
    refine le_trans ((HF i).monotone _ _ (le_trans (hf.monotone _ _ Hys) (le_trans (c1_ge_f f hf I F HF (i, []) _ Hs)
      (sup_le (fun n : ULift.{u} Nat => iterF (c1 f I F (i, [])) (lim fun j0 : y => cfe f I F (y j0)) n.down) ⟨1⟩)))) ?_
    exact le_trans (c1_fix_F f hf I F HF (i, []) _ (cfe_term_complete f hf I F HF y _ (some (i, [])) hy Hs)
        (c1_fixOrd_fix f hf I F HF (i, []) _ Hs))
      (sup_le (cfe_term f I F y _) (some (i, [])))

/-- With at least one component, values are fixpoints of `f`.
Rocq: `BachmannCfe.cfe_fix_f`. -/
theorem cfe_fix_f (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (i : I) (y : Ordinal.{u})
    (hy : Complete y) : f (cfe f I F y) ≤ cfe f I F y := by
  obtain ⟨_, Hs⟩ := cfe_complete_start f hf I F HF y hy
  have Hys := cfe_start_ge f hf I F y (complete_subord hy)
  rw [cfe_unroll f I F y]
  refine le_trans (hf.continuous _ _ none (cfe_dir f hf I F HF y _ Hs Hys)
    (fun o => cfe_term_complete f hf I F HF y _ o hy Hs)) (sup_least fun o => ?_)
  match o with
  | some p =>
    exact le_trans (c1_fix_f f hf I F HF p _ (cfe_term_complete f hf I F HF y _ (some p) hy Hs)
        (c1_fixOrd_fix f hf I F HF p _ Hs))
      (sup_le (cfe_term f I F y _) (some p))
  | none =>
    refine le_trans (hf.monotone _ _ (le_trans (hf.monotone _ _ Hys) (le_trans (c1_ge_f f hf I F HF (i, []) _ Hs)
      (sup_le (fun n : ULift.{u} Nat => iterF (c1 f I F (i, [])) (lim fun j0 : y => cfe f I F (y j0)) n.down) ⟨1⟩)))) ?_
    exact le_trans (c1_fix_f f hf I F HF (i, []) _ (cfe_term_complete f hf I F HF y _ (some (i, [])) hy Hs)
        (c1_fixOrd_fix f hf I F HF (i, []) _ Hs))
      (sup_le (cfe_term f I F y _) (some (i, [])))

/-- The value is the least ordinal above `f y` and the previous values that is
fixed by `f` and every `F_i` (`f` only when some `F_i` exists).
Rocq: `BachmannCfe.cfe_least`. -/
theorem cfe_least (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (y z : Ordinal.{u}) (H1 : f y ≤ z)
    (H2 : (lim fun j : y => cfe f I F (y j)) ≤ z) (H3 : ∀ i, F i z ≤ z ∧ f z ≤ z) : cfe f I F y ≤ z := by
  rw [cfe_unroll]
  refine sup_least fun o => ?_
  match o with
  | none => exact H1
  | some (i, L) =>
    exact fixOrd_least (c1_normal f hf I F HF _).monotone _ _ H2
      (le_trans ((HF i).monotone _ _ (comps_closed f I F HF z (H3 i).2 (fun j => (H3 j).1) L)) (H3 i).1)

/-- Strict monotonicity needs to know, as a proposition, whether there are any
components. Rocq: `BachmannCfe.cfe_increasing`. -/
theorem cfe_increasing (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (HdecI : Nonempty I ∨ ¬ Nonempty I) :
    ∀ x y : Ordinal.{u}, Complete y → x < y → cfe f I F x < cfe f I F y := by
  intro x y hy hxy
  cases y with
  | mk Y h =>
  obtain ⟨j, hj⟩ := lt_elim hxy
  refine lt_of_le_of_lt (cfe_monotone f hf I F HF _ _ hj) ?_
  match HdecI with
  | .inl ⟨i⟩ =>
    exact lt_of_lt_of_le (lt_of_lt_of_le (limit_lt (fun j : Y => cfe f I F (h j)) j) (fixOrd_above _ _))
      (cfe_ge_term f I F (mk Y h) (some (i, [])))
  | .inr hn =>
    refine lt_of_le_of_lt (b := f (h j)) ?_ (lt_of_lt_of_le (hf.increasing _ _ hy (index_lt (mk Y h) j))
      (cfe_ge_f f I F _))
    rw [cfe_unroll f I F (h j)]
    exact sup_least fun o => match o with
      | some p => (hn ⟨p.1⟩).elim
      | none => le_refl _

/-- Rocq: `BachmannCfe.cfe_continuous`. -/
theorem cfe_continuous (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (HdecI : Nonempty I ∨ ¬ Nonempty I) :
    ScottContinuous (cfe f I F) := by
  intro A g a0 hdir hc
  have hdir' : Directed A fun a => cfe f I F (g a) := fun a1 a2 =>
    let ⟨a', h1, h2⟩ := hdir a1 a2
    ⟨a', cfe_monotone f hf I F HF _ _ h1, cfe_monotone f hf I F HF _ _ h2⟩
  have hc' : ∀ a, Complete (cfe f I F (g a)) := fun a => cfe_complete f hf I F HF _ (hc a)
  refine cfe_least f hf I F HF _ _ (le_trans (hf.continuous A g a0 hdir hc) (sup_monotone fun a => cfe_ge_f f I F (g a)))
    (limit_least fun p => ?_) fun i => ⟨?_, ?_⟩
  · obtain ⟨a, c⟩ := p
    exact lt_of_lt_of_le (cfe_increasing f hf I F HF HdecI _ _ (hc a) (index_lt (g a) c))
      (sup_le (fun a => cfe f I F (g a)) a)
  · exact le_trans ((HF i).continuous A _ a0 hdir' hc') (sup_monotone fun a => cfe_fix_F f hf I F HF i (g a) (hc a))
  · exact le_trans (hf.continuous A _ a0 hdir' hc') (sup_monotone fun a => cfe_fix_f f hf I F HF i (g a) (hc a))

/-- Rocq: `BachmannCfe.cfe_normal`. -/
theorem cfe_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (I : Type u)
    (F : I → Ordinal.{u} → Ordinal.{u}) (HF : ∀ i, NormalFunction (F i)) (HdecI : Nonempty I ∨ ¬ Nonempty I) :
    NormalFunction (cfe f I F) where
  monotone := cfe_monotone f hf I F HF
  increasing := cfe_increasing f hf I F HF HdecI
  continuous := cfe_continuous f hf I F HF HdecI
  complete := cfe_complete f hf I F HF
  nonzero := cfe_nonzero f hf I F

/-! ## Monotonicity of the enumerator in its family -/

/-- Rocq: `BachmannCfe.c1_monotone_gen`. -/
theorem c1_monotone_gen (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x y, x ≤ y → f x ≤ f y) (HF : ∀ i x y, x ≤ y → F i x ≤ F i y) (p : I × List I) (x y : Ordinal.{u})
    (hxy : x ≤ y) : c1 f I F p x ≤ c1 f I F p y :=
  HF _ _ _ (comps_monotone_gen f I F hf HF _ _ _ hxy)

/-- Rocq: `BachmannCfe.cfe_monotone_gen`. -/
theorem cfe_monotone_gen (f : Ordinal.{u} → Ordinal.{u}) (I : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x y, x ≤ y → f x ≤ f y) (HF : ∀ i x y, x ≤ y → F i x ≤ F i y) :
    ∀ x y : Ordinal.{u}, x ≤ y → cfe f I F x ≤ cfe f I F y := by
  intro x y
  induction y generalizing x with
  | mk Y h ihy =>
  intro hxy
  cases x with
  | mk X g =>
  rw [cfe_unroll f I F (mk X g)]
  refine sup_least fun o => ?_
  match o with
  | some p =>
    refine le_trans ?_ (cfe_ge_term f I F (mk Y h) (some p))
    exact fixOrd_monotone (c1_monotone_gen f I F hf HF p) (limit_least fun i =>
      let ⟨j, hj⟩ := le_subord hxy i
      lt_of_le_of_lt (ihy j (g i) hj) (limit_lt (fun j : Y => cfe f I F (h j)) j))
  | none => exact le_trans (hf _ _ hxy) (cfe_ge_f f I F (mk Y h))

/-- Rocq: `BachmannCfe.cfe_mono_family`. -/
theorem cfe_mono_family (f : Ordinal.{u} → Ordinal.{u}) (I J : Type u) (F : I → Ordinal.{u} → Ordinal.{u})
    (F' : J → Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (HF' : ∀ j x y, x ≤ y → F' j x ≤ F' j y)
    (Hfam : ∀ i, ∃ j, ∀ x, F i x ≤ F' j x) : ∀ y : Ordinal.{u}, cfe f I F y ≤ cfe f J F' y := by
  intro y
  induction y with
  | mk Y h ih =>
  rw [cfe_unroll f I F (mk Y h)]
  refine sup_least fun o => ?_
  match o with
  | some (i, L) =>
    obtain ⟨j, hj⟩ := Hfam i
    obtain ⟨L', hL'⟩ := comps_mono_family f I J F F' HF' Hfam L
    refine le_trans ?_ (cfe_ge_term f J F' (mk Y h) (some (j, L')))
    exact le_trans (fixOrd_monotone_func (fun x => le_trans (hj _) (HF' j _ _ (hL' x))) (c1_monotone_gen f J F' hf HF' (j, L')) _)
      (fixOrd_monotone (c1_monotone_gen f J F' hf HF' (j, L')) (lim_le_mor _ _ _ fun j0 => ih j0))
  | none => exact cfe_ge_f f J F' (mk Y h)

/-! ## (B) A hierarchy that is normal by construction -/

section bphi

variable (f : Ordinal.{u} → Ordinal.{u})

/-- Rocq: `BachmannCfe.bphi`. -/
def bphi : BOrd.{u} → Ordinal.{u} → Ordinal.{u}
  | bnode A g C h => cfe f (A ⊕ C) (Sum.elim (fun a => bphi (g a)) (fun c ξ => bphi (h c ξ) 0))

/-- Rocq: `BachmannCfe.bphi_fam`. -/
def bphi_fam {A C : Type u} (g : A → BOrd.{u}) (h : C → Ordinal.{u} → BOrd.{u}) : A ⊕ C → Ordinal.{u} → Ordinal.{u} :=
  Sum.elim (fun a => bphi f (g a)) (fun c ξ => bphi f (h c ξ) 0)

theorem bphi_node (A : Type u) (g : A → BOrd.{u}) (C : Type u) (h : C → Ordinal.{u} → BOrd.{u}) :
    bphi f (bnode A g C h) = cfe f (A ⊕ C) (bphi_fam f g h) := rfl

/-- Every node decides (as a proposition) whether it has components; every
Ω-family has a normal diagonal, and its members at positive complete arguments
have components; members are required to be good at complete arguments.
Rocq: `BachmannCfe.bgood`. -/
def BGood : BOrd.{u} → Prop
  | bnode A g C h =>
    (∀ a, BGood (g a)) ∧ (∀ c ξ, Complete ξ → BGood (h c ξ)) ∧
      (∀ c, NormalFunction fun ξ => bphi f (h c ξ) 0) ∧
      (∀ c ξ, Complete ξ → 0 < ξ → Nonempty (bsmall (h c ξ) ⊕ bbig (h c ξ))) ∧
      (Nonempty (A ⊕ C) ∨ ¬ Nonempty (A ⊕ C))

/-- Rocq: `BachmannCfe.bphi_fam_normal`. -/
theorem bphi_fam_normal (A : Type u) (g : A → BOrd.{u}) (C : Type u) (h : C → Ordinal.{u} → BOrd.{u})
    (H1 : ∀ a, NormalFunction (bphi f (g a))) (H2 : ∀ c, NormalFunction fun ξ => bphi f (h c ξ) 0) :
    ∀ k, NormalFunction (bphi_fam f g h k)
  | .inl a => H1 a
  | .inr c => H2 c

variable {f}

/-- Rocq: `BachmannCfe.bphi_normal`. -/
theorem bphi_normal (hf : NormalFunction f) : ∀ T : BOrd.{u}, BGood f T → NormalFunction (bphi f T)
  | bnode A g C h, ⟨H1, _, H3, _, H4⟩ =>
    cfe_normal f hf (A ⊕ C) (bphi_fam f g h)
      (bphi_fam_normal f A g C h (fun a => bphi_normal hf (g a) (H1 a)) H3) H4

variable (f)

/-- Rocq: `BachmannCfe.bphi_ge_f`. -/
theorem bphi_ge_f (T : BOrd.{u}) (y : Ordinal.{u}) : f y ≤ bphi f T y := by
  cases T with
  | bnode A g C h => exact cfe_ge_f f (A ⊕ C) _ y

/-- Rocq: `BachmannCfe.bphi_fix_small`. -/
theorem bphi_fix_small (hf : NormalFunction f) (A : Type u) (g : A → BOrd.{u}) (C : Type u)
    (h : C → Ordinal.{u} → BOrd.{u}) (a : A) (y : Ordinal.{u}) (HT : BGood f (bnode A g C h)) (hy : Complete y) :
    bphi f (g a) (bphi f (bnode A g C h) y) ≤ bphi f (bnode A g C h) y :=
  have ⟨H1, _, H3, _, _⟩ := HT
  cfe_fix_F f hf (A ⊕ C) (bphi_fam f g h)
    (bphi_fam_normal f A g C h (fun a => bphi_normal hf _ (H1 a)) H3) (.inl a) y hy

/-- Rocq: `BachmannCfe.bphi_fix_big`. -/
theorem bphi_fix_big (hf : NormalFunction f) (A : Type u) (g : A → BOrd.{u}) (C : Type u)
    (h : C → Ordinal.{u} → BOrd.{u}) (c : C) (y : Ordinal.{u}) (HT : BGood f (bnode A g C h)) (hy : Complete y) :
    bphi f (h c (bphi f (bnode A g C h) y)) 0 ≤ bphi f (bnode A g C h) y :=
  have ⟨H1, _, H3, _, _⟩ := HT
  cfe_fix_F f hf (A ⊕ C) (bphi_fam f g h)
    (bphi_fam_normal f A g C h (fun a => bphi_normal hf _ (H1 a)) H3) (.inr c) y hy

end bphi

/-! ## Accessors for good trees -/

section good0

variable (f : Ordinal.{u} → Ordinal.{u})

/-- Rocq: `BachmannCfe.bgood_small`. -/
theorem bgood_small (x : BOrd.{u}) (a : bsmall x) (H : BGood f x) : BGood f (bsmallSz x a) := by
  cases x; exact H.1 a

/-- Rocq: `BachmannCfe.bgood_big`. -/
theorem bgood_big (x : BOrd.{u}) (c : bbig x) (ξ : Ordinal.{u}) (H : BGood f x) (hξ : Complete ξ) :
    BGood f (bbigSz x c ξ) := by
  cases x; exact H.2.1 c ξ hξ

/-- Rocq: `BachmannCfe.bgood_diag`. -/
theorem bgood_diag (x : BOrd.{u}) (c : bbig x) (H : BGood f x) : NormalFunction fun ξ => bphi f (bbigSz x c ξ) 0 := by
  cases x; exact H.2.2.1 c

/-- Rocq: `BachmannCfe.bgood_pos`. -/
theorem bgood_pos (x : BOrd.{u}) (c : bbig x) (ξ : Ordinal.{u}) (H : BGood f x) (hξ : Complete ξ) (hξ0 : 0 < ξ) :
    Nonempty (bsmall (bbigSz x c ξ) ⊕ bbig (bbigSz x c ξ)) := by
  cases x; exact H.2.2.2.1 c ξ hξ hξ0

variable {f} (hf : NormalFunction f)

include hf in
/-- Rocq: `BachmannCfe.bphi_fam_normal'`. -/
theorem bphi_fam_normal' (A : Type u) (g : A → BOrd.{u}) (C : Type u) (h : C → Ordinal.{u} → BOrd.{u})
    (HT : BGood f (bnode A g C h)) : ∀ k, NormalFunction (bphi_fam f g h k) :=
  bphi_fam_normal f A g C h (fun a => bphi_normal hf _ (HT.1 a)) HT.2.2.1

include hf in
/-- Rocq: `BachmannCfe.bphi_fix_small'`. -/
theorem bphi_fix_small' (T : BOrd.{u}) (a : bsmall T) (y : Ordinal.{u}) (HT : BGood f T) (hy : Complete y) :
    bphi f (bsmallSz T a) (bphi f T y) ≤ bphi f T y := by
  cases T; exact bphi_fix_small f hf _ _ _ _ a y HT hy

include hf in
/-- Rocq: `BachmannCfe.bphi_fix_big'`. -/
theorem bphi_fix_big' (T : BOrd.{u}) (c : bbig T) (y : Ordinal.{u}) (HT : BGood f T) (hy : Complete y) :
    bphi f (bbigSz T c (bphi f T y)) 0 ≤ bphi f T y := by
  cases T; exact bphi_fix_big f hf _ _ _ _ c y HT hy

include hf in
/-- With a component, every value is a fixpoint of the base.
Rocq: `BachmannCfe.bphi_fix_base'`. -/
theorem bphi_fix_base' (T : BOrd.{u}) (y : Ordinal.{u}) (HT : BGood f T) (hk : Nonempty (bsmall T ⊕ bbig T))
    (hy : Complete y) : f (bphi f T y) ≤ bphi f T y := by
  cases T with
  | bnode A g C h =>
  obtain ⟨k⟩ := hk
  exact cfe_fix_f f hf (A ⊕ C) (bphi_fam f g h) (bphi_fam_normal' hf A g C h HT) k y hy

include hf in
/-- Rocq: `BachmannCfe.bphi_nonzero`. -/
theorem bphi_nonzero (T : BOrd.{u}) (y : Ordinal.{u}) : 0 < bphi f T y := by
  cases T with
  | bnode A g C h => exact cfe_nonzero f hf _ _ y

include hf in
/-- Rocq: `BachmannCfe.bphi_complete`. -/
theorem bphi_complete (T : BOrd.{u}) (y : Ordinal.{u}) (HT : BGood f T) (hy : Complete y) : Complete (bphi f T y) :=
  (bphi_normal hf T HT).complete y hy

end good0

end Bachmann

end ConstructiveOrdinals
