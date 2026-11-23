import ConstructiveOrdinals.Bachmann.Power

/-!
# Calibration against known hierarchies

The step theorems of `Bachmann/Defs` and the power theorem of `Bachmann/Power`
give `φ_Ω = Γ₀`, `φ_{Ω·ξ}` as ternary Veblen, `φ_{Ω²}(0)` as Ackermann's
ordinal, and the Small and Large Veblen Ordinals.

Ported from the Rocq file `BachmannCalibration.v`.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-! ## Calibrations, as corollaries of the step theorems -/

/-- Rocq: `BachmannCalibration.powOmega_le_veblen0`. -/
theorem powOmega_le_veblen0 (x : Ordinal.{u}) (hx : Complete x) : powOmega x ≤ veblen powOmega x 0 :=
  le_trans (powOmega_monotone (add_zero x).ge) (veblen_fax powOmega_normal x 0 hx zero_complete)

/-- `φ_Ω` enumerates the strongly critical ordinals: `φ_Ω(0) = Γ₀`.
Rocq: `BachmannCalibration.bach_Ω_rep`. -/
theorem bach_Ω_rep : BRep powOmega bOmega.{u} Γ :=
  bach_Ωlim_step powOmega embed _ (veblen_first_normal powOmega_normal) (fun x y h => bach_embed0_mono x y h)
    (fun x _ => bach_embed _ (fun _ _ h => powOmega_monotone h) x 0) powOmega_le_veblen0

/-- Rocq: `BachmannCalibration.bach_Ω_Γ`. -/
theorem bach_Ω_Γ (y : Ordinal.{u}) (hy : Complete y) : bach powOmega bOmega y ≈ Γ y := bach_Ω_rep.2.1 y hy

/-- `φ_{Ω+ξ}` is the Veblen hierarchy over `Γ`. Rocq: `BachmannCalibration.bach_Ω_plus_rep`. -/
theorem bach_Ω_plus_rep (ξ : Ordinal.{u}) (hξ : Complete ξ) : BRep powOmega (badd bOmega (embed ξ)) (veblen Γ ξ) :=
  bach_veblen_step _ (fun _ _ h => powOmega_monotone h) _ _ (bmono_Ω _ fun _ _ h => powOmega_monotone h) bach_Ω_rep ξ hξ

/-- Rocq: `BachmannCalibration.bach_Ω_plus`. -/
theorem bach_Ω_plus (ξ : Ordinal.{u}) (hξ : Complete ξ) (y : Ordinal.{u}) (hy : Complete y) :
    bach powOmega (badd bOmega (embed ξ)) y ≈ veblen Γ ξ y :=
  (bach_Ω_plus_rep ξ hξ).2.1 y hy

/-- Rocq: `BachmannCalibration.bach_Ω1_rep`. -/
theorem bach_Ω1_rep : BRep powOmega (badd bOmega.{u} (bsucc bzero)) (enumFixpoints Γ) :=
  bach_succ_step _ (fun _ _ h => powOmega_monotone h) _ _ (bmono_Ω _ fun _ _ h => powOmega_monotone h) bach_Ω_rep

/-! ### `φ_{Ω·2}` enumerates the fixpoints of `ξ ↦ φ_{Ω+ξ}(0)` -/

/-- Rocq: `BachmannCalibration.bOmega2`. -/
def bOmega2 : BOrd.{u} := badd bOmega bOmega

/-- Rocq: `BachmannCalibration.bmono_Ω2`. -/
theorem bmono_Ω2 (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) : BMono f bOmega2 :=
  bmono_badd_Ω f hf _ (bmono_Ω f hf)

/-- Rocq: `BachmannCalibration.Γ2`. -/
def Γ2 : Ordinal.{u} → Ordinal.{u} := enumFixpoints fun ξ => veblen Γ ξ 0

/-- Rocq: `BachmannCalibration.bach_Ω2_rep`. -/
theorem bach_Ω2_rep : BRep powOmega bOmega2.{u} Γ2 :=
  bach_plusΩ_step _ (fun _ _ h => powOmega_monotone h) _ _ (bmono_Ω _ fun _ _ h => powOmega_monotone h) bach_Ω_rep

/-- Rocq: `BachmannCalibration.bach_Ω2`. -/
theorem bach_Ω2 (y : Ordinal.{u}) (hy : Complete y) : bach powOmega bOmega2 y ≈ Γ2 y := bach_Ω2_rep.2.1 y hy

/-! ### `φ_{Ω·n}` is the n-fold iterated `Γ` construction -/

/-- Rocq: `BachmannCalibration.bOmegaMul`. -/
def bOmegaMul : Nat → BOrd.{u}
  | 0 => bzero
  | n + 1 => badd (bOmegaMul n) bOmega

/-- Rocq: `BachmannCalibration.Γiter`. -/
def Γiter (f : Ordinal.{u} → Ordinal.{u}) : Nat → Ordinal.{u} → Ordinal.{u}
  | 0 => f
  | n + 1 => enumFixpoints fun ξ => veblen (Γiter f n) ξ 0

/-- Rocq: `BachmannCalibration.bach_Ωmul_rep`. -/
theorem bach_Ωmul_rep (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ n, BMono f (bOmegaMul n) ∧ BRep f (bOmegaMul n) (Γiter f n)
  | 0 => ⟨bmono_bzero f, bach_zero_rep f hf⟩
  | n + 1 =>
    let ⟨h1, h2⟩ := bach_Ωmul_rep f hf n
    ⟨bmono_badd_Ω f hf.monotone _ h1, bach_plusΩ_step f hf.monotone _ _ h1 h2⟩

/-- In particular `φ_{0+Ω}` is `Γ`, definitionally on the right (the Rocq
example `bach_Ωmul1_Γ`). -/
theorem bach_Ωmul1_Γ (y : Ordinal.{u}) (hy : Complete y) : bach powOmega (bOmegaMul 1) y ≈ Γ y :=
  (bach_Ωmul_rep powOmega powOmega_normal 1).2.2.1 y hy

/-! ## Multiples of Ω: `φ_{Ω·ξ}` is ternary Veblen

The tree `bmul bOmega (embed ξ)` merges, via `bsup`, the children of the trees
`Ω·ξ_i + Ω`. Its components are therefore the components of each `Ω·ξ_i`
together with each diagonal `ζ ↦ φ_{Ω·ξ_i+ζ}(0)`. We show that it represents
the third column of Schütte's Klammersymbols, `schutteColumn f 2 ξ`, i.e., the
ternary Veblen function `φ(ξ,0,·)`, for all complete `ξ` (including limits),
and deduce that `φ_{Ω²}` enumerates the fixpoints of `ξ ↦ φ(ξ,0,0)`. -/

/-- Rocq: `BachmannCalibration.bmono_small`. -/
theorem bmono_small (f : Ordinal.{u} → Ordinal.{u}) (x : BOrd.{u}) (H : BMono f x) : ∀ a, BMono f (bsmallSz x a) := by
  cases x; exact H.1

/-- Rocq: `BachmannCalibration.bmono_big`. -/
theorem bmono_big (f : Ordinal.{u} → Ordinal.{u}) (x : BOrd.{u}) (H : BMono f x) :
    ∀ c ξ, BMono f (bbigSz x c ξ) := by
  cases x; exact H.2.1

/-- Rocq: `BachmannCalibration.bmono_diag`. -/
theorem bmono_diag (f : Ordinal.{u} → Ordinal.{u}) (x : BOrd.{u}) (H : BMono f x) :
    ∀ c ξ ξ', ξ ≤ ξ' → bach f (bbigSz x c ξ) 0 ≤ bach f (bbigSz x c ξ') 0 := by
  cases x; exact H.2.2

/-- Rocq: `BachmannCalibration.bmono_bsup`. -/
theorem bmono_bsup (f : Ordinal.{u} → Ordinal.{u}) {I : Type u} (F : I → BOrd.{u}) (H : ∀ i, BMono f (F i)) :
    BMono f (bsup F) :=
  ⟨fun p => bmono_small f _ (H p.1) p.2, fun p ξ => bmono_big f _ (H p.1) p.2 ξ,
    fun p ξ ξ' hξ => bmono_diag f _ (H p.1) p.2 ξ ξ' hξ⟩

/-- Rocq: `BachmannCalibration.bmono_bmulΩ`. -/
theorem bmono_bmulΩ (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ ξ : Ordinal.{u}, BMono f (bmul bOmega (embed ξ))
  | mk X k => by
    rw [bmul_eq bOmega (embed (mk X k))]
    exact bmono_blub f _ _ (bmono_bsup f _ fun a => bmono_badd_Ω f hf _ (bmono_bmulΩ f hf (k a)))
      ⟨fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e)⟩

/-- Rocq: `BachmannCalibration.bsub_badd_embed_l`. -/
theorem bsub_badd_embed_l (x x' : BOrd.{u}) (H : bsub x x') :
    ∀ ζ : Ordinal.{u}, bsub (badd x (embed ζ)) (badd x' (embed ζ))
  | mk Z m => by
    rw [badd_eq x (embed (mk Z m)), badd_eq x' (embed (mk Z m))]
    exact bsub_blub _ _ _ _ H ⟨fun b => ⟨b, bsub_badd_embed_l x x' H (m b)⟩, fun e => (nomatch e)⟩

/-- Rocq: `BachmannCalibration.bsub_badd_Ω_l`. -/
theorem bsub_badd_Ω_l (x x' : BOrd.{u}) (H : bsub x x') : bsub (badd x bOmega) (badd x' bOmega) := by
  rw [badd_eq x bOmega, badd_eq x' bOmega]
  exact bsub_blub _ _ _ _ H ⟨fun e => (nomatch e), fun _ => ⟨⟨⟩, fun ζ => bsub_badd_embed_l x x' H ζ⟩⟩

/-- Rocq: `BachmannCalibration.bsub_bmulΩ`. -/
theorem bsub_bmulΩ : ∀ ξ ξ' : Ordinal.{u}, ξ ≤ ξ' → bsub (bmul bOmega (embed ξ)) (bmul bOmega (embed ξ'))
  | mk X k, mk X' k', H => by
    rw [bmul_eq _ (embed (mk X k)), bmul_eq _ (embed (mk X' k'))]
    refine bsub_blub _ _ _ _ (bsub_bsup _ _ fun a => ?_) ⟨fun e => (nomatch e), fun e => (nomatch e)⟩
    obtain ⟨b, hb⟩ := le_subord H a
    exact ⟨b, bsub_badd_Ω_l _ _ (bsub_bmulΩ (k a) (k' b) hb)⟩

/-- Classification of the components of `α+Ω`. Rocq: `BachmannCalibration.bcomp_badd_Ω_forall`. -/
theorem bcomp_badd_Ω_forall (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) (P : (Ordinal.{u} → Ordinal.{u}) → Prop)
    (H1 : ∀ k, P (bcomp f T k)) (H2 : P fun ζ => bach f (badd T (embed ζ)) 0) :
    ∀ k, P (bcomp f (badd T bOmega) k) := by
  cases T with
  | bnode A g C h =>
  intro k
  match k with
  | .inl (.inl a) => exact H1 (.inl a)
  | .inl (.inr e) => exact nomatch e
  | .inr (.inl c) => exact H1 (.inr c)
  | .inr (.inr _) => exact H2

/-- Rocq: `BachmannCalibration.badd_Ω_diag`. -/
theorem badd_Ω_diag (f : Ordinal.{u} → Ordinal.{u}) (T : BOrd.{u}) :
    ∃ k, bcomp f (badd T bOmega) k = fun ζ => bach f (badd T (embed ζ)) 0 := by
  cases T; exact ⟨.inr (.inr ⟨⟩), rfl⟩

/-- Classification of the components of `Ω·ξ`. Rocq: `BachmannCalibration.bcomp_bmulΩ_forall`. -/
theorem bcomp_bmulΩ_forall (f : Ordinal.{u} → Ordinal.{u}) (X : Type u) (k : X → Ordinal.{u})
    (P : (Ordinal.{u} → Ordinal.{u}) → Prop)
    (H : ∀ b kk, P (bcomp f (badd (bmul bOmega (embed (k b))) bOmega) kk)) :
    ∀ kk, P (bcomp f (bmul bOmega (embed (mk X k))) kk) := by
  intro kk
  match kk with
  | .inl (.inl ⟨b, a⟩) => exact H b (.inl a)
  | .inl (.inr e) => exact nomatch e
  | .inr (.inl ⟨b, c⟩) => exact H b (.inr c)
  | .inr (.inr e) => exact nomatch e

/-- Rocq: `BachmannCalibration.bach_bmulΩ_diag_le`. -/
theorem bach_bmulΩ_diag_le (f : Ordinal.{u} → Ordinal.{u}) (X : Type u) (k : X → Ordinal.{u}) (y : Ordinal.{u})
    (b : X) :
    fixOrd (fun ζ => bach f (badd (bmul bOmega (embed (k b))) (embed ζ)) 0)
        (lim fun j : y => bach f (bmul bOmega (embed (mk X k))) (y j)) ≤
      bach f (bmul bOmega (embed (mk X k))) y := by
  obtain ⟨kk, hkk⟩ := badd_Ω_diag f (bmul bOmega (embed (k b)))
  rw [← hkk]
  match kk with
  | .inl a => exact bach_comp_le f (bmul bOmega (embed (mk X k))) y (.inl (.inl ⟨b, a⟩))
  | .inr c => exact bach_comp_le f (bmul bOmega (embed (mk X k))) y (.inr (.inl ⟨b, c⟩))

/-- Rocq: `BachmannCalibration.lt_0_2`. -/
theorem lt_0_2 : (0 : Ordinal.{u}) < succ 1 := lt_intro ⟨⟩ (zero_least _)

/-- `φ_{Ω·ξ}` is the ternary Veblen function `φ(ξ,0,·)`.
Rocq: `BachmannCalibration.bach_Ωtimes_rep`. -/
theorem bach_Ωtimes_rep (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ ξ, Complete ξ → BRep f (bmul bOmega (embed ξ)) (S2 f ξ) := by
  have hfm := hf.monotone
  intro ξ
  induction ξ with
  | mk X k ihk =>
  intro hξ
  have hkc : ∀ b, Complete (k b) := fun b => complete_subord hξ b
  have HS : NormalFunction (S2 f (mk X k)) := schutte_column_normal _ _ f complete_2 hξ hf
  have HSk : ∀ b, NormalFunction (S2 f (k b)) := fun b => schutte_column_normal _ _ f complete_2 (hkc b) hf
  have HT : BMono f (bmul bOmega (embed (mk X k))) := bmono_bmulΩ f hfm _
  have HTk : ∀ b, BMono f (bmul bOmega (embed (k b))) := fun b => bmono_bmulΩ f hfm _
  have Hplus : ∀ b ζ, Complete ζ → BRep f (badd (bmul bOmega (embed (k b))) (embed ζ)) (veblen (S2 f (k b)) ζ) :=
    fun b ζ hζ => bach_veblen_step f hfm _ _ (HTk b) (ihk b (hkc b)) ζ hζ
  have Hdiag : ∀ b x, Complete x →
      bach f (badd (bmul bOmega (embed (k b))) (embed x)) 0 ≈ schutteColumn (S2 f (k b)) 1 x 0 := fun b x hx =>
    equiv_trans ((Hplus b x hx).2.1 0 zero_complete)
      (equiv_symm (schutte_column_veblen x 0 _ (HSk b) hx zero_complete))
  -- every component fixes the values of S2 ξ
  have Hcomp : ∀ kk y, Complete y →
      bcomp f (bmul bOmega (embed (mk X k))) kk (S2 f (mk X k) y) ≤ S2 f (mk X k) y := by
    intro kk y hy
    have hv := HS.complete y hy
    refine bcomp_bmulΩ_forall f X k (fun g => g (S2 f (mk X k) y) ≤ S2 f (mk X k) y) (fun b => ?_) kk
    have Hfix0 : S2 f (k b) (S2 f (mk X k) y) ≤ S2 f (mk X k) y :=
      le_trans ((HSk b).monotone _ _ (le_add_right _ 0))
        (le_trans (schutte_column0 _ _ 0).ge (schutte_column_fixpoint (succ 1) (mk X k) y f 0 (k b) complete_2 hξ hf
          lt_0_2 (index_lt (mk X k) b) zero_complete (hkc b) hy))
    refine bcomp_badd_Ω_forall f (bmul bOmega (embed (k b))) (fun g => g (S2 f (mk X k) y) ≤ S2 f (mk X k) y)
      (fun kk' => ?_) ?_
    · exact le_trans (bmono_bcomp f hfm _ (HTk b) kk' _ _ (normal_inflationary (HSk b) _ hv))
        (le_trans ((ihk b (hkc b)).2.2 kk' _ hv) Hfix0)
    · exact le_trans (Hdiag b _ hv).le
        (schutte_column_fixpoint (succ 1) (mk X k) y f 1 (k b) complete_2 hξ hf (succ_lt 1) (index_lt (mk X k) b)
          complete_1 (hkc b) hy)
  refine ⟨HS, ?_, Hcomp⟩
  intro y
  induction y with
  | mk Y h ihy =>
  intro hyc
  have hhc : ∀ j, Complete (h j) := fun j => complete_subord hyc j
  have Hs : lim (fun j : Y => bach f (bmul bOmega (embed (mk X k))) (h j)) ≈ lim (fun j : Y => S2 f (mk X k) (h j)) :=
    lim_eq_mor _ _ _ fun j => ihy j (hhc j)
  have Hsc : Complete (lim fun j : Y => S2 f (mk X k) (h j)) := lim_normal_complete (mk Y h) _ HS hyc
  refine equiv_intro ?_ ?_
  · refine bach_le_comp f _ _ _ (le_trans (hfm _ _ (le_add_left _ _)) (schutte_column_le_f _ _ _ f hfm))
      fun kk => ?_
    exact fixOrd_least (bmono_bcomp f hfm _ HT kk) _ _
      (le_trans Hs.le (limit_least fun j => HS.increasing _ _ hyc (index_lt (mk Y h) j))) (Hcomp kk _ hyc)
  · refine le_trans (schutte_column_succ f 1 (mk X k) (mk Y h) hf complete_1 hξ hyc).le
      (lub_least (f_le_bach f _ _) (sup_least fun b => ?_))
    have HN1 := schutte_column_normal_arg 1 (S2 f (k b)) complete_1 (HSk b)
    exact le_trans (fixOrd_eq_func_complete (fun ζ => bach f (badd (bmul bOmega (embed (k b))) (embed ζ)) 0)
        (fun δ => schutteColumn (S2 f (k b)) 1 δ 0) _ _ (Hdiag b) (badd_embed_diag_mono f hfm _ (HTk b))
        HN1.monotone HN1.complete Hs Hsc).ge
      (bach_bmulΩ_diag_le f X k (mk Y h) b)

/-- Rocq: `BachmannCalibration.bOmegaSq`. -/
def bOmegaSq : BOrd.{u} := bmul bOmega bOmega

/-- `φ_{Ω²}` enumerates the fixpoints of `ξ ↦ φ(ξ,0,0)`. Rocq: `BachmannCalibration.bach_Ωsq_rep`. -/
theorem bach_Ωsq_rep (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    BRep f bOmegaSq (enumFixpoints fun ξ => S2 f ξ 0) := by
  have hfm := hf.monotone
  have HN : NormalFunction fun ξ => S2 f ξ 0 := schutte_column_normal_arg _ f complete_2 hf
  refine bach_enum_step f bOmegaSq _ (.inr (.inr ⟨⟩)) HN ?_ ?_ ?_ ?_
  · intro kk x y hxy
    match kk with
    | .inl (.inl ⟨e, _⟩) => exact nomatch e
    | .inl (.inr e) => exact nomatch e
    | .inr (.inl ⟨e, _⟩) => exact nomatch e
    | .inr (.inr _) => exact bach_mono_index f hfm _ _ (bsub_bmulΩ x y hxy) (bmono_bmulΩ f hfm y) 0
  · exact fun x hx => (bach_Ωtimes_rep f hf x hx).2.1 0 zero_complete
  · exact fun x _ => le_trans (hfm _ _ (add_zero x).ge) (schutte_column_le_f _ _ _ f hfm)
  · intro kk y hy
    have hv : Complete (enumFixpoints (fun ξ => S2 f ξ 0) y) := (enum_fixpoints_normal HN).complete y hy
    match kk with
    | .inl (.inl ⟨e, _⟩) => exact nomatch e
    | .inl (.inr e) => exact nomatch e
    | .inr (.inl ⟨e, _⟩) => exact nomatch e
    | .inr (.inr _) =>
      show bach f (bmul bOmega (embed (enumFixpoints (fun ξ => S2 f ξ 0) y))) 0 ≤ _
      exact le_trans ((bach_Ωtimes_rep f hf _ hv).2.1 0 zero_complete).le (Con.enum_are_fixpoints HN y hy).ge

/-- With base `1+x`, `φ_{Ω²}(0)` is Ackermann's ordinal, as defined in
`AckermannTower`. Rocq: `BachmannCalibration.bach_Ωsq_Ackermann`. -/
theorem bach_Ωsq_Ackermann : bach (fun y => 1 + y) bOmegaSq 0 ≈ AckermannOrdinal.{u} := by
  have HN : NormalFunction fun ξ => S2 (fun y : Ordinal.{u} => 1 + y) ξ 0 :=
    schutte_column_normal_arg _ _ complete_2 onePlus_normal
  refine equiv_trans ((bach_Ωsq_rep _ onePlus_normal).2.1 0 zero_complete) (equiv_trans (enumFixpoints_zero HN.monotone) ?_)
  exact fixOrd_eq_func_complete _ _ _ _
    (fun x hx => schutte_column_2_ackermann_tower _ x 0 onePlus_normal hx zero_complete) HN.monotone
    (fun x y hxy => ackermann_tower_monotone _ onePlus_normal.monotone x y 0 0 hxy (le_refl 0))
    (ackermann_tower_normal_first _ onePlus_normal).complete (equiv_refl 0) zero_complete

/-! ## The Small and Large Veblen Ordinals -/

/-- Rocq: `BachmannCalibration.bach_SVO`. -/
theorem bach_SVO (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    bach f (bexpΩ (embed ω)) 0 ≈ schutteColumn f ω 1 0 :=
  equiv_trans (bach_bexpΩ_zero f hf ω omega_complete)
    (equiv_intro (schutte_column_monotoneβ _ _ 1 0 f hf.monotone (limit_onePlus omega_limit))
      (schutte_column_monotoneβ _ _ 1 0 f hf.monotone (le_add_left 1 ω)))

/-- Rocq: `BachmannCalibration.bach_SVO_SmallVeblen`. -/
theorem bach_SVO_SmallVeblen : bach powOmega (bexpΩ (embed ω)) 0 ≈ SmallVeblenOrdinal.{u} :=
  bach_SVO powOmega powOmega_normal

/-- Rocq: `BachmannCalibration.LVO_onePlus`. -/
theorem LVO_onePlus (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    fixOrd (fun ζ => schutteColumn f (1 + ζ) 1 0) 0 ≈ fixOrd (fun β => schutteColumn f β 1 0) 0 := by
  have hfm := hf.monotone
  have HF := schutte_column_normalβ f hf
  have HLc : Complete (fixOrd (fun β => schutteColumn f β 1 0) 0) :=
    normal_fix_complete _ zero_complete (normal_inflationary HF) HF.monotone HF.complete
  have HLfix := normal_fixpoint HF 0 zero_complete
  have Hmono1 : ∀ x y : Ordinal.{u}, x ≤ y → schutteColumn f (1 + x) 1 0 ≤ schutteColumn f (1 + y) 1 0 :=
    fun x y h => schutte_column_monotoneβ _ _ 1 0 f hfm (add_le_add (le_refl 1) h)
  refine equiv_intro (fixOrd_least Hmono1 _ _ (zero_least _) ?_)
    (fixOrd_monotone_func (fun x => schutte_column_monotoneβ _ _ 1 0 f hfm (le_add_left 1 x)) Hmono1 0)
  exact le_trans (schutte_column_monotoneβ _ _ 1 0 f hfm (le_trans (onePlus_least_normal HF _ HLc) HLfix.ge))
    HLfix.ge

/-- `Ω^Ω` is the canonical tree `bexpΩ bOmega`: the small child 0 (from the
leading 1) and the single family `ζ ↦ Ω^ζ`. Rocq: `BachmannCalibration.bach_LVO`. -/
theorem bach_LVO (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    bach f (bexpΩ bOmega) 0 ≈ fixOrd (fun β => schutteColumn f β 1 0) 0 := by
  have hfm := hf.monotone
  have HF := schutte_column_normalβ f hf
  have HLc : Complete (fixOrd (fun β => schutteColumn f β 1 0) 0) :=
    normal_fix_complete _ zero_complete (normal_inflationary HF) HF.monotone HF.complete
  have HLfix := normal_fixpoint HF 0 zero_complete
  have HDmono : ∀ x y : Ordinal.{u}, x ≤ y → bach f (bexpΩ (embed x)) 0 ≤ bach f (bexpΩ (embed y)) 0 :=
    fun x y hxy => bach_mono_index f hfm _ _ (bsub_bexpΩ _ _ (bsub_embed x y hxy))
      (bfam_bmono f hfm _ (bfam_bexpΩ _ (bfam_embed y))) 0
  have HD'mono : ∀ x y : Ordinal.{u}, x ≤ y → schutteColumn f (1 + x) 1 0 ≤ schutteColumn f (1 + y) 1 0 :=
    fun x y hxy => schutte_column_monotoneβ _ _ 1 0 f hfm (add_le_add (le_refl 1) hxy)
  have HD'c : ∀ x : Ordinal.{u}, Complete x → Complete (schutteColumn f (1 + x) 1 0) := fun x hx =>
    (schutte_column_normal _ _ f (onePlus_complete hx) complete_1 hf).complete 0 zero_complete
  have Hs0 : lim (fun j : (0 : Ordinal.{u}) => bach f (bexpΩ bOmega) ((0 : Ordinal.{u}) j)) ≈ 0 :=
    equiv_intro (limit_least fun e => (nomatch e)) (zero_least _)
  have Hdiag : fixOrd (fun ζ => bach f (bexpΩ (embed ζ)) 0)
        (lim fun j : (0 : Ordinal.{u}) => bach f (bexpΩ bOmega) ((0 : Ordinal.{u}) j)) ≈
      fixOrd (fun β => schutteColumn f β 1 0) 0 :=
    equiv_trans (fixOrd_eq_func_complete _ (fun ζ => schutteColumn f (1 + ζ) 1 0) _ _
      (fun x hx => bach_bexpΩ_zero f hf x hx) HDmono HD'mono HD'c Hs0 zero_complete) (LVO_onePlus f hf)
  -- the value L is a fixpoint of f
  have HL0 : 0 < fixOrd (fun β => schutteColumn f β 1 0) 0 :=
    lt_of_lt_of_le (lt_of_lt_of_le (hf.nonzero (1 + 0)) (schutte_column_le_f _ 1 0 f hfm)) HLfix.ge
  have HfL : f (fixOrd (fun β => schutteColumn f β 1 0) 0) ≤ fixOrd (fun β => schutteColumn f β 1 0) 0 := by
    refine le_trans (hfm _ _ HLfix.le) (le_trans ?_ HLfix.ge)
    calc f (schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 1 0)
        ≤ schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 0
            (schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 1 0) := (schutte_column_arg0 _ _ f hfm).ge
      _ ≤ schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 0
            (schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 1 0 + 0) :=
          schutte_column_monotone f _ 0 _ 0 _ hfm (le_refl 0) (le_add_right _ 0)
      _ ≤ schutteColumn (schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 0) 0
            (schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 1 0) 0 := (schutte_column0 _ _ 0).ge
      _ ≤ schutteColumn f (fixOrd (fun β => schutteColumn f β 1 0) 0) 1 0 :=
          schutte_column_fixpoint _ 1 0 f 0 0 HLc complete_1 hf HL0 (succ_lt 0) zero_complete zero_complete
            zero_complete
  refine equiv_intro (bach_le_comp f _ 0 _ (le_trans (hfm _ _ (zero_least _)) HfL) fun kk => ?_)
    (le_trans Hdiag.ge (bach_comp_le f (bexpΩ bOmega) 0 (.inr (.inr (.inr ⟨⟩)))))
  match kk with
  | .inl (.inl _) =>
    refine fixOrd_least (bmono_bcomp f hfm _ (bfam_bmono f hfm _ (bfam_bexpΩ _ bfam_Ω)) (.inl (.inl ⟨⟩))) _ _
      (limit_least fun e => (nomatch e)) ?_
    show bach f bzero _ ≤ _
    exact le_trans (bach_bzero f _).le HfL
  | .inl (.inr (.inl ⟨e, _⟩)) => exact nomatch e
  | .inl (.inr (.inr e)) => exact nomatch e
  | .inr (.inl e) => exact nomatch e
  | .inr (.inr (.inl ⟨e, _⟩)) => exact nomatch e
  | .inr (.inr (.inr _)) => exact Hdiag.le

/-- Rocq: `BachmannCalibration.bach_LVO_LargeVeblen`. -/
theorem bach_LVO_LargeVeblen : bach powOmega (bexpΩ bOmega) 0 ≈ LargeVeblenOrdinal.{u} :=
  bach_LVO powOmega powOmega_normal

end Bachmann

end ConstructiveOrdinals
