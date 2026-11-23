import ConstructiveOrdinals.Bachmann.Normal

/-!
# Agreement of Bachmann's `φ` with `bphi`, and the Bachmann–Howard ordinal

On the canonical trees up to `ε_{Ω+1}`, Bachmann's `φ` (`bach`, one component
at a time) agrees with the provably normal `bphi`. This needs the components
to be nested and directed, which we establish structurally. The end result
certifies `bach` at the Bachmann–Howard ordinal.

Ported from the Rocq file `BachmannAgree.v`.

Lean notes:

- As for `bslt`, the first argument of `bleZ` is uniform in Rocq's
  constructors and is a parameter here.
- Rocq's section-local `Hfm` (monotonicity of `f`) is `hf.monotone`.
  Rocq: `BachmannAgree.Hfm`.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-! ## Calibration of `bphi` against the Veblen hierarchy

Below `Ω`, `bphi` is the Veblen hierarchy: `bphi f (embed β) = veblen f β`. The
children of the ordinal `β` are the `β_i`, matching the family `{φ_{β_i}}`
whose common fixpoints `cfe` enumerates; when `β = 0` both sides are `f`. At
`Ω`, `bphi f bOmega` enumerates the fixpoints of `ξ ↦ φ(ξ,0)`, i.e., `Γ`. -/

/-- Rocq: `BachmannAgree.bphi_embed`. -/
theorem bphi_embed (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ β : Ordinal.{u}, Complete β → ∀ y, Complete y → bphi f (embed β) y ≈ veblen f β y := by
  intro β
  induction β with
  | mk X k ihk =>
  intro hβ
  have hkc : ∀ i, Complete (k i) := fun i => complete_subord hβ i
  have HV : NormalFunction (veblen f (mk X k)) := veblen_normal hf _ hβ
  have HE : NormalFunction (bphi f (embed (mk X k))) := bcanon_normal f hf _ (bcd_embed _ hβ)
  have HF : ∀ i, NormalFunction (bphi_fam f (fun a => embed (k a)) (PEmpty.elim : PEmpty → Ordinal.{u} → BOrd.{u}) i) :=
    fun i => match i with
      | .inl i => bcanon_normal f hf _ (bcd_embed _ (hkc i))
      | .inr e => nomatch e
  intro y
  induction y with
  | mk Y h ihy =>
  intro hyc
  have hhc : ∀ j, Complete (h j) := fun j => complete_subord hyc j
  have HVc := HV.complete _ hyc
  have HEc := HE.complete _ hyc
  have Hstart : lim (fun j : Y => bphi f (embed (mk X k)) (h j)) ≤ bphi f (embed (mk X k)) (mk Y h) :=
    limit_least fun j => HE.increasing _ _ hyc (index_lt (mk Y h) j)
  refine equiv_intro ?_ ?_
  · show cfe f (X ⊕ PEmpty) (bphi_fam f (fun a => embed (k a)) PEmpty.elim) (mk Y h) ≤ veblen f (mk X k) (mk Y h)
    refine cfe_least f hf _ _ HF _ _ ?_ ?_ fun i => ?_
    · rw [veblen_unroll]; exact lub_le1 _ _
    · exact limit_least fun j => lt_of_le_of_lt (ihy j (hhc j)).le (HV.increasing _ _ hyc (index_lt (mk Y h) j))
    · match i with
      | .inl i =>
        exact ⟨le_trans (ihk i (hkc i) _ HVc).le
            (veblen_fixpoints hf (k i) (mk X k) (mk Y h) (hkc i) hβ hyc (index_lt (mk X k) i)).le,
          le_trans (veblen_zero f _).ge
            (veblen_fixpoints hf 0 (mk X k) (mk Y h) zero_complete hβ hyc
              (lt_of_le_of_lt (zero_least (k i)) (index_lt (mk X k) i))).le⟩
      | .inr e => exact nomatch e
  · rw [veblen_unroll f (mk X k) (mk Y h)]
    refine lub_least (bphi_ge_f f _ _) (sup_least fun i => ?_)
    refine fixOrd_least (veblen_monotone hf.monotone (k i)) _ _ ?_ ?_
    · exact limit_least fun j => lt_of_le_of_lt (ihy j (hhc j)).ge
        (lt_of_lt_of_le (limit_lt (fun j : Y => bphi f (embed (mk X k)) (h j)) j) Hstart)
    · exact le_trans (ihk i (hkc i) _ HEc).ge (cfe_fix_F f hf _ _ HF (.inl i) (mk Y h) hyc)

/-- Rocq: `BachmannAgree.bphi_Ω`. -/
theorem bphi_Ω (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ y : Ordinal.{u}, Complete y → bphi f bOmega y ≈ enumFixpoints (fun ξ => veblen f ξ 0) y := by
  have hfm := hf.monotone
  have HD' : NormalFunction fun ξ => veblen f ξ 0 := veblen_first_normal hf
  have HG := enum_fixpoints_normal HD'
  have Hgood := (bcanon_good f hf _ bcanon_Ω bdec_Ω).2
  have HF : ∀ i, NormalFunction (bphi_fam f (PEmpty.elim : PEmpty → BOrd.{u}) (fun _ : PUnit => embed) i) :=
    fun i => match i with
      | .inl e => nomatch e
      | .inr _ => bgood_diag f bOmega ⟨⟩ Hgood
  have HE := bphi_Ω_normal f hf
  intro y
  induction y with
  | mk Y h ihy =>
  intro hyc
  have hhc : ∀ j, Complete (h j) := fun j => complete_subord hyc j
  have HGc := HG.complete _ hyc
  have HEc := HE.complete _ hyc
  have HGfix := Con.enum_are_fixpoints HD' (mk Y h) hyc
  refine equiv_intro ?_ ?_
  · show cfe f (PEmpty ⊕ PUnit) (bphi_fam f PEmpty.elim fun _ : PUnit => embed) (mk Y h) ≤ _
    have HfG : f (enumFixpoints (fun ξ => veblen f ξ 0) (mk Y h)) ≤ enumFixpoints (fun ξ => veblen f ξ 0) (mk Y h) :=
      le_trans (hfm _ _ HGfix.le) (le_trans (veblen_zero f _).ge
        (le_trans (veblen_fixpoints hf 0 _ 0 zero_complete HGc zero_complete (HG.nonzero _)).le HGfix.ge))
    refine cfe_least f hf _ _ HF _ _ (le_trans (hfm _ _ (normal_inflationary HG _ hyc)) HfG)
      (limit_least fun j => lt_of_le_of_lt (ihy j (hhc j)).le (HG.increasing _ _ hyc (index_lt (mk Y h) j)))
      fun i => ?_
    match i with
    | .inl e => exact nomatch e
    | .inr _ => exact ⟨le_trans (bphi_embed f hf _ HGc 0 zero_complete).le HGfix.ge, HfG⟩
  · show fixOrd (fun ξ => veblen f ξ 0) (mk Y fun j => enumFixpoints (fun ξ => veblen f ξ 0) (h j)) ≤ _
    refine fixOrd_least (fun x y hxy => veblen_monotone_first hfm y x 0 hxy) _ _ ?_ ?_
    · exact limit_least fun j => lt_of_le_of_lt (ihy j (hhc j)).ge (HE.increasing _ _ hyc (index_lt (mk Y h) j))
    · exact le_trans (bphi_embed f hf _ HEc 0 zero_complete).ge (cfe_fix_F f hf _ _ HF (.inr ⟨⟩) (mk Y h) hyc)

/-- Rocq: `BachmannAgree.bphi_Ω_Γ`. -/
theorem bphi_Ω_Γ (y : Ordinal.{u}) (hy : Complete y) : bphi powOmega bOmega y ≈ Γ y :=
  bphi_Ω powOmega powOmega_normal y hy

/-! ## Structural directedness

A component of a node is described either by a small child `x` or by an
Ω-family `h`; its semantics is `φ_x`, respectively `ξ ↦ φ_{h ξ}(0)`. We give
structural conditions (`D0`) under which one component dominates another,
close them under chaining through canonical intermediate components
(`Dstar`), and show this implies semantic domination. -/

/-- Descriptions of components. Rocq: `BachmannAgree.bdesc`. -/
inductive bdesc : Type (u + 1) where
  /-- Rocq: `BachmannAgree.DSmall`. -/
  | DSmall : BOrd.{u} → bdesc
  /-- Rocq: `BachmannAgree.DFam`. -/
  | DFam : (Ordinal.{u} → BOrd.{u}) → bdesc

/-- Rocq: `BachmannAgree.dcan`. -/
def DCan : bdesc.{u} → Prop
  | .DSmall x => BCd x
  | .DFam h => BCd (blimΩ h)

/-- `x` lies (non-strictly) below a descendant of `y` reached through small
children and family members at arguments at most `z`. If `z` is a common
fixpoint of `y`'s components, then `φ_x(0) ≤ z`. Rocq: `BachmannAgree.bleZ`. -/
inductive bleZ (z : Ordinal.{u}) (x : BOrd.{u}) : BOrd.{u} → Prop
  /-- Rocq: `BachmannAgree.LZ_sub`. -/
  | sub (y : BOrd.{u}) : bsub x y → bleZ z x y
  /-- Rocq: `BachmannAgree.LZ_small`. -/
  | small (y : BOrd.{u}) (b : bsmall y) : bleZ z x (bsmallSz y b) → bleZ z x y
  /-- Rocq: `BachmannAgree.LZ_big`. -/
  | big (y : BOrd.{u}) (d : bbig y) (ζ : Ordinal.{u}) : ζ ≤ z → bleZ z x (bbigSz y d ζ) → bleZ z x y

/-- Rocq: `BachmannAgree.bleZ_mono_r`. -/
theorem bleZ_mono_r (z : Ordinal.{u}) (x y y' : BOrd.{u}) (H : bleZ z x y) (Hy : bsub y y') : bleZ z x y' := by
  induction H generalizing y' with
  | sub y H => exact .sub _ (bsub_trans H Hy)
  | small y b _ ih =>
    obtain ⟨b', hb'⟩ := bsub_small _ _ Hy b
    exact .small _ b' (ih _ hb')
  | big y d ζ hζ _ ih =>
    obtain ⟨d', hd'⟩ := bsub_big _ _ Hy d
    exact .big _ d' ζ hζ (ih _ (hd' ζ))

/-- Rocq: `BachmannAgree.bleZ_shift`. -/
theorem bleZ_shift (x : BOrd.{u}) (z : Ordinal.{u}) (a b : BOrd.{u}) (H : bleZ z a b) :
    bleZ z (badd x a) (badd x b) := by
  induction H with
  | sub b H => exact .sub _ (bsub_badd_r _ _ _ H)
  | small b j _ ih =>
    obtain ⟨t, ht⟩ := badd_small_r x b j
    exact .small _ t (by rw [ht]; exact ih)
  | big b d ζ hζ _ ih =>
    obtain ⟨t, ht⟩ := badd_big_r x b d
    exact .big _ t ζ hζ (by rw [ht]; exact ih)

/-- Rocq: `BachmannAgree.bleZ_mul`. -/
theorem bleZ_mul (x : BOrd.{u}) (z : Ordinal.{u}) (a b : BOrd.{u}) (H : bleZ z a b) :
    bleZ z (bmul x a) (bmul x b) := by
  induction H with
  | sub b H => exact .sub _ (bsub_bmul_r _ _ _ H)
  | small b j _ ih => exact bleZ_mono_r _ _ _ _ ih (bsub_trans (bsub_le_badd _ _) (bsub_bmul_step x b j))
  | big b d ζ hζ _ ih =>
    obtain ⟨t, ht⟩ := bmul_big_fam x b d
    exact .big _ t ζ hζ (by rw [ht]; exact ih)

/-- Structural domination of one component by another. Rocq: `BachmannAgree.D0`. -/
inductive D0 : bdesc.{u} → bdesc.{u} → Prop
  /-- Rocq: `BachmannAgree.D0_ss_sub`. -/
  | ss_sub (x y : BOrd.{u}) : bsub x y → D0 (.DSmall x) (.DSmall y)
  /-- Rocq: `BachmannAgree.D0_ss_lt`. -/
  | ss_lt (x y : BOrd.{u}) : bslt x y → D0 (.DSmall x) (.DSmall y)
  /-- Rocq: `BachmannAgree.D0_sf`. -/
  | sf (x : BOrd.{u}) (h : Ordinal.{u} → BOrd.{u}) (n : Nat) : bslt x (h (ofNat n)) → D0 (.DSmall x) (.DFam h)
  /-- Rocq: `BachmannAgree.D0_fs`. -/
  | fs (h : Ordinal.{u} → BOrd.{u}) (y : BOrd.{u}) (e : bbig y) :
      (∀ ξ, bsub (h ξ) (bbigSz y e ξ)) → D0 (.DFam h) (.DSmall y)
  /-- Rocq: `BachmannAgree.D0_ff_pt`. -/
  | ff_pt (h1 h3 : Ordinal.{u} → BOrd.{u}) : (∀ ξ, bsub (h1 ξ) (h3 ξ)) → D0 (.DFam h1) (.DFam h3)
  /-- Rocq: `BachmannAgree.D0_ff_in`. -/
  | ff_in (h1 h3 : Ordinal.{u} → BOrd.{u}) (n : Nat) (e : bbig (h3 (ofNat n))) :
      (∀ ξ, bsub (h1 ξ) (bbigSz (h3 (ofNat n)) e ξ)) → D0 (.DFam h1) (.DFam h3)
  /-- Rocq: `BachmannAgree.D0_ffZ`. -/
  | ffZ (h1 h3 : Ordinal.{u} → BOrd.{u}) :
      (∀ z, (∀ n : Nat, ofNat n ≤ z) → bleZ z (h1 z) (h3 z)) → D0 (.DFam h1) (.DFam h3)

/-- Chains of structural domination through canonical components.
Rocq: `BachmannAgree.Dstar`. -/
inductive Dstar : bdesc.{u} → bdesc.{u} → Prop
  /-- Rocq: `BachmannAgree.Drefl`. -/
  | refl (d : bdesc.{u}) : Dstar d d
  /-- Rocq: `BachmannAgree.Dstep`. -/
  | step (d1 d2 d3 : bdesc.{u}) : DCan d2 → D0 d1 d2 → Dstar d2 d3 → Dstar d1 d3

/-- Rocq: `BachmannAgree.Dstar_trans`. -/
theorem Dstar_trans (d1 d2 d3 : bdesc.{u}) (H : Dstar d1 d2) (H' : Dstar d2 d3) : Dstar d1 d3 := by
  induction H with
  | refl _ => exact H'
  | step _ d2 _ hc h0 _ ih => exact .step _ d2 _ hc h0 (ih H')

/-- Rocq: `BachmannAgree.D0_star`. -/
theorem D0_star (d1 d2 : bdesc.{u}) (Hc : DCan d2) (H : D0 d1 d2) : Dstar d1 d2 := .step _ d2 _ Hc H (.refl _)

/-! ## Nesting

Bachmann's hierarchy takes least fixpoints of a node's components one at a
time, and agrees with the common-fixpoint enumerator only if the components
are nested. The basic nesting fact is that a tree strictly below `y` (in the
sense of `bslt`) has a `φ` that fixes every common fixpoint of `f` and `y`'s
components. For the family case the point is that a fixpoint `z` of a normal
diagonal is an exact value, `z = φ_{h z}(0)`, and hence fixed by the
components of `h z`. -/

/-- Rocq: `BachmannAgree.bfix`. -/
def BFix (f : Ordinal.{u} → Ordinal.{u}) (y : BOrd.{u}) (z : Ordinal.{u}) : Prop :=
  f z ≤ z ∧ (∀ a, bphi f (bsmallSz y a) z ≤ z) ∧ ∀ c, bphi f (bbigSz y c z) 0 ≤ z

section nest0

variable (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)

include hf in
/-- Rocq: `BachmannAgree.bfix_bsub`. -/
theorem bfix_bsub (a b : BOrd.{u}) (z : Ordinal.{u}) (H : bsub a b) (Hb : BFam b) (Hfix : BFix f b z) : BFix f a z := by
  obtain ⟨H1, H2, H3⟩ := Hfix
  refine ⟨H1, fun i => ?_, fun c => ?_⟩
  · obtain ⟨j, hj⟩ := bsub_small _ _ H i
    exact le_trans ((bphi_mono_index f hf.monotone _ (bfam_small _ Hb j)).2 _ hj z) (H2 j)
  · obtain ⟨d, hd⟩ := bsub_big _ _ H c
    exact le_trans ((bphi_mono_index f hf.monotone _ (bfam_big _ Hb d z)).2 _ (hd z) 0) (H3 d)

include hf in
/-- The components of `x` fix every value `w'` with `z ≤ φ_x(w) ≤ z`.
Rocq: `BachmannAgree.bfix_at`. -/
theorem bfix_at (x : BOrd.{u}) (z w : Ordinal.{u}) (Hx : BGood f x) (Hxf : BFam x) (Hw : Complete w)
    (_Hz : Complete z) (H1 : z ≤ bphi f x w) (H2 : bphi f x w ≤ z) (Hfz : f z ≤ z) : BFix f x z :=
  ⟨Hfz, fun a => le_trans ((bphi_normal hf _ (bgood_small f x a Hx)).monotone _ _ H1)
      (le_trans (bphi_fix_small' hf x a w Hx Hw) H2),
    fun c => le_trans ((bphi_mono_index f hf.monotone _ (bfam_big _ Hxf c _)).2 _ (bfam_fam _ Hxf c _ _ H1) 0)
      (le_trans (bphi_fix_big' hf x c w Hx Hw) H2)⟩

include hf in
/-- A fixpoint of `φ_x` is a common fixpoint of `f` and `x`'s components.
Rocq: `BachmannAgree.bfix_of_fix`. -/
theorem bfix_of_fix (x : BOrd.{u}) (z : Ordinal.{u}) (Hx : BGood f x) (Hxf : BFam x) (Hz : Complete z)
    (Hfix : bphi f x z ≤ z) : BFix f x z :=
  bfix_at f hf x z z Hx Hxf Hz Hz (normal_inflationary (bphi_normal hf x Hx) z Hz) Hfix
    (le_trans (bphi_ge_f f x z) Hfix)

include hf in
/-- A fixpoint `z` of a normal diagonal is the exact value `φ_{h z}(0)`, and
`h z` has a component (`z` is positive), so `z` is a fixpoint of `f`.
Rocq: `BachmannAgree.bfix_member`. -/
theorem bfix_member (y : BOrd.{u}) (d : bbig y) (z : Ordinal.{u}) (Hy : BGood f y) (Hyf : BFam y) (Hz : Complete z)
    (Hle : bphi f (bbigSz y d z) 0 ≤ z) : BFix f (bbigSz y d z) z :=
  have HD := bgood_diag f y d Hy
  have Hhz := bgood_big f y d z Hy Hz
  have Hzw : z ≤ bphi f (bbigSz y d z) 0 := normal_inflationary HD z Hz
  have Hpos : 0 < z := lt_of_lt_of_le (bphi_nonzero hf _ 0) Hle
  bfix_at f hf _ z 0 Hhz (bfam_big _ Hyf d z) zero_complete Hz Hzw Hle
    (le_trans (hf.monotone _ _ Hzw) (le_trans (bphi_fix_base' hf _ 0 Hhz (bgood_pos f y d z Hy Hz Hpos) zero_complete) Hle))

include hf in
/-- Rocq: `BachmannAgree.bphi_le_fix`. -/
theorem bphi_le_fix (y : BOrd.{u}) (z : Ordinal.{u}) (Hg : BGood f y) (_Hz : Complete z) (Hfix : BFix f y z) :
    bphi f y 0 ≤ z := by
  cases y with
  | bnode A g C h =>
  obtain ⟨H1, H2, H3⟩ := Hfix
  exact cfe_least f hf _ (bphi_fam f g h) (bphi_fam_normal' hf A g C h Hg) 0 z (le_trans (hf.monotone _ _ (zero_least z)) H1)
    (limit_least fun e => (nomatch e)) fun k => match k with
      | .inl a => ⟨H2 a, H1⟩
      | .inr c => ⟨H3 c, H1⟩

include hf in
/-- Rocq: `BachmannAgree.bnest`. -/
theorem bnest : ∀ x y : BOrd.{u}, bslt x y → BGood f y → BFam y → ∀ z, Complete z → BFix f y z → bphi f x z ≤ z := by
  intro x y H
  induction H with
  | small y j hj =>
    intro _ hfam z _ hfix
    exact le_trans ((bphi_mono_index f hf.monotone _ (bfam_small _ hfam j)).2 _ hj z) (hfix.2.1 j)
  | big y d n _ ih =>
    intro hg hfam z hz hfix
    have Hm := bfix_member f hf y d z hg hfam hz (hfix.2.2 d)
    exact ih (bgood_big f y d _ hg (ofNat_complete n)) (bfam_big _ hfam d _) z hz
      (bfix_bsub f hf _ _ z (bfam_fam _ hfam d _ _ (fix_onePlus_finite f hf z hz hfix.1 n)) (bfam_big _ hfam d z) Hm)
  | desc y j _ ih =>
    intro hg hfam z hz hfix
    exact ih (bgood_small f y j hg) (bfam_small _ hfam j) z hz
      (bfix_of_fix f hf _ z (bgood_small f y j hg) (bfam_small _ hfam j) hz (hfix.2.1 j))

include hf in
/-- Soundness of z-relative reachability, stated up to `bsub` of the target so
that family members are only visited at `z` itself. Rocq: `BachmannAgree.bleZ_sound`. -/
theorem bleZ_sound (z : Ordinal.{u}) (x y : BOrd.{u}) (H : bleZ z x y) :
    ∀ y', bsub y y' → BGood f y' → BFam y' → Complete z → BFix f y' z → bphi f x 0 ≤ z := by
  induction H with
  | sub y H =>
    intro y' hy hg hyf hz hfix
    exact le_trans ((bphi_mono_index f hf.monotone y' hyf).2 _ (bsub_trans H hy) 0) (bphi_le_fix f hf y' z hg hz hfix)
  | small y b _ ih =>
    intro y' hy hg hyf hz hfix
    obtain ⟨b', hb'⟩ := bsub_small _ _ hy b
    exact ih (bsmallSz y' b') hb' (bgood_small f y' b' hg) (bfam_small _ hyf b') hz
      (bfix_of_fix f hf _ z (bgood_small f y' b' hg) (bfam_small _ hyf b') hz (hfix.2.1 b'))
  | big y d ζ hζ _ ih =>
    intro y' hy hg hyf hz hfix
    obtain ⟨d', hd'⟩ := bsub_big _ _ hy d
    exact ih (bbigSz y' d' z) (bsub_trans (hd' ζ) (bfam_fam _ hyf d' ζ z hζ)) (bgood_big f y' d' z hg hz)
      (bfam_big _ hyf d' z) hz (bfix_member f hf y' d' z hg hyf hz (hfix.2.2 d'))

include hf in
/-- Rocq: `BachmannAgree.bleZ_nest`. -/
theorem bleZ_nest (z : Ordinal.{u}) (D y x : BOrd.{u}) (H : bleZ z D y) (Hx : bslt x D) :
    ∀ y', bsub y y' → BGood f y' → BFam y' → Complete z → BFix f y' z → bphi f x z ≤ z := by
  induction H with
  | sub y H =>
    intro y' hy hg hyf hz hfix
    exact bnest f hf x y' (bslt_bsub_r _ _ _ Hx (bsub_trans H hy)) hg hyf z hz hfix
  | small y b _ ih =>
    intro y' hy hg hyf hz hfix
    obtain ⟨b', hb'⟩ := bsub_small _ _ hy b
    exact ih (bsmallSz y' b') hb' (bgood_small f y' b' hg) (bfam_small _ hyf b') hz
      (bfix_of_fix f hf _ z (bgood_small f y' b' hg) (bfam_small _ hyf b') hz (hfix.2.1 b'))
  | big y d ζ hζ _ ih =>
    intro y' hy hg hyf hz hfix
    obtain ⟨d', hd'⟩ := bsub_big _ _ hy d
    exact ih (bbigSz y' d' z) (bsub_trans (hd' ζ) (bfam_fam _ hyf d' ζ z hζ)) (bgood_big f y' d' z hg hz)
      (bfam_big _ hyf d' z) hz (bfix_member f hf y' d' z hg hyf hz (hfix.2.2 d'))

end nest0

/-! ## Agreement of `bach` and `φ` under directed domination -/

/-- Rocq: `BachmannAgree.bdom`. -/
def BDom (f : Ordinal.{u} → Ordinal.{u}) {A C : Type u} (g : A → BOrd.{u}) (h : C → Ordinal.{u} → BOrd.{u})
    (k1 k3 : A ⊕ C) : Prop :=
  ∀ z, Complete z → bphi_fam f g h k3 z ≤ z → bphi_fam f g h k1 z ≤ z

/-- Rocq: `BachmannAgree.bdirH`. -/
def BDirH (f : Ordinal.{u} → Ordinal.{u}) : BOrd.{u} → Prop
  | bnode _ g _ h =>
    (∀ a, BDirH f (g a)) ∧ (∀ c ξ, Complete ξ → BDirH f (h c ξ)) ∧
      ∀ k1 k2, ∃ k3, BDom f g h k1 k3 ∧ BDom f g h k2 k3

/-- Every fixpoint of a component is a fixpoint of the base.
Rocq: `BachmannAgree.bphi_fam_fix_f`. -/
theorem bphi_fam_fix_f (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (A : Type u) (g : A → BOrd.{u})
    (C : Type u) (h : C → Ordinal.{u} → BOrd.{u}) (k : A ⊕ C) (z : Ordinal.{u}) (Hgood : BGood f (bnode A g C h))
    (Hz : Complete z) (Hk : bphi_fam f g h k z ≤ z) : f z ≤ z :=
  match k, Hk with
  | .inl a, Hk => le_trans (bphi_ge_f f (g a) z) Hk
  | .inr c, Hk =>
    have HD := bgood_diag f (bnode A g C h) c Hgood
    have Hhz := bgood_big f (bnode A g C h) c z Hgood Hz
    have Hzw : z ≤ bphi f (h c z) 0 := normal_inflationary HD z Hz
    have Hpos : 0 < z := lt_of_lt_of_le (bphi_nonzero hf _ 0) Hk
    le_trans (hf.monotone _ _ Hzw)
      (le_trans (bphi_fix_base' hf _ 0 Hhz (bgood_pos f (bnode A g C h) c z Hgood Hz Hpos) zero_complete) Hk)

/-- Rocq: `BachmannAgree.bach_bphi`. -/
theorem bach_bphi (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ T : BOrd.{u}, BGood f T → BFam T → BDirH f T → BRep f T (bphi f T)
  | bnode A g C h, Hgood, Hfam, Hdir => by
    have hfm := hf.monotone
    have Hgood' := Hgood
    obtain ⟨Hg1, Hg2, _, _, Hdec⟩ := Hgood'
    have Hfam' := Hfam
    obtain ⟨Hf1, Hf2, _⟩ := Hfam'
    obtain ⟨Hd1, Hd2, Hd3⟩ := Hdir
    have HIa : ∀ a, BRep f (g a) (bphi f (g a)) := fun a => bach_bphi f hf (g a) (Hg1 a) (Hf1 a) (Hd1 a)
    have HIc : ∀ c ξ, Complete ξ → BRep f (h c ξ) (bphi f (h c ξ)) := fun c ξ hξ =>
      bach_bphi f hf (h c ξ) (Hg2 c ξ hξ) (Hf2 c ξ) (Hd2 c ξ hξ)
    have HT : NormalFunction (bphi f (bnode A g C h)) := bphi_normal hf _ Hgood
    have HF := bphi_fam_normal' hf A g C h Hgood
    have Hmono := bmono_bcomp f hfm _ (bfam_bmono f hfm _ Hfam)
    have Hca : ∀ a x, Complete x → bach f (g a) x ≈ bphi f (g a) x := fun a x hx => (HIa a).2.1 x hx
    have Hcc : ∀ c x, Complete x → bach f (h c x) 0 ≈ bphi f (h c x) 0 := fun c x hx =>
      (HIc c x hx).2.1 0 zero_complete
    have Hclb : ∀ kk y, Complete y →
        bcomp f (bnode A g C h) kk (bphi f (bnode A g C h) y) ≤ bphi f (bnode A g C h) y := by
      intro kk y hy
      have hv := HT.complete y hy
      match kk with
      | .inl a => exact le_trans (Hca a _ hv).le (bphi_fix_small f hf A g C h a y Hgood hy)
      | .inr c => exact le_trans (Hcc c _ hv).le (bphi_fix_big f hf A g C h c y Hgood hy)
    refine ⟨HT, ?_, Hclb⟩
    intro y
    induction y with
    | mk Y k ihy =>
    intro hyc
    have hkc : ∀ j, Complete (k j) := fun j => complete_subord hyc j
    have Hs : lim (fun j : Y => bach f (bnode A g C h) (k j)) ≈ lim (fun j : Y => bphi f (bnode A g C h) (k j)) :=
      lim_eq_mor _ _ _ fun j => ihy j (hkc j)
    have Hsc : Complete (lim fun j : Y => bphi f (bnode A g C h) (k j)) := lim_normal_complete (mk Y k) _ HT hyc
    refine equiv_intro ?_ ?_
    · refine bach_le_comp f _ _ _ (bphi_ge_f f _ _) fun kk => ?_
      exact fixOrd_least (Hmono kk) _ _ (le_trans Hs.le (limit_least fun j => HT.increasing _ _ hyc (index_lt (mk Y k) j)))
        (Hclb kk _ hyc)
    · show cfe f (A ⊕ C) (bphi_fam f g h) (mk Y k) ≤ bach f (bnode A g C h) (mk Y k)
      match Hdec with
      | .inr hn =>
        refine le_trans ?_ (f_le_bach f _ _)
        rw [cfe_unroll]
        exact sup_least fun o => match o with
          | some p => (hn ⟨p.1⟩).elim
          | none => le_refl _
      | .inl ⟨k0⟩ =>
        have Hwc : ∀ kk, Complete (fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j))) :=
          fun kk => normal_fix_complete _ Hsc (normal_inflationary (HF kk)) (HF kk).monotone (HF kk).complete
        have Hwfix : ∀ kk, bphi_fam f g h kk (fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j))) ≤
            fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j)) :=
          fun kk => (normal_fixpoint (HF kk) _ Hsc).ge
        have DN : ∀ kk z, Complete z → bphi_fam f g h kk z ≤ z → f z ≤ z := fun kk z hz hk =>
          bphi_fam_fix_f f hf A g C h kk z Hgood hz hk
        have Hwmono : ∀ k1 k3, BDom f g h k1 k3 →
            fixOrd (bphi_fam f g h k1) (lim fun j : Y => bphi f (bnode A g C h) (k j)) ≤
              fixOrd (bphi_fam f g h k3) (lim fun j : Y => bphi f (bnode A g C h) (k j)) := fun k1 k3 D =>
          fixOrd_least (HF k1).monotone _ _ (fixOrd_above _ _) (D _ (Hwc k3) (Hwfix k3))
        have Hwdir : Directed (A ⊕ C) fun kk => fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j)) :=
          fun k1 k2 => let ⟨k3, D1, D2⟩ := Hd3 k1 k2; ⟨k3, Hwmono _ _ D1, Hwmono _ _ D2⟩
        have HwZ : ∀ kk, fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j)) ≤
            bach f (bnode A g C h) (mk Y k) := fun kk =>
          match kk with
          | .inl a =>
            le_trans (fixOrd_eq_func_complete (bach f (g a)) (bphi f (g a)) _ _ (Hca a) (Hmono (.inl a))
              (HF (.inl a)).monotone (HF (.inl a)).complete Hs Hsc).ge (bach_comp_le f (bnode A g C h) (mk Y k) (.inl a))
          | .inr c =>
            le_trans (fixOrd_eq_func_complete (fun ξ => bach f (h c ξ) 0) (fun ξ => bphi f (h c ξ) 0) _ _ (Hcc c)
              (Hmono (.inr c)) (HF (.inr c)).monotone (HF (.inr c)).complete Hs Hsc).ge
              (bach_comp_le f (bnode A g C h) (mk Y k) (.inr c))
        refine le_trans ?_ (sup_least HwZ)
        refine cfe_least f hf _ _ HF _ _ ?_ ?_ fun kk => ⟨?_, ?_⟩
        · refine le_trans ?_ (sup_le (fun kk => fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j))) k0)
          refine le_trans (hfm _ _ ?_) (DN k0 _ (Hwc k0) (Hwfix k0))
          exact le_trans (lim_le_mor _ _ _ fun j => normal_inflationary HT _ (hkc j)) (fixOrd_above _ _)
        · exact limit_least fun j => lt_of_lt_of_le (limit_lt (fun j : Y => bphi f (bnode A g C h) (k j)) j)
            (le_trans (fixOrd_above _ _) (sup_le (fun kk => fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j))) k0))
        · refine le_trans ((HF kk).continuous _ _ k0 Hwdir Hwc) (sup_least fun o => ?_)
          obtain ⟨o3, D1, D2⟩ := Hd3 o kk
          exact le_trans ((HF kk).monotone _ _ (Hwmono o o3 D1)) (le_trans (D2 _ (Hwc o3) (Hwfix o3)) (sup_le (fun kk => fixOrd (bphi_fam f g h kk) (lim fun j : Y => bphi f (bnode A g C h) (k j))) o3))
        · exact le_trans (hf.continuous _ _ k0 Hwdir Hwc) (sup_monotone fun o => DN o _ (Hwc o) (Hwfix o))

/-! ## Soundness of structural domination for `φ` -/

/-- Rocq: `BachmannAgree.dsem`. -/
def dsem (f : Ordinal.{u} → Ordinal.{u}) : bdesc.{u} → Ordinal.{u} → Ordinal.{u}
  | .DSmall x => bphi f x
  | .DFam h => fun ξ => bphi f (h ξ) 0

/-- Rocq: `BachmannAgree.semdom`. -/
def SemDom (f : Ordinal.{u} → Ordinal.{u}) (d1 d3 : bdesc.{u}) : Prop :=
  ∀ z, Complete z → dsem f d3 z ≤ z → dsem f d1 z ≤ z

section domination0

variable (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)

include hf in
/-- Rocq: `BachmannAgree.dcan_good`. -/
theorem dcan_good (x : BOrd.{u}) (H : BCd x) : BFam x ∧ BGood f x := bcanon_good f hf x H.1 H.2

include hf in
/-- Rocq: `BachmannAgree.D0_sound`. -/
theorem D0_sound (d1 d3 : bdesc.{u}) (_Hc1 : DCan d1) (Hc3 : DCan d3) (H : D0 d1 d3) : SemDom f d1 d3 := by
  have hfm := hf.monotone
  cases H with
  | ss_sub x y H =>
    intro z _ hle
    obtain ⟨Hyf, _⟩ := dcan_good f hf y Hc3
    exact le_trans ((bphi_mono_index f hfm y Hyf).2 _ H z) hle
  | ss_lt x y H =>
    intro z hz hle
    obtain ⟨Hyf, Hyg⟩ := dcan_good f hf y Hc3
    exact bnest f hf x y H Hyg Hyf z hz (bfix_of_fix f hf y z Hyg Hyf hz hle)
  | sf x h n H =>
    intro z hz hle
    obtain ⟨Hyf, Hyg⟩ := dcan_good f hf _ Hc3
    have Hfix : BFix f (h z) z := bfix_member f hf (blimΩ h) ⟨⟩ z Hyg Hyf hz hle
    exact bnest f hf x (h z) (bslt_bsub_r _ _ _ H (bfam_fam _ Hyf ⟨⟩ _ _ (fix_onePlus_finite f hf z hz Hfix.1 n)))
      (bgood_big f (blimΩ h) ⟨⟩ z Hyg hz) (bfam_big _ Hyf ⟨⟩ z) z hz Hfix
  | fs h y e H =>
    intro z hz hle
    obtain ⟨Hyf, Hyg⟩ := dcan_good f hf y Hc3
    have Hfix := bfix_of_fix f hf y z Hyg Hyf hz hle
    exact le_trans ((bphi_mono_index f hfm _ (bfam_big _ Hyf e z)).2 _ (H z) 0) (Hfix.2.2 e)
  | ff_pt h1 h3 H =>
    intro z _ hle
    obtain ⟨Hyf, _⟩ := dcan_good f hf _ Hc3
    exact le_trans ((bphi_mono_index f hfm _ (bfam_big _ Hyf ⟨⟩ z)).2 _ (H z) 0) hle
  | ff_in h1 h3 n e H =>
    intro z hz hle
    obtain ⟨Hyf, Hyg⟩ := dcan_good f hf _ Hc3
    have Hfix : BFix f (h3 z) z := bfix_member f hf (blimΩ h3) ⟨⟩ z Hyg Hyf hz hle
    have Hn : ofNat n ≤ z := fix_onePlus_finite f hf z hz Hfix.1 n
    have Hfix' : BFix f (h3 (ofNat n)) z :=
      bfix_bsub f hf _ _ z (bfam_fam _ Hyf ⟨⟩ _ _ Hn) (bfam_big _ Hyf ⟨⟩ z) Hfix
    exact le_trans ((bphi_mono_index f hfm _ (bfam_big _ (bfam_big _ Hyf ⟨⟩ _) e z)).2 _ (H z) 0) (Hfix'.2.2 e)
  | ffZ h1 h3 H =>
    intro z hz hle
    obtain ⟨Hyf, Hyg⟩ := dcan_good f hf _ Hc3
    have Hfix : BFix f (h3 z) z := bfix_member f hf (blimΩ h3) ⟨⟩ z Hyg Hyf hz hle
    exact bleZ_sound f hf z (h1 z) (h3 z) (H z fun n => fix_onePlus_finite f hf z hz Hfix.1 n) (h3 z) (bsub_refl _)
      (bgood_big f (blimΩ h3) ⟨⟩ z Hyg hz) (bfam_big _ Hyf ⟨⟩ z) hz Hfix

include hf in
/-- Rocq: `BachmannAgree.Dstar_sound`. -/
theorem Dstar_sound (d1 d3 : bdesc.{u}) (Hc1 : DCan d1) (_Hc3 : DCan d3) (H : Dstar d1 d3) : SemDom f d1 d3 := by
  induction H with
  | refl _ => exact fun _ _ hle => hle
  | step d1 d2 _ hc2 h0 _ ih => exact fun z hz hle => D0_sound f hf d1 d2 Hc1 hc2 h0 z hz (ih hc2 _Hc3 z hz hle)

end domination0

/-- Rocq: `BachmannAgree.ndesc`. -/
def ndesc (N : BOrd.{u}) : bsmall N ⊕ bbig N → bdesc.{u}
  | .inl a => .DSmall (bsmallSz N a)
  | .inr c => .DFam (bbigSz N c)

/-- Rocq: `BachmannAgree.sdir`. -/
def SDir (N : BOrd.{u}) : Prop :=
  ∀ k1 k2, ∃ k3, Dstar (ndesc N k1) (ndesc N k3) ∧ Dstar (ndesc N k2) (ndesc N k3)

/-- Rocq: `BachmannAgree.bsdirH`. -/
def BSdirH : BOrd.{u} → Prop
  | bnode A g C h => (∀ a, BSdirH (g a)) ∧ (∀ c ξ, Complete ξ → BSdirH (h c ξ)) ∧ SDir (bnode A g C h)

/-- Rocq: `BachmannAgree.dcan_ndesc`. -/
theorem dcan_ndesc (N : BOrd.{u}) (k : bsmall N ⊕ bbig N) (HN : BCd N) : DCan (ndesc N k) := by
  cases N with
  | bnode A g C h =>
  match k with
  | .inl a => exact bcd_small (bnode A g C h) a HN
  | .inr c =>
    obtain ⟨⟨_, H2, H3, H4, H5⟩, ⟨_, _, Hd⟩⟩ := HN
    exact ⟨⟨fun e => (nomatch e), fun _ => H2 c, fun _ => H3 c, fun _ => H4 c, fun _ => H5 c⟩,
      bdec_blimΩ _ fun ξ hξ => Hd c ξ hξ⟩

/-! ## Structural directedness gives semantic directedness for `φ` -/

/-- Rocq: `BachmannAgree.bsdirH_bdirH`. -/
theorem bsdirH_bdirH (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ T : BOrd.{u}, BCd T → BSdirH T → BDirH f T
  | bnode A g C h, HT, ⟨Hs1, Hs2, Hs3⟩ =>
    ⟨fun a => bsdirH_bdirH f hf (g a) (bcd_small (bnode A g C h) a HT) (Hs1 a),
     fun c ξ hξ => bsdirH_bdirH f hf (h c ξ) (bcd_big (bnode A g C h) c ξ HT hξ) (Hs2 c ξ hξ),
     fun k1 k2 => by
      obtain ⟨k3, D1, D2⟩ := Hs3 k1 k2
      have S1 := Dstar_sound f hf _ _ (dcan_ndesc (bnode A g C h) k1 HT) (dcan_ndesc (bnode A g C h) k3 HT) D1
      have S2 := Dstar_sound f hf _ _ (dcan_ndesc (bnode A g C h) k2 HT) (dcan_ndesc (bnode A g C h) k3 HT) D2
      refine ⟨k3, fun z hz hle => ?_, fun z hz hle => ?_⟩
      · cases k1 <;> cases k3 <;> exact S1 z hz hle
      · cases k2 <;> cases k3 <;> exact S2 z hz hle⟩

/-- On canonical, decided, structurally directed trees, Bachmann's `φ` (one
component at a time) represents `bphi`. Rocq: `BachmannAgree.bach_bphi_canon`. -/
theorem bach_bphi_canon (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (T : BOrd.{u}) (HT : BCd T)
    (Hd : BSdirH T) : BRep f T (bphi f T) :=
  have ⟨Hfam, Hgood⟩ := dcan_good f hf T HT
  bach_bphi f hf T Hgood Hfam (bsdirH_bdirH f hf T HT Hd)

/-! ### First instances -/

/-- Rocq: `BachmannAgree.bsdirH_embed`. -/
theorem bsdirH_embed : ∀ ξ : Ordinal.{u}, Complete ξ → BSdirH (embed ξ)
  | mk _ k, ⟨Hdir, _, Hkc⟩ =>
    ⟨fun a => bsdirH_embed (k a) (Hkc a), fun e => (nomatch e), fun k1 k2 =>
      match k1, k2 with
      | .inl a1, .inl a2 =>
        let ⟨a3, h1, h2⟩ := Hdir a1 a2
        ⟨.inl a3, D0_star _ _ (bcd_embed _ (Hkc a3)) (.ss_sub _ _ (bsub_embed _ _ h1)),
          D0_star _ _ (bcd_embed _ (Hkc a3)) (.ss_sub _ _ (bsub_embed _ _ h2))⟩
      | .inl _, .inr e => nomatch e
      | .inr e, _ => nomatch e⟩

/-- Rocq: `BachmannAgree.bsdirH_Ω`. -/
theorem bsdirH_Ω : BSdirH bOmega.{u} :=
  ⟨fun e => (nomatch e), fun _ ξ hξ => bsdirH_embed ξ hξ, fun k1 k2 =>
    match k1, k2 with
    | .inl e, _ => nomatch e
    | .inr _, .inl e => nomatch e
    | .inr _, .inr _ => ⟨.inr ⟨⟩, .refl _, .refl _⟩⟩

/-! ### Addition -/

/-- Rocq: `BachmannAgree.dshift`. -/
def dshift (x : BOrd.{u}) : bdesc.{u} → bdesc.{u}
  | .DSmall t => .DSmall (badd x t)
  | .DFam h => .DFam fun ξ => badd x (h ξ)

/-- Rocq: `BachmannAgree.D0_shift`. -/
theorem D0_shift (x : BOrd.{u}) (d1 d2 : bdesc.{u}) (H : D0 d1 d2) : D0 (dshift x d1) (dshift x d2) := by
  cases H with
  | ss_sub t y H => exact .ss_sub _ _ (bsub_badd_r _ _ _ H)
  | ss_lt t y H => exact .ss_lt _ _ (bslt_badd_r _ _ _ H)
  | sf t h n H => exact .sf _ _ n (bslt_badd_r _ _ _ H)
  | fs h y e H =>
    obtain ⟨e', He'⟩ := badd_big_r x y e
    exact .fs _ _ e' fun ξ => by rw [He']; exact bsub_badd_r _ _ _ (H ξ)
  | ff_pt h1 h3 H => exact .ff_pt _ _ fun ξ => bsub_badd_r _ _ _ (H ξ)
  | ff_in h1 h3 n e H =>
    obtain ⟨e', He'⟩ := badd_big_r x (h3 (ofNat n)) e
    exact .ff_in _ _ n e' fun ξ => by
      show bsub (badd x (h1 ξ)) (bbigSz (badd x (h3 (ofNat n))) e' ξ)
      rw [He']
      exact bsub_badd_r _ _ _ (H ξ)
  | ffZ h1 h3 H => exact .ffZ _ _ fun z hz => bleZ_shift x z _ _ (H z hz)

/-- Rocq: `BachmannAgree.dcan_shift`. -/
theorem dcan_shift (x : BOrd.{u}) (d : bdesc.{u}) (Hx : BCd x) : DCan d → DCan (dshift x d) := by
  cases d with
  | DSmall t => exact fun Ht => bcd_badd x t Hx Ht
  | DFam h =>
    intro H
    obtain ⟨⟨_, H2, H3, H4, H5⟩, Hd⟩ := H
    exact ⟨⟨fun e => (nomatch e), fun _ ξ => bcanon_badd x _ Hx.1 (H2 ⟨⟩ ξ),
      fun _ ξ ξ' hle => bsub_badd_r _ _ _ (H3 ⟨⟩ ξ ξ' hle), fun _ ξ ξ' hc hlt => bslt_badd_r _ _ _ (H4 ⟨⟩ ξ ξ' hc hlt),
      fun _ B k b0 hdir hk => bsub_trans (bsub_badd_r _ _ _ (H5 ⟨⟩ B k b0 hdir hk)) (bsub_badd_bsup x _ b0)⟩,
      bdec_blimΩ _ fun ξ hξ => bdec_badd _ _ Hx.2 (bdec_blimΩ_inv h Hd ξ hξ)⟩

/-- Rocq: `BachmannAgree.Dstar_shift`. -/
theorem Dstar_shift (x : BOrd.{u}) (d1 d2 : bdesc.{u}) (Hx : BCd x) (H : Dstar d1 d2) :
    Dstar (dshift x d1) (dshift x d2) := by
  induction H with
  | refl _ => exact .refl _
  | step _ d2 _ hc h0 _ ih => exact .step _ _ _ (dcan_shift x d2 Hx hc) (D0_shift x _ _ h0) ih

/-- Rocq: `BachmannAgree.blub_desc_cases`. -/
theorem blub_desc_cases (x z : BOrd.{u}) (k : bsmall (blub x z) ⊕ bbig (blub x z)) :
    (∃ kx, ndesc (blub x z) k = ndesc x kx) ∨ (∃ kz, ndesc (blub x z) k = ndesc z kz) := by
  cases x with
  | bnode A g C h =>
  cases z with
  | bnode B g' D h' =>
  match k with
  | .inl (.inl a) => exact .inl ⟨.inl a, rfl⟩
  | .inl (.inr b) => exact .inr ⟨.inl b, rfl⟩
  | .inr (.inl c) => exact .inl ⟨.inr c, rfl⟩
  | .inr (.inr d) => exact .inr ⟨.inr d, rfl⟩

/-- Rocq: `BachmannAgree.blub_desc_l`. -/
theorem blub_desc_l (x z : BOrd.{u}) (kx : bsmall x ⊕ bbig x) : ∃ k, ndesc (blub x z) k = ndesc x kx := by
  cases x with
  | bnode A g C h =>
  cases z with
  | bnode B g' D h' =>
  match kx with
  | .inl a => exact ⟨.inl (.inl a), rfl⟩
  | .inr c => exact ⟨.inr (.inl c), rfl⟩

/-- Rocq: `BachmannAgree.blub_desc_r`. -/
theorem blub_desc_r (x z : BOrd.{u}) (kz : bsmall z ⊕ bbig z) : ∃ k, ndesc (blub x z) k = ndesc z kz := by
  cases x with
  | bnode A g C h =>
  cases z with
  | bnode B g' D h' =>
  match kz with
  | .inl b => exact ⟨.inl (.inr b), rfl⟩
  | .inr d => exact ⟨.inr (.inr d), rfl⟩

/-- A merge is directed if both parts are, and every component of the left
part is dominated by every component of the right part. Rocq: `BachmannAgree.sdir_blub`. -/
theorem sdir_blub (x z : BOrd.{u}) (Hx : SDir x) (Hz : SDir z) (Hcross : ∀ kx kz, Dstar (ndesc x kx) (ndesc z kz)) :
    SDir (blub x z) := by
  intro k1 k2
  match blub_desc_cases x z k1, blub_desc_cases x z k2 with
  | .inl ⟨x1, E1⟩, .inl ⟨x2, E2⟩ =>
    obtain ⟨x3, H1, H2⟩ := Hx x1 x2
    obtain ⟨k3, E3⟩ := blub_desc_l x z x3
    exact ⟨k3, by rw [E1, E3]; exact H1, by rw [E2, E3]; exact H2⟩
  | .inl ⟨x1, E1⟩, .inr ⟨z2, E2⟩ =>
    obtain ⟨k3, E3⟩ := blub_desc_r x z z2
    exact ⟨k3, by rw [E1, E3]; exact Hcross x1 z2, by rw [E2, E3]; exact .refl _⟩
  | .inr ⟨z1, E1⟩, .inl ⟨x2, E2⟩ =>
    obtain ⟨k3, E3⟩ := blub_desc_r x z z1
    exact ⟨k3, by rw [E1, E3]; exact .refl _, by rw [E2, E3]; exact Hcross x2 z1⟩
  | .inr ⟨z1, E1⟩, .inr ⟨z2, E2⟩ =>
    obtain ⟨z3, H1, H2⟩ := Hz z1 z2
    obtain ⟨k3, E3⟩ := blub_desc_r x z z3
    exact ⟨k3, by rw [E1, E3]; exact H1, by rw [E2, E3]; exact H2⟩

/-- Rocq: `BachmannAgree.bsdirH_blub`. -/
theorem bsdirH_blub (x z : BOrd.{u}) (Hx : BSdirH x) (Hz : BSdirH z) (Hs : SDir (blub x z)) : BSdirH (blub x z) := by
  cases x with
  | bnode A g C h =>
  cases z with
  | bnode B g' D h' =>
  refine ⟨fun ab => ?_, fun cd ξ hξ => ?_, Hs⟩
  · match ab with
    | .inl a => exact Hx.1 a
    | .inr b => exact Hz.1 b
  · match cd with
    | .inl c => exact Hx.2.1 c ξ hξ
    | .inr d => exact Hz.2.1 d ξ hξ

/-- Rocq: `BachmannAgree.sdir_baddR`. -/
theorem sdir_baddR (x y : BOrd.{u}) (Hx : BCd x) (Hy : SDir y) : SDir (baddR x y) := by
  intro k1 k2
  obtain ⟨k3, H1, H2⟩ := Hy k1 k2
  refine ⟨k3, ?_, ?_⟩
  · cases k1 <;> cases k3 <;> exact Dstar_shift x _ _ Hx H1
  · cases k2 <;> cases k3 <;> exact Dstar_shift x _ _ Hx H2

/-- Rocq: `BachmannAgree.badd_cross`. -/
theorem badd_cross (x y : BOrd.{u}) (kx : bsmall x ⊕ bbig x) (kz : bsmall (baddR x y) ⊕ bbig (baddR x y))
    (Hx : BCd x) (Hy : BCd y) : Dstar (ndesc x kx) (ndesc (baddR x y) kz) := by
  refine D0_star _ _ ?_ ?_
  · match kz with
    | .inl b => exact dcan_shift x (ndesc y (.inl b)) Hx (dcan_ndesc y (.inl b) Hy)
    | .inr d => exact dcan_shift x (ndesc y (.inr d)) Hx (dcan_ndesc y (.inr d) Hy)
  · cases x with
    | bnode A g C h =>
    cases y with
    | bnode B g' D h' =>
    match kx, kz with
    | .inl a, .inl b =>
      exact .ss_lt _ _ (bslt_bsub_r _ _ _ (.small (bnode A g C h) a (bsub_refl _)) (bsub_le_badd _ _))
    | .inl a, .inr d =>
      exact .sf _ _ 0 (bslt_bsub_r _ _ _ (.small (bnode A g C h) a (bsub_refl _)) (bsub_le_badd _ _))
    | .inr c, .inl b =>
      obtain ⟨e, He⟩ := badd_big_l (bnode A g C h) (g' b) c
      exact .fs _ _ e fun ξ => by
        show bsub (h c ξ) (bbigSz (badd (bnode A g C h) (g' b)) e ξ)
        rw [He]
        exact bsub_refl _
    | .inr c, .inr d =>
      obtain ⟨e, He⟩ := badd_big_l (bnode A g C h) (h' d (ofNat 0)) c
      exact .ff_in _ _ 0 e fun ξ => by
        show bsub (h c ξ) (bbigSz (badd (bnode A g C h) (h' d (ofNat 0))) e ξ)
        rw [He]
        exact bsub_refl _

/-- Rocq: `BachmannAgree.bsdirH_badd`. -/
theorem bsdirH_badd (x y : BOrd.{u}) (Hxc : BCd x) (Hxd : BSdirH x) : BCd y → BSdirH y → BSdirH (badd x y) := by
  induction y with
  | bnode B g' D h' ihg ihh =>
  intro Hyc Hyd
  obtain ⟨Hy1, Hy2, Hy3⟩ := Hyd
  rw [badd_eq x (bnode B g' D h')]
  have HR : BSdirH (baddR x (bnode B g' D h')) :=
    ⟨fun b => ihg b (bcd_small _ b Hyc) (Hy1 b), fun d ξ hξ => ihh d ξ (bcd_big _ d ξ Hyc hξ) (Hy2 d ξ hξ),
      sdir_baddR x _ Hxc Hy3⟩
  refine bsdirH_blub _ _ Hxd HR (sdir_blub _ _ ?_ (sdir_baddR x _ Hxc Hy3) fun kx kz => badd_cross x _ kx kz Hxc Hyc)
  cases x; exact Hxd.2.2

/-! ### Covering -/

/-- Every component of `T` is dominated by some component of `U`.
Rocq: `BachmannAgree.Cov`. -/
def Cov (T U : BOrd.{u}) : Prop := ∀ k, ∃ k', Dstar (ndesc T k) (ndesc U k')

/-- Rocq: `BachmannAgree.cov_trans`. -/
theorem cov_trans (T U V : BOrd.{u}) (H1 : Cov T U) (H2 : Cov U V) : Cov T V := fun k =>
  let ⟨k', h'⟩ := H1 k
  let ⟨k'', h''⟩ := H2 k'
  ⟨k'', Dstar_trans _ _ _ h' h''⟩

/-- Rocq: `BachmannAgree.cov_bsub`. -/
theorem cov_bsub (T U : BOrd.{u}) (H : bsub T U) (HU : BCd U) : Cov T U := fun k =>
  match k with
  | .inl a => let ⟨a', ha'⟩ := bsub_small _ _ H a
    ⟨.inl a', D0_star _ _ (dcan_ndesc U (.inl a') HU) (.ss_sub _ _ ha')⟩
  | .inr c => let ⟨c', hc'⟩ := bsub_big _ _ H c
    ⟨.inr c', D0_star _ _ (dcan_ndesc U (.inr c') HU) (.ff_pt _ _ hc')⟩

/-- The components of a small child are dominated by the child itself.
Rocq: `BachmannAgree.cov_small_child`. -/
theorem cov_small_child (U : BOrd.{u}) (j : bsmall U) (HU : BCd U) :
    ∀ k, Dstar (ndesc (bsmallSz U j) k) (ndesc U (.inl j))
  | .inl a => D0_star _ _ (dcan_ndesc U (.inl j) HU) (.ss_lt _ _ (.small _ a (bsub_refl _)))
  | .inr c => D0_star _ _ (dcan_ndesc U (.inl j) HU) (.fs _ _ c fun _ => bsub_refl _)

/-- The components of a family member are dominated by the family.
Rocq: `BachmannAgree.cov_member`. -/
theorem cov_member (F : Ordinal.{u} → BOrd.{u}) (n : Nat) (HF : DCan (.DFam F)) :
    ∀ k, Dstar (ndesc (F (ofNat n)) k) (.DFam F)
  | .inl a => D0_star _ _ HF (.sf _ _ n (.small _ a (bsub_refl _)))
  | .inr c => D0_star _ _ HF (.ff_in _ _ n c fun _ => bsub_refl _)

/-- Rocq: `BachmannAgree.cov_member_eq`. -/
theorem cov_member_eq (U : BOrd.{u}) (t : bbig U) (n : Nat) (V : BOrd.{u}) (HU : BCd U)
    (E : bbigSz U t (ofNat n) = V) : Cov V U := by
  subst E
  exact fun k => ⟨.inr t, cov_member (bbigSz U t) n (dcan_ndesc U (.inr t) HU) k⟩

/-- Rocq: `BachmannAgree.cov_bmul_step`. -/
theorem cov_bmul_step (x t u : BOrd.{u}) (Hx : BCd x) (Hpos : bpos x) (Hu : BCd u) (H : bslt t u) :
    Cov (badd (bmul x t) x) (bmul x u) := by
  induction H with
  | small u j hj =>
    exact cov_bsub _ _ (bsub_trans (bsub_badd_l _ _ (bsub_bmul_r _ _ _ hj) x) (bsub_bmul_step x u j))
      (bcd_bmul _ _ Hx Hpos Hu)
  | big u d n _ ih =>
    obtain ⟨t', ht'⟩ := bmul_big_fam x u d
    exact cov_trans _ _ _ (ih (bcd_big u d _ Hu (ofNat_complete n)))
      (cov_member_eq (bmul x u) t' n _ (bcd_bmul _ _ Hx Hpos Hu) (ht' (ofNat n)))
  | desc u j _ ih =>
    exact cov_trans _ _ _ (ih (bcd_small u j Hu))
      (cov_bsub _ _ (bsub_trans (bsub_le_badd _ _) (bsub_bmul_step x u j)) (bcd_bmul _ _ Hx Hpos Hu))

/-! ### Multiplication -/

/-- Rocq: `BachmannAgree.bsdirH_sdir`. -/
theorem bsdirH_sdir (T : BOrd.{u}) (H : BSdirH T) : SDir T := by
  cases T; exact H.2.2

/-- Rocq: `BachmannAgree.bsdirH_small`. -/
theorem bsdirH_small (T : BOrd.{u}) (a : bsmall T) (H : BSdirH T) : BSdirH (bsmallSz T a) := by
  cases T; exact H.1 a

/-- Rocq: `BachmannAgree.bsdirH_big`. -/
theorem bsdirH_big (T : BOrd.{u}) (c : bbig T) (ξ : Ordinal.{u}) (H : BSdirH T) (hξ : Complete ξ) :
    BSdirH (bbigSz T c ξ) := by
  cases T; exact H.2.1 c ξ hξ

/-- Rocq: `BachmannAgree.dcan_mul`. -/
theorem dcan_mul (x : BOrd.{u}) (h : Ordinal.{u} → BOrd.{u}) (Hx : BCd x) (Hp : bpos x) (H : DCan (.DFam h)) :
    DCan (.DFam fun ξ => bmul x (h ξ)) := by
  obtain ⟨⟨_, H2, H3, H4, H5⟩, Hd⟩ := H
  exact ⟨⟨fun e => (nomatch e), fun _ ξ => bcanon_bmul x _ Hx.1 Hp (H2 ⟨⟩ ξ),
    fun _ ξ ξ' hle => bsub_bmul_r _ _ _ (H3 ⟨⟩ ξ ξ' hle), fun _ ξ ξ' hc hlt => bslt_bmul_r _ Hp _ _ (H4 ⟨⟩ ξ ξ' hc hlt),
    fun _ B k b0 hdir hk => bsub_trans (bsub_bmul_r _ _ _ (H5 ⟨⟩ B k b0 hdir hk)) (bsub_bmul_bsup x _)⟩,
    bdec_blimΩ _ fun ξ hξ => bdec_bmul _ _ (bslt_inh _ _ Hp) Hx.2 (bdec_blimΩ_inv h Hd ξ hξ)⟩

/-- The components of `x·y` contributed by a component of `y`: all the
components of `x·t + x` for a small child `t`, or the single family
`ξ ↦ x·h ξ` for a family `h`. Rocq: `BachmannAgree.mimg`. -/
def MImg (x : BOrd.{u}) : bdesc.{u} → bdesc.{u} → Prop
  | .DSmall t, c => ∃ k, c = ndesc (badd (bmul x t) x) k
  | .DFam h, c => c = .DFam fun ξ => bmul x (h ξ)

/-- Rocq: `BachmannAgree.mimg_D0`. -/
theorem mimg_D0 (x : BOrd.{u}) (d1 d3 : bdesc.{u}) (Hx : BCd x) (Hp : bpos x) (_Hc1 : DCan d1) (Hc3 : DCan d3)
    (H : D0 d1 d3) : ∀ c, MImg x d1 c → ∃ c', MImg x d3 c' ∧ Dstar c c' := by
  cases H with
  | ss_sub t u H =>
    intro c hc
    obtain ⟨k, rfl⟩ := hc
    obtain ⟨k', hk'⟩ := cov_bsub (badd (bmul x t) x) (badd (bmul x u) x) (bsub_badd_l _ _ (bsub_bmul_r x t u H) x)
      (bcd_badd _ _ (bcd_bmul x u Hx Hp Hc3) Hx) k
    exact ⟨ndesc (badd (bmul x u) x) k', ⟨k', rfl⟩, hk'⟩
  | ss_lt t u H =>
    intro c hc
    obtain ⟨k, rfl⟩ := hc
    have Hcov : Cov (badd (bmul x t) x) (badd (bmul x u) x) :=
      cov_trans _ _ _ (cov_bmul_step x t u Hx Hp Hc3 H)
        (cov_bsub _ _ (bsub_le_badd _ _) (bcd_badd _ _ (bcd_bmul _ _ Hx Hp Hc3) Hx))
    obtain ⟨k', hk'⟩ := Hcov k
    exact ⟨ndesc (badd (bmul x u) x) k', ⟨k', rfl⟩, hk'⟩
  | sf t h n H =>
    intro c hc
    obtain ⟨k, rfl⟩ := hc
    have Hhn : BCd (h (ofNat n)) := bcd_big (blimΩ h) ⟨⟩ (ofNat n) Hc3 (ofNat_complete n)
    obtain ⟨k'', hk''⟩ := cov_bmul_step x t (h (ofNat n)) Hx Hp Hhn H k
    exact ⟨.DFam fun ξ => bmul x (h ξ), rfl,
      Dstar_trans _ _ _ hk'' (cov_member (fun ξ => bmul x (h ξ)) n (dcan_mul x h Hx Hp Hc3) k'')⟩
  | fs h u e H =>
    intro c hc
    subst hc
    obtain ⟨t', ht'⟩ := bmul_big_fam x u e
    obtain ⟨e'', he''⟩ := badd_big_l (bmul x u) x t'
    refine ⟨ndesc (badd (bmul x u) x) (.inr e''), ⟨.inr e'', rfl⟩, D0_star _ _
      (dcan_ndesc _ _ (bcd_badd _ _ (bcd_bmul _ _ Hx Hp Hc3) Hx)) (.ff_pt _ _ fun ξ => ?_)⟩
    show bsub (bmul x (h ξ)) (bbigSz (badd (bmul x u) x) e'' ξ)
    rw [he'', ht']
    exact bsub_bmul_r _ _ _ (H ξ)
  | ff_pt h1 h3 H =>
    intro c hc
    subst hc
    exact ⟨.DFam fun ξ => bmul x (h3 ξ), rfl,
      D0_star _ _ (dcan_mul x h3 Hx Hp Hc3) (.ff_pt _ _ fun ξ => bsub_bmul_r _ _ _ (H ξ))⟩
  | ff_in h1 h3 n e H =>
    intro c hc
    subst hc
    obtain ⟨e', he'⟩ := bmul_big_fam x (h3 (ofNat n)) e
    refine ⟨.DFam fun ξ => bmul x (h3 ξ), rfl, D0_star _ _ (dcan_mul x h3 Hx Hp Hc3) (.ff_in _ _ n e' fun ξ => ?_)⟩
    show bsub (bmul x (h1 ξ)) (bbigSz (bmul x (h3 (ofNat n))) e' ξ)
    rw [he']
    exact bsub_bmul_r _ _ _ (H ξ)
  | ffZ h1 h3 H =>
    intro c hc
    subst hc
    exact ⟨.DFam fun ξ => bmul x (h3 ξ), rfl,
      D0_star _ _ (dcan_mul x h3 Hx Hp Hc3) (.ffZ _ _ fun z hz => bleZ_mul x z _ _ (H z hz))⟩

/-- Rocq: `BachmannAgree.mimg_Dstar`. -/
theorem mimg_Dstar (x : BOrd.{u}) (d1 d3 : bdesc.{u}) (Hx : BCd x) (Hp : bpos x) (Hc1 : DCan d1) (Hc3 : DCan d3)
    (H : Dstar d1 d3) : ∀ c, MImg x d1 c → ∃ c', MImg x d3 c' ∧ Dstar c c' := by
  induction H with
  | refl _ => exact fun c hc => ⟨c, hc, .refl _⟩
  | step d1 d2 _ hc2 h0 _ ih =>
    intro c hc
    obtain ⟨c', hc', e'⟩ := mimg_D0 x d1 d2 Hx Hp Hc1 hc2 h0 c hc
    obtain ⟨c'', hc'', e''⟩ := ih hc2 Hc3 c' hc'
    exact ⟨c'', hc'', Dstar_trans _ _ _ e' e''⟩

/-- Rocq: `BachmannAgree.bmul_desc_cases`. -/
theorem bmul_desc_cases (x y : BOrd.{u}) (k : bsmall (bmul x y) ⊕ bbig (bmul x y)) :
    ∃ yk, MImg x (ndesc y yk) (ndesc (bmul x y) k) := by
  cases y with
  | bnode B g' D h' =>
  match k with
  | .inl (.inl ⟨b, s⟩) => exact ⟨.inl b, .inl s, rfl⟩
  | .inl (.inr e) => exact nomatch e
  | .inr (.inl ⟨b, c⟩) => exact ⟨.inl b, .inr c, rfl⟩
  | .inr (.inr d) => exact ⟨.inr d, rfl⟩

/-- Rocq: `BachmannAgree.bmul_desc_back`. -/
theorem bmul_desc_back (x y : BOrd.{u}) (yk : bsmall y ⊕ bbig y) (c : bdesc.{u}) (Hc : MImg x (ndesc y yk) c) :
    ∃ k, ndesc (bmul x y) k = c := by
  cases y with
  | bnode B g' D h' =>
  match yk, Hc with
  | .inl b, ⟨.inl s, hc⟩ => exact ⟨.inl (.inl ⟨b, s⟩), hc.symm⟩
  | .inl b, ⟨.inr c', hc⟩ => exact ⟨.inr (.inl ⟨b, c'⟩), hc.symm⟩
  | .inr d, hc => exact ⟨.inr (.inr d), hc.symm⟩

/-- Rocq: `BachmannAgree.sdir_bmul`. -/
theorem sdir_bmul (x y : BOrd.{u}) (Hx : BCd x) (Hp : bpos x) (Hyc : BCd y) (Hy : SDir y)
    (Hpieces : ∀ b, SDir (badd (bmul x (bsmallSz y b)) x)) : SDir (bmul x y) := by
  intro k1 k2
  obtain ⟨y1, M1⟩ := bmul_desc_cases x y k1
  obtain ⟨y2, M2⟩ := bmul_desc_cases x y k2
  obtain ⟨y3, D1, D2⟩ := Hy y1 y2
  obtain ⟨c1, M1', E1⟩ := mimg_Dstar x _ _ Hx Hp (dcan_ndesc y y1 Hyc) (dcan_ndesc y y3 Hyc) D1 _ M1
  obtain ⟨c2, M2', E2⟩ := mimg_Dstar x _ _ Hx Hp (dcan_ndesc y y2 Hyc) (dcan_ndesc y y3 Hyc) D2 _ M2
  have Hc3 : ∃ c3, MImg x (ndesc y y3) c3 ∧ Dstar c1 c3 ∧ Dstar c2 c3 := by
    match y3, M1', M2' with
    | .inl b3, ⟨s1, h1⟩, ⟨s2, h2⟩ =>
      obtain ⟨s3, F1, F2⟩ := Hpieces b3 s1 s2
      subst h1 h2
      exact ⟨ndesc (badd (bmul x (bsmallSz y b3)) x) s3, ⟨s3, rfl⟩, F1, F2⟩
    | .inr d3, h1, h2 =>
      have h1 : c1 = .DFam fun ξ => bmul x (bbigSz y d3 ξ) := h1
      have h2 : c2 = .DFam fun ξ => bmul x (bbigSz y d3 ξ) := h2
      subst h1 h2
      exact ⟨.DFam fun ξ => bmul x (bbigSz y d3 ξ), rfl, .refl _, .refl _⟩
  obtain ⟨c3, M3, F1, F2⟩ := Hc3
  obtain ⟨k3, E3⟩ := bmul_desc_back x y _ c3 M3
  exact ⟨k3, by rw [E3]; exact Dstar_trans _ _ _ E1 F1, by rw [E3]; exact Dstar_trans _ _ _ E2 F2⟩

/-- Rocq: `BachmannAgree.bsdirH_bmul`. -/
theorem bsdirH_bmul (x y : BOrd.{u}) (Hx : BCd x) (Hp : bpos x) (Hxd : BSdirH x) :
    BCd y → BSdirH y → BSdirH (bmul x y) := by
  induction y with
  | bnode B g' D h' ihg ihh =>
  intro Hyc Hyd
  have Hyc1 : ∀ b, BCd (g' b) := fun b => bcd_small (bnode B g' D h') b Hyc
  have Hyc2 : ∀ d ξ, Complete ξ → BCd (h' d ξ) := fun d ξ hξ => bcd_big (bnode B g' D h') d ξ Hyc hξ
  obtain ⟨Hy1, Hy2, Hy3⟩ := Hyd
  have Hpieces : ∀ b, BSdirH (badd (bmul x (g' b)) x) := fun b =>
    bsdirH_badd _ _ (bcd_bmul _ _ Hx Hp (Hyc1 b)) (ihg b (Hyc1 b) (Hy1 b)) Hx Hxd
  have Hsd : SDir (bmul x (bnode B g' D h')) := sdir_bmul x _ Hx Hp Hyc Hy3 fun b => bsdirH_sdir _ (Hpieces b)
  refine ⟨fun s => ?_, fun c ξ hξ => ?_, Hsd⟩
  · match s with
    | .inl ⟨b, s⟩ => exact bsdirH_small _ s (Hpieces b)
    | .inr e => exact nomatch e
  · match c with
    | .inl ⟨b, c⟩ => exact bsdirH_big _ c ξ (Hpieces b) hξ
    | .inr d => exact ihh d ξ (Hyc2 d ξ hξ) (Hy2 d ξ hξ)

/-! ### Exponentiation -/

/-- Rocq: `BachmannAgree.bsub_absorb`. -/
theorem bsub_absorb (c : BOrd.{u}) : ∀ w : BOrd.{u}, bsub w (badd c w) := by
  cases c with
  | bnode A g0 C h0 =>
  intro w
  induction w with
  | bnode B g D h ihg ihh => exact ⟨fun b => ⟨.inr b, ihg b⟩, fun d => ⟨.inr d, fun ξ => ihh d ξ⟩⟩

/-- Rocq: `BachmannAgree.inf_pos`. -/
theorem inf_pos (z : Ordinal.{u}) (H : ∀ n : Nat, ofNat n ≤ z) : 0 < z := lt_of_lt_of_le (succ_lt 0) (H 1)

/-- `P ⊑ P·z` for every positive `z`. Rocq: `BachmannAgree.bsub_P_Pz`. -/
theorem bsub_P_Pz (P : BOrd.{u}) (z : Ordinal.{u}) (Hz : 0 < z) : bsub P (bmul P (embed z)) := by
  cases z with
  | mk Z k =>
  obtain ⟨c, _⟩ := lt_elim Hz
  exact bsub_trans (bsub_absorb (bmul P (embed (k c))) P) (bsub_bmul_step P (embed (mk Z k)) c)

/-- Rocq: `BachmannAgree.PF`. -/
def PF (P : BOrd.{u}) : Ordinal.{u} → BOrd.{u} := fun ξ => bmul P (embed ξ)

/-- Rocq: `BachmannAgree.bexpΩ_fam_s`. -/
theorem bexpΩ_fam_s (y : BOrd.{u}) (j : bsmall y) :
    ∃ t, ∀ ξ, bbigSz (bexpΩ y) t ξ = bmul (bexpΩ (bsmallSz y j)) (embed ξ) :=
  bexpΩ_big_s y j (.inr ⟨⟩)

/-- If `a ⊏ b` then, at every infinite `z`, `Ω^a·z` lies below a descendant of
`Ω^b` reached through arguments at most `z`. Rocq: `BachmannAgree.bleZ_exp_lt`. -/
theorem bleZ_exp_lt (a b : BOrd.{u}) (H : bslt a b) :
    ∀ z, (∀ n : Nat, ofNat n ≤ z) → bleZ z (bmul (bexpΩ a) (embed z)) (bexpΩ b) := by
  induction H with
  | small b j hj =>
    intro z _
    obtain ⟨t, ht⟩ := bexpΩ_fam_s b j
    exact .big _ t z (le_refl z) (by rw [ht]; exact .sub _ (bsub_bmul_l _ _ (bsub_bexpΩ _ _ hj) _))
  | big b d n _ ih =>
    intro z hz
    obtain ⟨t, ht⟩ := bexpΩ_big_b b d
    exact .big _ t (ofNat n) (hz n) (by rw [ht]; exact ih z hz)
  | desc b j _ ih =>
    intro z hz
    obtain ⟨t, ht⟩ := bexpΩ_fam_s b j
    exact .big _ t 1 (hz 1) (by rw [ht]; exact bleZ_mono_r _ _ _ _ (ih z hz) (bsub_bmul_one _).2)

/-- Rocq: `BachmannAgree.bleZ_exp`. -/
theorem bleZ_exp (z : Ordinal.{u}) (a b : BOrd.{u}) (Hz : ∀ n : Nat, ofNat n ≤ z) (H : bleZ z a b) :
    bleZ z (bexpΩ a) (bexpΩ b) := by
  induction H with
  | sub b H => exact .sub _ (bsub_bexpΩ _ _ H)
  | small b j _ ih =>
    obtain ⟨t, ht⟩ := bexpΩ_fam_s b j
    exact .big _ t 1 (Hz 1) (by rw [ht]; exact bleZ_mono_r _ _ _ _ ih (bsub_bmul_one _).2)
  | big b d ζ hζ _ ih =>
    obtain ⟨t, ht⟩ := bexpΩ_big_b b d
    exact .big _ t ζ hζ (by rw [ht]; exact ih)

/-- Rocq: `BachmannAgree.emap`. -/
def emap : bdesc.{u} → bdesc.{u}
  | .DSmall t => .DFam (PF (bexpΩ t))
  | .DFam h => .DFam fun ξ => bexpΩ (h ξ)

/-- Rocq: `BachmannAgree.dcan_emap`. -/
theorem dcan_emap (d : bdesc.{u}) (Hd : DCan d) : DCan (emap d) := by
  cases d with
  | DSmall t =>
    have HM : BCd (bmul (bexpΩ t) bOmega) := bcd_bmul _ _ (bcd_bexpΩ _ Hd) (bpos_bexpΩ _) bcd_Ω
    exact dcan_ndesc (bmul (bexpΩ t) bOmega) (.inr (.inr ⟨⟩)) HM
  | DFam h =>
    have HE : BCd (bexpΩ (blimΩ h)) := bcd_bexpΩ _ Hd
    exact dcan_ndesc (bexpΩ (blimΩ h)) (.inr (.inr (.inr ⟨⟩))) HE

/-- Rocq: `BachmannAgree.dcan_fam_mono`. -/
theorem dcan_fam_mono (h : Ordinal.{u} → BOrd.{u}) (Hd : DCan (.DFam h)) :
    ∀ ξ ξ', ξ ≤ ξ' → bsub (h ξ) (h ξ') :=
  fun ξ ξ' hle => Hd.1.2.2.1 ⟨⟩ ξ ξ' hle

/-- Rocq: `BachmannAgree.emap_D0`. -/
theorem emap_D0 (d1 d3 : bdesc.{u}) (_Hc1 : DCan d1) (Hc3 : DCan d3) (H : D0 d1 d3) : Dstar (emap d1) (emap d3) := by
  refine D0_star _ _ (dcan_emap _ Hc3) ?_
  cases H with
  | ss_sub t u H => exact .ff_pt _ _ fun ξ => bsub_bmul_l _ _ (bsub_bexpΩ _ _ H) _
  | ss_lt t u H =>
    exact .ffZ _ _ fun z hz => bleZ_mono_r _ _ _ _ (bleZ_exp_lt t u H z hz) (bsub_P_Pz _ z (inf_pos z hz))
  | sf t h n H =>
    exact .ffZ _ _ fun z hz => bleZ_exp_lt t (h z) (bslt_bsub_r _ _ _ H (dcan_fam_mono h Hc3 _ _ (hz n))) z hz
  | fs h u e H =>
    refine .ffZ _ _ fun z hz => ?_
    obtain ⟨t, ht⟩ := bexpΩ_big_b u e
    exact bleZ_mono_r _ _ _ _ (.big _ t z (le_refl z) (by rw [ht]; exact .sub _ (bsub_bexpΩ _ _ (H z))))
      (bsub_P_Pz _ z (inf_pos z hz))
  | ff_pt h1 h3 H => exact .ff_pt _ _ fun ξ => bsub_bexpΩ _ _ (H ξ)
  | ff_in h1 h3 n e H =>
    refine .ffZ _ _ fun z hz => ?_
    obtain ⟨t, ht⟩ := bexpΩ_big_b (h3 (ofNat n)) e
    exact bleZ_mono_r _ _ _ _ (.big _ t z (le_refl z) (by rw [ht]; exact .sub _ (bsub_bexpΩ _ _ (H z))))
      (bsub_bexpΩ _ _ (dcan_fam_mono h3 Hc3 _ _ (hz n)))
  | ffZ h1 h3 H => exact .ffZ _ _ fun z hz => bleZ_exp z _ _ hz (H z hz)

/-- Rocq: `BachmannAgree.emap_Dstar`. -/
theorem emap_Dstar (d1 d3 : bdesc.{u}) (Hc1 : DCan d1) (Hc3 : DCan d3) (H : Dstar d1 d3) : Dstar (emap d1) (emap d3) := by
  induction H with
  | refl _ => exact .refl _
  | step d1 d2 _ hc2 h0 _ ih => exact Dstar_trans _ _ _ (emap_D0 d1 d2 Hc1 hc2 h0) (ih hc2 Hc3)

/-- Rocq: `BachmannAgree.bexpΩ_desc_cases`. -/
theorem bexpΩ_desc_cases (y : BOrd.{u}) (k : bsmall (bexpΩ y) ⊕ bbig (bexpΩ y)) :
    ndesc (bexpΩ y) k = .DSmall bzero ∨ ∃ yk, ndesc (bexpΩ y) k = emap (ndesc y yk) := by
  cases y with
  | bnode B g' D h' =>
  match k with
  | .inl (.inl _) => exact .inl rfl
  | .inl (.inr (.inl ⟨_, .inl ⟨e, _⟩⟩)) => exact nomatch e
  | .inl (.inr (.inl ⟨_, .inr e⟩)) => exact nomatch e
  | .inl (.inr (.inr e)) => exact nomatch e
  | .inr (.inl e) => exact nomatch e
  | .inr (.inr (.inl ⟨_, .inl ⟨e, _⟩⟩)) => exact nomatch e
  | .inr (.inr (.inl ⟨b, .inr _⟩)) => exact .inr ⟨.inl b, rfl⟩
  | .inr (.inr (.inr d)) => exact .inr ⟨.inr d, rfl⟩

/-- Rocq: `BachmannAgree.bexpΩ_desc_back`. -/
theorem bexpΩ_desc_back (y : BOrd.{u}) (yk : bsmall y ⊕ bbig y) : ∃ k, ndesc (bexpΩ y) k = emap (ndesc y yk) := by
  cases y with
  | bnode B g' D h' =>
  match yk with
  | .inl b => exact ⟨.inr (.inr (.inl ⟨b, .inr ⟨⟩⟩)), rfl⟩
  | .inr d => exact ⟨.inr (.inr (.inr d)), rfl⟩

/-- Rocq: `BachmannAgree.bzero_dom_emap`. -/
theorem bzero_dom_emap (d : bdesc.{u}) (Hd : DCan d) : Dstar (.DSmall bzero) (emap d) := by
  refine D0_star _ _ (dcan_emap _ Hd) ?_
  cases d with
  | DSmall t => exact .sf _ _ 1 (bslt_bsub_r _ _ _ (bpos_bexpΩ t) (bsub_bmul_one _).2)
  | DFam h => exact .sf _ _ 0 (bpos_bexpΩ _)

/-- Rocq: `BachmannAgree.sdir_bexpΩ`. -/
theorem sdir_bexpΩ (y : BOrd.{u}) (Hyc : BCd y) (Hy : SDir y) : SDir (bexpΩ y) := by
  intro k1 k2
  match bexpΩ_desc_cases y k1, bexpΩ_desc_cases y k2 with
  | .inl E1, .inl E2 => exact ⟨k1, .refl _, by rw [E2, E1]; exact .refl _⟩
  | .inl E1, .inr ⟨y2, E2⟩ =>
    obtain ⟨k3, E3⟩ := bexpΩ_desc_back y y2
    exact ⟨k3, by rw [E1, E3]; exact bzero_dom_emap _ (dcan_ndesc y y2 Hyc), by rw [E2, E3]; exact .refl _⟩
  | .inr ⟨y1, E1⟩, .inl E2 =>
    obtain ⟨k3, E3⟩ := bexpΩ_desc_back y y1
    exact ⟨k3, by rw [E1, E3]; exact .refl _, by rw [E2, E3]; exact bzero_dom_emap _ (dcan_ndesc y y1 Hyc)⟩
  | .inr ⟨y1, E1⟩, .inr ⟨y2, E2⟩ =>
    obtain ⟨y3, D1, D2⟩ := Hy y1 y2
    obtain ⟨k3, E3⟩ := bexpΩ_desc_back y y3
    exact ⟨k3, by rw [E1, E3]; exact emap_Dstar _ _ (dcan_ndesc y y1 Hyc) (dcan_ndesc y y3 Hyc) D1,
      by rw [E2, E3]; exact emap_Dstar _ _ (dcan_ndesc y y2 Hyc) (dcan_ndesc y y3 Hyc) D2⟩

/-- Rocq: `BachmannAgree.bsdirH_bzero`. -/
theorem bsdirH_bzero : BSdirH bzero.{u} :=
  ⟨fun e => (nomatch e), fun e => (nomatch e), fun k1 _ => match k1 with
    | .inl e => nomatch e
    | .inr e => nomatch e⟩

/-- Rocq: `BachmannAgree.bsdirH_bexpΩ`. -/
theorem bsdirH_bexpΩ (y : BOrd.{u}) : BCd y → BSdirH y → BSdirH (bexpΩ y) := by
  induction y with
  | bnode B g' D h' ihg ihh =>
  intro Hyc Hyd
  have Hyc1 : ∀ b, BCd (g' b) := fun b => bcd_small (bnode B g' D h') b Hyc
  have Hyc2 : ∀ d ξ, Complete ξ → BCd (h' d ξ) := fun d ξ hξ => bcd_big (bnode B g' D h') d ξ Hyc hξ
  obtain ⟨Hy1, Hy2, Hy3⟩ := Hyd
  have Hsd : SDir (bexpΩ (bnode B g' D h')) := sdir_bexpΩ _ Hyc Hy3
  refine ⟨fun s => ?_, fun c ξ hξ => ?_, Hsd⟩
  · match s with
    | .inl _ => exact bsdirH_bzero
    | .inr (.inl ⟨_, .inl ⟨e, _⟩⟩) => exact nomatch e
    | .inr (.inl ⟨_, .inr e⟩) => exact nomatch e
    | .inr (.inr e) => exact nomatch e
  · match c with
    | .inl e => exact nomatch e
    | .inr (.inl ⟨_, .inl ⟨e, _⟩⟩) => exact nomatch e
    | .inr (.inl ⟨b, .inr _⟩) =>
      exact bsdirH_bmul (bexpΩ (g' b)) (embed ξ) (bcd_bexpΩ _ (Hyc1 b)) (bpos_bexpΩ _) (ihg b (Hyc1 b) (Hy1 b))
        (bcd_embed ξ hξ) (bsdirH_embed ξ hξ)
    | .inr (.inr d) => exact ihh d ξ (Hyc2 d ξ hξ) (Hy2 d ξ hξ)

/-! ### The tower below `ε_{Ω+1}` -/

/-- Rocq: `BachmannAgree.bsdirH_bsucc`. -/
theorem bsdirH_bsucc (x : BOrd.{u}) (Hx : BSdirH x) : BSdirH (bsucc x) :=
  ⟨fun _ => Hx, fun e => (nomatch e), fun k1 k2 => match k1, k2 with
    | .inl _, .inl _ => ⟨.inl ⟨⟩, .refl _, .refl _⟩
    | .inl _, .inr e => nomatch e
    | .inr e, _ => nomatch e⟩

/-- Rocq: `BachmannAgree.bsdirH_btower`. -/
theorem bsdirH_btower : ∀ n : Nat, BSdirH (btower.{u} n)
  | 0 => bsdirH_bsucc _ bsdirH_Ω
  | n + 1 => bsdirH_bexpΩ _ (bcd_btower n) (bsdirH_btower n)

/-- Rocq: `BachmannAgree.bach_bphi_tower`. -/
theorem bach_bphi_tower (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (n : Nat) :
    BRep f (btower n) (bphi f (btower n)) :=
  bach_bphi_canon f hf _ (bcd_btower n) (bsdirH_btower n)

/-! ## The top: `ε_{Ω+1}`

The components of `bεΩ1` are the towers. Each is dominated by the next:
tower `n` lies strictly below a tree `D` that is reachable from tower `n+1`
through arguments at most `z`, for every infinite `z`. This is a z-relative
variant of `bslt`, and it implies domination by `bnest` once the fixpoint
property is carried down the path. -/

/-- Rocq: `BachmannAgree.bleZ_trans`. -/
theorem bleZ_trans (z : Ordinal.{u}) (a b c : BOrd.{u}) (H1 : bleZ z a b) (H2 : bleZ z b c) : bleZ z a c := by
  induction H2 with
  | sub c H => exact bleZ_mono_r _ _ _ _ H1 H
  | small c j _ ih => exact .small _ j ih
  | big c d ζ hζ _ ih => exact .big _ d ζ hζ ih

/-! ### The base case: `Ω+1` -/

/-- Rocq: `BachmannAgree.embed_le_mul`. -/
theorem embed_le_mul (P : BOrd.{u}) (ζ : Ordinal.{u}) (H : ∃ t, bsmallSz P t = bzero) :
    bsub (embed ζ) (bmul P (embed ζ)) := by
  obtain ⟨t0, Ht0⟩ := H
  induction ζ with
  | mk X k ihk =>
  refine bsub_intro _ _ (fun i => ?_) (fun e => (nomatch e))
  obtain ⟨s, Hs⟩ := badd_small_r (bmul P (embed (k i))) P t0
  obtain ⟨t, Ht⟩ := bmul_small_r P (embed (mk X k)) i s
  refine ⟨t, ?_⟩
  rw [Ht]
  show bsub (embed (k i)) (bsmallSz (badd (bmul P (embed (k i))) P) s)
  rw [Hs, Ht0]
  exact bsub_trans (ihk i) (bsub_le_badd _ _)

/-- Rocq: `BachmannAgree.Ω_le_exp`. -/
theorem Ω_le_exp (w : Ordinal.{u}) (Hw : 0 < w) : bsub bOmega (bexpΩ (embed w)) := by
  cases w with
  | mk W m =>
  obtain ⟨c, _⟩ := lt_elim Hw
  refine bsub_intro _ _ (fun e => (nomatch e)) (fun _ => ?_)
  obtain ⟨t, Ht⟩ := bexpΩ_fam_s (embed (mk W m)) c
  exact ⟨t, fun ξ => by rw [Ht]; exact embed_le_mul _ ξ (bexpΩ_small_zero _)⟩

/-- `P·k` lies strictly below `P·(k+1)` when `P` has the small child 0.
Rocq: `BachmannAgree.bslt_mul_succ`. -/
theorem bslt_mul_succ (P : BOrd.{u}) (k : Ordinal.{u}) (H : ∃ t, bsmallSz P t = bzero) :
    bslt (bmul P (embed k)) (bmul P (embed (succ k))) := by
  obtain ⟨t0, Ht0⟩ := H
  obtain ⟨s, Hs⟩ := badd_small_r (bmul P (embed k)) P t0
  obtain ⟨t, Ht⟩ := bmul_small_r P (embed (succ k)) ⟨⟩ s
  refine .small _ t ?_
  rw [Ht]
  show bsub (bmul P (embed k)) (bsmallSz (badd (bmul P (embed k)) P) s)
  rw [Hs, Ht0]
  exact bsub_le_badd _ _

/-- Rocq: `BachmannAgree.bsucc_Ω_le`. -/
theorem bsucc_Ω_le (P : BOrd.{u}) (HP : bsub bOmega P) (H : ∃ t, bsmallSz P t = bzero) :
    bsub (bsucc bOmega) (bmul P (embed 2)) := by
  obtain ⟨t0, Ht0⟩ := H
  obtain ⟨s, Hs⟩ := badd_small_r (bmul P (embed 1)) P t0
  obtain ⟨t, Ht⟩ := bmul_small_r P (embed 2) ⟨⟩ s
  refine bsub_intro _ _ (fun _ => ⟨t, ?_⟩) (fun e => (nomatch e))
  rw [Ht]
  show bsub bOmega (bsmallSz (badd (bmul P (embed 1)) P) s)
  rw [Hs, Ht0]
  exact bsub_trans HP (bsub_trans (bsub_bmul_one P).2 (bsub_le_badd _ _))

/-- Rocq: `BachmannAgree.tower_base`. -/
theorem tower_base (z : Ordinal.{u}) (Hz : ∀ n : Nat, ofNat n ≤ z) :
    ∃ D, bslt (bsucc bOmega) D ∧ bleZ z D (bexpΩ (bsucc bOmega)) := by
  have H2 : 1 < z := lt_of_lt_of_le (succ_lt 1) (Hz 2)
  cases z with
  | mk Z k =>
  obtain ⟨c, hc⟩ := lt_elim H2
  have Hc0 : 0 < k c := lt_of_lt_of_le (succ_lt 0) hc
  refine ⟨bexpΩ (embed (mk Z k)), ?_, ?_⟩
  · obtain ⟨t, Ht⟩ := bexpΩ_fam_s (embed (mk Z k)) c
    refine .big _ t 3 ?_
    rw [Ht]
    show bslt (bsucc bOmega) (bmul (bexpΩ (embed (k c))) (embed (succ 2)))
    exact bslt_bsub_l _ _ _ (bsucc_Ω_le _ (Ω_le_exp _ Hc0) (bexpΩ_small_zero _))
      (bslt_mul_succ _ 2 (bexpΩ_small_zero _))
  · obtain ⟨t, Ht⟩ := bexpΩ_fam_s (bsucc bOmega) ⟨⟩
    refine .big _ t 1 (Hz 1) ?_
    rw [Ht]
    show bleZ (mk Z k) (bexpΩ (embed (mk Z k))) (bmul (bexpΩ bOmega) (embed 1))
    refine bleZ_mono_r _ _ _ _ ?_ (bsub_bmul_one _).2
    obtain ⟨t', Ht'⟩ := bexpΩ_big_b bOmega ⟨⟩
    exact .big _ t' (mk Z k) (le_refl _) (by rw [Ht']; exact .sub _ (bsub_refl _))

/-! ### The inductive step, and domination along the tower -/

/-- Rocq: `BachmannAgree.tower_rel`. -/
theorem tower_rel : ∀ (n : Nat) (z : Ordinal.{u}), (∀ m : Nat, ofNat m ≤ z) →
    ∃ D, bslt (btower n) D ∧ bleZ z D (btower (n + 1))
  | 0, z, hz => tower_base z hz
  | n + 1, z, hz =>
    let ⟨D, h1, h2⟩ := tower_rel n z hz
    ⟨bexpΩ D, bslt_bexpΩ _ _ h1, bleZ_exp z _ _ hz h2⟩

/-- Rocq: `BachmannAgree.tower_dom`. -/
theorem tower_dom (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (n : Nat) (z : Ordinal.{u})
    (Hz : Complete z) (Hle : bphi f (btower (n + 1)) z ≤ z) : bphi f (btower n) z ≤ z := by
  obtain ⟨Hfam, Hgood⟩ := dcan_good f hf _ (bcd_btower (n + 1))
  have Hfix := bfix_of_fix f hf _ z Hgood Hfam Hz Hle
  obtain ⟨D, H1, H2⟩ := tower_rel n z fun m => fix_onePlus_finite f hf z Hz Hfix.1 m
  exact bleZ_nest f hf z D (btower (n + 1)) (btower n) H2 H1 (btower (n + 1)) (bsub_refl _) Hgood Hfam Hz Hfix

/-- Rocq: `BachmannAgree.tower_dom_le`. -/
theorem tower_dom_le (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (n m : Nat) (H : n ≤ m) :
    ∀ z, Complete z → bphi f (btower m) z ≤ z → bphi f (btower n) z ≤ z := by
  induction H with
  | refl => exact fun _ _ hle => hle
  | step _ ih => exact fun z hz hle => ih z hz (tower_dom f hf _ z hz hle)

/-- Rocq: `BachmannAgree.bdirH_εΩ1`. -/
theorem bdirH_εΩ1 (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) : BDirH f bεΩ1 :=
  ⟨fun n => bsdirH_bdirH f hf _ (bcd_btower n.down) (bsdirH_btower n.down), fun e => (nomatch e), fun k1 k2 =>
    match k1, k2 with
    | .inl n1, .inl n2 =>
      ⟨.inl ⟨Nat.max n1.down n2.down⟩,
        fun z hz hle => tower_dom_le f hf _ _ (Nat.le_max_left _ _) z hz hle,
        fun z hz hle => tower_dom_le f hf _ _ (Nat.le_max_right _ _) z hz hle⟩
    | .inl _, .inr e => nomatch e
    | .inr e, _ => nomatch e⟩

/-- Rocq: `BachmannAgree.bach_bphi_εΩ1`. -/
theorem bach_bphi_εΩ1 (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) : BRep f bεΩ1 (bphi f bεΩ1) :=
  have ⟨Hfam, Hgood⟩ := dcan_good f hf _ bcd_bεΩ1
  bach_bphi f hf _ Hgood Hfam (bdirH_εΩ1 f hf)

/-! ## Certification of the Bachmann–Howard ordinal

Bachmann's `φ` (one component at a time), at the index `ε_{Ω+1}`, represents
the provably normal hierarchy `bphi` there. In particular the Bachmann–Howard
ordinal as defined in `Bachmann/Defs` is `BachmannHoward`. -/

/-- Rocq: `BachmannAgree.bach_BachmannHoward`. -/
theorem bach_BachmannHoward : BHO.{u} ≈ BachmannHoward.{u} :=
  (bach_bphi_εΩ1 powOmega powOmega_normal).2.1 0 zero_complete

end Bachmann

end ConstructiveOrdinals
