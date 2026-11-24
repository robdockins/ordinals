import ConstructiveOrdinals.Bachmann.Assoc

/-!
# Arbitrary powers of Ω, and the canonical trees

Ported from the Rocq file `BachmannPower.v`.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-! ## Auxiliary lemmas for the power theorems -/

/-- Rocq: `BachmannPower.fixOrd_ext_eq`. -/
theorem fixOrd_ext_eq (F F' : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) (H : ∀ x, F x = F' x) :
    fixOrd F a ≈ fixOrd F' a := by
  have hiter : ∀ n, iterF F a n = iterF F' a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => show F (iterF F a n) = F' (iterF F' a n); rw [ih, H]
  exact sup_congr fun n => by rw [hiter n.down]

/-- Rocq: `BachmannPower.BRep_ext`. -/
theorem BRep_ext (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (T : BOrd.{u})
    (G G' : Ordinal.{u} → Ordinal.{u}) (HT : BMono f T) (HR : BRep f T G) (HG' : NormalFunction G')
    (Heq : ∀ x, Complete x → G x ≈ G' x) : BRep f T G' := by
  obtain ⟨_, Hrep, Hcl⟩ := HR
  refine ⟨HG', fun y hy => equiv_trans (Hrep y hy) (Heq y hy), fun k y hy => ?_⟩
  exact le_trans (bmono_bcomp f hf T HT k _ _ (Heq y hy).ge) (le_trans (Hcl k y hy) (Heq y hy).le)

/-! Adding to zero does not change `φ`. -/

/-- Rocq: `BachmannPower.bsub_badd_zero_l1`. -/
theorem bsub_badd_zero_l1 : ∀ y : BOrd.{u}, bsub (badd bzero y) y
  | bnode _ g _ h => ⟨fun s => match s with
      | .inl e => nomatch e
      | .inr b => ⟨b, bsub_badd_zero_l1 (g b)⟩,
    fun c => match c with
      | .inl e => nomatch e
      | .inr d => ⟨d, fun ξ => bsub_badd_zero_l1 (h d ξ)⟩⟩

/-- Rocq: `BachmannPower.bsub_badd_zero_l2`. -/
theorem bsub_badd_zero_l2 : ∀ y : BOrd.{u}, bsub y (badd bzero y)
  | bnode _ g _ h => ⟨fun b => ⟨.inr b, bsub_badd_zero_l2 (g b)⟩, fun d => ⟨.inr d, fun ξ => bsub_badd_zero_l2 (h d ξ)⟩⟩

/-- Rocq: `BachmannPower.bach_badd_zero_l`. -/
theorem bach_badd_zero_l (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (y : BOrd.{u})
    (hy : BFam y) (z : Ordinal.{u}) : bach f (badd bzero y) z ≈ bach f y z :=
  bach_bsub_eq f hf _ _ (bsub_badd_zero_l1 y) (bsub_badd_zero_l2 y) (bfam_badd _ _ bfam_bzero hy) hy z

/-! ## Arbitrary powers of Ω: the full Schütte column

We now treat all exponents uniformly. `bPow ζ` is `Ω^ζ`, defined by recursion
on the tree `ζ`: a node with the small child `0` and, for each child `ζ_i` of
`ζ`, the Ω-family `ξ ↦ Ω^(ζ_i)·ξ`. The children of the Schütte column `1+ζ`
are exactly `0` and the `1+ζ_i`, matching these components one for one, so
`β + Ω^ζ·ξ` represents column `1+ζ` over `β`, for zero, successor and limit
`ζ` alike.

Because the column may be a limit, we cannot use `schutte_column_succ` and must
absorb the base term `G(ξ+y)` of the general unrolling. When `ξ` has children
this uses continuity of `G` over the directed family of column-0 fixpoints,
each of which lies above `ξ`. -/

/-- `Ω^ζ`, by recursion on `ζ`. Rocq: `BachmannPower.bPow`. -/
def bPow : Ordinal.{u} → BOrd.{u}
  | mk Z m => bnode PUnit (fun _ => bzero) Z (fun i ξ => bmul (bPow (m i)) (embed ξ))

/-- Rocq: `BachmannPower.bfam_bPow`. -/
theorem bfam_bPow : ∀ ζ : Ordinal.{u}, BFam (bPow ζ)
  | mk _ m => ⟨fun _ => bfam_bzero, fun i ξ => bfam_bmul _ _ (bfam_bPow (m i)) (bfam_embed ξ),
      fun _ ξ ξ' H => bsub_bmul_r _ _ _ (bsub_embed ξ ξ' H)⟩

/-- Every component of `β + Q·ξ` (for `ξ` with children `k b`) is one of: a
component of `β`, a component of `β + Q·(k b)`, or `β + (Q·(k b) + c)` for a
component `c` of `Q`. Rocq: `BachmannPower.bcomp_shift_bmul_forall'`. -/
theorem bcomp_shift_bmul_forall' (f : Ordinal.{u} → Ordinal.{u}) (β Q : BOrd.{u}) (X : Type u) (k : X → Ordinal.{u})
    (P : (Ordinal.{u} → Ordinal.{u}) → Prop) (Pext : ∀ g g', (∀ x, g x = g' x) → P g → P g')
    (H1 : ∀ kk, P (bcomp f β kk))
    (H2 : ∀ b kk, P (bcomp f (badd β (bmul Q (embed (k b)))) kk))
    (H3 : ∀ b q, P (bach f (badd β (badd (bmul Q (embed (k b))) (bsmallSz Q q)))))
    (H4 : ∀ b d, P fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d ζ))) 0) :
    ∀ kk, P (bcomp f (badd β (bmul Q (embed (mk X k)))) kk) := by
  intro kk
  match kk with
  | .inl s =>
    match badd_small_cases β (bmul Q (embed (mk X k))) s with
    | .inl ⟨a, Ha⟩ =>
      refine Pext (bcomp f β (.inl a)) _ (fun x => ?_) (H1 _)
      show bach f (bsmallSz β a) x = bach f (bsmallSz (badd β (bmul Q (embed (mk X k)))) s) x
      rw [Ha]
    | .inr ⟨mm, Hm⟩ =>
      match mm, Hm with
      | .inr e, _ => exact nomatch e
      | .inl ⟨b, m'⟩, Hm =>
        have Hm : bsmallSz (badd β (bmul Q (embed (mk X k)))) s =
            badd β (bsmallSz (badd (bmul Q (embed (k b))) Q) m') := Hm
        match badd_small_cases (bmul Q (embed (k b))) Q m' with
        | .inl ⟨a'', Ha''⟩ =>
          obtain ⟨t, Ht⟩ := badd_small_r β (bmul Q (embed (k b))) a''
          refine Pext (bcomp f (badd β (bmul Q (embed (k b)))) (.inl t)) _ (fun x => ?_) (H2 b _)
          show bach f (bsmallSz (badd β (bmul Q (embed (k b)))) t) x =
            bach f (bsmallSz (badd β (bmul Q (embed (mk X k)))) s) x
          rw [Ht, Hm, Ha'']
        | .inr ⟨q, Hq⟩ =>
          refine Pext _ _ (fun x => ?_) (H3 b q)
          show bach f (badd β (badd (bmul Q (embed (k b))) (bsmallSz Q q))) x =
            bach f (bsmallSz (badd β (bmul Q (embed (mk X k)))) s) x
          rw [Hm, Hq]
  | .inr c =>
    match badd_big_cases β (bmul Q (embed (mk X k))) c with
    | .inl ⟨c', Hc⟩ =>
      refine Pext (bcomp f β (.inr c')) _ (fun x => ?_) (H1 _)
      show bach f (bbigSz β c' x) 0 = bach f (bbigSz (badd β (bmul Q (embed (mk X k)))) c x) 0
      rw [Hc x]
    | .inr ⟨mm, Hm⟩ =>
      match mm, Hm with
      | .inr e, _ => exact nomatch e
      | .inl ⟨b, m'⟩, Hm =>
        have Hm' : ∀ ξ, bbigSz (badd β (bmul Q (embed (mk X k)))) c ξ =
            badd β (bbigSz (badd (bmul Q (embed (k b))) Q) m' ξ) := Hm
        match badd_big_cases (bmul Q (embed (k b))) Q m' with
        | .inl ⟨e, He⟩ =>
          obtain ⟨t, Ht⟩ := badd_big_r β (bmul Q (embed (k b))) e
          refine Pext (bcomp f (badd β (bmul Q (embed (k b)))) (.inr t)) _ (fun x => ?_) (H2 b _)
          show bach f (bbigSz (badd β (bmul Q (embed (k b)))) t x) 0 =
            bach f (bbigSz (badd β (bmul Q (embed (mk X k)))) c x) 0
          rw [Ht x, Hm' x, He x]
        | .inr ⟨d, Hd⟩ =>
          refine Pext (fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d ζ))) 0) _
            (fun x => ?_) (H4 b d)
          show bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d x))) 0 =
            bach f (bbigSz (badd β (bmul Q (embed (mk X k)))) c x) 0
          rw [Hm' x, Hd x]

/-- Rocq: `BachmannPower.Scol_fix0'`. -/
theorem Scol_fix0' (G : Ordinal.{u} → Ordinal.{u}) (HG : NormalFunction G) (C a ξ y : Ordinal.{u})
    (HC : Complete C) (HC0 : 0 < C) (Ha : Complete a) (Hξ : Complete ξ) (Hy : Complete y) (Haξ : a < ξ) :
    schutteColumn G C a (schutteColumn G C ξ y) ≤ schutteColumn G C ξ y :=
  calc schutteColumn G C a (schutteColumn G C ξ y)
      ≤ schutteColumn G C a (schutteColumn G C ξ y + 0) :=
        (schutte_column_normal C a G HC Ha HG).monotone _ _ (le_add_right _ _)
    _ ≤ schutteColumn (schutteColumn G C a) 0 (schutteColumn G C ξ y) 0 := (schutte_column0 _ _ 0).ge
    _ ≤ schutteColumn G C ξ y := schutte_column_fixpoint C ξ y G 0 a HC Hξ HG HC0 Haξ zero_complete Ha Hy

/-- Rocq: `BachmannPower.Scol_value_cases'`. -/
theorem Scol_value_cases' (G : Ordinal.{u} → Ordinal.{u}) (HG : NormalFunction G) (C ξ y : Ordinal.{u})
    (HC : Complete C) (HC0 : 0 < C) (Hξ : Complete ξ) (Hy : Complete y) :
    schutteColumn G C ξ y ≈ G y ∨ schutteColumn G C ξ y ≈ G (schutteColumn G C ξ y) := by
  cases ξ with
  | mk X k =>
  have Hξ' : Complete (mk X k) := Hξ
  obtain ⟨_, hne, hkc⟩ := Hξ
  match hne with
  | .inl ⟨x0⟩ =>
    have hv := (schutte_column_normal C _ G HC Hξ' HG).complete y Hy
    refine .inr (equiv_intro (normal_inflationary HG _ hv) ?_)
    calc G (schutteColumn G C (mk X k) y) ≤ G (k x0 + schutteColumn G C (mk X k) y) :=
          HG.monotone _ _ (le_add_left _ _)
      _ ≤ schutteColumn G C (k x0) (schutteColumn G C (mk X k) y) := schutte_column_le_f C (k x0) _ G HG.monotone
      _ ≤ schutteColumn G C (mk X k) y :=
          Scol_fix0' G HG C (k x0) (mk X k) y HC HC0 (hkc x0) Hξ' Hy (index_lt (mk X k) x0)
  | .inr hn =>
    have Hξy : mk X k + y ≈ y :=
      equiv_intro (le_trans (add_le_add (le_intro fun a => (hn ⟨a⟩).elim : mk X k ≤ 0) (le_refl y)) (zero_add y).le)
        (le_add_left _ _)
    refine .inl (equiv_intro ?_ (le_trans (HG.monotone _ _ Hξy.ge) (schutte_column_le_f C (mk X k) y G HG.monotone)))
    rw [schutte_column_unroll]
    exact lub_least (HG.monotone _ _ Hξy.le) (sup_least fun _ => sup_least fun a => (hn ⟨a⟩).elim)

/-- The power theorem: `β + Ω^ζ·ξ` represents the Schütte column `1+ζ` over
`β`. Rocq: `BachmannPower.bach_bPow_rep`. -/
theorem bach_bPow_rep (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ ζ : Ordinal.{u}, Complete ζ → ∀ (β : BOrd.{u}) (G : Ordinal.{u} → Ordinal.{u}), BFam β → BRep f β G →
      ∀ ξ, Complete ξ → BRep f (badd β (bmul (bPow ζ) (embed ξ))) (schutteColumn G (1 + ζ) ξ) := by
  intro ζ
  induction ζ with
  | mk Z m ihm =>
  intro hζ β G hβ HR
  have hmc : ∀ i, Complete (m i) := fun i => complete_subord hζ i
  have HC : Complete (1 + mk Z m) := onePlus_complete hζ
  have HC0 : 0 < 1 + mk Z m := onePlus_nonzero _
  have HR' := HR
  obtain ⟨HG, Hrep, Hcl⟩ := HR'
  have HGm := HG.monotone
  have hbm : BMono f β := bfam_bmono f hf β hβ
  have HMfam : ∀ ξ, BFam (bmul (bPow (mk Z m)) (embed ξ)) := fun ξ => bfam_bmul _ _ (bfam_bPow _) (bfam_embed ξ)
  have HTfam : ∀ ξ, BFam (badd β (bmul (bPow (mk Z m)) (embed ξ))) := fun ξ => bfam_badd _ _ hβ (HMfam ξ)
  have Hmono : ∀ ξ, BMono f (badd β (bmul (bPow (mk Z m)) (embed ξ))) := fun ξ => bfam_bmono f hf _ (HTfam ξ)
  intro ξ
  induction ξ with
  | mk X k ihk =>
  intro hξ
  have hξ' := hξ
  obtain ⟨hdirξ, hinhξ, hkc⟩ := hξ'
  have HS : NormalFunction (schutteColumn G (1 + mk Z m) (mk X k)) := schutte_column_normal _ _ G HC hξ HG
  have HSk : ∀ b, NormalFunction (schutteColumn G (1 + mk Z m) (k b)) := fun b =>
    schutte_column_normal _ _ G HC (hkc b) HG
  have HIH : ∀ b, BRep f (badd β (bmul (bPow (mk Z m)) (embed (k b)))) (schutteColumn G (1 + mk Z m) (k b)) :=
    fun b => ihk b (hkc b)
  -- the small component 0 of Ω^ζ, shifted
  have Hsm : ∀ b x, Complete x →
      bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) bzero)) x ≈
        schutteColumn (schutteColumn G (1 + mk Z m) (k b)) 0 x 0 := fun b x hx =>
    equiv_trans (bach_badd_assoc f hf β _ bzero hβ (HMfam (k b)) bfam_bzero x)
      (equiv_trans (bach_badd_zero f hf _ (Hmono (k b)) x)
        (equiv_trans ((HIH b).2.1 x hx)
          (equiv_symm (equiv_trans (schutte_column0 _ x 0)
            (equiv_intro ((HSk b).monotone _ _ (add_zero x).le) ((HSk b).monotone _ _ (add_zero x).ge))))))
  have Hsm_mono : ∀ b x y, x ≤ y →
      bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) bzero)) x ≤
        bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) bzero)) y := fun b x y hxy =>
    bach_monotone hf _ (bfam_bmono f hf _ (bfam_badd _ _ hβ (bfam_badd _ _ (HMfam _) bfam_bzero))) x y hxy
  -- the Ω-family components ξ' ↦ Ω^(ζ_i)·ξ', shifted
  have Hfm : ∀ b i x, Complete x →
      bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) (bmul (bPow (m i)) (embed x)))) 0 ≈
        schutteColumn (schutteColumn G (1 + mk Z m) (k b)) (1 + m i) x 0 := fun b i x hx =>
    equiv_trans (bach_badd_assoc f hf _ _ _ hβ (HMfam _) (bfam_bmul _ _ (bfam_bPow _) (bfam_embed x)) 0)
      ((ihm i (hmc i) _ _ (HTfam (k b)) (HIH b) x hx).2.1 0 zero_complete)
  have Hfm_mono : ∀ b i x y, x ≤ y →
      bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) (bmul (bPow (m i)) (embed x)))) 0 ≤
        bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) (bmul (bPow (m i)) (embed y)))) 0 :=
    fun b i x y hxy =>
      bach_mono_index f hf _ _ (bsub_badd_r _ _ _ (bsub_badd_r _ _ _ (bsub_bmul_r _ _ _ (bsub_embed _ _ hxy))))
        (bfam_bmono f hf _ (bfam_badd _ _ hβ (bfam_badd _ _ (HMfam _) (bfam_bmul _ _ (bfam_bPow _) (bfam_embed y)))))
        0
  have Hcomp : ∀ kk y, Complete y →
      bcomp f (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) kk (schutteColumn G (1 + mk Z m) (mk X k) y) ≤
        schutteColumn G (1 + mk Z m) (mk X k) y := by
    intro kk y hy
    have hv := HS.complete y hy
    refine bcomp_shift_bmul_forall' f β (bPow (mk Z m)) X k
      (fun g => g (schutteColumn G (1 + mk Z m) (mk X k) y) ≤ schutteColumn G (1 + mk Z m) (mk X k) y)
      (fun g g' H h => H _ ▸ h) ?_ ?_ ?_ ?_ kk
    · intro kk'
      match Scol_value_cases' G HG (1 + mk Z m) (mk X k) y HC HC0 hξ hy with
      | .inl H => exact le_trans (bmono_bcomp f hf β hbm kk' _ _ H.le) (le_trans (Hcl kk' y hy) H.ge)
      | .inr H => exact le_trans (bmono_bcomp f hf β hbm kk' _ _ H.le) (le_trans (Hcl kk' _ hv) H.ge)
    · intro b kk'
      exact le_trans (bmono_bcomp f hf _ (Hmono (k b)) kk' _ _ (normal_inflationary (HSk b) _ hv))
        (le_trans ((HIH b).2.2 kk' _ hv)
          (Scol_fix0' G HG _ (k b) (mk X k) y HC HC0 (hkc b) hξ hy (index_lt (mk X k) b)))
    · intro b _
      show bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) bzero)) _ ≤ _
      exact le_trans (Hsm b _ hv).le
        (schutte_column_fixpoint (1 + mk Z m) (mk X k) y G 0 (k b) HC hξ HG HC0 (index_lt (mk X k) b) zero_complete
          (hkc b) hy)
    · intro b d
      show bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k b))) (bmul (bPow (m d)) (embed _)))) 0 ≤ _
      exact le_trans (Hfm b d _ hv).le
        (schutte_column_fixpoint (1 + mk Z m) (mk X k) y G (1 + m d) (k b) HC hξ HG
          (add_lt_add_left 1 (index_lt (mk Z m) d)) (index_lt (mk X k) b) (onePlus_complete (hmc d)) (hkc b) hy)
  refine ⟨HS, ?_, Hcomp⟩
  intro y
  induction y with
  | mk Y h ihy =>
  intro hyc
  have hhc : ∀ j, Complete (h j) := fun j => complete_subord hyc j
  have Hs : lim (fun j : Y => bach f (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) (h j)) ≈
      lim (fun j : Y => schutteColumn G (1 + mk Z m) (mk X k) (h j)) :=
    lim_eq_mor _ _ _ fun j => ihy j (hhc j)
  have Hsc : Complete (lim fun j : Y => schutteColumn G (1 + mk Z m) (mk X k) (h j)) :=
    lim_normal_complete (mk Y h) _ HS hyc
  -- the column-0 terms are below φ_T(y)
  have Hcol0 : ∀ a,
      fixOrd (fun δ => schutteColumn (schutteColumn G (1 + mk Z m) (k a)) 0 δ 0)
          (lim fun j : Y => schutteColumn G (1 + mk Z m) (mk X k) (h j)) ≤
        bach f (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) (mk Y h) := by
    intro a
    have HN0 := schutte_column_normal_arg 0 (schutteColumn G (1 + mk Z m) (k a)) zero_complete (HSk a)
    obtain ⟨cc, Hcc⟩ := badd_small_r (bmul (bPow (mk Z m)) (embed (k a))) (bPow (mk Z m)) ⟨⟩
    obtain ⟨t, Ht⟩ := badd_small_r β (bmul (bPow (mk Z m)) (embed (mk X k))) (.inl ⟨a, cc⟩)
    refine le_trans ?_ (bach_comp_le f (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) (mk Y h) (.inl t))
    have Heq : ∀ x, bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k a))) bzero)) x =
        bcomp f (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) (.inl t) x := fun x => by
      show _ = bach f (bsmallSz (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) t) x
      rw [Ht]
      show _ = bach f (badd β (bsmallSz (badd (bmul (bPow (mk Z m)) (embed (k a))) (bPow (mk Z m))) cc)) x
      rw [Hcc]
      rfl
    exact le_trans (fixOrd_eq_func_complete _ (fun δ => schutteColumn (schutteColumn G (1 + mk Z m) (k a)) 0 δ 0)
      _ _ (Hsm a) (Hsm_mono a) HN0.monotone HN0.complete Hs Hsc).ge (fixOrd_ext_eq _ _ _ Heq).le
  refine equiv_intro ?_ ?_
  · refine bach_le_comp f _ _ _ ?_ fun kk => ?_
    · exact le_trans (le_trans (f_le_bach f β _) (Hrep _ hyc).le)
        (le_trans (HGm _ _ (le_add_left _ _)) (schutte_column_le_f _ (mk X k) (mk Y h) G HGm))
    · refine fixOrd_least (bmono_bcomp f hf _ (Hmono _) kk) _ _ (le_trans Hs.le ?_) (Hcomp kk _ hyc)
      exact limit_least fun j => HS.increasing _ _ hyc (index_lt (mk Y h) j)
  · rw [schutte_column_unroll G (1 + mk Z m) (mk X k) (mk Y h)]
    refine lub_least ?_ (sup_least fun bb => ?_)
    · -- the base term G(ξ+y)
      match hinhξ with
      | .inl ⟨x0⟩ =>
        have HN0 : ∀ a, NormalFunction fun δ => schutteColumn (schutteColumn G (1 + mk Z m) (k a)) 0 δ 0 :=
          fun a => schutte_column_normal_arg 0 _ zero_complete (HSk a)
        let W := fun a => fixOrd (fun δ => schutteColumn (schutteColumn G (1 + mk Z m) (k a)) 0 δ 0)
          (lim fun j : Y => schutteColumn G (1 + mk Z m) (mk X k) (h j))
        have HWc : ∀ a, Complete (W a) := fun a =>
          normal_fix_complete _ Hsc (normal_inflationary (HN0 a)) (HN0 a).monotone (HN0 a).complete
        have HWbig : ∀ a, G (k a + W a) ≤ W a := fun a =>
          calc G (k a + W a) ≤ G (k a + (W a + 0)) := HGm _ _ (add_le_add (le_refl _) (add_zero _).ge)
            _ ≤ schutteColumn G (1 + mk Z m) (k a) (W a + 0) := schutte_column_le_f _ (k a) _ G HGm
            _ ≤ schutteColumn (schutteColumn G (1 + mk Z m) (k a)) 0 (W a) 0 := (schutte_column0 _ _ _).ge
            _ ≤ W a := (normal_fixpoint (HN0 a) _ Hsc).ge
        have HWpos : ∀ a, 0 < W a := fun a => lt_of_lt_of_le (HG.nonzero _) (HWbig a)
        have HkW : ∀ a, k a < W a := fun a =>
          calc k a ≤ k a + 0 := (add_zero _).ge
            _ < k a + W a := add_lt_add_left _ (HWpos a)
            _ ≤ G (k a + W a) := normal_inflationary HG _ (add_complete (hkc a) (HWc a))
            _ ≤ W a := HWbig a
        have HGW : ∀ a, G (W a) ≤ W a := fun a => le_trans (HGm _ _ (le_add_left _ _)) (HWbig a)
        have HWmono : ∀ a a', k a ≤ k a' → W a ≤ W a' := fun a a' ha =>
          fixOrd_monotone_func (fun δ => schutte_column_monotone_func _ _ 0 δ 0 δ 0 (HSk a).monotone (HSk a').monotone
            (fun x => schutte_column_monotone G (1 + mk Z m) (k a) x (k a') x HGm ha (le_refl x)) (le_refl δ)
            (le_refl 0)) (HN0 a').monotone _
        have HWdir : Directed X W := fun a1 a2 =>
          let ⟨a', h1, h2⟩ := hdirξ a1 a2
          ⟨a', HWmono a1 a' h1, HWmono a2 a' h2⟩
        have HξyZ : mk X k + mk Y h ≤ sup W := by
          rw [add_unfold]
          refine lub_least (le_intro fun a => lt_of_lt_of_le (HkW a) (sup_le W a)) (sup_least fun j => succ_least ?_)
          calc mk X k + h j ≤ G (mk X k + h j) := normal_inflationary HG _ (add_complete hξ (hhc j))
            _ ≤ schutteColumn G (1 + mk Z m) (mk X k) (h j) := schutte_column_le_f _ (mk X k) (h j) G HGm
            _ < lim (fun j : Y => schutteColumn G (1 + mk Z m) (mk X k) (h j)) :=
                limit_lt (fun j : Y => schutteColumn G (1 + mk Z m) (mk X k) (h j)) j
            _ ≤ W x0 := fixOrd_above _ _
            _ ≤ sup W := sup_le W x0
        calc G (mk X k + mk Y h) ≤ G (sup W) := HGm _ _ HξyZ
          _ ≤ sup fun a => G (W a) := HG.continuous X W x0 HWdir HWc
          _ ≤ sup W := sup_monotone HGW
          _ ≤ _ := sup_least Hcol0
      | .inr hn =>
        have Hξy : mk X k + mk Y h ≤ mk Y h :=
          le_trans (add_le_add (le_intro fun a => (hn ⟨a⟩).elim : mk X k ≤ 0) (le_refl _)) (zero_add _).le
        refine le_trans (HGm _ _ Hξy) (le_trans (Hrep _ hyc).ge (bach_mono_index f hf _ _ ?_ (Hmono _) _))
        rw [badd_eq β (bmul (bPow (mk Z m)) (embed (mk X k)))]
        exact bsub_blub_l _ _
    · match bb with
      | .inl _ => exact sup_least Hcol0
      | .inr ⟨d, _⟩ =>
        refine sup_least fun a => ?_
        have HNd := schutte_column_normal_arg (1 + m d) (schutteColumn G (1 + mk Z m) (k a)) (onePlus_complete (hmc d))
          (HSk a)
        obtain ⟨cc, Hcc⟩ := badd_big_r (bmul (bPow (mk Z m)) (embed (k a))) (bPow (mk Z m)) d
        obtain ⟨t, Ht⟩ := badd_big_r β (bmul (bPow (mk Z m)) (embed (mk X k))) (.inl ⟨a, cc⟩)
        refine le_trans ?_ (bach_comp_le f (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) (mk Y h) (.inr t))
        have Heq : ∀ x, (fun ζ' => bach f (badd β (badd (bmul (bPow (mk Z m)) (embed (k a)))
              (bmul (bPow (m d)) (embed ζ')))) 0) x =
            bcomp f (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) (.inr t) x := fun x => by
          show _ = bach f (bbigSz (badd β (bmul (bPow (mk Z m)) (embed (mk X k)))) t x) 0
          rw [Ht x]
          show _ = bach f (badd β (bbigSz (badd (bmul (bPow (mk Z m)) (embed (k a))) (bPow (mk Z m))) cc x)) 0
          rw [Hcc x]
          rfl
        exact le_trans (fixOrd_eq_func_complete _
            (fun δ => schutteColumn (schutteColumn G (1 + mk Z m) (k a)) (1 + m d) δ 0) _ _
            (Hfm a d) (Hfm_mono a d) HNd.monotone HNd.complete Hs Hsc).ge
          (fixOrd_ext_eq _ _ _ Heq).le

/-! ## The canonical trees

The power theorem above is stated for `bPow ζ`, which presents `Ω^ζ` by
recursion on `ζ`. The canonical tree `bexpΩ (embed ζ)` produced by the tree
arithmetic has the same components (the small child `0` and the families
`ξ ↦ Ω^(ζ_i)·ξ`), merely arranged differently, and the two are
`bsub`-equivalent; likewise `Ω^ζ·1` and `Ω^ζ`. We transfer the power theorem
along such equivalences, and along extensions by components that already fix
the represented values. -/

/-- Rocq: `BachmannPower.bsub_bPow`. -/
theorem bsub_bPow : ∀ ζ ζ' : Ordinal.{u}, ζ ≤ ζ' → bsub (bPow ζ) (bPow ζ')
  | mk _ m, mk _ m', H =>
    ⟨fun _ => ⟨⟨⟩, bsub_refl bzero⟩,
     fun i => let ⟨j, hj⟩ := le_subord H i; ⟨j, fun _ => bsub_bmul_l _ _ (bsub_bPow (m i) (m' j) hj) _⟩⟩

/-- Rocq: `BachmannPower.bsub_bPow_bexpΩ`. -/
theorem bsub_bPow_bexpΩ : ∀ ζ : Ordinal.{u}, bsub (bPow ζ) (bexpΩ (embed ζ)) ∧ bsub (bexpΩ (embed ζ)) (bPow ζ)
  | mk _ m =>
    ⟨⟨fun _ => ⟨.inl ⟨⟩, bsub_refl bzero⟩,
      fun i => ⟨.inr (.inl ⟨i, .inr ⟨⟩⟩), fun _ => bsub_bmul_l _ _ (bsub_bPow_bexpΩ (m i)).1 _⟩⟩,
     ⟨fun s => match s with
        | .inl _ => ⟨⟨⟩, bsub_refl bzero⟩
        | .inr (.inl ⟨_, .inl ⟨e, _⟩⟩) => nomatch e
        | .inr (.inl ⟨_, .inr e⟩) => nomatch e
        | .inr (.inr e) => (nomatch e),
      fun c => match c with
        | .inl e => nomatch e
        | .inr (.inl ⟨_, .inl ⟨e, _⟩⟩) => nomatch e
        | .inr (.inl ⟨i, .inr _⟩) => ⟨i, fun _ => bsub_bmul_l _ _ (bsub_bPow_bexpΩ (m i)).2 _⟩
        | .inr (.inr e) => nomatch e⟩⟩

/-- Rocq: `BachmannPower.bsub_badd_empty_l`. -/
theorem bsub_badd_empty_l (x : BOrd.{u}) (Hs : bsmall x → False) (Hb : bbig x → False) :
    ∀ y, bsub (badd x y) y ∧ bsub y (badd x y) := by
  cases x with
  | bnode A g C h =>
  intro y
  induction y with
  | bnode B g' D h' ihg ihh =>
  refine ⟨⟨fun s => ?_, fun c => ?_⟩, ⟨fun b => ⟨.inr b, (ihg b).2⟩, fun d => ⟨.inr d, fun ξ => (ihh d ξ).2⟩⟩⟩
  · match s with
    | .inl a => exact (Hs a).elim
    | .inr b => exact ⟨b, (ihg b).1⟩
  · match c with
    | .inl c' => exact (Hb c').elim
    | .inr d => exact ⟨d, fun ξ => (ihh d ξ).1⟩

/-- `P·1` and `P` are `bsub`-equivalent. Rocq: `BachmannPower.bsub_bmul_one`. -/
theorem bsub_bmul_one (P : BOrd.{u}) : bsub (bmul P (embed 1)) P ∧ bsub P (bmul P (embed 1)) := by
  obtain ⟨HZ1, HZ2⟩ := bsub_badd_empty_l (bmul P (embed 0))
    (fun s => match s with
      | .inl ⟨e, _⟩ => nomatch e
      | .inr e => nomatch e)
    (fun c => match c with
      | .inl ⟨e, _⟩ => nomatch e
      | .inr e => nomatch e) P
  refine ⟨bsub_intro _ _ (fun s => ?_) (fun c => ?_), bsub_intro _ _ (fun b => ?_) (fun d => ?_)⟩
  · match s with
    | .inl ⟨_, s⟩ => exact bsub_small _ _ HZ1 s
    | .inr e => exact nomatch e
  · match c with
    | .inl ⟨_, c⟩ => exact bsub_big _ _ HZ1 c
    | .inr e => exact nomatch e
  · obtain ⟨s, hs⟩ := bsub_small _ _ HZ2 b
    exact ⟨.inl ⟨⟨⟩, s⟩, hs⟩
  · obtain ⟨c, hc⟩ := bsub_big _ _ HZ2 d
    exact ⟨.inl ⟨⟨⟩, c⟩, hc⟩

/-- Transferring `BRep` along `bsub`. Rocq: `BachmannPower.bcomp_bsub`. -/
theorem bcomp_bsub (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (T T' : BOrd.{u})
    (H : bsub T' T) (HT : BFam T) : ∀ k', ∃ k, ∀ x, bcomp f T' k' x ≤ bcomp f T k x := by
  intro k'
  match k' with
  | .inl a' =>
    obtain ⟨a, ha⟩ := bsub_small _ _ H a'
    exact ⟨.inl a, fun x => bach_mono_index f hf _ _ ha (bfam_bmono f hf _ (bfam_small _ HT a)) x⟩
  | .inr c' =>
    obtain ⟨c, hc⟩ := bsub_big _ _ H c'
    exact ⟨.inr c, fun x => bach_mono_index f hf _ _ (hc x) (bfam_bmono f hf _ (bfam_big _ HT c x)) 0⟩

/-- If `T ⊑ T'` and every component of `T'` fixes the values of `G`, then `T'`
represents `G` whenever `T` does. Rocq: `BachmannPower.BRep_extend`. -/
theorem BRep_extend (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (T T' : BOrd.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (HTT' : bsub T T') (HT' : BFam T') (HR : BRep f T G)
    (Hcl' : ∀ k y, Complete y → bcomp f T' k (G y) ≤ G y) : BRep f T' G := by
  obtain ⟨HG, Hrep, _⟩ := HR
  have HT'm := bfam_bmono f hf T' HT'
  refine ⟨HG, ?_, Hcl'⟩
  intro y
  induction y with
  | mk Y h ihy =>
  intro hyc
  have hhc : ∀ j, Complete (h j) := fun j => complete_subord hyc j
  refine equiv_intro (bach_le_comp f T' _ _ (le_trans (f_le_bach f T _) (Hrep _ hyc).le) fun k => ?_)
    (le_trans (Hrep _ hyc).ge (bach_mono_index f hf _ _ HTT' HT'm _))
  refine fixOrd_least (bmono_bcomp f hf _ HT'm k) _ _ (limit_least fun j => ?_) (Hcl' k _ hyc)
  exact lt_of_le_of_lt (ihy j (hhc j)).le (HG.increasing _ _ hyc (index_lt (mk Y h) j))

/-- Rocq: `BachmannPower.BRep_bsub_equiv`. -/
theorem BRep_bsub_equiv (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (T T' : BOrd.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (H1 : bsub T T') (H2 : bsub T' T) (HT : BFam T) (HT' : BFam T')
    (HR : BRep f T G) : BRep f T' G :=
  BRep_extend f hf T T' G H1 HT' HR fun k' y hy =>
    let ⟨k, hk⟩ := bcomp_bsub f hf T T' H2 HT k'
    le_trans (hk _) (HR.2.2 k y hy)

/-- The power theorem for the canonical trees. Rocq: `BachmannPower.bach_bexpΩ_rep`. -/
theorem bach_bexpΩ_rep (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) (ζ : Ordinal.{u})
    (hζ : Complete ζ) (β : BOrd.{u}) (G : Ordinal.{u} → Ordinal.{u}) (hβ : BFam β) (HR : BRep f β G)
    (ξ : Ordinal.{u}) (hξ : Complete ξ) :
    BRep f (badd β (bmul (bexpΩ (embed ζ)) (embed ξ))) (schutteColumn G (1 + ζ) ξ) :=
  BRep_bsub_equiv f hf (badd β (bmul (bPow ζ) (embed ξ))) _ _
    (bsub_badd_r _ _ _ (bsub_bmul_l _ _ (bsub_bPow_bexpΩ ζ).1 _))
    (bsub_badd_r _ _ _ (bsub_bmul_l _ _ (bsub_bPow_bexpΩ ζ).2 _))
    (bfam_badd _ _ hβ (bfam_bmul _ _ (bfam_bPow ζ) (bfam_embed ξ)))
    (bfam_badd _ _ hβ (bfam_bmul _ _ (bfam_bexpΩ _ (bfam_embed ζ)) (bfam_embed ξ)))
    (bach_bPow_rep f hf ζ hζ β G hβ HR ξ hξ)

/-- `φ_{Ω^ζ}(0)` is the Schütte column `1+ζ` at coefficient 1. Rocq: `BachmannPower.bach_bexpΩ_zero`. -/
theorem bach_bexpΩ_zero (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (ζ : Ordinal.{u})
    (hζ : Complete ζ) : bach f (bexpΩ (embed ζ)) 0 ≈ schutteColumn f (1 + ζ) 1 0 := by
  have hfm := hf.monotone
  have HP : BFam (bexpΩ (embed ζ)) := bfam_bexpΩ _ (bfam_embed ζ)
  have HP1 : BFam (bmul (bexpΩ (embed ζ)) (embed 1)) := bfam_bmul _ _ HP (bfam_embed 1)
  refine equiv_trans (bach_bsub_eq f hfm _ _ (bsub_bmul_one _).2 (bsub_bmul_one _).1 HP HP1 0) ?_
  refine equiv_trans (bach_badd_zero_l f hfm _ HP1 0).symm ?_
  exact (bach_bexpΩ_rep f hfm ζ hζ bzero f bfam_bzero (bach_zero_rep f hf) 1 complete_1).2.1 0 zero_complete

end Bachmann

end ConstructiveOrdinals
